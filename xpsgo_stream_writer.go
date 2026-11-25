// Copyright 2026 肖其顿 (XIAO QI DUN)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package xpsgo

import (
	"archive/zip"
	"bytes"
	"compress/flate"
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"hash/crc32"
	"image"
	"io"
	"maps"
	"math"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/xiaoqidun/jxrgo"
)

// StreamWriteOptions 设置前向流式写出器的压缩策略、交错分片大小、自动释放提示、资源预算与固定时间戳
// InterleaveBytes为零时按整部件直接落盘，非零时按至多8MiB分片交错落盘；AutoDiscard启用后按页生命周期自动生成DiscardControl
type StreamWriteOptions struct {
	Compression     Compression
	InterleaveBytes int64
	AutoDiscard     bool
	Limits          Limits
	MaxImagePixels  uint64
	FixedTime       time.Time
}

// streamWrittenPart 保存已落盘逻辑部件的规范名称与内容类型，不滞留部件字节载荷
type streamWrittenPart struct {
	name  string
	media string
}

// streamHashEntry 保存已落盘资源的内容摘要、长度、媒体类型及规范路径，供流式去重复用
type streamHashEntry struct {
	name  string
	media string
	size  int
}

// streamPieceSink 为逐行流式图像编码提供可选分片直写ZIP通道，避免整图载荷驻留内存
type streamPieceSink struct {
	writer    *StreamWriter
	ctx       context.Context
	part      string
	maxBytes  int64
	written   int64
	pieceIdx  int
	direct    io.Writer
	buf       bytes.Buffer
	finalized bool
}

// StreamWriter 提供真前向低内存流式XPS/OpenXPS写出器，资源与页面提交即落盘ZIP流，关闭时补齐索引与元数据
type StreamWriter struct {
	mu               sync.Mutex
	format           Format
	limits           Limits
	maxImagePixels   uint64
	compression      Compression
	interleaveBytes  int64
	autoDiscard      bool
	fixedTime        time.Time
	counted          packageOutput
	archive          *zipMetadataWriter
	sequence         string
	documents        []Document
	currentDoc       int
	allPages         []string
	parts            map[string]streamWrittenPart
	names            map[string]bool
	parents          map[string]int
	allocated        map[string]int
	hashes           map[[32]byte][]streamHashEntry
	relations        map[string][]Relationship
	restrictedFonts  map[string]bool
	dictDeps         map[string][]string
	resourceLastPage map[string]int
	releasedAfter    map[string]int
	partBytes        int64
	entryCount       int
	closed           bool
	closeErr         error
	failed           error
	optimizer        *flate.Writer
	candidate        compressionBuffer
	copyBuf          []byte
}

// DefaultStreamWriteOptions 返回前向流式写出器的默认配置
// 返回: StreamWriteOptions 默认流式写出选项
func DefaultStreamWriteOptions() StreamWriteOptions {
	return StreamWriteOptions{Compression: CompressionDeflate, Limits: DefaultLimits(), MaxImagePixels: DefaultImageOptions().MaxPixels}
}

// NewStreamWriter 创建前向流式交错写出器，不接管底层输出流关闭责任，结束前必须调用Close
// 入参: ctx 取消Context，nil采用Background, w 底层输出流, format 文档方言，FormatUnknown默认OpenXPS, options 流式写出选项，nil采用默认值
// 返回: *StreamWriter 流式写出器, error 参数、预算或取消错误
func NewStreamWriter(ctx context.Context, w io.Writer, format Format, options *StreamWriteOptions) (*StreamWriter, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if w == nil {
		return nil, fmt.Errorf("%w: nil stream output writer", ErrInvalid)
	}
	if format == FormatUnknown {
		format = FormatOpenXPS
	}
	if formatNamespace(format) == "" {
		return nil, fmt.Errorf("%w: invalid stream package format", ErrInvalid)
	}
	cfg := DefaultStreamWriteOptions()
	if options != nil {
		cfg.Compression = options.Compression
		cfg.InterleaveBytes = options.InterleaveBytes
		cfg.AutoDiscard = options.AutoDiscard
		cfg.Limits = mergeLimits(cfg.Limits, options.Limits)
		if options.MaxImagePixels != 0 {
			cfg.MaxImagePixels = options.MaxImagePixels
		}
		cfg.FixedTime = options.FixedTime
	}
	if cfg.Compression == CompressionOriginal {
		cfg.Compression = CompressionDeflate
	}
	if cfg.Compression > CompressionOptimize || cfg.InterleaveBytes < 0 || cfg.InterleaveBytes > compressionBufferLimit {
		return nil, fmt.Errorf("%w: invalid stream write options", ErrInvalid)
	}
	if err := validateLimits(cfg.Limits); err != nil {
		return nil, err
	}
	sw := &StreamWriter{
		format:           format,
		limits:           cfg.Limits,
		maxImagePixels:   cfg.MaxImagePixels,
		compression:      cfg.Compression,
		interleaveBytes:  cfg.InterleaveBytes,
		autoDiscard:      cfg.AutoDiscard,
		fixedTime:        cfg.FixedTime,
		sequence:         "/FixedDocSeq.fdseq",
		currentDoc:       -1,
		parts:            make(map[string]streamWrittenPart),
		names:            make(map[string]bool),
		parents:          make(map[string]int),
		allocated:        make(map[string]int),
		hashes:           make(map[[32]byte][]streamHashEntry),
		relations:        make(map[string][]Relationship),
		restrictedFonts:  make(map[string]bool),
		dictDeps:         make(map[string][]string),
		resourceLastPage: make(map[string]int),
		releasedAfter:    make(map[string]int),
		copyBuf:          make([]byte, 32<<10),
	}
	if cfg.Compression == CompressionOptimize {
		opt, err := flate.NewWriter(io.Discard, flate.BestCompression)
		if err != nil {
			return nil, err
		}
		sw.optimizer = opt
	}
	sw.counted = packageOutput{writer: w, context: ctx, limit: cfg.Limits.MaxPackageBytes}
	sw.archive = newZIPMetadataWriter(&sw.counted, ctx)
	sw.registerName(sw.sequence)
	sw.registerName("/_rels/.rels")
	sw.registerName(opcTypesName)
	return sw, nil
}

// BytesWritten 返回当前已写入底层输出流的累计字节数
// 返回: int64 已写字节数
func (w *StreamWriter) BytesWritten() int64 {
	if w == nil {
		return 0
	}
	w.mu.Lock()
	defer w.mu.Unlock()
	return w.counted.count
}

// BeginDocument 在当前流式包中开启新的固定文档并将其设为后续AddPage的默认目标文档
// 入参: ctx 取消Context，nil采用Background
// 返回: int 新固定文档的零基序号, error 状态、名称或取消错误
func (w *StreamWriter) BeginDocument(ctx context.Context) (int, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return 0, err
	}
	if err := w.lock(ctx); err != nil {
		return 0, err
	}
	defer w.mu.Unlock()
	return w.beginDocumentLocked(ctx)
}

// beginDocumentLocked 在持有互斥锁时分配并开启新固定文档
// 入参: ctx 已规范化取消Context
// 返回: int 新固定文档序号, error 名称、预算或取消错误
func (w *StreamWriter) beginDocumentLocked(ctx context.Context) (int, error) {
	const pattern = "/Documents/%d/FixedDoc.fdoc"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return 0, err
	}
	if len(w.names)+1 >= w.limits.MaxPartCount {
		return 0, fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	w.documents = append(w.documents, Document{Part: part})
	w.currentDoc = len(w.documents) - 1
	w.registerName(part)
	w.commitNameLocked(pattern, part)
	return w.currentDoc, nil
}

// AddFont 校验字体嵌入许可后按唯一GUID路径混淆并立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始OpenType或TrueType字体字节
// 返回: string 混淆字体的包根URI, error 格式、许可、取消或写出错误
func (w *StreamWriter) AddFont(ctx context.Context, data []byte) (string, error) {
	return w.AddFontWithOptions(ctx, data, nil)
}

// AddFontWithOptions 按指定选项校验许可、可选去重与混淆嵌入字体并立即落盘，对TTC/OTC返回带#index的FontUri
// 入参: ctx 取消Context，nil采用Background, data 原始字体字节, options 嵌入选项，nil默认混淆
// 返回: string 字体部件URI，集合字体附加#index片段, error 格式、许可、索引、取消或写出错误
func (w *StreamWriter) AddFontWithOptions(ctx context.Context, data []byte, options *AddFontOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	obfuscate := true
	deduplicate := false
	collectionIndex := 0
	if options != nil {
		if options.Obfuscate != nil {
			obfuscate = *options.Obfuscate
		}
		deduplicate = options.Deduplicate
		collectionIndex = options.CollectionIndex
	}
	isCollection, isCFF, err := validateEmbeddedFontData(ctx, data, w.limits.MaxPartBytes, obfuscate, collectionIndex)
	if err != nil {
		return "", err
	}
	media := "application/vnd.ms-package.obfuscated-opentype"
	if !obfuscate {
		media = "application/vnd.ms-opentype"
	}
	digest := sha256.Sum256(data)
	if deduplicate {
		if existing, found := w.findHashLocked(digest, media, len(data)); found {
			if isCollection {
				return fmt.Sprintf("%s#%d", existing, collectionIndex), nil
			}
			return existing, nil
		}
	}
	var part string
	pattern := ""
	if obfuscate {
		part, err = w.newFontPartLocked()
	} else {
		ext := "ttf"
		if isCollection {
			ext = "ttc"
		} else if isCFF {
			ext = "otf"
		}
		pattern = "/Resources/Fonts/%d." + ext
		part, err = w.newNameLocked(pattern, ctx)
	}
	if err != nil {
		return "", err
	}
	payload := data
	if obfuscate {
		payload, err = ObfuscateFont(part, data)
		if err != nil {
			return "", err
		}
	}
	if err := w.writePartLocked(ctx, part, media, payload, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.recordHashLocked(digest, part, media, len(data))
	if fontDataHasRestrictedEmbedding(data) {
		w.restrictedFonts[strings.ToLower(part)] = true
	}
	if isCollection {
		return fmt.Sprintf("%s#%d", part, collectionIndex), nil
	}
	return part, nil
}

// fontDataHasRestrictedEmbedding 检查字体任意面是否带有OS/2预览与打印嵌入限制标志
// 入参: data 已通过校验的原始字体字节
// 返回: bool 是否需要Restricted Font关系
func fontDataHasRestrictedEmbedding(data []byte) bool {
	face, err := parseFontFace(data, 0)
	if err != nil {
		return false
	}
	count := uint32(1)
	if face.collection {
		count = binary.BigEndian.Uint32(data[8:12])
	}
	for index := uint32(0); index < count; index++ {
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return false
			}
		}
		if os2, err := parseFontOS2Metrics(face); err == nil && os2 != nil && os2.fsType&4 != 0 {
			return true
		}
	}
	return false
}

// AddImage 按魔数识别图像并立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始图像字节
// 返回: string 图像部件URI, error 格式、预算、取消或写出错误
func (w *StreamWriter) AddImage(ctx context.Context, data []byte) (string, error) {
	return w.AddImageWithOptions(ctx, data, nil)
}

// AddImageWithOptions 按魔数识别图像并支持流式摘要去重后立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始图像字节, options 嵌入选项，nil禁用去重
// 返回: string 图像部件URI, error 格式、预算、取消或写出错误
func (w *StreamWriter) AddImageWithOptions(ctx context.Context, data []byte, options *AddImageOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty image data", ErrInvalid)
	}
	media, ext, err := detectImageFormat(data)
	if err != nil {
		return "", err
	}
	return w.writeDeduplicatedResourceLocked(ctx, "/Resources/Images/%d."+ext, media, data, options != nil && options.Deduplicate)
}

// AddGoImage 编码Go标准图像并立即落盘至底层流，支持内容去重
// 入参: ctx 取消Context，nil采用Background, img 标准Go图像, options 编码与去重选项，nil自动选择格式
// 返回: string 图像部件URI, error 编码、预算、取消或写出错误
func (w *StreamWriter) AddGoImage(ctx context.Context, img image.Image, options *ImageEncodeOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	data, media, ext, err := encodeGoImage(ctx, img, options, w.limits.MaxPartBytes)
	if err != nil {
		return "", err
	}
	return w.writeDeduplicatedResourceLocked(ctx, "/Resources/Images/%d."+ext, media, data, options != nil && options.Deduplicate)
}

// AddImageFromRows 通过逐行流式回调对接jxrgo.EncodeRows直接流式写入底层ZIP，避免整图滞留内存
// 入参: ctx 取消Context，nil采用Background, info JPEG XR图像头信息, read 逐行像素回调, options JPEG XR编码选项，nil采用默认值
// 返回: string 图像部件URI, error 编码、预算、取消或写出错误
func (w *StreamWriter) AddImageFromRows(ctx context.Context, info jxrgo.Info, read jxrgo.RasterRowReader, options *jxrgo.EncodeOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if read == nil {
		return "", fmt.Errorf("%w: missing row reader", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	const pattern = "/Resources/Images/%d.jxr"
	const media = "image/vnd.ms-photo"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if len(w.names)+1 >= w.limits.MaxPartCount {
		return "", fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	var cfg jxrgo.EncodeOptions
	if options != nil {
		cfg = *options
	}
	maxPart := min(w.limits.MaxPartBytes, w.limits.MaxPackageBytes-w.partBytes)
	if maxPart <= 0 {
		return "", fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	if cfg.MaxOutputBytes == 0 || cfg.MaxOutputBytes > uint64(maxPart) {
		cfg.MaxOutputBytes = uint64(maxPart)
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	if err := jxrgo.EncodeRows(ctx, sink, info, read, &cfg); err != nil {
		w.failed = err
		return "", err
	}
	if err := sink.finish(); err != nil {
		w.failed = err
		return "", err
	}
	w.registerPartMetaLocked(part, media, sink.written)
	w.commitNameLocked(pattern, part)
	return part, nil
}

// AddColorProfile 校验ICC颜色配置文件并立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始ICC字节
// 返回: string 配置文件部件URI, error 格式、预算、取消或写出错误
func (w *StreamWriter) AddColorProfile(ctx context.Context, data []byte) (string, error) {
	return w.AddColorProfileWithOptions(ctx, data, false)
}

// AddColorProfileWithOptions 校验ICC颜色配置文件并支持去重后立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始ICC字节, deduplicate 是否按摘要去重
// 返回: string 配置文件部件URI, error 格式、预算、取消或写出错误
func (w *StreamWriter) AddColorProfileWithOptions(ctx context.Context, data []byte, deduplicate bool) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty color profile data", ErrInvalid)
	}
	if int64(len(data)) > w.limits.MaxPartBytes {
		return "", fmt.Errorf("%w: color profile byte budget", ErrLimit)
	}
	if _, err := validateCreatedICCProfile(data, ctx); err != nil {
		return "", err
	}
	return w.writeDeduplicatedResourceLocked(ctx, "/Resources/Profiles/%d.icc", "application/vnd.ms-color.iccprofile", data, deduplicate)
}

// writeDeduplicatedResourceLocked 在持有互斥锁时按可选SHA-256摘要去重并分配路径写入资源部件
// 入参: ctx 已规范化取消Context, pattern 路径模板, media 内容类型, data 资源字节, deduplicate 是否启用摘要去重
// 返回: string 部件URI, error 名称、预算、取消或写出错误
func (w *StreamWriter) writeDeduplicatedResourceLocked(ctx context.Context, pattern, media string, data []byte, deduplicate bool) (string, error) {
	digest := sha256.Sum256(data)
	if deduplicate {
		if existing, found := w.findHashLocked(digest, media, len(data)); found {
			return existing, nil
		}
	}
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, media, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.recordHashLocked(digest, part, media, len(data))
	return part, nil
}

// AddResourceDictionary 编码共享远程资源字典并立即落盘，同时记录其直接资源依赖供页面关系与释放提示追踪
// 入参: ctx 取消Context，nil采用Background, dict 资源字典模型，Source必须为空
// 返回: string 资源字典部件URI, error 模型、编码、预算、取消或写出错误
func (w *StreamWriter) AddResourceDictionary(ctx context.Context, dict *ResourceDictionary) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if dict == nil {
		return "", fmt.Errorf("%w: nil resource dictionary", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	const pattern = "/Resources/Dictionaries/%d.dict"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	var buf bytes.Buffer
	if _, err := EncodeResourceDictionary(ctx, &buf, dict, &EncodeOptions{Format: w.format, Limits: w.limits, Part: part}); err != nil {
		return "", err
	}
	data := buf.Bytes()
	root, err := decodeXML(data, w.limits)
	if err != nil {
		return "", err
	}
	deps, err := collectNodeResourceParts(part, root)
	if err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, resourceDictionaryContentType, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.dictDeps[strings.ToLower(part)] = deps
	return part, nil
}

// AddPart 按OPC规则与[M12.8]标准媒体类型校验并立即落盘自定义或扩展部件
// 入参: ctx 取消Context，nil采用Background, part 部件URI, media 内容类型, data 部件内容
// 返回: error 名称冲突、媒体类型、预算、取消或写出错误
func (w *StreamWriter) AddPart(ctx context.Context, part, media string, data []byte) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return err
	}
	if opcRelationshipName(canonical) || strings.EqualFold(canonical, opcTypesName) || strings.EqualFold(canonical, w.sequence) {
		return fmt.Errorf("%w: managed stream part name", ErrInvalid)
	}
	if err := w.availableLocked(canonical); err != nil {
		return err
	}
	return w.writePartLocked(ctx, canonical, media, data, true)
}

// AddPage 编码单页模型并立即落盘至底层流，不在内存中保留页面字节载荷，并自动更新依赖关系与释放周期
// 入参: ctx 取消Context，nil采用Background, page 页面模型，Part为空时自动分配
// 返回: string 写入的固定页面部件URI, error 模型、链接目标、编码、预算、取消或写出错误
func (w *StreamWriter) AddPage(ctx context.Context, page *Page) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if page == nil {
		return "", fmt.Errorf("%w: nil stream page", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	implicitDoc := w.currentDoc < 0
	const docPattern = "/Documents/%d/FixedDoc.fdoc"
	prevDocAlloc, hadDocAlloc := w.allocated[docPattern]
	var implicitDocPart string
	committed := false
	if implicitDoc {
		if _, err := w.beginDocumentLocked(ctx); err != nil {
			return "", err
		}
		implicitDocPart = w.documents[w.currentDoc].Part
		defer func() {
			if !committed {
				w.documents = w.documents[:len(w.documents)-1]
				w.currentDoc = -1
				w.unregisterName(implicitDocPart)
				if hadDocAlloc {
					w.allocated[docPattern] = prevDocAlloc
				} else {
					delete(w.allocated, docPattern)
				}
			}
		}()
	}
	if len(w.allPages) >= w.limits.MaxPageCount {
		return "", fmt.Errorf("%w: stream page count", ErrLimit)
	}
	docIdx := w.currentDoc
	docPart := w.documents[docIdx].Part
	value := *page
	pattern := ""
	if value.Part == "" {
		base := docPart[:strings.LastIndexByte(docPart, '/')+1]
		pattern = base + "Pages/%d.fpage"
		var err error
		value.Part, err = w.newNameLocked(pattern, ctx)
		if err != nil {
			return "", err
		}
	}
	part, err := opcPartName(value.Part)
	if err != nil {
		return "", err
	}
	if err := w.availableLocked(part); err != nil {
		return "", err
	}
	value.Part = part
	var buf bytes.Buffer
	if _, err := EncodePage(ctx, &buf, &value, &EncodeOptions{Format: w.format, Limits: w.limits}); err != nil {
		return "", err
	}
	data := buf.Bytes()
	root, err := decodeXML(data, w.limits)
	if err != nil {
		return "", err
	}
	targets, err := validateExplicitLinkTargetsForPage(w.format, w.documents, value.LinkTargets, createdPageTargets(root), docIdx, -1)
	if err != nil {
		return "", err
	}
	deps, err := collectNodeResourceParts(part, root)
	if err != nil {
		return "", err
	}
	expandedDeps := w.expandPageDependenciesLocked(deps)
	if err := w.writePartLocked(ctx, part, fixedContentType("fixedpage"), data, true); err != nil {
		return "", err
	}
	committed = true
	w.commitNameLocked(pattern, part)
	pageIndex := len(w.allPages)
	w.allPages = append(w.allPages, part)
	w.documents[docIdx].Pages = append(w.documents[docIdx].Pages, PageReference{Part: part, Width: value.Width, Height: value.Height, LinkTargets: targets})
	reqType := formatNamespace(w.format) + "/required-resource"
	resType := formatNamespace(w.format) + "/restricted-font"
	for _, dep := range expandedDeps {
		depKey := strings.ToLower(dep)
		w.resourceLastPage[depKey] = pageIndex
		w.appendRelationLocked(part, reqType, dep, false)
		if w.restrictedFonts[depKey] {
			w.appendRelationLocked(docPart, resType, dep, false)
		}
	}
	return part, nil
}

// ReleaseResource 标记指定资源在当前已提交页面之后不再被引用，在Close时自动生成合规DiscardControl提示
// 入参: part 已写入的资源部件URI
// 返回: error 部件名错误或流式写出器已关闭错误
func (w *StreamWriter) ReleaseResource(part string) error {
	if err := w.lock(context.Background()); err != nil {
		return err
	}
	defer w.mu.Unlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return err
	}
	key := strings.ToLower(canonical)
	if _, exists := w.parts[key]; !exists {
		return fmt.Errorf("%w: released resource %s does not exist", ErrInvalid, canonical)
	}
	w.releasedAfter[key] = len(w.allPages) - 1
	return nil
}

// SetCoreProperties 编码OPC核心属性并立即落盘，同时记录包根核心属性关系
// 入参: ctx 取消Context，nil采用Background, props 核心属性数据
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) SetCoreProperties(ctx context.Context, props CoreProperties) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	var buf bytes.Buffer
	encoder := xml.NewEncoder(&buf)
	if err := props.MarshalXML(encoder, xml.StartElement{}); err != nil {
		return err
	}
	if err := encoder.Flush(); err != nil {
		return err
	}
	data := buf.Bytes()
	if int64(len(data)) > min(w.limits.MaxPartBytes, w.limits.MaxMetadataBytes) {
		return fmt.Errorf("%w: core properties byte budget", ErrLimit)
	}
	part := "/docProps/core.xml"
	pattern := ""
	if w.availableLocked(part) != nil {
		pattern = "/docProps/core%d.xml"
		var err error
		part, err = w.newNameLocked(pattern, ctx)
		if err != nil {
			return err
		}
	}
	if err := w.writePartLocked(ctx, part, opcCoreType, data, true); err != nil {
		return err
	}
	w.commitNameLocked(pattern, part)
	w.replaceSingleRelationLocked("/", opcCoreRel, part)
	return nil
}

// SetPrintTicket 编码Framework打印票据、立即落盘并绑定至文档序列、固定文档或固定页面
// 入参: ctx 取消Context，nil采用Background, targetPart 目标来源部件，空字符串表示文档序列, settings 打印设置模型
// 返回: string 写入的打印票据部件URI, error 来源、编码、预算、取消或写出错误
func (w *StreamWriter) SetPrintTicket(ctx context.Context, targetPart string, settings *PrintSettings) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if settings == nil {
		return "", fmt.Errorf("%w: nil print settings", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	source := targetPart
	if source == "" {
		source = w.sequence
	}
	canonical, err := opcPartName(source)
	if err != nil {
		return "", err
	}
	if w.partScopeLocked(canonical) == PrintScopeUnknown {
		return "", fmt.Errorf("%w: stream print ticket source is not a fixed layout part", ErrInvalid)
	}
	var buf bytes.Buffer
	if _, err := EncodePrintSettings(ctx, &buf, settings, &PrintSettingsOptions{Limits: w.limits}); err != nil {
		return "", err
	}
	const pattern = "/Metadata/PrintTicket%d.xml"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, printTicketType, buf.Bytes(), true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.replaceSingleRelationLocked(canonical, formatNamespace(w.format)+"/printticket", part)
	return part, nil
}

// SetThumbnail 校验JPEG或PNG缩略图图像、立即落盘并绑定至包根或固定页面
// 入参: ctx 取消Context，nil采用Background, targetPart 目标来源部件，空字符串或/表示包根, data JPEG或PNG图像字节
// 返回: string 写入的缩略图部件URI, error 来源、图像格式、解码、预算、取消或写出错误
func (w *StreamWriter) SetThumbnail(ctx context.Context, targetPart string, data []byte) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty thumbnail image data", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	source := targetPart
	if source == "" {
		source = "/"
	}
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return "", err
		}
		source = canonical
		scope := w.partScopeLocked(source)
		if scope != PrintScopePage {
			return "", fmt.Errorf("%w: invalid stream thumbnail source", ErrInvalid)
		}
	}
	media, ext, err := detectImageFormat(data)
	if err != nil || !thumbnailMedia(media) {
		return "", fmt.Errorf("%w: thumbnail requires JPEG or PNG image", ErrInvalid)
	}
	if int64(len(data)) > w.limits.MaxPartBytes {
		return "", fmt.Errorf("%w: thumbnail byte budget", ErrLimit)
	}
	if _, err := decodeRasterImageContext(ctx, data, media, w.maxImagePixels); err != nil {
		return "", err
	}
	pattern := "/Metadata/Thumbnail%d." + ext
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, media, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.replaceSingleRelationLocked(source, thumbnailRelationship, part)
	return part, nil
}

// SetDocumentStructure 编码指定固定文档的目录与故事结构、立即落盘并绑定documentstructure关系
// 入参: ctx 取消Context，nil采用Background, docIndex 固定文档序号, structure 文档结构模型
// 返回: error 序号、编码、预算、取消或写出错误
func (w *StreamWriter) SetDocumentStructure(ctx context.Context, docIndex int, structure *DocumentStructure) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if structure == nil {
		return fmt.Errorf("%w: nil document structure", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	if docIndex < 0 || docIndex >= len(w.documents) {
		return fmt.Errorf("%w: stream document index", ErrInvalid)
	}
	source := w.documents[docIndex].Part
	data, err := createdDocumentStructure(structure, w.format, w.limits, ctx)
	if err != nil {
		return err
	}
	pattern := source[:strings.LastIndexByte(source, '/')+1] + "Structure%d.struct"
	part := structure.Part
	usedPattern := ""
	if part == "" {
		usedPattern = pattern
		part, err = w.newNameLocked(pattern, ctx)
		if err != nil {
			return err
		}
	} else {
		part, err = opcPartName(part)
		if err != nil {
			return err
		}
		if err := w.availableLocked(part); err != nil {
			return err
		}
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("documentstructure"), data, true); err != nil {
		return err
	}
	w.commitNameLocked(usedPattern, part)
	w.replaceSingleRelationLocked(source, formatNamespace(w.format)+"/documentstructure", part)
	return nil
}

// SetStoryFragments 编码指定页面的故事片段、立即落盘并绑定storyfragments关系
// 入参: ctx 取消Context，nil采用Background, docIndex 文档序号, pageIndex 文档内页面序号, fragments 故事片段模型
// 返回: error 序号、编码、预算、取消或写出错误
func (w *StreamWriter) SetStoryFragments(ctx context.Context, docIndex, pageIndex int, fragments *StoryFragments) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if fragments == nil {
		return fmt.Errorf("%w: nil story fragments", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	if docIndex < 0 || docIndex >= len(w.documents) || pageIndex < 0 || pageIndex >= len(w.documents[docIndex].Pages) {
		return fmt.Errorf("%w: stream document or page index", ErrInvalid)
	}
	source := w.documents[docIndex].Pages[pageIndex].Part
	data, err := createdStoryFragments(fragments, w.format, w.limits, ctx)
	if err != nil {
		return err
	}
	pattern := source[:strings.LastIndexByte(source, '/')+1] + "Structure/%d.frag"
	part := fragments.Part
	usedPattern := ""
	if part == "" {
		usedPattern = pattern
		part, err = w.newNameLocked(pattern, ctx)
		if err != nil {
			return err
		}
	} else {
		part, err = opcPartName(part)
		if err != nil {
			return err
		}
		if err := w.availableLocked(part); err != nil {
			return err
		}
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("storyfragments"), data, true); err != nil {
		return err
	}
	w.commitNameLocked(usedPattern, part)
	w.replaceSingleRelationLocked(source, formatNamespace(w.format)+"/storyfragments", part)
	return nil
}

// Close 幂等完成流式包收尾：补齐写入FixedDocument、FixedDocumentSequence、DiscardControl、全部.rels与[Content_Types].xml并关闭ZIP容器
// 入参: ctx 取消Context，nil采用Background
// 返回: error 结构、编码、预算、取消或ZIP关闭错误
func (w *StreamWriter) Close(ctx context.Context) error {
	ctx = normalizeContext(ctx)
	if w == nil {
		return fmt.Errorf("%w: nil stream writer", ErrInvalid)
	}
	w.mu.Lock()
	defer w.mu.Unlock()
	if w.closed {
		return w.closeErr
	}
	w.closed = true
	if w.optimizer != nil {
		defer w.optimizer.Close()
	}
	if w.failed != nil {
		w.closeErr = w.failed
		return w.closeErr
	}
	if err := checkContext(ctx); err != nil {
		w.closeErr = err
		return err
	}
	w.counted.context = ctx
	w.archive.context = ctx
	w.closeErr = w.finalizeLocked(ctx)
	return w.closeErr
}

// finalizeLocked 在Close期间写出剩余布局索引、释放提示、关系部件与内容类型表并关闭ZIP
// 入参: ctx 已规范化取消Context
// 返回: error 结构、编码或写出错误
func (w *StreamWriter) finalizeLocked(ctx context.Context) error {
	if len(w.documents) == 0 {
		return fmt.Errorf("%w: stream package requires at least one document", ErrInvalid)
	}
	ns := formatNamespace(w.format)
	sequence := createdNode(ns, "FixedDocumentSequence")
	for _, doc := range w.documents {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if len(doc.Pages) == 0 {
			return fmt.Errorf("%w: stream document %s requires at least one page", ErrInvalid, doc.Part)
		}
		docRef := createdNode(ns, "DocumentReference")
		docSrc, err := relativePart(w.sequence, doc.Part)
		if err != nil {
			return err
		}
		docRef.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: docSrc}}
		sequence.Children = append(sequence.Children, docRef)
		docRoot := createdNode(ns, "FixedDocument")
		for _, page := range doc.Pages {
			child := createdNode(ns, "PageContent")
			pageSrc, err := relativePart(doc.Part, page.Part)
			if err != nil {
				return err
			}
			child.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: pageSrc}}
			if page.Width > 0 {
				child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "Width"}, Value: encodeNumber(page.Width)})
			}
			if page.Height > 0 {
				child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "Height"}, Value: encodeNumber(page.Height)})
			}
			if len(page.LinkTargets) != 0 {
				container := createdNode(ns, "PageContent.LinkTargets")
				for _, target := range page.LinkTargets {
					node := createdNode(ns, "LinkTarget")
					node.Attr = []xml.Attr{{Name: xml.Name{Local: "Name"}, Value: target}}
					container.Children = append(container.Children, node)
				}
				child.Children = []*xmlElement{container}
			}
			docRoot.Children = append(docRoot.Children, child)
		}
		docData, err := createdMarkup(docRoot, w.limits, ctx)
		if err != nil {
			return err
		}
		if err := w.writePartLocked(ctx, doc.Part, fixedContentType("fixeddocument"), docData, true); err != nil {
			return err
		}
	}
	seqData, err := createdMarkup(sequence, w.limits, ctx)
	if err != nil {
		return err
	}
	if err := w.writePartLocked(ctx, w.sequence, fixedContentType("fixeddocumentsequence"), seqData, true); err != nil {
		return err
	}
	hints := w.buildDiscardHintsLocked()
	if len(hints) != 0 {
		discardPart := "/DiscardControl.xml"
		if w.availableLocked(discardPart) != nil {
			discardPart, err = w.newNameLocked("/DiscardControl%d.xml", ctx)
			if err != nil {
				return err
			}
		}
		var discardBuf bytes.Buffer
		if _, err := EncodeDiscardControl(ctx, &discardBuf, hints, &EncodeOptions{Format: w.format, Limits: w.limits, Part: discardPart}); err != nil {
			return err
		}
		if err := w.writePartLocked(ctx, discardPart, fixedContentType("discard-control"), discardBuf.Bytes(), true); err != nil {
			return err
		}
		w.replaceSingleRelationLocked("/", ns+"/discard-control", discardPart)
	}
	w.prependRelationLocked("/", ns+"/fixedrepresentation", w.sequence)
	for _, sourceKey := range slices.Sorted(maps.Keys(w.relations)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		rels := w.relations[sourceKey]
		if len(rels) == 0 {
			continue
		}
		source := w.resolveSourceCaseLocked(sourceKey)
		relPart := createdRelationshipPart(source)
		relData, err := createdRelationshipMarkup(rels, w.limits, ctx)
		if err != nil {
			return err
		}
		if err := w.writePartLocked(ctx, relPart, opcRelsType, relData, false); err != nil {
			return err
		}
	}
	typesRoot := createdNode(opcTypesNS, "Types")
	for _, key := range slices.Sorted(maps.Keys(w.parts)) {
		part := w.parts[key]
		child := createdNode(opcTypesNS, "Override")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "PartName"}, Value: part.name}, {Name: xml.Name{Local: "ContentType"}, Value: part.media}}
		typesRoot.Children = append(typesRoot.Children, child)
	}
	typesData, err := createdMarkup(typesRoot, w.limits, ctx)
	if err != nil {
		return err
	}
	if err := w.writeRawEntryLocked(ctx, opcTypesName, typesData, false); err != nil {
		return err
	}
	return w.archive.Close()
}

// buildDiscardHintsLocked 按AutoDiscard与显式ReleaseResource记录生成严格合法的释放提示列表
// 返回: []DiscardHint 按目标路径排序的合规释放提示
func (w *StreamWriter) buildDiscardHintsLocked() []DiscardHint {
	if len(w.allPages) == 0 {
		return nil
	}
	lastPageIdx := len(w.allPages) - 1
	pageIndexByKey := make(map[string]int, len(w.allPages))
	for idx, pagePart := range w.allPages {
		pageIndexByKey[strings.ToLower(pagePart)] = idx
	}
	minLastPage := make(map[string]int)
	bump := func(part string, idx int) {
		key := strings.ToLower(part)
		if prev, exists := minLastPage[key]; !exists || idx > prev {
			minLastPage[key] = idx
		}
		for _, dep := range w.dictDeps[key] {
			depKey := strings.ToLower(dep)
			if prev, exists := minLastPage[depKey]; !exists || idx > prev {
				minLastPage[depKey] = idx
			}
		}
	}
	ns := formatNamespace(w.format)
	restrictedRel := ns + "/restricted-font"
	discardRel := ns + "/discard-control"
	bumpRelations := func(source string, idx int, skipRestricted bool) {
		for _, rel := range w.relations[strings.ToLower(source)] {
			if rel.TargetMode != "" && rel.TargetMode != TargetModeInternal {
				continue
			}
			if rel.Type == discardRel || skipRestricted && rel.Type == restrictedRel {
				continue
			}
			bump(rel.Target, idx)
		}
	}
	bump(w.sequence, lastPageIdx)
	bumpRelations("/", lastPageIdx, false)
	bumpRelations(w.sequence, lastPageIdx, false)
	for _, doc := range w.documents {
		docLast := -1
		for _, page := range doc.Pages {
			if idx, ok := pageIndexByKey[strings.ToLower(page.Part)]; ok && idx > docLast {
				docLast = idx
			}
		}
		if docLast < 0 {
			continue
		}
		bump(doc.Part, docLast)
		bumpRelations(doc.Part, docLast, true)
	}
	for idx, pagePart := range w.allPages {
		bump(pagePart, idx)
		bumpRelations(pagePart, idx, false)
	}
	candidates := make(map[string]int)
	if w.autoDiscard {
		for key, lastIdx := range w.resourceLastPage {
			candidates[key] = lastIdx
		}
	}
	for key, releaseIdx := range w.releasedAfter {
		effective := releaseIdx
		if lastIdx, used := w.resourceLastPage[key]; used && lastIdx > effective {
			effective = lastIdx
		}
		if prev, exists := candidates[key]; !exists || effective > prev {
			candidates[key] = effective
		}
	}
	var hints []DiscardHint
	for _, key := range slices.Sorted(maps.Keys(candidates)) {
		part, exists := w.parts[key]
		if !exists {
			continue
		}
		effective := candidates[key]
		if minIdx, protected := minLastPage[key]; protected && minIdx > effective {
			effective = minIdx
		}
		sentinelIdx := effective + 1
		if sentinelIdx < 0 {
			sentinelIdx = 0
		}
		if sentinelIdx >= len(w.allPages) {
			continue
		}
		hints = append(hints, DiscardHint{Target: part.name, SentinelPage: w.allPages[sentinelIdx]})
	}
	return hints
}

// lock 校验流式写出器状态、获取互斥锁并刷新底层输出与ZIP写出器的取消Context
// 入参: ctx 已规范化取消Context
// 返回: error 空指针、已关闭或已失败状态错误
func (w *StreamWriter) lock(ctx context.Context) error {
	if w == nil {
		return fmt.Errorf("%w: nil stream writer", ErrInvalid)
	}
	w.mu.Lock()
	if w.closed {
		w.mu.Unlock()
		return ErrClosed
	}
	if w.failed != nil {
		err := w.failed
		w.mu.Unlock()
		return err
	}
	w.counted.context = ctx
	w.archive.context = ctx
	return nil
}

// writePartLocked 校验媒体类型与字节预算后将单个逻辑部件立即写入ZIP流并登记轻量元数据
// 入参: ctx 取消Context, part 已规范化部件URI, media 内容类型, data 部件字节, allowInterleave 是否允许按InterleaveBytes分片
// 返回: error 类型、预算、取消或写出错误
func (w *StreamWriter) writePartLocked(ctx context.Context, part, media string, data []byte, allowInterleave bool) error {
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return err
	}
	if int64(len(data)) > w.limits.MaxPartBytes {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if int64(len(data)) > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	key := strings.ToLower(part)
	if _, exists := w.parts[key]; exists {
		return fmt.Errorf("%w: duplicate stream part %s", ErrInvalid, part)
	}
	if len(w.parts)+1 >= w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	if err := w.writeRawEntryLocked(ctx, part, data, allowInterleave); err != nil {
		w.failed = err
		return err
	}
	w.registerPartMetaLocked(part, media, int64(len(data)))
	return nil
}

// registerPartMetaLocked 登记已落盘部件的轻量名称与媒体类型并累计解压字节统计
// 入参: part 规范化部件URI, media 内容类型, size 逻辑字节长度
func (w *StreamWriter) registerPartMetaLocked(part, media string, size int64) {
	key := strings.ToLower(part)
	w.parts[key] = streamWrittenPart{name: part, media: media}
	w.registerName(part)
	w.partBytes += size
}

// writeRawEntryLocked 将指定部件载荷按整部件或OPC分片方式立即写入底层ZIP流
// 入参: ctx 取消Context, part 部件URI, data 部件原始字节, allowInterleave 是否允许分片
// 返回: error 压缩、预算、取消或写出错误
func (w *StreamWriter) writeRawEntryLocked(ctx context.Context, part string, data []byte, allowInterleave bool) error {
	baseName := strings.TrimPrefix(part, "/")
	if !allowInterleave || w.interleaveBytes == 0 {
		return w.writeZIPPayloadLocked(ctx, baseName, data)
	}
	pieceSize := int(w.interleaveBytes)
	if len(data) == 0 {
		return w.writeZIPPayloadLocked(ctx, baseName+"/[0].last.piece", data)
	}
	pieceIdx := 0
	for offset := 0; offset < len(data); offset += pieceSize {
		end := min(offset+pieceSize, len(data))
		last := end == len(data)
		name := baseName + "/[" + strconv.Itoa(pieceIdx) + "]"
		if last {
			name += ".last"
		}
		name += ".piece"
		if err := w.writeZIPPayloadLocked(ctx, name, data[offset:end]); err != nil {
			return err
		}
		pieceIdx++
	}
	return nil
}

// writeZIPPayloadLocked 写入单个物理ZIP条目，支持Store、Deflate与无损Optimize压缩模式
// 入参: ctx 取消Context, entryName 物理ZIP条目路径, data 未压缩载荷
// 返回: error 条目计数、压缩、取消或写出错误
func (w *StreamWriter) writeZIPPayloadLocked(ctx context.Context, entryName string, data []byte) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if w.entryCount >= w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream ZIP entry count", ErrLimit)
	}
	w.entryCount++
	header := zip.FileHeader{Name: entryName, Method: zip.Deflate, Modified: w.fixedTime}
	if w.compression == CompressionStore {
		header.Method = zip.Store
		header.CRC32 = crc32.ChecksumIEEE(data)
		header.UncompressedSize64, header.CompressedSize64 = uint64(len(data)), uint64(len(data))
		if uint64(len(data)) < math.MaxUint32 {
			header.UncompressedSize, header.CompressedSize = uint32(len(data)), uint32(len(data))
		}
		header.ReaderVersion, header.CreatorVersion = 20, 20
		out, err := w.archive.CreateRaw(&header)
		if err != nil {
			return err
		}
		return writeCompressionInput(out, bytes.NewReader(data), w.copyBuf, ctx)
	}
	if w.compression == CompressionOptimize {
		limit := min(len(data), compressionBufferLimit)
		w.candidate.reset(limit)
		w.optimizer.Reset(&w.candidate)
		copyErr := writeCompressionInput(w.optimizer, bytes.NewReader(data), w.copyBuf, ctx)
		closeErr := w.optimizer.Close()
		if err := checkContext(ctx); err != nil {
			return err
		}
		if copyErr != nil && !errors.Is(copyErr, errCompressionBuffer) {
			return copyErr
		}
		if closeErr != nil && !errors.Is(closeErr, errCompressionBuffer) {
			return closeErr
		}
		header.Method = zip.Store
		payload := data
		if copyErr == nil && closeErr == nil && w.candidate.Len() < len(data) {
			header.Method = zip.Deflate
			payload = w.candidate.Bytes()
		}
		header.CRC32 = crc32.ChecksumIEEE(data)
		header.UncompressedSize64 = uint64(len(data))
		header.CompressedSize64 = uint64(len(payload))
		if header.UncompressedSize64 < math.MaxUint32 && header.CompressedSize64 < math.MaxUint32 {
			header.UncompressedSize = uint32(len(data))
			header.CompressedSize = uint32(len(payload))
		}
		header.ReaderVersion, header.CreatorVersion = 20, 20
		out, err := w.archive.CreateRaw(&header)
		if err != nil {
			return err
		}
		return writeCompressionInput(out, bytes.NewReader(payload), w.copyBuf, ctx)
	}
	out, err := w.archive.CreateHeader(&header)
	if err != nil {
		return err
	}
	return writeCompressionInput(out, bytes.NewReader(data), w.copyBuf, ctx)
}

// Write 接收流式编码器输出的字节块，按整部件直写或定长分片落盘至底层ZIP流
// 入参: p 待写字节切片
// 返回: int 已接收字节数, error 预算、取消或ZIP写出错误
func (s *streamPieceSink) Write(p []byte) (int, error) {
	if err := checkContext(s.ctx); err != nil {
		return 0, err
	}
	if int64(len(p)) > s.maxBytes-s.written {
		return 0, fmt.Errorf("%w: streaming image exceeds byte budget", ErrLimit)
	}
	if s.writer.interleaveBytes == 0 && s.writer.compression != CompressionOptimize {
		if s.direct == nil {
			if s.writer.entryCount >= s.writer.limits.MaxPartCount {
				return 0, fmt.Errorf("%w: stream ZIP entry count", ErrLimit)
			}
			s.writer.entryCount++
			method := zip.Deflate
			if s.writer.compression == CompressionStore {
				method = zip.Store
			}
			header := zip.FileHeader{Name: strings.TrimPrefix(s.part, "/"), Method: method, Modified: s.writer.fixedTime}
			out, err := s.writer.archive.CreateHeader(&header)
			if err != nil {
				return 0, err
			}
			s.direct = out
		}
		n, err := s.direct.Write(p)
		s.written += int64(n)
		return n, err
	}
	if s.writer.interleaveBytes == 0 {
		n, err := s.buf.Write(p)
		s.written += int64(n)
		return n, err
	}
	limit := int(s.writer.interleaveBytes)
	total := 0
	for len(p) > 0 {
		space := limit - s.buf.Len()
		if space == 0 {
			name := strings.TrimPrefix(s.part, "/") + "/[" + strconv.Itoa(s.pieceIdx) + "].piece"
			if err := s.writer.writeZIPPayloadLocked(s.ctx, name, s.buf.Bytes()); err != nil {
				return total, err
			}
			s.buf.Reset()
			s.pieceIdx++
			space = limit
		}
		take := min(len(p), space)
		s.buf.Write(p[:take])
		p = p[take:]
		total += take
		s.written += int64(take)
	}
	return total, nil
}

// finish 刷写剩余分片或Optimize整部件缓冲至底层ZIP流
// 返回: error 写出错误
func (s *streamPieceSink) finish() error {
	if s.finalized {
		return nil
	}
	s.finalized = true
	if s.writer.interleaveBytes == 0 && s.writer.compression != CompressionOptimize {
		if s.direct == nil {
			return s.writer.writeZIPPayloadLocked(s.ctx, strings.TrimPrefix(s.part, "/"), nil)
		}
		return nil
	}
	if s.writer.interleaveBytes == 0 {
		data := s.buf.Bytes()
		err := s.writer.writeZIPPayloadLocked(s.ctx, strings.TrimPrefix(s.part, "/"), data)
		s.buf.Reset()
		return err
	}
	name := strings.TrimPrefix(s.part, "/") + "/[" + strconv.Itoa(s.pieceIdx) + "].last.piece"
	data := s.buf.Bytes()
	err := s.writer.writeZIPPayloadLocked(s.ctx, name, data)
	s.buf.Reset()
	return err
}

// collectNodeResourceParts 扫描FixedPage或ResourceDictionary元素树收集其直接引用的包内资源部件URI
// 入参: sourcePart 当前XML所属规范部件URI, root XML根节点
// 返回: []string 去重后的规范资源部件URI切片, error URI解析错误
func collectNodeResourceParts(sourcePart string, root *xmlElement) ([]string, error) {
	seen := make(map[string]bool)
	var result []string
	addTarget := func(raw string) error {
		target, err := resolvePart(sourcePart, strings.Trim(raw, " \t\r\n"))
		if err != nil {
			return err
		}
		key := strings.ToLower(target)
		if !seen[key] {
			seen[key] = true
			result = append(result, target)
		}
		return nil
	}
	var walk func(*xmlElement) error
	walk = func(node *xmlElement) error {
		if node == nil {
			return nil
		}
		switch node.Name.Local {
		case "ResourceDictionary":
			if source, ok := node.attribute("Source"); ok {
				if err := addTarget(source); err != nil {
					return err
				}
			}
		case "Glyphs":
			if fontURI, ok := node.attribute("FontUri"); ok {
				uri, _, _, err := ParseFontURI(strings.Trim(fontURI, " \t\r\n"))
				if err != nil {
					return err
				}
				if err := addTarget(uri); err != nil {
					return err
				}
			}
		case "ImageBrush":
			if imgSrc, ok := node.attribute("ImageSource"); ok {
				trimmed := strings.Trim(imgSrc, " \t\r\n")
				if strings.HasPrefix(trimmed, "{ColorConvertedBitmap ") && strings.HasSuffix(trimmed, "}") {
					fields := strings.Fields(trimmed[1 : len(trimmed)-1])
					if len(fields) == 3 {
						if err := addTarget(fields[1]); err != nil {
							return err
						}
						if err := addTarget(fields[2]); err != nil {
							return err
						}
					}
				} else if err := addTarget(trimmed); err != nil {
					return err
				}
			}
		}
		for _, attr := range node.Attr {
			if attr.Name.Space != "" || !requiredColorAttribute(node.Name.Local, attr.Name.Local) {
				continue
			}
			if _, ref, err := parseResourceReference(attr.Value); err == nil && ref {
				continue
			}
			if colorValue, err := parseBrushColor(attr.Value, node.Name.Space); err == nil && colorValue.Space == ColorContext {
				if err := addTarget(colorValue.ProfileURI); err != nil {
					return err
				}
			}
		}
		for _, child := range node.Children {
			if err := walk(child); err != nil {
				return err
			}
		}
		return nil
	}
	if err := walk(root); err != nil {
		return nil, err
	}
	return result, nil
}

// expandPageDependenciesLocked 展开页面直接资源及其所引用远程资源字典的传递依赖集合
// 入参: direct 页面直接引用的资源部件URI列表
// 返回: []string 去重后的完整依赖部件URI列表
func (w *StreamWriter) expandPageDependenciesLocked(direct []string) []string {
	seen := make(map[string]bool, len(direct))
	result := make([]string, 0, len(direct))
	for _, dep := range direct {
		key := strings.ToLower(dep)
		if !seen[key] {
			seen[key] = true
			result = append(result, dep)
		}
		for _, sub := range w.dictDeps[key] {
			subKey := strings.ToLower(sub)
			if !seen[subKey] {
				seen[subKey] = true
				result = append(result, sub)
			}
		}
	}
	return result
}

// appendRelationLocked 为指定源部件追加内部关系，若已存在相同类型与目标则跳过重复记录
// 入参: source 源部件URI或/, relType 关系类型URI, target 目标部件URI, allowDuplicate 是否允许重复相同目标
func (w *StreamWriter) appendRelationLocked(source, relType, target string, allowDuplicate bool) {
	key := strings.ToLower(source)
	rels := w.relations[key]
	if !allowDuplicate {
		for _, rel := range rels {
			if rel.Type == relType && strings.EqualFold(rel.Target, target) {
				return
			}
		}
	}
	nextID := createdRelationshipIDs(rels)
	w.relations[key] = append(rels, Relationship{ID: nextID(), Type: relType, Target: target, TargetMode: TargetModeInternal})
}

// prependRelationLocked 在源部件关系列表首位插入固定布局主入口关系
// 入参: source 源部件URI或/, relType 关系类型URI, target 目标部件URI
func (w *StreamWriter) prependRelationLocked(source, relType, target string) {
	key := strings.ToLower(source)
	rels := w.relations[key]
	nextID := createdRelationshipIDs(rels)
	head := Relationship{ID: nextID(), Type: relType, Target: target, TargetMode: TargetModeInternal}
	w.relations[key] = append([]Relationship{head}, rels...)
}

// replaceSingleRelationLocked 替换源部件指定类型的单一关系目标，保留其他关系
// 入参: source 源部件URI或/, relType 关系类型URI, target 新目标部件URI
func (w *StreamWriter) replaceSingleRelationLocked(source, relType, target string) {
	key := strings.ToLower(source)
	rels := w.relations[key]
	for i := range rels {
		if rels[i].Type == relType {
			rels[i].Target = target
			rels[i].TargetMode = TargetModeInternal
			w.relations[key] = rels
			return
		}
	}
	nextID := createdRelationshipIDs(rels)
	w.relations[key] = append(rels, Relationship{ID: nextID(), Type: relType, Target: target, TargetMode: TargetModeInternal})
}

// resolveSourceCaseLocked 根据小写关系键还原原始大小写的源部件URI
// 入参: sourceKey 小写源部件键或/
// 返回: string 规范化原始大小写源部件URI
func (w *StreamWriter) resolveSourceCaseLocked(sourceKey string) string {
	if sourceKey == "/" {
		return "/"
	}
	if part, exists := w.parts[sourceKey]; exists {
		return part.name
	}
	if strings.EqualFold(w.sequence, sourceKey) {
		return w.sequence
	}
	for _, doc := range w.documents {
		if strings.EqualFold(doc.Part, sourceKey) {
			return doc.Part
		}
		for _, page := range doc.Pages {
			if strings.EqualFold(page.Part, sourceKey) {
				return page.Part
			}
		}
	}
	return sourceKey
}

// partScopeLocked 判断指定部件属于流式包中的作业、文档还是页面层级
// 入参: source 规范化部件URI
// 返回: PrintScope 所属固定布局层级
func (w *StreamWriter) partScopeLocked(source string) PrintScope {
	if strings.EqualFold(source, w.sequence) {
		return PrintScopeJob
	}
	for _, doc := range w.documents {
		if strings.EqualFold(source, doc.Part) {
			return PrintScopeDocument
		}
		for _, page := range doc.Pages {
			if strings.EqualFold(source, page.Part) {
				return PrintScopePage
			}
		}
	}
	return PrintScopeUnknown
}

// findHashLocked 在已落盘资源哈希索引中查找媒体类型与字节长度均一致的复用部件
// 入参: digest 内容SHA-256摘要, media 内容类型, size 原始字节长度
// 返回: string 已有部件URI, bool 是否命中复用
func (w *StreamWriter) findHashLocked(digest [32]byte, media string, size int) (string, bool) {
	for _, entry := range w.hashes[digest] {
		if entry.size == size && strings.EqualFold(entry.media, media) {
			return entry.name, true
		}
	}
	return "", false
}

// recordHashLocked 记录已落盘资源的轻量哈希索引项
// 入参: digest 内容SHA-256摘要, name 部件URI, media 内容类型, size 原始字节长度
func (w *StreamWriter) recordHashLocked(digest [32]byte, name, media string, size int) {
	w.hashes[digest] = append(w.hashes[digest], streamHashEntry{name: name, media: media, size: size})
}

// registerName 登记名称占用及其祖先路径计数以阻止OPC派生路径冲突
// 入参: part 已规范化部件URI
func (w *StreamWriter) registerName(part string) {
	key := strings.ToLower(part)
	if w.names[key] {
		return
	}
	w.names[key] = true
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		w.parents[key[:slash]]++
	}
}

// unregisterName 撤销名称占用及其祖先路径计数，用于回滚失败的隐式文档分配
// 入参: part 已规范化部件URI
func (w *StreamWriter) unregisterName(part string) {
	key := strings.ToLower(part)
	if !w.names[key] {
		return
	}
	delete(w.names, key)
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		parent := key[:slash]
		if w.parents[parent] <= 1 {
			delete(w.parents, parent)
		} else {
			w.parents[parent]--
		}
	}
}

// availableLocked 检查部件URI是否未与已有名称或祖先/后代路径冲突
// 入参: part 已规范化部件URI
// 返回: error 名称冲突错误
func (w *StreamWriter) availableLocked(part string) error {
	key := strings.ToLower(part)
	if opcRelationshipName(part) || w.names[key] || w.parents[key] != 0 {
		return fmt.Errorf("%w: stream part name collision %s", ErrInvalid, part)
	}
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		if w.names[key[:slash]] {
			return fmt.Errorf("%w: derived stream part name %s", ErrInvalid, part)
		}
	}
	return nil
}

// newFontPartLocked 生成不冲突的UUIDv4混淆字体部件路径
// 返回: string 字体部件URI, error 随机数或冲突错误
func (w *StreamWriter) newFontPartLocked() (string, error) {
	var raw [16]byte
	for range 1024 {
		if _, err := rand.Read(raw[:]); err != nil {
			return "", err
		}
		raw[6] = raw[6]&0x0f | 0x40
		raw[8] = raw[8]&0x3f | 0x80
		part := fmt.Sprintf("/Resources/Fonts/%X-%X-%X-%X-%X.odttf", raw[0:4], raw[4:6], raw[6:8], raw[8:10], raw[10:16])
		if w.availableLocked(part) == nil {
			return part, nil
		}
	}
	return "", fmt.Errorf("%w: unable to allocate unique stream font part", ErrLimit)
}

// newNameLocked 按含%d占位符的路径模板顺序分配不冲突的规范部件URI
// 入参: pattern 含唯一%d占位的路径模板, ctx 取消Context
// 返回: string 规范化可用部件URI, error 模板、冲突、预算或取消错误
func (w *StreamWriter) newNameLocked(pattern string, ctx context.Context) (string, error) {
	prefix, suffix, err := packageNamePattern(pattern, ctx)
	if err != nil {
		return "", err
	}
	index := w.allocated[pattern]
	if index < 0 || index == math.MaxInt {
		return "", fmt.Errorf("%w: stream part index exhausted", ErrLimit)
	}
	for range w.limits.MaxPartCount {
		if err := checkContext(ctx); err != nil {
			return "", err
		}
		if index == math.MaxInt {
			break
		}
		index++
		part := prefix + strconv.Itoa(index) + suffix
		if w.availableLocked(part) == nil {
			return part, nil
		}
	}
	return "", fmt.Errorf("%w: stream part name search exhausted", ErrLimit)
}

// commitNameLocked 提交最近一次模板分配的编号以加速后续分配
// 入参: pattern 路径模板，空串忽略, part 实际采用的部件URI
func (w *StreamWriter) commitNameLocked(pattern, part string) {
	if pattern == "" {
		return
	}
	prefix, suffix, err := packageNamePattern(pattern, nil)
	if err != nil || len(part) <= len(prefix)+len(suffix) || !strings.HasPrefix(part, prefix) || !strings.HasSuffix(part, suffix) {
		return
	}
	index, err := strconv.Atoi(part[len(prefix) : len(part)-len(suffix)])
	if err != nil {
		return
	}
	w.allocated[pattern] = index
}
