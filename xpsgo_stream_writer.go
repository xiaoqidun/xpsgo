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
	"fmt"
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

// StreamWriteOptions 设置前向流式写出器的压缩策略、交错分片大小、自动释放提示、前置内容类型表、紧凑编码、资源预算与固定时间戳
// InterleaveBytes为零时按整部件直接落盘，非零时按至多8MiB分片交错落盘；AutoDiscard启用后按页生命周期自动生成DiscardControl
// EarlyContentTypes启用后在流起始即写入包含全部标准扩展名Default映射的[Content_Types].xml并以交错分片增量推进索引、关系与释放提示，供ConsumeStream实时逐页交付
// Compact启用后对页面与资源字典使用紧凑属性编码
type StreamWriteOptions struct {
	Compression       Compression
	InterleaveBytes   int64
	AutoDiscard       bool
	EarlyContentTypes bool
	Compact           bool
	Limits            Limits
	MaxImagePixels    uint64
	FixedTime         time.Time
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
	touched   bool
	finalized bool
}

// streamResourceRef 保存单个页面或远程资源字典引用的规范资源部件URI、用途及可选TTC字体面序号
type streamResourceRef struct {
	part      string
	kind      requiredResourceKind
	faceIndex uint32
	hasFace   bool
}

// streamPageDeps 记录已落盘页面的轻量化直接依赖，供Close阶段展开后置远程字典与终检
type streamPageDeps struct {
	docPart   string
	pagePart  string
	pageIndex int
	deps      []streamResourceRef
}

// streamOpenPart 记录EarlyContentTypes模式下尚未闭合的OPC交错分片XML流状态
type streamOpenPart struct {
	part     string
	media    string
	pieceIdx int
	bytes    int64
	closing  string
	closed   bool
}

// StreamWriter 提供真前向低内存流式XPS/OpenXPS写出器，资源与页面提交即落盘ZIP流，关闭时补齐索引与元数据
type StreamWriter struct {
	mu                 sync.Mutex
	format             Format
	limits             Limits
	maxImagePixels     uint64
	compression        Compression
	interleaveBytes    int64
	autoDiscard        bool
	earlyContentTypes  bool
	compact            bool
	earlyDefaults      map[string]string
	fixedTime          time.Time
	counted            packageOutput
	archive            *zipMetadataWriter
	sequence           string
	documents          []Document
	currentDoc         int
	allPages           []string
	parts              map[string]streamWrittenPart
	registry           partNameRegistry
	allocated          map[string]int
	hashes             map[[32]byte][]streamHashEntry
	relations          map[string][]Relationship
	restrictedFaces    map[fontCacheKey]bool
	dictDeps           map[string][]streamResourceRef
	pageDeps           []streamPageDeps
	docStructMaxPage   map[int]int
	resourceLastPage   map[string]int
	releasedAfter      map[string]int
	openStreams        map[string]*streamOpenPart
	emittedRelCount    map[string]int
	emittedDiscardPage map[string]int
	lateDictSources    map[string]bool
	lastOpenPageRel    string
	discardPart        string
	partBytes          int64
	entryCount         int
	closed             bool
	closeErr           error
	failed             error
	optimizer          *flate.Writer
	candidate          compressionBuffer
	copyBuf            []byte
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
		cfg.EarlyContentTypes = options.EarlyContentTypes
		cfg.Compact = options.Compact
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
		format:             format,
		limits:             cfg.Limits,
		maxImagePixels:     cfg.MaxImagePixels,
		compression:        cfg.Compression,
		interleaveBytes:    cfg.InterleaveBytes,
		autoDiscard:        cfg.AutoDiscard,
		earlyContentTypes:  cfg.EarlyContentTypes,
		compact:            cfg.Compact,
		fixedTime:          cfg.FixedTime,
		sequence:           "/FixedDocSeq.fdseq",
		currentDoc:         -1,
		parts:              make(map[string]streamWrittenPart),
		registry:           newPartNameRegistry(),
		allocated:          make(map[string]int),
		hashes:             make(map[[32]byte][]streamHashEntry),
		relations:          make(map[string][]Relationship),
		restrictedFaces:    make(map[fontCacheKey]bool),
		dictDeps:           make(map[string][]streamResourceRef),
		docStructMaxPage:   make(map[int]int),
		resourceLastPage:   make(map[string]int),
		releasedAfter:      make(map[string]int),
		openStreams:        make(map[string]*streamOpenPart),
		emittedRelCount:    make(map[string]int),
		emittedDiscardPage: make(map[string]int),
		lateDictSources:    make(map[string]bool),
		copyBuf:            make([]byte, 32<<10),
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
	sw.registry.register(sw.sequence)
	sw.registry.register("/_rels/.rels")
	sw.registry.register(opcTypesName)
	if cfg.EarlyContentTypes {
		if err := sw.initEarlyStreamLocked(ctx); err != nil {
			if sw.optimizer != nil {
				_ = sw.optimizer.Close()
			}
			return nil, err
		}
	}
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

// SequencePart 返回当前流式包的固定文档序列部件URI
// 返回: string 文档序列部件URI，接收器为nil时返回空字符串
func (w *StreamWriter) SequencePart() string {
	if w == nil {
		return ""
	}
	w.mu.Lock()
	defer w.mu.Unlock()
	return w.sequence
}

// DocumentPart 返回指定序号固定文档的规范部件URI，便于绑定文档级PrintTicket等元数据
// 入参: docIndex 零基固定文档序号
// 返回: string 固定文档部件URI, error 接收器非法或序号越界错误
func (w *StreamWriter) DocumentPart(docIndex int) (string, error) {
	if w == nil {
		return "", fmt.Errorf("%w: nil stream writer", ErrInvalid)
	}
	w.mu.Lock()
	defer w.mu.Unlock()
	if docIndex < 0 || docIndex >= len(w.documents) {
		return "", fmt.Errorf("%w: stream document index", ErrInvalid)
	}
	return w.documents[docIndex].Part, nil
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

// beginDocumentLocked 在持有互斥锁时分配并开启新固定文档，EarlyContentTypes模式下同步推进分片流
// 入参: ctx 已规范化取消Context
// 返回: int 新固定文档序号, error 名称、预算或取消错误
func (w *StreamWriter) beginDocumentLocked(ctx context.Context) (int, error) {
	const pattern = "/Documents/%d/FixedDoc.fdoc"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return 0, err
	}
	if w.registry.count() >= w.limits.MaxPartCount {
		return 0, fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	if w.earlyContentTypes {
		if w.lastOpenPageRel != "" && !w.lateDictSources[strings.ToLower(w.lastOpenPageRel)] {
			if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(w.lastOpenPageRel)); err != nil {
				return 0, err
			}
			w.lastOpenPageRel = ""
		}
		if w.currentDoc >= 0 {
			prevPart := w.documents[w.currentDoc].Part
			if err := w.closePieceStreamLocked(ctx, prevPart); err != nil {
				return 0, err
			}
			if !w.lateDictSources[strings.ToLower(prevPart)] {
				if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(prevPart)); err != nil {
					return 0, err
				}
			}
		}
		ns := formatNamespace(w.format)
		docSrc, err := relativePart(w.sequence, part)
		if err != nil {
			return 0, err
		}
		refNode := createdNode(ns, "DocumentReference")
		refNode.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: docSrc}}
		refXML, err := encodeStreamChildXML(ctx, refNode, w.limits.MaxPartBytes)
		if err != nil {
			return 0, err
		}
		if err := w.appendPieceStreamLocked(ctx, w.sequence, refXML); err != nil {
			return 0, err
		}
		if err := w.openPieceStreamLocked(ctx, part, fixedContentType("fixeddocument"), `<FixedDocument xmlns="`+ns+`">`, `</FixedDocument>`); err != nil {
			return 0, err
		}
	}
	w.documents = append(w.documents, Document{Part: part})
	w.currentDoc = len(w.documents) - 1
	w.registry.register(part)
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
	w.recordRestrictedFacesLocked(part, data)
	if isCollection {
		return fmt.Sprintf("%s#%d", part, collectionIndex), nil
	}
	return part, nil
}

// recordRestrictedFacesLocked 按单个字体面粒度登记OS/2带有预览与打印限制标志的面索引
// 入参: part 规范字体部件URI, raw 原始未混淆字体字节
func (w *StreamWriter) recordRestrictedFacesLocked(part string, raw []byte) {
	partKey := strings.ToLower(part)
	for _, index := range collectRestrictedFontFaces(raw) {
		w.restrictedFaces[fontCacheKey{part: partKey, index: index}] = true
	}
}

// collectRestrictedFontFaces 扫描原始SFNT/TTC字体数据并返回带有OS/2预览与打印受限标志的面索引列表
// 入参: data 原始未混淆字体字节
// 返回: []uint32 需要标注RestrictedFont关系的字体面序号切片
func collectRestrictedFontFaces(data []byte) []uint32 {
	face, err := parseFontFace(data, 0)
	if err != nil {
		return nil
	}
	count := uint32(1)
	if face.collection {
		count = binary.BigEndian.Uint32(data[8:12])
	}
	var restricted []uint32
	for index := uint32(0); index < count; index++ {
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return restricted
			}
		}
		if os2, err := parseFontOS2Metrics(face); err == nil && os2 != nil && os2.fsType&4 != 0 {
			restricted = append(restricted, index)
		}
	}
	return restricted
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

// AddGoImage 编码Go标准图像并立即落盘至底层流，支持内容去重与MaxImagePixels像素上限控制
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
	data, media, ext, err := encodeGoImageWithLimits(ctx, img, options, w.limits.MaxPartBytes, w.maxImagePixels)
	if err != nil {
		return "", err
	}
	return w.writeDeduplicatedResourceLocked(ctx, "/Resources/Images/%d."+ext, media, data, options != nil && options.Deduplicate)
}

// AddImageFromRows 通过逐行流式回调对接jxrgo.EncodeRows直接流式写入底层ZIP，前置参数校验失败不毒死写出器
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
	if err := validateImageRowsInfoLimits(info, w.maxImagePixels); err != nil {
		return "", err
	}
	const pattern = "/Resources/Images/%d.jxr"
	const media = "image/vnd.ms-photo"
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.validateEarlyContentTypeLocked(part, media); err != nil {
		return "", err
	}
	if w.registry.count() >= w.limits.MaxPartCount {
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
	if cfg.Limits.MaxPixels == 0 || cfg.Limits.MaxPixels > w.maxImagePixels {
		cfg.Limits.MaxPixels = w.maxImagePixels
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	if err := jxrgo.EncodeRows(ctx, sink, info, read, &cfg); err != nil {
		if sink.touched {
			w.failed = err
		}
		return "", err
	}
	if err := sink.finish(); err != nil {
		if sink.touched {
			w.failed = err
		}
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

// AddResourceDictionary 编码共享远程资源字典并立即落盘，复用编码树记录其直接资源依赖供页面关系与释放提示追踪
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
	root, data, err := encodeResourceDictionaryTree(ctx, dict, &EncodeOptions{Format: w.format, Limits: w.limits, Part: part, Compact: w.compact})
	if err != nil {
		return "", err
	}
	deps, err := collectStreamNodeDependencies(part, root)
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

// AddPart 按OPC规则与[M12.8]标准媒体类型校验并立即落盘自定义或扩展部件，遇远程资源字典或字体时同步登记依赖与受限面表
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
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return err
	}
	if err := w.validateEarlyContentTypeLocked(canonical, media); err != nil {
		return err
	}
	var parsedDictDeps []streamResourceRef
	isDict := requiredResourceMedia(requiredDictionary, media)
	if isDict {
		root, err := decodeXML(data, w.limits)
		if err != nil {
			return err
		}
		ns := formatNamespace(w.format)
		root, err = preprocessXMLContext(root, []string{ns, ns + "/resourcedictionary-key"}, ctx)
		if err != nil {
			return err
		}
		if root.Name != (xml.Name{Space: ns, Local: "ResourceDictionary"}) {
			return fmt.Errorf("%w: invalid resource dictionary root element", ErrInvalid)
		}
		parsedDictDeps, err = collectStreamNodeDependencies(canonical, root)
		if err != nil {
			return err
		}
	}
	var fontRaw []byte
	if requiredResourceMedia(requiredFont, media) {
		if matchStandardContentType(FormatOpenXPS, media, "application/vnd.ms-package.obfuscated-opentype") {
			if decoded, deobfErr := DeobfuscateFont(canonical, data); deobfErr == nil {
				fontRaw = decoded
			}
		} else {
			fontRaw = data
		}
	}
	if err := w.writePartLocked(ctx, canonical, media, data, true); err != nil {
		return err
	}
	if isDict {
		w.dictDeps[strings.ToLower(canonical)] = parsedDictDeps
	}
	if len(fontRaw) != 0 {
		w.recordRestrictedFacesLocked(canonical, fontRaw)
	}
	return nil
}

// AddPage 编码单页模型并立即落盘至底层流，复用编码树消除二次解码并自动维护依赖、受限字体关系与前向交错索引
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
	if len(w.allPages) >= w.limits.MaxPageCount {
		return "", fmt.Errorf("%w: stream page count", ErrLimit)
	}
	implicitDoc := w.currentDoc < 0
	var docPart string
	var docIdx int
	if implicitDoc {
		var err error
		docPart, err = w.newNameLocked("/Documents/%d/FixedDoc.fdoc", ctx)
		if err != nil {
			return "", err
		}
		if w.registry.count()+1 >= w.limits.MaxPartCount {
			return "", fmt.Errorf("%w: stream package part count", ErrLimit)
		}
		docIdx = len(w.documents)
	} else {
		docIdx = w.currentDoc
		docPart = w.documents[docIdx].Part
	}
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
	if implicitDoc {
		probe := w.registry.clone()
		probe.register(docPart)
		if err := probe.available(part); err != nil {
			return "", err
		}
	}
	if err := w.validateEarlyContentTypeLocked(part, fixedContentType("fixedpage")); err != nil {
		return "", err
	}
	value.Part = part
	root, data, err := encodePageTree(ctx, &value, &EncodeOptions{Format: w.format, Limits: w.limits, Compact: w.compact})
	if err != nil {
		return "", err
	}
	targets, err := validateExplicitLinkTargetsForPage(w.format, w.documents, value.LinkTargets, createdPageTargets(root), docIdx, -1)
	if err != nil {
		return "", err
	}
	deps, err := collectStreamNodeDependencies(part, root)
	if err != nil {
		return "", err
	}
	expandedDeps := w.expandDependenciesRecursiveLocked(deps)
	for _, dep := range expandedDeps {
		if _, discarded := w.emittedDiscardPage[strings.ToLower(dep.part)]; discarded {
			return "", fmt.Errorf("%w: resource %s was already discarded", ErrInvalid, dep.part)
		}
	}
	if len(expandedDeps) != 0 {
		if err := w.canReserveRelationPartLocked(part); err != nil {
			return "", err
		}
		for _, dep := range expandedDeps {
			if dep.hasFace && w.restrictedFaces[fontCacheKey{part: strings.ToLower(dep.part), index: dep.faceIndex}] {
				if err := w.canReserveRelationPartLocked(docPart); err != nil {
					return "", err
				}
				break
			}
		}
	}
	if implicitDoc {
		if docIdx, err = w.beginDocumentLocked(ctx); err != nil {
			return "", err
		}
		docPart = w.documents[docIdx].Part
	}
	if w.earlyContentTypes {
		if w.lastOpenPageRel != "" && !w.lateDictSources[strings.ToLower(w.lastOpenPageRel)] {
			if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(w.lastOpenPageRel)); err != nil {
				return "", err
			}
			w.lastOpenPageRel = ""
		}
		if err := w.flushEarlyDiscardsForNextPageLocked(ctx, part, expandedDeps); err != nil {
			return "", err
		}
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("fixedpage"), data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	pageIndex := len(w.allPages)
	w.allPages = append(w.allPages, part)
	ref := PageReference{Part: part, Width: value.Width, Height: value.Height, LinkTargets: targets}
	w.documents[docIdx].Pages = append(w.documents[docIdx].Pages, ref)
	w.pageDeps = append(w.pageDeps, streamPageDeps{docPart: docPart, pagePart: part, pageIndex: pageIndex, deps: deps})
	reqType := formatNamespace(w.format) + "/required-resource"
	resType := formatNamespace(w.format) + "/restricted-font"
	hasPendingDict := false
	hasPendingFont := false
	for _, dep := range expandedDeps {
		depKey := strings.ToLower(dep.part)
		w.resourceLastPage[depKey] = pageIndex
		if err := w.appendRelationLocked(part, reqType, dep.part, false); err != nil {
			return "", err
		}
		if _, written := w.parts[depKey]; !written {
			if dep.kind == requiredDictionary {
				hasPendingDict = true
			} else if dep.kind == requiredFont {
				hasPendingFont = true
			}
		}
		if dep.hasFace && w.restrictedFaces[fontCacheKey{part: depKey, index: dep.faceIndex}] {
			if err := w.appendRelationLocked(docPart, resType, dep.part, false); err != nil {
				return "", err
			}
		}
	}
	if hasPendingDict {
		w.lateDictSources[strings.ToLower(part)] = true
		w.lateDictSources[strings.ToLower(docPart)] = true
	} else if hasPendingFont {
		w.lateDictSources[strings.ToLower(docPart)] = true
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, part); err != nil {
			return "", err
		}
		if w.openStreams[strings.ToLower(createdRelationshipPart(part))] != nil {
			w.lastOpenPageRel = part
		}
		if err := w.flushStreamRelationsLocked(ctx, docPart); err != nil {
			return "", err
		}
		pageContentNode, err := buildFixedDocumentPageContentNode(w.format, docPart, ref)
		if err != nil {
			return "", err
		}
		pageContentXML, err := encodeStreamChildXML(ctx, pageContentNode, w.limits.MaxPartBytes)
		if err != nil {
			return "", err
		}
		if err := w.appendPieceStreamLocked(ctx, docPart, pageContentXML); err != nil {
			return "", err
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

// SetCoreProperties 编码OPC核心属性并立即落盘，同时记录包根核心属性关系，重复设置返回ErrInvalid
// 入参: ctx 取消Context，nil采用Background, props 核心属性数据
// 返回: error 编码、重复设置、预算、取消或写出错误
func (w *StreamWriter) SetCoreProperties(ctx context.Context, props CoreProperties) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	if w.hasRelationLocked("/", opcCoreRel) {
		return fmt.Errorf("%w: stream core properties already set", ErrInvalid)
	}
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
	fallback := "/docProps/core%d.xml"
	if w.earlyContentTypes {
		part = "/docProps/core.psmdcp"
		fallback = "/docProps/core%d.psmdcp"
	}
	pattern := ""
	if w.availableLocked(part) != nil {
		pattern = fallback
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
	if err := w.appendRelationLocked("/", opcCoreRel, part, false); err != nil {
		return err
	}
	if w.earlyContentTypes {
		return w.flushStreamRelationsLocked(ctx, "/")
	}
	return nil
}

// SetPrintTicket 编码Framework打印票据、立即落盘并绑定至文档序列、固定文档或固定页面，同一目标重复设置返回ErrInvalid
// 入参: ctx 取消Context，nil采用Background, targetPart 目标来源部件，空字符串表示文档序列, settings 打印设置模型
// 返回: string 写入的打印票据部件URI, error 来源、重复设置、编码、预算、取消或写出错误
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
	canonical, _, err := w.validatePrintTicketTargetLocked(targetPart)
	if err != nil {
		return "", err
	}
	var buf bytes.Buffer
	if _, err := EncodePrintSettings(ctx, &buf, settings, &PrintSettingsOptions{Limits: w.limits}); err != nil {
		return "", err
	}
	return w.writeBoundPrintTicketLocked(ctx, canonical, printTicketType, buf.Bytes())
}

// SetRawPrintTicket 校验原始打印票据载荷、立即落盘并绑定至文档序列、固定文档或固定页面，OpenXPS支持自定义媒体类型与非XML票据字节
// 入参: ctx 取消Context，nil采用Background, targetPart 目标来源部件，空字符串表示文档序列, contentType 票据内容类型，空字符串默认标准PrintTicket媒体类型, data 原始票据字节
// 返回: string 写入的打印票据部件URI, error 来源、重复设置、媒体类型、XML结构、预算、取消或写出错误
func (w *StreamWriter) SetRawPrintTicket(ctx context.Context, targetPart, contentType string, data []byte) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty print ticket data", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	canonical, scope, err := w.validatePrintTicketTargetLocked(targetPart)
	if err != nil {
		return "", err
	}
	if contentType == "" {
		contentType = printTicketType
	}
	if err := validatePackageMediaForFormat(w.format, contentType); err != nil {
		return "", err
	}
	if w.format == FormatXPS && !matchStandardContentType(FormatXPS, contentType, printTicketType) {
		return "", fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)
	}
	baseType := opcMediaTypeBase(contentType)
	known, capabilities := printResourceMedia(baseType)
	if known && !capabilities {
		if int64(len(data)) > min(w.limits.MaxMetadataBytes, w.limits.MaxPartBytes) {
			return "", fmt.Errorf("%w: print ticket byte budget", ErrLimit)
		}
		cfg, err := printSettingsOptions(ctx, &PrintSettingsOptions{Limits: w.limits, Scope: scope})
		if err != nil {
			return "", err
		}
		root, err := decodeXML(data, cfg.Limits)
		if err != nil {
			return "", err
		}
		if _, err := parsePrintSettings(root, cfg); err != nil {
			return "", err
		}
		if err := xmlNamespaceTreeOutput(root, ctx); err != nil {
			return "", err
		}
	}
	return w.writeBoundPrintTicketLocked(ctx, canonical, contentType, data)
}

// validatePrintTicketTargetLocked 校验流式打印票据目标归属、单值不重复及伴生关系部件无派生冲突
// 入参: targetPart 调用方传入的目标部件，空串表示文档序列
// 返回: string 规范化目标部件URI, PrintScope 所属打印作用域, error 目标非法、重复设置或关系冲突错误
func (w *StreamWriter) validatePrintTicketTargetLocked(targetPart string) (string, PrintScope, error) {
	source := targetPart
	if source == "" {
		source = w.sequence
	}
	canonical, err := opcPartName(source)
	if err != nil {
		return "", PrintScopeUnknown, err
	}
	scope := w.partScopeLocked(canonical)
	if scope == PrintScopeUnknown {
		return "", PrintScopeUnknown, fmt.Errorf("%w: stream print ticket source is not a fixed layout part", ErrInvalid)
	}
	relType := formatNamespace(w.format) + "/printticket"
	if w.hasRelationLocked(canonical, relType) {
		return "", PrintScopeUnknown, fmt.Errorf("%w: stream print ticket already set for %s", ErrInvalid, canonical)
	}
	if err := w.canReserveRelationPartLocked(canonical); err != nil {
		return "", PrintScopeUnknown, err
	}
	return canonical, scope, nil
}

// writeBoundPrintTicketLocked 分配票据路径、落盘载荷并绑定对应目标的printticket关系
// 入参: ctx 已规范化取消Context, canonical 已校验目标来源URI, contentType 媒体类型, data 票据原始载荷
// 返回: string 写入的打印票据部件URI, error 分配、类型、预算、取消或写出错误
func (w *StreamWriter) writeBoundPrintTicketLocked(ctx context.Context, canonical, contentType string, data []byte) (string, error) {
	baseType := strings.ToLower(opcMediaTypeBase(contentType))
	pattern := "/Metadata/PrintTicket%d.xml"
	if !strings.EqualFold(baseType, printTicketType) && !strings.HasSuffix(baseType, "+xml") && baseType != "application/xml" && baseType != "text/xml" {
		pattern = "/Metadata/PrintTicket%d.bin"
	}
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, contentType, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	if err := w.appendRelationLocked(canonical, formatNamespace(w.format)+"/printticket", part, false); err != nil {
		return "", err
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, canonical); err != nil {
			return "", err
		}
		if strings.EqualFold(canonical, w.sequence) {
			if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(canonical)); err != nil {
				return "", err
			}
		}
	}
	return part, nil
}

// SetThumbnail 校验JPEG或PNG缩略图图像、立即落盘并绑定至包根或固定页面，同一目标重复设置返回ErrInvalid
// 入参: ctx 取消Context，nil采用Background, targetPart 目标来源部件，空字符串或/表示包根, data JPEG或PNG图像字节
// 返回: string 写入的缩略图部件URI, error 来源、重复设置、图像格式、解码、预算、取消或写出错误
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
	if w.hasRelationLocked(source, thumbnailRelationship) {
		return "", fmt.Errorf("%w: stream thumbnail already set for %s", ErrInvalid, source)
	}
	if err := w.canReserveRelationPartLocked(source); err != nil {
		return "", err
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
	if err := w.appendRelationLocked(source, thumbnailRelationship, part, false); err != nil {
		return "", err
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, source); err != nil {
			return "", err
		}
	}
	return part, nil
}

// SetDocumentStructure 编码指定固定文档的目录与故事结构、立即落盘并绑定documentstructure关系，关闭时终检故事页码上界，同一文档重复设置返回ErrInvalid
// 入参: ctx 取消Context，nil采用Background, docIndex 固定文档序号, structure 文档结构模型
// 返回: error 序号、重复设置、编码、预算、取消或写出错误
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
	relType := formatNamespace(w.format) + "/documentstructure"
	if w.hasRelationLocked(source, relType) {
		return fmt.Errorf("%w: stream document structure already set for %s", ErrInvalid, source)
	}
	if err := w.canReserveRelationPartLocked(source); err != nil {
		return err
	}
	maxPage := 0
	for _, story := range structure.Stories {
		for _, ref := range story.Fragments {
			if ref.PageNumber < 1 {
				return fmt.Errorf("%w: invalid story fragment page number %d", ErrInvalid, ref.PageNumber)
			}
			if ref.PageNumber > maxPage {
				maxPage = ref.PageNumber
			}
		}
	}
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
	w.docStructMaxPage[docIndex] = maxPage
	if err := w.appendRelationLocked(source, relType, part, false); err != nil {
		return err
	}
	if w.earlyContentTypes {
		return w.flushStreamRelationsLocked(ctx, source)
	}
	return nil
}

// SetStoryFragments 编码指定页面的故事片段、立即落盘并绑定storyfragments关系，同一页面重复设置返回ErrInvalid
// 入参: ctx 取消Context，nil采用Background, docIndex 文档序号, pageIndex 文档内页面序号, fragments 故事片段模型
// 返回: error 序号、重复设置、编码、预算、取消或写出错误
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
	relType := formatNamespace(w.format) + "/storyfragments"
	if w.hasRelationLocked(source, relType) {
		return fmt.Errorf("%w: stream story fragments already set for %s", ErrInvalid, source)
	}
	if err := w.canReserveRelationPartLocked(source); err != nil {
		return err
	}
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
	if err := w.appendRelationLocked(source, relType, part, false); err != nil {
		return err
	}
	if w.earlyContentTypes {
		return w.flushStreamRelationsLocked(ctx, source)
	}
	return nil
}

// Close 幂等完成流式包收尾：终检依赖与页码上界，补齐或闭合固定布局、释放提示、全部.rels与[Content_Types].xml并关闭ZIP容器
// 入参: ctx 取消Context，nil采用Background
// 返回: error 结构、依赖、编码、预算、取消或ZIP关闭错误
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

// finalizeLocked 在Close期间执行终检、展开后置字典依赖、写出或闭合剩余索引、释放提示、关系与内容类型表并关闭ZIP
// 入参: ctx 已规范化取消Context
// 返回: error 结构、依赖、页码、编码或写出错误
func (w *StreamWriter) finalizeLocked(ctx context.Context) error {
	if len(w.documents) == 0 {
		return fmt.Errorf("%w: stream package requires at least one document", ErrInvalid)
	}
	ns := formatNamespace(w.format)
	for docIdx, doc := range w.documents {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if len(doc.Pages) == 0 {
			return fmt.Errorf("%w: stream document %s requires at least one page", ErrInvalid, doc.Part)
		}
		if maxPage := w.docStructMaxPage[docIdx]; maxPage > len(doc.Pages) {
			return fmt.Errorf("%w: document %d structure story page %d exceeds page count %d", ErrInvalid, docIdx, maxPage, len(doc.Pages))
		}
	}
	reqType := ns + "/required-resource"
	resType := ns + "/restricted-font"
	for _, rec := range w.pageDeps {
		if err := checkContext(ctx); err != nil {
			return err
		}
		expanded := w.expandDependenciesRecursiveLocked(rec.deps)
		for _, dep := range expanded {
			depKey := strings.ToLower(dep.part)
			wp, exists := w.parts[depKey]
			if !exists {
				return fmt.Errorf("%w: missing referenced resource %s", ErrInvalid, dep.part)
			}
			if !requiredResourceMedia(dep.kind, wp.media) {
				return fmt.Errorf("%w: unexpected resource content type %q for %s", ErrInvalid, wp.media, dep.part)
			}
			if sentinelIdx, discarded := w.emittedDiscardPage[depKey]; discarded && rec.pageIndex >= sentinelIdx {
				return fmt.Errorf("%w: resource %s was discarded before page %s", ErrInvalid, dep.part, rec.pagePart)
			}
			if prev, seen := w.resourceLastPage[depKey]; !seen || rec.pageIndex > prev {
				w.resourceLastPage[depKey] = rec.pageIndex
			}
			if err := w.appendRelationLocked(rec.pagePart, reqType, dep.part, false); err != nil {
				return err
			}
			if dep.hasFace && w.restrictedFaces[fontCacheKey{part: depKey, index: dep.faceIndex}] {
				if err := w.appendRelationLocked(rec.docPart, resType, dep.part, false); err != nil {
					return err
				}
			}
		}
	}
	if w.earlyContentTypes {
		return w.finalizeEarlyLocked(ctx)
	}
	for _, doc := range w.documents {
		if err := checkContext(ctx); err != nil {
			return err
		}
		docRoot, err := buildFixedDocumentNode(w.format, doc)
		if err != nil {
			return err
		}
		docData, err := createdMarkup(docRoot, w.limits, ctx)
		if err != nil {
			return err
		}
		if err := w.writePartLocked(ctx, doc.Part, fixedContentType("fixeddocument"), docData, true); err != nil {
			return err
		}
	}
	sequence, err := buildFixedDocumentSequenceNode(w.format, w.sequence, w.documents)
	if err != nil {
		return err
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
		if err := w.appendRelationLocked("/", ns+"/discard-control", discardPart, false); err != nil {
			return err
		}
	}
	if err := w.prependRelationLocked("/", ns+"/fixedrepresentation", w.sequence); err != nil {
		return err
	}
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

// finalizeEarlyLocked 闭合EarlyContentTypes模式下全部打开的分片布局、释放提示与关系流并关闭ZIP容器
// 入参: ctx 已规范化取消Context
// 返回: error 编码、预算、取消或ZIP关闭错误
func (w *StreamWriter) finalizeEarlyLocked(ctx context.Context) error {
	for _, doc := range w.documents {
		if err := w.closePieceStreamLocked(ctx, doc.Part); err != nil {
			return err
		}
	}
	if err := w.closePieceStreamLocked(ctx, w.sequence); err != nil {
		return err
	}
	hints := w.buildDiscardHintsLocked()
	var remaining []DiscardHint
	for _, hint := range hints {
		if _, emitted := w.emittedDiscardPage[strings.ToLower(hint.Target)]; !emitted {
			remaining = append(remaining, hint)
		}
	}
	if len(remaining) != 0 {
		if err := w.ensureEarlyDiscardStreamLocked(ctx); err != nil {
			return err
		}
		if err := w.appendEarlyDiscardHintsLocked(ctx, remaining); err != nil {
			return err
		}
	}
	if w.discardPart != "" {
		if err := w.closePieceStreamLocked(ctx, w.discardPart); err != nil {
			return err
		}
	}
	for _, sourceKey := range slices.Sorted(maps.Keys(w.relations)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if len(w.relations[sourceKey]) == 0 {
			continue
		}
		source := w.resolveSourceCaseLocked(sourceKey)
		if err := w.flushStreamRelationsLocked(ctx, source); err != nil {
			return err
		}
		if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(source)); err != nil {
			return err
		}
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
	var bump func(part string, idx int, seen map[string]bool)
	bump = func(part string, idx int, seen map[string]bool) {
		key := strings.ToLower(part)
		if prev, exists := minLastPage[key]; !exists || idx > prev {
			minLastPage[key] = idx
		}
		if seen[key] {
			return
		}
		seen[key] = true
		for _, dep := range w.dictDeps[key] {
			bump(dep.part, idx, seen)
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
			bump(rel.Target, idx, make(map[string]bool))
		}
	}
	bump(w.sequence, lastPageIdx, make(map[string]bool))
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
		bump(doc.Part, docLast, make(map[string]bool))
		bumpRelations(doc.Part, docLast, true)
	}
	for idx, pagePart := range w.allPages {
		bump(pagePart, idx, make(map[string]bool))
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

// writePartLocked 校验媒体类型、前置类型表、派生路径冲突与字节预算后将单个逻辑部件立即写入ZIP流并登记轻量元数据
// 入参: ctx 取消Context, part 已规范化部件URI, media 内容类型, data 部件字节, allowInterleave 是否允许按InterleaveBytes分片
// 返回: error 类型、冲突、预算、取消或写出错误
func (w *StreamWriter) writePartLocked(ctx context.Context, part, media string, data []byte, allowInterleave bool) error {
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return err
	}
	if err := w.validateEarlyContentTypeLocked(part, media); err != nil {
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
	if !w.registry.has(part) {
		if err := w.registry.available(part); err != nil {
			return err
		}
		if w.registry.count() >= w.limits.MaxPartCount {
			return fmt.Errorf("%w: stream package part count", ErrLimit)
		}
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
	w.registry.register(part)
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

// writeZIPPayloadLocked 写入单个物理ZIP条目，复用共享writeZIPBufferEntry支持Store、Deflate与无损Optimize压缩模式
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
	return writeZIPBufferEntry(ctx, w.archive, header, data, w.compression, w.optimizer, &w.candidate, w.copyBuf)
}

// Write 接收流式编码器输出的字节块，按整部件直写或定长分片落盘至底层ZIP流，落盘后方置touched标志
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
			s.touched = true
			out, err := s.writer.archive.CreateHeader(&header)
			if err != nil {
				return 0, err
			}
			s.direct = out
		}
		s.touched = true
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
			s.touched = true
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
			s.touched = true
			return s.writer.writeZIPPayloadLocked(s.ctx, strings.TrimPrefix(s.part, "/"), nil)
		}
		return nil
	}
	if s.writer.interleaveBytes == 0 {
		data := s.buf.Bytes()
		s.touched = true
		err := s.writer.writeZIPPayloadLocked(s.ctx, strings.TrimPrefix(s.part, "/"), data)
		s.buf.Reset()
		return err
	}
	name := strings.TrimPrefix(s.part, "/") + "/[" + strconv.Itoa(s.pieceIdx) + "].last.piece"
	data := s.buf.Bytes()
	s.touched = true
	err := s.writer.writeZIPPayloadLocked(s.ctx, name, data)
	s.buf.Reset()
	return err
}

// collectStreamNodeDependencies 统一复用resourceAttributeReferences扫描FixedPage或ResourceDictionary树收集直接资源依赖及字体面索引
// 入参: sourcePart 当前XML所属规范部件URI, root XML根节点
// 返回: []streamResourceRef 去重后的规范资源引用切片, error URI或引用语法错误
func collectStreamNodeDependencies(sourcePart string, root *xmlElement) ([]streamResourceRef, error) {
	type depKey struct {
		part      string
		kind      requiredResourceKind
		faceIndex uint32
		hasFace   bool
	}
	seen := make(map[depKey]bool)
	var result []streamResourceRef
	var walk func(*xmlElement) error
	walk = func(node *xmlElement) error {
		if node == nil {
			return nil
		}
		for _, attr := range node.Attr {
			refs, err := resourceAttributeReferences(node, attr)
			if err != nil {
				return err
			}
			var faceIndex uint32
			hasFace := false
			if node.Name.Local == "Glyphs" && attr.Name == (xml.Name{Local: "FontUri"}) && (node.Name.Space == xpsNamespace || node.Name.Space == openXPSNamespace) {
				_, idx, _, err := ParseFontURI(strings.Trim(attr.Value, " \t\r\n"))
				if err != nil {
					return err
				}
				faceIndex, hasFace = idx, true
			}
			for _, ref := range refs {
				target, err := resolvePart(sourcePart, ref.uri)
				if err != nil {
					return err
				}
				entry := streamResourceRef{part: target, kind: ref.kind}
				if ref.kind == requiredFont && hasFace {
					entry.faceIndex, entry.hasFace = faceIndex, true
				}
				key := depKey{part: strings.ToLower(target), kind: entry.kind, faceIndex: entry.faceIndex, hasFace: entry.hasFace}
				if !seen[key] {
					seen[key] = true
					result = append(result, entry)
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

// expandDependenciesRecursiveLocked 递归展开页面或远程字典的全部传递资源依赖并防环去重
// 入参: direct 直接资源引用列表
// 返回: []streamResourceRef 展开去重后的完整依赖列表
func (w *StreamWriter) expandDependenciesRecursiveLocked(direct []streamResourceRef) []streamResourceRef {
	type depKey struct {
		part      string
		kind      requiredResourceKind
		faceIndex uint32
		hasFace   bool
	}
	seen := make(map[depKey]bool, len(direct))
	visitedDict := make(map[string]bool)
	result := make([]streamResourceRef, 0, len(direct))
	queue := make([]streamResourceRef, 0, len(direct))
	enqueue := func(ref streamResourceRef) {
		key := depKey{part: strings.ToLower(ref.part), kind: ref.kind, faceIndex: ref.faceIndex, hasFace: ref.hasFace}
		if !seen[key] {
			seen[key] = true
			result = append(result, ref)
			if ref.kind == requiredDictionary {
				queue = append(queue, ref)
			}
		}
	}
	for _, dep := range direct {
		enqueue(dep)
	}
	for len(queue) != 0 {
		cur := queue[0]
		queue = queue[1:]
		dictKey := strings.ToLower(cur.part)
		if visitedDict[dictKey] {
			continue
		}
		visitedDict[dictKey] = true
		for _, sub := range w.dictDeps[dictKey] {
			enqueue(sub)
		}
	}
	return result
}

// earlyStreamDefaultTypes 按OPC§10.1.2.2返回指定方言全部标准扩展名的默认内容类型映射表
// 入参: format 文档方言
// 返回: map[string]string 小写扩展名到无参数标准内容类型的映射
func earlyStreamDefaultTypes(format Format) map[string]string {
	defaults := map[string]string{
		"rels":    opcRelsType,
		"fdseq":   fixedContentType("fixeddocumentsequence"),
		"fdoc":    fixedContentType("fixeddocument"),
		"fpage":   fixedContentType("fixedpage"),
		"dict":    resourceDictionaryContentType,
		"struct":  fixedContentType("documentstructure"),
		"frag":    fixedContentType("storyfragments"),
		"discard": fixedContentType("discard-control"),
		"xml":     printTicketType,
		"psmdcp":  opcCoreType,
		"png":     "image/png",
		"jpg":     "image/jpeg",
		"jpeg":    "image/jpeg",
		"tif":     "image/tiff",
		"tiff":    "image/tiff",
		"wdp":     "image/vnd.ms-photo",
		"jxr":     "image/vnd.ms-photo",
		"hdp":     "image/vnd.ms-photo",
		"ttf":     "application/vnd.ms-opentype",
		"otf":     "application/vnd.ms-opentype",
		"ttc":     "application/vnd.ms-opentype",
		"odttf":   "application/vnd.ms-package.obfuscated-opentype",
		"odttc":   "application/vnd.ms-package.obfuscated-opentype",
		"icc":     "application/vnd.ms-color.iccprofile",
		"icm":     "application/vnd.ms-color.iccprofile",
	}
	if format != FormatXPS {
		defaults["x3d"] = "model/x3d+xml"
		defaults["x3db"] = "model/x3d+binary"
	}
	return defaults
}

// validateEarlyContentTypeLocked 校验EarlyContentTypes模式下目标部件扩展名与预声明Default类型完全一致
// 入参: part 已规范化部件URI, media 目标内容类型
// 返回: error 扩展名缺失、未预声明或内容类型冲突错误
func (w *StreamWriter) validateEarlyContentTypeLocked(part, media string) error {
	if !w.earlyContentTypes || strings.EqualFold(part, opcTypesName) {
		return nil
	}
	segment := part[strings.LastIndexByte(part, '/')+1:]
	dot := strings.LastIndexByte(segment, '.')
	if dot < 0 || dot == len(segment)-1 {
		return fmt.Errorf("%w: part %s has no extension for early [Content_Types].xml", ErrInvalid, part)
	}
	ext := strings.ToLower(segment[dot+1:])
	expected, exists := w.earlyDefaults[ext]
	if !exists {
		return fmt.Errorf("%w: extension %q of %s is not declared in early [Content_Types].xml", ErrUnsupported, ext, part)
	}
	if !strings.EqualFold(media, expected) {
		return fmt.Errorf("%w: part %s content type %q conflicts with early default %q", ErrInvalid, part, media, expected)
	}
	return nil
}

// initEarlyStreamLocked 在EarlyContentTypes模式下于流最前端写出[Content_Types].xml并打开包根关系、可选释放提示与文档序列分片流
// 入参: ctx 已规范化取消Context
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) initEarlyStreamLocked(ctx context.Context) error {
	w.earlyDefaults = earlyStreamDefaultTypes(w.format)
	typesRoot := createdNode(opcTypesNS, "Types")
	for _, ext := range slices.Sorted(maps.Keys(w.earlyDefaults)) {
		child := createdNode(opcTypesNS, "Default")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "Extension"}, Value: ext}, {Name: xml.Name{Local: "ContentType"}, Value: w.earlyDefaults[ext]}}
		typesRoot.Children = append(typesRoot.Children, child)
	}
	typesData, err := createdMarkup(typesRoot, w.limits, ctx)
	if err != nil {
		return err
	}
	if err := w.writeRawEntryLocked(ctx, opcTypesName, typesData, false); err != nil {
		w.failed = err
		return err
	}
	ns := formatNamespace(w.format)
	if err := w.appendRelationLocked("/", ns+"/fixedrepresentation", w.sequence, false); err != nil {
		return err
	}
	if w.autoDiscard {
		if err := w.ensureEarlyDiscardStreamLocked(ctx); err != nil {
			return err
		}
	} else if err := w.flushStreamRelationsLocked(ctx, "/"); err != nil {
		return err
	}
	return w.openPieceStreamLocked(ctx, w.sequence, fixedContentType("fixeddocumentsequence"), `<FixedDocumentSequence xmlns="`+ns+`">`, `</FixedDocumentSequence>`)
}

// ensureEarlyDiscardStreamLocked 在EarlyContentTypes模式下按需打开/DiscardControl.discard分片流并刷出包根关系
// 入参: ctx 已规范化取消Context
// 返回: error 命名、关系、预算或写出错误
func (w *StreamWriter) ensureEarlyDiscardStreamLocked(ctx context.Context) error {
	if w.discardPart != "" {
		return nil
	}
	discardPart := "/DiscardControl.discard"
	if w.availableLocked(discardPart) != nil {
		var err error
		discardPart, err = w.newNameLocked("/DiscardControl%d.discard", ctx)
		if err != nil {
			return err
		}
	}
	if w.registry.count() >= w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	ns := formatNamespace(w.format)
	w.discardPart = discardPart
	w.registry.register(discardPart)
	if err := w.appendRelationLocked("/", ns+"/discard-control", discardPart, false); err != nil {
		return err
	}
	if err := w.flushStreamRelationsLocked(ctx, "/"); err != nil {
		return err
	}
	return w.openPieceStreamLocked(ctx, discardPart, fixedContentType("discard-control"), `<DiscardControl xmlns="`+ns+`/discard-control">`, `</DiscardControl>`)
}

// appendEarlyDiscardHintsLocked 将一批释放提示元素作为交错分片立即追加至已打开的DiscardControl分片流
// 入参: ctx 已规范化取消Context, hints 待追加释放提示列表
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) appendEarlyDiscardHintsLocked(ctx context.Context, hints []DiscardHint) error {
	if len(hints) == 0 {
		return nil
	}
	ns := formatNamespace(w.format) + "/discard-control"
	var buf bytes.Buffer
	for _, hint := range hints {
		node := createdNode(ns, "Discard")
		node.Attr = []xml.Attr{{Name: xml.Name{Local: "SentinelPage"}, Value: hint.SentinelPage}, {Name: xml.Name{Local: "Target"}, Value: hint.Target}}
		chunk, err := encodeStreamChildXML(ctx, node, w.limits.MaxPartBytes)
		if err != nil {
			return err
		}
		buf.Write(chunk)
	}
	return w.appendPieceStreamLocked(ctx, w.discardPart, buf.Bytes())
}

// flushEarlyDiscardsForNextPageLocked 在EarlyContentTypes模式下对已显式ReleaseResource且不受新页及全局关系保护的资源立即落盘Discard分片
// 入参: ctx 已规范化取消Context, sentinelPage 即将落盘的新页面URI, nextPageDeps 新页面展开依赖集合
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) flushEarlyDiscardsForNextPageLocked(ctx context.Context, sentinelPage string, nextPageDeps []streamResourceRef) error {
	if len(w.releasedAfter) == 0 {
		return nil
	}
	nextUsed := make(map[string]bool, len(nextPageDeps))
	for _, dep := range nextPageDeps {
		nextUsed[strings.ToLower(dep.part)] = true
	}
	protected := make(map[string]bool)
	ns := formatNamespace(w.format)
	restrictedRel := ns + "/restricted-font"
	discardRel := ns + "/discard-control"
	markProtected := func(source string, skipRestricted bool) {
		for _, rel := range w.relations[strings.ToLower(source)] {
			if rel.TargetMode != "" && rel.TargetMode != TargetModeInternal {
				continue
			}
			if rel.Type == discardRel || skipRestricted && rel.Type == restrictedRel {
				continue
			}
			protected[strings.ToLower(rel.Target)] = true
		}
	}
	protected[strings.ToLower(w.sequence)] = true
	if w.discardPart != "" {
		protected[strings.ToLower(w.discardPart)] = true
	}
	markProtected("/", false)
	markProtected(w.sequence, false)
	for _, doc := range w.documents {
		protected[strings.ToLower(doc.Part)] = true
		markProtected(doc.Part, true)
		for _, page := range doc.Pages {
			protected[strings.ToLower(page.Part)] = true
		}
	}
	nextPageIdx := len(w.allPages)
	var ready []DiscardHint
	for _, key := range slices.Sorted(maps.Keys(w.releasedAfter)) {
		if _, emitted := w.emittedDiscardPage[key]; emitted {
			continue
		}
		if w.releasedAfter[key] >= nextPageIdx || nextUsed[key] || protected[key] {
			continue
		}
		part, exists := w.parts[key]
		if !exists {
			continue
		}
		ready = append(ready, DiscardHint{Target: part.name, SentinelPage: sentinelPage})
	}
	if len(ready) == 0 {
		return nil
	}
	if err := w.ensureEarlyDiscardStreamLocked(ctx); err != nil {
		return err
	}
	if err := w.appendEarlyDiscardHintsLocked(ctx, ready); err != nil {
		return err
	}
	for _, hint := range ready {
		w.emittedDiscardPage[strings.ToLower(hint.Target)] = nextPageIdx
	}
	return nil
}

// openPieceStreamLocked 在底层ZIP打开OPC分片XML部件并写入[0].piece起始片
// 入参: ctx 已规范化取消Context, part 规范化部件URI, media 内容类型, opening 起始XML内容, closing 闭合XML尾标签
// 返回: error 冲突、类型、预算、取消或写出错误
func (w *StreamWriter) openPieceStreamLocked(ctx context.Context, part, media, opening, closing string) error {
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return err
	}
	if err := w.validateEarlyContentTypeLocked(part, media); err != nil {
		return err
	}
	key := strings.ToLower(part)
	if _, exists := w.parts[key]; exists {
		return fmt.Errorf("%w: duplicate stream part %s", ErrInvalid, part)
	}
	if _, open := w.openStreams[key]; open {
		return fmt.Errorf("%w: duplicate open stream part %s", ErrInvalid, part)
	}
	if !w.registry.has(part) {
		if err := w.registry.available(part); err != nil {
			return err
		}
		if w.registry.count() >= w.limits.MaxPartCount {
			return fmt.Errorf("%w: stream package part count", ErrLimit)
		}
	}
	raw := []byte(opening)
	maxPart := w.limits.MaxPartBytes
	if opcRelationshipName(part) {
		maxPart = min(maxPart, w.limits.MaxMetadataBytes)
	}
	if int64(len(raw)) > maxPart {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if int64(len(raw)) > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	entryName := strings.TrimPrefix(part, "/") + "/[0].piece"
	if err := w.writeZIPPayloadLocked(ctx, entryName, raw); err != nil {
		w.failed = err
		return err
	}
	w.registry.register(part)
	w.partBytes += int64(len(raw))
	w.openStreams[key] = &streamOpenPart{part: part, media: media, pieceIdx: 1, bytes: int64(len(raw)), closing: closing}
	return nil
}

// appendPieceStreamLocked 向已打开的OPC分片XML部件追加下一序号分片
// 入参: ctx 已规范化取消Context, part 规范化部件URI, chunk 追加XML片段字节
// 返回: error 状态、预算、取消或写出错误
func (w *StreamWriter) appendPieceStreamLocked(ctx context.Context, part string, chunk []byte) error {
	if len(chunk) == 0 {
		return nil
	}
	stream := w.openStreams[strings.ToLower(part)]
	if stream == nil || stream.closed {
		return fmt.Errorf("%w: stream part %s is not open", ErrInvalid, part)
	}
	maxPart := w.limits.MaxPartBytes
	if opcRelationshipName(part) {
		maxPart = min(maxPart, w.limits.MaxMetadataBytes)
	}
	if int64(len(chunk)) > maxPart-stream.bytes {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if int64(len(chunk)) > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	entryName := strings.TrimPrefix(stream.part, "/") + "/[" + strconv.Itoa(stream.pieceIdx) + "].piece"
	if err := w.writeZIPPayloadLocked(ctx, entryName, chunk); err != nil {
		w.failed = err
		return err
	}
	stream.pieceIdx++
	stream.bytes += int64(len(chunk))
	w.partBytes += int64(len(chunk))
	return nil
}

// closePieceStreamLocked 向已打开的OPC分片XML部件写出最终.last.piece闭合片并登记逻辑元数据
// 入参: ctx 已规范化取消Context, part 规范化部件URI
// 返回: error 预算、取消或写出错误
func (w *StreamWriter) closePieceStreamLocked(ctx context.Context, part string) error {
	key := strings.ToLower(part)
	stream := w.openStreams[key]
	if stream == nil || stream.closed {
		return nil
	}
	raw := []byte(stream.closing)
	maxPart := w.limits.MaxPartBytes
	if opcRelationshipName(stream.part) {
		maxPart = min(maxPart, w.limits.MaxMetadataBytes)
	}
	if int64(len(raw)) > maxPart-stream.bytes {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if int64(len(raw)) > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	entryName := strings.TrimPrefix(stream.part, "/") + "/[" + strconv.Itoa(stream.pieceIdx) + "].last.piece"
	if err := w.writeZIPPayloadLocked(ctx, entryName, raw); err != nil {
		w.failed = err
		return err
	}
	stream.closed = true
	stream.bytes += int64(len(raw))
	w.partBytes += int64(len(raw))
	w.parts[key] = streamWrittenPart{name: stream.part, media: stream.media}
	return nil
}

// flushStreamRelationsLocked 在EarlyContentTypes模式下将指定源新增尚未落盘的关系条目标记作为分片立即写入ZIP流
// 入参: ctx 已规范化取消Context, source 规范源部件URI或/
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) flushStreamRelationsLocked(ctx context.Context, source string) error {
	sourceKey := strings.ToLower(source)
	rels := w.relations[sourceKey]
	sent := w.emittedRelCount[sourceKey]
	if sent >= len(rels) {
		return nil
	}
	var buf bytes.Buffer
	for _, rel := range rels[sent:] {
		child := createdNode(opcRelsNS, "Relationship")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "Id"}, Value: rel.ID}, {Name: xml.Name{Local: "Type"}, Value: rel.Type}, {Name: xml.Name{Local: "Target"}, Value: rel.Target}}
		if rel.TargetMode != "" {
			child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "TargetMode"}, Value: string(rel.TargetMode)})
		}
		chunk, err := encodeStreamChildXML(ctx, child, w.limits.MaxMetadataBytes)
		if err != nil {
			return err
		}
		buf.Write(chunk)
	}
	relPart := createdRelationshipPart(source)
	relKey := strings.ToLower(relPart)
	if w.openStreams[relKey] == nil {
		if err := w.openPieceStreamLocked(ctx, relPart, opcRelsType, `<Relationships xmlns="`+opcRelsNS+`">`+buf.String(), `</Relationships>`); err != nil {
			return err
		}
	} else if err := w.appendPieceStreamLocked(ctx, relPart, buf.Bytes()); err != nil {
		return err
	}
	w.emittedRelCount[sourceKey] = len(rels)
	return nil
}

// encodeStreamChildXML 将单个标准子元素编码为继承父级默认命名空间的UTF-8 XML片段
// 入参: ctx 已规范化取消Context, node 目标子元素节点, maxBytes 输出字节上限
// 返回: []byte XML元素片段字节, error 编码、预算或取消错误
func encodeStreamChildXML(ctx context.Context, node *xmlElement, maxBytes int64) ([]byte, error) {
	var buf bytes.Buffer
	if _, err := writeEncodedXMLNode(ctx, &buf, node, maxBytes); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// canReserveRelationPartLocked 预检源部件对应伴生.rels路径是否尚未闭合、无OPC M1.11派生冲突且满足部件数量上限
// 入参: source 源部件URI或/
// 返回: error 已闭合、派生路径冲突或部件上限错误
func (w *StreamWriter) canReserveRelationPartLocked(source string) error {
	relPart := createdRelationshipPart(source)
	if stream := w.openStreams[strings.ToLower(relPart)]; stream != nil && stream.closed {
		return fmt.Errorf("%w: stream relationships for %s already finalized", ErrInvalid, source)
	}
	if w.registry.has(relPart) {
		return nil
	}
	if err := w.registry.available(relPart); err != nil {
		return err
	}
	if w.registry.count() >= w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	return nil
}

// reserveRelationPartLocked 首次为源部件建立关系时强制校验无OPC M1.11派生冲突并登记伴生.rels路径
// 入参: source 源部件URI或/
// 返回: error 已闭合、派生路径冲突或部件上限错误
func (w *StreamWriter) reserveRelationPartLocked(source string) error {
	if err := w.canReserveRelationPartLocked(source); err != nil {
		return err
	}
	w.registry.register(createdRelationshipPart(source))
	return nil
}

// hasRelationLocked 检查指定源部件是否已存在给定类型的关系
// 入参: source 源部件URI或/, relType 关系类型URI
// 返回: bool 是否已存在该类型关系
func (w *StreamWriter) hasRelationLocked(source, relType string) bool {
	for _, rel := range w.relations[strings.ToLower(source)] {
		if rel.Type == relType {
			return true
		}
	}
	return false
}

// appendRelationLocked 为指定源部件校验并预订伴生.rels路径后追加内部关系，若已存在相同类型与目标则跳过重复记录
// 入参: source 源部件URI或/, relType 关系类型URI, target 目标部件URI, allowDuplicate 是否允许重复相同目标
// 返回: error 伴生关系部件派生冲突或部件数量上限错误
func (w *StreamWriter) appendRelationLocked(source, relType, target string, allowDuplicate bool) error {
	key := strings.ToLower(source)
	rels := w.relations[key]
	if !allowDuplicate {
		for _, rel := range rels {
			if rel.Type == relType && strings.EqualFold(rel.Target, target) {
				return nil
			}
		}
	}
	if err := w.reserveRelationPartLocked(source); err != nil {
		return err
	}
	nextID := createdRelationshipIDs(rels)
	w.relations[key] = append(rels, Relationship{ID: nextID(), Type: relType, Target: target, TargetMode: TargetModeInternal})
	return nil
}

// prependRelationLocked 在源部件关系列表首位插入固定布局主入口关系并校验预订伴生.rels路径
// 入参: source 源部件URI或/, relType 关系类型URI, target 目标部件URI
// 返回: error 伴生关系部件派生冲突或部件数量上限错误
func (w *StreamWriter) prependRelationLocked(source, relType, target string) error {
	if err := w.reserveRelationPartLocked(source); err != nil {
		return err
	}
	key := strings.ToLower(source)
	rels := w.relations[key]
	nextID := createdRelationshipIDs(rels)
	head := Relationship{ID: nextID(), Type: relType, Target: target, TargetMode: TargetModeInternal}
	w.relations[key] = append([]Relationship{head}, rels...)
	return nil
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
	if name := resolveLayoutPartName(w.sequence, w.documents, sourceKey); name != "" {
		return name
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

// availableLocked 检查部件URI是否未与已有名称或祖先/后代路径冲突，并禁止关系保留名
// 入参: part 已规范化部件URI
// 返回: error 名称冲突错误
func (w *StreamWriter) availableLocked(part string) error {
	if opcRelationshipName(part) {
		return fmt.Errorf("%w: stream part name collision %s", ErrInvalid, part)
	}
	return w.registry.available(part)
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
