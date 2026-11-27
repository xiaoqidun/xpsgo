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
	"crypto/sha256"
	"encoding/binary"
	"encoding/xml"
	"fmt"
	"image"
	"io"
	"maps"
	"math"
	"net/url"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/xiaoqidun/jxrgo"
)

const (
	// StreamColorUnknown 表示未指定逐行流式图像色彩模型
	StreamColorUnknown StreamImageColorModel = iota
	// StreamColorGray 表示每像素单通道灰度（8或16位，16位按大端字节序）
	StreamColorGray
	// StreamColorGrayAlpha 表示每像素灰度加非预乘Alpha双通道（8或16位，16位按大端字节序）
	StreamColorGrayAlpha
	// StreamColorRGB 表示每像素红绿蓝三通道（8或16位，16位按大端字节序）
	StreamColorRGB
	// StreamColorRGBA 表示每像素非预乘红绿蓝加Alpha四通道（8或16位，16位按大端字节序）
	StreamColorRGBA
	// StreamColorCMYK 表示每像素青品黄黑四通道（8或16位，16位按大端字节序，仅TIFF支持）
	StreamColorCMYK
	// StreamColorBilevel 表示1位MSB优先打包黑白二值位图（每行ceil(Width/8)字节，0为白1为黑，仅TIFF支持）
	StreamColorBilevel
)

// streamEarlyAutoPieceBytes 定义EarlyContentTypes且未显式分片的Deflate流式图像自动分片字节数以消除尾条挂起
const streamEarlyAutoPieceBytes = 64 << 10

// StreamImageColorModel 表示逐行流式图像写入时的像素色彩模型
type StreamImageColorModel uint8

// StreamImageRowOptions 设置逐行流式PNG与多Strip TIFF图像写入的尺寸、位深、色彩模型、分辨率、可选ICC配置及TIFF压缩方式
// BitDepth为零时按ColorModel取默认值（StreamColorBilevel为1，其余为8）；16位多字节样本统一按大端字节序排列
type StreamImageRowOptions struct {
	Width           int
	Height          int
	BitDepth        int
	ColorModel      StreamImageColorModel
	DPIX            float64
	DPIY            float64
	ICCProfile      []byte
	TIFFCompression TIFFCompression
}

// StreamWriteOptions 设置前向流式写出器的压缩策略、交错分片大小、自动释放提示、前置内容类型表、紧凑编码、资源预算与固定时间戳
// InterleaveBytes为零时按整部件直接落盘，非零时按至多8MiB分片交错落盘；AutoDiscard启用后按页生命周期自动生成DiscardControl
// EarlyContentTypes启用后在流起始即写入[Content_Types].xml并以交错分片增量推进索引、关系与释放提示，供ConsumeStream实时逐页交付
// EarlyExcludePrintTicket启用后前置Default表不预声明xml打印票据类型，使无票据包在StreamTicketsStrict下零阻塞实时交付
// EarlyDefaultTypes允许在EarlyContentTypes下扩展或覆写前置Default扩展名到媒体类型映射，Compact启用后使用紧凑属性编码
type StreamWriteOptions struct {
	Compression             Compression
	InterleaveBytes         int64
	AutoDiscard             bool
	EarlyContentTypes       bool
	EarlyExcludePrintTicket bool
	EarlyDefaultTypes       map[string]string
	Compact                 bool
	Limits                  Limits
	MaxImagePixels          uint64
	FixedTime               time.Time
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

// streamNavRef 记录页面内声明的NavigateUri引用及其来源固定页面URI，供Close阶段终检存在性
type streamNavRef struct {
	sourcePart string
	target     string
}

// streamStoryFragmentRef 记录DocumentStructure中单条StoryFragmentReference元数据，供Close阶段交叉终检
type streamStoryFragmentRef struct {
	storyName    string
	pageNumber   int
	fragmentName *string
}

// streamDocStructInfo 记录已写入DocumentStructure的大纲目标与故事索引元数据，供Close阶段交叉终检
type streamDocStructInfo struct {
	part           string
	storyNames     map[string]bool
	storyRefs      []streamStoryFragmentRef
	outlineTargets []string
}

// streamPageStoryFragment 记录StoryFragments中单个StoryFragment的故事与片段标识
type streamPageStoryFragment struct {
	storyName    *string
	fragmentName *string
}

// streamPageStoryInfo 记录已写入页面StoryFragments的片段标识与命名元素引用列表，供Close阶段交叉终检
type streamPageStoryInfo struct {
	part      string
	fragments []streamPageStoryFragment
	namedRefs []string
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

// StreamJXRImageWriter 提供面向StreamWriter的推式JPEG XR逐行图像写入句柄，使用完毕须调用Close提交至底层流
type StreamJXRImageWriter struct {
	writer  *StreamWriter
	part    string
	pattern string
	media   string
	sink    *streamPieceSink
	enc     *jxrgo.RowEncoder
	closed  bool
}

// StreamPNGImageWriter 提供面向StreamWriter的推式PNG逐行图像写入句柄，使用完毕须调用Close提交至底层流
type StreamPNGImageWriter struct {
	writer   *StreamWriter
	part     string
	pattern  string
	media    string
	rowBytes int
	sink     *streamPieceSink
	enc      *pngRowEncoder
	closed   bool
}

// streamDeferredFont 保存已预登记待后置非紧凑子集化落盘的延迟字体原始字节、字形缓存及累计用字集合
type streamDeferredFont struct {
	part        string
	media       string
	obfuscate   bool
	data        []byte
	usedGlyphs  map[uint32]map[uint16]bool
	faceMetrics map[uint32]*fontMetrics
	faceCmaps   map[uint32]*fontCmap
	subsettable map[uint32]bool
	flushed     bool
}

// streamPreparedFont 保存字体许可校验、可选单面提取、去重检查与部件分配后的共享准备结果
type streamPreparedFont struct {
	data            []byte
	media           string
	pattern         string
	part            string
	uri             string
	digest          [32]byte
	restrictedFaces []uint32
	obfuscate       bool
	isCollection    bool
	deduplicated    bool
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
	needObfFaces       map[fontCacheKey]bool
	prohibitedFaces    map[fontCacheKey]bool
	dictDeps           map[string][]streamResourceRef
	dictNavRefs        map[string][]string
	pageDeps           []streamPageDeps
	pageNames          map[string]map[string]bool
	pageNavRefs        []streamNavRef
	docStructures      map[int]*streamDocStructInfo
	pageStories        map[string]*streamPageStoryInfo
	resourceLastPage   map[string]int
	releasedAfter      map[string]int
	openStreams        map[string]*streamOpenPart
	emittedRelCount    map[string]int
	emittedDiscardPage map[string]int
	lateDictSources    map[string]bool
	pendingDicts       map[string]bool
	openPageRels       map[string]string
	deferredFonts      map[string]*streamDeferredFont
	signatureSpotIDs   map[string]bool
	activeStreamPart   string
	discardPart        string
	partBytes          int64
	entryCount         int
	closed             bool
	closeErr           error
	failed             error
	optimizer          *flate.Writer
	deflater           *flate.Writer
	candidate          compressionBuffer
	copyBuf            []byte
}

// String 返回逐行流式图像色彩模型的可读名称
// 返回: string 色彩模型名称
func (m StreamImageColorModel) String() string {
	switch m {
	case StreamColorUnknown:
		return "unknown"
	case StreamColorGray:
		return "gray"
	case StreamColorGrayAlpha:
		return "grayalpha"
	case StreamColorRGB:
		return "rgb"
	case StreamColorRGBA:
		return "rgba"
	case StreamColorCMYK:
		return "cmyk"
	case StreamColorBilevel:
		return "bilevel"
	default:
		return fmt.Sprintf("StreamImageColorModel(%d)", m)
	}
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
		cfg.EarlyExcludePrintTicket = options.EarlyExcludePrintTicket
		cfg.EarlyDefaultTypes = options.EarlyDefaultTypes
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
	var earlyDefaults map[string]string
	if cfg.EarlyContentTypes {
		var err error
		earlyDefaults, err = earlyStreamDefaultTypes(format, cfg.EarlyExcludePrintTicket, cfg.EarlyDefaultTypes)
		if err != nil {
			return nil, err
		}
	}
	sw := &StreamWriter{
		format:             format,
		limits:             cfg.Limits,
		maxImagePixels:     cfg.MaxImagePixels,
		compression:        cfg.Compression,
		interleaveBytes:    cfg.InterleaveBytes,
		autoDiscard:        cfg.AutoDiscard,
		earlyContentTypes:  cfg.EarlyContentTypes,
		earlyDefaults:      earlyDefaults,
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
		needObfFaces:       make(map[fontCacheKey]bool),
		prohibitedFaces:    make(map[fontCacheKey]bool),
		dictDeps:           make(map[string][]streamResourceRef),
		dictNavRefs:        make(map[string][]string),
		pageNames:          make(map[string]map[string]bool),
		docStructures:      make(map[int]*streamDocStructInfo),
		pageStories:        make(map[string]*streamPageStoryInfo),
		resourceLastPage:   make(map[string]int),
		releasedAfter:      make(map[string]int),
		openStreams:        make(map[string]*streamOpenPart),
		emittedRelCount:    make(map[string]int),
		emittedDiscardPage: make(map[string]int),
		lateDictSources:    make(map[string]bool),
		pendingDicts:       make(map[string]bool),
		openPageRels:       make(map[string]string),
		deferredFonts:      make(map[string]*streamDeferredFont),
		signatureSpotIDs:   make(map[string]bool),
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
			if sw.deflater != nil {
				_ = sw.deflater.Close()
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

// BeginDocument 在当前流式包中开启新的固定文档并将其设为后续AddPage的默认目标文档，EarlyContentTypes模式下自动闭合上一文档与就绪页面关系分片流
// 入参: ctx 取消Context，nil采用Background
// 返回: int 新固定文档的零基序号, error 状态、名称、类型、预算、取消或写出错误
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

// beginDocumentLocked 在持有互斥锁时分配并开启新固定文档，EarlyContentTypes模式下预检预算并同步推进分片流
// 入参: ctx 已规范化取消Context
// 返回: int 新固定文档序号, error 名称、类型、预算、取消或写出错误
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
		if err := w.validateEarlyContentTypeLocked(part, fixedContentType("fixeddocument")); err != nil {
			return 0, err
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
		opening := `<FixedDocument xmlns="` + ns + `">`
		if err := w.checkAppendStreamBudgetLocked(w.sequence, int64(len(refXML))); err != nil {
			return 0, err
		}
		if int64(len(opening)) > w.limits.MaxPartBytes {
			return 0, fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
		}
		extraBytes := int64(len(refXML)) + int64(len(opening)) + w.pendingReadyPageRelClosingBytesLocked()
		if w.currentDoc >= 0 {
			prevPart := w.documents[w.currentDoc].Part
			extraBytes += w.streamClosingBytesLocked(prevPart)
			if !w.lateDictSources[strings.ToLower(prevPart)] {
				extraBytes += w.streamClosingBytesLocked(createdRelationshipPart(prevPart))
			}
		}
		if extraBytes > w.limits.MaxPackageBytes-w.partBytes {
			return 0, fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
		}
		if err := w.closeReadyPageRelsLocked(ctx); err != nil {
			return 0, w.failLocked(err)
		}
		if w.currentDoc >= 0 {
			prevPart := w.documents[w.currentDoc].Part
			if err := w.closePieceStreamLocked(ctx, prevPart); err != nil {
				return 0, w.failLocked(err)
			}
			if !w.lateDictSources[strings.ToLower(prevPart)] {
				if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(prevPart)); err != nil {
					return 0, w.failLocked(err)
				}
			}
		}
		if err := w.appendPieceStreamLocked(ctx, w.sequence, refXML); err != nil {
			return 0, w.failLocked(err)
		}
		if err := w.openPieceStreamLocked(ctx, part, fixedContentType("fixeddocument"), opening, `</FixedDocument>`); err != nil {
			return 0, w.failLocked(err)
		}
	}
	w.documents = append(w.documents, Document{Part: part})
	w.currentDoc = len(w.documents) - 1
	w.registry.register(part)
	w.commitNameLocked(pattern, part)
	return w.currentDoc, nil
}

// EndPage 在EarlyContentTypes模式下显式闭合当前及先前无待定远程字典的页面.fpage.rels分片流并刷新底层缓冲，推动下游零延迟交付与回收
// 入参: ctx 取消Context，nil采用Background
// 返回: error 状态、预算、取消或写出错误
func (w *StreamWriter) EndPage(ctx context.Context) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	if !w.earlyContentTypes {
		return nil
	}
	if err := w.flushResolvedLateSourcesLocked(ctx); err != nil {
		return w.failLocked(err)
	}
	if err := w.closeReadyPageRelsLocked(ctx); err != nil {
		return w.failLocked(err)
	}
	return w.failLocked(w.archive.Flush())
}

// EndDocument 显式结束当前活动固定文档，在EarlyContentTypes模式下立即闭合就绪页面关系、当前.fdoc及其.fdoc.rels分片流并刷新底层缓冲
// 入参: ctx 取消Context，nil采用Background
// 返回: error 文档无页、状态、预算、取消或写出错误
func (w *StreamWriter) EndDocument(ctx context.Context) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	if w.currentDoc < 0 {
		return nil
	}
	doc := w.documents[w.currentDoc]
	if len(doc.Pages) == 0 {
		return fmt.Errorf("%w: stream document %s requires at least one page", ErrInvalid, doc.Part)
	}
	if err := w.flushDeferredFontsLocked(ctx, true); err != nil {
		return w.failLocked(err)
	}
	if w.earlyContentTypes {
		if err := w.flushResolvedLateSourcesLocked(ctx); err != nil {
			return w.failLocked(err)
		}
		if err := w.closeReadyPageRelsLocked(ctx); err != nil {
			return w.failLocked(err)
		}
		if err := w.closePieceStreamLocked(ctx, doc.Part); err != nil {
			return w.failLocked(err)
		}
		if !w.lateDictSources[strings.ToLower(doc.Part)] {
			if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(doc.Part)); err != nil {
				return w.failLocked(err)
			}
		}
		if err := w.archive.Flush(); err != nil {
			return w.failLocked(err)
		}
	}
	w.currentDoc = -1
	return nil
}

// AddFont 校验字体嵌入许可后按唯一GUID路径混淆并立即落盘至底层流
// 入参: ctx 取消Context，nil采用Background, data 原始OpenType或TrueType字体字节
// 返回: string 混淆字体的包根URI, error 格式、许可、取消或写出错误
func (w *StreamWriter) AddFont(ctx context.Context, data []byte) (string, error) {
	return w.AddFontWithOptions(ctx, data, nil)
}

// AddFontWithOptions 按指定选项校验许可、可选单面提取、去重与混淆嵌入字体并立即落盘，整份TTC/OTC集合返回带#index的FontUri
// 入参: ctx 取消Context，nil采用Background, data 原始字体字节, options 嵌入选项，nil默认混淆
// 返回: string 字体部件URI，保留集合封装时附加#index片段, error 格式、许可、索引、取消或写出错误
func (w *StreamWriter) AddFontWithOptions(ctx context.Context, data []byte, options *AddFontOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	prep, err := w.prepareEmbeddedFontLocked(ctx, data, options, true)
	if err != nil {
		return "", err
	}
	if prep.deduplicated {
		return prep.uri, nil
	}
	payload := prep.data
	if prep.obfuscate {
		payload, err = ObfuscateFont(prep.part, prep.data)
		if err != nil {
			return "", err
		}
	}
	if err := w.writePartLocked(ctx, prep.part, prep.media, payload, true); err != nil {
		return "", err
	}
	w.commitNameLocked(prep.pattern, prep.part)
	w.recordHashLocked(prep.digest, prep.part, prep.media, len(prep.data))
	w.recordRestrictedFaceIndicesLocked(prep.part, prep.restrictedFaces)
	return prep.uri, nil
}

// RegisterDeferredFont 预登记字体以延迟至ReleaseResource后的EndDocument或Close阶段执行非紧凑子集化落盘，保持已写入页面的GID索引不变
// 禁止嵌入、需混淆未混淆或含矢量轮廓的纯位图限制字体会立即返回ErrRestricted；带NoSubsetting标志或非子集化格式会在落盘时保留原字体字节
// 入参: ctx 取消Context，nil采用Background, data 原始OpenType/TrueType或TTC/OTC字体字节, options 嵌入与单面提取选项，nil默认混淆
// 返回: string 预分配的字体部件URI，保留集合封装时附加#index片段, error 格式、许可、索引、取消或资源错误
func (w *StreamWriter) RegisterDeferredFont(ctx context.Context, data []byte, options *AddFontOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	prep, err := w.prepareEmbeddedFontLocked(ctx, data, options, false)
	if err != nil {
		return "", err
	}
	if err := validatePackageMediaForFormat(w.format, prep.media); err != nil {
		return "", err
	}
	if err := w.validateEarlyContentTypeLocked(prep.part, prep.media); err != nil {
		return "", err
	}
	if w.registry.count() >= w.limits.MaxPartCount {
		return "", fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	owned := bytes.Clone(prep.data)
	df, err := buildStreamDeferredFont(owned, prep.part, prep.media, prep.obfuscate, prep.isCollection)
	if err != nil {
		return "", err
	}
	w.registry.register(prep.part)
	w.commitNameLocked(prep.pattern, prep.part)
	w.recordRestrictedFaceIndicesLocked(prep.part, prep.restrictedFaces)
	w.deferredFonts[strings.ToLower(prep.part)] = df
	return prep.uri, nil
}

// prepareEmbeddedFontLocked 在持有互斥锁时完成字体选项解析、许可校验、可选单面提取、可选哈希去重与部件URI分配
// 入参: ctx 已规范化取消Context, data 原始字体字节, options 嵌入选项, allowDeduplicate 是否计算内容哈希并按选项尝试去重
// 返回: streamPreparedFont 共享字体准备结果, error 格式、许可、索引、取消或名称分配错误
func (w *StreamWriter) prepareEmbeddedFontLocked(ctx context.Context, data []byte, options *AddFontOptions, allowDeduplicate bool) (streamPreparedFont, error) {
	obfuscate := true
	deduplicate := false
	collectionIndex := 0
	extractFace := false
	if options != nil {
		if options.Obfuscate != nil {
			obfuscate = *options.Obfuscate
		}
		deduplicate = allowDeduplicate && options.Deduplicate
		collectionIndex = options.CollectionIndex
		extractFace = options.ExtractCollectionFace
	}
	isCollection, isCFF, err := validateEmbeddedFontDataWithPolicy(ctx, data, w.limits.MaxPartBytes, obfuscate, collectionIndex, extractFace)
	if err != nil {
		return streamPreparedFont{}, err
	}
	if isCollection && extractFace {
		extracted, faceCFF, extractErr := extractCollectionFaceSFNT(ctx, data, uint32(collectionIndex), w.limits.MaxPartBytes)
		if extractErr != nil {
			return streamPreparedFont{}, extractErr
		}
		data = extracted
		isCollection = false
		isCFF = faceCFF
	}
	restrictedFaces, err := collectRestrictedFontFaces(data)
	if err != nil {
		return streamPreparedFont{}, err
	}
	media, pattern := embeddedFontMediaAndPattern(obfuscate, isCollection, isCFF)
	formatURI := func(part string) string {
		if isCollection {
			return fmt.Sprintf("%s#%d", part, collectionIndex)
		}
		return part
	}
	var digest [32]byte
	if allowDeduplicate {
		digest = sha256.Sum256(data)
		if deduplicate {
			if existing, found := w.findHashLocked(digest, media, len(data)); found {
				return streamPreparedFont{uri: formatURI(existing), deduplicated: true}, nil
			}
		}
	}
	var part string
	if obfuscate {
		part, err = w.newFontPartLocked()
	} else {
		part, err = w.newNameLocked(pattern, ctx)
	}
	if err != nil {
		return streamPreparedFont{}, err
	}
	return streamPreparedFont{
		data:            data,
		media:           media,
		pattern:         pattern,
		part:            part,
		uri:             formatURI(part),
		digest:          digest,
		restrictedFaces: restrictedFaces,
		obfuscate:       obfuscate,
		isCollection:    isCollection,
	}, nil
}

// buildStreamDeferredFont 预解析延迟字体的各面度量、cmap与子集化资格，供AddPage增量收集引用GID
// 入参: data 独立原始字体字节, part 预分配部件URI, media 内容类型, obfuscate 是否混淆, isCollection 是否为集合
// 返回: *streamDeferredFont 延迟字体状态, error 字体解析错误
func buildStreamDeferredFont(data []byte, part, media string, obfuscate, isCollection bool) (*streamDeferredFont, error) {
	count := uint32(1)
	if isCollection {
		count = binary.BigEndian.Uint32(data[8:12])
	}
	df := &streamDeferredFont{
		part:        part,
		media:       media,
		obfuscate:   obfuscate,
		data:        data,
		usedGlyphs:  make(map[uint32]map[uint16]bool, count),
		faceMetrics: make(map[uint32]*fontMetrics, count),
		faceCmaps:   make(map[uint32]*fontCmap, count),
		subsettable: make(map[uint32]bool, count),
	}
	for index := uint32(0); index < count; index++ {
		face, err := parseFontFace(data, index)
		if err != nil {
			return nil, err
		}
		metrics, err := parseFontMetrics(face)
		if err != nil {
			return nil, err
		}
		df.faceMetrics[index] = metrics
		if cmapRaw, err := face.table("cmap"); err == nil {
			if parsed, cmapErr := parseFontCmap(cmapRaw, uint32(metrics.numGlyphs)); cmapErr == nil {
				df.faceCmaps[index] = parsed
			}
		}
		canSubset := !isCollection && !fontIsBitmapOnly(face)
		if canSubset && metrics.os2 != nil {
			if rights, rErr := fontEmbeddingRights(metrics.os2); rErr != nil || rights&0x302 != 0 {
				canSubset = false
			}
		}
		if canSubset {
			for _, unsupported := range []string{"CFF2", "fvar", "gvar", "COLR", "CPAL", "SVG "} {
				if _, has := face.tables[unsupported]; has {
					canSubset = false
					break
				}
			}
		}
		df.subsettable[index] = canSubset
	}
	return df, nil
}

// recordDeferredFontGlyphsLocked 扫描页面或远程资源字典XML中的Glyphs元素，增量记录其对已注册延迟字体的GID使用集合
// 入参: sourcePart 所属页面或远程字典部件URI, root XML根节点
func (w *StreamWriter) recordDeferredFontGlyphsLocked(sourcePart string, root *xmlElement) {
	if len(w.deferredFonts) == 0 || root == nil {
		return
	}
	var walk func(*xmlElement)
	walk = func(node *xmlElement) {
		if node == nil {
			return
		}
		if node.Name.Local == "Glyphs" && (node.Name.Space == xpsNamespace || node.Name.Space == openXPSNamespace) {
			if rawURI, ok := node.attribute("FontUri"); ok {
				uri, faceIdx, _, err := ParseFontURI(strings.Trim(rawURI, " \t\r\n"))
				if err == nil {
					if fontPart, rErr := resolvePart(sourcePart, uri); rErr == nil {
						if df := w.deferredFonts[strings.ToLower(fontPart)]; df != nil && !df.flushed {
							collectDeferredGlyphsFromNode(df, faceIdx, node)
						}
					}
				}
			}
		}
		for _, child := range node.Children {
			walk(child)
		}
	}
	walk(root)
}

// collectDeferredGlyphsFromNode 从单个Glyphs节点解析显式Indices或经UnicodeString查cmap收集目标字体面的引用GID
// 入参: df 延迟字体状态, faceIdx 字体面索引, node Glyphs元素节点
func collectDeferredGlyphsFromNode(df *streamDeferredFont, faceIdx uint32, node *xmlElement) {
	metrics := df.faceMetrics[faceIdx]
	if metrics == nil {
		return
	}
	used := df.usedGlyphs[faceIdx]
	if used == nil {
		used = map[uint16]bool{0: true}
		df.usedGlyphs[faceIdx] = used
	}
	text, _ := node.attribute("UnicodeString")
	if strings.HasPrefix(text, "{}") {
		text = text[2:]
	}
	var indices []GlyphCluster
	if rawIndices, has := node.attribute("Indices"); has && strings.TrimSpace(rawIndices) != "" {
		if parsed, err := ParseGlyphIndices(rawIndices); err == nil {
			indices = parsed
		}
	}
	g := &Glyphs{Text: text, Indices: indices, FontRenderingEmSize: 1}
	cmap := df.faceCmaps[faceIdx]
	var lookup func(rune) (uint16, error)
	if cmap != nil {
		lookup = cmap.unicodeGlyph
	}
	if _, err := glyphRunCount(g, 1<<20); err == nil {
		_ = walkGlyphRun(g, func(entry GlyphIndex, r rune, _, _, _ int) error {
			gid, gErr := glyphRunIndex(entry, r, metrics.numGlyphs, lookup)
			if gErr == nil {
				used[gid] = true
			}
			return nil
		})
		return
	}
	for _, cluster := range indices {
		for _, entry := range cluster.Glyphs {
			if entry.HasIndex && entry.Index < metrics.numGlyphs {
				used[entry.Index] = true
			}
		}
	}
	if cmap != nil {
		for _, r := range text {
			if gid, err := cmap.unicodeGlyph(r); err == nil && gid < metrics.numGlyphs {
				used[gid] = true
			}
		}
	}
}

// flushDeferredFontsLocked 将符合条件的延迟字体执行非紧凑子集化并落盘写入底层ZIP，随后立即释放原始字体内存
// 入参: ctx 已规范化取消Context, releasedOnly 为true时仅落盘已显式ReleaseResource释放的延迟字体
// 返回: error 子集化、混淆、预算、取消或写出错误
func (w *StreamWriter) flushDeferredFontsLocked(ctx context.Context, releasedOnly bool) error {
	if len(w.deferredFonts) == 0 {
		return nil
	}
	for _, key := range slices.Sorted(maps.Keys(w.deferredFonts)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		df := w.deferredFonts[key]
		if df == nil || df.flushed {
			continue
		}
		if releasedOnly {
			if _, released := w.releasedAfter[key]; !released {
				continue
			}
		}
		outBytes := df.data
		if df.subsettable[0] {
			glyphSet := df.usedGlyphs[0]
			glyphs := make([]uint16, 0, max(1, len(glyphSet)))
			if len(glyphSet) == 0 {
				glyphs = append(glyphs, 0)
			} else {
				for _, gid := range slices.Sorted(maps.Keys(glyphSet)) {
					glyphs = append(glyphs, gid)
				}
			}
			subset, subErr := SubsetFont(ctx, df.data, glyphs, &FontSubsetOptions{
				MaxBytes:         w.limits.MaxPartBytes,
				AllowMissingCmap: true,
				CompactGIDs:      false,
			})
			if subErr == nil && len(subset) > 0 && len(subset) <= len(outBytes) {
				outBytes = subset
			} else if subErr != nil && ctx.Err() != nil {
				return ctx.Err()
			}
		}
		payload := outBytes
		if df.obfuscate {
			obf, err := ObfuscateFont(df.part, outBytes)
			if err != nil {
				return err
			}
			payload = obf
		}
		if err := w.writePartLocked(ctx, df.part, df.media, payload, true); err != nil {
			return err
		}
		df.flushed = true
		df.data = nil
		df.faceMetrics = nil
		df.faceCmaps = nil
		df.usedGlyphs = nil
	}
	return nil
}

// recordRestrictedFaceIndicesLocked 按预扫描结果登记OS/2带有预览与打印限制标志的面索引
// 入参: part 规范字体部件URI, indices 需要标注RestrictedFont关系的面序号切片
func (w *StreamWriter) recordRestrictedFaceIndicesLocked(part string, indices []uint32) {
	partKey := strings.ToLower(part)
	for _, index := range indices {
		w.restrictedFaces[fontCacheKey{part: partKey, index: index}] = true
	}
}

// recordFontFaceGuardsLocked 登记通过AddPart写入的多面集合字体中单面需混淆或禁止嵌入的面索引，供页面引用时精准拦截
// 入参: part 规范字体部件URI, needObf 需要混淆嵌入的面索引切片, prohibited 禁止嵌入的面索引切片
func (w *StreamWriter) recordFontFaceGuardsLocked(part string, needObf, prohibited []uint32) {
	partKey := strings.ToLower(part)
	for _, index := range needObf {
		w.needObfFaces[fontCacheKey{part: partKey, index: index}] = true
	}
	for _, index := range prohibited {
		w.prohibitedFaces[fontCacheKey{part: partKey, index: index}] = true
	}
}

// validateStreamAddedFontPart 校验经AddPart直接写入的字体封装、全部面OS/2表及嵌入许可
// 单面字体严格复用validateEmbeddedFontDataWithPolicy立即拦截禁止嵌入与未混淆限制，多面TTC逐面核验结构并放行至少含一合法可用面的集合
// 入参: ctx 已规范化取消Context, data 原始未混淆字体字节, maxBytes 字节上限, obfuscated 是否以混淆媒体类型写入
// 返回: []uint32 需标RestrictedFont的面索引, []uint32 未混淆时需混淆的面索引, []uint32 禁止嵌入的面索引, error 封装、许可、预算或取消错误
func validateStreamAddedFontPart(ctx context.Context, data []byte, maxBytes int64, obfuscated bool) ([]uint32, []uint32, []uint32, error) {
	if err := checkContext(ctx); err != nil {
		return nil, nil, nil, err
	}
	if len(data) == 0 {
		return nil, nil, nil, fmt.Errorf("%w: empty font data", ErrInvalid)
	}
	if int64(len(data)) > maxBytes {
		return nil, nil, nil, fmt.Errorf("%w: font byte budget", ErrLimit)
	}
	firstFace, err := parseFontFace(data, 0)
	if err != nil {
		return nil, nil, nil, err
	}
	if !firstFace.collection {
		if _, _, err := validateEmbeddedFontDataWithPolicy(ctx, data, maxBytes, obfuscated, 0, false); err != nil {
			return nil, nil, nil, err
		}
		restricted, err := collectRestrictedFontFaces(data)
		return restricted, nil, nil, err
	}
	count := binary.BigEndian.Uint32(data[8:12])
	var restricted []uint32
	var needObf []uint32
	var prohibited []uint32
	usable := 0
	for index := uint32(0); index < count; index++ {
		if err := checkContext(ctx); err != nil {
			return nil, nil, nil, err
		}
		face := firstFace
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return nil, nil, nil, err
			}
		}
		os2, err := parseFontOS2Metrics(face)
		if err != nil {
			return nil, nil, nil, err
		}
		if os2 == nil {
			return nil, nil, nil, fmt.Errorf("%w: producer font needs OS/2", ErrInvalid)
		}
		rights, err := fontEmbeddingRights(os2)
		if err != nil {
			return nil, nil, nil, err
		}
		if rights&4 != 0 {
			restricted = append(restricted, index)
		}
		if rights&2 != 0 || rights&0x200 != 0 && fontFaceHasVectorOutline(face) {
			prohibited = append(prohibited, index)
			continue
		}
		if !obfuscated && rights&0x30c != 0 {
			needObf = append(needObf, index)
			continue
		}
		usable++
	}
	if usable == 0 {
		if len(prohibited) != 0 {
			return nil, nil, nil, fmt.Errorf("%w: font prohibits embedding", ErrRestricted)
		}
		return nil, nil, nil, fmt.Errorf("%w: font requires obfuscation", ErrRestricted)
	}
	return restricted, needObf, prohibited, nil
}

// collectRestrictedFontFaces 扫描原始SFNT/TTC字体数据并按fontEmbeddingRights语义返回带有预览与打印受限标志的面索引列表
// 入参: data 原始未混淆字体字节
// 返回: []uint32 需要标注RestrictedFont关系的字体面序号切片, error 字体解析或OS/2标志错误
func collectRestrictedFontFaces(data []byte) ([]uint32, error) {
	face, err := parseFontFace(data, 0)
	if err != nil {
		return nil, err
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
				return nil, err
			}
		}
		os2, err := parseFontOS2Metrics(face)
		if err != nil {
			return nil, err
		}
		if os2 == nil {
			continue
		}
		rights, err := fontEmbeddingRights(os2)
		if err != nil {
			return nil, err
		}
		if rights&4 != 0 {
			restricted = append(restricted, index)
		}
	}
	return restricted, nil
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
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return "", err
	}
	var cfg jxrgo.EncodeOptions
	if options != nil {
		cfg = *options
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

// AddPNGFromRows 通过逐行扫描回调将图像直接流式编码为标准PNG并写入底层ZIP流，仅占用单扫描行与zlib窗口内存
// 入参: ctx 取消Context，nil采用Background, options 图像尺寸、位深、色彩模型、分辨率与ICC配置, readRow 按零基行号填充单行原始像素的回调，16位样本按大端字节序
// 返回: string 图像部件URI, error 参数、回调、编码、预算、取消或写出错误
func (w *StreamWriter) AddPNGFromRows(ctx context.Context, options StreamImageRowOptions, readRow func(y int, dst []byte) error) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if readRow == nil {
		return "", fmt.Errorf("%w: missing PNG row reader", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	dpix, dpiy, bitDepth, colorType, rowBytes, err := validateStreamPNGRowOptions(ctx, options, w.maxImagePixels)
	if err != nil {
		return "", err
	}
	const pattern = "/Resources/Images/%d.png"
	const media = "image/png"
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return "", err
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	if err := encodePNGFromValidatedRowsTo(ctx, sink, options, dpix, dpiy, bitDepth, colorType, rowBytes, readRow); err != nil {
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

// AddTIFFFromRows 通过逐行扫描回调将图像按多Strip编码为Little-Endian Baseline TIFF并写入底层ZIP流
// 无压缩模式采用恒定单条带内存直接前向流式落盘，压缩模式逐条带压缩并直写流式通道，落盘前失败不毒化写出器
// 入参: ctx 取消Context，nil采用Background, options 图像尺寸、位深、色彩模型、压缩方式、分辨率与ICC配置, readRow 按零基行号填充单行原始像素的回调，16位样本按大端字节序
// 返回: string 图像部件URI, error 参数、回调、编码、预算、取消或写出错误
func (w *StreamWriter) AddTIFFFromRows(ctx context.Context, options StreamImageRowOptions, readRow func(y int, dst []byte) error) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if readRow == nil {
		return "", fmt.Errorf("%w: missing TIFF row reader", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	spec, rowBytes, err := validateStreamTIFFRowOptions(ctx, options, w.maxImagePixels)
	if err != nil {
		return "", err
	}
	const pattern = "/Resources/Images/%d.tif"
	const media = "image/tiff"
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return "", err
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	if err := encodeTIFFFromValidatedRowsTo(ctx, sink, spec, rowBytes, maxPart, readRow); err != nil {
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

// BeginJXRImage 打开一个推式JPEG XR逐行图像写入句柄并直接对接jxrgo.NewRowEncoder写入底层ZIP流
// 句柄打开期间不得交错调用宿主StreamWriter的其他写方法，全部像素行写入后须调用Close提交部件元数据
// 入参: ctx 取消Context，nil采用Background, info JPEG XR图像头信息, options JPEG XR编码选项，nil采用默认值
// 返回: *StreamJXRImageWriter 推式行流图像写入句柄, error 参数、预算、取消或初始化错误
func (w *StreamWriter) BeginJXRImage(ctx context.Context, info jxrgo.Info, options *jxrgo.EncodeOptions) (*StreamJXRImageWriter, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := w.lock(ctx); err != nil {
		return nil, err
	}
	defer w.mu.Unlock()
	if err := validateImageRowsInfoLimits(info, w.maxImagePixels); err != nil {
		return nil, err
	}
	const pattern = "/Resources/Images/%d.jxr"
	const media = "image/vnd.ms-photo"
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return nil, err
	}
	var cfg jxrgo.EncodeOptions
	if options != nil {
		cfg = *options
	}
	if cfg.MaxOutputBytes == 0 || cfg.MaxOutputBytes > uint64(maxPart) {
		cfg.MaxOutputBytes = uint64(maxPart)
	}
	if cfg.Limits.MaxPixels == 0 || cfg.Limits.MaxPixels > w.maxImagePixels {
		cfg.Limits.MaxPixels = w.maxImagePixels
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	enc, err := jxrgo.NewRowEncoder(ctx, sink, info, &cfg)
	if err != nil {
		if sink.touched {
			w.failed = err
		}
		return nil, err
	}
	sink.ctx = nil
	w.activeStreamPart = part
	return &StreamJXRImageWriter{writer: w, part: part, pattern: pattern, media: media, sink: sink, enc: enc}, nil
}

// Part 返回推式JPEG XR图像写入句柄对应的规范部件URI
// 返回: string 图像部件URI
func (h *StreamJXRImageWriter) Part() string {
	if h == nil {
		return ""
	}
	return h.part
}

// Info 返回底层JPEG XR行编码器的目标图像头信息
// 返回: jxrgo.Info 图像头信息
func (h *StreamJXRImageWriter) Info() jxrgo.Info {
	if h == nil || h.enc == nil {
		return jxrgo.Info{}
	}
	return h.enc.Info()
}

// RowStep 返回每次行写入推进的像素行数
// 返回: int 单步推进像素行数
func (h *StreamJXRImageWriter) RowStep() int {
	if h == nil || h.enc == nil {
		return 0
	}
	return h.enc.RowStep()
}

// WrittenRows 返回已提交给底层JPEG XR编码器的累计像素行数
// 返回: int 已写入像素行数
func (h *StreamJXRImageWriter) WrittenRows() int {
	if h == nil || h.enc == nil {
		return 0
	}
	return h.enc.WrittenRows()
}

// runWrite 在互斥锁保护下为推式JPEG XR句柄绑定本次调用Context并执行编码写入操作
// 入参: ctx 取消Context，nil采用Background, fn 实际调用RowEncoder的闭包
// 返回: error 状态、编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) runWrite(ctx context.Context, fn func(context.Context) error) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if h == nil || h.writer == nil || h.enc == nil {
		return fmt.Errorf("%w: nil stream JXR image writer", ErrInvalid)
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed || h.writer.closed {
		return ErrClosed
	}
	if h.writer.failed != nil {
		return h.writer.failed
	}
	h.sink.ctx = ctx
	h.writer.counted.context = ctx
	h.writer.archive.context = ctx
	defer func() {
		h.sink.ctx = nil
	}()
	if err := fn(ctx); err != nil {
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	return nil
}

// WriteRow 向推式JPEG XR图像句柄写入一行或一个步长的通用栅格像素
// 入参: ctx 取消Context，nil采用Background, src 源栅格行缓冲
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRow(ctx context.Context, src *jxrgo.Raster) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRow(c, src) })
}

// WriteRowNRGBA 向推式JPEG XR图像句柄写入一行8位非预乘RGBA像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowNRGBA(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowNRGBA(c, src) })
}

// WriteRowNRGBA64 向推式JPEG XR图像句柄写入一行16位大端非预乘RGBA像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowNRGBA64(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowNRGBA64(c, src) })
}

// WriteRowGray 向推式JPEG XR图像句柄写入一行8位灰度像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowGray(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowGray(c, src) })
}

// WriteRowGray16 向推式JPEG XR图像句柄写入一行16位大端灰度像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowGray16(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowGray16(c, src) })
}

// WriteRowCMYK 向推式JPEG XR图像句柄写入一行8位CMYK像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowCMYK(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowCMYK(c, src) })
}

// WriteRowCMYKAlpha 向推式JPEG XR图像句柄写入一行8位CMYK加分离Alpha像素
// 入参: ctx 取消Context，nil采用Background, cmyk 行CMYK字节切片, alpha 行Alpha字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowCMYKAlpha(ctx context.Context, cmyk, alpha []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowCMYKAlpha(c, cmyk, alpha) })
}

// WriteRowRGB 向推式JPEG XR图像句柄写入一行24位紧凑RGB像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowRGB(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowRGB(c, src) })
}

// WriteRowRGBA 向推式JPEG XR图像句柄写入一行8位预乘RGBA像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowRGBA(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowRGBA(c, src) })
}

// WriteRowRGBA64 向推式JPEG XR图像句柄写入一行16位大端预乘RGBA像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowRGBA64(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowRGBA64(c, src) })
}

// WriteRowBlackWhite 向推式JPEG XR图像句柄写入一行1位MSB优先黑白像素
// 入参: ctx 取消Context，nil采用Background, src 打包位图行字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowBlackWhite(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowBlackWhite(c, src) })
}

// WriteRowCMYK16 向推式JPEG XR图像句柄写入一行16位大端CMYK像素
// 入参: ctx 取消Context，nil采用Background, src 行像素字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowCMYK16(ctx context.Context, src []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowCMYK16(c, src) })
}

// WriteRowCMYK16Alpha 向推式JPEG XR图像句柄写入一行16位大端CMYK加分离16位Alpha像素
// 入参: ctx 取消Context，nil采用Background, cmyk 行CMYK字节切片, alpha 行Alpha字节切片
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) WriteRowCMYK16Alpha(ctx context.Context, cmyk, alpha []byte) error {
	return h.runWrite(ctx, func(c context.Context) error { return h.enc.WriteRowCMYK16Alpha(c, cmyk, alpha) })
}

// Close 幂等完成JPEG XR推式编码器刷写、闭合ZIP分片通道并向宿主StreamWriter提交部件元数据
// 入参: ctx 取消Context，nil采用Background
// 返回: error 编码、预算、取消或写出错误
func (h *StreamJXRImageWriter) Close(ctx context.Context) error {
	ctx = normalizeContext(ctx)
	if h == nil || h.writer == nil {
		return fmt.Errorf("%w: nil stream JXR image writer", ErrInvalid)
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed {
		return nil
	}
	h.closed = true
	if h.writer.activeStreamPart == h.part {
		h.writer.activeStreamPart = ""
	}
	if h.writer.closed {
		return ErrClosed
	}
	if h.writer.failed != nil {
		return h.writer.failed
	}
	h.sink.ctx = ctx
	h.writer.counted.context = ctx
	h.writer.archive.context = ctx
	defer func() {
		h.sink.ctx = nil
	}()
	if err := h.enc.CloseContext(ctx); err != nil {
		h.enc = nil
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	h.enc = nil
	if err := h.sink.finish(); err != nil {
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	h.writer.registerPartMetaLocked(h.part, h.media, h.sink.written)
	h.writer.commitNameLocked(h.pattern, h.part)
	return nil
}

// Abort 幂等中止推式JPEG XR图像写入句柄并释放活跃锁；未触碰底层ZIP流时不毒化宿主StreamWriter，已落盘部分数据时标记宿主失败
// 返回: error 恒返回nil
func (h *StreamJXRImageWriter) Abort() error {
	if h == nil || h.writer == nil {
		return nil
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed {
		return nil
	}
	h.closed = true
	if h.writer.activeStreamPart == h.part {
		h.writer.activeStreamPart = ""
	}
	h.enc = nil
	if h.sink != nil {
		h.sink.buf.Reset()
		h.sink.finalized = true
		if h.sink.touched {
			h.writer.failLocked(fmt.Errorf("%w: streaming JXR image %s aborted after partial write", ErrInvalid, h.part))
		}
	}
	return nil
}

// BeginPNGImage 打开一个推式PNG逐行图像写入句柄并直接流式写入底层ZIP流
// 句柄打开期间不得交错调用宿主StreamWriter的其他写方法，全部像素行写入后须调用Close提交部件元数据
// 入参: ctx 取消Context，nil采用Background, options PNG尺寸、位深、色彩模型、分辨率与ICC配置
// 返回: *StreamPNGImageWriter 推式PNG图像写入句柄, error 参数、预算、取消或初始化错误
func (w *StreamWriter) BeginPNGImage(ctx context.Context, options StreamImageRowOptions) (*StreamPNGImageWriter, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := w.lock(ctx); err != nil {
		return nil, err
	}
	defer w.mu.Unlock()
	dpix, dpiy, bitDepth, colorType, rowBytes, err := validateStreamPNGRowOptions(ctx, options, w.maxImagePixels)
	if err != nil {
		return nil, err
	}
	const pattern = "/Resources/Images/%d.png"
	const media = "image/png"
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return nil, err
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	enc, err := newPNGRowEncoder(ctx, sink, options.Width, options.Height, uint8(bitDepth), colorType, dpix, dpiy, options.ICCProfile)
	if err != nil {
		if sink.touched {
			w.failed = err
		}
		return nil, err
	}
	sink.ctx = nil
	w.activeStreamPart = part
	return &StreamPNGImageWriter{writer: w, part: part, pattern: pattern, media: media, rowBytes: rowBytes, sink: sink, enc: enc}, nil
}

// Part 返回推式PNG图像写入句柄对应的规范部件URI
// 返回: string 图像部件URI
func (h *StreamPNGImageWriter) Part() string {
	if h == nil {
		return ""
	}
	return h.part
}

// RowBytes 返回单扫描行期望的原始像素字节长度
// 返回: int 单行字节长度
func (h *StreamPNGImageWriter) RowBytes() int {
	if h == nil {
		return 0
	}
	return h.rowBytes
}

// WrittenRows 返回已写入的累计像素行数
// 返回: int 已写入像素行数
func (h *StreamPNGImageWriter) WrittenRows() int {
	if h == nil || h.enc == nil {
		return 0
	}
	return h.enc.rows
}

// WriteRow 向推式PNG图像句柄写入单行原始像素数据，16位样本须按大端字节序排列
// 入参: ctx 取消Context，nil采用Background, row 单行原始像素字节切片
// 返回: error 行长、状态、预算、取消或写出错误
func (h *StreamPNGImageWriter) WriteRow(ctx context.Context, row []byte) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if h == nil || h.writer == nil || h.enc == nil {
		return fmt.Errorf("%w: nil stream PNG image writer", ErrInvalid)
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed || h.writer.closed {
		return ErrClosed
	}
	if h.writer.failed != nil {
		return h.writer.failed
	}
	h.sink.ctx = ctx
	h.writer.counted.context = ctx
	h.writer.archive.context = ctx
	defer func() {
		h.sink.ctx = nil
	}()
	if err := h.enc.writeRow(ctx, row); err != nil {
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	return nil
}

// Close 幂等完成PNG推式编码器刷写、闭合ZIP分片通道并向宿主StreamWriter提交部件元数据
// 入参: ctx 取消Context，nil采用Background
// 返回: error 行数不足、预算、取消或写出错误
func (h *StreamPNGImageWriter) Close(ctx context.Context) error {
	ctx = normalizeContext(ctx)
	if h == nil || h.writer == nil {
		return fmt.Errorf("%w: nil stream PNG image writer", ErrInvalid)
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed {
		return nil
	}
	h.closed = true
	if h.writer.activeStreamPart == h.part {
		h.writer.activeStreamPart = ""
	}
	if h.writer.closed {
		return ErrClosed
	}
	if h.writer.failed != nil {
		return h.writer.failed
	}
	h.sink.ctx = ctx
	h.writer.counted.context = ctx
	h.writer.archive.context = ctx
	defer func() {
		h.sink.ctx = nil
	}()
	if err := h.enc.close(ctx); err != nil {
		h.enc = nil
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	h.enc = nil
	if err := h.sink.finish(); err != nil {
		if h.sink.touched {
			h.writer.failed = err
		}
		return err
	}
	h.writer.registerPartMetaLocked(h.part, h.media, h.sink.written)
	h.writer.commitNameLocked(h.pattern, h.part)
	return nil
}

// Abort 幂等中止推式PNG图像写入句柄并释放活跃锁；未触碰底层ZIP流时不毒化宿主StreamWriter，已落盘部分数据时标记宿主失败
// 返回: error 恒返回nil
func (h *StreamPNGImageWriter) Abort() error {
	if h == nil || h.writer == nil {
		return nil
	}
	h.writer.mu.Lock()
	defer h.writer.mu.Unlock()
	if h.closed {
		return nil
	}
	h.closed = true
	if h.writer.activeStreamPart == h.part {
		h.writer.activeStreamPart = ""
	}
	if h.enc != nil {
		h.enc.closed = true
		h.enc = nil
	}
	if h.sink != nil {
		h.sink.buf.Reset()
		h.sink.finalized = true
		if h.sink.touched {
			h.writer.failLocked(fmt.Errorf("%w: streaming PNG image %s aborted after partial write", ErrInvalid, h.part))
		}
	}
	return nil
}

// AddImageFromReader 读取头部魔数识别图像格式后以恒定内存直通流式拷贝至底层ZIP，不整图缓存
// 入参: ctx 取消Context，nil采用Background, r 原始图像字节流
// 返回: string 图像部件URI, error 格式、读取、预算、取消或写出错误
func (w *StreamWriter) AddImageFromReader(ctx context.Context, r io.Reader) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if r == nil {
		return "", fmt.Errorf("%w: nil image reader", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	var head [8]byte
	n, err := io.ReadFull(r, head[:])
	if err != nil && err != io.EOF && err != io.ErrUnexpectedEOF {
		return "", err
	}
	if n == 0 {
		return "", fmt.Errorf("%w: empty image data", ErrInvalid)
	}
	media, ext, err := detectImageFormat(head[:n])
	if err != nil {
		return "", err
	}
	pattern := "/Resources/Images/%d." + ext
	part, maxPart, err := w.prepareStreamImagePartLocked(ctx, pattern, media)
	if err != nil {
		return "", err
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: part, maxBytes: maxPart}
	if err := w.copyStreamToSinkLocked(ctx, sink, head[:n], r); err != nil {
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

// copyStreamToSinkLocked 以固定缓冲先写前缀再循环读取输入流拷贝至streamPieceSink，严格执行取消与预算检查
// 入参: ctx 已规范化取消Context, sink 流式分片输出通道, prefix 已预读前缀字节, r 剩余输入流
// 返回: error 读取、预算、取消或写出错误
func (w *StreamWriter) copyStreamToSinkLocked(ctx context.Context, sink *streamPieceSink, prefix []byte, r io.Reader) error {
	if len(prefix) != 0 {
		if _, err := sink.Write(prefix); err != nil {
			return err
		}
	}
	for {
		if err := checkContext(ctx); err != nil {
			return err
		}
		n, readErr := r.Read(w.copyBuf)
		if n > 0 {
			if _, err := sink.Write(w.copyBuf[:n]); err != nil {
				return err
			}
		}
		if readErr == io.EOF {
			return nil
		}
		if readErr != nil {
			return readErr
		}
	}
}

// prepareStreamImagePartLocked 为流式图像写入预检名称、前置内容类型表、逻辑部件数与剩余字节预算
// 入参: ctx 已规范化取消Context, pattern 图像路径模板, media 目标媒体类型
// 返回: string 分配的规范部件URI, int64 允许写出的单部件最大字节数, error 名称、类型或预算错误
func (w *StreamWriter) prepareStreamImagePartLocked(ctx context.Context, pattern, media string) (string, int64, error) {
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", 0, err
	}
	if err := w.validateEarlyContentTypeLocked(part, media); err != nil {
		return "", 0, err
	}
	if w.registry.count() >= w.limits.MaxPartCount {
		return "", 0, fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	maxPart := min(w.limits.MaxPartBytes, w.limits.MaxPackageBytes-w.partBytes)
	if maxPart <= 0 {
		return "", 0, fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	return part, maxPart, nil
}

// validateStreamImageCommonOptions 校验逐行流式PNG/TIFF图像共用的尺寸、像素上限、DPI与ICC色彩空间一致性
// 入参: ctx 已规范化取消Context, options 流式图像选项, maxPixels 像素总数上限, iccSpace 目标ICC四字节空间签名
// 返回: float64 规范化水平DPI, float64 规范化垂直DPI, error 参数、配置或预算错误
func validateStreamImageCommonOptions(ctx context.Context, options StreamImageRowOptions, maxPixels uint64, iccSpace string) (float64, float64, error) {
	if options.Width < 1 || options.Height < 1 {
		return 0, 0, fmt.Errorf("%w: invalid streaming image dimensions", ErrInvalid)
	}
	if maxPixels == 0 {
		maxPixels = DefaultImageOptions().MaxPixels
	}
	if options.Width > rasterMaxDimension || options.Height > rasterMaxDimension || uint64(options.Width) > maxPixels/uint64(options.Height) {
		return 0, 0, fmt.Errorf("%w: image exceeds MaxImagePixels", ErrLimit)
	}
	dpix, dpiy := options.DPIX, options.DPIY
	if dpix < 0 || dpiy < 0 || math.IsNaN(dpix) || math.IsInf(dpix, 0) || math.IsNaN(dpiy) || math.IsInf(dpiy, 0) {
		return 0, 0, fmt.Errorf("%w: invalid image DPI", ErrInvalid)
	}
	if dpix > 0 && dpiy == 0 {
		dpiy = dpix
	} else if dpiy > 0 && dpix == 0 {
		dpix = dpiy
	}
	if len(options.ICCProfile) != 0 {
		parsed, err := validateCreatedICCProfile(options.ICCProfile, ctx)
		if err != nil {
			return 0, 0, err
		}
		if parsed.class == "link" || parsed.class == "abst" {
			return 0, 0, fmt.Errorf("%w: ICC profile class cannot be embedded in an image", ErrInvalid)
		}
		if iccSpace == "" || parsed.space != iccSpace {
			return 0, 0, fmt.Errorf("%w: ICC profile color space %q is incompatible with encoded %q image", ErrInvalid, parsed.space, iccSpace)
		}
	}
	return dpix, dpiy, nil
}

// validateStreamPNGRowOptions 校验逐行流式PNG写入选项并返回规范化DPI、位深、PNG色彩类型与单行字节数
// 入参: ctx 已规范化取消Context, options 流式图像选项, maxPixels 像素总数上限
// 返回: float64 水平DPI, float64 垂直DPI, int 采样位深, uint8 PNG色彩类型, int 单行字节数, error 参数或预算错误
func validateStreamPNGRowOptions(ctx context.Context, options StreamImageRowOptions, maxPixels uint64) (float64, float64, int, uint8, int, error) {
	bitDepth := options.BitDepth
	if bitDepth == 0 {
		bitDepth = 8
	}
	if bitDepth != 8 && bitDepth != 16 {
		return 0, 0, 0, 0, 0, fmt.Errorf("%w: unsupported streaming PNG bit depth %d", ErrInvalid, bitDepth)
	}
	var colorType uint8
	var channels int
	var iccSpace string
	switch options.ColorModel {
	case StreamColorGray:
		colorType, channels, iccSpace = 0, 1, "GRAY"
	case StreamColorGrayAlpha:
		colorType, channels, iccSpace = 4, 2, "GRAY"
	case StreamColorRGB:
		colorType, channels, iccSpace = 2, 3, "RGB "
	case StreamColorRGBA:
		colorType, channels, iccSpace = 6, 4, "RGB "
	default:
		return 0, 0, 0, 0, 0, fmt.Errorf("%w: unsupported streaming PNG color model %s", ErrInvalid, options.ColorModel)
	}
	dpix, dpiy, err := validateStreamImageCommonOptions(ctx, options, maxPixels, iccSpace)
	if err != nil {
		return 0, 0, 0, 0, 0, err
	}
	if _, _, err := encodePNGPhysPixels(dpix, dpiy); err != nil {
		return 0, 0, 0, 0, 0, err
	}
	rowBytes64 := int64(options.Width) * int64(channels) * int64(bitDepth/8)
	if rowBytes64 <= 0 || rowBytes64 > int64(^uint(0)>>1) {
		return 0, 0, 0, 0, 0, fmt.Errorf("%w: streaming PNG row length overflow", ErrLimit)
	}
	return dpix, dpiy, bitDepth, colorType, int(rowBytes64), nil
}

// validateStreamTIFFRowOptions 校验逐行流式TIFF写入选项并构造tiffStripSpec与单行字节数
// 入参: ctx 已规范化取消Context, options 流式图像选项, maxPixels 像素总数上限
// 返回: tiffStripSpec TIFF条带规格, int 单行字节数, error 参数或预算错误
func validateStreamTIFFRowOptions(ctx context.Context, options StreamImageRowOptions, maxPixels uint64) (tiffStripSpec, int, error) {
	if options.TIFFCompression > TIFFCompressionCCITTGroup4 {
		return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF compression %d", ErrInvalid, options.TIFFCompression)
	}
	bitDepth := options.BitDepth
	if bitDepth == 0 {
		if options.ColorModel == StreamColorBilevel {
			bitDepth = 1
		} else {
			bitDepth = 8
		}
	}
	if options.TIFFCompression == TIFFCompressionCCITTGroup4 && (options.ColorModel != StreamColorBilevel || bitDepth != 1) {
		return tiffStripSpec{}, 0, fmt.Errorf("%w: CCITT Group 4 TIFF requires 1-bit StreamColorBilevel", ErrInvalid)
	}
	spec := tiffStripSpec{
		width:       options.Width,
		height:      options.Height,
		compression: options.TIFFCompression,
		icc:         options.ICCProfile,
	}
	var iccSpace string
	var rowBytes64 int64
	switch options.ColorModel {
	case StreamColorBilevel:
		if bitDepth != 1 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: StreamColorBilevel requires 1-bit depth", ErrInvalid)
		}
		spec.spp, spec.bps, spec.photometric, iccSpace = 1, 1, 0, "GRAY"
		rowBytes64 = (int64(options.Width) + 7) / 8
	case StreamColorGray:
		if bitDepth != 8 && bitDepth != 16 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF gray bit depth %d", ErrInvalid, bitDepth)
		}
		spec.spp, spec.bps, spec.photometric, iccSpace = 1, uint16(bitDepth), 1, "GRAY"
		rowBytes64 = int64(options.Width) * int64(bitDepth/8)
	case StreamColorGrayAlpha:
		if bitDepth != 8 && bitDepth != 16 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF gray alpha bit depth %d", ErrInvalid, bitDepth)
		}
		spec.spp, spec.bps, spec.photometric, spec.extraSample, spec.hasExtra, iccSpace = 2, uint16(bitDepth), 1, 2, true, "GRAY"
		rowBytes64 = int64(options.Width) * 2 * int64(bitDepth/8)
	case StreamColorRGB:
		if bitDepth != 8 && bitDepth != 16 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF RGB bit depth %d", ErrInvalid, bitDepth)
		}
		spec.spp, spec.bps, spec.photometric, iccSpace = 3, uint16(bitDepth), 2, "RGB "
		rowBytes64 = int64(options.Width) * 3 * int64(bitDepth/8)
	case StreamColorRGBA:
		if bitDepth != 8 && bitDepth != 16 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF RGBA bit depth %d", ErrInvalid, bitDepth)
		}
		spec.spp, spec.bps, spec.photometric, spec.extraSample, spec.hasExtra, iccSpace = 4, uint16(bitDepth), 2, 2, true, "RGB "
		rowBytes64 = int64(options.Width) * 4 * int64(bitDepth/8)
	case StreamColorCMYK:
		if bitDepth != 8 && bitDepth != 16 {
			return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported TIFF CMYK bit depth %d", ErrInvalid, bitDepth)
		}
		spec.spp, spec.bps, spec.photometric, iccSpace = 4, uint16(bitDepth), 5, "CMYK"
		rowBytes64 = int64(options.Width) * 4 * int64(bitDepth/8)
	default:
		return tiffStripSpec{}, 0, fmt.Errorf("%w: unsupported streaming TIFF color model %s", ErrInvalid, options.ColorModel)
	}
	dpix, dpiy, err := validateStreamImageCommonOptions(ctx, options, maxPixels, iccSpace)
	if err != nil {
		return tiffStripSpec{}, 0, err
	}
	spec.dpix, spec.dpiy = dpix, dpiy
	if dpix > 0 && !(math.Round(dpix*1000) <= math.MaxUint32) || dpiy > 0 && !(math.Round(dpiy*1000) <= math.MaxUint32) {
		return tiffStripSpec{}, 0, fmt.Errorf("%w: TIFF DPI exceeds rational range", ErrInvalid)
	}
	if rowBytes64 <= 0 || rowBytes64 > int64(^uint(0)>>1) {
		return tiffStripSpec{}, 0, fmt.Errorf("%w: streaming TIFF row length overflow", ErrLimit)
	}
	return spec, int(rowBytes64), nil
}

// swapUint16Bytes 将16位采样行中的每对字节就地交换以在大端与小端字节序间转换
// 入参: data 长度为偶数的16位采样字节切片
func swapUint16Bytes(data []byte) {
	for i := 0; i+1 < len(data); i += 2 {
		data[i], data[i+1] = data[i+1], data[i]
	}
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

// AddResourceDictionary 编码共享远程资源字典并立即落盘，复用编码树记录其直接资源依赖与导航引用供页面关系与释放提示追踪
// 入参: ctx 取消Context，nil采用Background, dict 资源字典模型，Source必须为空
// 返回: string 资源字典部件URI, error 模型、编码、预算、取消或写出错误
func (w *StreamWriter) AddResourceDictionary(ctx context.Context, dict *ResourceDictionary) (string, error) {
	return w.AddResourceDictionaryWithOptions(ctx, dict, false)
}

// AddResourceDictionaryWithOptions 编码共享远程资源字典并支持按内容摘要去重，复用编码树记录依赖、导航引用与延迟字体用字
// 入参: ctx 取消Context，nil采用Background, dict 资源字典模型，Source必须为空, deduplicate 是否按内容摘要复用已落盘的相同字典
// 返回: string 资源字典部件URI, error 模型、编码、预算、取消或写出错误
func (w *StreamWriter) AddResourceDictionaryWithOptions(ctx context.Context, dict *ResourceDictionary, deduplicate bool) (string, error) {
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
	const probePart = "/Resources/Dictionaries/0.dict"
	root, data, err := encodeResourceDictionaryTree(ctx, dict, &EncodeOptions{Format: w.format, Limits: w.limits, Part: probePart, Compact: w.compact})
	if err != nil {
		return "", err
	}
	digest := sha256.Sum256(data)
	if deduplicate {
		if existing, found := w.findHashLocked(digest, resourceDictionaryContentType, len(data)); found {
			return existing, nil
		}
	}
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	deps, err := collectStreamNodeDependencies(part, root)
	if err != nil {
		return "", err
	}
	navRefs := collectStreamNodeNavigateURIs(root)
	if err := w.writePartLocked(ctx, part, resourceDictionaryContentType, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.recordHashLocked(digest, part, resourceDictionaryContentType, len(data))
	w.recordDeferredFontGlyphsLocked(part, root)
	dictKey := strings.ToLower(part)
	w.dictDeps[dictKey] = deps
	if len(navRefs) != 0 {
		w.dictNavRefs[dictKey] = navRefs
	}
	w.onLateDictWrittenLocked(dictKey)
	return part, nil
}

// AddPart 按OPC规则与[M12.8]标准媒体类型校验并立即落盘自定义或扩展部件，严格校验远程资源字典与嵌入字体后同步登记依赖与受限面表
// 入参: ctx 取消Context，nil采用Background, part 部件URI, media 内容类型, data 部件内容
// 返回: error 名称冲突、媒体类型、字典结构、字体许可、预算、取消或写出错误
func (w *StreamWriter) AddPart(ctx context.Context, part, media string, data []byte) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	return w.addPartLocked(ctx, part, media, data)
}

// AddPartFromReader 按OPC规则与媒体类型校验后将自定义或扩展部件流式写入底层ZIP，普通二进制载荷采用恒定内存直通拷贝
// 远程资源字典与字体部件受限于MaxPartBytes有界读入以执行完整结构与嵌入许可校验，不绕过安全约束
// 入参: ctx 取消Context，nil采用Background, part 部件URI, media 内容类型, r 部件数据流
// 返回: error 名称冲突、媒体类型、字典结构、字体许可、读取、预算、取消或写出错误
func (w *StreamWriter) AddPartFromReader(ctx context.Context, part, media string, r io.Reader) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if r == nil {
		return fmt.Errorf("%w: nil part reader", ErrInvalid)
	}
	if err := w.lock(ctx); err != nil {
		return err
	}
	defer w.mu.Unlock()
	canonical, err := w.validateAddPartHeaderLocked(part, media)
	if err != nil {
		return err
	}
	if requiredResourceMedia(requiredDictionary, media) || requiredResourceMedia(requiredFont, media) {
		maxBytes := min(w.limits.MaxPartBytes, w.limits.MaxPackageBytes-w.partBytes)
		if maxBytes < 0 {
			return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
		}
		var buf bytes.Buffer
		var total int64
		for {
			if err := checkContext(ctx); err != nil {
				return err
			}
			n, readErr := r.Read(w.copyBuf)
			if n > 0 {
				if int64(n) > maxBytes-total {
					return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
				}
				buf.Write(w.copyBuf[:n])
				total += int64(n)
			}
			if readErr == io.EOF {
				break
			}
			if readErr != nil {
				return readErr
			}
		}
		return w.addPartLocked(ctx, canonical, media, buf.Bytes())
	}
	if !w.registry.has(canonical) && w.registry.count() >= w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	maxPart := min(w.limits.MaxPartBytes, w.limits.MaxPackageBytes-w.partBytes)
	if maxPart < 0 {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	sink := &streamPieceSink{writer: w, ctx: ctx, part: canonical, maxBytes: maxPart}
	if err := w.copyStreamToSinkLocked(ctx, sink, nil, r); err != nil {
		if sink.touched {
			w.failed = err
		}
		return err
	}
	if err := sink.finish(); err != nil {
		if sink.touched {
			w.failed = err
		}
		return err
	}
	w.registerPartMetaLocked(canonical, media, sink.written)
	return nil
}

// validateAddPartHeaderLocked 在持有互斥锁时校验自定义部件名称规范、保留路径冲突、重复占用、格式媒体类型及前置内容类型
// 入参: part 部件URI, media 内容类型
// 返回: string 规范化部件URI, error 名称冲突、保留部件或媒体类型错误
func (w *StreamWriter) validateAddPartHeaderLocked(part, media string) (string, error) {
	canonical, err := opcPartName(part)
	if err != nil {
		return "", err
	}
	if opcRelationshipName(canonical) || strings.EqualFold(canonical, opcTypesName) || strings.EqualFold(canonical, w.sequence) {
		return "", fmt.Errorf("%w: managed stream part name", ErrInvalid)
	}
	if err := w.availableLocked(canonical); err != nil {
		return "", err
	}
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return "", err
	}
	if err := w.validateEarlyContentTypeLocked(canonical, media); err != nil {
		return "", err
	}
	return canonical, nil
}

// addPartLocked 在持有互斥锁时完成AddPart的完整校验、落盘及远程字典与字体登记
// 入参: ctx 已规范化取消Context, part 部件URI, media 内容类型, data 部件原始字节
// 返回: error 名称冲突、媒体类型、字典结构、字体许可、预算、取消或写出错误
func (w *StreamWriter) addPartLocked(ctx context.Context, part, media string, data []byte) error {
	canonical, err := w.validateAddPartHeaderLocked(part, media)
	if err != nil {
		return err
	}
	var parsedDictRoot *xmlElement
	var parsedDictDeps []streamResourceRef
	var parsedDictNavs []string
	isDict := requiredResourceMedia(requiredDictionary, media)
	if isDict {
		if int64(len(data)) > w.limits.MaxPartBytes {
			return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
		}
		root, err := decodeXML(data, w.limits)
		if err != nil {
			return err
		}
		ns := formatNamespace(w.format)
		root, err = preprocessXMLContext(root, []string{ns, ns + "/resourcedictionary-key"}, ctx)
		if err != nil {
			return err
		}
		if err := fixedChild(root, w.format, "ResourceDictionary"); err != nil {
			return err
		}
		if err := validateFixedNames(root, w.format); err != nil {
			return err
		}
		parser := &resourceParser{
			format: w.format, limits: w.limits, context: ctx,
			graph:  &resourceGraph{PagePart: canonical, Bindings: make(map[*xmlElement]map[string]*resourceDefinition), Parts: make(map[*xmlElement]string)},
			remote: make(map[string]*resourceScope),
		}
		if _, err := parser.dictionary(root, canonical, nil, true, 1); err != nil {
			return err
		}
		parsedDictDeps, err = collectStreamNodeDependencies(canonical, root)
		if err != nil {
			return err
		}
		parsedDictNavs = collectStreamNodeNavigateURIs(root)
		parsedDictRoot = root
	}
	var restrictedFaces []uint32
	var needObfFaces []uint32
	var prohibitedFaces []uint32
	if requiredResourceMedia(requiredFont, media) {
		isObfuscated := matchStandardContentType(w.format, media, "application/vnd.ms-package.obfuscated-opentype")
		fontRaw := data
		if isObfuscated {
			decoded, deobfErr := DeobfuscateFont(canonical, data)
			if deobfErr != nil {
				return deobfErr
			}
			fontRaw = decoded
		}
		var fontErr error
		restrictedFaces, needObfFaces, prohibitedFaces, fontErr = validateStreamAddedFontPart(ctx, fontRaw, w.limits.MaxPartBytes, isObfuscated)
		if fontErr != nil {
			return fontErr
		}
	}
	if err := w.writePartLocked(ctx, canonical, media, data, true); err != nil {
		return err
	}
	if isDict {
		w.recordDeferredFontGlyphsLocked(canonical, parsedDictRoot)
		dictKey := strings.ToLower(canonical)
		w.dictDeps[dictKey] = parsedDictDeps
		if len(parsedDictNavs) != 0 {
			w.dictNavRefs[dictKey] = parsedDictNavs
		}
		w.onLateDictWrittenLocked(dictKey)
	}
	if len(restrictedFaces) != 0 {
		w.recordRestrictedFaceIndicesLocked(canonical, restrictedFaces)
	}
	if len(needObfFaces) != 0 || len(prohibitedFaces) != 0 {
		w.recordFontFaceGuardsLocked(canonical, needObfFaces, prohibitedFaces)
	}
	return nil
}

// AddPage 编码单页模型并立即落盘至底层流，写前完成全部可预判预算校验，复用编码树记录依赖、名称与导航引用并推进交错索引
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
	if err := w.validateEarlyContentTypeLocked(part, fixedContentType("fixedpage")); err != nil {
		return "", err
	}
	value.Part = part
	root, data, err := encodePageTree(ctx, &value, &EncodeOptions{Format: w.format, Limits: w.limits, Compact: w.compact})
	if err != nil {
		return "", err
	}
	if int64(len(data)) > w.limits.MaxPartBytes {
		return "", fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	pageTargetNames := createdPageTargets(root)
	targets, err := validateExplicitLinkTargetsForPage(w.format, w.documents, value.LinkTargets, pageTargetNames, docIdx, -1)
	if err != nil {
		return "", err
	}
	deps, err := collectStreamNodeDependencies(part, root)
	if err != nil {
		return "", err
	}
	expandedDeps := w.expandDependenciesRecursiveLocked(deps)
	hasRestricted := false
	for _, dep := range expandedDeps {
		depKey := strings.ToLower(dep.part)
		if _, discarded := w.emittedDiscardPage[depKey]; discarded {
			return "", fmt.Errorf("%w: resource %s was already discarded", ErrInvalid, dep.part)
		}
		if dep.hasFace {
			faceKey := fontCacheKey{part: depKey, index: dep.faceIndex}
			if w.prohibitedFaces[faceKey] {
				return "", fmt.Errorf("%w: font %s#%d prohibits embedding", ErrRestricted, dep.part, dep.faceIndex)
			}
			if w.needObfFaces[faceKey] {
				return "", fmt.Errorf("%w: font %s#%d requires obfuscation", ErrRestricted, dep.part, dep.faceIndex)
			}
			if w.restrictedFaces[faceKey] {
				hasRestricted = true
			}
		}
	}
	neededParts := 1
	if implicitDoc {
		neededParts++
	}
	pageRelPart := createdRelationshipPart(part)
	docRelPart := createdRelationshipPart(docPart)
	if len(expandedDeps) != 0 {
		if err := w.canReserveRelationPartLocked(part); err != nil {
			return "", err
		}
		if !w.registry.has(pageRelPart) {
			neededParts++
		}
	}
	if hasRestricted {
		if err := w.canReserveRelationPartLocked(docPart); err != nil {
			return "", err
		}
		if !w.registry.has(docRelPart) {
			neededParts++
		}
	}
	if w.registry.count()+neededParts > w.limits.MaxPartCount {
		return "", fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	if implicitDoc {
		probe := w.registry.clone()
		probe.register(docPart)
		if err := probe.available(part); err != nil {
			return "", err
		}
		probe.register(part)
		if len(expandedDeps) != 0 {
			if err := probe.available(pageRelPart); err != nil {
				return "", err
			}
			probe.register(pageRelPart)
		}
		if hasRestricted {
			if err := probe.available(docRelPart); err != nil {
				return "", err
			}
		}
	}
	ref := PageReference{Part: part, Width: value.Width, Height: value.Height, LinkTargets: targets}
	var pageContentXML []byte
	if w.earlyContentTypes {
		pageContentNode, err := buildFixedDocumentPageContentNode(w.format, docPart, ref)
		if err != nil {
			return "", err
		}
		pageContentXML, err = encodeStreamChildXML(ctx, pageContentNode, w.limits.MaxPartBytes)
		if err != nil {
			return "", err
		}
		if !implicitDoc {
			if err := w.checkAppendStreamBudgetLocked(docPart, int64(len(pageContentXML))); err != nil {
				return "", err
			}
		}
		if int64(len(data))+int64(len(pageContentXML)) > w.limits.MaxPackageBytes-w.partBytes {
			return "", fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
		}
	} else if int64(len(data)) > w.limits.MaxPackageBytes-w.partBytes {
		return "", fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	pageNavs := collectStreamNodeNavigateURIs(root)
	if implicitDoc {
		if docIdx, err = w.beginDocumentLocked(ctx); err != nil {
			return "", err
		}
		docPart = w.documents[docIdx].Part
	}
	if w.earlyContentTypes {
		if err := w.closeReadyPageRelsLocked(ctx); err != nil {
			return "", w.failLocked(err)
		}
		if err := w.flushEarlyDiscardsForNextPageLocked(ctx, part, expandedDeps); err != nil {
			return "", w.failLocked(err)
		}
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("fixedpage"), data, true); err != nil {
		if implicitDoc || w.earlyContentTypes {
			return "", w.failLocked(err)
		}
		return "", err
	}
	w.commitNameLocked(pattern, part)
	w.recordDeferredFontGlyphsLocked(part, root)
	pageIndex := len(w.allPages)
	w.allPages = append(w.allPages, part)
	w.documents[docIdx].Pages = append(w.documents[docIdx].Pages, ref)
	w.pageDeps = append(w.pageDeps, streamPageDeps{docPart: docPart, pagePart: part, pageIndex: pageIndex, deps: deps})
	nameSet := make(map[string]bool, len(pageTargetNames))
	for _, name := range pageTargetNames {
		nameSet[name] = true
	}
	w.pageNames[strings.ToLower(part)] = nameSet
	for _, navTarget := range pageNavs {
		w.pageNavRefs = append(w.pageNavRefs, streamNavRef{sourcePart: part, target: navTarget})
	}
	reqType := formatNamespace(w.format) + "/required-resource"
	resType := formatNamespace(w.format) + "/restricted-font"
	hasPendingDict := false
	hasPendingFont := false
	for _, dep := range expandedDeps {
		depKey := strings.ToLower(dep.part)
		w.resourceLastPage[depKey] = pageIndex
		if err := w.appendRelationLocked(part, reqType, dep.part, false); err != nil {
			return "", w.failLocked(err)
		}
		if _, written := w.parts[depKey]; !written {
			if dep.kind == requiredDictionary {
				hasPendingDict = true
				w.pendingDicts[depKey] = true
			} else if dep.kind == requiredFont {
				if _, isDeferred := w.deferredFonts[depKey]; !isDeferred {
					hasPendingFont = true
				}
			}
		}
		if dep.hasFace && w.restrictedFaces[fontCacheKey{part: depKey, index: dep.faceIndex}] {
			if err := w.appendRelationLocked(docPart, resType, dep.part, false); err != nil {
				return "", w.failLocked(err)
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
			return "", w.failLocked(err)
		}
		w.trackOpenPageRelLocked(part)
		if err := w.flushStreamRelationsLocked(ctx, docPart); err != nil {
			return "", w.failLocked(err)
		}
		if err := w.appendPieceStreamLocked(ctx, docPart, pageContentXML); err != nil {
			return "", w.failLocked(err)
		}
		if err := w.archive.Flush(); err != nil {
			return "", w.failLocked(err)
		}
	}
	return part, nil
}

// ReleaseResource 标记指定资源在当前已提交页面之后不再被引用，EarlyContentTypes下于后续页面提交时即时落盘，其余模式在Close时生成合规DiscardControl提示
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
		if _, deferred := w.deferredFonts[key]; !deferred {
			return fmt.Errorf("%w: released resource %s does not exist", ErrInvalid, canonical)
		}
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
	if err := w.canReserveRelationPartLocked("/"); err != nil {
		return err
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
	if err := w.canWritePartWithRelLocked(part, "/", opcCoreType, int64(len(data))); err != nil {
		return err
	}
	if err := w.writePartLocked(ctx, part, opcCoreType, data, true); err != nil {
		return err
	}
	w.commitNameLocked(pattern, part)
	if err := w.appendRelationLocked("/", opcCoreRel, part, false); err != nil {
		return w.failLocked(err)
	}
	if w.earlyContentTypes {
		return w.failLocked(w.flushStreamRelationsLocked(ctx, "/"))
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
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	canonical, scope, err := w.validatePrintTicketTargetLocked(targetPart)
	if err != nil {
		return "", err
	}
	resolvedType, err := validatePrintTicketPayload(ctx, w.format, scope, contentType, data, w.limits)
	if err != nil {
		return "", err
	}
	return w.writeBoundPrintTicketLocked(ctx, canonical, resolvedType, data)
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

// writeBoundPrintTicketLocked 分配票据路径、写前预检预算、落盘载荷并绑定对应目标的printticket关系
// 入参: ctx 已规范化取消Context, canonical 已校验目标来源URI, contentType 媒体类型, data 票据原始载荷
// 返回: string 写入的打印票据部件URI, error 分配、类型、预算、取消或写出错误
func (w *StreamWriter) writeBoundPrintTicketLocked(ctx context.Context, canonical, contentType string, data []byte) (string, error) {
	baseType := strings.ToLower(opcMediaTypeBase(contentType))
	preferredExt := "xml"
	if !strings.EqualFold(baseType, printTicketType) && !strings.HasSuffix(baseType, "+xml") && baseType != "application/xml" && baseType != "text/xml" {
		preferredExt = "bin"
	}
	ext := preferredExt
	if w.earlyContentTypes {
		if expected, ok := w.earlyDefaults[preferredExt]; !ok || !matchEarlyDefaultContentType(w.format, contentType, expected) {
			for _, candidateExt := range slices.Sorted(maps.Keys(w.earlyDefaults)) {
				if matchEarlyDefaultContentType(w.format, contentType, w.earlyDefaults[candidateExt]) {
					ext = candidateExt
					break
				}
			}
		}
	}
	pattern := "/Metadata/PrintTicket%d." + ext
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.canWritePartWithRelLocked(part, canonical, contentType, int64(len(data))); err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, contentType, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	if err := w.appendRelationLocked(canonical, formatNamespace(w.format)+"/printticket", part, false); err != nil {
		return "", w.failLocked(err)
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, canonical); err != nil {
			return "", w.failLocked(err)
		}
		w.trackOpenPageRelLocked(canonical)
		if strings.EqualFold(canonical, w.sequence) {
			if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(canonical)); err != nil {
				return "", w.failLocked(err)
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
	media, ext, err := validateThumbnailPayload(ctx, data, w.limits.MaxPartBytes, w.maxImagePixels)
	if err != nil {
		return "", err
	}
	pattern := "/Metadata/Thumbnail%d." + ext
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.canWritePartWithRelLocked(part, source, media, int64(len(data))); err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, media, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	if err := w.appendRelationLocked(source, thumbnailRelationship, part, false); err != nil {
		return "", w.failLocked(err)
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, source); err != nil {
			return "", w.failLocked(err)
		}
		w.trackOpenPageRelLocked(source)
	}
	return part, nil
}

// SetDocumentStructure 编码指定固定文档的目录与故事结构、立即落盘并绑定documentstructure关系，关闭时终检大纲目标与故事交叉对应，同一文档重复设置返回ErrInvalid
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
	info := &streamDocStructInfo{storyNames: make(map[string]bool, len(structure.Stories))}
	for _, story := range structure.Stories {
		info.storyNames[story.Name] = true
		for _, ref := range story.Fragments {
			if ref.PageNumber < 1 {
				return fmt.Errorf("%w: invalid story fragment page number %d", ErrInvalid, ref.PageNumber)
			}
			info.storyRefs = append(info.storyRefs, streamStoryFragmentRef{
				storyName:    story.Name,
				pageNumber:   ref.PageNumber,
				fragmentName: cloneOptionalString(ref.FragmentName),
			})
		}
	}
	if structure.Outline != nil {
		for _, entry := range structure.Outline.Entries {
			if entry.Target != "" {
				info.outlineTargets = append(info.outlineTargets, entry.Target)
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
	if err := w.canWritePartWithRelLocked(part, source, fixedContentType("documentstructure"), int64(len(data))); err != nil {
		return err
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("documentstructure"), data, true); err != nil {
		return err
	}
	w.commitNameLocked(usedPattern, part)
	info.part = part
	w.docStructures[docIndex] = info
	if err := w.appendRelationLocked(source, relType, part, false); err != nil {
		return w.failLocked(err)
	}
	if w.earlyContentTypes {
		return w.failLocked(w.flushStreamRelationsLocked(ctx, source))
	}
	return nil
}

// SetStoryFragments 编码指定页面的故事片段、立即落盘并绑定storyfragments关系，关闭时终检故事归属与命名元素存在性，同一页面重复设置返回ErrInvalid
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
	storyInfo := &streamPageStoryInfo{fragments: make([]streamPageStoryFragment, 0, len(fragments.Fragments))}
	for _, frag := range fragments.Fragments {
		storyInfo.fragments = append(storyInfo.fragments, streamPageStoryFragment{
			storyName:    cloneOptionalString(frag.StoryName),
			fragmentName: cloneOptionalString(frag.FragmentName),
		})
		refs, err := collectStreamStoryNamedRefs(frag.Content, w.limits.MaxXMLDepth)
		if err != nil {
			return err
		}
		storyInfo.namedRefs = append(storyInfo.namedRefs, refs...)
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
	if err := w.canWritePartWithRelLocked(part, source, fixedContentType("storyfragments"), int64(len(data))); err != nil {
		return err
	}
	if err := w.writePartLocked(ctx, part, fixedContentType("storyfragments"), data, true); err != nil {
		return err
	}
	w.commitNameLocked(usedPattern, part)
	storyInfo.part = part
	w.pageStories[strings.ToLower(source)] = storyInfo
	if err := w.appendRelationLocked(source, relType, part, false); err != nil {
		return w.failLocked(err)
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, source); err != nil {
			return w.failLocked(err)
		}
		w.trackOpenPageRelLocked(source)
	}
	return nil
}

// SetSignatureDefinitions 编码指定固定文档的签署请求定义、校验全局SpotID唯一、立即落盘并绑定signature-definitions关系
// 入参: ctx 取消Context，nil采用Background, docIndex 零基固定文档序号, definitions 非空签署请求列表
// 返回: string 写入的签名定义部件URI, error 序号、重复SpotID、编码、预算、取消或写出错误
func (w *StreamWriter) SetSignatureDefinitions(ctx context.Context, docIndex int, definitions []SignatureDefinition) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := w.lock(ctx); err != nil {
		return "", err
	}
	defer w.mu.Unlock()
	if docIndex < 0 || docIndex >= len(w.documents) || len(definitions) == 0 {
		return "", fmt.Errorf("%w: signature definition document index or empty requests", ErrInvalid)
	}
	source := w.documents[docIndex].Part
	if err := w.canReserveRelationPartLocked(source); err != nil {
		return "", err
	}
	var encoded bytes.Buffer
	if _, err := EncodeSignatureDefinitions(ctx, &encoded, definitions, &EncodeOptions{Format: w.format, Limits: w.limits}); err != nil {
		return "", err
	}
	batchIDs := make(map[string]bool, len(definitions))
	for _, def := range definitions {
		id := strings.Trim(def.ID, " \t\r\n")
		if id == "" || w.signatureSpotIDs[id] || batchIDs[id] {
			return "", fmt.Errorf("%w: duplicate or empty global signature spot ID %q", ErrInvalid, id)
		}
		batchIDs[id] = true
	}
	data := encoded.Bytes()
	if int64(len(data)) > min(w.limits.MaxPartBytes, w.limits.MaxMetadataBytes) {
		return "", fmt.Errorf("%w: signature definitions byte budget", ErrLimit)
	}
	media := fixedContentType("signaturedefinitions")
	ext := "xml"
	if w.earlyContentTypes {
		ext = "psigdef"
		if expected, ok := w.earlyDefaults[ext]; !ok || !matchEarlyDefaultContentType(w.format, media, expected) {
			for _, candidateExt := range slices.Sorted(maps.Keys(w.earlyDefaults)) {
				if matchEarlyDefaultContentType(w.format, media, w.earlyDefaults[candidateExt]) {
					ext = candidateExt
					break
				}
			}
		}
	}
	pattern := "/Metadata/SignatureDefinitions%d." + ext
	part, err := w.newNameLocked(pattern, ctx)
	if err != nil {
		return "", err
	}
	if err := w.canWritePartWithRelLocked(part, source, media, int64(len(data))); err != nil {
		return "", err
	}
	if err := w.writePartLocked(ctx, part, media, data, true); err != nil {
		return "", err
	}
	w.commitNameLocked(pattern, part)
	for id := range batchIDs {
		w.signatureSpotIDs[id] = true
	}
	if err := w.appendRelationLocked(source, formatNamespace(w.format)+"/signature-definitions", part, false); err != nil {
		return "", w.failLocked(err)
	}
	if w.earlyContentTypes {
		if err := w.flushStreamRelationsLocked(ctx, source); err != nil {
			return "", w.failLocked(err)
		}
	}
	return part, nil
}

// Close 幂等完成流式包收尾：终检依赖、导航目标与故事结构，补齐或闭合固定布局、释放提示、全部.rels与[Content_Types].xml并关闭ZIP容器
// 入参: ctx 取消Context，nil采用Background
// 返回: error 结构、依赖、导航、故事、编码、预算、取消或ZIP关闭错误
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
	if w.deflater != nil {
		defer w.deflater.Close()
	}
	if w.failed != nil {
		w.closeErr = w.failed
		return w.closeErr
	}
	if w.activeStreamPart != "" {
		w.closeErr = fmt.Errorf("%w: unclosed streaming image writer %s", ErrInvalid, w.activeStreamPart)
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

// finalizeLocked 在Close期间执行终检、延迟字体子集落盘、展开后置字典依赖、写出或闭合剩余索引、释放提示、关系与内容类型表并关闭ZIP
// 入参: ctx 已规范化取消Context
// 返回: error 结构、依赖、导航、故事、编码或写出错误
func (w *StreamWriter) finalizeLocked(ctx context.Context) error {
	if len(w.documents) == 0 {
		return fmt.Errorf("%w: stream package requires at least one document", ErrInvalid)
	}
	ns := formatNamespace(w.format)
	for _, doc := range w.documents {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if len(doc.Pages) == 0 {
			return fmt.Errorf("%w: stream document %s requires at least one page", ErrInvalid, doc.Part)
		}
	}
	if err := w.flushDeferredFontsLocked(ctx, false); err != nil {
		return err
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
			if dep.hasFace {
				faceKey := fontCacheKey{part: depKey, index: dep.faceIndex}
				if w.prohibitedFaces[faceKey] {
					return fmt.Errorf("%w: font %s#%d prohibits embedding", ErrRestricted, dep.part, dep.faceIndex)
				}
				if w.needObfFaces[faceKey] {
					return fmt.Errorf("%w: font %s#%d requires obfuscation", ErrRestricted, dep.part, dep.faceIndex)
				}
				if w.restrictedFaces[faceKey] {
					if err := w.appendRelationLocked(rec.docPart, resType, dep.part, false); err != nil {
						return err
					}
				}
			}
		}
	}
	if err := w.validateStreamNavigationAndStoriesLocked(ctx); err != nil {
		return err
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

// visitProtectedRelationsLocked 遍历源部件下应受生命周期保护的内部关系目标，排除discard-control及可选restricted-font关系
// 入参: source 源部件URI或/, skipRestricted 是否跳过restricted-font关系, visit 接收目标URI的回调
func (w *StreamWriter) visitProtectedRelationsLocked(source string, skipRestricted bool, visit func(target string)) {
	ns := formatNamespace(w.format)
	restrictedRel := ns + "/restricted-font"
	discardRel := ns + "/discard-control"
	for _, rel := range w.relations[strings.ToLower(source)] {
		if rel.TargetMode != "" && rel.TargetMode != TargetModeInternal {
			continue
		}
		if rel.Type == discardRel || skipRestricted && rel.Type == restrictedRel {
			continue
		}
		visit(rel.Target)
	}
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
	bumpRelations := func(source string, idx int, skipRestricted bool) {
		w.visitProtectedRelationsLocked(source, skipRestricted, func(target string) {
			bump(target, idx, make(map[string]bool))
		})
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
	if w.activeStreamPart != "" {
		part := w.activeStreamPart
		w.mu.Unlock()
		return fmt.Errorf("%w: active streaming image writer %s must be closed first", ErrInvalid, part)
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
	pieceSize := int(w.interleaveBytes)
	if allowInterleave && pieceSize == 0 && w.earlyContentTypes && w.compression == CompressionDeflate && len(data) > compressionBufferLimit {
		pieceSize = streamEarlyAutoPieceBytes
	}
	if !allowInterleave || pieceSize == 0 {
		return w.writeZIPPayloadLocked(ctx, baseName, data)
	}
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

// streamMaxPhysicalEntries 计算与逻辑MaxPartCount解耦的物理ZIP条目安全上限，避免交错分片与EarlyContentTypes多片提前耗尽逻辑部件配额
// 入参: maxPartCount 逻辑部件数量上限
// 返回: int 物理ZIP条目数量安全上限
func streamMaxPhysicalEntries(maxPartCount int) int {
	limit := int64(maxPartCount) * 64
	if limit < 65536 {
		limit = 65536
	}
	if limit > int64(^uint(0)>>1) {
		return int(^uint(0) >> 1)
	}
	return int(limit)
}

// writeZIPPayloadLocked 写入单个物理ZIP条目，EarlyContentTypes的Deflate条目走预压缩CreateRaw以消除尾条挂起延迟并支持即时Flush
// 入参: ctx 取消Context, entryName 物理ZIP条目路径, data 未压缩载荷
// 返回: error 条目计数、压缩、取消或写出错误
func (w *StreamWriter) writeZIPPayloadLocked(ctx context.Context, entryName string, data []byte) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if w.entryCount >= streamMaxPhysicalEntries(w.limits.MaxPartCount) {
		return fmt.Errorf("%w: stream ZIP entry count", ErrLimit)
	}
	w.entryCount++
	header := zip.FileHeader{Name: entryName, Method: zip.Deflate, Modified: w.fixedTime}
	if w.earlyContentTypes && w.compression == CompressionDeflate && len(data) <= compressionBufferLimit {
		if w.deflater == nil {
			fw, err := flate.NewWriter(io.Discard, flate.DefaultCompression)
			if err != nil {
				return err
			}
			w.deflater = fw
		}
		w.candidate.reset(compressionBufferLimit)
		w.deflater.Reset(&w.candidate)
		copyErr := writeCompressionInput(w.deflater, bytes.NewReader(data), w.copyBuf, ctx)
		closeErr := w.deflater.Close()
		if err := checkContext(ctx); err != nil {
			return err
		}
		if copyErr == nil && closeErr == nil {
			crc, err := zipChunkedCRC32(ctx, data, len(w.copyBuf))
			if err != nil {
				return err
			}
			payload := w.candidate.Bytes()
			header.Method = zip.Deflate
			header.CRC32 = crc
			header.UncompressedSize64 = uint64(len(data))
			header.CompressedSize64 = uint64(len(payload))
			header.UncompressedSize, header.CompressedSize = 0, 0
			if header.UncompressedSize64 < uint64(^uint32(0)) && header.CompressedSize64 < uint64(^uint32(0)) {
				header.UncompressedSize = uint32(len(data))
				header.CompressedSize = uint32(len(payload))
			}
			header.Flags &^= 0xe
			header.ReaderVersion, header.CreatorVersion = 20, header.CreatorVersion&0xff00|20
			prepareRawZIPHeader(&header)
			writer, err := w.archive.CreateRaw(&header)
			if err != nil {
				return err
			}
			return writeCompressionInput(writer, bytes.NewReader(payload), w.copyBuf, ctx)
		}
	}
	return writeZIPBufferEntry(ctx, w.archive, header, data, w.compression, w.optimizer, &w.candidate, w.copyBuf)
}

// pieceSize 返回流式输出通道使用的物理分片字节数，EarlyContentTypes下无显式分片的Deflate自动启用受控分片以消除尾条挂起
// 返回: int64 物理分片字节上限，0表示不分片
func (s *streamPieceSink) pieceSize() int64 {
	if s.writer.interleaveBytes > 0 {
		return s.writer.interleaveBytes
	}
	if s.writer.earlyContentTypes && s.writer.compression == CompressionDeflate {
		return streamEarlyAutoPieceBytes
	}
	return 0
}

// Write 接收流式编码器输出的字节块，无分片Deflate直写、无分片Store/Optimize受控缓冲走CreateRaw、分片模式滞后冲刷上一满片消除0字节尾片
// 入参: p 待写字节切片
// 返回: int 已接收字节数, error 预算、取消或ZIP写出错误
func (s *streamPieceSink) Write(p []byte) (int, error) {
	if err := checkContext(s.ctx); err != nil {
		return 0, err
	}
	if int64(len(p)) > s.maxBytes-s.written {
		return 0, fmt.Errorf("%w: streaming image exceeds byte budget", ErrLimit)
	}
	pieceLimit := s.pieceSize()
	if pieceLimit == 0 && s.writer.compression == CompressionDeflate {
		if s.direct == nil {
			if s.writer.entryCount >= streamMaxPhysicalEntries(s.writer.limits.MaxPartCount) {
				return 0, fmt.Errorf("%w: stream ZIP entry count", ErrLimit)
			}
			s.writer.entryCount++
			header := zip.FileHeader{Name: strings.TrimPrefix(s.part, "/"), Method: zip.Deflate, Modified: s.writer.fixedTime}
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
	if pieceLimit == 0 {
		n, err := s.buf.Write(p)
		s.written += int64(n)
		return n, err
	}
	limit := int(pieceLimit)
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

// finish 刷写剩余分片或Store/Optimize整部件缓冲至底层ZIP流，复用writeZIPBufferEntry与prepareRawZIPHeader保持时间戳和UTF-8标志一致
// 返回: error 写出错误
func (s *streamPieceSink) finish() error {
	if s.finalized {
		return nil
	}
	s.finalized = true
	pieceLimit := s.pieceSize()
	if pieceLimit == 0 && s.writer.compression == CompressionDeflate {
		if s.direct == nil {
			s.touched = true
			return s.writer.writeZIPPayloadLocked(s.ctx, strings.TrimPrefix(s.part, "/"), nil)
		}
		return nil
	}
	if pieceLimit == 0 {
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

// collectStreamNodeNavigateURIs 扫描页面或远程字典XML树中所有Canvas、Path、Glyphs元素的FixedPage.NavigateUri属性
// 入参: root XML根节点
// 返回: []string 原始NavigateUri属性值切片
func collectStreamNodeNavigateURIs(root *xmlElement) []string {
	var refs []string
	var walk func(*xmlElement)
	walk = func(node *xmlElement) {
		if node == nil {
			return
		}
		if node.Name.Local == "Canvas" || node.Name.Local == "Path" || node.Name.Local == "Glyphs" {
			if target, present := node.attribute("FixedPage.NavigateUri"); present {
				refs = append(refs, target)
			}
		}
		for _, child := range node.Children {
			walk(child)
		}
	}
	walk(root)
	return refs
}

// collectStreamStoryNamedRefs 递归收集StoryFragment语义树中全部NamedElement与列表Marker引用的页面元素名称
// 入参: content 故事语义结构节点切片, maxDepth 允许的最大递归深度
// 返回: []string 引用的页面元素名称切片, error 深度超限错误
func collectStreamStoryNamedRefs(content []ContentStructure, maxDepth int) ([]string, error) {
	var refs []string
	var walk func(nodes []ContentStructure, depth int) error
	walk = func(nodes []ContentStructure, depth int) error {
		if depth >= maxDepth {
			return fmt.Errorf("%w: story link depth", ErrLimit)
		}
		for _, node := range nodes {
			if node.Kind == StructureNamedElement {
				refs = append(refs, node.NameReference)
			} else if node.Marker != nil {
				refs = append(refs, *node.Marker)
			}
			if len(node.Children) != 0 {
				if err := walk(node.Children, depth+1); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if err := walk(content, 0); err != nil {
		return nil, err
	}
	return refs, nil
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

// earlyStreamDefaultTypes 按OPC§10.1.2.2构建指定方言前置Default内容类型表，支持排除默认xml打印票据映射及合并用户自定义映射
// 入参: format 文档方言, excludePrintTicket 是否不预声明默认xml打印票据映射, custom 可选用户扩展或覆写映射
// 返回: map[string]string 小写扩展名到合法内容类型的映射, error 扩展名或内容类型非法错误
func earlyStreamDefaultTypes(format Format, excludePrintTicket bool, custom map[string]string) (map[string]string, error) {
	defaults := map[string]string{
		"rels":     opcRelsType,
		"fdseq":    fixedContentType("fixeddocumentsequence"),
		"fdoc":     fixedContentType("fixeddocument"),
		"fpage":    fixedContentType("fixedpage"),
		"dict":     resourceDictionaryContentType,
		"struct":   fixedContentType("documentstructure"),
		"frag":     fixedContentType("storyfragments"),
		"discard":  fixedContentType("discard-control"),
		"psigdef":  fixedContentType("signaturedefinitions"),
		"psigdefs": fixedContentType("signaturedefinitions"),
		"xml":      printTicketType,
		"psmdcp":   opcCoreType,
		"png":      "image/png",
		"jpg":      "image/jpeg",
		"jpeg":     "image/jpeg",
		"tif":      "image/tiff",
		"tiff":     "image/tiff",
		"wdp":      "image/vnd.ms-photo",
		"jxr":      "image/vnd.ms-photo",
		"hdp":      "image/vnd.ms-photo",
		"ttf":      "application/vnd.ms-opentype",
		"otf":      "application/vnd.ms-opentype",
		"ttc":      "application/vnd.ms-opentype",
		"otc":      "application/vnd.ms-opentype",
		"odttf":    "application/vnd.ms-package.obfuscated-opentype",
		"odttc":    "application/vnd.ms-package.obfuscated-opentype",
		"icc":      "application/vnd.ms-color.iccprofile",
		"icm":      "application/vnd.ms-color.iccprofile",
	}
	if format != FormatXPS {
		defaults["x3d"] = "model/x3d+xml"
		defaults["x3db"] = "model/x3d+binary"
	}
	if excludePrintTicket {
		delete(defaults, "xml")
	}
	for _, rawExt := range slices.Sorted(maps.Keys(custom)) {
		media := custom[rawExt]
		ext, ok := opcNormalizeExtension(strings.TrimPrefix(rawExt, "."))
		if !ok {
			return nil, fmt.Errorf("%w: invalid early default extension %q", ErrInvalid, rawExt)
		}
		if err := validatePackageMediaForFormat(format, media); err != nil {
			return nil, err
		}
		defaults[ext] = media
	}
	return defaults, nil
}

// matchEarlyDefaultContentType 按方言与OPC规则判断部件媒体类型是否与前置Default表声明一致，OpenXPS下放行带合法MIME参数的非禁参媒体类型
// 入参: format 文档方言, media 待写部件实际媒体类型, expected 前置Default声明的媒体类型
// 返回: bool 媒体类型是否兼容
func matchEarlyDefaultContentType(format Format, media, expected string) bool {
	if format == FormatOpenXPS && !strings.Contains(expected, ";") {
		return matchStandardContentType(format, media, expected)
	}
	return strings.EqualFold(media, expected)
}

// validateEarlyContentTypeLocked 校验EarlyContentTypes模式下目标部件扩展名与预声明Default类型一致
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
	if !matchEarlyDefaultContentType(w.format, media, expected) {
		return fmt.Errorf("%w: part %s content type %q conflicts with early default %q", ErrInvalid, part, media, expected)
	}
	return nil
}

// initEarlyStreamLocked 在EarlyContentTypes模式下于流最前端写出[Content_Types].xml并打开包根关系、可选释放提示与文档序列分片流
// 入参: ctx 已规范化取消Context
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) initEarlyStreamLocked(ctx context.Context) error {
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
		return w.failLocked(err)
	}
	if w.autoDiscard {
		if err := w.ensureEarlyDiscardStreamLocked(ctx); err != nil {
			return w.failLocked(err)
		}
	} else if err := w.flushStreamRelationsLocked(ctx, "/"); err != nil {
		return w.failLocked(err)
	}
	return w.failLocked(w.openPieceStreamLocked(ctx, w.sequence, fixedContentType("fixeddocumentsequence"), `<FixedDocumentSequence xmlns="`+ns+`">`, `</FixedDocumentSequence>`))
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
// 当存在尚未落盘的后置远程资源字典时暂缓刷出该批早释放提示，避免违反ECMA-388§10.2.3提前释放传递依赖资源
// 入参: ctx 已规范化取消Context, sentinelPage 即将落盘的新页面URI, nextPageDeps 新页面展开依赖集合
// 返回: error 编码、预算、取消或写出错误
func (w *StreamWriter) flushEarlyDiscardsForNextPageLocked(ctx context.Context, sentinelPage string, nextPageDeps []streamResourceRef) error {
	if len(w.releasedAfter) == 0 {
		return nil
	}
	if len(w.pendingDicts) != 0 {
		return nil
	}
	nextUsed := make(map[string]bool, len(nextPageDeps))
	for _, dep := range nextPageDeps {
		depKey := strings.ToLower(dep.part)
		if dep.kind == requiredDictionary {
			if _, written := w.parts[depKey]; !written {
				return nil
			}
		}
		nextUsed[depKey] = true
	}
	protected := make(map[string]bool)
	markProtected := func(source string, skipRestricted bool) {
		w.visitProtectedRelationsLocked(source, skipRestricted, func(target string) {
			protected[strings.ToLower(target)] = true
		})
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
		effective := w.releasedAfter[key]
		if lastIdx, used := w.resourceLastPage[key]; used && lastIdx > effective {
			effective = lastIdx
		}
		if effective >= nextPageIdx || nextUsed[key] || protected[key] {
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

// failLocked 在已触碰底层ZIP流或持久状态后记录首个失败错误以毒化写出器，防止半残流继续写入
// 入参: err 操作返回的错误
// 返回: error 原样透传的错误
func (w *StreamWriter) failLocked(err error) error {
	if err != nil && w.failed == nil {
		w.failed = err
	}
	return err
}

// checkAppendStreamBudgetLocked 预检向已打开分片流追加指定字节数是否满足单部件与整包字节预算
// 入参: part 目标分片流部件URI, addBytes 待追加字节数
// 返回: error 状态或预算超限错误
func (w *StreamWriter) checkAppendStreamBudgetLocked(part string, addBytes int64) error {
	if addBytes <= 0 {
		return nil
	}
	stream := w.openStreams[strings.ToLower(part)]
	if stream == nil || stream.closed {
		return fmt.Errorf("%w: stream part %s is not open", ErrInvalid, part)
	}
	maxPart := w.limits.MaxPartBytes
	if opcRelationshipName(stream.part) {
		maxPart = min(maxPart, w.limits.MaxMetadataBytes)
	}
	if addBytes > maxPart-stream.bytes {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if addBytes > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	return nil
}

// streamClosingBytesLocked 返回指定打开分片流闭合尾标签所需的字节长度，未打开或已闭合返回0
// 入参: part 目标部件URI
// 返回: int64 闭合尾标签字节数
func (w *StreamWriter) streamClosingBytesLocked(part string) int64 {
	stream := w.openStreams[strings.ToLower(part)]
	if stream == nil || stream.closed {
		return 0
	}
	return int64(len(stream.closing))
}

// pendingReadyPageRelClosingBytesLocked 统计当前全部可立即闭合页面.fpage.rels尾标签总字节数
// 返回: int64 待闭合页面关系尾标签总字节数
func (w *StreamWriter) pendingReadyPageRelClosingBytesLocked() int64 {
	var total int64
	for key, pagePart := range w.openPageRels {
		if !w.lateDictSources[key] {
			total += w.streamClosingBytesLocked(createdRelationshipPart(pagePart))
		}
	}
	return total
}

// canWritePartWithRelLocked 写前统一预检新部件及伴生.rels逻辑部件总数、单部件与整包字节预算及前置内容类型表
// 入参: part 目标新部件URI, relSource 关系源部件URI或/, media 新部件内容类型, size 新部件字节长度
// 返回: error 类型、预算或部件上限错误
func (w *StreamWriter) canWritePartWithRelLocked(part, relSource, media string, size int64) error {
	if err := validatePackageMediaForFormat(w.format, media); err != nil {
		return err
	}
	if err := w.validateEarlyContentTypeLocked(part, media); err != nil {
		return err
	}
	if size > w.limits.MaxPartBytes {
		return fmt.Errorf("%w: stream part exceeds MaxPartBytes", ErrLimit)
	}
	if size > w.limits.MaxPackageBytes-w.partBytes {
		return fmt.Errorf("%w: stream package exceeds MaxPackageBytes", ErrLimit)
	}
	needed := 0
	if !w.registry.has(part) {
		needed++
	}
	relPart := createdRelationshipPart(relSource)
	if !w.registry.has(relPart) && !strings.EqualFold(relPart, part) {
		needed++
	}
	if w.registry.count()+needed > w.limits.MaxPartCount {
		return fmt.Errorf("%w: stream package part count", ErrLimit)
	}
	return nil
}

// trackOpenPageRelLocked 在EarlyContentTypes模式下将已打开的页面.fpage.rels登记至待闭合集合，确保无依赖页后补元数据可及时闭合
// 入参: source 关系源部件URI
func (w *StreamWriter) trackOpenPageRelLocked(source string) {
	if !w.earlyContentTypes || w.partScopeLocked(source) != PrintScopePage {
		return
	}
	relKey := strings.ToLower(createdRelationshipPart(source))
	if stream := w.openStreams[relKey]; stream != nil && !stream.closed {
		w.openPageRels[strings.ToLower(source)] = source
	}
}

// closeReadyPageRelsLocked 闭合全部不再等待后置远程字典的已打开页面.fpage.rels分片流
// 入参: ctx 已规范化取消Context
// 返回: error 预算、取消或写出错误
func (w *StreamWriter) closeReadyPageRelsLocked(ctx context.Context) error {
	for _, key := range slices.Sorted(maps.Keys(w.openPageRels)) {
		if w.lateDictSources[key] {
			continue
		}
		pagePart := w.openPageRels[key]
		if err := w.closePieceStreamLocked(ctx, createdRelationshipPart(pagePart)); err != nil {
			return err
		}
		delete(w.openPageRels, key)
	}
	return nil
}

// onLateDictWrittenLocked 在后置远程资源字典落盘后清理待定标记并更新依赖该字典的已提交页面资源最后使用页号
// 入参: dictKey 小写远程字典部件URI键
func (w *StreamWriter) onLateDictWrittenLocked(dictKey string) {
	delete(w.pendingDicts, dictKey)
	for _, rec := range w.pageDeps {
		expanded := w.expandDependenciesRecursiveLocked(rec.deps)
		for _, dep := range expanded {
			depKey := strings.ToLower(dep.part)
			if prev, seen := w.resourceLastPage[depKey]; !seen || rec.pageIndex > prev {
				w.resourceLastPage[depKey] = rec.pageIndex
			}
			if dep.kind == requiredDictionary {
				if _, written := w.parts[depKey]; !written {
					w.pendingDicts[depKey] = true
				}
			}
		}
	}
}

// flushResolvedLateSourcesLocked 检查已落盘后置远程字典或字体所解除阻塞的延迟页面与文档，刷出新增关系并解除延迟标记
// 入参: ctx 已规范化取消Context
// 返回: error 关系或写出错误
func (w *StreamWriter) flushResolvedLateSourcesLocked(ctx context.Context) error {
	if len(w.lateDictSources) == 0 {
		return nil
	}
	ns := formatNamespace(w.format)
	reqType := ns + "/required-resource"
	resType := ns + "/restricted-font"
	docStillPending := make(map[string]bool)
	for _, rec := range w.pageDeps {
		pageKey := strings.ToLower(rec.pagePart)
		docKey := strings.ToLower(rec.docPart)
		if !w.lateDictSources[pageKey] && !w.lateDictSources[docKey] {
			continue
		}
		expanded := w.expandDependenciesRecursiveLocked(rec.deps)
		pagePendingDict := false
		docPending := false
		for _, dep := range expanded {
			depKey := strings.ToLower(dep.part)
			if _, written := w.parts[depKey]; !written {
				if dep.kind == requiredDictionary {
					pagePendingDict = true
					docPending = true
				} else if dep.kind == requiredFont {
					docPending = true
				}
			}
			if err := w.appendRelationLocked(rec.pagePart, reqType, dep.part, false); err != nil {
				return err
			}
			if dep.hasFace {
				faceKey := fontCacheKey{part: depKey, index: dep.faceIndex}
				if w.prohibitedFaces[faceKey] {
					return fmt.Errorf("%w: font %s#%d prohibits embedding", ErrRestricted, dep.part, dep.faceIndex)
				}
				if w.needObfFaces[faceKey] {
					return fmt.Errorf("%w: font %s#%d requires obfuscation", ErrRestricted, dep.part, dep.faceIndex)
				}
				if w.restrictedFaces[faceKey] {
					if err := w.appendRelationLocked(rec.docPart, resType, dep.part, false); err != nil {
						return err
					}
				}
			}
		}
		if err := w.flushStreamRelationsLocked(ctx, rec.pagePart); err != nil {
			return err
		}
		w.trackOpenPageRelLocked(rec.pagePart)
		if err := w.flushStreamRelationsLocked(ctx, rec.docPart); err != nil {
			return err
		}
		if !pagePendingDict {
			delete(w.lateDictSources, pageKey)
		}
		if docPending {
			docStillPending[docKey] = true
		}
	}
	for _, doc := range w.documents {
		docKey := strings.ToLower(doc.Part)
		if w.lateDictSources[docKey] && !docStillPending[docKey] {
			delete(w.lateDictSources, docKey)
		}
	}
	return nil
}

// validateStreamNavigationAndStoriesLocked 在Close阶段终检页面与字典NavigateUri、目录OutlineEntry.Target、StoryFragmentReference与NamedElement交叉存在性
// 入参: ctx 已规范化取消Context
// 返回: error 导航目标、目录锚点、故事片段或命名元素缺失错误
func (w *StreamWriter) validateStreamNavigationAndStoriesLocked(ctx context.Context) error {
	navParts := make(map[string]createdNavigationKind, len(w.documents)+len(w.allPages)+1)
	docIndexByKey := make(map[string]int, len(w.documents))
	docTargets := make([]map[string]bool, len(w.documents))
	allTargets := make(map[string]bool)
	navParts[strings.ToLower(w.sequence)] = createdNavigationSequence
	for docIdx, doc := range w.documents {
		docKey := strings.ToLower(doc.Part)
		navParts[docKey] = createdNavigationDocument
		docIndexByKey[docKey] = docIdx
		targets := make(map[string]bool)
		for _, page := range doc.Pages {
			pageKey := strings.ToLower(page.Part)
			navParts[pageKey] = createdNavigationPage
			for _, name := range page.LinkTargets {
				targets[name] = true
				allTargets[name] = true
			}
		}
		docTargets[docIdx] = targets
	}
	validateTarget := func(sourcePart, raw string, allowEmpty bool) error {
		value := structureURI(raw)
		if value == "" {
			if allowEmpty {
				return nil
			}
			return fmt.Errorf("%w: empty navigation URI on %s", ErrInvalid, sourcePart)
		}
		if linkExternal(value) {
			return nil
		}
		uri, err := url.Parse(value)
		if err != nil {
			return fmt.Errorf("%w: navigation URI: %w", ErrInvalid, err)
		}
		targetPart := sourcePart
		if uri.Path != "" {
			targetPart, err = resolvePart(sourcePart, uri.EscapedPath())
			if err != nil {
				return err
			}
		}
		targetKey := strings.ToLower(targetPart)
		kind := navParts[targetKey]
		if kind == createdNavigationOther {
			if _, exists := w.parts[targetKey]; !exists {
				return fmt.Errorf("%w: navigation target part %s does not exist", ErrInvalid, targetPart)
			}
		}
		if uri.Fragment == "" {
			return nil
		}
		if linkPageNumber(uri.Fragment) {
			if kind != createdNavigationSequence {
				return fmt.Errorf("%w: M9.8 page address must target the fixed document sequence", ErrInvalid)
			}
			number, parseErr := strconv.ParseUint(uri.Fragment, 10, 64)
			if parseErr != nil || number < 1 || number > uint64(len(w.allPages)) {
				return fmt.Errorf("%w: navigation page number #%s out of range (1..%d)", ErrInvalid, uri.Fragment, len(w.allPages))
			}
			return nil
		}
		if kind == createdNavigationPage {
			return fmt.Errorf("%w: M9.4 named address must target a fixed document or sequence", ErrInvalid)
		}
		if kind == createdNavigationDocument {
			docIdx := docIndexByKey[targetKey]
			if !docTargets[docIdx][uri.Fragment] {
				return fmt.Errorf("%w: navigation LinkTarget %q does not exist in %s", ErrInvalid, uri.Fragment, targetPart)
			}
		} else if kind == createdNavigationSequence {
			if !allTargets[uri.Fragment] {
				return fmt.Errorf("%w: navigation LinkTarget %q does not exist in %s", ErrInvalid, uri.Fragment, targetPart)
			}
		}
		return nil
	}
	for _, ref := range w.pageNavRefs {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if err := validateTarget(ref.sourcePart, ref.target, false); err != nil {
			return &PartError{Part: ref.sourcePart, Err: fmt.Errorf("FixedPage.NavigateUri: %w", err)}
		}
	}
	for _, rec := range w.pageDeps {
		if err := checkContext(ctx); err != nil {
			return err
		}
		expanded := w.expandDependenciesRecursiveLocked(rec.deps)
		for _, dep := range expanded {
			if dep.kind != requiredDictionary {
				continue
			}
			for _, navTarget := range w.dictNavRefs[strings.ToLower(dep.part)] {
				if err := validateTarget(rec.pagePart, navTarget, false); err != nil {
					return &PartError{Part: dep.part, Err: fmt.Errorf("FixedPage.NavigateUri: %w", err)}
				}
			}
		}
	}
	for docIdx, doc := range w.documents {
		if err := checkContext(ctx); err != nil {
			return err
		}
		docStruct := w.docStructures[docIdx]
		if docStruct != nil {
			for _, outlineTarget := range docStruct.outlineTargets {
				if err := validateTarget(docStruct.part, outlineTarget, true); err != nil {
					return &PartError{Part: docStruct.part, Element: "OutlineEntry", Err: err}
				}
			}
		}
		locations := make(map[contentFragmentKey]int)
		fragmentNames := make(map[contentFragmentKey]bool)
		for local, page := range doc.Pages {
			pageKey := strings.ToLower(page.Part)
			pageStory := w.pageStories[pageKey]
			if pageStory == nil {
				continue
			}
			for _, frag := range pageStory.fragments {
				if frag.storyName != nil {
					if docStruct == nil || !docStruct.storyNames[*frag.storyName] {
						return &PartError{Part: pageStory.part, Element: "StoryFragment", Err: fmt.Errorf("%w: story %q is not defined in its fixed document", ErrInvalid, *frag.storyName)}
					}
					key := contentFragmentKey{page: local, story: *frag.storyName}
					locations[key]++
					if frag.fragmentName != nil {
						key.named, key.name = true, *frag.fragmentName
						locations[key]++
						identity := contentFragmentKey{story: key.story, name: key.name, named: true}
						if fragmentNames[identity] {
							return &PartError{Part: pageStory.part, Element: "StoryFragment", Err: fmt.Errorf("%w: duplicate fragment name %q in story %q", ErrInvalid, key.name, key.story)}
						}
						fragmentNames[identity] = true
					}
				}
			}
			names := w.pageNames[pageKey]
			for _, namedRef := range pageStory.namedRefs {
				if !names[namedRef] {
					return &PartError{Part: pageStory.part, Element: "StoryFragment", Err: fmt.Errorf("%w: named element %q is absent from page %s", ErrInvalid, namedRef, page.Part)}
				}
			}
		}
		if docStruct != nil {
			for _, ref := range docStruct.storyRefs {
				key := contentFragmentKey{page: ref.pageNumber - 1, story: ref.storyName}
				if ref.fragmentName != nil {
					key.named, key.name = true, *ref.fragmentName
				}
				if ref.pageNumber < 1 || ref.pageNumber > len(doc.Pages) || locations[key] != 1 {
					return &PartError{Part: docStruct.part, Element: "StoryFragmentReference", Err: fmt.Errorf("%w: story %q page %d identifies %d fragments", ErrInvalid, ref.storyName, ref.pageNumber, locations[key])}
				}
			}
		}
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
	return layoutPartScope(w.sequence, w.documents, source)
}

// findHashLocked 在已落盘资源哈希索引中查找未释放且媒体类型与字节长度均一致的复用部件
// 入参: digest 内容SHA-256摘要, media 内容类型, size 原始字节长度
// 返回: string 已有部件URI, bool 是否命中复用
func (w *StreamWriter) findHashLocked(digest [32]byte, media string, size int) (string, bool) {
	for _, entry := range w.hashes[digest] {
		if entry.size == size && strings.EqualFold(entry.media, media) {
			key := strings.ToLower(entry.name)
			if _, discarded := w.emittedDiscardPage[key]; discarded {
				continue
			}
			if _, released := w.releasedAfter[key]; released {
				continue
			}
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
	return allocateObfuscatedFontPart(w.availableLocked)
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
	if index, ok := extractAllocatedPatternIndex(pattern, part); ok {
		w.allocated[pattern] = index
	}
}
