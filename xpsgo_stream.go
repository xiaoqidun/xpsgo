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
	"bufio"
	"bytes"
	"compress/flate"
	"container/list"
	"context"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"hash/crc32"
	"io"
	"io/fs"
	"maps"
	"math"
	"slices"
	"strings"
	"sync"
)

// streamCacheBytes 规定默认流式解压资源缓存容量，不包含活动渲染器或原压缩存储
const streamCacheBytes = 16 << 20

// streamBufferBytes 规定输入存储和载荷校验的复用块大小
const streamBufferBytes = 32 << 10

// streamXMLSlots 规定默认活动XML解析状态数量，不限制延迟到完整部件后处理的XML数量
const streamXMLSlots = 16

const (
	// StreamTicketsStrict 严格等待所有潜在关系及打印票据部件到达后再交付页面
	StreamTicketsStrict StreamTicketPolicy = iota
	// StreamTicketsInterleaved 按交错流顺序约定仅等待已到达关系声明的打印票据，避免默认rels扩展挂起页面交付
	StreamTicketsInterleaved
)

// StreamTicketPolicy 控制前向流交付页面前对打印票据及关系部件的等待策略
type StreamTicketPolicy uint8

// StreamReadOptions 设置前向流读取的存储、预算、票据等待策略与回调，MaxInputBytes与MaxMemoryBytes零值沿用MaxPackageBytes（默认1GiB）
// Storage为nil使用有界内存并在Reader.Close或ConsumeStream结束时释放，外部Storage不由库关闭；MaxCacheBytes默认16MiB，MaxXMLStreams默认16
// TicketPolicy零值为StreamTicketsStrict，Windows交错假脱机流推荐使用StreamTicketsInterleaved
// OnPart、OnPage、OnDiscard、OnXML、OnCoreProperties、OnDocumentStructure、OnJobPrintTicket、OnDocumentStart与OnDocumentEnd回调交付临时视图，Read或ConsumeStream成功返回后方确认整包完整有效
type StreamReadOptions struct {
	Limits              Limits
	MaxInputBytes       int64
	MaxMemoryBytes      int64
	MaxCacheBytes       int64
	MaxXMLStreams       int
	TicketPolicy        StreamTicketPolicy
	Storage             StreamStorage
	OnPart              func(context.Context, PartInfo, io.Reader) error
	OnPage              func(context.Context, *StreamPage) error
	OnDiscard           func(context.Context, StreamDiscard) error
	OnXML               func(context.Context, PartInfo, StreamXMLToken) error
	OnCoreProperties    func(context.Context, *CoreProperties) error
	OnDocumentStructure func(context.Context, int, *DocumentStructure) error
	OnJobPrintTicket    func(context.Context, *PrintSettings) error
	OnDocumentStart     func(context.Context, StreamDocumentEvent) error
	OnDocumentEnd       func(context.Context, StreamDocumentEvent) error
}

// StreamDocumentEvent 描述前向流中固定文档的开始或结束边界事件及当前读取进度
type StreamDocumentEvent struct {
	DocumentIndex int
	Part          string
	PageCount     int
	BytesRead     int64
}

// StreamProgress 描述前向流当前的字节读取进度、页面发现与交付计数及已完结文档计数
type StreamProgress struct {
	BytesRead          int64
	DeliveredPages     int
	DiscoveredPages    int
	DeliveredDocuments int
}

// streamEntry 保存已经消费并校验的物理载荷范围，不分配完整解压部件
type streamEntry struct {
	header            zip.FileHeader
	offset            int64
	data              int64
	finish            int64
	localZIP64        bool
	headerFreed       bool
	payloadFreed      bool
	headerFreedBytes  int64
	payloadFreedBytes int64
	trailerFreedBytes int64
}

// streamPart 保存完整或待组装的逻辑部件，last为末片编号，whole排除整部件和分片混用
type streamPart struct {
	name                 string
	entries              map[int]*streamEntry
	last                 int
	bytes                uint64
	whole                bool
	emitted              bool
	reclaimed            bool
	partiallyReclaimed   bool
	reclaimPending       bool
	relsVerified         bool
	relsRecorded         bool
	pageDelivered        bool
	deliveredRelsClosed  bool
	deliveredPageTicket  string
	ticketVerifiedScopes uint8
	xml                  *streamXMLParser
	xmlNext              int
	xmlTokens            int
	xmlDone              bool
	xmlDeferred          bool
	xmlMetadata          bool
	xmlReplay            int
	control              *streamPartialDiscard
	layout               *streamPartialLayout
	relations            *streamPartialRelationships
	page                 *streamPartialPage
}

// streamDeliveredPage 保存已交付页面的完结状态、关系快照、依赖资源与三级票据，用于EOF跳过未变更页重复全解析
type streamDeliveredPage struct {
	partComplete  bool
	relsPart      string
	relsComplete  bool
	relsCount     int
	resourceParts []string
	tickets       []string
}

// streamTicketCacheKey 标识按票据部件、作用域及解析预算区分的缓存键
type streamTicketCacheKey struct {
	part                 string
	scope                PrintScope
	limits               Limits
	maxNumericDigits     int
	maxOptionComparisons int
}

// streamCachedTicket 保存已解析并校验通过的打印设置及原始票据字节数
type streamCachedTicket struct {
	settings *PrintSettings
	size     int64
}

// streamPackage 保存前向读取的物理索引、逻辑部件组装状态及内容类型表
type streamPackage struct {
	input                *streamInput
	options              StreamReadOptions
	context              context.Context
	consumeOnly          bool
	ownedMemory          *streamMemory
	reclaimed            bool
	centralVerified      bool
	entries              []*streamEntry
	parts                map[string]*streamPart
	seen                 map[string]bool
	types                *packageReader
	bytes                uint64
	deferred             bool
	pagePkg              *packageReader
	index                *Reader
	pages                int
	pageValidated        bool
	pageWait             map[string]bool
	pageMissing          map[string]bool
	pageResources        []string
	pageHold             bool
	deliveredPages       []streamDeliveredPage
	documents            []string
	document             int
	documentKeys         map[string]bool
	sequenceRead         bool
	seenPages            map[string]bool
	pageNames            map[string]bool
	cache                *streamResourceCache
	discard              *streamDiscardState
	discardTarget        string
	xmlActive            int
	xmlNodes             int
	xmlBindings          int
	xmlQueue             []*streamPart
	xmlResuming          bool
	corePropsDelivered   bool
	corePropsCached      *CoreProperties
	corePropsTarget      string
	jobTicketDelivered   bool
	jobTicketTarget      string
	ticketTargets        map[string]string
	ticketSources        map[string]string
	ticketRequiredScopes map[string]uint8
	deliveredJobSet      bool
	deliveredJobTicket   string
	deliveredDocTickets  map[int]string
	docStructDelivered   map[int]bool
	docStructCached      map[int]*DocumentStructure
	docStructMaxPage     map[int]int
	docStructTargets     map[string]string
	reclaimedDocuments   map[int]bool
	activeDocument       int
	nextDocumentStart    int
	deliveredDocuments   int
	pendingEnvelopes     []*streamEntry
	pendingParts         map[string]bool
	pinnedParts          map[string]int
	onConsumeFinish      func(*Reader, bool) error
	ticketMu             sync.RWMutex
	ticketCache          map[streamTicketCacheKey]streamCachedTicket
}

// streamCachedResource 保存独立且不再修改的部件字节，活动读取器可在缓存淘汰后继续读取
type streamCachedResource struct {
	key  string
	data []byte
}

// streamResourceCache 保存有界最近使用资源及处理状态，缓存淘汰不删除原始部件
type streamResourceCache struct {
	mu        sync.Mutex
	limit     int64
	bytes     int64
	order     list.List
	entries   map[string]*list.Element
	processed map[string]bool
	changed   []string
}

// StreamDiscard 报告按DiscardControl提示移除的缓存引用，Bytes不含活动读取器仍持有的字节
// Late表示目标或提示在哨兵页面开始后就绪，Read成功前事件均为临时结果
type StreamDiscard struct {
	Hint  DiscardHint
	Bytes int64
	Late  bool
}

// streamDiscardState 按哨兵页面和未处理目标索引提示，不逐页扫描全部提示
type streamDiscardState struct {
	target     string
	checked    bool
	loaded     bool
	hints      []DiscardHint
	byPage     map[string][]int
	started    map[string]bool
	waiting    map[string][]int
	done       map[int]bool
	targetRefs map[string]int
}

// streamLimitedInput 为有明确压缩长度的载荷提供精确边界，不让Deflate缓冲越过描述符
type streamLimitedInput struct {
	input *streamInput
	left  uint64
}

// streamInput 记录真正消费的字节并批量存储，为Deflate提供不越过码流结尾的ReadByte
type streamInput struct {
	reader      *bufio.Reader
	storage     StreamStorage
	ownedMemory *streamMemory
	onLimit     func() int64
	context     context.Context
	limit       int64
	count       int64
	pending     []byte
}

// streamPartialDiscard 保存释放提示的根声明和已闭合子元素，不把未结束元素作为完整提示
type streamPartialDiscard struct {
	root     *xmlElement
	stack    []*xmlElement
	hints    []DiscardHint
	deferred bool
}

// streamLogicalReader 惰性解压已校验的物理范围，最多保持一个分片解压器，关闭后不可再读取
type streamLogicalReader struct {
	storage StreamStorage
	entries []*streamEntry
	context context.Context
	index   int
	current io.ReadCloser
	closed  bool
}

// StreamStorage 为前向输入提供随机访问存储，不要求操作系统文件或接管关闭责任
// 使用期间不得被外部修改；返回的Reader并发读取要求存储支持并发ReadAt
type StreamStorage interface {
	io.ReaderAt
	io.WriterAt
}

// streamMemory 按固定块保存实际到达的压缩容器，不按声明尺寸提前分配，纯前向消费模式支持按范围回收已释放块
type streamMemory struct {
	mu         sync.RWMutex
	chunks     [][]byte
	liveChunks map[int][]byte
	liveFreed  map[int]int
	chunkSize  int64
	size       int64
	live       int64
	limit      int64
	closed     bool
	reclaim    bool
}

// streamTailInput 为纯前向消费模式校验ZIP中央目录与结束记录提供受限计数读取，不占用压缩载荷内存
type streamTailInput struct {
	reader  *bufio.Reader
	context context.Context
	limit   int64
	count   int64
}

// StreamXMLToken 保存已校验的XML词元及UTF-8字节范围（不含BOM），Depth以根元素为零
// Token与Namespaces独立于解析器可由调用方保留，Read成功前均为临时结果
type StreamXMLToken struct {
	Token      xml.Token
	Namespaces map[string]string
	Depth      int
	Start      int64
	End        int64
}

// streamXMLChunk 传递已校验物理分片的解压游标，last表示逻辑部件输入结束
type streamXMLChunk struct {
	input io.ReadCloser
	last  bool
}

// streamXMLEvent 在调用线程传递独立词元、输入边界或最终解析结果
type streamXMLEvent struct {
	token *StreamXMLToken
	need  bool
	err   error
}

// streamXMLParser 为一个逻辑XML保持持续解析状态，停止后等待解析Goroutine释放所有输入引用
type streamXMLParser struct {
	context  context.Context
	cancel   context.CancelFunc
	chunks   chan streamXMLChunk
	events   chan streamXMLEvent
	stop     chan struct{}
	done     chan struct{}
	stopOnce sync.Once
}

// streamXMLInput 在分片之间等待已校验的后续输入，不把临时缺少分片返回为EOF
type streamXMLInput struct {
	parser  *streamXMLParser
	current io.ReadCloser
	last    bool
}

// String 返回流式打印票据等待策略的可读名称
// 返回: string 策略名称
func (p StreamTicketPolicy) String() string {
	switch p {
	case StreamTicketsStrict:
		return "strict"
	case StreamTicketsInterleaved:
		return "interleaved"
	default:
		return fmt.Sprintf("StreamTicketPolicy(%d)", p)
	}
}

// DefaultStreamReadOptions 返回默认流式读取选项
// 返回: StreamReadOptions 流式读取选项
func DefaultStreamReadOptions() StreamReadOptions {
	limits := DefaultLimits()
	return StreamReadOptions{
		Limits:         limits,
		MaxInputBytes:  limits.MaxPackageBytes,
		MaxMemoryBytes: limits.MaxPackageBytes,
		MaxCacheBytes:  streamCacheBytes,
		MaxXMLStreams:  streamXMLSlots,
		TicketPolicy:   StreamTicketsStrict,
	}
}

// normalizeStreamReadOptions 合并并校验前向流读取参数，确保预算与策略合法
// 入参: ctx 取消Context, input 前向输入, options 调用方选项，nil采用默认值
// 返回: context.Context 规范化Context, StreamReadOptions 合并后选项, error 参数或取消错误
func normalizeStreamReadOptions(ctx context.Context, input io.Reader, options *StreamReadOptions) (context.Context, StreamReadOptions, error) {
	ctx = normalizeContext(ctx)
	configuration := StreamReadOptions{Limits: DefaultLimits()}
	if options != nil {
		configuration = *options
		configuration.Limits = mergeLimits(DefaultLimits(), options.Limits)
	}
	if configuration.MaxInputBytes == 0 {
		configuration.MaxInputBytes = configuration.Limits.MaxPackageBytes
	}
	if configuration.MaxMemoryBytes == 0 {
		configuration.MaxMemoryBytes = configuration.MaxInputBytes
	}
	if configuration.MaxCacheBytes == 0 {
		configuration.MaxCacheBytes = streamCacheBytes
	}
	if configuration.MaxXMLStreams == 0 {
		configuration.MaxXMLStreams = streamXMLSlots
	}
	if input == nil || configuration.MaxInputBytes < 1 || configuration.MaxMemoryBytes < 1 || configuration.MaxCacheBytes < 0 || configuration.MaxXMLStreams < 1 || configuration.OnDiscard != nil && configuration.OnPage == nil || configuration.TicketPolicy != StreamTicketsStrict && configuration.TicketPolicy != StreamTicketsInterleaved {
		return nil, StreamReadOptions{}, fmt.Errorf("%w: stream read parameters", ErrInvalid)
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return nil, StreamReadOptions{}, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, StreamReadOptions{}, err
	}
	return ctx, configuration, nil
}

// Read 从前向输入流式消费XPS或OpenXPS，在完整校验目录与载荷后返回支持随机读取的Reader，失败时返回nil
// 压缩容器保留于存储按需解压，不关闭输入与外部存储；回调交付均为临时结果，外部存储须在Reader期间保持不变
// 入参: ctx 取消Context，nil采用Background, input 前向输入, options 存储、预算及回调参数，nil采用默认值
// 返回: *Reader 完整验证的封装及文档索引，失败为nil, error 输入、封装、存储、回调、预算或取消错误
func Read(ctx context.Context, input io.Reader, options *StreamReadOptions) (*Reader, error) {
	ctx, configuration, err := normalizeStreamReadOptions(ctx, input, options)
	if err != nil {
		return nil, err
	}
	var owned *streamMemory
	storage := configuration.Storage
	if storage == nil {
		owned = &streamMemory{limit: min(configuration.MaxMemoryBytes, configuration.MaxInputBytes)}
		storage = owned
	}
	success := false
	defer func() {
		if !success && owned != nil {
			_ = owned.Close()
		}
	}()
	inputBytes := configuration.MaxInputBytes
	if inputBytes < math.MaxInt64 {
		inputBytes++
	}
	feed := &streamInput{reader: bufio.NewReaderSize(io.LimitReader(input, inputBytes), streamBufferBytes), storage: storage, context: ctx, limit: configuration.MaxInputBytes, pending: make([]byte, 0, streamBufferBytes)}
	p := streamPackage{input: feed, options: configuration, context: ctx, parts: make(map[string]*streamPart), seen: make(map[string]bool)}
	defer p.closeXML()
	if configuration.OnPage != nil {
		p.cache = &streamResourceCache{limit: min(configuration.MaxCacheBytes, configuration.Limits.MaxPartBytes, configuration.Limits.MaxPackageBytes)}
		defer p.cache.clear()
		p.discard = &streamDiscardState{started: make(map[string]bool), waiting: make(map[string][]int)}
	}
	if err := p.consume(); err != nil {
		return nil, normalizeStreamError(ctx, err)
	}
	if err := feed.flush(); err != nil {
		return nil, err
	}
	r, err := NewReader(ctx, storage, feed.count, &ReaderOptions{Limits: configuration.Limits})
	if err != nil {
		return nil, err
	}
	valid := false
	defer func() {
		if !valid {
			_ = r.Close()
		}
	}()
	if err := p.finalizeRandomAccess(r); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if owned != nil {
		r.closer = owned
	}
	success, valid = true, true
	return r, nil
}

// ConsumeStream 以纯前向恒定低内存模式消费XPS或OpenXPS流，不构造最终随机访问Reader
// 当Storage为nil时，收到DiscardControl哨兵或完成固定页面交付后立即释放已消费压缩分片并回收内存配额
// 入参: ctx 取消Context，nil采用Background, input 前向输入, options 存储、预算、票据策略及回调参数，nil采用默认值
// 返回: error 输入、封装、结构、存储、回调、预算或取消错误
func ConsumeStream(ctx context.Context, input io.Reader, options *StreamReadOptions) error {
	return consumeStreamInternal(ctx, input, options, nil)
}

// consumeStreamInternal 执行纯前向流式消费并在流收尾释放存储前触发可选完成钩子
// 入参: ctx 取消Context, input 前向输入, options 读取选项, onFinish 流消费完成时的收尾钩子
// 返回: error 输入、封装、结构、存储、回调、预算或取消错误
func consumeStreamInternal(ctx context.Context, input io.Reader, options *StreamReadOptions, onFinish func(*Reader, bool) error) error {
	ctx, configuration, err := normalizeStreamReadOptions(ctx, input, options)
	if err != nil {
		return err
	}
	var owned *streamMemory
	storage := configuration.Storage
	pendingCap := streamBufferBytes
	if storage == nil {
		owned = &streamMemory{limit: min(configuration.MaxMemoryBytes, configuration.MaxInputBytes), reclaim: true}
		storage = owned
		defer owned.Close()
		if owned.limit < int64(pendingCap) {
			pendingCap = int(max(owned.limit, 1))
		}
	}
	inputBytes := configuration.MaxInputBytes
	if inputBytes < math.MaxInt64 {
		inputBytes++
	}
	feed := &streamInput{reader: bufio.NewReaderSize(io.LimitReader(input, inputBytes), streamBufferBytes), storage: storage, ownedMemory: owned, context: ctx, limit: configuration.MaxInputBytes, pending: make([]byte, 0, pendingCap)}
	p := streamPackage{input: feed, options: configuration, context: ctx, consumeOnly: true, ownedMemory: owned, parts: make(map[string]*streamPart), seen: make(map[string]bool), onConsumeFinish: onFinish}
	if owned != nil {
		feed.onLimit = p.reclaimPendingStorage
	}
	defer p.closeXML()
	if configuration.OnPage != nil {
		p.cache = &streamResourceCache{limit: min(configuration.MaxCacheBytes, configuration.Limits.MaxPartBytes, configuration.Limits.MaxPackageBytes)}
		defer p.cache.clear()
		p.discard = &streamDiscardState{started: make(map[string]bool), waiting: make(map[string][]int)}
	}
	if err := p.consume(); err != nil {
		return normalizeStreamError(ctx, err)
	}
	if p.centralVerified {
		return p.finishConsume()
	}
	if p.reclaimed {
		return fmt.Errorf("%w: streamed input requires random access after memory reclamation", ErrUnsupported)
	}
	if err := feed.flush(); err != nil {
		return err
	}
	r, err := NewReader(ctx, storage, feed.count, &ReaderOptions{Limits: configuration.Limits})
	if err != nil {
		return err
	}
	defer r.Close()
	if err := p.finalizeRandomAccess(r); err != nil {
		return err
	}
	if err := p.verifyFallbackConsume(r); err != nil {
		return err
	}
	if p.onConsumeFinish != nil {
		if err := p.onConsumeFinish(r, true); err != nil {
			return err
		}
	}
	return checkContext(ctx)
}

// finalizeRandomAccess 在随机访问回退构造Reader后完成目录核对、关系与XML校验及剩余回调收尾
// 入参: r 已构造的随机访问阅读器
// 返回: error 核对、关系、XML、回调、预算或取消错误
func (p *streamPackage) finalizeRandomAccess(r *Reader) error {
	if err := p.reconcile(r); err != nil {
		return err
	}
	if err := p.finishRelationships(r); err != nil {
		return err
	}
	if err := p.finishXML(r); err != nil {
		return err
	}
	if p.cache != nil {
		r.pkg.cache = p.cache
		defer func() { r.pkg.cache = nil }()
	}
	if err := p.emitRemaining(r); err != nil {
		return err
	}
	if err := p.finishMetadataCallbacks(r); err != nil {
		return err
	}
	if err := p.finishPages(r); err != nil {
		return err
	}
	return p.advanceDocumentEvents(r, true)
}

// needsIndex 判断当前流式消费是否需要建立临时包后端与文档索引
// 返回: bool 是否需要建立索引
func (p *streamPackage) needsIndex() bool {
	return p.consumeOnly || p.options.OnPage != nil || p.options.OnCoreProperties != nil || p.options.OnDocumentStructure != nil || p.options.OnJobPrintTicket != nil || p.options.OnDocumentStart != nil || p.options.OnDocumentEnd != nil
}

// consume 顺序处理可确定边界的本地条目，遇到中央记录或不明确边界时按模式执行流式校验或延迟接收
// 返回: error 输入、物理记录、载荷、回调或资源错误
func (p *streamPackage) consume() error {
	buffer := make([]byte, streamBufferBytes)
	for {
		if err := checkContext(p.context); err != nil {
			return err
		}
		offset := p.input.count
		var signature [4]byte
		if _, err := io.ReadFull(p.input, signature[:]); err != nil {
			return p.streamInputError("stream ZIP record", err)
		}
		sig := binary.LittleEndian.Uint32(signature[:])
		if sig != packageZIPLocalSignature {
			if p.consumeOnly && offset != 0 && (sig == packageZIPCentralSignature || sig == packageZIPEndSignature || sig == packageZIP64EndSignature || sig == packageZIPDigitalSignature) {
				if p.ownedMemory != nil {
					p.reclaimRangeProgress(offset, p.input.count, true)
				}
				return p.verifyStreamCentralDirectory(sig, offset)
			}
			if offset == 0 {
				p.deferred = true
			}
			if err := writeCompressionInput(io.Discard, p.input, buffer, p.context); err != nil {
				return normalizeStreamError(p.context, err)
			}
			return nil
		}
		if len(p.entries) >= p.options.Limits.MaxPartCount {
			return fmt.Errorf("%w: streamed ZIP entry count", ErrLimit)
		}
		entry, unknown, err := p.readEntry(offset, buffer)
		if err != nil {
			return normalizeStreamError(p.context, err)
		}
		if unknown {
			if p.consumeOnly && p.reclaimed {
				return fmt.Errorf("%w: streamed entry requires random access after memory reclamation", ErrUnsupported)
			}
			p.deferred = true
			return normalizeStreamError(p.context, writeCompressionInput(io.Discard, p.input, buffer, p.context))
		}
		if p.consumeOnly && p.ownedMemory != nil {
			p.reclaimEntryEnvelope(entry)
		}
		if err := p.accept(entry); err != nil {
			return err
		}
	}
}

// accept 检查物理及逻辑身份，组装完整分片后解析内容类型或发出临时部件
// 入参: entry 已校验物理条目
// 返回: error 身份、分片、元数据、预算或回调错误
func (p *streamPackage) accept(entry *streamEntry) error {
	name := entry.header.Name
	key := strings.ToLower(name)
	if p.seen[key] {
		return fmt.Errorf("%w: duplicate streamed ZIP item %s", ErrInvalid, name)
	}
	p.seen[key] = true
	p.entries = append(p.entries, entry)
	if strings.HasSuffix(name, "/") {
		if entry.header.UncompressedSize64 != 0 {
			return fmt.Errorf("%w: nonempty streamed directory", ErrInvalid)
		}
		dir := strings.TrimSuffix(name, "/")
		if !strings.EqualFold(dir, strings.TrimPrefix(opcTypesName, "/")) {
			if _, err := opcPartName("/" + dir); err != nil {
				return fmt.Errorf("directory: %w", err)
			}
		}
		if p.consumeOnly && p.ownedMemory != nil && !entry.payloadFreed {
			p.reclaimEntryPayloadMode(entry, true)
		}
		return nil
	}
	partName, index, last, err := opcPieceName(name)
	if err != nil {
		return err
	}
	if strings.EqualFold(partName, strings.TrimPrefix(opcTypesName, "/")) {
		partName = opcTypesName
	} else {
		partName, err = opcPartName("/" + partName)
		if err != nil {
			return err
		}
	}
	key = strings.ToLower(partName)
	part := p.parts[key]
	if part == nil {
		part = &streamPart{name: partName, last: -1, entries: make(map[int]*streamEntry)}
		p.parts[key] = part
	}
	if part.reclaimed {
		return fmt.Errorf("%w: streamed piece after completed part", ErrInvalid)
	}
	if index == -1 {
		if len(part.entries) != 0 {
			return fmt.Errorf("%w: streamed whole part and pieces", ErrInvalid)
		}
		part.whole, part.last, index = true, 0, 0
	} else if part.whole || part.emitted || part.last >= 0 && index > part.last {
		return fmt.Errorf("%w: streamed piece after completed part", ErrInvalid)
	}
	if _, duplicate := part.entries[index]; duplicate {
		return fmt.Errorf("%w: repeated streamed piece number", ErrInvalid)
	}
	if last {
		if part.last >= 0 {
			return fmt.Errorf("%w: repeated streamed last piece", ErrInvalid)
		}
		part.last = index
		for existing := range part.entries {
			if existing > index {
				return fmt.Errorf("%w: streamed piece beyond last", ErrInvalid)
			}
		}
	}
	if entry.header.UncompressedSize64 > uint64(p.options.Limits.MaxPartBytes)-part.bytes {
		return fmt.Errorf("%w: streamed logical part bytes", ErrLimit)
	}
	part.bytes += entry.header.UncompressedSize64
	part.entries[index] = entry
	if part.last < 0 || len(part.entries) != part.last+1 {
		return p.emit(part)
	}
	if err := p.input.flush(); err != nil {
		return err
	}
	if key == strings.ToLower(opcTypesName) {
		if part.bytes > uint64(p.options.Limits.MaxMetadataBytes) {
			return fmt.Errorf("%w: streamed content types bytes", ErrLimit)
		}
		if p.options.OnPart == nil && !p.needsIndex() && p.options.OnXML == nil && !p.consumeOnly {
			part.emitted = true
			return nil
		}
		reader := p.partReader(part)
		limit := p.options.Limits.MaxMetadataBytes
		if limit < math.MaxInt64 {
			limit++
		}
		data, err := io.ReadAll(io.LimitReader(reader, limit))
		closeErr := reader.Close()
		if err != nil {
			return err
		}
		if closeErr != nil {
			return closeErr
		}
		if int64(len(data)) > p.options.Limits.MaxMetadataBytes {
			return fmt.Errorf("%w: streamed content types bytes", ErrLimit)
		}
		p.types = &packageReader{limits: p.options.Limits, defaults: make(map[string]string), overrides: make(map[string]string)}
		if err := p.types.parseContentTypes(data); err != nil {
			return err
		}
		part.emitted = true
		if p.consumeOnly && p.ownedMemory != nil {
			p.reclaimPart(key)
		}
		for _, known := range slices.SortedFunc(maps.Values(p.parts), func(a, b *streamPart) int { return strings.Compare(a.name, b.name) }) {
			if err := p.emit(known); err != nil {
				return err
			}
		}
		return nil
	}
	return p.emit(part)
}

// streamInputError 透传取消、限额、关闭及短写错误，其余底层流读取错误归类为格式无效
// 入参: label 错误位置说明, err 原始错误
// 返回: error 保留原分类或归类为ErrInvalid的错误
func (p *streamPackage) streamInputError(label string, err error) error {
	err = normalizeStreamError(p.context, err)
	if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) || errors.Is(err, ErrLimit) || errors.Is(err, ErrClosed) || errors.Is(err, io.ErrShortWrite) {
		return err
	}
	return fmt.Errorf("%w: %s: %w", ErrInvalid, label, err)
}

// normalizeStreamError 还原被本地条目读取包装的Context取消错误，避免误判为文档结构无效
// 入参: ctx 流读取Context, err 原始错误
// 返回: error 规范化错误
func normalizeStreamError(ctx context.Context, err error) error {
	if err == nil {
		return nil
	}
	if ctxErr := checkContext(ctx); ctxErr != nil {
		if errors.Is(err, ctxErr) || errors.Is(err, io.EOF) || errors.Is(err, io.ErrUnexpectedEOF) || errors.Is(err, io.ErrClosedPipe) {
			return ctxErr
		}
	}
	return err
}

// get 借用只读缓存字节并更新使用顺序，调用方不得修改返回数据
// 入参: key 规范化部件键
// 返回: []byte 只读资源, bool 是否命中
func (c *streamResourceCache) get(key string) ([]byte, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	entry := c.entries[key]
	if entry == nil {
		return nil, false
	}
	c.order.MoveToFront(entry)
	return entry.Value.(*streamCachedResource).data, true
}

// put 标记完整读取并按容量保存可缓存资源，过大资源不进入缓存，也不阻止正常处理
// 入参: key 规范化部件键, data 完整读取结果, cacheable 是否为图形资源
func (c *streamResourceCache) put(key string, data []byte, cacheable bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.markLocked(key)
	if !cacheable || int64(len(data)) > c.limit || c.limit == 0 {
		return
	}
	if entry := c.entries[key]; entry != nil {
		c.order.MoveToFront(entry)
		return
	}
	for c.bytes > c.limit-int64(len(data)) {
		c.removeLocked(c.order.Back())
	}
	if c.entries == nil {
		c.entries = make(map[string]*list.Element)
	}
	resource := &streamCachedResource{key: key, data: append([]byte(nil), data...)}
	c.entries[key] = c.order.PushFront(resource)
	c.bytes += int64(len(resource.data))
}

// mark 记录已完成部件回调或完整读取的部件，供尚未知目标的释放提示恢复执行
// 入参: key 规范化部件键
func (c *streamResourceCache) mark(key string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.markLocked(key)
}

// markLocked 在持有缓存锁时记录首次处理状态，不为重复读取累计通知
// 入参: key 规范化部件键
func (c *streamResourceCache) markLocked(key string) {
	if c.processed[key] {
		return
	}
	if c.processed == nil {
		c.processed = make(map[string]bool)
	}
	c.processed[key] = true
	c.changed = append(c.changed, key)
}

// wasProcessed 检查目标是否已被当前消费者完整读取或处理
// 入参: key 规范化部件键
// 返回: bool 是否已处理
func (c *streamResourceCache) wasProcessed(key string) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.processed[key]
}

// takeProcessed 取出新增处理状态，避免逐页扫描所有等待提示
// 返回: []string 首次处理的部件键
func (c *streamResourceCache) takeProcessed() []string {
	c.mu.Lock()
	defer c.mu.Unlock()
	changed := c.changed
	c.changed = nil
	return changed
}

// discard 删除缓存引用，不改变原始存储或正在使用的只读字节
// 入参: key 规范化部件键
// 返回: int64 从缓存移除的字节数
func (c *streamResourceCache) discard(key string) int64 {
	c.mu.Lock()
	defer c.mu.Unlock()
	entry := c.entries[key]
	if entry == nil {
		return 0
	}
	return c.removeLocked(entry)
}

// removeLocked 在持有缓存锁时移除资源及链表节点，不清零借用中的资源字节
// 入参: entry 已存在缓存节点
// 返回: int64 移除的缓存字节数
func (c *streamResourceCache) removeLocked(entry *list.Element) int64 {
	resource := entry.Value.(*streamCachedResource)
	bytes := int64(len(resource.data))
	delete(c.entries, resource.key)
	c.order.Remove(entry)
	c.bytes -= bytes
	return bytes
}

// forgetProcessed 在不再被任何未执行释放提示引用时移除已处理状态，避免大作业无界增长
// 入参: key 规范化部件键
func (c *streamResourceCache) forgetProcessed(key string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	delete(c.processed, key)
}

// clear 释放当前处理的所有缓存和状态引用，不接管原压缩存储
func (c *streamResourceCache) clear() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.entries, c.processed, c.changed = nil, nil, nil
	c.bytes = 0
	c.order.Init()
}

// updateDiscard 接入已闭合提示或完整控制部件，晚到提示对已经开始的哨兵页面恢复调度
// 入参: source 当前可用文档索引
// 返回: error 关联、提示、回调、预算或取消错误
func (p *streamPackage) updateDiscard(source *Reader) error {
	d := p.discard
	if d == nil || d.loaded {
		return nil
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	if !d.checked {
		if source == p.index && p.rootRelationshipsPending() {
			root := p.parts["/_rels/.rels"]
			if root == nil || root.relations == nil || root.relations.discards[formatNamespace(source.format)+"/discard-control"] == 0 {
				return nil
			}
		}
		relations, err := source.pkg.relationships("/")
		if err != nil {
			return err
		}
		target, err := discardControlTarget(relations, source.format)
		if err != nil {
			return err
		}
		d.target, d.checked = target, true
		if target == "" {
			d.loaded = true
			return nil
		}
	}
	key := strings.ToLower(d.target)
	if part := p.parts[key]; part != nil && part.control != nil && part.control.root != nil && !part.control.deferred {
		if part.control.root.Name.Space != formatNamespace(source.format)+"/discard-control" {
			return fmt.Errorf("%w: streamed discard format mismatch", ErrInvalid)
		}
		if err := p.appendDiscardHints(part.control.hints, false); err != nil {
			return err
		}
		d.loaded = part.xmlDone
		return nil
	}
	if _, present := source.pkg.parts[key]; !present {
		return nil
	}
	control, err := source.DiscardControl(p.context)
	if err != nil {
		return err
	}
	if err := p.appendDiscardHints(control.Hints, true); err != nil {
		return err
	}
	d.loaded = true
	return nil
}

// appendDiscardHints 追加新提示，只在最终重读时比较前缀，持续解析不重复扫描已有提示
// 入参: hints 已校验的完整或前缀提示, verify 是否校验已交付前缀
// 返回: error 前缀冲突、预算、回调或取消错误
func (p *streamPackage) appendDiscardHints(hints []DiscardHint, verify bool) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	d := p.discard
	if len(hints) < len(d.hints) {
		return fmt.Errorf("%w: streamed discard prefix length", ErrInvalid)
	}
	if verify {
		for index, hint := range d.hints {
			if hints[index] != hint {
				return fmt.Errorf("%w: streamed discard prefix conflict", ErrInvalid)
			}
		}
	}
	if d.byPage == nil {
		d.byPage, d.done, d.targetRefs = make(map[string][]int), make(map[int]bool), make(map[string]int)
	}
	for index := len(d.hints); index < len(hints); index++ {
		hint := hints[index]
		if err := checkContext(p.context); err != nil {
			return err
		}
		key := strings.ToLower(hint.SentinelPage)
		targetKey := strings.ToLower(hint.Target)
		d.hints = append(d.hints, hint)
		d.byPage[key] = append(d.byPage[key], index)
		d.targetRefs[targetKey]++
		if d.started[key] {
			if err := p.scheduleDiscard(index, true); err != nil {
				return err
			}
		}
	}
	return nil
}

// startDiscard 在当前消费者开始处理哨兵页面时调度提示，未知目标保留到首次处理或输入结束
// 入参: source 当前文档索引, index 页面序号
// 返回: error 提示、回调或取消错误
func (p *streamPackage) startDiscard(source *Reader, index int) error {
	if p.discard == nil {
		return nil
	}
	if err := p.updateDiscard(source); err != nil {
		return err
	}
	key := strings.ToLower(source.pages[index].Part)
	if p.discard.started[key] {
		return nil
	}
	p.discard.started[key] = true
	for _, hint := range p.discard.byPage[key] {
		if err := p.scheduleDiscard(hint, false); err != nil {
			return err
		}
	}
	return nil
}

// scheduleDiscard 对已处理目标执行提示，未处理目标按部件身份排队，纯前向消费模式对已完整到达且不待回调的目标直接触发释放
// 入参: index 提示序号, late 是否在哨兵页面开始后就绪
// 返回: error 回调或取消错误
func (p *streamPackage) scheduleDiscard(index int, late bool) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	if p.discard.done[index] {
		return nil
	}
	key := strings.ToLower(p.discard.hints[index].Target)
	if !p.cache.wasProcessed(key) {
		if !p.consumeOnly || !p.canReclaimPart(p.parts[key]) {
			p.discard.waiting[key] = append(p.discard.waiting[key], index)
			return nil
		}
	}
	return p.executeDiscard(index, late)
}

// executeDiscard 移除缓存并在纯前向消费模式下回收底层压缩存储，不使缓存中借出的只读字节失效
// 入参: index 提示序号, late 是否晚到
// 返回: error 回调或取消错误
func (p *streamPackage) executeDiscard(index int, late bool) error {
	if p.discard.done[index] {
		return nil
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	hint := p.discard.hints[index]
	key := strings.ToLower(hint.Target)
	bytes := p.cache.discard(key)
	if p.consumeOnly && p.ownedMemory != nil {
		if part := p.parts[key]; part != nil {
			if p.canReclaimPart(part) {
				bytes += p.reclaimPart(key)
			} else {
				part.reclaimPending = true
			}
		}
	}
	p.discard.done[index] = true
	if p.discard.targetRefs != nil {
		if refs := p.discard.targetRefs[key] - 1; refs <= 0 {
			delete(p.discard.targetRefs, key)
			if p.consumeOnly {
				p.cache.forgetProcessed(key)
			}
		} else {
			p.discard.targetRefs[key] = refs
		}
	}
	if p.options.OnDiscard != nil {
		if err := p.options.OnDiscard(p.context, StreamDiscard{Hint: hint, Bytes: bytes, Late: late}); err != nil {
			return err
		}
	}
	return checkContext(p.context)
}

// releaseProcessed 恢复刚完成处理的目标提示，每个目标只检查关联的等待项
// 返回: error 回调或取消错误
func (p *streamPackage) releaseProcessed() error {
	if p.cache == nil || p.discard == nil {
		return nil
	}
	for _, key := range p.cache.takeProcessed() {
		waiting := p.discard.waiting[key]
		delete(p.discard.waiting, key)
		for _, index := range waiting {
			if err := p.executeDiscard(index, true); err != nil {
				return err
			}
		}
	}
	return nil
}

// Read 消费当前载荷的已声明字节，达到边界后返回EOF
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 输入、存储或载荷结束
func (s *streamLimitedInput) Read(output []byte) (int, error) {
	if len(output) == 0 {
		return 0, nil
	}
	if s.left == 0 {
		return 0, io.EOF
	}
	if uint64(len(output)) > s.left {
		output = output[:int(s.left)]
	}
	n, err := s.input.Read(output)
	s.left -= uint64(n)
	return n, err
}

// ReadByte 为Deflate保持声明载荷边界和精确消费计数
// 返回: byte 输入字节, error 输入或载荷结束
func (s *streamLimitedInput) ReadByte() (byte, error) {
	var value [1]byte
	_, err := s.Read(value[:])
	return value[0], err
}

// readEntry 读取本地头及载荷，遇未知长度Store加数据描述符时流式识别合法描述符边界，仅无签名格式才返回延迟标记
// 入参: offset 已消费本地头标记的偏移, buffer 复用解压缓冲
// 返回: *streamEntry 已校验条目, bool 是否需要等待中央目录, error 本地头、解压、描述符或预算错误
func (p *streamPackage) readEntry(offset int64, buffer []byte) (*streamEntry, bool, error) {
	var fields [26]byte
	if _, err := io.ReadFull(p.input, fields[:]); err != nil {
		return nil, false, p.streamInputError("streamed local header", err)
	}
	header := zip.FileHeader{ReaderVersion: binary.LittleEndian.Uint16(fields[:]), Flags: binary.LittleEndian.Uint16(fields[2:]), Method: binary.LittleEndian.Uint16(fields[4:]), ModifiedTime: binary.LittleEndian.Uint16(fields[6:]), ModifiedDate: binary.LittleEndian.Uint16(fields[8:]), CRC32: binary.LittleEndian.Uint32(fields[10:]), CompressedSize: binary.LittleEndian.Uint32(fields[14:]), UncompressedSize: binary.LittleEndian.Uint32(fields[18:])}
	nameBytes, extraBytes := int(binary.LittleEndian.Uint16(fields[22:])), int(binary.LittleEndian.Uint16(fields[24:]))
	if err := validateZIPMetadata(nameBytes, extraBytes, 0); err != nil {
		return nil, false, err
	}
	variable := make([]byte, nameBytes+extraBytes)
	if _, err := io.ReadFull(p.input, variable); err != nil {
		return nil, false, p.streamInputError("streamed local variable fields", err)
	}
	header.Name, header.Extra = string(variable[:nameBytes]), variable[nameBytes:]
	if header.Flags&1 != 0 || header.Method != zip.Store && header.Method != zip.Deflate {
		return nil, false, fmt.Errorf("%w: streamed ZIP encryption or method", ErrUnsupported)
	}
	descriptor := header.Flags&8 != 0
	uncompressed, compressed, wide, err := packageZIPLocal64Values(header.Extra, uint64(header.UncompressedSize), uint64(header.CompressedSize), descriptor)
	if err != nil {
		return nil, false, err
	}
	header.Extra = nil
	if wide && header.ReaderVersion < 45 {
		return nil, false, fmt.Errorf("%w: streamed ZIP64 local extraction version", ErrInvalid)
	}
	if uncompressed > uint64(p.options.Limits.MaxPartBytes) || uncompressed > uint64(p.options.Limits.MaxPackageBytes)-p.bytes {
		return nil, false, fmt.Errorf("%w: streamed local declared bytes", ErrLimit)
	}
	if compressed > uint64(p.input.limit-p.input.count) {
		return nil, false, fmt.Errorf("%w: streamed local compressed bytes", ErrLimit)
	}
	if descriptor && header.Method == zip.Store && compressed == 0 {
		return p.readStoreDescriptorEntry(offset, header, uncompressed, wide, buffer)
	}
	entry := &streamEntry{header: header, offset: offset, data: p.input.count, localZIP64: wide}
	var source io.Reader = p.input
	var limited *streamLimitedInput
	if !descriptor || compressed != 0 {
		limited = &streamLimitedInput{input: p.input, left: compressed}
		source = limited
	}
	var decoder io.ReadCloser
	if header.Method == zip.Deflate {
		decoder = flate.NewReader(source)
		defer decoder.Close()
		source = decoder
	}
	checksum := crc32.NewIEEE()
	var count uint64
	for {
		if err := checkContext(p.context); err != nil {
			return nil, false, err
		}
		n, readErr := source.Read(buffer)
		if uint64(n) > uint64(p.options.Limits.MaxPartBytes)-count || uint64(n) > uint64(p.options.Limits.MaxPackageBytes)-p.bytes {
			return nil, false, fmt.Errorf("%w: streamed decoded bytes", ErrLimit)
		}
		count += uint64(n)
		p.bytes += uint64(n)
		_, _ = checksum.Write(buffer[:n])
		if readErr != nil {
			if readErr != io.EOF {
				return nil, false, p.streamInputError("streamed ZIP payload", readErr)
			}
			break
		}
		if n == 0 {
			return nil, false, io.ErrNoProgress
		}
	}
	if limited != nil && limited.left != 0 {
		return nil, false, fmt.Errorf("%w: trailing or truncated streamed payload", ErrInvalid)
	}
	actualCompressed := uint64(p.input.count - entry.data)
	actualCRC := checksum.Sum32()
	if descriptor {
		if header.CRC32 != 0 && header.CRC32 != actualCRC || compressed != 0 && compressed != actualCompressed || uncompressed != 0 && uncompressed != count {
			return nil, false, fmt.Errorf("%w: streamed local descriptor placeholders", ErrInvalid)
		}
		if err := p.readDescriptor(actualCRC, actualCompressed, count, wide, header.ReaderVersion); err != nil {
			return nil, false, err
		}
	} else if actualCRC != header.CRC32 || actualCompressed != compressed || count != uncompressed {
		return nil, false, fmt.Errorf("%w: streamed payload CRC or sizes", ErrInvalid)
	}
	entry.finish = p.input.count
	entry.header.CRC32, entry.header.CompressedSize64, entry.header.UncompressedSize64 = actualCRC, actualCompressed, count
	return entry, false, nil
}

// validStreamNextZIPSignature 检查紧随数据描述符之后的4字节是否为合法ZIP结构头签名
// 入参: sig 小端读取的4字节签名值
// 返回: bool 是否为合法后续ZIP签名
func validStreamNextZIPSignature(sig uint32) bool {
	return sig == packageZIPLocalSignature || sig == packageZIPCentralSignature || sig == packageZIPEndSignature || sig == packageZIP64EndSignature || sig == packageZIPDigitalSignature
}

// allowRandomAccess 判断当前流式消费状态是否仍保留全部物理字节以允许回退至随机访问解析
// 返回: bool 是否允许回退随机访问
func (p *streamPackage) allowRandomAccess() bool {
	return !p.consumeOnly || !p.reclaimed
}

// readStoreDescriptorEntry 流式读取Store加Data Descriptor条目，在滑动窗口中以CRC、双尺寸与后续ZIP签名联合确认边界
// 入参: offset 本地头起点偏移, header 本地头, uncompressed 本地头声明未压缩尺寸, wide 是否启用ZIP64扩展, buffer 复用缓冲
// 返回: *streamEntry 已校验条目, bool 未找到签名描述符需延迟至中央目录, error 预算、输入或取消错误
func (p *streamPackage) readStoreDescriptorEntry(offset int64, header zip.FileHeader, uncompressed uint64, wide bool, buffer []byte) (*streamEntry, bool, error) {
	dataStart := p.input.count
	startBytes := p.bytes
	widths := []int{4}
	if wide {
		widths = []int{8}
	} else if header.ReaderVersion >= 45 {
		widths = []int{8, 4}
	}
	checksum := crc32.NewIEEE()
	var count uint64
	var descBuf [24]byte
	sawBadSigned := false
	sawEOCD := false
	passedNextHeader := false
	consumePayload := func(size int) (bool, error) {
		for size > 0 {
			step := min(size, len(buffer))
			partRemain := uint64(p.options.Limits.MaxPartBytes) - count
			pkgRemain := uint64(p.options.Limits.MaxPackageBytes) - p.bytes
			if uint64(step) > partRemain || uint64(step) > pkgRemain {
				return true, nil
			}
			if _, err := io.ReadFull(p.input, buffer[:step]); err != nil {
				return false, p.streamInputError("streamed ZIP payload", err)
			}
			count += uint64(step)
			p.bytes += uint64(step)
			_, _ = checksum.Write(buffer[:step])
			size -= step
		}
		return false, nil
	}
	deferPartLimit := func() (*streamEntry, bool, error) {
		p.bytes = startBytes
		if !p.allowRandomAccess() {
			if sawBadSigned {
				return nil, false, fmt.Errorf("%w: streamed descriptor CRC or sizes", ErrInvalid)
			}
			return nil, false, fmt.Errorf("%w: streamed entry requires random access after memory reclamation", ErrUnsupported)
		}
		return nil, true, nil
	}
	finishEOF := func() (*streamEntry, bool, error) {
		p.bytes = startBytes
		if !p.allowRandomAccess() && (sawBadSigned || !sawEOCD) {
			return nil, false, fmt.Errorf("%w: streamed descriptor CRC or sizes", ErrInvalid)
		}
		return nil, true, nil
	}
	for {
		if err := checkContext(p.context); err != nil {
			return nil, false, err
		}
		avail := p.input.reader.Buffered()
		if avail == 0 {
			if _, peekErr := p.input.reader.Peek(1); peekErr != nil {
				if peekErr == io.EOF {
					return finishEOF()
				}
				return nil, false, p.streamInputError("streamed ZIP payload", peekErr)
			}
			avail = p.input.reader.Buffered()
		}
		if avail > len(buffer) {
			avail = len(buffer)
		}
		peeked, peekErr := p.input.reader.Peek(avail)
		if peekErr != nil && peekErr != io.EOF {
			return nil, false, p.streamInputError("streamed ZIP payload", peekErr)
		}
		if len(peeked) == 0 {
			return finishEOF()
		}
		idx := bytes.IndexByte(peeked, 0x50)
		if idx < 0 {
			exceeded, err := consumePayload(len(peeked))
			if err != nil {
				return nil, false, err
			}
			if exceeded {
				return deferPartLimit()
			}
			continue
		}
		if idx > 0 {
			exceeded, err := consumePayload(idx)
			if err != nil {
				return nil, false, err
			}
			if exceeded {
				return deferPartLimit()
			}
		}
		sig4, sigErr := p.input.reader.Peek(4)
		if sigErr != nil && sigErr != io.EOF {
			return nil, false, p.streamInputError("streamed ZIP payload", sigErr)
		}
		if len(sig4) < 4 {
			exceeded, err := consumePayload(1)
			if err != nil {
				return nil, false, err
			}
			if exceeded {
				return deferPartLimit()
			}
			continue
		}
		sigVal := binary.LittleEndian.Uint32(sig4)
		if sigVal == packageZIPEndSignature {
			sawEOCD = true
		}
		if validStreamNextZIPSignature(sigVal) {
			passedNextHeader = true
		}
		if sigVal != packageZIPDescriptorSignature {
			exceeded, err := consumePayload(1)
			if err != nil {
				return nil, false, err
			}
			if exceeded {
				return deferPartLimit()
			}
			continue
		}
		tryWidths := widths
		if !wide && count >= 0xffffffff {
			tryWidths = []int{8}
		}
		actualCRC := checksum.Sum32()
		for _, width := range tryWidths {
			descLen := 8 + 2*width
			cand, candErr := p.input.reader.Peek(descLen + 4)
			if candErr != nil && candErr != io.EOF {
				return nil, false, p.streamInputError("streamed descriptor input", candErr)
			}
			if len(cand) < descLen+4 {
				continue
			}
			nextSig := binary.LittleEndian.Uint32(cand[descLen : descLen+4])
			if !validStreamNextZIPSignature(nextSig) {
				continue
			}
			descCRC := binary.LittleEndian.Uint32(cand[4:8])
			var descComp, descUncomp uint64
			if width == 4 {
				descComp = uint64(binary.LittleEndian.Uint32(cand[8:12]))
				descUncomp = uint64(binary.LittleEndian.Uint32(cand[12:16]))
			} else {
				descComp = binary.LittleEndian.Uint64(cand[8:16])
				descUncomp = binary.LittleEndian.Uint64(cand[16:24])
			}
			if descCRC != actualCRC || descComp != count || descUncomp != count || header.CRC32 != 0 && header.CRC32 != descCRC || uncompressed != 0 && uncompressed != count {
				if !passedNextHeader && (descComp == count && descUncomp == count || descCRC == actualCRC) {
					sawBadSigned = true
				}
				continue
			}
			if _, err := io.ReadFull(p.input, descBuf[:descLen]); err != nil {
				return nil, false, p.streamInputError("streamed descriptor fields", err)
			}
			entry := &streamEntry{header: header, offset: offset, data: dataStart, finish: p.input.count, localZIP64: wide}
			entry.header.CRC32, entry.header.CompressedSize64, entry.header.UncompressedSize64 = actualCRC, count, count
			return entry, false, nil
		}
		exceeded, err := consumePayload(1)
		if err != nil {
			return nil, false, err
		}
		if exceeded {
			return deferPartLimit()
		}
	}
}

// readDescriptor 根据已经解码的CRC、尺寸及ZIP64状态识别允许的描述符形式，标记碰撞不依赖猜测
// 入参: checksum 实际CRC, compressed, uncompressed 实际字节数, wide 本地ZIP64标识, version 本地提取版本
// 返回: error 描述符、输入、预算或取消错误
func (p *streamPackage) readDescriptor(checksum uint32, compressed, uncompressed uint64, wide bool, version uint16) error {
	widths := []int{4}
	if wide || compressed >= 0xffffffff || uncompressed >= 0xffffffff {
		widths = []int{8}
	} else if version >= 45 {
		widths = []int{8, 4}
	}
	var first [4]byte
	if _, err := io.ReadFull(p.input, first[:]); err != nil {
		return p.streamInputError("streamed descriptor CRC", err)
	}
	value := binary.LittleEndian.Uint32(first[:])
	var inputErr error
	for _, width := range widths {
		for _, signed := range []bool{false, true} {
			length := 2 * width
			if signed {
				if value != packageZIPDescriptorSignature {
					continue
				}
				length += 4
			} else if value != checksum {
				continue
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
			peeked, err := p.input.reader.Peek(length)
			if err != nil {
				if err == io.EOF && int64(len(peeked)) > p.input.limit-p.input.count {
					inputErr = fmt.Errorf("%w: stream input bytes", ErrLimit)
				} else {
					inputErr = err
				}
				continue
			}
			fields := peeked
			if signed {
				if binary.LittleEndian.Uint32(fields) != checksum {
					continue
				}
				fields = fields[4:]
			}
			left, right := uint64(0), uint64(0)
			if width == 4 {
				left, right = uint64(binary.LittleEndian.Uint32(fields)), uint64(binary.LittleEndian.Uint32(fields[4:]))
			} else {
				left, right = binary.LittleEndian.Uint64(fields), binary.LittleEndian.Uint64(fields[8:])
			}
			if left != compressed || right != uncompressed {
				continue
			}
			if len(widths) > 1 && width == 8 {
				if next, nextErr := p.input.reader.Peek(length + 4); nextErr == nil {
					sig := binary.LittleEndian.Uint32(next[length : length+4])
					if sig != packageZIPLocalSignature && sig != packageZIPCentralSignature && sig != packageZIPEndSignature && sig != packageZIP64EndSignature && sig != packageZIPDigitalSignature {
						continue
					}
				}
			}
			var consumed [20]byte
			if _, err := io.ReadFull(p.input, consumed[:length]); err != nil {
				return p.streamInputError("streamed descriptor fields", err)
			}
			return nil
		}
	}
	if inputErr != nil {
		return p.streamInputError("streamed descriptor input", inputErr)
	}
	return fmt.Errorf("%w: streamed descriptor CRC or sizes", ErrInvalid)
}

// Read 消费输入并保存实际字节，取消及输入预算在调用底层读取前检查
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 输入、存储、预算或取消错误
func (s *streamInput) Read(output []byte) (int, error) {
	if err := checkContext(s.context); err != nil {
		return 0, err
	}
	if len(output) == 0 {
		return 0, nil
	}
	if s.count == s.limit {
		var extra [1]byte
		n, err := s.reader.Read(extra[:])
		if n != 0 {
			return 0, fmt.Errorf("%w: stream input bytes", ErrLimit)
		}
		if err == nil {
			return 0, io.ErrNoProgress
		}
		return 0, err
	}
	if int64(len(output)) > s.limit-s.count {
		output = output[:int(s.limit-s.count)]
	}
	n, err := s.reader.Read(output)
	if n != 0 {
		if storeErr := s.store(output[:n]); storeErr != nil {
			return n, storeErr
		}
	}
	if n == 0 && err == nil {
		return 0, io.ErrNoProgress
	}
	return n, err
}

// ReadByte 精确消费一个压缩字节，批量存储避免文件存储逐字节写入
// 返回: byte 输入字节, error 输入、存储、预算或取消错误
func (s *streamInput) ReadByte() (byte, error) {
	var value [1]byte
	n, err := s.Read(value[:])
	if n == 1 && err == io.EOF {
		return value[0], nil
	}
	return value[0], err
}

// store 将已经消费的输入追加到复用缓冲，满块后提交存储
// 入参: data 实际输入字节
// 返回: error 存储或取消错误
func (s *streamInput) store(data []byte) error {
	for len(data) != 0 {
		count := min(len(data), cap(s.pending)-len(s.pending))
		s.pending = append(s.pending, data[:count]...)
		s.count += int64(count)
		data = data[count:]
		if len(s.pending) == cap(s.pending) {
			if err := s.flush(); err != nil {
				return err
			}
		}
	}
	return nil
}

// flushAvailable 按可回收内存存储当前剩余可用配额增量刷出待写缓冲前缀，不触发递归回收或ErrLimit
// 返回: int64 本次实际刷入存储的字节数, error 存储或取消错误
func (s *streamInput) flushAvailable() (int64, error) {
	if err := checkContext(s.context); err != nil {
		return 0, err
	}
	if len(s.pending) == 0 || s.ownedMemory == nil {
		return 0, nil
	}
	var total int64
	for len(s.pending) > 0 {
		avail := s.ownedMemory.availableBytes()
		if avail <= 0 {
			break
		}
		chunk := int(min(int64(len(s.pending)), avail))
		n, err := s.storage.WriteAt(s.pending[:chunk], s.count-int64(len(s.pending)))
		if n < 0 || n > chunk {
			return total, fmt.Errorf("%w: stream storage write count", ErrInvalid)
		}
		if err != nil {
			return total, err
		}
		if n != chunk {
			return total, io.ErrShortWrite
		}
		remaining := len(s.pending) - n
		copy(s.pending, s.pending[n:])
		s.pending = s.pending[:remaining]
		total += int64(n)
	}
	return total, nil
}

// flush 将当前缓冲完整写入随机存储，在可回收内存模式下遇配额不足先推进待回收前缀再续写
// 返回: error 存储、计数或取消错误
func (s *streamInput) flush() error {
	if err := checkContext(s.context); err != nil {
		return err
	}
	if len(s.pending) == 0 {
		return nil
	}
	if s.ownedMemory == nil {
		n, err := s.storage.WriteAt(s.pending, s.count-int64(len(s.pending)))
		if n < 0 || n > len(s.pending) {
			return fmt.Errorf("%w: stream storage write count", ErrInvalid)
		}
		if err != nil {
			return err
		}
		if n != len(s.pending) {
			return io.ErrShortWrite
		}
		s.pending = s.pending[:0]
		return nil
	}
	for len(s.pending) > 0 {
		wrote, err := s.flushAvailable()
		if err != nil {
			return err
		}
		if len(s.pending) == 0 {
			return nil
		}
		var freed int64
		if s.onLimit != nil {
			freed = s.onLimit()
		}
		if wrote == 0 && freed == 0 {
			return fmt.Errorf("%w: stream memory bytes", ErrLimit)
		}
	}
	return nil
}

// selectedDiscard 只对已确认包根关联的控制部件启用自动语义，不解释未关联附加部件
// 入参: name 部件名, media 声明媒体类型
// 返回: bool 是否为当前消费者的控制部件
func (p *streamPackage) selectedDiscard(name, media string) bool {
	return p.options.OnPage != nil && p.discard != nil && p.discard.checked && p.index != nil && strings.EqualFold(p.discard.target, name) && matchStandardContentType(p.index.format, media, fixedContentType("discard-control"))
}

// cloneEventNamespaces 仅在存在用户XML回调可能就地修改词元时复制命名空间映射
// 入参: namespaces 词元携带的命名空间映射
// 返回: map[string]string 可安全保存的命名空间映射
func (p *streamPackage) cloneEventNamespaces(namespaces map[string]string) map[string]string {
	if p.options.OnXML != nil {
		return maps.Clone(namespaces)
	}
	return namespaces
}

// consumeMetadata 将已校验词元按部件类别分发至页面标记、关系、布局索引或释放提示增量处理，调用方回调尚未执行时复制所需数据
// 入参: part 当前逻辑部件, media 声明媒体类型, event 独立XML词元
// 返回: error 增量元数据、结构、调度、回调或取消错误
func (p *streamPackage) consumeMetadata(part *streamPart, media string, event StreamXMLToken) error {
	if p.selectedPage(part.name, media) {
		return p.consumePageMarkup(part, event)
	}
	if p.selectedRelationships(part.name, media) {
		return p.consumeRelationships(part, event)
	}
	if p.selectedLayout(part.name, media) {
		return p.consumeLayout(part, event)
	}
	if !p.selectedDiscard(part.name, media) {
		return nil
	}
	if part.control == nil {
		part.control = &streamPartialDiscard{}
	}
	s := part.control
	if s.deferred {
		return nil
	}
	switch token := event.Token.(type) {
	case xml.StartElement:
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: p.cloneEventNamespaces(event.Namespaces)}
		if len(s.stack) == 0 {
			if s.root != nil {
				return fmt.Errorf("%w: multiple streamed discard roots", ErrInvalid)
			}
			s.root = node
			namespace := formatNamespace(p.index.format) + "/discard-control"
			if p.index.format == FormatOpenXPS && node.Name != (xml.Name{Space: namespace, Local: "DiscardControl"}) {
				s.deferred = true
				return nil
			}
			if _, err := processDiscardControl(node, part.name, p.index.format, p.context); err != nil {
				return err
			}
		} else if len(s.stack) > 1 {
			parent := s.stack[len(s.stack)-1]
			parent.Children = append(parent.Children, node)
		}
		s.stack = append(s.stack, node)
	case xml.CharData:
		if len(s.stack) == 0 {
			return nil
		}
		node := s.stack[len(s.stack)-1]
		if len(s.stack) == 1 {
			if !xmlWhitespace(string(token)) {
				return fmt.Errorf("%w: streamed discard root text", ErrInvalid)
			}
			return nil
		}
		node.text = append(node.text, token...)
	case xml.EndElement:
		if len(s.stack) == 0 {
			return fmt.Errorf("%w: streamed discard end", ErrInvalid)
		}
		node := s.stack[len(s.stack)-1]
		node.Text, node.text = string(node.text), nil
		s.stack[len(s.stack)-1] = nil
		s.stack = s.stack[:len(s.stack)-1]
		if len(s.stack) == 1 {
			fragment := &xmlElement{Name: s.root.Name, Attr: s.root.Attr, Namespaces: s.root.Namespaces, Children: []*xmlElement{node}}
			control, err := processDiscardControl(fragment, part.name, p.index.format, p.context)
			if err != nil {
				return err
			}
			s.hints = append(s.hints, control.Hints...)
			if err := p.updateDiscard(p.index); err != nil {
				return err
			}
			return p.releaseProcessed()
		}
	}
	return nil
}

// partReader 为完整逻辑部件创建独立游标，不一次打开全部分片解压器
// 入参: part 完整部件
// 返回: *streamLogicalReader 仅供当前消费阶段使用的游标
func (p *streamPackage) partReader(part *streamPart) *streamLogicalReader {
	entries := make([]*streamEntry, part.last+1)
	for index := range entries {
		entries[index] = part.entries[index]
	}
	return &streamLogicalReader{storage: p.input.storage, entries: entries, context: p.context}
}

// Read 顺序读取已到达的部件分片，不暴露可写存储或缓冲
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 解压、输入、关闭、取消或结束信息
func (s *streamLogicalReader) Read(output []byte) (int, error) {
	if s.closed {
		return 0, ErrClosed
	}
	if err := checkContext(s.context); err != nil {
		return 0, err
	}
	if len(output) == 0 {
		return 0, nil
	}
	for {
		if s.current == nil {
			if s.index == len(s.entries) {
				return 0, io.EOF
			}
			entry := s.entries[s.index]
			raw := io.NewSectionReader(s.storage, entry.data, int64(entry.header.CompressedSize64))
			if entry.header.Method == zip.Store {
				s.current = io.NopCloser(raw)
			} else {
				s.current = flate.NewReader(raw)
			}
		}
		n, err := s.current.Read(output)
		if err == io.EOF {
			closeErr := s.current.Close()
			s.current = nil
			s.index++
			if closeErr != nil {
				return n, closeErr
			}
			if n != 0 {
				return n, nil
			}
			continue
		}
		return n, err
	}
}

// Close 释放解压器及存储引用，回调返回后保留的读取器不可再使用
// 返回: error 解压器关闭错误
func (s *streamLogicalReader) Close() error {
	if s.closed {
		return nil
	}
	s.closed, s.storage, s.entries, s.context = true, nil, nil, nil
	if s.current != nil {
		err := s.current.Close()
		s.current = nil
		return err
	}
	return nil
}

// emit 在内容类型可确定时发出完整临时部件，回调只借用当前读取器
// 入参: part 当前逻辑部件
// 返回: error 内容类型、回调或取消错误
func (p *streamPackage) emit(part *streamPart) error {
	if part.emitted || part.reclaimed || p.types == nil {
		return nil
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	key := strings.ToLower(part.name)
	media := p.types.declaredContentType(part.name)
	p.preparePagePackage()
	if err := p.advanceXML(part, media); err != nil {
		return err
	}
	if part.last < 0 || len(part.entries) != part.last+1 {
		return p.emitPages(part.name)
	}
	if media == "" {
		return nil
	}
	if opcRelationshipName(part.name) && !strings.EqualFold(media, opcRelsType) {
		return fmt.Errorf("%w: streamed relationship content type", ErrInvalid)
	}
	p.registerPagePart(part)
	if p.options.OnPart == nil {
		part.emitted = true
		if part.reclaimPending && p.canReclaimPart(part) {
			p.reclaimPart(key)
		}
		if err := p.emitPages(part.name); err != nil {
			return err
		}
		return p.tryReclaimWithoutPage(part, key, media)
	}
	reader := p.partReader(part)
	err := p.options.OnPart(p.context, PartInfo{Name: part.name, ContentType: media, Size: int64(part.bytes)}, reader)
	closeErr := reader.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	part.emitted = true
	if p.cache != nil {
		p.cache.mark(key)
	}
	if part.reclaimPending && p.canReclaimPart(part) {
		p.reclaimPart(key)
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	if err := p.emitPages(part.name); err != nil {
		return err
	}
	return p.tryReclaimWithoutPage(part, key, media)
}

// tryReclaimWithoutPage 在纯前向无页面回调模式下立即回收不再被索引或元数据回调依赖的部件存储
// 入参: part 已完成接收的逻辑部件, key 小写规范部件键, media 声明媒体类型
// 返回: error 固定页面头校验或取消错误
func (p *streamPackage) tryReclaimWithoutPage(part *streamPart, key, media string) error {
	if !p.consumeOnly || p.ownedMemory == nil || p.options.OnPage != nil || part == nil || part.reclaimed {
		return nil
	}
	if !p.canReclaimPart(part) {
		return nil
	}
	if opcRelationshipName(part.name) {
		if part.relsVerified && part.relsRecorded && !strings.EqualFold(part.name, "/_rels/.rels") {
			p.reclaimPart(key)
		}
		return nil
	}
	base := opcMediaTypeBase(media)
	if strings.EqualFold(base, fixedContentType("fixeddocumentsequence")) {
		if p.index != nil && p.sequenceRead && strings.EqualFold(part.name, p.index.sequence) {
			p.reclaimPart(key)
		}
		return nil
	}
	if strings.EqualFold(base, fixedContentType("fixeddocument")) {
		if p.index != nil && p.sequenceRead {
			if idx := p.documentIndexByPart(part.name); idx < 0 || idx < p.document {
				p.reclaimPart(key)
			}
		}
		return nil
	}
	if strings.EqualFold(base, fixedContentType("discard-control")) {
		return nil
	}
	if p.options.OnCoreProperties != nil && !p.corePropsDelivered && strings.EqualFold(media, opcCoreType) {
		return nil
	}
	if p.options.OnDocumentStructure != nil && strings.EqualFold(base, fixedContentType("documentstructure")) {
		return nil
	}
	if p.options.OnJobPrintTicket != nil && !p.jobTicketDelivered && (p.jobTicketTarget == "" && (p.index == nil || streamPotentialPrintTicketMedia(p.index.format, media)) || strings.EqualFold(part.name, p.jobTicketTarget)) {
		return nil
	}
	if strings.EqualFold(base, fixedContentType("fixedpage")) {
		if p.index == nil || !p.pageNames[key] {
			return nil
		}
		if _, err := p.index.readPageHeaderStream(p.context, part.name); err != nil {
			return err
		}
	}
	p.reclaimPart(key)
	return nil
}

// reconcile 对照中央目录核对全部物理覆盖，未索引本地条目、载荷空洞及早期结果冲突均使整次读取失败
// 入参: r 最终随机索引
// 返回: error 物理覆盖、载荷、预算或取消错误
func (p *streamPackage) reconcile(r *Reader) error {
	known := make(map[int64]*streamEntry)
	for _, entry := range p.entries {
		known[entry.offset] = entry
	}
	if !p.deferred && len(p.entries) != len(r.pkg.files) {
		return fmt.Errorf("%w: streamed local/central entry count", ErrInvalid)
	}
	position := r.pkg.zipLayout.base
	buffer := make([]byte, streamBufferBytes)
	for _, record := range r.pkg.zipRecords {
		if err := checkContext(p.context); err != nil {
			return err
		}
		if record.start != position {
			return fmt.Errorf("%w: unindexed or missing streamed physical bytes", ErrInvalid)
		}
		position = record.finish
		if entry := known[record.start]; entry != nil {
			header := entry.header
			if header.Name != record.file.Name || entry.data != record.data || header.CRC32 != record.file.CRC32 || header.CompressedSize64 != record.file.CompressedSize64 || header.UncompressedSize64 != record.file.UncompressedSize64 {
				return fmt.Errorf("%w: streamed provisional/central fields", ErrInvalid)
			}
			delete(known, record.start)
		} else if err := validateStreamPayload(record, p.input.storage, buffer, p.context); err != nil {
			return err
		}
	}
	if position != r.pkg.zipLayout.central || len(known) != 0 {
		return fmt.Errorf("%w: streamed central coverage", ErrInvalid)
	}
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		if err := checkContext(p.context); err != nil {
			return err
		}
		if _, exists := r.pkg.parts[key]; exists {
			continue
		}
		part := p.parts[key]
		if p.options.OnPart != nil && part.emitted || part.xmlTokens != 0 || part.xmlDone || part.page != nil || part.layout != nil || part.relations != nil || part.control != nil {
			return fmt.Errorf("%w: streamed provisional part %q conflicts with central directory", ErrInvalid, part.name)
		}
		if part.xml != nil {
			part.xml.Close()
			part.xml = nil
			p.xmlActive--
		}
		delete(p.parts, key)
		if p.pagePkg != nil {
			delete(p.pagePkg.parts, key)
			delete(p.pagePkg.names, key)
		}
	}
	return nil
}

// validateStreamPayload 校验延迟处理的压缩范围、实际尺寸及CRC，拒绝Deflate结束后的尾随载荷
// 入参: record 已确认物理范围, storage 原压缩存储, buffer 复用解压缓冲, ctx 取消Context
// 返回: error 解压、尾随载荷、尺寸、CRC、存储或取消错误
func validateStreamPayload(record packageZIPLocal, storage StreamStorage, buffer []byte, ctx context.Context) error {
	raw := bufio.NewReaderSize(io.NewSectionReader(storage, record.data, record.end-record.data), streamBufferBytes)
	var source io.Reader = raw
	if record.file.Method == zip.Deflate {
		decoder := flate.NewReader(raw)
		defer decoder.Close()
		source = decoder
	}
	checksum := crc32.NewIEEE()
	var count uint64
	for {
		if err := checkContext(ctx); err != nil {
			return err
		}
		n, err := source.Read(buffer)
		if uint64(n) > record.file.UncompressedSize64-count {
			return fmt.Errorf("%w: streamed deferred payload size", ErrInvalid)
		}
		count += uint64(n)
		_, _ = checksum.Write(buffer[:n])
		if err != nil {
			if err != io.EOF {
				return fmt.Errorf("%w: streamed deferred payload: %w", ErrInvalid, err)
			}
			break
		}
		if n == 0 {
			return io.ErrNoProgress
		}
	}
	if count != record.file.UncompressedSize64 || checksum.Sum32() != record.file.CRC32 {
		return fmt.Errorf("%w: streamed deferred payload CRC or size", ErrInvalid)
	}
	if _, err := raw.ReadByte(); err != io.EOF {
		if err != nil {
			return fmt.Errorf("%w: streamed deferred payload boundary: %w", ErrInvalid, err)
		}
		return fmt.Errorf("%w: streamed deferred compressed tail", ErrInvalid)
	}
	return checkContext(ctx)
}

// emitRemaining 在目录核对完成后回调尚未发出的部件，不重复早期已回调的身份
// 入参: r 已核对读取器
// 返回: error 部件、回调或取消错误
func (p *streamPackage) emitRemaining(r *Reader) error {
	if p.options.OnPart == nil {
		return nil
	}
	parts, err := r.Parts()
	if err != nil {
		return err
	}
	slices.SortFunc(parts, func(a, b PartInfo) int { return strings.Compare(a.Name, b.Name) })
	for _, part := range parts {
		if known := p.parts[strings.ToLower(part.Name)]; known != nil && known.emitted {
			continue
		}
		reader, err := r.OpenPart(p.context, part.Name, nil)
		if err != nil {
			return err
		}
		err = p.options.OnPart(p.context, part, reader)
		closeErr := reader.Close()
		if err != nil {
			return err
		}
		if closeErr != nil {
			return closeErr
		}
		if p.cache != nil {
			p.cache.mark(strings.ToLower(part.Name))
		}
		if err := checkContext(p.context); err != nil {
			return err
		}
	}
	return nil
}

// WriteAt 顺序追加到已占用范围之后，不接受会改写早期临时部件的随机覆盖
// 入参: data 输入字节, offset 顺序写入偏移
// 返回: int 已存字节数, error 顺序、容量或关闭错误
func (s *streamMemory) WriteAt(data []byte, offset int64) (int, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return 0, ErrClosed
	}
	if offset != s.size || offset < 0 {
		return 0, fmt.Errorf("%w: stream storage append offset", ErrInvalid)
	}
	if s.reclaim {
		if int64(len(data)) > s.limit-s.live {
			return 0, fmt.Errorf("%w: stream memory bytes", ErrLimit)
		}
		if s.chunkSize <= 0 {
			s.chunkSize = min(int64(streamBufferBytes), max(s.limit/32, min(s.limit, 4096)), max(s.limit, 1))
		}
		if s.liveChunks == nil {
			s.liveChunks = make(map[int][]byte)
			s.liveFreed = make(map[int]int)
		}
		count := 0
		for len(data) != 0 {
			rawIndex := int(s.size / s.chunkSize)
			position := int(s.size % s.chunkSize)
			chunk := s.liveChunks[rawIndex]
			if chunk == nil {
				chunk = make([]byte, int(s.chunkSize))
				s.liveChunks[rawIndex] = chunk
			}
			n := copy(chunk[position:], data)
			s.size += int64(n)
			s.live += int64(n)
			count += n
			data = data[n:]
		}
		return count, nil
	}
	if int64(len(data)) > s.limit-s.size {
		return 0, fmt.Errorf("%w: stream memory bytes", ErrLimit)
	}
	count := 0
	for len(data) != 0 {
		index := int(s.size / streamBufferBytes)
		position := int(s.size % streamBufferBytes)
		if index == len(s.chunks) {
			capacity := int(min(int64(streamBufferBytes), s.limit-int64(index)*streamBufferBytes))
			s.chunks = append(s.chunks, make([]byte, capacity))
		}
		n := copy(s.chunks[index][position:], data)
		s.size += int64(n)
		count += n
		data = data[n:]
	}
	return count, nil
}

// ReadAt 从已经到达的压缩字节读取，不暴露内部块或将未写区域当作零字节
// 入参: output 读取缓冲, offset 读取偏移
// 返回: int 已读字节数, error 越界、结束、已回收或关闭错误
func (s *streamMemory) ReadAt(output []byte, offset int64) (int, error) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	if s.closed {
		return 0, ErrClosed
	}
	if offset < 0 {
		return 0, fmt.Errorf("%w: negative stream storage offset", ErrInvalid)
	}
	if len(output) == 0 {
		return 0, nil
	}
	if offset >= s.size {
		return 0, io.EOF
	}
	blockSize := s.chunkSize
	if blockSize <= 0 {
		blockSize = streamBufferBytes
	}
	count := 0
	for len(output) != 0 && offset < s.size {
		rawIndex, position := int(offset/blockSize), int(offset%blockSize)
		var chunk []byte
		if s.reclaim {
			chunk = s.liveChunks[rawIndex]
		} else if rawIndex >= 0 && rawIndex < len(s.chunks) {
			chunk = s.chunks[rawIndex]
		}
		if chunk == nil {
			return count, fmt.Errorf("%w: streamed memory chunk reclaimed", ErrNotFound)
		}
		available := min(int64(len(chunk)-position), s.size-offset)
		n := copy(output, chunk[position:position+int(available)])
		offset += int64(n)
		count += n
		output = output[n:]
	}
	if len(output) != 0 {
		return count, io.EOF
	}
	return count, nil
}

// availableBytes 返回可回收内存存储当前剩余可用驻留字节配额
// 返回: int64 剩余可用字节配额
func (s *streamMemory) availableBytes() int64 {
	s.mu.RLock()
	defer s.mu.RUnlock()
	if s.closed {
		return 0
	}
	if s.reclaim {
		return max(s.limit-s.live, 0)
	}
	return max(s.limit-s.size, 0)
}

// writtenSize 返回当前已落入内存存储的逻辑总字节数
// 返回: int64 已写入字节数
func (s *streamMemory) writtenSize() int64 {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.size
}

// releaseRange 标记已消费区间并释放全部字节均已释放且写满的底层块，实时归还驻留配额并报告是否真实发生释放
// 入参: start 起始逻辑偏移, end 结束逻辑偏移（半开区间）
// 返回: int64 本次实际归还的块字节数, bool 是否真实释放至少一个底层块
func (s *streamMemory) releaseRange(start, end int64) (int64, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.reclaim || s.closed || s.chunkSize <= 0 || s.liveChunks == nil {
		return 0, false
	}
	if start < 0 {
		start = 0
	}
	if end > s.size {
		end = s.size
	}
	if end <= start {
		return 0, false
	}
	var reclaimed int64
	blockSize := s.chunkSize
	for pos := start; pos < end; {
		rawIndex := int(pos / blockSize)
		chunkEnd := int64(rawIndex+1) * blockSize
		segEnd := min(end, chunkEnd)
		if chunk := s.liveChunks[rawIndex]; chunk != nil {
			freed := s.liveFreed[rawIndex] + int(segEnd-pos)
			if s.size >= chunkEnd && freed >= len(chunk) {
				freedBytes := int64(len(chunk))
				delete(s.liveChunks, rawIndex)
				delete(s.liveFreed, rawIndex)
				s.live -= freedBytes
				if s.live < 0 {
					s.live = 0
				}
				reclaimed += freedBytes
			} else {
				s.liveFreed[rawIndex] = freed
			}
		}
		pos = segEnd
	}
	return reclaimed, reclaimed > 0
}

// Close 释放全部压缩块，重复关闭无副作用
// 返回: error nil
func (s *streamMemory) Close() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.closed, s.chunks, s.liveChunks, s.liveFreed, s.size, s.live = true, nil, nil, nil, 0, 0
	return nil
}

// reclaimRangeProgress 优先释放已落盘前缀再按需增量刷盘释放尾段，不提前吞错也不重复释放同一区间
// 入参: start 起始逻辑偏移, end 结束逻辑偏移, allowFlush 是否允许增量刷出待提交输入缓冲
// 返回: int64 本次实际归还的块字节数, int64 推进后的下一未释放偏移, bool 是否已覆盖整个区间
func (p *streamPackage) reclaimRangeProgress(start, end int64, allowFlush bool) (int64, int64, bool) {
	if p.ownedMemory == nil || end <= start {
		return 0, end, true
	}
	var total int64
	pos := start
	for pos < end {
		written := p.ownedMemory.writtenSize()
		if pos < written {
			prefixEnd := min(end, written)
			reclaimed, released := p.ownedMemory.releaseRange(pos, prefixEnd)
			if released {
				p.reclaimed = true
			}
			total += reclaimed
			pos = prefixEnd
			if pos >= end {
				return total, pos, true
			}
		}
		if !allowFlush {
			return total, pos, false
		}
		wrote, err := p.input.flushAvailable()
		if err != nil || wrote == 0 {
			return total, pos, false
		}
	}
	return total, pos, true
}

// reclaimEntryEnvelopeMode 按指定刷盘模式释放物理条目的本地头与数据描述符范围，全部释放后才置headerFreed
// 入参: entry 已校验物理条目, allowFlush 是否允许增量刷盘
// 返回: int64 本次释放的块字节数, bool 条目外层范围是否已全部释放
func (p *streamPackage) reclaimEntryEnvelopeMode(entry *streamEntry, allowFlush bool) (int64, bool) {
	if p.ownedMemory == nil || entry == nil {
		return 0, true
	}
	if entry.headerFreed {
		return 0, true
	}
	var total int64
	headStart := entry.offset + entry.headerFreedBytes
	headFreed, headPos, headDone := p.reclaimRangeProgress(headStart, entry.data, allowFlush)
	total += headFreed
	entry.headerFreedBytes = headPos - entry.offset
	payloadEnd := entry.data + int64(entry.header.CompressedSize64)
	tailDone := true
	if entry.finish > payloadEnd {
		tailStart := payloadEnd + entry.trailerFreedBytes
		tailFreed, tailPos, ok := p.reclaimRangeProgress(tailStart, entry.finish, allowFlush)
		total += tailFreed
		entry.trailerFreedBytes = tailPos - payloadEnd
		tailDone = ok
	}
	if headDone && tailDone {
		entry.headerFreed = true
		return total, true
	}
	return total, false
}

// reclaimEntryEnvelope 释放物理条目的本地头与数据描述符字节范围，未完全落盘时登记延迟重试队列
// 入参: entry 已校验物理条目
func (p *streamPackage) reclaimEntryEnvelope(entry *streamEntry) {
	if p.ownedMemory == nil || entry == nil || entry.headerFreed {
		return
	}
	if _, done := p.reclaimEntryEnvelopeMode(entry, true); !done {
		if !slices.Contains(p.pendingEnvelopes, entry) {
			p.pendingEnvelopes = append(p.pendingEnvelopes, entry)
		}
	}
}

// reclaimEntryPayloadMode 按指定刷盘模式释放物理条目的压缩载荷范围，全部释放后才置payloadFreed
// 入参: entry 已校验物理条目, allowFlush 是否允许增量刷盘
// 返回: int64 本次释放的块字节数, bool 载荷范围是否已全部释放
func (p *streamPackage) reclaimEntryPayloadMode(entry *streamEntry, allowFlush bool) (int64, bool) {
	if p.ownedMemory == nil || entry == nil {
		return 0, true
	}
	if entry.payloadFreed {
		return 0, true
	}
	payloadEnd := entry.data + int64(entry.header.CompressedSize64)
	start := entry.data + entry.payloadFreedBytes
	freed, nextPos, done := p.reclaimRangeProgress(start, payloadEnd, allowFlush)
	entry.payloadFreedBytes = nextPos - entry.data
	if done {
		entry.payloadFreed = true
	}
	return freed, done
}

// reclaimPendingStorage 推进全部延迟未完全释放条目与部件的已落盘前缀回收，供flush在撞限时打破死锁
// 返回: int64 本次实际释放的块字节数
func (p *streamPackage) reclaimPendingStorage() int64 {
	return p.reclaimPendingStorageMode(false)
}

// reclaimPendingStorageMode 按指定刷盘模式重试全部未完全释放条目与部件的回收并清理已完成项
// 入参: allowFlush 是否允许增量刷盘
// 返回: int64 本次实际释放的块字节数
func (p *streamPackage) reclaimPendingStorageMode(allowFlush bool) int64 {
	if p.ownedMemory == nil {
		return 0
	}
	var total int64
	if len(p.pendingEnvelopes) != 0 {
		remaining := p.pendingEnvelopes[:0]
		for _, entry := range p.pendingEnvelopes {
			if entry == nil || entry.headerFreed {
				continue
			}
			freed, done := p.reclaimEntryEnvelopeMode(entry, allowFlush)
			total += freed
			if !done {
				remaining = append(remaining, entry)
			}
		}
		if len(remaining) == 0 {
			p.pendingEnvelopes = nil
		} else {
			p.pendingEnvelopes = remaining
		}
	}
	if len(p.pendingParts) != 0 {
		for _, key := range slices.Sorted(maps.Keys(p.pendingParts)) {
			freed, done := p.reclaimPartMode(key, allowFlush)
			total += freed
			if done {
				delete(p.pendingParts, key)
			}
		}
		if len(p.pendingParts) == 0 {
			p.pendingParts = nil
		}
	}
	return total
}

// pinPart 增加指定逻辑部件的窗口引用计数以阻止流式内存与丢弃提示提前物理回收
// 入参: key 小写规范部件键
func (p *streamPackage) pinPart(key string) {
	if key == "" {
		return
	}
	if p.pinnedParts == nil {
		p.pinnedParts = make(map[string]int)
	}
	p.pinnedParts[key]++
}

// unpinPart 减少指定逻辑部件的窗口引用计数，归零且存在待回收标记时立即回收其压缩存储
// 入参: key 小写规范部件键
func (p *streamPackage) unpinPart(key string) {
	if key == "" || p.pinnedParts == nil {
		return
	}
	count := p.pinnedParts[key]
	if count <= 1 {
		delete(p.pinnedParts, key)
		if part := p.parts[key]; part != nil && part.reclaimPending && p.canReclaimPart(part) {
			p.reclaimPart(key)
		}
		return
	}
	p.pinnedParts[key] = count - 1
}

// canReclaimPart 判断逻辑部件是否已经完整到达、已完成关系与多作用域票据验证且未被窗口锁定或阻塞外部回调
// 入参: part 目标逻辑部件
// 返回: bool 是否可以立即释放压缩存储
func (p *streamPackage) canReclaimPart(part *streamPart) bool {
	if part == nil || part.reclaimed || part.last < 0 || len(part.entries) != part.last+1 {
		return false
	}
	key := strings.ToLower(part.name)
	if p.pinnedParts[key] > 0 {
		return false
	}
	if p.options.OnPart != nil && !part.emitted {
		return false
	}
	if p.options.OnXML != nil && p.types != nil && xmlMedia(p.types.declaredContentType(part.name)) && !part.xmlDone {
		return false
	}
	if p.consumeOnly && opcRelationshipName(part.name) && (!part.relsVerified || !part.relsRecorded) {
		return false
	}
	if p.consumeOnly && p.types != nil {
		if known, capabilities := printResourceMedia(opcMediaTypeBase(p.types.declaredContentType(part.name))); known && !capabilities {
			if !p.centralVerified {
				return false
			}
			required := p.ticketRequiredScopes[key]
			if required == 0 || part.ticketVerifiedScopes&required != required {
				return false
			}
		}
	}
	return true
}

// requestReclaimPart 请求回收逻辑部件存储，若当前被回调、窗口锁定或验证阻塞则打延迟回收标记
// 入参: key 小写规范部件键
// 返回: int64 立即回收的块字节数
func (p *streamPackage) requestReclaimPart(key string) int64 {
	if !p.consumeOnly || p.ownedMemory == nil {
		return 0
	}
	part := p.parts[key]
	if part == nil || part.reclaimed {
		return 0
	}
	if p.canReclaimPart(part) {
		return p.reclaimPart(key)
	}
	part.reclaimPending = true
	return 0
}

// reclaimPart 释放逻辑部件全部分片的原始压缩载荷、内存树、条目映射与缓存条目，未完全落盘时保留重试状态
// 入参: key 小写规范部件键
// 返回: int64 实际回收的块字节数
func (p *streamPackage) reclaimPart(key string) int64 {
	reclaimed, done := p.reclaimPartMode(key, true)
	if !done {
		if part := p.parts[key]; part != nil && !part.reclaimed {
			part.reclaimPending = true
			if p.pendingParts == nil {
				p.pendingParts = make(map[string]bool)
			}
			p.pendingParts[key] = true
		}
	}
	return reclaimed
}

// reclaimPartMode 按指定刷盘模式释放逻辑部件各分片存储，仅全部区间释放完成后才标记reclaimed并清空条目表
// 入参: key 小写规范部件键, allowFlush 是否允许增量刷盘
// 返回: int64 本次回收的块字节数, bool 该部件是否已完全释放
func (p *streamPackage) reclaimPartMode(key string, allowFlush bool) (int64, bool) {
	if p.ownedMemory == nil {
		return 0, true
	}
	part := p.parts[key]
	if part == nil || part.reclaimed {
		return 0, true
	}
	var reclaimed int64
	allDone := true
	anyProgress := false
	for _, pieceIndex := range slices.Sorted(maps.Keys(part.entries)) {
		entry := part.entries[pieceIndex]
		if entry == nil {
			continue
		}
		entry.header.Extra = nil
		envFreed, envDone := p.reclaimEntryEnvelopeMode(entry, allowFlush)
		reclaimed += envFreed
		if !envDone {
			allDone = false
			if !slices.Contains(p.pendingEnvelopes, entry) {
				p.pendingEnvelopes = append(p.pendingEnvelopes, entry)
			}
		}
		payFreed, payDone := p.reclaimEntryPayloadMode(entry, allowFlush)
		reclaimed += payFreed
		if payFreed > 0 || entry.payloadFreedBytes > 0 {
			anyProgress = true
		}
		if !payDone {
			allDone = false
		}
	}
	if anyProgress || allDone {
		if p.cache != nil {
			p.cache.discard(key)
			if p.discard == nil || p.discard.targetRefs[key] == 0 {
				p.cache.forgetProcessed(key)
			}
		}
		if p.pagePkg != nil {
			delete(p.pagePkg.parts, key)
		}
	}
	if !allDone {
		if anyProgress {
			part.partiallyReclaimed = true
		}
		part.reclaimPending = true
		return reclaimed, false
	}
	part.reclaimed = true
	part.partiallyReclaimed = false
	part.reclaimPending = false
	part.page = nil
	part.relations = nil
	part.layout = nil
	part.control = nil
	part.entries = nil
	delete(p.pendingParts, key)
	return reclaimed, true
}

// reclaimDeliveredPage 在纯前向消费模式交付完单页后立即释放页面本体、页面关系及私有StoryFragments，并检查文档级回收
// 入参: source 当前文档索引, pagePart 页面部件URI, docIndex 文档序号, pageIndex 文档内页序号
// 返回: error 关系校验错误
func (p *streamPackage) reclaimDeliveredPage(source *Reader, pagePart string, docIndex, pageIndex int) error {
	if !p.consumeOnly || p.ownedMemory == nil {
		return nil
	}
	pageKey := strings.ToLower(pagePart)
	p.requestReclaimPart(pageKey)
	relsPartName := createdRelationshipPart(pagePart)
	relsKey := strings.ToLower(relsPartName)
	var storyKey string
	if relsPart := p.parts[relsKey]; relsPart != nil && !relsPart.reclaimed {
		if items, err := source.pkg.relationshipsContext(p.context, pagePart); err == nil {
			storyType := formatNamespace(source.format) + "/storyfragments"
			for _, rel := range items {
				if rel.Type == storyType && rel.TargetMode == TargetModeInternal {
					if target, err := resolvePart(pagePart, rel.Target); err == nil {
						storyKey = strings.ToLower(target)
					}
					break
				}
			}
			if !relsPart.relsVerified && relsPart.last >= 0 && len(relsPart.entries) == relsPart.last+1 {
				if _, complete := p.pagePkg.parts[relsKey]; complete {
					if verified, vErr := p.pagePkg.readRelationshipsContext(p.context, pagePart, relsPart.name); vErr == nil {
						if err := p.recordVerifiedRelationships(pagePart, verified); err != nil {
							return err
						}
						relsPart.relsVerified = true
						relsPart.relsRecorded = true
					}
				}
			}
		}
		p.requestReclaimPart(relsKey)
	}
	if storyKey != "" {
		p.requestReclaimPart(storyKey)
	}
	if docIndex >= 0 && docIndex < p.document && docIndex < len(source.documents) && pageIndex == len(source.documents[docIndex].Pages)-1 {
		return p.reclaimCompletedDocument(source, docIndex)
	}
	return nil
}

// tryReclaimCompletedDocument 检查已闭合文档是否已交付全部页面，满足条件时补触发文档回收
// 入参: source 当前文档索引, docIndex 已闭合文档序号
// 返回: error 关系校验错误
func (p *streamPackage) tryReclaimCompletedDocument(source *Reader, docIndex int) error {
	if !p.consumeOnly || p.ownedMemory == nil || source == nil || docIndex < 0 || docIndex >= p.document || docIndex >= len(source.documents) {
		return nil
	}
	if p.options.OnPage != nil && p.pages < p.documentEndPage(source, docIndex) {
		return nil
	}
	return p.reclaimCompletedDocument(source, docIndex)
}

// reclaimCompletedDocument 释放已完成全部页面交付的固定文档本体、文档关系、文档结构缓存与文档级票据缓存，回收前保留未到达文档结构目标
// 入参: source 当前文档索引, docIndex 已完结文档序号
// 返回: error 关系校验错误
func (p *streamPackage) reclaimCompletedDocument(source *Reader, docIndex int) error {
	if !p.consumeOnly || p.ownedMemory == nil {
		return nil
	}
	if p.reclaimedDocuments == nil {
		p.reclaimedDocuments = make(map[int]bool)
	}
	if p.reclaimedDocuments[docIndex] {
		return nil
	}
	docPart := source.documents[docIndex].Part
	docKey := strings.ToLower(docPart)
	docRelsKey := strings.ToLower(createdRelationshipPart(docPart))
	if relsPart := p.parts[docRelsKey]; relsPart != nil && !relsPart.reclaimed {
		if !relsPart.relsVerified && relsPart.last >= 0 && len(relsPart.entries) == relsPart.last+1 {
			if _, complete := p.pagePkg.parts[docRelsKey]; complete {
				if verified, vErr := p.pagePkg.readRelationshipsContext(p.context, docPart, relsPart.name); vErr == nil {
					if err := p.recordVerifiedRelationships(docPart, verified); err != nil {
						return err
					}
					relsPart.relsVerified = true
					relsPart.relsRecorded = true
				}
			}
		} else if relsPart.relations != nil && !relsPart.relations.deferred && relsPart.relations.closed && !relsPart.relsRecorded {
			if err := p.recordVerifiedRelationships(docPart, relsPart.relations.items); err != nil {
				return err
			}
			relsPart.relsRecorded = true
		}
		p.requestReclaimPart(docRelsKey)
	}
	p.reclaimedDocuments[docIndex] = true
	if part := p.parts[docKey]; part != nil {
		if part.layout != nil && part.layout.closed {
			part.layout = nil
		}
		p.requestReclaimPart(docKey)
	}
	delete(p.docStructCached, docIndex)
	p.evictDocumentTicketCache()
	return nil
}

// Read 从缓冲流读取中央目录及结束记录并严格校验MaxInputBytes与取消状态，不写入压缩存储
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 输入、预算或取消错误
func (s *streamTailInput) Read(output []byte) (int, error) {
	if err := checkContext(s.context); err != nil {
		return 0, err
	}
	if len(output) == 0 {
		return 0, nil
	}
	if s.count == s.limit {
		var extra [1]byte
		n, err := s.reader.Read(extra[:])
		if n != 0 {
			return 0, fmt.Errorf("%w: stream input bytes", ErrLimit)
		}
		if err == nil {
			return 0, io.ErrNoProgress
		}
		return 0, err
	}
	if int64(len(output)) > s.limit-s.count {
		output = output[:int(s.limit-s.count)]
	}
	n, err := s.reader.Read(output)
	s.count += int64(n)
	if n == 0 && err == nil {
		return 0, io.ErrNoProgress
	}
	return n, err
}

// verifyStreamCentralDirectory 在纯前向消费模式下流式核对中央目录、ZIP64结束记录及EOCD，不占用载荷内存
// 入参: firstSig 首个非本地头4字节签名, centralOffset 中央目录起始逻辑偏移
// 返回: error 结构、字段冲突、截断、尾随垃圾、预算或取消错误
func (p *streamPackage) verifyStreamCentralDirectory(firstSig uint32, centralOffset int64) error {
	tail := &streamTailInput{reader: p.input.reader, context: p.context, limit: p.input.limit, count: p.input.count}
	known := make(map[int64]*streamEntry, len(p.entries))
	for _, entry := range p.entries {
		known[entry.offset] = entry
	}
	sig := firstSig
	var entryCount uint64
	for sig == packageZIPCentralSignature {
		if err := checkContext(p.context); err != nil {
			return err
		}
		entryCount++
		if entryCount > uint64(p.options.Limits.MaxPartCount) {
			return fmt.Errorf("%w: ZIP central entry count", ErrLimit)
		}
		var fixed [42]byte
		if _, err := io.ReadFull(tail, fixed[:]); err != nil {
			return p.streamInputError("streamed central record", err)
		}
		creatorVersion := binary.LittleEndian.Uint16(fixed[0:2])
		cdVersion := binary.LittleEndian.Uint16(fixed[2:])
		flags := binary.LittleEndian.Uint16(fixed[4:])
		method := binary.LittleEndian.Uint16(fixed[6:])
		modTime := binary.LittleEndian.Uint16(fixed[8:])
		modDate := binary.LittleEndian.Uint16(fixed[10:])
		crcVal := binary.LittleEndian.Uint32(fixed[12:])
		cdComp := binary.LittleEndian.Uint32(fixed[16:])
		cdUncomp := binary.LittleEndian.Uint32(fixed[20:])
		nameBytes := int(binary.LittleEndian.Uint16(fixed[24:]))
		extraBytes := int(binary.LittleEndian.Uint16(fixed[26:]))
		commentBytes := int(binary.LittleEndian.Uint16(fixed[28:]))
		if err := validateZIPMetadata(nameBytes, extraBytes, commentBytes); err != nil {
			return err
		}
		disk := uint64(binary.LittleEndian.Uint16(fixed[30:]))
		externalAttrs := binary.LittleEndian.Uint32(fixed[34:38])
		cdOffset := binary.LittleEndian.Uint32(fixed[38:])
		variable := make([]byte, nameBytes+extraBytes+commentBytes)
		if _, err := io.ReadFull(tail, variable); err != nil {
			return p.streamInputError("streamed central variable fields", err)
		}
		name := string(variable[:nameBytes])
		uncomp, comp, offset, diskVal, cdZIP64, err := packageZIP64Values(variable[nameBytes:nameBytes+extraBytes], uint64(cdUncomp), uint64(cdComp), uint64(cdOffset), disk)
		if err != nil {
			return err
		}
		if diskVal != 0 {
			return fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
		}
		entry := known[int64(offset)]
		if entry == nil {
			return fmt.Errorf("%w: streamed central record mismatch", ErrInvalid)
		}
		header := entry.header
		extendedOffset := cdOffset == 0xffffffff
		cdSizeZIP64 := cdUncomp == 0xffffffff || cdComp == 0xffffffff
		extendedSize := flags&8 != 0 && (cdSizeZIP64 || comp >= 0xffffffff || uncomp >= 0xffffffff)
		versionMatch := header.ReaderVersion == cdVersion || (extendedOffset || extendedSize) && cdVersion == 45 && (header.ReaderVersion == 10 && method == zip.Store || header.ReaderVersion == 20)
		if !versionMatch || cdZIP64 && cdVersion < 45 || entry.localZIP64 && (header.ReaderVersion != cdVersion || cdVersion < 45) {
			return fmt.Errorf("%w: streamed ZIP extraction version", ErrInvalid)
		}
		if header.Name != name || header.Flags != flags || header.Method != method || header.ModifiedTime != modTime || header.ModifiedDate != modDate || header.CRC32 != crcVal || header.CompressedSize64 != comp || header.UncompressedSize64 != uncomp {
			return fmt.Errorf("%w: streamed provisional/central fields", ErrInvalid)
		}
		cdHeader := zip.FileHeader{Name: name, CreatorVersion: creatorVersion, ExternalAttrs: externalAttrs}
		if cdHeader.FileInfo().IsDir() {
			if uncomp != 0 {
				return fmt.Errorf("%w: nonempty ZIP directory %q", ErrInvalid, name)
			}
			dir := strings.TrimSuffix(name, "/")
			if !strings.EqualFold(dir, strings.TrimPrefix(opcTypesName, "/")) {
				if _, err := opcPartName("/" + dir); err != nil {
					return fmt.Errorf("directory: %w", err)
				}
			}
			if !strings.HasSuffix(name, "/") {
				if err := p.reconcileStreamDirectoryAttribute(name, entry); err != nil {
					return err
				}
			}
		} else if !cdHeader.Mode().IsRegular() {
			return fmt.Errorf("%w: nonregular ZIP entry %q", ErrUnsupported, name)
		}
		delete(known, int64(offset))
		var nextSig [4]byte
		if _, err := io.ReadFull(tail, nextSig[:]); err != nil {
			return p.streamInputError("streamed central next signature", err)
		}
		sig = binary.LittleEndian.Uint32(nextSig[:])
	}
	if len(known) != 0 {
		return fmt.Errorf("%w: streamed central coverage", ErrInvalid)
	}
	cdEnd := tail.count - 4
	cdSize := uint64(cdEnd - centralOffset)
	if cdSize > uint64(p.options.Limits.MaxPackageBytes) {
		return fmt.Errorf("%w: ZIP central metadata budget", ErrLimit)
	}
	cdSizeWithSig := cdSize
	if sig == packageZIPDigitalSignature {
		var lengthBuf [2]byte
		if _, err := io.ReadFull(tail, lengthBuf[:]); err != nil {
			return p.streamInputError("streamed ZIP digital signature length", err)
		}
		dsLen := int(binary.LittleEndian.Uint16(lengthBuf[:]))
		if _, err := io.CopyN(io.Discard, tail, int64(dsLen)); err != nil {
			return p.streamInputError("streamed ZIP digital signature", err)
		}
		cdSizeWithSig = cdSize + 6 + uint64(dsLen)
		if cdSizeWithSig > uint64(p.options.Limits.MaxPackageBytes) {
			return fmt.Errorf("%w: ZIP central metadata budget", ErrLimit)
		}
		var nextSig [4]byte
		if _, err := io.ReadFull(tail, nextSig[:]); err != nil {
			return p.streamInputError("streamed ZIP post-signature record", err)
		}
		sig = binary.LittleEndian.Uint32(nextSig[:])
	}
	hasZIP64 := false
	matchedCDSize := cdSize
	if sig == packageZIP64EndSignature {
		hasZIP64 = true
		zip64Offset := tail.count - 4
		var z64 [52]byte
		if _, err := io.ReadFull(tail, z64[:]); err != nil {
			return p.streamInputError("streamed ZIP64 end record", err)
		}
		recordSize := binary.LittleEndian.Uint64(z64[:8])
		if recordSize < 44 || recordSize > uint64(p.options.Limits.MaxPackageBytes) {
			return fmt.Errorf("%w: ZIP64 end size", ErrInvalid)
		}
		if binary.LittleEndian.Uint16(z64[10:12]) >= 62 {
			return fmt.Errorf("%w: ZIP64 second-version end record", ErrUnsupported)
		}
		diskNum := binary.LittleEndian.Uint32(z64[12:16])
		cdDisk := binary.LittleEndian.Uint32(z64[16:20])
		diskEntries := binary.LittleEndian.Uint64(z64[20:28])
		totalEntries := binary.LittleEndian.Uint64(z64[28:36])
		z64Size := binary.LittleEndian.Uint64(z64[36:44])
		z64Offset := binary.LittleEndian.Uint64(z64[44:52])
		if diskNum != 0 || cdDisk != 0 || diskEntries != totalEntries {
			return fmt.Errorf("%w: multiple ZIP64 disks", ErrUnsupported)
		}
		if totalEntries != entryCount || z64Size != cdSize && z64Size != cdSizeWithSig || z64Offset != uint64(centralOffset) {
			return fmt.Errorf("%w: ZIP64 end fields", ErrInvalid)
		}
		matchedCDSize = z64Size
		if recordSize > 44 {
			if _, err := io.CopyN(io.Discard, tail, int64(recordSize-44)); err != nil {
				return p.streamInputError("streamed ZIP64 extensible data", err)
			}
		}
		var loc [20]byte
		if _, err := io.ReadFull(tail, loc[:]); err != nil {
			return p.streamInputError("streamed ZIP64 end locator", err)
		}
		if binary.LittleEndian.Uint32(loc[:4]) != packageZIP64LocatorSignature {
			return fmt.Errorf("%w: ZIP64 locator signature", ErrInvalid)
		}
		if binary.LittleEndian.Uint32(loc[4:8]) != 0 || binary.LittleEndian.Uint32(loc[16:20]) != 1 {
			return fmt.Errorf("%w: multiple ZIP64 disks", ErrUnsupported)
		}
		if binary.LittleEndian.Uint64(loc[8:16]) != uint64(zip64Offset) {
			return fmt.Errorf("%w: ZIP64 locator offset", ErrInvalid)
		}
		var nextSig [4]byte
		if _, err := io.ReadFull(tail, nextSig[:]); err != nil {
			return p.streamInputError("streamed ZIP end record signature", err)
		}
		sig = binary.LittleEndian.Uint32(nextSig[:])
	}
	if sig != packageZIPEndSignature {
		return fmt.Errorf("%w: missing ZIP end record", ErrInvalid)
	}
	var eocd [18]byte
	if _, err := io.ReadFull(tail, eocd[:]); err != nil {
		return p.streamInputError("streamed ZIP end record", err)
	}
	diskNum := binary.LittleEndian.Uint16(eocd[:2])
	cdDisk := binary.LittleEndian.Uint16(eocd[2:4])
	diskEntries := binary.LittleEndian.Uint16(eocd[4:6])
	totalEntries := binary.LittleEndian.Uint16(eocd[6:8])
	eocdSize := uint64(binary.LittleEndian.Uint32(eocd[8:12]))
	eocdOffset := uint64(binary.LittleEndian.Uint32(eocd[12:16]))
	commentLen := int(binary.LittleEndian.Uint16(eocd[16:18]))
	if hasZIP64 {
		if diskNum != 0 && diskNum != 0xffff || cdDisk != 0 && cdDisk != 0xffff {
			return fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
		}
		if diskEntries != 0xffff && uint64(diskEntries) != entryCount || totalEntries != 0xffff && uint64(totalEntries) != entryCount || eocdSize != 0xffffffff && eocdSize != matchedCDSize || eocdOffset != 0xffffffff && eocdOffset != uint64(centralOffset) {
			return fmt.Errorf("%w: ZIP32/ZIP64 end fields", ErrInvalid)
		}
	} else {
		if diskNum != 0 || cdDisk != 0 || diskEntries != totalEntries {
			return fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
		}
		if uint64(totalEntries) != entryCount || eocdSize != cdSize && eocdSize != cdSizeWithSig || eocdOffset != uint64(centralOffset) {
			return fmt.Errorf("%w: ZIP end fields", ErrInvalid)
		}
	}
	if commentLen > 0 {
		if _, err := io.CopyN(io.Discard, tail, int64(commentLen)); err != nil {
			return p.streamInputError("streamed ZIP end comment", err)
		}
	}
	var trailing [1]byte
	n, err := tail.Read(trailing[:])
	if n != 0 {
		return fmt.Errorf("%w: trailing bytes after ZIP end record", ErrInvalid)
	}
	if err != nil && err != io.EOF {
		return p.streamInputError("streamed ZIP end EOF", err)
	}
	p.input.count = tail.count
	p.centralVerified = true
	return nil
}

// reconcileStreamDirectoryAttribute 核对中央目录标记为目录但名称无斜杠后缀的条目，与Read路径保持一致
// 入参: name 物理ZIP条目名, entry 对应物理条目
// 返回: error 早期临时部件冲突或目录名无效错误
func (p *streamPackage) reconcileStreamDirectoryAttribute(name string, entry *streamEntry) error {
	partName, index, _, err := opcPieceName(name)
	if err != nil || index >= 0 {
		return fmt.Errorf("%w: streamed directory piece conflict %q", ErrInvalid, name)
	}
	if strings.EqualFold(partName, strings.TrimPrefix(opcTypesName, "/")) {
		return fmt.Errorf("%w: content types cannot be a directory", ErrInvalid)
	}
	canonical, err := opcPartName("/" + partName)
	if err != nil {
		return err
	}
	key := strings.ToLower(canonical)
	if part := p.parts[key]; part != nil {
		if p.options.OnPart != nil && part.emitted || part.xmlTokens != 0 || part.xmlDone || part.page != nil || part.layout != nil || part.relations != nil || part.control != nil || part.reclaimed {
			return fmt.Errorf("%w: streamed provisional part %q conflicts with central directory", ErrInvalid, part.name)
		}
		if part.xml != nil {
			part.xml.Close()
			part.xml = nil
			p.xmlActive--
		}
		delete(p.parts, key)
		if p.pagePkg != nil {
			delete(p.pagePkg.parts, key)
			delete(p.pagePkg.names, key)
		}
	}
	if p.ownedMemory != nil && entry != nil && !entry.payloadFreed {
		p.reclaimEntryPayloadMode(entry, true)
	}
	return nil
}

// finishConsume 完成纯前向消费模式下的完整性终检、全包关系、票据冲突、DiscardControl与剩余回调收尾
// 返回: error 完整性、内容类型、结构、关系、票据、回调、预算或取消错误
func (p *streamPackage) finishConsume() error {
	if p.ownedMemory != nil {
		p.reclaimPendingStorageMode(true)
	}
	if p.types == nil {
		return fmt.Errorf("%w: missing content types", ErrInvalid)
	}
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		if err := checkContext(p.context); err != nil {
			return err
		}
		part := p.parts[key]
		if !part.reclaimed && (part.last < 0 || len(part.entries) != part.last+1) {
			return fmt.Errorf("%w: incomplete streamed piece sequence for %q", ErrInvalid, part.name)
		}
		for i := strings.LastIndexByte(key, '/'); i > 0; i = strings.LastIndexByte(key[:i], '/') {
			if _, exists := p.parts[key[:i]]; exists {
				return fmt.Errorf("%w: part %q derives from another part", ErrInvalid, part.name)
			}
		}
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media := p.types.declaredContentType(part.name)
		if media == "" {
			return fmt.Errorf("%w: no content type for %q", ErrInvalid, part.name)
		}
		if opcRelationshipName(key) && !strings.EqualFold(media, opcRelsType) {
			return fmt.Errorf("%w: incorrect relationship content type for %q", ErrInvalid, part.name)
		}
	}
	if err := p.resumeDeferredXML(); err != nil {
		return err
	}
	p.preparePagePackage()
	if rootPart := p.parts["/_rels/.rels"]; rootPart != nil && !rootPart.reclaimed {
		if err := p.advanceRelationshipPart("/_rels/.rels"); err != nil {
			return err
		}
	}
	if err := p.activateStreamIndex(); err != nil {
		return err
	}
	if p.index == nil {
		return fmt.Errorf("%w: missing fixed representation relationship", ErrInvalid)
	}
	if err := p.verifyConsumeRelationships(); err != nil {
		return err
	}
	if err := p.verifyConsumeLayout(); err != nil {
		return err
	}
	if err := p.verifyConsumeTickets(); err != nil {
		return err
	}
	if err := p.verifyConsumeDiscard(); err != nil {
		return err
	}
	if err := p.emitMetadataCallbacks(); err != nil {
		return err
	}
	if err := p.verifyConsumeMetadataBounds(); err != nil {
		return err
	}
	if p.options.OnPage != nil {
		if err := p.releaseProcessed(); err != nil {
			return err
		}
		p.pageHold = false
		p.pageWait = nil
		p.pageMissing = nil
		for p.pages < len(p.index.pages) {
			if err := checkContext(p.context); err != nil {
				return err
			}
			parsed, err := p.index.Page(p.context, p.pages)
			if err != nil {
				return err
			}
			if err := p.notifyPage(p.index, p.pages, parsed); err != nil {
				return err
			}
			p.pages++
			if err := p.advanceDocumentEvents(p.index, true); err != nil {
				return err
			}
		}
	}
	if err := p.advanceDocumentEvents(p.index, true); err != nil {
		return err
	}
	if p.options.OnXML != nil {
		for _, key := range slices.Sorted(maps.Keys(p.parts)) {
			if key == strings.ToLower(opcTypesName) {
				continue
			}
			part := p.parts[key]
			if part.xmlDone || part.reclaimed {
				continue
			}
			media := p.types.declaredContentType(part.name)
			if !xmlMedia(media) {
				continue
			}
			if err := p.advanceXML(part, media); err != nil {
				return err
			}
		}
	}
	if p.options.OnPart != nil {
		for _, key := range slices.Sorted(maps.Keys(p.parts)) {
			if key == strings.ToLower(opcTypesName) {
				continue
			}
			part := p.parts[key]
			if part.emitted || part.reclaimed {
				continue
			}
			if err := p.emit(part); err != nil {
				return err
			}
		}
		if err := p.releaseProcessed(); err != nil {
			return err
		}
	}
	if p.onConsumeFinish != nil {
		if err := p.onConsumeFinish(p.index, !p.reclaimed); err != nil {
			return err
		}
	}
	p.closeXML()
	return checkContext(p.context)
}

// verifyConsumeLayout 终审纯前向消费模式下的固定文档序列、全部固定文档与全部固定页面的存在性与媒体类型合法性
// 返回: error 缺失部件、媒体类型或结构错误
func (p *streamPackage) verifyConsumeLayout() error {
	if err := p.advanceLayoutIndex(); err != nil {
		return err
	}
	seqKey := strings.ToLower(p.index.sequence)
	seqPart := p.parts[seqKey]
	if seqPart == nil {
		return &PartError{Part: p.index.sequence, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, seqKey, fs.ErrNotExist)}
	}
	seqMedia := p.types.declaredContentType(p.index.sequence)
	if !matchStandardContentType(p.index.format, seqMedia, fixedContentType("fixeddocumentsequence")) {
		return &PartError{Part: p.index.sequence, Err: fmt.Errorf("%w: unexpected content type %q", ErrInvalid, seqMedia)}
	}
	if !p.sequenceRead && !seqPart.reclaimed && (seqPart.layout == nil || seqPart.layout.deferred || !seqPart.layout.closed) {
		refs, err := p.index.readDocumentReferencesContext(p.context)
		if err != nil {
			return err
		}
		if len(refs) < len(p.documents) {
			return fmt.Errorf("%w: streamed sequence prefix length", ErrInvalid)
		}
		for _, ref := range refs[len(p.documents):] {
			p.documents = append(p.documents, ref)
			p.documentKeys[strings.ToLower(ref)] = true
		}
		p.sequenceRead = true
	}
	if len(p.documents) == 0 {
		return fmt.Errorf("%w: incomplete fixed document sequence", ErrInvalid)
	}
	if err := p.advanceLayoutIndex(); err != nil {
		return err
	}
	if p.document != len(p.documents) {
		missingDoc := p.documents[p.document]
		docKey := strings.ToLower(missingDoc)
		if p.parts[docKey] == nil {
			return &PartError{Part: missingDoc, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, docKey, fs.ErrNotExist)}
		}
		return fmt.Errorf("%w: incomplete fixed document %q", ErrInvalid, missingDoc)
	}
	for _, page := range p.index.pages {
		if err := checkContext(p.context); err != nil {
			return err
		}
		pageKey := strings.ToLower(page.Part)
		pagePart := p.parts[pageKey]
		if pagePart == nil {
			return &PartError{Part: page.Part, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, pageKey, fs.ErrNotExist)}
		}
		pageMedia := p.types.declaredContentType(page.Part)
		if !matchStandardContentType(p.index.format, pageMedia, fixedContentType("fixedpage")) {
			return &PartError{Part: page.Part, Err: fmt.Errorf("%w: unexpected content type %q", ErrInvalid, pageMedia)}
		}
		if p.options.OnPage == nil && !pagePart.reclaimed && !pagePart.partiallyReclaimed {
			if _, err := p.index.readPageHeaderStream(p.context, page.Part); err != nil {
				return err
			}
		}
	}
	return nil
}

// verifyConsumeDiscard 终审包级DiscardControl目标存在性、媒体类型及完整结构合法性
// 返回: error 缺失目标、媒体类型、结构或取消错误
func (p *streamPackage) verifyConsumeDiscard() error {
	if p.discard != nil {
		if err := p.updateDiscard(p.index); err != nil {
			return err
		}
		if p.discard.target != "" && !p.discard.loaded {
			key := strings.ToLower(p.discard.target)
			if p.parts[key] == nil {
				return &PartError{Part: p.discard.target, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
			}
			control, err := p.index.DiscardControl(p.context)
			if err != nil {
				return err
			}
			if err := p.appendDiscardHints(control.Hints, true); err != nil {
				return err
			}
			p.discard.loaded = true
		}
		return nil
	}
	if p.discardTarget == "" {
		return nil
	}
	key := strings.ToLower(p.discardTarget)
	targetPart := p.parts[key]
	if targetPart == nil {
		return &PartError{Part: p.discardTarget, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
	}
	media := p.types.declaredContentType(p.discardTarget)
	if !matchStandardContentType(p.index.format, media, fixedContentType("discard-control")) {
		return &PartError{Part: p.discardTarget, Err: fmt.Errorf("%w: discard control content type", ErrInvalid)}
	}
	if !targetPart.reclaimed && !targetPart.partiallyReclaimed {
		if _, err := p.index.DiscardControl(p.context); err != nil {
			return err
		}
	}
	return nil
}

// verifyFallbackConsume 在ConsumeStream回退随机访问路径后补齐固定页面存在性、票据关联与DiscardControl目标检查
// 入参: r 已完成构造的随机访问阅读器
// 返回: error 缺失部件、媒体类型、结构、票据或取消错误
func (p *streamPackage) verifyFallbackConsume(r *Reader) error {
	for _, page := range r.pages {
		if err := checkContext(p.context); err != nil {
			return err
		}
		key := strings.ToLower(page.Part)
		if _, exists := r.pkg.parts[key]; !exists {
			return &PartError{Part: page.Part, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
		}
		media, err := r.pkg.contentType(page.Part)
		if err != nil {
			return &PartError{Part: page.Part, Err: err}
		}
		if !matchStandardContentType(r.format, media, fixedContentType("fixedpage")) {
			return &PartError{Part: page.Part, Err: fmt.Errorf("%w: unexpected content type %q", ErrInvalid, media)}
		}
	}
	if err := r.validatePrintTicketLinks(p.context); err != nil {
		return err
	}
	relations, err := r.pkg.relationshipsContext(p.context, "/")
	if err != nil {
		return err
	}
	target, err := discardControlTarget(relations, r.format)
	if err != nil {
		return err
	}
	if target != "" {
		if _, err := r.DiscardControl(p.context); err != nil {
			return err
		}
	}
	return nil
}

// newStreamXMLParser 启动单个有界XML解析状态，wantNamespaces控制是否为所有词元深拷贝命名空间快照
// 入参: limits XML复杂度及字节上限, ctx 取消Context, wantNamespaces 是否为每个词元生成独立命名空间快照
// 返回: *streamXMLParser 持续解析状态
func newStreamXMLParser(limits Limits, ctx context.Context, wantNamespaces bool) *streamXMLParser {
	ctx, cancel := context.WithCancel(normalizeContext(ctx))
	p := &streamXMLParser{context: ctx, cancel: cancel, chunks: make(chan streamXMLChunk), events: make(chan streamXMLEvent), stop: make(chan struct{}), done: make(chan struct{})}
	go func() {
		defer close(p.done)
		defer p.cancel()
		input := &streamXMLInput{parser: p}
		defer input.Close()
		depth := 0
		var ownerStack []*xmlElement
		var nsStack []map[string]string
		err := scanXMLReader(input, limits, ctx, func(token xml.Token, node *xmlElement, start, end int64) error {
			var event StreamXMLToken
			if wantNamespaces {
				event = streamXMLToken(token, node, depth, start, end)
				if _, begin := token.(xml.StartElement); begin {
					depth++
				} else if _, finish := token.(xml.EndElement); finish {
					depth--
					event.Depth = depth
				}
			} else {
				var ns map[string]string
				if _, begin := token.(xml.StartElement); begin {
					if node != nil {
						if len(ownerStack) > 0 && ownerStack[len(ownerStack)-1] == node.namespaceOwner {
							ns = nsStack[len(nsStack)-1]
						} else {
							ns = maps.Clone(node.Namespaces)
						}
						ownerStack = append(ownerStack, node.namespaceOwner)
						nsStack = append(nsStack, ns)
					}
					event = streamXMLTokenWithNS(token, node, depth, start, end, ns)
					depth++
				} else if _, finish := token.(xml.EndElement); finish {
					if len(ownerStack) > 0 {
						ownerStack[len(ownerStack)-1] = nil
						ownerStack = ownerStack[:len(ownerStack)-1]
						nsStack[len(nsStack)-1] = nil
						nsStack = nsStack[:len(nsStack)-1]
					}
					depth--
					event = streamXMLTokenWithNS(token, node, depth, start, end, nil)
				} else {
					event = streamXMLTokenWithNS(token, node, depth, start, end, nil)
				}
			}
			select {
			case <-p.stop:
				return ErrClosed
			case <-p.context.Done():
				return p.context.Err()
			default:
			}
			select {
			case p.events <- streamXMLEvent{token: &event}:
				return nil
			case <-p.stop:
				return ErrClosed
			case <-p.context.Done():
				return p.context.Err()
			}
		})
		select {
		case p.events <- streamXMLEvent{err: err}:
		case <-p.stop:
		case <-p.context.Done():
		}
	}()
	return p
}

// streamXMLToken 复制校验后的词元、属性和命名空间，不向消费线程暴露正在增长的XML树
// 入参: token 已校验词元, node 所属元素, depth 当前层级, start, end UTF-8范围
// 返回: StreamXMLToken 独立词元
func streamXMLToken(token xml.Token, node *xmlElement, depth int, start, end int64) StreamXMLToken {
	var ns map[string]string
	if node != nil {
		ns = make(map[string]string, len(node.Namespaces))
		maps.Copy(ns, node.Namespaces)
	}
	return streamXMLTokenWithNS(token, node, depth, start, end, ns)
}

// streamXMLTokenWithNS 按给定命名空间映射构造独立词元，避免内部元数据消费逐词元复制整张命名空间表
// 入参: token 已校验词元, node 所属元素, depth 当前层级, start, end UTF-8范围, namespaces 关联命名空间映射
// 返回: StreamXMLToken 独立词元
func streamXMLTokenWithNS(token xml.Token, node *xmlElement, depth int, start, end int64, namespaces map[string]string) StreamXMLToken {
	result := StreamXMLToken{Token: xml.CopyToken(token), Namespaces: namespaces, Depth: depth, Start: start, End: end}
	if node == nil {
		return result
	}
	switch token := result.Token.(type) {
	case xml.StartElement:
		token.Name, token.Attr = node.Name, append([]xml.Attr(nil), node.Attr...)
		result.Token = token
	case xml.EndElement:
		token.Name = node.Name
		result.Token = token
	}
	return result
}

// Read 只在当前分片确认结束后请求后续分片，最后分片结束才返回逻辑EOF
// 入参: output 接收缓冲
// 返回: int 已读字节数, error 输入、关闭或逻辑结束信息
func (s *streamXMLInput) Read(output []byte) (int, error) {
	if len(output) == 0 {
		return 0, nil
	}
	for {
		if s.current == nil {
			if s.last {
				return 0, io.EOF
			}
			select {
			case <-s.parser.stop:
				return 0, ErrClosed
			case <-s.parser.context.Done():
				return 0, s.parser.context.Err()
			default:
			}
			select {
			case s.parser.events <- streamXMLEvent{need: true}:
			case <-s.parser.stop:
				return 0, ErrClosed
			case <-s.parser.context.Done():
				return 0, s.parser.context.Err()
			}
			select {
			case chunk := <-s.parser.chunks:
				s.current, s.last = chunk.input, chunk.last
			case <-s.parser.stop:
				return 0, ErrClosed
			case <-s.parser.context.Done():
				return 0, s.parser.context.Err()
			}
			if s.current == nil {
				if s.last {
					continue
				}
				return 0, fmt.Errorf("%w: empty stream XML chunk", ErrInvalid)
			}
		}
		n, err := s.current.Read(output)
		if err == io.EOF {
			closeErr := s.current.Close()
			s.current = nil
			if closeErr != nil {
				return n, closeErr
			}
			if n != 0 {
				return n, nil
			}
			continue
		}
		return n, err
	}
}

// Close 释放当前分片，不关闭原压缩存储
// 返回: error 当前分片关闭错误
func (s *streamXMLInput) Close() error {
	if s.current == nil {
		return nil
	}
	err := s.current.Close()
	s.current = nil
	return err
}

// Close 停止词元发送及分片等待，并等待解析状态完全退出，重复关闭无副作用
func (p *streamXMLParser) Close() {
	p.stopOnce.Do(func() {
		p.cancel()
		close(p.stop)
	})
	<-p.done
}

// xmlMedia 判断已声明媒体类型是否为XML，自动剥离合法MIME参数，不按文件扩展名猜测输入内容
// 入参: media 声明媒体类型
// 返回: bool 是否应进入XML词元处理
func xmlMedia(media string) bool {
	media = strings.ToLower(opcMediaTypeBase(media))
	return strings.HasSuffix(media, "+xml") || media == "application/xml" || media == "text/xml"
}

// deliverXML 在调用线程交付词元，仅当订阅OnXML时累计全包词元及命名空间快照预算
// 入参: part 逻辑部件信息，尚未完成时Size为负一, event 独立词元
// 返回: error 预算、回调或取消错误
func (p *streamPackage) deliverXML(part PartInfo, event StreamXMLToken) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	if p.options.OnXML == nil {
		return nil
	}
	if _, begin := event.Token.(xml.StartElement); begin {
		p.xmlNodes++
		if p.xmlNodes > p.options.Limits.MaxXMLNodes {
			return fmt.Errorf("%w: streamed XML element budget", ErrLimit)
		}
	}
	if len(event.Namespaces) > p.options.Limits.MaxXMLBindings-p.xmlBindings {
		return fmt.Errorf("%w: streamed XML namespace snapshot budget", ErrLimit)
	}
	p.xmlBindings += len(event.Namespaces)
	if err := p.options.OnXML(p.context, part, event); err != nil {
		return err
	}
	return checkContext(p.context)
}

// drainXML 处理当前分片可完成的词元，停在需要新分片或逻辑XML最终结果的明确边界，释槽后自动恢复排队XML部件
// 入参: part 当前逻辑部件, media 声明媒体类型
// 返回: error XML、预算、回调或取消错误
func (p *streamPackage) drainXML(part *streamPart, media string) error {
	parser := part.xml
	for {
		if err := checkContext(p.context); err != nil {
			return err
		}
		select {
		case event := <-parser.events:
			if event.need {
				return checkContext(p.context)
			}
			if event.token != nil {
				if err := checkContext(p.context); err != nil {
					return err
				}
				if err := p.consumeMetadata(part, media, *event.token); err != nil {
					return err
				}
				size := int64(-1)
				if part.last >= 0 && len(part.entries) == part.last+1 {
					size = int64(part.bytes)
				}
				if part.xmlReplay != 0 {
					part.xmlReplay--
				} else {
					if err := p.deliverXML(PartInfo{Name: part.name, ContentType: media, Size: size}, *event.token); err != nil {
						return err
					}
					part.xmlTokens++
				}
				continue
			}
			part.xmlDone = true
			p.xmlActive--
			parser.Close()
			part.xml = nil
			if event.err != nil {
				return event.err
			}
			if opcRelationshipName(part.name) && part.relations != nil && part.relations.closed && !part.relations.deferred {
				part.relsVerified = true
				if p.index != nil && !part.relsRecorded {
					if err := p.recordVerifiedRelationships(relationshipSource(part.name), part.relations.items); err != nil {
						return err
					}
					part.relsRecorded = true
				}
			}
			if part.reclaimPending && p.canReclaimPart(part) {
				p.reclaimPart(strings.ToLower(part.name))
			}
			return p.resumeDeferredXML()
		case <-p.context.Done():
			return p.context.Err()
		case <-parser.done:
			if err := parser.context.Err(); err != nil {
				return err
			}
			return ErrClosed
		}
	}
}

// resumeDeferredXML 在存在空闲解析槽位时按入队顺序恢复先前延迟的XML部件增量解析
// 返回: error XML、预算、回调或取消错误
func (p *streamPackage) resumeDeferredXML() error {
	if p.xmlResuming || p.types == nil {
		return nil
	}
	p.xmlResuming = true
	defer func() { p.xmlResuming = false }()
	for p.xmlActive < p.options.MaxXMLStreams && len(p.xmlQueue) != 0 {
		if err := checkContext(p.context); err != nil {
			return err
		}
		next := p.xmlQueue[0]
		p.xmlQueue[0] = nil
		p.xmlQueue = p.xmlQueue[1:]
		if next == nil || next.xmlDone || next.reclaimed || !next.xmlDeferred {
			continue
		}
		next.xmlDeferred = false
		media := p.types.declaredContentType(next.name)
		if err := p.advanceXML(next, media); err != nil {
			return err
		}
	}
	if len(p.xmlQueue) == 0 {
		p.xmlQueue = nil
	}
	return nil
}

// advanceXML 保持跨分片解析状态，乱序分片等待缺口补齐；满槽入队等待并在槽位释放后自动恢复
// 入参: part 当前逻辑部件, media 已声明媒体类型
// 返回: error XML、输入、预算、回调或取消错误
func (p *streamPackage) advanceXML(part *streamPart, media string) error {
	layout := p.selectedLayout(part.name, media)
	discard := p.selectedDiscard(part.name, media)
	relations := p.selectedRelationships(part.name, media)
	metadata := discard || layout || relations || p.selectedPage(part.name, media)
	if (discard || relations) && part.bytes > uint64(min(p.options.Limits.MaxMetadataBytes, p.options.Limits.MaxPartBytes, p.options.Limits.MaxPackageBytes)) {
		return fmt.Errorf("%w: streamed metadata bytes", ErrLimit)
	}
	if !metadata && p.options.OnXML == nil || !xmlMedia(media) || part.xmlDone || part.reclaimed {
		return nil
	}
	if part.xmlDeferred {
		if p.xmlActive >= p.options.MaxXMLStreams {
			return nil
		}
		part.xmlDeferred = false
	}
	if part.entries[0] == nil {
		return nil
	}
	if metadata && !part.xmlMetadata && part.xml != nil {
		part.xml.Close()
		p.xmlActive--
		part.xml, part.xmlNext, part.xmlReplay = nil, 0, part.xmlTokens
	}
	if part.xml == nil {
		if p.xmlActive >= p.options.MaxXMLStreams {
			part.xmlDeferred = true
			p.xmlQueue = append(p.xmlQueue, part)
			return nil
		}
		part.xml = newStreamXMLParser(p.options.Limits, p.context, p.options.OnXML != nil)
		part.xmlMetadata = metadata
		p.xmlActive++
		if err := p.drainXML(part, media); err != nil {
			return err
		}
	}
	if err := p.input.flush(); err != nil {
		return err
	}
	for !part.xmlDone && part.xml != nil && part.entries[part.xmlNext] != nil {
		if err := checkContext(p.context); err != nil {
			return err
		}
		entry := part.entries[part.xmlNext]
		chunk := streamXMLChunk{input: &streamLogicalReader{storage: p.input.storage, entries: []*streamEntry{entry}, context: part.xml.context}, last: part.last >= 0 && part.xmlNext == part.last}
		select {
		case part.xml.chunks <- chunk:
			part.xmlNext++
		case <-p.context.Done():
			chunk.input.Close()
			return p.context.Err()
		case <-part.xml.done:
			chunk.input.Close()
			if err := part.xml.context.Err(); err != nil {
				return err
			}
			return ErrClosed
		}
		if err := p.drainXML(part, media); err != nil {
			return err
		}
	}
	return nil
}

// closeXML 停止并等待所有解析状态，不让失败或延迟输入留下等待分片的Goroutine
func (p *streamPackage) closeXML() {
	for _, part := range p.parts {
		if part.xml != nil {
			part.xml.Close()
			part.xml = nil
		}
	}
	p.xmlActive = 0
	p.xmlQueue = nil
}

// finishXML 对延迟部件完整解析，已交付前缀只做重新校验，不重复调用词元回调
// 入参: r 已完成物理校验的最终阅读器
// 返回: error XML、输入、预算、回调或取消错误
func (p *streamPackage) finishXML(r *Reader) error {
	p.closeXML()
	if p.options.OnXML == nil && !p.needsIndex() {
		return nil
	}
	if p.options.OnPage != nil {
		if err := p.updateDiscard(r); err != nil {
			return err
		}
	}
	parts, err := r.Parts()
	if err != nil {
		return err
	}
	wantNS := p.options.OnXML != nil
	for _, info := range parts {
		metadata := p.selectedDiscard(info.Name, info.ContentType) || p.selectedLayout(info.Name, info.ContentType) || p.selectedRelationships(info.Name, info.ContentType) || p.selectedPage(info.Name, info.ContentType)
		if !xmlMedia(info.ContentType) || !wantNS && !metadata {
			continue
		}
		part := p.parts[strings.ToLower(info.Name)]
		skip := 0
		if part != nil {
			if part.xmlDone {
				continue
			}
			skip = part.xmlTokens
			part.control = nil
			part.layout = nil
		}
		input, err := r.OpenPart(p.context, info.Name, nil)
		if err != nil {
			return err
		}
		depth := 0
		err = scanXMLReader(input, p.options.Limits, p.context, func(token xml.Token, node *xmlElement, start, end int64) error {
			var event StreamXMLToken
			if wantNS {
				event = streamXMLToken(token, node, depth, start, end)
			} else {
				event = streamXMLTokenWithNS(token, node, depth, start, end, nil)
			}
			if _, begin := token.(xml.StartElement); begin {
				depth++
			} else if _, finish := token.(xml.EndElement); finish {
				depth--
				event.Depth = depth
			}
			if skip != 0 {
				skip--
				return nil
			}
			return p.deliverXML(info, event)
		})
		closeErr := input.Close()
		if err != nil {
			return err
		}
		if closeErr != nil {
			return closeErr
		}
		if part != nil {
			part.xmlDone = true
		}
	}
	return nil
}
