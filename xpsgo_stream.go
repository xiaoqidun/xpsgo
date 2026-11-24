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
	"compress/flate"
	"container/list"
	"context"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"hash/crc32"
	"io"
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

// StreamReadOptions 设置前向流读取的存储、预算与回调，MaxInputBytes与MaxMemoryBytes零值沿用MaxPackageBytes（默认1GiB）
// Storage为nil使用有界内存并在Reader.Close释放，外部Storage不由库关闭；MaxCacheBytes默认16MiB，MaxXMLStreams默认16
// OnPart、OnPage、OnDiscard与OnXML回调交付临时视图，Read成功返回后方确认整包完整有效
type StreamReadOptions struct {
	Limits         Limits
	MaxInputBytes  int64
	MaxMemoryBytes int64
	MaxCacheBytes  int64
	MaxXMLStreams  int
	Storage        StreamStorage
	OnPart         func(context.Context, PartInfo, io.Reader) error
	OnPage         func(context.Context, *StreamPage) error
	OnDiscard      func(context.Context, StreamDiscard) error
	OnXML          func(context.Context, PartInfo, StreamXMLToken) error
}

// streamEntry 保存已经消费并校验的物理载荷范围，不分配完整解压部件
type streamEntry struct {
	header zip.FileHeader
	offset int64
	data   int64
}

// streamPart 保存完整或待组装的逻辑部件，last为末片编号，whole排除整部件和分片混用
type streamPart struct {
	name        string
	entries     map[int]*streamEntry
	last        int
	bytes       uint64
	whole       bool
	emitted     bool
	xml         *streamXMLParser
	xmlNext     int
	xmlTokens   int
	xmlDone     bool
	xmlDeferred bool
	xmlMetadata bool
	xmlReplay   int
	control     *streamPartialDiscard
	layout      *streamPartialLayout
	relations   *streamPartialRelationships
	page        *streamPartialPage
}

// streamPackage 保存前向读取的物理索引、逻辑部件组装状态及内容类型表
type streamPackage struct {
	input        *streamInput
	options      StreamReadOptions
	context      context.Context
	entries      []*streamEntry
	parts        map[string]*streamPart
	seen         map[string]bool
	types        *packageReader
	bytes        uint64
	deferred     bool
	pagePkg      *packageReader
	index        *Reader
	pages        int
	pageWait     map[string]bool
	pageHold     bool
	pageTickets  [][]string
	ticketRefs   map[string]bool
	documents    []string
	document     int
	documentKeys map[string]bool
	sequenceRead bool
	seenPages    map[string]bool
	pageNames    map[string]bool
	cache        *streamResourceCache
	discard      *streamDiscardState
	xmlActive    int
	xmlNodes     int
	xmlBindings  int
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
	target  string
	checked bool
	loaded  bool
	hints   []DiscardHint
	byPage  map[string][]int
	started map[string]bool
	waiting map[string][]int
	done    map[int]bool
}

// streamLimitedInput 为有明确压缩长度的载荷提供精确边界，不让Deflate缓冲越过描述符
type streamLimitedInput struct {
	input *streamInput
	left  uint64
}

// streamInput 记录真正消费的字节并批量存储，为Deflate提供不越过码流结尾的ReadByte
type streamInput struct {
	reader  *bufio.Reader
	storage StreamStorage
	context context.Context
	limit   int64
	count   int64
	pending []byte
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

// streamMemory 按固定块保存实际到达的压缩容器，不按声明尺寸提前分配
type streamMemory struct {
	mu     sync.RWMutex
	chunks [][]byte
	size   int64
	limit  int64
	closed bool
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
	}
}

// Read 从前向输入流式消费XPS或OpenXPS，在完整校验目录与载荷后返回支持随机读取的Reader，失败时返回nil
// 压缩容器保留于存储按需解压，不关闭输入与外部存储；回调交付均为临时结果，外部存储须在Reader期间保持不变
// 入参: ctx 取消Context，nil采用Background, input 前向输入, options 存储、预算及回调参数，nil采用默认值
// 返回: *Reader 完整验证的封装及文档索引，失败为nil, error 输入、封装、存储、回调、预算或取消错误
func Read(ctx context.Context, input io.Reader, options *StreamReadOptions) (*Reader, error) {
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
	if input == nil || configuration.MaxInputBytes < 1 || configuration.MaxMemoryBytes < 1 || configuration.MaxCacheBytes < 0 || configuration.MaxXMLStreams < 1 || configuration.OnDiscard != nil && configuration.OnPage == nil {
		return nil, fmt.Errorf("%w: stream read parameters", ErrInvalid)
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
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
	if err := p.reconcile(r); err != nil {
		return nil, err
	}
	if err := p.finishRelationships(r); err != nil {
		return nil, err
	}
	if err := p.finishXML(r); err != nil {
		return nil, err
	}
	if p.cache != nil {
		r.pkg.cache = p.cache
		defer func() { r.pkg.cache = nil }()
	}
	if err := p.emitRemaining(r); err != nil {
		return nil, err
	}
	if err := p.finishPages(r); err != nil {
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

// consume 顺序处理可确定边界的本地条目，遇到中央记录或不明确边界时只继续接收，不猜测下一个头
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
		if binary.LittleEndian.Uint32(signature[:]) != packageZIPLocalSignature {
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
			p.deferred = true
			return normalizeStreamError(p.context, writeCompressionInput(io.Discard, p.input, buffer, p.context))
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
		if p.options.OnPart == nil && p.options.OnPage == nil && p.options.OnXML == nil {
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
		d.byPage, d.done = make(map[string][]int), make(map[int]bool)
	}
	for index := len(d.hints); index < len(hints); index++ {
		hint := hints[index]
		if err := checkContext(p.context); err != nil {
			return err
		}
		key := strings.ToLower(hint.SentinelPage)
		d.hints = append(d.hints, hint)
		d.byPage[key] = append(d.byPage[key], index)
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

// scheduleDiscard 对已处理目标执行提示，未处理目标按部件身份排队，不把到达当作已经处理
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
		p.discard.waiting[key] = append(p.discard.waiting[key], index)
		return nil
	}
	return p.executeDiscard(index, late)
}

// executeDiscard 移除缓存后报告提示，不使缓存中借出的只读字节失效
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
	bytes := p.cache.discard(strings.ToLower(hint.Target))
	p.discard.done[index] = true
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

// readEntry 读取本地头及可以确定边界的载荷，未知长度Store返回延迟标记而不扫描签名
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
		return nil, true, nil
	}
	entry := &streamEntry{header: header, offset: offset, data: p.input.count}
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
	entry.header.CRC32, entry.header.CompressedSize64, entry.header.UncompressedSize64 = actualCRC, actualCompressed, count
	return entry, false, nil
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

// flush 将当前缓冲完整写入随机存储，不吞掉短写及原始存储错误
// 返回: error 存储、计数或取消错误
func (s *streamInput) flush() error {
	if err := checkContext(s.context); err != nil {
		return err
	}
	if len(s.pending) == 0 {
		return nil
	}
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

// selectedDiscard 只对已确认包根关联的控制部件启用自动语义，不解释未关联附加部件
// 入参: name 部件名, media 声明媒体类型
// 返回: bool 是否为当前消费者的控制部件
func (p *streamPackage) selectedDiscard(name, media string) bool {
	return p.options.OnPage != nil && p.discard != nil && p.discard.checked && strings.EqualFold(p.discard.target, name) && strings.EqualFold(media, fixedContentType("discard-control"))
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
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: maps.Clone(event.Namespaces)}
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
	if part.emitted || p.types == nil {
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
		return p.emitPages(part.name)
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
	if err := checkContext(p.context); err != nil {
		return err
	}
	return p.emitPages(part.name)
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
// 返回: int 已读字节数, error 越界、结束或关闭错误
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
	count := 0
	for len(output) != 0 && offset < s.size {
		index, position := int(offset/streamBufferBytes), int(offset%streamBufferBytes)
		available := min(int64(len(s.chunks[index])-position), s.size-offset)
		n := copy(output, s.chunks[index][position:position+int(available)])
		offset += int64(n)
		count += n
		output = output[n:]
	}
	if len(output) != 0 {
		return count, io.EOF
	}
	return count, nil
}

// Close 释放全部压缩块，重复关闭无副作用
// 返回: error nil
func (s *streamMemory) Close() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.closed, s.chunks, s.size = true, nil, 0
	return nil
}

// newStreamXMLParser 启动单个有界XML解析状态，调用方回调在主消费线程执行
// 入参: limits XML复杂度及字节上限, ctx 取消Context
// 返回: *streamXMLParser 持续解析状态
func newStreamXMLParser(limits Limits, ctx context.Context) *streamXMLParser {
	ctx, cancel := context.WithCancel(ctx)
	p := &streamXMLParser{context: ctx, cancel: cancel, chunks: make(chan streamXMLChunk), events: make(chan streamXMLEvent), stop: make(chan struct{}), done: make(chan struct{})}
	go func() {
		defer close(p.done)
		defer p.cancel()
		input := &streamXMLInput{parser: p}
		defer input.Close()
		depth := 0
		err := scanXMLReader(input, limits, ctx, func(token xml.Token, node *xmlElement, start, end int64) error {
			event := streamXMLToken(token, node, depth, start, end)
			if _, begin := token.(xml.StartElement); begin {
				depth++
			} else if _, end := token.(xml.EndElement); end {
				depth--
				event.Depth = depth
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
	result := StreamXMLToken{Token: xml.CopyToken(token), Depth: depth, Start: start, End: end}
	if node == nil {
		return result
	}
	result.Namespaces = make(map[string]string, len(node.Namespaces))
	maps.Copy(result.Namespaces, node.Namespaces)
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

// xmlMedia 判断已声明媒体类型是否为XML，不按文件扩展名猜测输入内容
// 入参: media 无参数媒体类型
// 返回: bool 是否应进入XML词元处理
func xmlMedia(media string) bool {
	media = strings.ToLower(media)
	return strings.HasSuffix(media, "+xml") || media == "application/xml" || media == "text/xml"
}

// deliverXML 在调用线程交付词元并执行全包累计元素及命名空间快照预算
// 入参: part 逻辑部件信息，尚未完成时Size为负一, event 独立词元
// 返回: error 预算、回调或取消错误
func (p *streamPackage) deliverXML(part PartInfo, event StreamXMLToken) error {
	if err := checkContext(p.context); err != nil {
		return err
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
	if p.options.OnXML != nil {
		if err := p.options.OnXML(p.context, part, event); err != nil {
			return err
		}
	}
	return checkContext(p.context)
}

// drainXML 处理当前分片可完成的词元，停在需要新分片或逻辑XML最终结果的明确边界
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
			return event.err
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

// advanceXML 保持跨分片解析状态，乱序分片等待缺口补齐；晚到语义选择回放前缀但不重复交付词元
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
	if !metadata && p.options.OnXML == nil || !xmlMedia(media) || part.xmlDone || part.xmlDeferred {
		return nil
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
			return nil
		}
		part.xml = newStreamXMLParser(p.options.Limits, p.context)
		part.xmlMetadata = metadata
		p.xmlActive++
		if err := p.drainXML(part, media); err != nil {
			return err
		}
	}
	if err := p.input.flush(); err != nil {
		return err
	}
	for !part.xmlDone && part.entries[part.xmlNext] != nil {
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
}

// finishXML 对延迟部件完整解析，已交付前缀只做重新校验，不重复调用词元回调
// 入参: r 已完成物理校验的最终阅读器
// 返回: error XML、输入、预算、回调或取消错误
func (p *streamPackage) finishXML(r *Reader) error {
	p.closeXML()
	if p.options.OnXML == nil && p.options.OnPage == nil {
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
	for _, info := range parts {
		metadata := p.selectedDiscard(info.Name, info.ContentType) || p.selectedLayout(info.Name, info.ContentType) || p.selectedRelationships(info.Name, info.ContentType) || p.selectedPage(info.Name, info.ContentType)
		if !xmlMedia(info.ContentType) || p.options.OnXML == nil && !metadata {
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
			event := streamXMLToken(token, node, depth, start, end)
			if _, begin := token.(xml.StartElement); begin {
				depth++
			} else if _, end := token.(xml.EndElement); end {
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
