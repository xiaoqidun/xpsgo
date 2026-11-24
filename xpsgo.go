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

// Package xpsgo 首个原生、全平台、纯 Go 语言高性能 XPS 引擎
package xpsgo

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"runtime"
	"sync"
	"sync/atomic"
	"time"
)

const (
	// FormatUnknown 表示未知文档格式
	FormatUnknown Format = iota
	// FormatXPS 表示XPS 1.0文档格式
	FormatXPS
	// FormatOpenXPS 表示OpenXPS文档格式
	FormatOpenXPS
)

// ErrClosed 表示阅读器已经关闭
var ErrClosed = errors.New("reader is closed")

// ErrInvalid 表示文档结构或内容不符合格式要求
var ErrInvalid = errors.New("invalid document")

// ErrNotFound 表示请求的包内部件不存在
var ErrNotFound = errors.New("part not found")

// ErrUnsupported 表示尚未实现所需的格式能力
var ErrUnsupported = errors.New("unsupported feature")

// ErrLimit 表示处理过程超出配置的资源上限
var ErrLimit = errors.New("resource limit exceeded")

// ErrRestricted 表示字体嵌入许可禁止修改固定文档或其引用资源
var ErrRestricted = errors.New("font embedding restricts editing")

// closedContextDone 为已关闭的共享取消信号Channel
var closedContextDone = makeClosedContextDone()

// Format 表示文档格式
type Format uint8

// Limits 规定读取文档时的资源上限，MaxXMLBindings限制创建及复制命名空间绑定的累计数量
// MaxPackageBytes同时约束全部声明解压量及ZIP中央目录元数据，不限制整个压缩容器长度
type Limits struct {
	MaxPartBytes     int64
	MaxPackageBytes  int64
	MaxMetadataBytes int64
	MaxPartCount     int
	MaxXMLDepth      int
	MaxXMLNodes      int
	MaxXMLBindings   int
	MaxPageCount     int
}

// Reader 持有文档结构和封装资源，支持并发读取
type Reader struct {
	mu        sync.RWMutex
	pkg       *packageReader
	closer    io.Closer
	closed    bool
	format    Format
	limits    Limits
	sequence  string
	documents []Document
	pages     []PageReference
	fixedXML  func(string) (*xmlElement, bool, error)
}

// ReaderOptions 设置打开文档时的读取选项，Limits中的零值字段采用DefaultLimits
type ReaderOptions struct {
	Limits Limits
}

// PartError 记录发生错误的部件及元素
type PartError struct {
	Part    string
	Element string
	Err     error
}

// mergedContext 合并主副取消Context，优先保留主Context的截止时间与键值链，冻结首个取消错误
type mergedContext struct {
	primary   context.Context
	secondary context.Context
	delegate  context.Context
	done      chan struct{}
	once      sync.Once
	err       error
}

// String 返回文档格式的可读名称
// 返回: string 格式名称
func (f Format) String() string {
	switch f {
	case FormatXPS:
		return "xps"
	case FormatOpenXPS:
		return "openxps"
	default:
		return "unknown"
	}
}

// Error 返回包含部件位置的错误信息
// 返回: string 错误信息
func (e *PartError) Error() string {
	if e == nil {
		return "<nil>"
	}
	if e.Element != "" {
		return fmt.Sprintf("%s <%s>: %v", e.Part, e.Element, e.Err)
	}
	return fmt.Sprintf("%s: %v", e.Part, e.Err)
}

// Unwrap 返回原始错误
// 返回: error 原始错误
func (e *PartError) Unwrap() error {
	if e == nil {
		return nil
	}
	return e.Err
}

// DefaultLimits 返回默认资源上限
// 返回: Limits 资源上限
func DefaultLimits() Limits {
	return Limits{MaxPartBytes: 256 << 20, MaxPackageBytes: 1 << 30, MaxMetadataBytes: 16 << 20, MaxPartCount: 100000, MaxXMLDepth: 256, MaxXMLNodes: 2000000, MaxXMLBindings: 2000000, MaxPageCount: 1000000}
}

// DefaultReaderOptions 返回默认阅读器选项
// 返回: ReaderOptions 阅读器选项
func DefaultReaderOptions() ReaderOptions {
	return ReaderOptions{Limits: DefaultLimits()}
}

// Open 打开文档文件，使用完毕后需调用Close
// 入参: ctx 取消Context，nil采用Background, path 文件路径, options 阅读器选项，nil采用默认值
// 返回: *Reader 阅读器实例, error 错误信息
func Open(ctx context.Context, path string, options *ReaderOptions) (*Reader, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	info, err := f.Stat()
	if err != nil {
		f.Close()
		return nil, err
	}
	r, err := NewReader(ctx, f, info.Size(), options)
	if err != nil {
		f.Close()
		return nil, err
	}
	r.closer = f
	return r, nil
}

// OpenBytes 从内存字节切片打开文档，不额外拷贝原始切片，调用方须保证阅读期间切片不变
// 入参: ctx 取消Context，nil采用Background, data 完整文档字节切片, options 阅读器选项，nil采用默认值
// 返回: *Reader 阅读器实例, error 错误信息
func OpenBytes(ctx context.Context, data []byte, options *ReaderOptions) (*Reader, error) {
	return NewReader(ctx, bytes.NewReader(data), int64(len(data)), options)
}

// NewReader 从随机读取器打开文档，不接管输入的关闭责任
// 调用方须保证输入在阅读器使用期间不变；并发读取还要求输入支持并发ReadAt
// 入参: ctx 取消Context，nil采用Background, input 输入读取器, size 输入长度, options 阅读器选项，nil采用默认值
// 返回: *Reader 阅读器实例, error 错误信息
func NewReader(ctx context.Context, input io.ReaderAt, size int64, options *ReaderOptions) (*Reader, error) {
	ctx = normalizeContext(ctx)
	if input == nil || size < 0 {
		return nil, fmt.Errorf("%w: invalid input", ErrInvalid)
	}
	limits := DefaultLimits()
	if options != nil {
		limits = mergeLimits(limits, options.Limits)
	}
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	pkg, err := newPackageReaderWithLimits(ctx, input, size, limits)
	if err != nil {
		return nil, err
	}
	r := &Reader{pkg: pkg, limits: limits}
	if err := r.readSequenceContext(ctx); err != nil {
		return nil, err
	}
	return r, nil
}

// readLock 校验阅读器状态并获取读锁，成功返回后调用方须立即通过Defer释放读锁
// 返回: error 空、已关闭或未初始化错误
func (r *Reader) readLock() error {
	if r == nil {
		return fmt.Errorf("%w: nil reader", ErrInvalid)
	}
	r.mu.RLock()
	if r.closed {
		r.mu.RUnlock()
		return ErrClosed
	}
	if r.pkg == nil {
		r.mu.RUnlock()
		return fmt.Errorf("%w: uninitialized reader", ErrInvalid)
	}
	return nil
}

// Close 关闭阅读器，等待正在进行的读取结束后释放自有文件
// 返回: error 错误信息
func (r *Reader) Close() error {
	if r == nil {
		return nil
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.closed {
		return nil
	}
	r.closed = true
	r.pkg = nil
	r.fixedXML = nil
	closer := r.closer
	r.closer = nil
	if closer != nil {
		return closer.Close()
	}
	return nil
}

// Format 返回文档格式
// 返回: Format 文档格式
func (r *Reader) Format() Format {
	if r == nil {
		return FormatUnknown
	}
	return r.format
}

// DocumentCount 返回文档数量
// 返回: int 文档数量
func (r *Reader) DocumentCount() int {
	if r == nil {
		return 0
	}
	return len(r.documents)
}

// PageCount 返回文档序列中的页面总数
// 返回: int 页面总数
func (r *Reader) PageCount() int {
	if r == nil {
		return 0
	}
	return len(r.pages)
}

// Document 返回指定文档的索引信息副本
// 入参: docIndex 从零开始的文档序号
// 返回: Document 文档索引, error 错误信息
func (r *Reader) Document(docIndex int) (Document, error) {
	if err := r.readLock(); err != nil {
		return Document{}, err
	}
	defer r.mu.RUnlock()
	if docIndex < 0 || docIndex >= len(r.documents) {
		return Document{}, fmt.Errorf("%w: document index out of range: %d", ErrInvalid, docIndex)
	}
	doc := r.documents[docIndex]
	doc.Pages = append([]PageReference(nil), doc.Pages...)
	for i := range doc.Pages {
		doc.Pages[i].LinkTargets = append([]string(nil), doc.Pages[i].LinkTargets...)
	}
	return doc, nil
}

// ReadPart 返回部件数据，不解析或获取外部资源
// 入参: ctx 取消Context，nil采用Background, name 部件名称
// 返回: []byte 部件数据, error 错误信息
func (r *Reader) ReadPart(ctx context.Context, name string) ([]byte, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return r.pkg.readPartContext(ctx, name)
}

// Relationships 返回指定部件的关系，包级关系使用斜线作为来源
// 入参: ctx 取消Context，nil采用Background, source 来源部件
// 返回: []Relationship 关系列表, error 错误信息
func (r *Reader) Relationships(ctx context.Context, source string) ([]Relationship, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return r.pkg.relationshipsContext(ctx, source)
}

// mergeLimits 以非零字段覆盖现有资源上限，不改变调用方数据
// 入参: base 原始上限, override 待覆盖字段
// 返回: Limits 合并后的上限
func mergeLimits(base, override Limits) Limits {
	if override.MaxPartBytes != 0 {
		base.MaxPartBytes = override.MaxPartBytes
	}
	if override.MaxPackageBytes != 0 {
		base.MaxPackageBytes = override.MaxPackageBytes
	}
	if override.MaxMetadataBytes != 0 {
		base.MaxMetadataBytes = override.MaxMetadataBytes
	}
	if override.MaxPartCount != 0 {
		base.MaxPartCount = override.MaxPartCount
	}
	if override.MaxXMLDepth != 0 {
		base.MaxXMLDepth = override.MaxXMLDepth
	}
	if override.MaxXMLNodes != 0 {
		base.MaxXMLNodes = override.MaxXMLNodes
	}
	if override.MaxXMLBindings != 0 {
		base.MaxXMLBindings = override.MaxXMLBindings
	}
	if override.MaxPageCount != 0 {
		base.MaxPageCount = override.MaxPageCount
	}
	return base
}

// validateLimits 检查资源上限均为正值，供读取和编码路径使用
// 入参: limits 已合并默认值的资源上限
// 返回: error 非法上限错误
func validateLimits(limits Limits) error {
	if limits.MaxPartBytes < 1 || limits.MaxPackageBytes < 1 || limits.MaxMetadataBytes < 1 || limits.MaxPartCount < 1 || limits.MaxXMLDepth < 1 || limits.MaxXMLNodes < 1 || limits.MaxXMLBindings < 1 || limits.MaxPageCount < 1 {
		return fmt.Errorf("%w: limits must be positive", ErrInvalid)
	}
	return nil
}

// Deadline 返回主副Context中更早的截止时间
// 返回: time.Time 截止时间, bool 是否存在截止时间
func (m *mergedContext) Deadline() (time.Time, bool) {
	pDeadline, pOK := m.primary.Deadline()
	sDeadline, sOK := m.secondary.Deadline()
	if !pOK {
		return sDeadline, sOK
	}
	if !sOK || !sDeadline.Before(pDeadline) {
		return pDeadline, true
	}
	return sDeadline, true
}

// Done 返回任一Context取消时关闭的Channel
// 返回: <-chan struct{} 取消信号Channel
func (m *mergedContext) Done() <-chan struct{} {
	if m.delegate != nil {
		return m.delegate.Done()
	}
	return m.done
}

// Err 在Done关闭前恒返回nil，关闭后恒返回首次冻结的取消错误
// 返回: error 取消错误
func (m *mergedContext) Err() error {
	if m.delegate != nil {
		return m.delegate.Err()
	}
	select {
	case <-m.done:
		return m.err
	default:
		return nil
	}
}

// Value 优先从主Context读取键值，未命中时回落副Context
// 入参: key 查询键
// 返回: any 对应键值
func (m *mergedContext) Value(key any) any {
	if value := m.primary.Value(key); value != nil {
		return value
	}
	return m.secondary.Value(key)
}

// makeClosedContextDone 创建并立即关闭共享取消信号Channel
// 返回: chan struct{} 已关闭的Channel
func makeClosedContextDone() chan struct{} {
	ch := make(chan struct{})
	close(ch)
	return ch
}

// checkContext 检查可选取消Context，不创建额外执行任务
// 入参: ctx 可选Context
// 返回: error 取消错误
func checkContext(ctx context.Context) error {
	if ctx != nil {
		return ctx.Err()
	}
	return nil
}

// normalizeContext 将nil Context回落为context.Background
// 入参: ctx 可选Context
// 返回: context.Context 非空Context
func normalizeContext(ctx context.Context) context.Context {
	if ctx == nil {
		return context.Background()
	}
	return ctx
}

// mergeContext 合并优先与辅助Context，任一取消均立即冻结首个错误并保留双侧Value链
// 入参: primary 优先Context, secondary 辅助Context
// 返回: context.Context 合并后的非空Context, func() 释放关联的清理函数
func mergeContext(primary, secondary context.Context) (context.Context, func()) {
	if primary == nil {
		return normalizeContext(secondary), func() {}
	}
	if secondary == nil {
		return primary, func() {}
	}
	if err := primary.Err(); err != nil {
		return &mergedContext{primary: primary, secondary: secondary, done: closedContextDone, err: err}, func() {}
	}
	if err := secondary.Err(); err != nil {
		return &mergedContext{primary: primary, secondary: secondary, done: closedContextDone, err: err}, func() {}
	}
	if secondary.Done() == nil {
		return &mergedContext{primary: primary, secondary: secondary, delegate: primary}, func() {}
	}
	if primary.Done() == nil {
		return &mergedContext{primary: primary, secondary: secondary, delegate: secondary}, func() {}
	}
	merged := &mergedContext{primary: primary, secondary: secondary, done: make(chan struct{})}
	finish := func(source context.Context) {
		merged.once.Do(func() {
			err := source.Err()
			if err == nil {
				err = primary.Err()
			}
			if err == nil {
				err = secondary.Err()
			}
			merged.err = err
			close(merged.done)
		})
	}
	stopPrimary := context.AfterFunc(primary, func() { finish(primary) })
	stopSecondary := context.AfterFunc(secondary, func() { finish(secondary) })
	return merged, func() {
		stopPrimary()
		stopSecondary()
	}
}

// resolveXPSWorkers 根据请求并发上限与任务数确定有效工作数，单任务或单核直接返回1
// 入参: requested 请求并发上限，零值取当前CPU核数, tasks 待执行任务数
// 返回: int 最终并发工作数
func resolveXPSWorkers(requested, tasks int) int {
	if tasks <= 1 || requested == 1 {
		return 1
	}
	workers := requested
	if workers <= 0 {
		workers = runtime.GOMAXPROCS(0)
	}
	if workers < 1 {
		return 1
	}
	return min(tasks, workers)
}

// budgetXPSWorkers 根据可用内存或像素预算与单个工作区开销收缩并发度，最小保底为1
// 入参: workers 目标并发数, available 可用预算额度, perWorker 单个并发工作区开销
// 返回: int 预算安全范围内的并发数
func budgetXPSWorkers(workers int, available, perWorker uint64) int {
	if workers <= 1 {
		return 1
	}
	if perWorker == 0 {
		return workers
	}
	allowed := available / perWorker
	if allowed <= 1 {
		return 1
	}
	if allowed < uint64(workers) {
		return int(allowed)
	}
	return workers
}

// runXPSWorkerSlots 使用有界并发池执行独立任务并分配独占槽位，子Goroutine发生panic时汇总后重抛
// 入参: ctx 非空取消Context, workers 最大并发数, tasks 任务总数, fn 接收Context、槽位号与任务号的回调
// 返回: error 首个真实错误或Context取消错误
func runXPSWorkerSlots(ctx context.Context, workers, tasks int, fn func(context.Context, int, int) error) error {
	if fn == nil {
		return fmt.Errorf("%w: nil worker function", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	if tasks <= 0 {
		return nil
	}
	if workers <= 1 || tasks <= 1 {
		for task := range tasks {
			if err := checkContext(ctx); err != nil {
				return err
			}
			if err := fn(ctx, 0, task); err != nil {
				return err
			}
		}
		return checkContext(ctx)
	}
	workers = min(workers, tasks)
	runCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	var next atomic.Int64
	var errMu sync.Mutex
	var firstErr error
	firstTask := tasks
	hasRealErr := false
	var panicVal any
	hasPanic := false
	panicTask := tasks
	recordErr := func(task int, taskErr error) {
		if taskErr == nil {
			return
		}
		isCancelErr := errors.Is(taskErr, context.Canceled) || errors.Is(taskErr, context.DeadlineExceeded)
		errMu.Lock()
		if firstErr == nil || !isCancelErr && !hasRealErr || (!isCancelErr || !hasRealErr) && task < firstTask {
			firstErr = taskErr
			firstTask = task
			hasRealErr = !isCancelErr
		}
		errMu.Unlock()
		cancel()
	}
	recordPanic := func(task int, recovered any) {
		errMu.Lock()
		if !hasPanic || task < panicTask {
			hasPanic = true
			panicTask = task
			panicVal = recovered
		}
		errMu.Unlock()
		cancel()
	}
	runSlot := func(slot int) {
		task := -1
		completed := false
		defer func() {
			if !completed {
				recordPanic(task, recover())
			}
		}()
		for runCtx.Err() == nil {
			idx := int(next.Add(1) - 1)
			if idx >= tasks {
				break
			}
			task = idx
			if taskErr := fn(runCtx, slot, idx); taskErr != nil {
				recordErr(idx, taskErr)
				break
			}
		}
		completed = true
	}
	var wg sync.WaitGroup
	wg.Add(workers - 1)
	for slot := 1; slot < workers; slot++ {
		go func() {
			defer wg.Done()
			runSlot(slot)
		}()
	}
	runSlot(0)
	wg.Wait()
	if hasPanic {
		panic(panicVal)
	}
	if firstErr != nil {
		return firstErr
	}
	return checkContext(ctx)
}
