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
	"context"
	"encoding/xml"
	"errors"
	"fmt"
	"image"
	"io"
	"io/fs"
	"maps"
	"slices"
	"strings"
)

// StreamPage 表示前向流读取中资源已就绪的临时页面视图，Index为零基全局页号，DocumentPart为所属文档URI
// Page、Walk、Font、Image、PrintTicketHierarchy、PrintSettings、PrintColorPlan、Render与RenderDevice仅在OnPage回调期间可用
// 回调结束后视图自动关闭，返回的页面数据、资源及图像独立于视图；Read成功前均为临时结果
type StreamPage struct {
	Index        int
	DocumentPart string
	Reference    PageReference
	view         *streamPageView
}

// streamPageView 保存临时页面视图的只读阅读器、页号、文档位置与流取消Context
type streamPageView struct {
	reader        *Reader
	index         int
	documentIndex int
	pageIndex     int
	context       context.Context
}

// streamPartialPage 保存跨分片解析的页面标记与已校验根内容
type streamPartialPage struct {
	root     *xmlElement
	stack    []*xmlElement
	names    map[string]bool
	children int
	closed   bool
	deferred bool
}

// streamPartialLayout 保存固定序列或文档的已闭合引用，只保留当前直接子树及必要的索引状态
type streamPartialLayout struct {
	root       *xmlElement
	stack      []*xmlElement
	documents  []string
	pages      []PageReference
	references map[string]bool
	names      map[string]bool
	closed     bool
	deferred   bool
}

// streamPartialRelationships 保存已闭合的OPC关系和部件内ID，不把关系前缀登记为完整部件
type streamPartialRelationships struct {
	root     *xmlElement
	stack    []*xmlElement
	items    []Relationship
	ids      map[string]bool
	discards map[string]int
	fixed    bool
	closed   bool
	deferred bool
}

// DocumentIndex 返回当前页面所属文档在固定文档序列中的零基序号，无效或未初始化返回-1
// 返回: int 零基文档序号
func (p *StreamPage) DocumentIndex() int {
	if p == nil || p.view == nil {
		return -1
	}
	return p.view.documentIndex
}

// PageIndex 返回当前页面在所属文档中的零基页序号，无效或未初始化返回-1
// 返回: int 零基文档内页序号
func (p *StreamPage) PageIndex() int {
	if p == nil || p.view == nil {
		return -1
	}
	return p.view.pageIndex
}

// Part 返回当前页面的规范部件URI，接收者为nil返回空字符串
// 返回: string 页面部件URI
func (p *StreamPage) Part() string {
	if p == nil {
		return ""
	}
	return p.Reference.Part
}

// lockReader 校验临时页面视图并获取读锁与合并后的Context，成功时调用方须立即通过Defer执行清理函数
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Reader 有效只读阅读器, context.Context 合并后的Context, func() 释放清理函数, error 关闭错误
func (p *StreamPage) lockReader(ctx context.Context) (*Reader, context.Context, func(), error) {
	if p == nil || p.view == nil || p.view.reader == nil {
		return nil, nil, nil, ErrClosed
	}
	r := p.view.reader
	r.mu.RLock()
	if r.closed {
		r.mu.RUnlock()
		return nil, nil, nil, ErrClosed
	}
	merged, stop := mergeContext(ctx, p.view.context)
	return r, merged, func() {
		stop()
		r.mu.RUnlock()
	}, nil
}

// Page 解析当前临时页面及资源绑定，不访问未到达部件或外部地址
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Page 独立页面内容, error 解析、资源、预算、取消或关闭错误
func (p *StreamPage) Page(ctx context.Context) (*Page, error) {
	r, pageCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	if err := checkContext(pageCtx); err != nil {
		return nil, err
	}
	return r.readPageSceneLoaders(p.view.index, false, nil, nil, pageCtx)
}

// PrintTicketHierarchy 按作业、文档及页面顺序读取当前临时页关联的PrintTicket链，省略未关联层级
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: []PrintTicket 独立票据数据, error 关联、读取、资源、取消或关闭错误
func (p *StreamPage) PrintTicketHierarchy(ctx context.Context) ([]PrintTicket, error) {
	r, ticketCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return r.streamPrintTicketHierarchy(ticketCtx, p.view.index, r.limits)
}

// activeReader 校验临时页面视图与底层阅读器尚未关闭，确保回调结束后稳定返回ErrClosed
// 返回: *Reader 有效只读阅读器, error 关闭错误
func (p *StreamPage) activeReader() (*Reader, error) {
	if p == nil || p.view == nil || p.view.reader == nil {
		return nil, ErrClosed
	}
	r := p.view.reader
	r.mu.RLock()
	closed := r.closed
	r.mu.RUnlock()
	if closed {
		return nil, ErrClosed
	}
	return r, nil
}

// Walk 在前向读取回调期间按严格绘制顺序遍历当前临时页面场景
// 回调期间不持有阅读器读锁，允许回调安全调用Font或Image读取已到达资源；回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 页面读取、参数、资源上限、取消、关闭或回调返回的错误
func (p *StreamPage) Walk(ctx context.Context, visitor *SceneVisitor, options *WalkOptions) error {
	r, err := p.activeReader()
	if err != nil {
		return err
	}
	walkCtx, cleanup := mergeContext(ctx, p.view.context)
	defer cleanup()
	return r.Walk(walkCtx, p.view.index, visitor, options)
}

// Font 在前向读取回调期间读取并解混淆当前临时页引用的已到达字体资源
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, fontURI 相对或包根字体URI，可附#index集合索引
// 返回: *FontResource 独立只读字体资源, error URI、读取、格式、取消或关闭错误
func (p *StreamPage) Font(ctx context.Context, fontURI string) (*FontResource, error) {
	r, err := p.activeReader()
	if err != nil {
		return nil, err
	}
	fontCtx, cleanup := mergeContext(ctx, p.view.context)
	defer cleanup()
	return r.Font(fontCtx, fontURI)
}

// Image 在前向读取回调期间读取当前临时页引用的已到达图像资源，不访问未到达部件
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 图像部件的包根URI, options 图像参数，nil采用默认值
// 返回: *ImageResource 独立图像数据, error 输入、解码、资源、取消或关闭错误
func (p *StreamPage) Image(ctx context.Context, part string, options *ImageOptions) (*ImageResource, error) {
	r, err := p.activeReader()
	if err != nil {
		return nil, err
	}
	imageCtx, cleanup := mergeContext(ctx, p.view.context)
	defer cleanup()
	return r.Image(imageCtx, part, options)
}

// PrintSettings 在回调期间合并基础设置与当前临时页的三级PrintTicket，不修改输入设置
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, defaults 基础设置，nil为空设置, options 输出作用域及资源参数
// 返回: *PrintSettings 独立有效设置, error 票据格式、关联、资源、取消或关闭错误
func (p *StreamPage) PrintSettings(ctx context.Context, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, error) {
	r, settingsCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return r.streamReadPrintSettings(settingsCtx, p.view.index, defaults, options)
}

// PrintColorPlan 在回调期间解析当前临时页生效的颜色管理计划，未声明时返回nil
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, defaults 基础设置，nil为空设置, options 票据解析预算
// 返回: *PrintColorPlan 独立颜色计划，未声明为nil, error 结构、引用、资源、取消或关闭错误
func (p *StreamPage) PrintColorPlan(ctx context.Context, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintColorPlan, error) {
	r, colorCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	settings, err := r.streamReadPrintSettings(colorCtx, p.view.index, defaults, options)
	if err != nil {
		return nil, err
	}
	_, result, err := printColorPlanSettings(colorCtx, settings, options)
	return result, err
}

// Render 使用文档引擎现有渲染器绘制当前页面，不重新封装ZIP或另行解释页面语义
// 未指定绘制Context时沿用前向读取Context，同时响应两者的取消信号，不修改调用方参数
// 入参: ctx 取消Context，nil沿用流读取Context, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 独立页面图像, error 绘制、资源、预算、取消或关闭错误
func (p *StreamPage) Render(ctx context.Context, options *RenderOptions) (*image.NRGBA, error) {
	r, err := p.activeReader()
	if err != nil {
		return nil, err
	}
	renderCtx, cleanup := mergeContext(ctx, p.view.context)
	defer cleanup()
	return r.Render(renderCtx, p.view.index, options)
}

// RenderDevice 在前向读取回调中绘制目标ICC分量，缺省沿用流读取Context并兼顾流取消
// 入参: ctx 取消Context，nil沿用流读取Context, device 必需目标配置, options 绘制参数
// 返回: *DeviceImage 独立设备图像，失败为nil, error 关闭、资源、转换或取消错误
func (p *StreamPage) RenderDevice(ctx context.Context, device *DeviceColorTarget, options *RenderOptions) (*DeviceImage, error) {
	r, err := p.activeReader()
	if err != nil {
		return nil, err
	}
	renderCtx, cleanup := mergeContext(ctx, p.view.context)
	defer cleanup()
	return r.RenderDevice(renderCtx, p.view.index, device, options)
}

// registerPagePart 将完整部件接入前向读取后端，原始部件保存物理范围并释放已结束页面的增量树
// 入参: part 完整逻辑部件
func (p *streamPackage) registerPagePart(part *streamPart) {
	if p.options.OnPage == nil {
		return
	}
	p.preparePagePackage()
	key := strings.ToLower(part.name)
	if _, present := p.pagePkg.parts[key]; present {
		return
	}
	p.pagePkg.names[key] = part.name
	for index := 0; index <= part.last; index++ {
		p.pagePkg.parts[key] = append(p.pagePkg.parts[key], &zip.File{FileHeader: part.entries[index].header})
	}
	part.page = nil
}

// preparePagePackage 建立临时完整部件后端，并通过独立关系快照支持未结束的元数据，不伪造完整部件
func (p *streamPackage) preparePagePackage() {
	if p.options.OnPage != nil && p.pagePkg == nil {
		p.pagePkg = &packageReader{limits: p.options.Limits, parts: make(map[string][]*zip.File), names: make(map[string]string), defaults: p.types.defaults, overrides: p.types.overrides, cache: p.cache}
		p.pagePkg.open = func(key string) (io.ReadCloser, error) {
			part := p.parts[key]
			if part == nil || part.last < 0 || len(part.entries) != part.last+1 {
				return nil, fmt.Errorf("%w: streamed part %s: %w", ErrNotFound, key, fs.ErrNotExist)
			}
			return p.partReader(part), nil
		}
		p.pagePkg.missing = func(key string) {
			if p.pageWait != nil {
				p.pageWait[key] = true
			}
		}
		p.pagePkg.relation = p.relationshipSnapshot
	}
}

// emitPages 在元数据或页面依赖到达后按顺序提供可解析页面，未确认的缺失及关系错误留待最终校验
// 入参: name 到达部件名
// 返回: error 预算、输入、取消、已确定结构或调用方回调错误
func (p *streamPackage) emitPages(name string) error {
	if p.options.OnPage == nil || p.pagePkg == nil {
		return nil
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	if err := p.advanceRelationshipPart("/_rels/.rels"); err != nil {
		return err
	}
	if err := p.activateStreamIndex(); err != nil {
		return err
	}
	if p.index == nil {
		return nil
	}
	if err := p.updateDiscard(p.index); err != nil {
		return err
	}
	if p.discard != nil && p.discard.checked && !p.discard.loaded {
		if part := p.parts[strings.ToLower(p.discard.target)]; part != nil {
			if err := p.advanceMetadataPart(part.name, "discard-control"); err != nil {
				return err
			}
		}
	}
	if err := p.advanceLayoutIndex(); err != nil {
		return err
	}
	if err := p.advancePageMarkup(); err != nil {
		return err
	}
	return p.emitReadyPages(name)
}

// emitReadyPages 按当前索引交付依赖完整的页面，不在词元回调期间推进其他XML解析状态
// 入参: name 当前到达或已消费的部件名
// 返回: error 页面、资源、预算或回调错误
func (p *streamPackage) emitReadyPages(name string) error {
	if err := p.releaseProcessed(); err != nil {
		return err
	}
	if p.pageHold || len(p.pageWait) != 0 && !p.pageWait[strings.ToLower(name)] {
		return nil
	}
	for p.pages < len(p.index.pages) {
		if err := checkContext(p.context); err != nil {
			return err
		}
		key := strings.ToLower(p.index.pages[p.pages].Part)
		if _, exists := p.pagePkg.parts[key]; !exists {
			part := p.parts[key]
			if part == nil || part.page == nil || !part.page.closed || part.page.deferred {
				return nil
			}
		}
		p.pageWait = make(map[string]bool)
		if _, err := p.index.Page(p.context, p.pages); err != nil {
			if errors.Is(err, ErrInvalid) || errors.Is(err, ErrUnsupported) || errors.Is(err, fs.ErrNotExist) {
				p.pageHold = len(p.pageWait) == 0
				return nil
			}
			return err
		}
		p.pageWait = nil
		waits, hold, err := p.streamPageTicketsReady(p.pages)
		if err != nil {
			return err
		}
		if hold {
			p.pageHold = true
			return nil
		}
		if len(waits) != 0 {
			p.pageWait = make(map[string]bool, len(waits))
			for _, wait := range waits {
				p.pageWait[wait] = true
			}
			return nil
		}
		if err := p.notifyPage(p.index, p.pages); err != nil {
			return err
		}
		p.pages++
	}
	return nil
}

// notifyPage 创建仅供本次回调使用的页面视图，关闭时等待正在进行的读取和渲染
// 入参: source 当前文档索引, index 页面序号
// 返回: error 回调或取消错误
func (p *streamPackage) notifyPage(source *Reader, index int) error {
	if err := p.startDiscard(source, index); err != nil {
		return err
	}
	view := &Reader{pkg: source.pkg, limits: source.limits, format: source.format, sequence: source.sequence, documents: source.documents, pages: source.pages, fixedXML: source.fixedXML}
	defer view.Close()
	reference := source.pages[index]
	reference.LinkTargets = append([]string(nil), reference.LinkTargets...)
	docPart, docIndex, pageIndex := source.pageLocation(index)
	if docPart == "" {
		return fmt.Errorf("%w: streamed page document", ErrInvalid)
	}
	tickets, err := source.pageTicketTargets(p.context, index)
	if err != nil {
		return err
	}
	page := &StreamPage{Index: index, DocumentPart: docPart, Reference: reference, view: &streamPageView{reader: view, index: index, documentIndex: docIndex, pageIndex: pageIndex, context: p.context}}
	if err := p.options.OnPage(p.context, page); err != nil {
		return err
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	view.Close()
	p.pageTickets = append(p.pageTickets, tickets)
	return p.releaseProcessed()
}

// finishPages 用最终索引重新校验已发出页面，再提供尚未就绪的页面，不重复回调临时结果
// 入参: r 已完成物理校验的最终阅读器
// 返回: error 页面、资源、回调、预算或取消错误
func (p *streamPackage) finishPages(r *Reader) error {
	if p.options.OnPage == nil {
		return nil
	}
	if p.pages > len(r.pages) {
		return fmt.Errorf("%w: streamed page index conflict", ErrInvalid)
	}
	if p.pages != 0 && (p.index == nil || p.index.format != r.format || p.index.sequence != r.sequence) {
		return fmt.Errorf("%w: streamed fixed representation conflict", ErrInvalid)
	}
	if err := p.updateDiscard(r); err != nil {
		return err
	}
	if err := p.releaseProcessed(); err != nil {
		return err
	}
	for index := range r.pages {
		if err := checkContext(p.context); err != nil {
			return err
		}
		if _, err := r.Page(p.context, index); err != nil {
			return err
		}
		tickets, err := r.pageTicketTargets(p.context, index)
		if err != nil {
			return err
		}
		if index < p.pages {
			if p.index == nil || index >= len(p.index.pages) || p.index.pages[index].Part != r.pages[index].Part || p.index.pages[index].Width != r.pages[index].Width || p.index.pages[index].Height != r.pages[index].Height || !slices.Equal(p.index.pages[index].LinkTargets, r.pages[index].LinkTargets) {
				return fmt.Errorf("%w: streamed page reference conflict", ErrInvalid)
			}
			if index >= len(p.pageTickets) || !slices.Equal(p.pageTickets[index], tickets) {
				return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
			}
			continue
		}
		if err := p.notifyPage(r, index); err != nil {
			return err
		}
		p.pages++
	}
	return p.releaseProcessed()
}

// streamPotentialPrintTicketMedia 判断内容类型声明在当前方言下是否可能表示打印票据部件
// 入参: format 文档方言, media 已解析的媒体类型字符串
// 返回: bool 是否可能用于打印票据
func streamPotentialPrintTicketMedia(format Format, media string) bool {
	base, _, _ := strings.Cut(media, ";")
	base = strings.TrimSpace(base)
	if base == "" {
		return false
	}
	if strings.EqualFold(base, printTicketType) {
		return true
	}
	if format != FormatOpenXPS || standardResourceMedia(base) != 0 {
		return false
	}
	for _, known := range []string{
		fixedContentType("fixeddocumentsequence"),
		fixedContentType("fixeddocument"),
		fixedContentType("fixedpage"),
		fixedContentType("documentstructure"),
		fixedContentType("storyfragments"),
		fixedContentType("discard-control"),
		fixedContentType("signaturedefinitions"),
		opcRelsType,
		opcCoreType,
		opcSignatureType,
		opcSignatureOriginType,
		opcCertificateType,
		"application/vnd.ms-package.3dmanufacturing-3dmodel+xml",
		"model/x3d+xml",
		"model/x3d+binary",
	} {
		if strings.EqualFold(base, known) {
			return false
		}
	}
	return true
}

// mayHavePrintTicket 检查内容类型流是否声明了任何可能作为打印票据的媒体类型
// 返回: bool 包内是否可能存在打印票据
func (p *streamPackage) mayHavePrintTicket() bool {
	if p.types == nil || p.index == nil {
		return false
	}
	for _, media := range p.types.defaults {
		if streamPotentialPrintTicketMedia(p.index.format, media) {
			return true
		}
	}
	for _, media := range p.types.overrides {
		if streamPotentialPrintTicketMedia(p.index.format, media) {
			return true
		}
	}
	return false
}

// pageTicketTargets 按作业、文档及页面顺序提取规范化打印票据目标URI切片，用于流式交付一致性复核
// 入参: ctx 取消Context, index 全局页序号
// 返回: []string 三级票据目标小写URI切片, error 关系、取消或预算错误
func (r *Reader) pageTicketTargets(ctx context.Context, index int) ([]string, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.pages) {
		return nil, fmt.Errorf("%w: page index out of range: %d", ErrInvalid, index)
	}
	pagePart := r.pages[index].Part
	docPart, _, _ := r.pageLocation(index)
	if docPart == "" {
		return nil, fmt.Errorf("%w: streamed page document", ErrInvalid)
	}
	result := make([]string, 3)
	for level, source := range [3]string{r.sequence, docPart, pagePart} {
		relations, err := r.pkg.relationshipsContext(ctx, source)
		if err != nil {
			return nil, err
		}
		target, err := printTicketTarget(source, relations, r.format)
		if err != nil {
			return nil, err
		}
		if target != "" {
			result[level] = strings.ToLower(target)
		}
	}
	return result, nil
}

// streamRelsPossible 检查内容类型流是否允许指定关系部件在包中出现
// 入参: relsKey 关系部件的小写规范URI
// 返回: bool 该关系部件是否可能存在于当前包
func (p *streamPackage) streamRelsPossible(relsKey string) bool {
	if p.types == nil {
		return false
	}
	if p.types.overrides[relsKey] != "" {
		return true
	}
	return p.types.defaults["rels"] != ""
}

// streamPageTicketsReady 检查页面三级关系及打印票据部件是否均已就绪，避免交错未闭合或晚到关系静默丢失票据
// 入参: index 待交付页面序号
// 返回: []string 等待到达的部件键列表, bool 是否遇到确定错误需暂缓至最终校验, error 预算或取消错误
func (p *streamPackage) streamPageTicketsReady(index int) ([]string, bool, error) {
	pagePart := p.index.pages[index].Part
	docPart, _, _ := p.index.pageLocation(index)
	if docPart == "" {
		return nil, false, nil
	}
	mayTicket := p.mayHavePrintTicket()
	var waits []string
	for _, source := range []string{p.index.sequence, docPart, pagePart} {
		if err := checkContext(p.context); err != nil {
			return nil, false, err
		}
		relsKey := strings.ToLower(createdRelationshipPart(source))
		if _, complete := p.pagePkg.parts[relsKey]; complete {
			relations, err := p.index.pkg.relationshipsContext(p.context, source)
			if err != nil {
				if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
					return nil, false, err
				}
				return nil, true, nil
			}
			target, err := printTicketTarget(source, relations, p.index.format)
			if err != nil {
				return nil, true, nil
			}
			if target != "" {
				targetKey := strings.ToLower(target)
				if _, exists := p.pagePkg.parts[targetKey]; !exists {
					waits = append(waits, targetKey)
				}
			}
			continue
		}
		if relsPart := p.parts[relsKey]; relsPart != nil {
			if relsPart.relations == nil || relsPart.relations.deferred {
				if mayTicket {
					waits = append(waits, relsKey)
				}
				continue
			}
			target, err := printTicketTarget(source, relsPart.relations.items, p.index.format)
			if err != nil {
				return nil, true, nil
			}
			if target != "" {
				targetKey := strings.ToLower(target)
				if _, exists := p.pagePkg.parts[targetKey]; !exists {
					waits = append(waits, targetKey)
				}
			} else if !relsPart.relations.closed && mayTicket {
				waits = append(waits, relsKey)
			}
			continue
		}
		if mayTicket && p.streamRelsPossible(relsKey) {
			waits = append(waits, relsKey)
		}
	}
	return waits, false, nil
}

// streamPrintTicketHierarchy 在流式视图读锁内按作业、文档及页面顺序读取已关联票据
// 入参: ctx 取消Context, index 页面序号, limits 载荷预算
// 返回: []PrintTicket 独立票据链, error 状态、关联、读取、资源或取消错误
func (r *Reader) streamPrintTicketHierarchy(ctx context.Context, index int, limits Limits) ([]PrintTicket, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.pages) {
		return nil, fmt.Errorf("%w: page index out of range: %d", ErrInvalid, index)
	}
	page := r.pages[index].Part
	document, _, _ := r.pageLocation(index)
	if document == "" {
		return nil, fmt.Errorf("%w: streamed page document", ErrInvalid)
	}
	sources := [3]struct {
		part  string
		scope PrintScope
	}{
		{r.sequence, PrintScopeJob},
		{document, PrintScopeDocument},
		{page, PrintScopePage},
	}
	var result []PrintTicket
	remaining := min(r.limits.MaxPackageBytes, r.limits.MaxMetadataBytes, limits.MaxPackageBytes, limits.MaxMetadataBytes)
	for _, source := range sources {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		canonical, err := opcPartName(source.part)
		if err != nil {
			return nil, err
		}
		relations, err := r.pkg.relationships(canonical)
		if err != nil {
			return nil, err
		}
		part, err := printTicketTarget(canonical, relations, r.format)
		if err != nil {
			return nil, err
		}
		if part == "" {
			continue
		}
		typeName, err := r.pkg.contentType(part)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		sourceName := r.pkg.names[strings.ToLower(canonical)]
		if sourceName == "" {
			sourceName = canonical
		}
		partName := r.pkg.names[strings.ToLower(part)]
		if partName == "" {
			partName = part
		}
		ticket := PrintTicket{Source: sourceName, Part: partName, Scope: source.scope, ContentType: typeName}
		if err := r.readPrintTicketData(&ticket, min(remaining, r.limits.MaxPartBytes, limits.MaxPartBytes), ctx); err != nil {
			return nil, err
		}
		remaining -= int64(len(ticket.Data))
		result = append(result, ticket)
	}
	return result, nil
}

// streamReadPrintSettings 在流式视图读锁内合并基础设置与三级PrintTicket，兼容半完成布局部件
// 入参: ctx 取消Context, index 页面序号, defaults 基础设置, options 输出过滤及资源参数
// 返回: *PrintSettings 独立合并设置, error 状态、读取、合并或取消错误
func (r *Reader) streamReadPrintSettings(ctx context.Context, index int, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	outputScope := configuration.Scope
	configuration.Scope = PrintScopeUnknown
	empty := &PrintSettings{Version: 1}
	if defaults == nil {
		defaults = empty
	}
	result, err := MergePrintSettings(configuration.context, empty, defaults, &configuration.PrintSettingsOptions)
	if err != nil {
		return nil, err
	}
	tickets, err := r.streamPrintTicketHierarchy(configuration.context, index, configuration.Limits)
	if err != nil {
		return nil, err
	}
	for _, ticket := range tickets {
		local := configuration.PrintSettingsOptions
		local.Scope = ticket.Scope
		settings, err := ticket.Settings(configuration.context, &local)
		if err != nil {
			return nil, &PartError{Part: ticket.Part, Err: err}
		}
		result, err = MergePrintSettings(configuration.context, result, settings, &configuration.PrintSettingsOptions)
		if err != nil {
			return nil, &PartError{Part: ticket.Part, Err: err}
		}
	}
	if outputScope != PrintScopeUnknown {
		configuration.Scope = outputScope
		return MergePrintSettings(configuration.context, result, empty, &configuration.PrintSettingsOptions)
	}
	return result, checkContext(configuration.context)
}

// selectedPage 对索引中的未完成页面启用增量处理，完整页面沿用现有读取路径
// 入参: name 部件URI, media 声明类型
// 返回: bool 是否为当前索引页面
func (p *streamPackage) selectedPage(name, media string) bool {
	key := strings.ToLower(name)
	if p.options.OnPage == nil || p.index == nil || !p.pageNames[key] || !strings.EqualFold(media, fixedContentType("fixedpage")) {
		return false
	}
	part := p.parts[key]
	return part != nil && (part.page != nil || part.last < 0 || len(part.entries) != part.last+1)
}

// consumePageMarkup 保持页面解析状态，按闭合顶层内容共用MCE、结构、名称及绘制属性校验
// 入参: part 所选页面部件, event 独立词元
// 返回: error 页面、属性、名称、资源、回调或取消错误
func (p *streamPackage) consumePageMarkup(part *streamPart, event StreamXMLToken) error {
	if part.page == nil {
		part.page = &streamPartialPage{names: make(map[string]bool)}
	}
	s := part.page
	if s.deferred {
		return nil
	}
	switch token := event.Token.(type) {
	case xml.StartElement:
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: maps.Clone(event.Namespaces)}
		if len(s.stack) == 0 {
			if s.root != nil {
				return fmt.Errorf("%w: multiple streamed page roots", ErrInvalid)
			}
			s.root = node
			if node.Name != (xml.Name{Space: formatNamespace(p.index.format), Local: "FixedPage"}) {
				s.deferred = true
				return nil
			}
			root, err := p.pageFragment(part, nil)
			if err != nil {
				return err
			}
			if _, err := parsePageHeader(root, part.name, p.index.format); err != nil {
				return err
			}
			if err := validateFixedNamesSeen(root, p.index.format, s.names); err != nil {
				return err
			}
		} else {
			parent := s.stack[len(s.stack)-1]
			parent.Children = append(parent.Children, node)
		}
		s.stack = append(s.stack, node)
	case xml.CharData:
		if len(s.stack) == 0 {
			return nil
		}
		if len(s.stack) == 1 {
			if !xmlWhitespace(string(token)) {
				return fmt.Errorf("%w: streamed page root text", ErrInvalid)
			}
			return nil
		}
		node := s.stack[len(s.stack)-1]
		node.text = append(node.text, token...)
	case xml.EndElement:
		if len(s.stack) == 0 {
			return fmt.Errorf("%w: streamed page end", ErrInvalid)
		}
		node := s.stack[len(s.stack)-1]
		node.Text, node.text = string(node.text), nil
		s.stack[len(s.stack)-1] = nil
		s.stack = s.stack[:len(s.stack)-1]
		if len(s.stack) == 1 {
			root, err := p.pageFragment(part, node)
			if err != nil {
				return err
			}
			for _, child := range root.Children {
				if child.Name.Local == "FixedPage.Resources" {
					if s.children != 0 {
						return fmt.Errorf("%w: streamed page resources must precede drawing", ErrInvalid)
					}
				} else if err := validateVisual(child, p.index.format); err != nil {
					return err
				}
				if err := validateFixedNamesSeen(child, p.index.format, s.names); err != nil {
					return err
				}
				s.children++
			}
		} else if len(s.stack) == 0 {
			s.closed = true
			return p.emitReadyPages(part.name)
		}
	}
	return nil
}

// pageFragment 在页面根的原兼容作用域下处理一个闭合子树，不重新处理此前的图形内容
// 入参: part 所选页面, child 闭合子树，nil用于页面头校验
// 返回: *xmlElement 独立过滤片段, error MCE或固定结构错误
func (p *streamPackage) pageFragment(part *streamPart, child *xmlElement) (*xmlElement, error) {
	s := part.page
	fragment := &xmlElement{Name: s.root.Name, Attr: s.root.Attr, Namespaces: s.root.Namespaces}
	if child != nil {
		fragment.Children = []*xmlElement{child}
	}
	namespace := formatNamespace(p.index.format)
	root, err := preprocessXMLContext(fragment, []string{namespace, namespace + "/resourcedictionary-key"}, p.context)
	if err != nil {
		return nil, err
	}
	if err := validateFixedStructure(root, p.index.format); err != nil {
		return nil, err
	}
	return root, nil
}

// closedPageRoot 返回临时页面的只读完整根内容，不宣称原XML或逻辑部件已经结束
// 入参: name 页面URI
// 返回: *xmlElement 原始闭合根, bool 是否具备完整内容, error 恒为nil，满足fixedXML读取回调签名
func (p *streamPackage) closedPageRoot(name string) (*xmlElement, bool, error) {
	part := p.parts[strings.ToLower(name)]
	if part == nil || part.page == nil || !part.page.closed || part.page.deferred {
		return nil, false, nil
	}
	return part.page.root, true, nil
}

// advancePageMarkup 按页面顺序推进已到达标记，根内容或依赖未齐时继续接收，不在回调中驱动XML状态
// 返回: error 页面、XML、预算或回调错误
func (p *streamPackage) advancePageMarkup() error {
	for p.pages < len(p.index.pages) {
		before := p.pages
		name := p.index.pages[p.pages].Part
		if err := p.advanceMetadataPart(name, "fixedpage"); err != nil {
			return err
		}
		if err := p.emitReadyPages(name); err != nil {
			return err
		}
		if before == p.pages {
			break
		}
	}
	return nil
}

// selectedLayout 只解释已确认固定表示及其文档引用，不自动解释未关联的同类型附加部件
// 入参: name 部件名, media 声明媒体类型
// 返回: bool 是否属于当前固定布局索引
func (p *streamPackage) selectedLayout(name, media string) bool {
	if p.options.OnPage == nil || p.index == nil {
		return false
	}
	if strings.EqualFold(name, p.index.sequence) {
		return strings.EqualFold(media, fixedContentType("fixeddocumentsequence"))
	}
	return p.documentKeys[strings.ToLower(name)] && strings.EqualFold(media, fixedContentType("fixeddocument"))
}

// consumeLayout 组装一个已闭合直接子树，共用MCE与固定布局校验，再更新临时索引和就绪页面
// 入参: part 所选序列或文档, event 独立词元
// 返回: error 结构、引用、预算、回调或取消错误
func (p *streamPackage) consumeLayout(part *streamPart, event StreamXMLToken) error {
	if part.layout == nil {
		part.layout = &streamPartialLayout{references: make(map[string]bool), names: make(map[string]bool)}
	}
	s := part.layout
	if s.deferred {
		return nil
	}
	switch token := event.Token.(type) {
	case xml.StartElement:
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: maps.Clone(event.Namespaces)}
		if len(s.stack) == 0 {
			if s.root != nil {
				return fmt.Errorf("%w: multiple streamed layout roots", ErrInvalid)
			}
			s.root = node
			name := "FixedDocument"
			if strings.EqualFold(part.name, p.index.sequence) {
				name = "FixedDocumentSequence"
			}
			if node.Name.Space != formatNamespace(p.index.format) || node.Name.Local != name {
				s.deferred = true
				return nil
			}
			if _, err := p.layoutFragment(part, nil); err != nil {
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
		if len(s.stack) == 1 {
			if !xmlWhitespace(string(token)) {
				return fmt.Errorf("%w: streamed layout root text", ErrInvalid)
			}
			return nil
		}
		node := s.stack[len(s.stack)-1]
		node.text = append(node.text, token...)
	case xml.EndElement:
		if len(s.stack) == 0 {
			return fmt.Errorf("%w: streamed layout end", ErrInvalid)
		}
		node := s.stack[len(s.stack)-1]
		node.Text, node.text = string(node.text), nil
		s.stack[len(s.stack)-1] = nil
		s.stack = s.stack[:len(s.stack)-1]
		if len(s.stack) == 1 {
			root, err := p.layoutFragment(part, node)
			if err != nil {
				return err
			}
			if err := validateFixedNamesSeen(root, p.index.format, s.names); err != nil {
				return &PartError{Part: part.name, Err: err}
			}
			for _, child := range root.Children {
				if err := p.appendLayoutReference(part, child); err != nil {
					return err
				}
			}
		} else if len(s.stack) == 0 {
			if len(s.documents)+len(s.pages) == 0 {
				return &PartError{Part: part.name, Element: s.root.Name.Local, Err: fmt.Errorf("%w: missing streamed layout reference", ErrInvalid)}
			}
			s.closed = true
		} else {
			return nil
		}
		if err := p.applyLayoutIndex(); err != nil {
			return err
		}
		return p.emitReadyPages(part.name)
	}
	return nil
}

// layoutFragment 在原根的MCE作用域下处理已闭合直接子树，根结束前仅暂缓最少引用数量检查
// 入参: part 所选固定布局部件, child 已闭合子树，nil用于根属性校验
// 返回: *xmlElement 独立过滤片段, error MCE、根名称或结构错误
func (p *streamPackage) layoutFragment(part *streamPart, child *xmlElement) (*xmlElement, error) {
	s := part.layout
	fragment := &xmlElement{Name: s.root.Name, Attr: s.root.Attr, Namespaces: s.root.Namespaces}
	if child != nil {
		fragment.Children = []*xmlElement{child}
	}
	namespace := formatNamespace(p.index.format)
	root, err := preprocessXMLContext(fragment, []string{namespace, namespace + "/resourcedictionary-key"}, p.context)
	if err != nil {
		return nil, &PartError{Part: part.name, Err: err}
	}
	name := "FixedDocument"
	if strings.EqualFold(part.name, p.index.sequence) {
		name = "FixedDocumentSequence"
	}
	if root.Name.Space != namespace || root.Name.Local != name {
		return nil, &PartError{Part: part.name, Element: root.Name.Local, Err: fmt.Errorf("%w: streamed layout root", ErrInvalid)}
	}
	if err := validateFixedStructureElement(root, p.index.format, false); err != nil {
		return nil, &PartError{Part: part.name, Element: root.Name.Local, Err: err}
	}
	return root, nil
}

// appendLayoutReference 共用引用值解析并保存规范化部件身份，不保留已经消费的XML子树
// 入参: part 所选固定布局部件, node 已校验引用
// 返回: error URI、重复引用或预算错误
func (p *streamPackage) appendLayoutReference(part *streamPart, node *xmlElement) error {
	s := part.layout
	var target string
	var page PageReference
	var err error
	if strings.EqualFold(part.name, p.index.sequence) {
		target, err = p.index.readDocumentReference(part.name, node)
	} else {
		if len(s.pages) >= p.options.Limits.MaxPageCount {
			return fmt.Errorf("%w: streamed document page count", ErrLimit)
		}
		page, err = p.index.readPageReference(part.name, node)
		target = page.Part
	}
	if err != nil {
		return err
	}
	key := strings.ToLower(target)
	if s.references[key] {
		return &PartError{Part: part.name, Element: node.Name.Local, Err: fmt.Errorf("%w: duplicate streamed reference %s", ErrInvalid, target)}
	}
	s.references[key] = true
	if page.Part == "" {
		s.documents = append(s.documents, target)
	} else {
		s.pages = append(s.pages, page)
	}
	return nil
}

// advanceLayoutIndex 接入已到达的所选元数据分片，再按文档顺序推进索引，不重入正在交付词元的解析器
// 返回: error 元数据、类型、索引或回调错误
func (p *streamPackage) advanceLayoutIndex() error {
	if !p.sequenceRead {
		if err := p.advanceMetadataPart(p.index.sequence, "fixeddocumentsequence"); err != nil {
			return err
		}
	}
	if err := p.applyLayoutIndex(); err != nil {
		return err
	}
	for p.document < len(p.documents) {
		before := p.document
		if err := p.advanceMetadataPart(p.documents[p.document], "fixeddocument"); err != nil {
			return err
		}
		if err := p.applyLayoutIndex(); err != nil {
			return err
		}
		if before == p.document {
			break
		}
	}
	return nil
}

// advanceMetadataPart 使用实际声明类型推进所选元数据，不把引用位置当作类型证明
// 入参: name 所选部件URI, kind 固定布局种类
// 返回: error 内容类型、XML或回调错误
func (p *streamPackage) advanceMetadataPart(name, kind string) error {
	part := p.parts[strings.ToLower(name)]
	if part == nil {
		return nil
	}
	media := p.types.declaredContentType(name)
	if !strings.EqualFold(media, fixedContentType(kind)) {
		return &PartError{Part: name, Err: fmt.Errorf("%w: streamed layout content type", ErrInvalid)}
	}
	return p.advanceXML(part, media)
}

// applyLayoutIndex 消费已经校验的引用前缀或完整延迟部件，前一文档未结束时不加入后一文档的页面
// 返回: error 索引、引用、预算或读取错误
func (p *streamPackage) applyLayoutIndex() error {
	if p.pageNames == nil {
		p.pageNames = make(map[string]bool)
	}
	before := len(p.index.pages)
	defer func() {
		for _, page := range p.index.pages[before:] {
			p.pageNames[strings.ToLower(page.Part)] = true
		}
	}()
	sequence := p.parts[strings.ToLower(p.index.sequence)]
	if sequence == nil {
		return nil
	}
	var references []string
	if sequence.layout != nil && !sequence.layout.deferred {
		references = sequence.layout.documents
	} else if !p.sequenceRead {
		if _, present := p.pagePkg.parts[strings.ToLower(sequence.name)]; !present {
			return nil
		}
		var err error
		references, err = p.index.readDocumentReferences()
		if err != nil {
			return err
		}
		p.sequenceRead = true
	} else {
		references = p.documents
	}
	if len(references) < len(p.documents) {
		return fmt.Errorf("%w: streamed sequence prefix length", ErrInvalid)
	}
	for _, reference := range references[len(p.documents):] {
		p.documents = append(p.documents, reference)
		p.documentKeys[strings.ToLower(reference)] = true
	}
	for p.document < len(p.documents) {
		name := p.documents[p.document]
		part := p.parts[strings.ToLower(name)]
		if part == nil {
			return nil
		}
		if part.layout == nil || part.layout.deferred {
			if _, present := p.pagePkg.parts[strings.ToLower(name)]; !present {
				return nil
			}
			doc, err := p.index.readDocument(name, p.seenPages)
			if err != nil {
				return err
			}
			p.index.documents = append(p.index.documents, doc)
			p.document++
			continue
		}
		if len(p.index.documents) == p.document {
			p.index.documents = append(p.index.documents, Document{Part: name})
		}
		doc := &p.index.documents[p.document]
		for _, page := range part.layout.pages[len(doc.Pages):] {
			if err := p.index.appendDocumentPage(doc, page, p.seenPages); err != nil {
				return err
			}
		}
		if !part.layout.closed {
			return nil
		}
		p.document++
	}
	return nil
}

// selectedRelationships 对页面消费者启用规范关系部件的语义，不按媒体类型解释一般附加XML
// 入参: name 规范部件URI, media 声明类型
// 返回: bool 是否处理关系语义
func (p *streamPackage) selectedRelationships(name, media string) bool {
	return p.options.OnPage != nil && opcRelationshipName(name) && strings.EqualFold(media, opcRelsType)
}

// consumeRelationships 在原根作用域下处理闭合关系子树，共用OPC、MCE及关系值校验
// 入参: part 关系部件, event 独立词元
// 返回: error 元数据、关联、预算、回调或取消错误
func (p *streamPackage) consumeRelationships(part *streamPart, event StreamXMLToken) error {
	if part.relations == nil {
		part.relations = &streamPartialRelationships{ids: make(map[string]bool), discards: make(map[string]int)}
	}
	s := part.relations
	if s.deferred {
		return nil
	}
	switch token := event.Token.(type) {
	case xml.StartElement:
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: maps.Clone(event.Namespaces)}
		if len(s.stack) == 0 {
			if s.root != nil {
				return fmt.Errorf("%w: multiple streamed relationship roots", ErrInvalid)
			}
			s.root = node
			if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationships"}) {
				s.deferred = true
				return nil
			}
			if err := p.relationshipFragment(part, nil); err != nil {
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
		if len(s.stack) == 1 {
			if !xmlWhitespace(string(token)) {
				return fmt.Errorf("%w: streamed relationship root text", ErrInvalid)
			}
			return nil
		}
		node := s.stack[len(s.stack)-1]
		node.text = append(node.text, token...)
	case xml.EndElement:
		if len(s.stack) == 0 {
			return fmt.Errorf("%w: streamed relationship end", ErrInvalid)
		}
		node := s.stack[len(s.stack)-1]
		node.Text, node.text = string(node.text), nil
		s.stack[len(s.stack)-1] = nil
		s.stack = s.stack[:len(s.stack)-1]
		before := len(s.items)
		if len(s.stack) == 1 {
			if err := p.relationshipFragment(part, node); err != nil {
				return err
			}
		} else if len(s.stack) == 0 {
			s.closed = true
		} else {
			return nil
		}
		if err := p.activateStreamIndex(); err != nil {
			return err
		}
		if p.index != nil {
			if strings.EqualFold(part.name, "/_rels/.rels") {
				if s.discards[formatNamespace(p.index.format)+"/discard-control"] > 1 {
					return fmt.Errorf("%w: multiple discard control relationships", ErrInvalid)
				}
				if err := p.updateDiscard(p.index); err != nil {
					return err
				}
				if err := p.applyLayoutIndex(); err != nil {
					return err
				}
				return p.emitReadyPages(part.name)
			}
			needed := s.closed
			ticketBound := false
			requiredType := formatNamespace(p.index.format) + "/required-resource"
			ticketType := formatNamespace(p.index.format) + "/printticket"
			for _, item := range s.items[before:] {
				if item.Type == requiredType {
					needed = true
				}
				if item.Type == ticketType {
					needed = true
					ticketBound = true
				}
			}
			if ticketBound {
				p.pageWait = nil
			}
			if needed {
				return p.emitReadyPages(part.name)
			}
		}
	}
	return nil
}

// relationshipFragment 共用关系元数据的兼容处理及解析，重复ID在整个逻辑部件内累积
// 入参: part 关系部件, child 闭合直接子树，nil校验根声明
// 返回: error 兼容性、结构、值或根关联重复错误
func (p *streamPackage) relationshipFragment(part *streamPart, child *xmlElement) error {
	s := part.relations
	fragment := &xmlElement{Name: s.root.Name, Attr: s.root.Attr, Namespaces: s.root.Namespaces}
	if child != nil {
		fragment.Children = []*xmlElement{child}
	}
	root, err := preprocessXMLContext(fragment, []string{opcRelsNS}, p.context)
	if err != nil {
		return err
	}
	source := relationshipSource(part.name)
	return opcMetadataElements(root, opcRelsNS, "Relationships", func(element xml.StartElement, attrs map[string]string) error {
		rel, err := parseRelationship(source, element, attrs, s.ids)
		if err != nil {
			return err
		}
		if source == "/" {
			switch rel.Type {
			case xpsNamespace + "/fixedrepresentation", openXPSNamespace + "/fixedrepresentation":
				if s.fixed {
					return fmt.Errorf("%w: multiple fixed representations", ErrInvalid)
				}
				s.fixed = true
			case xpsNamespace + "/discard-control", openXPSNamespace + "/discard-control":
				s.discards[rel.Type]++
			}
		}
		s.items = append(s.items, rel)
		return nil
	})
}

// relationshipSnapshot 为临时消费者提供独立关系前缀，未结束时记录当前页面等待的元数据部件
// 入参: source 规范源URI，包根为/
// 返回: []Relationship 独立前缀, bool 是否由流式状态处理, error 源或元数据错误
func (p *streamPackage) relationshipSnapshot(source string) ([]Relationship, bool, error) {
	if source != "/" && p.parts[strings.ToLower(source)] == nil {
		return nil, false, nil
	}
	name := createdRelationshipPart(source)
	part := p.parts[strings.ToLower(name)]
	if part == nil || part.relations == nil || part.relations.root == nil || part.relations.deferred {
		if source != "/" {
			if _, present := p.pagePkg.parts[strings.ToLower(source)]; !present {
				if _, complete := p.pagePkg.parts[strings.ToLower(name)]; complete {
					items, err := p.pagePkg.readRelationships(source, name)
					return items, true, err
				}
				if p.pageWait != nil {
					p.pageWait[strings.ToLower(name)] = true
				}
				return nil, true, nil
			}
		}
		return nil, false, nil
	}
	if !part.relations.closed && p.pageWait != nil {
		p.pageWait[strings.ToLower(name)] = true
	}
	return slices.Clone(part.relations.items), true, nil
}

// advanceRelationshipPart 推进规范关系部件的已到达分片，声明类型与元数据预算仍须成立
// 入参: name 关系部件URI
// 返回: error 类型、XML、预算或回调错误
func (p *streamPackage) advanceRelationshipPart(name string) error {
	part := p.parts[strings.ToLower(name)]
	if part == nil {
		return nil
	}
	media := p.types.declaredContentType(name)
	if !strings.EqualFold(media, opcRelsType) {
		return fmt.Errorf("%w: streamed relationship content type", ErrInvalid)
	}
	return p.advanceXML(part, media)
}

// activateStreamIndex 在固定表示关系明确后建立临时索引，没有闭合固定表示时继续接收
// 返回: error 完整根或已闭合关联错误
func (p *streamPackage) activateStreamIndex() error {
	if p.index != nil || p.pagePkg == nil {
		return nil
	}
	root := p.parts["/_rels/.rels"]
	if root != nil && root.relations != nil && !root.relations.deferred {
		if !root.relations.fixed && !root.relations.closed {
			return nil
		}
	} else if _, complete := p.pagePkg.parts["/_rels/.rels"]; !complete {
		return nil
	}
	index := &Reader{pkg: p.pagePkg, limits: p.options.Limits}
	if err := index.readFixedRepresentation(); err != nil {
		return err
	}
	p.index, p.seenPages, p.documentKeys = index, make(map[string]bool), make(map[string]bool)
	p.index.fixedXML = p.closedPageRoot
	return nil
}

// rootRelationshipsPending 判断包根关系部件是否仍处于增量接收阶段
// 返回: bool 根关系尚未结束
func (p *streamPackage) rootRelationshipsPending() bool {
	part := p.parts["/_rels/.rels"]
	if part != nil && part.relations != nil && !part.relations.deferred {
		return !part.relations.closed
	}
	_, complete := p.pagePkg.parts["/_rels/.rels"]
	return !complete
}

// finishRelationships 用完整索引校验前向关系结果及源存在性，较晚的关系错误不能被早期页面掩盖
// 入参: r 最终读取器
// 返回: error 关系、源、前缀冲突或取消错误
func (p *streamPackage) finishRelationships(r *Reader) error {
	if p.options.OnPage == nil {
		return nil
	}
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		part := p.parts[key]
		if !opcRelationshipName(part.name) {
			continue
		}
		if err := checkContext(p.context); err != nil {
			return err
		}
		items, err := r.pkg.relationships(relationshipSource(part.name))
		if err != nil {
			return err
		}
		if part.relations == nil || part.relations.deferred {
			continue
		}
		if len(items) < len(part.relations.items) {
			return fmt.Errorf("%w: streamed relationship prefix length", ErrInvalid)
		}
		for index, item := range part.relations.items {
			if items[index] != item {
				return fmt.Errorf("%w: streamed relationship prefix conflict", ErrInvalid)
			}
		}
	}
	return nil
}
