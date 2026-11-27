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
	"math"
	"slices"
	"strings"
)

// StreamPage 表示前向流读取中资源已就绪的临时页面视图，Index为零基全局页号，DocumentPart为所属文档URI
// Page、PageHeader、Walk、WalkPrint、Font、Image、ImageInfo、ReadPart、ColorProfile、StoryFragments、Resources、ResolveColor、PrintTicketHierarchy、PrintSettings、PrintColorPlan、PrintLayout、CoreProperties、DocumentStructure、Render、RenderDevice、RenderElement、RenderElementMapped、RenderBrushTile与RenderBrushTileWithState仅在OnPage回调期间可用
// 回调结束后视图自动关闭，返回的页面数据、资源及图像独立于视图；Read或ConsumeStream成功前均为临时结果
type StreamPage struct {
	Index        int
	DocumentPart string
	Reference    PageReference
	view         *streamPageView
}

// StreamPrintWalkOptions 设置流式单页打印遍历的基础票据、物理介质、票据解析预算与未支持Feature忽略策略
type StreamPrintWalkOptions struct {
	Defaults                  *PrintSettings
	Media                     PrintMedia
	Settings                  PrintSettingsOptions
	IgnoreUnsupportedFeatures bool
}

// streamPageView 保存临时页面视图的只读阅读器、方言、页号、文档位置、资源清单、读取进度、未完流标志、所属流状态与流取消Context
type streamPageView struct {
	reader           *Reader
	owner            *streamPackage
	format           Format
	index            int
	documentIndex    int
	pageIndex        int
	resources        []string
	progress         StreamProgress
	streamIncomplete bool
	context          context.Context
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

// Format 返回当前文档的XPS或OpenXPS方言，无效或未初始化返回FormatUnknown
// 返回: Format 文档方言
func (p *StreamPage) Format() Format {
	if p == nil || p.view == nil {
		return FormatUnknown
	}
	return p.view.format
}

// Progress 返回交付当前页面时的流式读取字节数、已交付页数、已发现页数与已完结文档数快照
// 返回: StreamProgress 当前流式消费进度快照
func (p *StreamPage) Progress() StreamProgress {
	if p == nil || p.view == nil {
		return StreamProgress{}
	}
	return p.view.progress
}

// PageHeader 仅读取当前临时页FixedPage根标签属性返回页面尺寸、裁剪区域、语言与名称，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *PageHeader 轻量页面头信息, error 状态、媒体类型、XML、取消或关闭错误
func (p *StreamPage) PageHeader(ctx context.Context) (*PageHeader, error) {
	r, headerCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	canonical, err := opcPartName(p.Reference.Part)
	if err != nil {
		return nil, err
	}
	if _, exists := r.pkg.parts[strings.ToLower(canonical)]; exists {
		return r.readPageHeaderStream(headerCtx, canonical)
	}
	page, err := r.readPageHeader(p.view.index, nil, headerCtx)
	if err != nil {
		return nil, err
	}
	return &PageHeader{
		Part:          page.Part,
		Width:         page.Width,
		Height:        page.Height,
		ContentBox:    page.ContentBox,
		BleedBox:      page.BleedBox,
		HasContentBox: page.HasContentBox,
		HasBleedBox:   page.HasBleedBox,
		Language:      page.Language,
		Name:          page.Name,
	}, nil
}

// lockReader 校验临时页面视图、获取读锁、合并并检查Context，成功时调用方须立即通过Defer执行清理函数
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Reader 有效只读阅读器, context.Context 合并后的Context, func() 释放清理函数, error 关闭或取消错误
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
	if err := checkContext(merged); err != nil {
		stop()
		r.mu.RUnlock()
		return nil, nil, nil, err
	}
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

// prepareCall 校验临时页面视图与底层阅读器未关闭并合并检查流取消Context，不持有阅读器读锁
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Reader 有效只读阅读器, context.Context 合并后的Context, func() 取消监听清理函数, error 关闭或取消错误
func (p *StreamPage) prepareCall(ctx context.Context) (*Reader, context.Context, func(), error) {
	if p == nil || p.view == nil || p.view.reader == nil {
		return nil, nil, nil, ErrClosed
	}
	r := p.view.reader
	r.mu.RLock()
	closed := r.closed
	r.mu.RUnlock()
	if closed {
		return nil, nil, nil, ErrClosed
	}
	merged, cleanup := mergeContext(ctx, p.view.context)
	if err := checkContext(merged); err != nil {
		cleanup()
		return nil, nil, nil, err
	}
	return r, merged, cleanup, nil
}

// Walk 在前向读取回调期间按严格绘制顺序遍历当前临时页面场景
// 回调期间不持有阅读器读锁，允许回调安全调用Font或Image读取已到达资源；回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 页面读取、参数、资源上限、取消、关闭或回调返回的错误
func (p *StreamPage) Walk(ctx context.Context, visitor *SceneVisitor, options *WalkOptions) error {
	r, walkCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return err
	}
	defer cleanup()
	return r.Walk(walkCtx, p.view.index, visitor, options)
}

// Font 在前向读取回调期间相对当前页解析URI并读取解混淆后的已到达字体资源，支持#index集合索引
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, fontURI 相对或包根字体URI，可附#index集合索引
// 返回: *FontResource 独立只读字体资源, error URI、读取、格式、取消或关闭错误
func (p *StreamPage) Font(ctx context.Context, fontURI string) (*FontResource, error) {
	r, fontCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	partURI, collectionIndex, hasCollectionIndex, err := ParseFontURI(strings.Trim(fontURI, " \t\r\n"))
	if err != nil {
		return nil, err
	}
	part, err := resolvePart(p.Reference.Part, partURI)
	if err != nil {
		return nil, err
	}
	resolved := part
	if hasCollectionIndex {
		resolved = fmt.Sprintf("%s#%d", part, collectionIndex)
	}
	return r.Font(fontCtx, resolved)
}

// Image 在前向读取回调期间读取当前临时页引用的已到达图像资源，不访问未到达部件
// 未指定Context时沿用流读取Context并同时响应两者取消信号，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 图像部件的包根URI, options 图像参数，nil采用默认值
// 返回: *ImageResource 独立图像数据, error 输入、解码、资源、取消或关闭错误
func (p *StreamPage) Image(ctx context.Context, part string, options *ImageOptions) (*ImageResource, error) {
	r, imageCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.Image(imageCtx, part, options)
}

// ImageInfo 相对当前页或包根解析URI并仅读取已到达图像文件头元数据，不解码像素，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 相对或包根图像部件URI
// 返回: *ImageInfo 轻量图像头元数据, error URI、媒体类型、文件头、预算、取消或关闭错误
func (p *StreamPage) ImageInfo(ctx context.Context, part string) (*ImageInfo, error) {
	r, imageCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	resolved, err := resolvePart(p.Reference.Part, part)
	if err != nil {
		return nil, err
	}
	return r.ImageInfo(imageCtx, resolved)
}

// StoryFragments 返回当前页已关联且已到达的故事片段独立副本，未关联或尚未到达时返回nil，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *StoryFragments 独立片段数据或nil, error 关系、媒体类型、结构、预算、取消或关闭错误
func (p *StreamPage) StoryFragments(ctx context.Context) (*StoryFragments, error) {
	r, sfCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return r.streamReadStoryFragmentsIfPresent(sfCtx, p.Reference.Part)
}

// Resources 返回当前页已解析去重并按字典序稳定排列的规范必需资源部件URI列表，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: []string 规范必需资源部件URI列表, error 取消或关闭错误
func (p *StreamPage) Resources(ctx context.Context) ([]string, error) {
	_, _, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return slices.Clone(p.view.resources), nil
}

// ResolveColor 以当前页部件为基准解析sRGB、scRGB及含ICC配置的ContextColor，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, value 待解析颜色, options 色彩解析选项，nil采用默认值
// 返回: ResolvedColor 解析后的多空间颜色结果, error 参数、部件、配置、转换、取消或关闭错误
func (p *StreamPage) ResolveColor(ctx context.Context, value Color, options *ColorResolveOptions) (ResolvedColor, error) {
	r, colorCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return ResolvedColor{}, err
	}
	defer cleanup()
	return r.ResolveColor(colorCtx, p.Reference.Part, value, options)
}

// ReadPart 按安全受限方式读取已到达的任意包内部件原始字节，未到达部件返回ErrNotFound，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, name 部件包根URI
// 返回: []byte 独立部件字节, error URI、不存在、预算、取消或关闭错误
func (p *StreamPage) ReadPart(ctx context.Context, name string) ([]byte, error) {
	r, partCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return r.pkg.readPartContext(partCtx, name)
}

// ColorProfile 相对当前页部件解析URI并读取已到达ICC配置部件原始字节，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, uri 相对或包根ICC配置URI
// 返回: []byte 独立ICC配置字节, error URI、类型、不存在、预算、取消或关闭错误
func (p *StreamPage) ColorProfile(ctx context.Context, uri string) ([]byte, error) {
	r, profileCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	part, err := resolvePart(p.Reference.Part, uri)
	if err != nil {
		return nil, err
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if !requiredResourceMedia(requiredProfile, media) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: unexpected color profile content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readPartContext(profileCtx, part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	return data, nil
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
	return r.streamReadPrintSettingsCached(settingsCtx, p.view.index, defaults, options, p.view.owner)
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
	settings, err := r.streamReadPrintSettingsCached(colorCtx, p.view.index, defaults, options, p.view.owner)
	if err != nil {
		return nil, err
	}
	_, result, err := printColorPlanSettings(colorCtx, settings, options)
	return result, err
}

// PrintLayout 基于当前临时页已合并有效票据直接计算物理打印布局，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, options 基础票据、介质及解析预算，nil采用默认值
// 返回: *PrintLayout 独立打印布局, error 页面、票据、设置、预算、取消或关闭错误
func (p *StreamPage) PrintLayout(ctx context.Context, options *PrintLayoutOptions) (*PrintLayout, error) {
	r, layoutCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	configuration := DefaultPrintLayoutOptions()
	if options != nil {
		configuration = *options
	}
	if configuration.Settings.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print page layout", ErrInvalid)
	}
	settings, err := r.streamReadPrintSettingsCached(layoutCtx, p.view.index, configuration.Defaults, &configuration.Settings, p.view.owner)
	if err != nil {
		return nil, err
	}
	page, err := r.readPageHeader(p.view.index, nil, layoutCtx)
	if err != nil {
		return nil, err
	}
	effective := settings
	if configuration.IgnoreUnsupportedFeatures {
		effective = printStripPrivateExtensions(settings)
	}
	return effective.Layout(layoutCtx, page, configuration.Media, &configuration.Settings)
}

// CoreProperties 返回已到达的包级核心属性独立副本，未关联或尚未到达时返回nil，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *CoreProperties 独立核心属性或nil, error 关系、格式、预算、取消或关闭错误
func (p *StreamPage) CoreProperties(ctx context.Context) (*CoreProperties, error) {
	r, propsCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	if p.view.owner != nil && p.view.owner.corePropsCached != nil {
		return cloneCoreProperties(p.view.owner.corePropsCached), nil
	}
	props, _, err := r.streamReadCorePropertiesIfPresent(propsCtx)
	return props, err
}

// DocumentStructure 返回当前页所属文档已到达的文档结构独立副本，未关联或尚未到达时返回nil，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *DocumentStructure 独立文档结构或nil, error 关系、格式、预算、取消或关闭错误
func (p *StreamPage) DocumentStructure(ctx context.Context) (*DocumentStructure, error) {
	r, structCtx, release, err := p.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	docIdx := p.view.documentIndex
	if p.view.owner != nil && p.view.owner.docStructCached != nil {
		if cached := p.view.owner.docStructCached[docIdx]; cached != nil {
			return cloneDocumentStructure(cached), nil
		}
	}
	pageLimit := math.MaxInt32
	if p.view.owner == nil || docIdx < p.view.owner.document {
		if docIdx >= 0 && docIdx < len(r.documents) {
			pageLimit = len(r.documents[docIdx].Pages)
		}
	}
	ds, _, _, err := r.streamReadDocumentStructureIfPresent(structCtx, p.DocumentPart, pageLimit)
	return ds, err
}

// Render 使用文档引擎现有渲染器绘制当前页面，不重新封装ZIP或另行解释页面语义
// 未指定绘制Context时沿用前向读取Context，同时响应两者的取消信号，不修改调用方参数
// 入参: ctx 取消Context，nil沿用流读取Context, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 独立页面图像, error 绘制、资源、预算、取消或关闭错误
func (p *StreamPage) Render(ctx context.Context, options *RenderOptions) (*image.NRGBA, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.Render(renderCtx, p.view.index, options)
}

// RenderDevice 在前向读取回调中绘制目标ICC分量，缺省沿用流读取Context并兼顾流取消
// 入参: ctx 取消Context，nil沿用流读取Context, device 必需目标配置, options 绘制参数
// 返回: *DeviceImage 独立设备图像，失败为nil, error 关闭、资源、转换或取消错误
func (p *StreamPage) RenderDevice(ctx context.Context, device *DeviceColorTarget, options *RenderOptions) (*DeviceImage, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.RenderDevice(renderCtx, p.view.index, device, options)
}

// RenderElement 在前向读取回调中以当前页为默认资源基准隔离光栅化单个元素到透明背景画布，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, elem 单个Canvas/Path/Glyphs元素, state 有效图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 透明背景隔离图像, Rect 图像在页面或纸面坐标系中的包围盒, error 参数、资源、预算、取消或关闭错误
func (p *StreamPage) RenderElement(ctx context.Context, elem Element, state WalkState, options *RenderOptions) (*image.NRGBA, Rect, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	defer cleanup()
	basePart := state.PagePart
	if basePart == "" {
		basePart = p.Reference.Part
	}
	return r.RenderElement(renderCtx, basePart, elem, state, options)
}

// RenderElementMapped 在前向读取回调中隔离光栅化单个元素并返回PixelToPage仿射映射矩阵，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, elem 单个Canvas/Path/Glyphs元素, state 有效图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *RenderedElement 含图像、包围盒与映射矩阵的结果, error 参数、资源、预算、取消或关闭错误
func (p *StreamPage) RenderElementMapped(ctx context.Context, elem Element, state WalkState, options *RenderOptions) (*RenderedElement, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	if state.PagePart == "" {
		state.PagePart = p.Reference.Part
	}
	return r.RenderElementMapped(renderCtx, elem, state, options)
}

// RenderBrushTile 在前向读取回调中以当前页为默认资源基准隔离光栅化单个画刷瓦片，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, brush 待光栅化画刷, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 透明背景单瓦片图像, Rect 瓦片物理范围矩形, error 参数、画刷、资源、预算、取消或关闭错误
func (p *StreamPage) RenderBrushTile(ctx context.Context, brush *Brush, options *RenderOptions) (*image.NRGBA, Rect, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	defer cleanup()
	return r.RenderBrushTileWithState(renderCtx, brush, p.Reference.Part, WalkState{PagePart: p.Reference.Part, Opacity: 1, Matrix: IdentityMatrix()}, options)
}

// RenderBrushTileWithState 在前向读取回调中按指定图形与打印色彩状态隔离光栅化单个画刷瓦片，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, brush 待光栅化画刷, state 图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 透明背景单瓦片图像, Rect 瓦片物理范围矩形, error 参数、画刷、资源、预算、取消或关闭错误
func (p *StreamPage) RenderBrushTileWithState(ctx context.Context, brush *Brush, state WalkState, options *RenderOptions) (*image.NRGBA, Rect, error) {
	r, renderCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	defer cleanup()
	basePart := state.PagePart
	if basePart == "" {
		basePart = p.Reference.Part
	}
	return r.RenderBrushTileWithState(renderCtx, brush, basePart, state, options)
}

// WalkPrint 结合当前临时页有效PrintSettings、PrintLayout、PrintColorPlan与PrintWatermark合成单页PrintSide并复用WalkPrintSide遍历
// 遇非恒等拼版特征（N-Up、Poster、Booklet、Duplex）或未完流下要求数字签名验证时显式返回ErrUnsupported
// 回调期间不持有阅读器读锁，允许回调安全调用Font、Image或RenderElement；回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, options 基础票据、介质与解析预算，nil采用默认值, visitor 事件回调集合, walkOptions 遍历选项，nil采用默认值
// 返回: error 票据、布局、页面读取、签名、预算、取消、关闭或回调返回的错误
func (p *StreamPage) WalkPrint(ctx context.Context, options *StreamPrintWalkOptions, visitor *SceneVisitor, walkOptions *WalkOptions) error {
	r, walkCtx, cleanup, err := p.prepareCall(ctx)
	if err != nil {
		return err
	}
	defer cleanup()
	r.mu.RLock()
	if r.closed {
		r.mu.RUnlock()
		return ErrClosed
	}
	side, effectiveWalk, err := p.buildStreamPrintSide(r, walkCtx, options, walkOptions)
	r.mu.RUnlock()
	if err != nil {
		return err
	}
	return r.WalkPrintSide(walkCtx, side, visitor, effectiveWalk)
}

// buildStreamPrintSide 在持有阅读器读锁期间基于当前页合并后的有效打印票据合成单页PrintSide与有效遍历参数
// 入参: r 有效只读阅读器, ctx 已合并取消Context, options 打印遍历参数, walkOptions 遍历选项
// 返回: *PrintSide 合成单页纸面, *WalkOptions 有效遍历选项, error 票据、拼版、签名、布局、页面或取消错误
func (p *StreamPage) buildStreamPrintSide(r *Reader, ctx context.Context, options *StreamPrintWalkOptions, walkOptions *WalkOptions) (*PrintSide, *WalkOptions, error) {
	defaults := DefaultPrintLayoutOptions()
	configuration := StreamPrintWalkOptions{Defaults: defaults.Defaults, Media: defaults.Media, Settings: defaults.Settings, IgnoreUnsupportedFeatures: defaults.IgnoreUnsupportedFeatures}
	if options != nil {
		configuration = *options
	}
	if configuration.Settings.Scope != PrintScopeUnknown {
		return nil, nil, fmt.Errorf("%w: scope on stream print walk", ErrInvalid)
	}
	media := configuration.Media
	if err := validatePrintMedia(media); err != nil {
		return nil, nil, err
	}
	settingsCfg, err := printSettingsOptions(ctx, &configuration.Settings)
	if err != nil {
		return nil, nil, err
	}
	settingsCfg.ignoreUnsupported = configuration.IgnoreUnsupportedFeatures
	model, err := r.streamReadPrintSettingsCached(ctx, p.view.index, configuration.Defaults, &configuration.Settings, p.view.owner)
	if err != nil {
		return nil, nil, err
	}
	if configuration.IgnoreUnsupportedFeatures {
		model = printStripPrivateExtensions(model)
	}
	control := newPrintLayoutSettings(model, settingsCfg)
	if err := control.checkBindingConflict(); err != nil {
		return nil, nil, err
	}
	jobFin, _, err := control.binding("JobBindAllDocuments")
	if err != nil {
		return nil, nil, err
	}
	docFin, _, err := control.binding("DocumentBinding")
	if err != nil {
		return nil, nil, err
	}
	finishing := jobFin
	if docFin.Binding != PrintBindingNone {
		finishing = docFin
	}
	if finishing.Binding == PrintBindingBooklet {
		return nil, nil, fmt.Errorf("%w: booklet imposition requires print plan", ErrUnsupported)
	}
	maxInt := int(^uint(0) >> 1)
	nup, _, err := control.effectiveNUp(maxInt)
	if err != nil {
		return nil, nil, err
	}
	if nup > 1 {
		return nil, nil, fmt.Errorf("%w: N-up imposition requires print plan", ErrUnsupported)
	}
	poster, err := control.poster(maxInt)
	if err != nil {
		return nil, nil, err
	}
	if poster > 1 {
		return nil, nil, fmt.Errorf("%w: poster tiling requires print plan", ErrUnsupported)
	}
	duplex, _, err := control.effectiveDuplex()
	if err != nil {
		return nil, nil, err
	}
	if duplex != PrintSimplex {
		return nil, nil, fmt.Errorf("%w: duplex imposition requires print plan", ErrUnsupported)
	}
	sigPolicy, err := printSignaturePolicy(model, ctx)
	if err != nil {
		return nil, nil, err
	}
	effectivePolicy := sigPolicy
	if walkOptions != nil && walkOptions.Signatures != nil && walkOptions.Signatures.Policy != PrintSignatureFromTicket {
		if walkOptions.Signatures.Policy > PrintSignatureRequireValid {
			return nil, nil, fmt.Errorf("%w: print side signature policy", ErrInvalid)
		}
		effectivePolicy = walkOptions.Signatures.Policy
	}
	if effectivePolicy != PrintSignatureIgnore && p.view.streamIncomplete {
		return nil, nil, fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
	}
	page, err := r.readPageHeader(p.view.index, nil, ctx)
	if err != nil {
		return nil, nil, err
	}
	state, err := preparePrintPageState(ctx, model, settingsCfg, page, media, printPageStateOptions{
		stripSignatures:      true,
		stripPlanFeatures:    true,
		ignoreUnsupported:    configuration.IgnoreUnsupportedFeatures,
		ignoreColorPlanError: configuration.IgnoreUnsupportedFeatures,
	})
	if err != nil {
		return nil, nil, err
	}
	side := &PrintSide{
		Width:           state.layout.Width,
		Height:          state.layout.Height,
		MediaClip:       state.layout.MediaClip,
		Color:           state.outputColor,
		SignaturePolicy: sigPolicy,
		Pages: []PrintPlacement{{
			Page:          p.view.index,
			DocumentIndex: p.view.documentIndex,
			Transform:     state.layout.Transform,
			PageClip:      state.layout.PageClip,
			MediaClip:     state.layout.MediaClip,
			Watermark:     state.watermark,
			Negative:      state.negative,
			Color:         state.colorPlan,
		}},
	}
	side.Gutter = printBindingGutter(finishing, *side, PrintSimplex, false)
	effectiveWalk := walkOptions
	if walkOptions == nil || walkOptions.Signatures == nil {
		copied := WalkOptions{}
		if walkOptions != nil {
			copied = *walkOptions
		}
		copied.Signatures = &PrintSignatureOptions{Policy: sigPolicy}
		effectiveWalk = &copied
	} else if walkOptions.Signatures.Policy == PrintSignatureFromTicket {
		copied := *walkOptions
		sigCopy := *walkOptions.Signatures
		sigCopy.Policy = sigPolicy
		copied.Signatures = &sigCopy
		effectiveWalk = &copied
	}
	return side, effectiveWalk, nil
}

// registerPagePart 将完整部件接入前向读取后端，原始部件保存物理范围并释放已结束页面的增量树
// 入参: part 完整逻辑部件
func (p *streamPackage) registerPagePart(part *streamPart) {
	if !p.needsIndex() || part.reclaimed {
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
	if p.needsIndex() && p.pagePkg == nil {
		p.pagePkg = &packageReader{limits: p.options.Limits, parts: make(map[string][]*zip.File), names: make(map[string]string), defaults: p.types.defaults, overrides: p.types.overrides, cache: p.cache}
		p.pagePkg.open = func(key string) (io.ReadCloser, error) {
			part := p.parts[key]
			if part == nil || part.reclaimed || part.partiallyReclaimed || part.last < 0 || len(part.entries) != part.last+1 {
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

// emitPages 在元数据或页面依赖到达后按顺序提供元数据回调与可解析页面，未确认的缺失及关系错误留待最终校验
// 入参: name 到达部件名
// 返回: error 预算、输入、取消、已确定结构或调用方回调错误
func (p *streamPackage) emitPages(name string) error {
	if !p.needsIndex() || p.pagePkg == nil {
		return nil
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	if err := p.advanceRelationshipPart("/_rels/.rels"); err != nil {
		return err
	}
	if err := p.emitMetadataCallbacks(); err != nil {
		return err
	}
	if err := p.activateStreamIndex(); err != nil {
		return err
	}
	if p.index == nil {
		return nil
	}
	if p.options.OnPage != nil {
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
	}
	if err := p.advanceLayoutIndex(); err != nil {
		return err
	}
	if err := p.emitMetadataCallbacks(); err != nil {
		return err
	}
	if p.options.OnPage == nil {
		return nil
	}
	if err := p.advancePageMarkup(); err != nil {
		return err
	}
	return p.emitReadyPages(name)
}

// streamPageMissingResources 从页面已到达关系中收集当前缺失的必需资源部件键，避免每缺失一项重复全解析整页
// 入参: index 待检查页面序号
// 返回: []string 尚未到达的必需资源小写键列表
func (p *streamPackage) streamPageMissingResources(index int) []string {
	pagePart := p.index.pages[index].Part
	relsKey := strings.ToLower(createdRelationshipPart(pagePart))
	var relations []Relationship
	if _, complete := p.pagePkg.parts[relsKey]; complete {
		items, err := p.index.pkg.relationshipsContext(p.context, pagePart)
		if err != nil {
			return nil
		}
		relations = items
	} else if relsPart := p.parts[relsKey]; relsPart != nil && relsPart.relations != nil && !relsPart.relations.deferred {
		relations = relsPart.relations.items
	} else {
		return nil
	}
	requiredType := formatNamespace(p.index.format) + "/required-resource"
	var missing []string
	seen := make(map[string]bool)
	for _, rel := range relations {
		if rel.Type != requiredType || rel.TargetMode != TargetModeInternal {
			continue
		}
		target, err := resolvePart(pagePart, rel.Target)
		if err != nil {
			return nil
		}
		key := strings.ToLower(target)
		if _, exists := p.pagePkg.parts[key]; !exists && !seen[key] {
			seen[key] = true
			missing = append(missing, key)
		}
	}
	return missing
}

// streamCollectResourceParts 提取单页资源图中全部直接与间接必需资源的规范化去重并按字典序稳定排列的部件URI列表
// 入参: graph 页面资源图, format 文档方言, names 包内原始规范部件名映射
// 返回: []string 规范资源部件URI列表
func streamCollectResourceParts(graph *resourceGraph, format Format, names map[string]string) []string {
	if graph == nil {
		return nil
	}
	resources, err := collectRequiredResources(graph, format)
	if err != nil || len(resources) == 0 {
		return nil
	}
	seen := make(map[string]bool, len(resources))
	parts := make([]string, 0, len(resources))
	for _, dep := range resources {
		key := strings.ToLower(dep.Part)
		if !seen[key] {
			seen[key] = true
			name := names[key]
			if name == "" {
				name = dep.Part
			}
			parts = append(parts, name)
		}
	}
	slices.Sort(parts)
	return parts
}

// emitReadyPages 按当前索引交付依赖完整的页面，缓存缺失必需资源清单与已校验状态以消除重复全解析
// 入参: name 当前到达或已消费的部件名
// 返回: error 页面、资源、预算或回调错误
func (p *streamPackage) emitReadyPages(name string) error {
	if p.options.OnPage == nil || p.index == nil {
		return nil
	}
	if err := p.releaseProcessed(); err != nil {
		return err
	}
	if p.pageHold {
		return nil
	}
	nameKey := strings.ToLower(name)
	if len(p.pageMissing) != 0 {
		if p.pageMissing[nameKey] {
			_, complete := p.pagePkg.parts[nameKey]
			part := p.parts[nameKey]
			relationUpdated := opcRelationshipName(nameKey) && part != nil && part.relations != nil && !part.relations.deferred
			pageClosed := part != nil && part.page != nil && part.page.closed && !part.page.deferred
			if complete || relationUpdated || pageClosed {
				delete(p.pageMissing, nameKey)
			}
		}
		if len(p.pageMissing) != 0 {
			return nil
		}
	} else if len(p.pageWait) != 0 && !p.pageWait[nameKey] {
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
				p.pageMissing = map[string]bool{key: true}
				p.pageWait = nil
				return nil
			}
		}
		var parsed *Page
		if !p.pageValidated {
			if missing := p.streamPageMissingResources(p.pages); len(missing) != 0 {
				p.pageMissing = make(map[string]bool, len(missing))
				for _, item := range missing {
					p.pageMissing[item] = true
				}
				p.pageWait = nil
				return nil
			}
			p.pageWait = make(map[string]bool)
			var err error
			parsed, err = p.index.Page(p.context, p.pages)
			if err != nil {
				if errors.Is(err, ErrInvalid) || errors.Is(err, ErrUnsupported) || errors.Is(err, fs.ErrNotExist) {
					if len(p.pageWait) == 0 {
						p.pageHold = true
					} else {
						p.pageMissing = p.pageWait
					}
					p.pageWait = nil
					return nil
				}
				p.pageWait = nil
				return err
			}
			p.pageWait = nil
			p.pageMissing = nil
			p.pageValidated = true
			p.pageResources = streamCollectResourceParts(parsed.resources, p.index.format, p.index.pkg.names)
		}
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
		if err := p.notifyPage(p.index, p.pages, parsed); err != nil {
			return err
		}
		p.pages++
		p.pageValidated = false
		p.pageResources = nil
		p.pageWait = nil
		p.pageMissing = nil
		if err := p.advanceDocumentEvents(p.index, false); err != nil {
			return err
		}
	}
	return nil
}

// notifyPage 创建仅供本次回调使用的页面视图，记录交付状态并在纯前向消费模式下回收已消费页面存储
// 入参: source 当前文档索引, index 页面序号, parsed 可选已解析页面，用于复用资源清单
// 返回: error 回调或取消错误
func (p *streamPackage) notifyPage(source *Reader, index int, parsed *Page) error {
	p.pageWait = nil
	if err := p.advanceDocumentEvents(source, false); err != nil {
		return err
	}
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
	if err := p.ensureDocumentStarted(source, docIndex); err != nil {
		return err
	}
	tickets, err := source.pageTicketTargets(p.context, index)
	if err != nil {
		return err
	}
	pageKey := strings.ToLower(reference.Part)
	_, partComplete := source.pkg.parts[pageKey]
	relsPart := createdRelationshipPart(reference.Part)
	relsKey := strings.ToLower(relsPart)
	_, relsComplete := source.pkg.parts[relsKey]
	relsCount := 0
	if rels, relErr := source.pkg.relationshipsContext(p.context, reference.Part); relErr == nil {
		relsCount = len(rels)
	}
	resources := p.pageResources
	if len(resources) == 0 && parsed != nil {
		resources = streamCollectResourceParts(parsed.resources, source.format, source.pkg.names)
	}
	resources = slices.Clone(resources)
	progress := StreamProgress{
		BytesRead:          p.input.count,
		DeliveredPages:     index + 1,
		DiscoveredPages:    len(source.pages),
		DeliveredDocuments: p.deliveredDocuments,
	}
	page := &StreamPage{Index: index, DocumentPart: docPart, Reference: reference, view: &streamPageView{reader: view, owner: p, format: source.format, index: index, documentIndex: docIndex, pageIndex: pageIndex, resources: resources, progress: progress, streamIncomplete: source == p.index && (!p.centralVerified || p.reclaimed), context: p.context}}
	if err := p.options.OnPage(p.context, page); err != nil {
		return err
	}
	if err := checkContext(p.context); err != nil {
		return err
	}
	if p.consumeOnly {
		if !p.deliveredJobSet {
			p.deliveredJobSet = true
			p.deliveredJobTicket = tickets[0]
		}
		if p.deliveredDocTickets == nil {
			p.deliveredDocTickets = make(map[int]string)
		}
		if _, recorded := p.deliveredDocTickets[docIndex]; !recorded {
			p.deliveredDocTickets[docIndex] = tickets[1]
		}
		if pagePart := p.parts[pageKey]; pagePart != nil {
			pagePart.pageDelivered = true
			relsClosed := relsComplete
			if rp := p.parts[relsKey]; rp != nil && rp.relations != nil && rp.relations.closed && !rp.relations.deferred {
				relsClosed = true
			}
			pagePart.deliveredRelsClosed = relsClosed
			if !relsClosed {
				pagePart.deliveredPageTicket = tickets[2]
			}
		}
	} else {
		resourceKeys := make([]string, len(resources))
		for i, res := range resources {
			resourceKeys[i] = strings.ToLower(res)
		}
		p.deliveredPages = append(p.deliveredPages, streamDeliveredPage{
			partComplete:  partComplete,
			relsPart:      relsPart,
			relsComplete:  relsComplete,
			relsCount:     relsCount,
			resourceParts: resourceKeys,
			tickets:       tickets,
		})
	}
	if err := p.reclaimDeliveredPage(source, reference.Part, docIndex, pageIndex); err != nil {
		return err
	}
	return p.releaseProcessed()
}

// pageNeedsFinalValidation 检查已流式交付页面在EOF前是否发生了可能影响校验结果的新增或变更
// 入参: r 最终阅读器, index 页面序号, delivered 流式交付时记录的状态
// 返回: bool 是否需要执行最终r.Page全量复检
func (p *streamPackage) pageNeedsFinalValidation(r *Reader, index int, delivered streamDeliveredPage) bool {
	if !delivered.partComplete {
		return true
	}
	relsKey := strings.ToLower(delivered.relsPart)
	_, hasFinalRels := r.pkg.parts[relsKey]
	if !delivered.relsComplete {
		if hasFinalRels {
			return true
		}
	} else if !hasFinalRels {
		return true
	} else if rels, err := r.pkg.relationshipsContext(p.context, r.pages[index].Part); err != nil || len(rels) != delivered.relsCount {
		return true
	}
	for _, resPart := range delivered.resourceParts {
		resRelsKey := strings.ToLower(createdRelationshipPart(resPart))
		if _, hasResRels := r.pkg.parts[resRelsKey]; hasResRels {
			return true
		}
	}
	return false
}

// finishPages 用最终索引核对已交付页面并跳过未发生新变更页的重复全解析，再交付尚未就绪页面
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
	if p.discard != nil && p.discard.target != "" && !p.discard.loaded {
		if _, err := r.DiscardControl(p.context); err != nil {
			return err
		}
		p.discard.loaded = true
	}
	if err := p.releaseProcessed(); err != nil {
		return err
	}
	for index := range r.pages {
		if err := checkContext(p.context); err != nil {
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
			if !p.consumeOnly {
				if index >= len(p.deliveredPages) || !slices.Equal(p.deliveredPages[index].tickets, tickets) {
					return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
				}
				if p.pageNeedsFinalValidation(r, index, p.deliveredPages[index]) {
					if _, err := r.Page(p.context, index); err != nil {
						return err
					}
				}
			} else {
				_, docIndex, _ := r.pageLocation(index)
				if p.deliveredJobSet && tickets[0] != p.deliveredJobTicket {
					return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
				}
				if deliveredDoc, ok := p.deliveredDocTickets[docIndex]; ok && tickets[1] != deliveredDoc {
					return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
				}
				if pagePart := p.parts[strings.ToLower(r.pages[index].Part)]; pagePart != nil && pagePart.pageDelivered && !pagePart.deliveredRelsClosed && tickets[2] != pagePart.deliveredPageTicket {
					return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
				}
			}
			continue
		}
		parsed, err := r.Page(p.context, index)
		if err != nil {
			return err
		}
		if err := p.notifyPage(r, index, parsed); err != nil {
			return err
		}
		p.pages++
		if err := p.advanceDocumentEvents(r, true); err != nil {
			return err
		}
	}
	return p.releaseProcessed()
}

// streamPotentialPrintTicketMedia 判断内容类型声明在当前方言下是否可能表示打印票据部件
// 入参: format 文档方言, media 已解析的媒体类型字符串
// 返回: bool 是否可能用于打印票据
func streamPotentialPrintTicketMedia(format Format, media string) bool {
	base := opcMediaTypeBase(media)
	if base == "" {
		return false
	}
	if strings.EqualFold(base, printTicketType) {
		return true
	}
	if format != FormatOpenXPS {
		return false
	}
	if strings.EqualFold(base, printTicket2Type) {
		return true
	}
	if standardResourceMedia(base) != 0 {
		return false
	}
	lower := strings.ToLower(base)
	for _, prefix := range [...]string{"image/", "font/", "audio/", "video/", "model/", "application/font-", "application/x-font-"} {
		if strings.HasPrefix(lower, prefix) {
			return false
		}
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
		"application/vnd.ms-printing.printcapabilities+xml",
		"application/vnd.ms-printschemacapabilities+xml",
		"application/vnd.ms-printdevicecapabilities+xml",
		"application/vnd.iccprofile",
		"application/pdf",
		"application/zip",
		"application/gzip",
		"application/x-zip-compressed",
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

// streamPageTicketsReady 按TicketPolicy检查页面三级关系及打印票据部件是否就绪
// 入参: index 待交付页面序号
// 返回: []string 等待到达的部件键列表, bool 是否遇到确定错误需暂缓至最终校验, error 预算或取消错误
func (p *streamPackage) streamPageTicketsReady(index int) ([]string, bool, error) {
	pagePart := p.index.pages[index].Part
	docPart, _, _ := p.index.pageLocation(index)
	if docPart == "" {
		return nil, false, nil
	}
	mayTicket := p.mayHavePrintTicket()
	strict := p.options.TicketPolicy != StreamTicketsInterleaved
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
		if relsPart := p.parts[relsKey]; relsPart != nil && !relsPart.reclaimed {
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
			} else if !relsPart.relations.closed && mayTicket && strict {
				waits = append(waits, relsKey)
			}
			continue
		}
		if strict && mayTicket && p.streamRelsPossible(relsKey) {
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
		relations, err := r.pkg.relationshipsContext(ctx, canonical)
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

// streamReadPrintSettingsCached 在流式视图读锁内合并基础设置与三级PrintTicket，并复用作业与文档级已解析票据缓存
// 入参: ctx 取消Context, index 页面序号, defaults 基础设置, options 输出过滤及资源参数, owner 流式包缓存持有者，可为nil
// 返回: *PrintSettings 独立合并设置, error 状态、读取、合并或取消错误
func (r *Reader) streamReadPrintSettingsCached(ctx context.Context, index int, defaults *PrintSettings, options *PrintSettingsOptions, owner *streamPackage) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if err := checkContext(configuration.context); err != nil {
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
	outputScope := configuration.Scope
	configuration.Scope = PrintScopeUnknown
	empty := &PrintSettings{Version: 1}
	if defaults == nil {
		defaults = empty
	}
	result, err := validatePrintSettingsModel(defaults, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsOutputBudget(result, configuration, printDocumentTicket); err != nil {
		return nil, err
	}
	sources := [3]struct {
		part  string
		scope PrintScope
	}{
		{r.sequence, PrintScopeJob},
		{docPart, PrintScopeDocument},
		{pagePart, PrintScopePage},
	}
	remaining := min(r.limits.MaxPackageBytes, r.limits.MaxMetadataBytes, configuration.Limits.MaxPackageBytes, configuration.Limits.MaxMetadataBytes)
	for _, source := range sources {
		if err := checkContext(configuration.context); err != nil {
			return nil, err
		}
		canonical, err := opcPartName(source.part)
		if err != nil {
			return nil, err
		}
		relations, err := r.pkg.relationshipsContext(configuration.context, canonical)
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
		partName := r.pkg.names[strings.ToLower(part)]
		if partName == "" {
			partName = part
		}
		local := configuration.PrintSettingsOptions
		local.Scope = source.scope
		cacheKey := streamTicketCacheKey{
			part:                 strings.ToLower(part),
			scope:                source.scope,
			limits:               local.Limits,
			maxNumericDigits:     local.MaxNumericDigits,
			maxOptionComparisons: local.MaxOptionComparisons,
		}
		var settings *PrintSettings
		if owner != nil && source.scope != PrintScopePage {
			if cached, hit := owner.getCachedTicket(cacheKey); hit {
				maxSingle := min(remaining, r.limits.MaxPartBytes, configuration.Limits.MaxPartBytes)
				if cached.size > maxSingle {
					return nil, &PartError{Part: partName, Err: fmt.Errorf("%w: print ticket bytes", ErrLimit)}
				}
				remaining -= cached.size
				settings = cached.settings
			}
		}
		if settings == nil {
			typeName, err := r.pkg.contentType(part)
			if err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			sourceName := r.pkg.names[strings.ToLower(canonical)]
			if sourceName == "" {
				sourceName = canonical
			}
			ticket := PrintTicket{Source: sourceName, Part: partName, Scope: source.scope, ContentType: typeName}
			if err := r.readPrintTicketData(&ticket, min(remaining, r.limits.MaxPartBytes, configuration.Limits.MaxPartBytes), configuration.context); err != nil {
				return nil, err
			}
			remaining -= int64(len(ticket.Data))
			settings, err = ticket.Settings(configuration.context, &local)
			if err != nil {
				return nil, &PartError{Part: ticket.Part, Err: err}
			}
			if owner != nil && source.scope != PrintScopePage {
				owner.putCachedTicket(cacheKey, settings, int64(len(ticket.Data)))
			}
		}
		result, err = mergeStreamPrintSettings(configuration.context, result, settings, configuration, PrintScopeUnknown)
		if err != nil {
			return nil, &PartError{Part: partName, Err: err}
		}
	}
	if outputScope != PrintScopeUnknown {
		configuration.Scope = outputScope
		filtered, err := validatePrintSettingsModel(result, configuration, printDocumentTicket)
		if err != nil {
			return nil, err
		}
		if err := validatePrintSettingsOutputBudget(filtered, configuration, printDocumentTicket); err != nil {
			return nil, err
		}
		return filtered, nil
	}
	return result, checkContext(configuration.context)
}

// getCachedTicket 并发安全读取作业或文档级已解析打印设置缓存
// 入参: key 票据缓存键
// 返回: streamCachedTicket 缓存设置与字节数, bool 是否命中
func (p *streamPackage) getCachedTicket(key streamTicketCacheKey) (streamCachedTicket, bool) {
	p.ticketMu.RLock()
	defer p.ticketMu.RUnlock()
	if p.ticketCache == nil {
		return streamCachedTicket{}, false
	}
	value, ok := p.ticketCache[key]
	return value, ok
}

// putCachedTicket 并发安全写入作业或文档级已解析打印设置缓存
// 入参: key 票据缓存键, settings 已校验只读设置, size 原始票据字节数
func (p *streamPackage) putCachedTicket(key streamTicketCacheKey, settings *PrintSettings, size int64) {
	p.ticketMu.Lock()
	defer p.ticketMu.Unlock()
	if p.ticketCache == nil {
		p.ticketCache = make(map[streamTicketCacheKey]streamCachedTicket)
	}
	p.ticketCache[key] = streamCachedTicket{settings: settings, size: size}
}

// evictDocumentTicketCache 清理文档级打印设置缓存条目以在多文档流式作业中控制内存
func (p *streamPackage) evictDocumentTicketCache() {
	p.ticketMu.Lock()
	defer p.ticketMu.Unlock()
	for key := range p.ticketCache {
		if key.scope == PrintScopeDocument {
			delete(p.ticketCache, key)
		}
	}
}

// streamReadCorePropertiesPart 直接按已确定的核心属性部件URI读取并校验核心属性，支持根关系已回收的后置到达场景
// 入参: ctx 取消Context, part 核心属性部件URI
// 返回: *CoreProperties 独立核心属性或nil, bool 是否已到达, error 类型、解析、预算或取消错误
func (r *Reader) streamReadCorePropertiesPart(ctx context.Context, part string) (*CoreProperties, bool, error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, err
	}
	key := strings.ToLower(part)
	if _, exists := r.pkg.parts[key]; !exists {
		return nil, false, nil
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	if !strings.EqualFold(media, opcCoreType) {
		return nil, false, &PartError{Part: part, Err: fmt.Errorf("%w: core properties content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, key, min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes))
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	root, content, err := decodeXMLContent(data, r.limits, ctx)
	if err == nil {
		var result *CoreProperties
		result, err = parseCorePropertiesContent(root, content)
		if err == nil {
			if err := checkContext(ctx); err != nil {
				return nil, false, err
			}
			result.Part = part
			return result, true, nil
		}
	}
	return nil, false, &PartError{Part: part, Err: err}
}

// streamCorePropertiesTarget 从包根关系列表中解析唯一的核心属性目标部件URI，未关联返回空字符串
// 入参: relations 包根关系列表
// 返回: string 目标部件URI, error 多重关系、外部目标或非法URI错误
func streamCorePropertiesTarget(relations []Relationship) (string, error) {
	part := ""
	for _, relation := range relations {
		if relation.Type != opcCoreRel {
			continue
		}
		if part != "" {
			return "", fmt.Errorf("%w: multiple package core properties relationships", ErrInvalid)
		}
		if relation.TargetMode != TargetModeInternal {
			return "", fmt.Errorf("%w: external package core properties", ErrInvalid)
		}
		var err error
		part, err = resolvePart("/", relation.Target)
		if err != nil {
			return "", err
		}
	}
	return part, nil
}

// streamReadCorePropertiesIfPresent 若包级核心属性已关联且目标部件已到达则解析返回，尚未到达时返回nil
// 入参: ctx 取消Context
// 返回: *CoreProperties 独立核心属性或nil, bool 是否命中已到达核心属性, error 关系、类型、解析、预算或取消错误
func (r *Reader) streamReadCorePropertiesIfPresent(ctx context.Context) (*CoreProperties, bool, error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, "/")
	if err != nil {
		return nil, false, &PartError{Part: "/", Err: err}
	}
	part, err := streamCorePropertiesTarget(relations)
	if err != nil || part == "" {
		return nil, false, err
	}
	return r.streamReadCorePropertiesPart(ctx, part)
}

// streamReadStoryFragmentsIfPresent 若指定页面已关联故事片段部件且目标已到达则解析返回，未关联或尚未到达时返回nil
// 入参: ctx 取消Context, pagePart 页面部件URI
// 返回: *StoryFragments 独立片段数据或nil, error 关系、媒体类型、结构、预算或取消错误
func (r *Reader) streamReadStoryFragmentsIfPresent(ctx context.Context, pagePart string) (*StoryFragments, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, pagePart)
	if err != nil {
		return nil, &PartError{Part: pagePart, Err: err}
	}
	part := ""
	typeURI := formatNamespace(r.format) + "/storyfragments"
	for _, relation := range relations {
		if relation.Type != typeURI {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return nil, &PartError{Part: pagePart, Err: fmt.Errorf("%w: external StoryFragments part", ErrInvalid)}
		}
		target, err := resolvePart(pagePart, relation.Target)
		if err != nil {
			return nil, &PartError{Part: pagePart, Err: err}
		}
		if part != "" && !strings.EqualFold(part, target) {
			return nil, &PartError{Part: pagePart, Err: fmt.Errorf("%w: multiple distinct StoryFragments parts", ErrInvalid)}
		}
		part = target
	}
	if part == "" {
		return nil, nil
	}
	key := strings.ToLower(part)
	if _, exists := r.pkg.parts[key]; !exists {
		return nil, nil
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if !matchStandardContentType(r.format, media, fixedContentType("storyfragments")) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: StoryFragments content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, key, r.limits.MaxPartBytes)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	root, err := decodeXMLVisit(data, r.limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err == nil {
		root, err = preprocessXMLContext(root, []string{structureNamespace(r.format)}, ctx)
	}
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if root.Name.Space != structureNamespace(r.format) || root.Name.Local != "StoryFragments" {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%w: expected StoryFragments root", ErrInvalid)}
	}
	result, err := parseStoryFragments(root, structureNamespace(r.format), r.limits.MaxXMLDepth)
	if err != nil {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: err}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	result.Part = part
	return result, nil
}

// streamReadDocumentStructureTarget 解析文档关系中的DocumentStructure目标部件URI，未关联返回空字符串
// 入参: docPart 固定文档部件URI, relations 文档关系列表, format 文档方言
// 返回: string 目标部件URI, error 外部目标、非法URI或多目标错误
func streamReadDocumentStructureTarget(docPart string, relations []Relationship, format Format) (string, error) {
	part := ""
	typeURI := formatNamespace(format) + "/documentstructure"
	for _, relation := range relations {
		if relation.Type != typeURI {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return "", &PartError{Part: docPart, Err: fmt.Errorf("%w: external DocumentStructure part", ErrInvalid)}
		}
		target, err := resolvePart(docPart, relation.Target)
		if err != nil {
			return "", &PartError{Part: docPart, Err: err}
		}
		if part != "" && !strings.EqualFold(part, target) {
			return "", &PartError{Part: docPart, Err: fmt.Errorf("%w: multiple distinct DocumentStructure parts", ErrInvalid)}
		}
		part = target
	}
	return part, nil
}

// streamReadDocumentStructurePart 直接按已确定的结构部件URI读取并校验文档结构，支持文档关系已被回收的后置到达场景
// 入参: ctx 取消Context, part 文档结构部件URI, pageLimit 当前允许校验的故事页码上限
// 返回: *DocumentStructure 独立文档结构或nil, bool 是否已到达, int 故事引用的最大页码, error 类型、格式、预算或取消错误
func (r *Reader) streamReadDocumentStructurePart(ctx context.Context, part string, pageLimit int) (*DocumentStructure, bool, int, error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, 0, err
	}
	key := strings.ToLower(part)
	if _, exists := r.pkg.parts[key]; !exists {
		return nil, false, 0, nil
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, false, 0, &PartError{Part: part, Err: err}
	}
	if !matchStandardContentType(r.format, media, fixedContentType("documentstructure")) {
		return nil, false, 0, &PartError{Part: part, Err: fmt.Errorf("%w: DocumentStructure content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, key, r.limits.MaxPartBytes)
	if err != nil {
		return nil, false, 0, &PartError{Part: part, Err: err}
	}
	root, err := decodeXMLVisit(data, r.limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err == nil {
		root, err = preprocessXMLContext(root, []string{structureNamespace(r.format)}, ctx)
	}
	if err != nil {
		return nil, false, 0, &PartError{Part: part, Err: err}
	}
	if root.Name.Space != structureNamespace(r.format) || root.Name.Local != "DocumentStructure" {
		return nil, false, 0, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%w: expected DocumentStructure root", ErrInvalid)}
	}
	result, err := parseDocumentStructure(root, structureNamespace(r.format), pageLimit)
	if err != nil {
		return nil, false, 0, &PartError{Part: part, Element: root.Name.Local, Err: err}
	}
	if err := checkContext(ctx); err != nil {
		return nil, false, 0, err
	}
	result.Part = part
	maxPage := 0
	for _, story := range result.Stories {
		for _, frag := range story.Fragments {
			if frag.PageNumber > maxPage {
				maxPage = frag.PageNumber
			}
		}
	}
	return result, true, maxPage, nil
}

// streamReadDocumentStructureIfPresent 若指定固定文档已关联结构部件且目标已到达则解析返回，尚未到达时返回nil
// 入参: ctx 取消Context, docPart 固定文档部件URI, pageLimit 当前允许校验的故事页码上限
// 返回: *DocumentStructure 独立文档结构或nil, bool 是否已到达, int 故事引用的最大页码, error 关系、格式、预算或取消错误
func (r *Reader) streamReadDocumentStructureIfPresent(ctx context.Context, docPart string, pageLimit int) (*DocumentStructure, bool, int, error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, 0, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, docPart)
	if err != nil {
		return nil, false, 0, &PartError{Part: docPart, Err: err}
	}
	part, err := streamReadDocumentStructureTarget(docPart, relations, r.format)
	if err != nil || part == "" {
		return nil, false, 0, err
	}
	return r.streamReadDocumentStructurePart(ctx, part, pageLimit)
}

// streamReadJobPrintSettingsIfPresent 若作业级PrintTicket已关联且目标部件已到达则解析返回并写入缓存
// 入参: ctx 取消Context, owner 可选流式包缓存持有者
// 返回: *PrintSettings 独立作业打印设置或nil, string 命中的票据部件URI, bool 是否已到达, error 关系、读取、格式、预算或取消错误
func (r *Reader) streamReadJobPrintSettingsIfPresent(ctx context.Context, owner *streamPackage) (*PrintSettings, string, bool, error) {
	if err := checkContext(ctx); err != nil {
		return nil, "", false, err
	}
	target := ""
	if owner != nil && owner.jobTicketTarget != "" {
		target = owner.jobTicketTarget
	} else {
		relations, err := r.pkg.relationshipsContext(ctx, r.sequence)
		if err != nil {
			if errors.Is(err, ErrNotFound) {
				return nil, "", false, nil
			}
			return nil, "", false, err
		}
		target, err = printTicketTarget(r.sequence, relations, r.format)
		if err != nil {
			return nil, "", false, err
		}
		if owner != nil && target != "" {
			owner.jobTicketTarget = target
		}
	}
	if target == "" {
		return nil, "", false, nil
	}
	key := strings.ToLower(target)
	if _, exists := r.pkg.parts[key]; !exists {
		return nil, target, false, nil
	}
	opts := PrintSettingsOptions{Scope: PrintScopeJob, Limits: r.limits}
	normalized, err := printSettingsOptions(ctx, &opts)
	if err != nil {
		return nil, target, false, err
	}
	cacheKey := streamTicketCacheKey{
		part:                 key,
		scope:                PrintScopeJob,
		limits:               normalized.Limits,
		maxNumericDigits:     normalized.MaxNumericDigits,
		maxOptionComparisons: normalized.MaxOptionComparisons,
	}
	if owner != nil {
		if cached, hit := owner.getCachedTicket(cacheKey); hit {
			return printCloneSettings(cached.settings), target, true, nil
		}
	}
	typeName, err := r.pkg.contentType(target)
	if err != nil {
		return nil, target, false, &PartError{Part: target, Err: err}
	}
	partName := r.pkg.names[key]
	if partName == "" {
		partName = target
	}
	sourceName := r.pkg.names[strings.ToLower(r.sequence)]
	if sourceName == "" {
		sourceName = r.sequence
	}
	ticket := PrintTicket{Source: sourceName, Part: partName, Scope: PrintScopeJob, ContentType: typeName}
	if err := r.readPrintTicketData(&ticket, min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes, r.limits.MaxPackageBytes), ctx); err != nil {
		return nil, target, false, err
	}
	settings, err := ticket.Settings(ctx, &normalized.PrintSettingsOptions)
	if err != nil {
		return nil, target, false, &PartError{Part: ticket.Part, Err: err}
	}
	if owner != nil {
		owner.putCachedTicket(cacheKey, settings, int64(len(ticket.Data)))
		if tp := owner.parts[key]; tp != nil {
			tp.ticketVerifiedScopes |= streamTicketScopeBit(PrintScopeJob)
		}
	}
	return printCloneSettings(settings), target, true, nil
}

// cloneOptionalString 深拷贝可选字符串指针，确保调用方修改不影响流式缓存
// 入参: value 原始指针
// 返回: *string 独立指针副本
func cloneOptionalString(value *string) *string {
	if value == nil {
		return nil
	}
	copied := *value
	return &copied
}

// cloneCoreProperties 构造CoreProperties的完整独立深拷贝
// 入参: src 原始核心属性
// 返回: *CoreProperties 独立深拷贝
func cloneCoreProperties(src *CoreProperties) *CoreProperties {
	if src == nil {
		return nil
	}
	dst := &CoreProperties{
		Part:           src.Part,
		Category:       cloneOptionalString(src.Category),
		ContentStatus:  cloneOptionalString(src.ContentStatus),
		ContentType:    cloneOptionalString(src.ContentType),
		Created:        cloneOptionalString(src.Created),
		Creator:        cloneOptionalString(src.Creator),
		Description:    cloneOptionalString(src.Description),
		Identifier:     cloneOptionalString(src.Identifier),
		Keywords:       cloneOptionalString(src.Keywords),
		Language:       cloneOptionalString(src.Language),
		LastModifiedBy: cloneOptionalString(src.LastModifiedBy),
		LastPrinted:    cloneOptionalString(src.LastPrinted),
		Modified:       cloneOptionalString(src.Modified),
		Revision:       cloneOptionalString(src.Revision),
		Subject:        cloneOptionalString(src.Subject),
		Title:          cloneOptionalString(src.Title),
		Version:        cloneOptionalString(src.Version),
	}
	if len(src.KeywordValues) != 0 {
		dst.KeywordValues = make([]CoreKeyword, len(src.KeywordValues))
		for i, item := range src.KeywordValues {
			dst.KeywordValues[i] = CoreKeyword{Value: item.Value, Language: cloneOptionalString(item.Language), IsText: item.IsText}
		}
	}
	if len(src.Languages) != 0 {
		dst.Languages = maps.Clone(src.Languages)
	}
	return dst
}

// cloneDocumentStructure 构造DocumentStructure的完整独立深拷贝
// 入参: src 原始文档结构
// 返回: *DocumentStructure 独立深拷贝
func cloneDocumentStructure(src *DocumentStructure) *DocumentStructure {
	if src == nil {
		return nil
	}
	dst := &DocumentStructure{Part: src.Part}
	if src.Outline != nil {
		outline := &DocumentOutline{Language: src.Outline.Language}
		if len(src.Outline.Entries) != 0 {
			outline.Entries = make([]OutlineEntry, len(src.Outline.Entries))
			for i, entry := range src.Outline.Entries {
				outline.Entries[i] = OutlineEntry{Level: entry.Level, Target: entry.Target, Description: entry.Description, Language: cloneOptionalString(entry.Language)}
			}
		}
		dst.Outline = outline
	}
	if len(src.Stories) != 0 {
		dst.Stories = make([]Story, len(src.Stories))
		for i, story := range src.Stories {
			copied := Story{Name: story.Name}
			if len(story.Fragments) != 0 {
				copied.Fragments = make([]StoryFragmentReference, len(story.Fragments))
				for j, frag := range story.Fragments {
					copied.Fragments[j] = StoryFragmentReference{PageNumber: frag.PageNumber, FragmentName: cloneOptionalString(frag.FragmentName)}
				}
			}
			dst.Stories[i] = copied
		}
	}
	return dst
}

// emitMetadataCallbacks 在作业票据、核心属性或文档结构就绪时立即触发对应流式回调并缓存结果
// 返回: error 解析、预算、回调或取消错误
func (p *streamPackage) emitMetadataCallbacks() error {
	if p.pagePkg == nil {
		return nil
	}
	if p.options.OnJobPrintTicket != nil && !p.jobTicketDelivered && p.index != nil {
		if err := checkContext(p.context); err != nil {
			return err
		}
		settings, target, arrived, err := p.index.streamReadJobPrintSettingsIfPresent(p.context, p)
		if err != nil {
			return err
		}
		if arrived {
			p.jobTicketDelivered = true
			if err := p.options.OnJobPrintTicket(p.context, settings); err != nil {
				return err
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
			if p.consumeOnly && p.ownedMemory != nil && p.options.OnPage == nil && target != "" {
				p.requestReclaimPart(strings.ToLower(target))
			}
		}
	}
	if p.options.OnCoreProperties != nil && !p.corePropsDelivered {
		if err := checkContext(p.context); err != nil {
			return err
		}
		probe := &Reader{pkg: p.pagePkg, limits: p.options.Limits}
		var props *CoreProperties
		var arrived bool
		var err error
		if p.corePropsTarget != "" {
			props, arrived, err = probe.streamReadCorePropertiesPart(p.context, p.corePropsTarget)
		} else {
			props, arrived, err = probe.streamReadCorePropertiesIfPresent(p.context)
		}
		if err != nil {
			return err
		}
		if arrived {
			p.corePropsDelivered = true
			p.corePropsCached = props
			if err := p.options.OnCoreProperties(p.context, cloneCoreProperties(props)); err != nil {
				return err
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
			if p.consumeOnly && p.ownedMemory != nil {
				p.requestReclaimPart(strings.ToLower(props.Part))
			}
		}
	}
	if p.options.OnDocumentStructure != nil && p.index != nil {
		if p.docStructDelivered == nil {
			p.docStructDelivered = make(map[int]bool)
			p.docStructCached = make(map[int]*DocumentStructure)
			p.docStructMaxPage = make(map[int]int)
		}
		for docIdx := range p.index.documents {
			if p.docStructDelivered[docIdx] {
				continue
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
			pageLimit := math.MaxInt32
			if docIdx < p.document {
				pageLimit = len(p.index.documents[docIdx].Pages)
			}
			var ds *DocumentStructure
			var arrived bool
			var maxPage int
			var err error
			docKey := strings.ToLower(p.index.documents[docIdx].Part)
			if target := p.docStructTargets[docKey]; target != "" {
				ds, arrived, maxPage, err = p.index.streamReadDocumentStructurePart(p.context, target, pageLimit)
			} else if docPart := p.parts[docKey]; docPart != nil && !docPart.reclaimed {
				relations, relErr := p.index.pkg.relationshipsContext(p.context, p.index.documents[docIdx].Part)
				if relErr != nil {
					return &PartError{Part: p.index.documents[docIdx].Part, Err: relErr}
				}
				resolvedTarget, targetErr := streamReadDocumentStructureTarget(p.index.documents[docIdx].Part, relations, p.index.format)
				if targetErr != nil {
					return targetErr
				}
				if resolvedTarget != "" {
					if p.docStructTargets == nil {
						p.docStructTargets = make(map[string]string)
					}
					p.docStructTargets[docKey] = resolvedTarget
					ds, arrived, maxPage, err = p.index.streamReadDocumentStructurePart(p.context, resolvedTarget, pageLimit)
				}
			}
			if err != nil {
				return err
			}
			if arrived {
				p.docStructDelivered[docIdx] = true
				if !p.reclaimedDocuments[docIdx] {
					p.docStructCached[docIdx] = ds
				}
				p.docStructMaxPage[docIdx] = maxPage
				delete(p.docStructTargets, docKey)
				if err := p.options.OnDocumentStructure(p.context, docIdx, cloneDocumentStructure(ds)); err != nil {
					return err
				}
				if err := checkContext(p.context); err != nil {
					return err
				}
				if p.consumeOnly && p.ownedMemory != nil {
					p.requestReclaimPart(strings.ToLower(ds.Part))
				}
			}
		}
	}
	return nil
}

// finishMetadataCallbacks 在EOF阶段补发此前因延迟或晚到未能触发的作业票据、核心属性与文档结构回调，并校验故事页码上界
// 入参: r 已完成物理校验的最终阅读器
// 返回: error 解析、页码越界、回调或取消错误
func (p *streamPackage) finishMetadataCallbacks(r *Reader) error {
	if p.options.OnJobPrintTicket != nil && !p.jobTicketDelivered {
		if err := checkContext(p.context); err != nil {
			return err
		}
		settings, _, arrived, err := r.streamReadJobPrintSettingsIfPresent(p.context, p)
		if err != nil {
			return err
		}
		if arrived {
			p.jobTicketDelivered = true
			if err := p.options.OnJobPrintTicket(p.context, settings); err != nil {
				return err
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
		}
	}
	if p.options.OnCoreProperties != nil && !p.corePropsDelivered {
		if err := checkContext(p.context); err != nil {
			return err
		}
		props, err := r.CoreProperties(p.context)
		if err != nil {
			return err
		}
		if props != nil {
			p.corePropsDelivered = true
			p.corePropsCached = props
			if err := p.options.OnCoreProperties(p.context, cloneCoreProperties(props)); err != nil {
				return err
			}
			if err := checkContext(p.context); err != nil {
				return err
			}
		}
	}
	if p.options.OnDocumentStructure != nil {
		for docIdx := range r.documents {
			if err := checkContext(p.context); err != nil {
				return err
			}
			if p.docStructDelivered != nil && p.docStructDelivered[docIdx] {
				if p.docStructMaxPage[docIdx] > len(r.documents[docIdx].Pages) {
					return fmt.Errorf("%w: story page %d outside its fixed document", ErrInvalid, p.docStructMaxPage[docIdx])
				}
				continue
			}
			ds, err := r.DocumentStructure(p.context, docIdx)
			if err != nil {
				return err
			}
			if ds != nil {
				if p.docStructDelivered == nil {
					p.docStructDelivered = make(map[int]bool)
				}
				p.docStructDelivered[docIdx] = true
				if err := p.options.OnDocumentStructure(p.context, docIdx, cloneDocumentStructure(ds)); err != nil {
					return err
				}
				if err := checkContext(p.context); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

// selectedPage 对索引中的未完成页面启用增量处理，完整页面沿用现有读取路径
// 入参: name 部件URI, media 声明类型
// 返回: bool 是否为当前索引页面
func (p *streamPackage) selectedPage(name, media string) bool {
	key := strings.ToLower(name)
	if p.options.OnPage == nil || p.index == nil || !p.pageNames[key] || !matchStandardContentType(p.index.format, media, fixedContentType("fixedpage")) {
		return false
	}
	part := p.parts[key]
	return part != nil && !part.reclaimed && (part.page != nil || part.last < 0 || len(part.entries) != part.last+1)
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
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: p.cloneEventNamespaces(event.Namespaces)}
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
	if !p.needsIndex() || p.index == nil {
		return false
	}
	if strings.EqualFold(name, p.index.sequence) {
		return matchStandardContentType(p.index.format, media, fixedContentType("fixeddocumentsequence"))
	}
	return p.documentKeys[strings.ToLower(name)] && matchStandardContentType(p.index.format, media, fixedContentType("fixeddocument"))
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
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: p.cloneEventNamespaces(event.Namespaces)}
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
	if part == nil || part.reclaimed {
		return nil
	}
	media := p.types.declaredContentType(name)
	if !matchStandardContentType(p.index.format, media, fixedContentType(kind)) {
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
	if p.sequenceRead {
		references = p.documents
	} else if sequence.layout != nil && !sequence.layout.deferred {
		references = sequence.layout.documents
		if sequence.layout.closed {
			p.sequenceRead = true
		}
	} else {
		if _, present := p.pagePkg.parts[strings.ToLower(sequence.name)]; !present {
			return nil
		}
		var err error
		references, err = p.index.readDocumentReferences()
		if err != nil {
			return err
		}
		p.sequenceRead = true
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
			finishedDoc := p.document
			if p.docStructMaxPage != nil && p.docStructMaxPage[finishedDoc] > len(doc.Pages) {
				return fmt.Errorf("%w: story page %d outside its fixed document", ErrInvalid, p.docStructMaxPage[finishedDoc])
			}
			p.document++
			if err := p.advanceDocumentEvents(p.index, false); err != nil {
				return err
			}
			if err := p.tryReclaimCompletedDocument(p.index, finishedDoc); err != nil {
				return err
			}
			continue
		}
		if len(p.index.documents) == p.document {
			p.index.documents = append(p.index.documents, Document{Part: name})
			if err := p.advanceDocumentEvents(p.index, false); err != nil {
				return err
			}
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
		finishedDoc := p.document
		if p.docStructMaxPage != nil && p.docStructMaxPage[finishedDoc] > len(doc.Pages) {
			return fmt.Errorf("%w: story page %d outside its fixed document", ErrInvalid, p.docStructMaxPage[finishedDoc])
		}
		p.document++
		if err := p.advanceDocumentEvents(p.index, false); err != nil {
			return err
		}
		if err := p.tryReclaimCompletedDocument(p.index, finishedDoc); err != nil {
			return err
		}
	}
	return nil
}
