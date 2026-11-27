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
	"context"
	"crypto"
	"encoding/xml"
	"fmt"
	"image"
	"io"
	"math/big"
	"slices"
	"strings"
)

// StreamPlanPage 描述输入到流式拼版器的单个源页面序号、归属文档、物理尺寸、可选盒边界及可选页级打印设置
// PageIndex为零基全局页序号，DocumentIndex为零基文档序号，DocumentPageIndex为零基文档内页序号
// Width与Height采用XPS标准的1/96英寸单位，Settings可为已合并页级设置或相对作业默认的增量设置，nil沿用作业默认设置
type StreamPlanPage struct {
	PageIndex         int
	DocumentIndex     int
	DocumentPageIndex int
	Width             float64
	Height            float64
	ContentBox        Rect
	BleedBox          Rect
	HasContentBox     bool
	HasBleedBox       bool
	Settings          *PrintSettings
}

// StreamPrintOptions 设置前向流式有界窗口拼版消费的读取参数、打印计划参数、常驻锁定部件列表与物理纸张回调
// Stream配置输入存储、内存配额与票据等待策略，OnPage非nil时在拼版前按页序交付页面视图；Plan配置默认票据、物理介质、预算与忽略策略
// PinParts指定流式消费全程保持引用计数锁定的包内部件URI列表，防止外部水印字体等资源被自动丢弃或提前回收
// OnSheet在窗口凑满物理纸张时实时交付临时纸张视图，回调返回后自动释放不再被窗口引用的页面与资源存储
// 若有效票据要求逆序、小册子、逐份多副本或非单调页范围，则在完整接收流后于收尾阶段统一编排交付OnSheet
type StreamPrintOptions struct {
	Stream   StreamReadOptions
	Plan     PrintPlanOptions
	PinParts []string
	OnSheet  func(context.Context, *StreamPrintSheet) error
}

// StreamPrintSheet 表示前向流式拼版消费中窗口资源已就绪的临时物理纸张视图，Index为零基纸张序号
// WalkPrintSide、RenderPrintSide、RenderPrintSideDevice、Font、Image、ImageInfo、DecodeImageRows、ReadPart、ColorProfile、ResolveColor、ResolveGradientStops、NewColorResolver、RenderElement、RenderElementMapped与RenderBrushTileWithState仅在OnSheet回调期间可用
// 回调结束后视图自动关闭并回收不再被后续窗口引用的源页面存储，ConsumeStreamPrintPlan成功返回前均为临时结果
type StreamPrintSheet struct {
	Index int
	Sheet PrintSheet
	streamReaderView
}

// streamPendingSheet 保存因等待晚到票据包内ICC部件而暂缓交付的物理纸张与待到达键集合
type streamPendingSheet struct {
	sheet    PrintSheet
	waitKeys map[string]bool
	pinKeys  []string
}

// streamPrintCoordinator 协调前向流页面到达、有界窗口页资源锁定、晚到票据ICC等待、StreamPrintPlanner编排与及时内存回收
type streamPrintCoordinator struct {
	planOptions       PrintPlanOptions
	onSheet           func(context.Context, *StreamPrintSheet) error
	planner           *StreamPrintPlanner
	owner             *streamPackage
	lastDoc           int
	sheetIndex        int
	sigPolicy         PrintSignaturePolicy
	sigVerified       bool
	sigVerifiedPolicy PrintSignaturePolicy
	sigVerifiedOpts   *PrintSignatureOptions
	pinnedByPage      map[int][]string
	pendingSheets     []streamPendingSheet
}

// streamDocumentConfig 保存单个文档在当前作业基线上合并后的有效打印设置与编排参数
type streamDocumentConfig struct {
	settings       *PrintSettings
	docFinishing   PrintFinishing
	finishing      PrintFinishing
	copies         int
	collated       bool
	nup            int
	direction      string
	duplex         PrintDuplex
	manual         bool
	hasDuplex      bool
	separate       bool
	separateCopies bool
	pageRanges     string
	hasPageRanges  bool
	rangeSpans     []printPageRangeSpan
	sheetCopies    int
	needsBuffer    bool
}

// streamBufferedDocument 保存随机访问模式下按文档分组缓冲的轻量页面元数据与文档级编排配置
type streamBufferedDocument struct {
	documentIndex int
	config        streamDocumentConfig
	pages         []printPlanPage
}

// StreamPrintPlanner 基于PrintSchema语义提供纯前向直通、滑动窗口与随机访问回退的流式拼版规划器
// 直通或滑动窗口模式下攒满单张物理纸张即刻产出PrintSheet并清空窗口内存，逆序、小册子、逐份多副本或非单调页范围在Flush或文档边界统一编排输出
type StreamPrintPlanner struct {
	capability         PrintStreamCapability
	options            PrintPlanOptions
	settings           printSettingsConfig
	jobSettings        *PrintSettings
	jobFinishing       PrintFinishing
	jobCopies          int
	jobCollated        bool
	reverseOrder       bool
	jobNUp             int
	jobDirection       string
	jobDuplex          PrintDuplex
	jobManual          bool
	jobHasDuplex       bool
	defaultDoc         streamDocumentConfig
	activeDoc          streamDocumentConfig
	activeDocSet       bool
	activeDocIndex     int
	activeDocPages     []printPlanPage
	readySheets        []PrintSheet
	seenDocs           map[int]bool
	builder            printPlanBuilder
	batch              PrintPlan
	packer             printSheetPacker
	docPageCount       int
	docExplicitPageIdx bool
	totalPushed        int
	bufferedDocs       []streamBufferedDocument
	flushed            bool
}

// NewStreamPrintPlanner 按作业默认打印设置与编排选项创建流式拼版规划器并分析流式可行性模式
// 入参: ctx 取消Context，nil采用Background, defaults 作业级有效或默认打印设置，nil采用空默认设置, options 介质、预算与忽略策略，nil采用默认值
// 返回: *StreamPrintPlanner 独立流式拼版器, error 设置、冲突、预算或取消错误
func NewStreamPrintPlanner(ctx context.Context, defaults *PrintSettings, options *PrintPlanOptions) (*StreamPrintPlanner, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	configuration := DefaultPrintPlanOptions()
	if options != nil {
		configuration = *options
		if configuration.MaxSheets == 0 {
			configuration.MaxSheets = 1 << 16
		}
		if configuration.MaxPlacements == 0 {
			configuration.MaxPlacements = 1 << 18
		}
		if configuration.MaxWork == 0 {
			configuration.MaxWork = 1 << 28
		}
	}
	if configuration.MaxSheets < 1 || configuration.MaxPlacements < 1 || configuration.Print.Settings.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: stream print planner options", ErrInvalid)
	}
	if err := validatePrintMedia(configuration.Print.Media); err != nil {
		return nil, err
	}
	settingsCfg, err := printSettingsOptions(ctx, &configuration.Print.Settings)
	if err != nil {
		return nil, err
	}
	settingsCfg.ignoreUnsupported = configuration.IgnoreUnsupportedFeatures || configuration.Print.IgnoreUnsupportedFeatures
	jobSettings := &PrintSettings{Version: 1}
	if configuration.Print.Defaults != nil {
		jobSettings, err = mergeStreamPrintSettings(ctx, jobSettings, configuration.Print.Defaults, settingsCfg, PrintScopeUnknown)
		if err != nil {
			return nil, err
		}
	}
	if defaults != nil {
		jobSettings, err = mergeStreamPrintSettings(ctx, jobSettings, defaults, settingsCfg, PrintScopeUnknown)
		if err != nil {
			return nil, err
		}
	}
	if settingsCfg.ignoreUnsupported {
		jobSettings = printStripPrivateExtensions(jobSettings)
	}
	capability, err := AnalyzePrintStreamCapability(ctx, jobSettings, &settingsCfg.PrintSettingsOptions)
	if err != nil {
		return nil, err
	}
	control := newPrintLayoutSettings(jobSettings, settingsCfg)
	if err := control.checkBindingConflict(); err != nil {
		return nil, err
	}
	jobFinishing, _, err := control.binding("JobBindAllDocuments")
	if err != nil {
		return nil, err
	}
	jobCopies, err := control.count("JobCopiesAllDocuments", 1, configuration.MaxPlacements)
	if err != nil {
		return nil, err
	}
	jobCollate, err := control.choice("JobCollateAllDocuments", "Collated", "Collated", "Uncollated")
	if err != nil {
		return nil, err
	}
	pageOrder, err := control.choice("JobPageOrder", "Standard", "Standard", "Reverse")
	if err != nil {
		return nil, err
	}
	jobNUp, jobDirection, err := control.nup("JobNUpAllDocumentsContiguously", configuration.MaxPlacements)
	if err != nil {
		return nil, err
	}
	jobDuplex, jobManual, err := control.duplex("JobDuplexAllDocumentsContiguously")
	if err != nil {
		return nil, err
	}
	jobDuplexOpt, _, _ := control.option(jobSettings.Elements, "JobDuplexAllDocumentsContiguously")
	jobHasDuplex := jobDuplexOpt != nil
	settingsCfg.context = nil
	planner := &StreamPrintPlanner{
		capability:   capability,
		options:      configuration,
		settings:     settingsCfg,
		jobSettings:  jobSettings,
		jobFinishing: jobFinishing,
		jobCopies:    jobCopies,
		jobCollated:  jobCollate == "Collated",
		reverseOrder: pageOrder == "Reverse",
		jobNUp:       jobNUp,
		jobDirection: jobDirection,
		jobDuplex:    jobDuplex,
		jobManual:    jobManual,
		jobHasDuplex: jobHasDuplex,
		seenDocs:     make(map[int]bool),
	}
	planner.builder = printPlanBuilder{
		options:      configuration,
		settings:     settingsCfg,
		remaining:    configuration.MaxWork,
		jobFinishing: jobFinishing,
	}
	planner.packer = printSheetPacker{
		builder: &planner.builder,
		output:  &planner.batch,
	}
	defaultDoc, err := planner.resolveDocumentConfig(ctx, nil)
	if err != nil {
		return nil, err
	}
	planner.defaultDoc = defaultDoc
	planner.activeDoc = defaultDoc
	return planner, nil
}

// BeginDocument 在进入新文档边界时注册文档级打印设置并与作业基线合并，支持多文档异构票据编排并立即返回上一文档已结算的物理纸张
// 入参: ctx 取消Context，nil采用Background, docIndex 零基文档序号, docSettings 当前文档级打印设置，nil沿用作业默认设置
// 返回: []PrintSheet 切换文档边界时立即结算产出的物理纸张，无产出为nil, error 序号、冲突、票据、预算、关闭或取消错误
func (p *StreamPrintPlanner) BeginDocument(ctx context.Context, docIndex int, docSettings *PrintSettings) ([]PrintSheet, error) {
	if p == nil {
		return nil, fmt.Errorf("%w: nil stream print planner", ErrInvalid)
	}
	if p.flushed {
		return nil, ErrClosed
	}
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if docIndex < 0 {
		return nil, fmt.Errorf("%w: negative stream plan document index", ErrInvalid)
	}
	if p.seenDocs[docIndex] || p.activeDocSet && p.activeDocIndex == docIndex {
		return nil, fmt.Errorf("%w: duplicate stream plan document index %d", ErrInvalid, docIndex)
	}
	p.builder.settings.context = ctx
	defer func() { p.builder.settings.context = nil }()
	nextCfg, err := p.resolveDocumentConfig(ctx, docSettings)
	if err != nil {
		return nil, err
	}
	if p.activeDocSet {
		if err := p.finishActiveDocument(ctx, &nextCfg); err != nil {
			return nil, err
		}
		p.seenDocs[p.activeDocIndex] = true
	}
	p.activeDoc = nextCfg
	p.activeDocIndex = docIndex
	p.activeDocSet = true
	p.docPageCount = 0
	p.docExplicitPageIdx = false
	return p.takeReadySheets(), nil
}

// Capability 返回当前流式拼版器的流式执行模式、窗口页数、页码范围与分析原因独立副本
// 返回: PrintStreamCapability 流式可行性分析结果
func (p *StreamPrintPlanner) Capability() PrintStreamCapability {
	if p == nil {
		return PrintStreamCapability{}
	}
	result := p.capability
	result.Reasons = slices.Clone(p.capability.Reasons)
	return result
}

// PushPage 输入单个源页面，自动按页码范围过滤；直通或滑动窗口模式攒满物理纸张后立即返回对应PrintSheet并释放窗口内存，随机访问模式缓冲页头待Flush统一编排
// 入参: ctx 取消Context，nil采用Background, page 源页面尺寸、盒子与可选页级打印设置
// 返回: []PrintSheet 本次产出的完整物理纸张，未凑满窗口或缓冲模式返回nil, error 参数、票据、几何、容量、关闭或取消错误
func (p *StreamPrintPlanner) PushPage(ctx context.Context, page StreamPlanPage) ([]PrintSheet, error) {
	sheets, _, err := p.pushPageWithColorPlan(ctx, page)
	return sheets, err
}

// pushPageWithColorPlan 输入单个源页面执行流式拼版或缓冲，并单次返回已解析的有效色彩计划供流式资源锁定复用
// 入参: ctx 取消Context，nil采用Background, page 源页面尺寸、盒子与可选页级打印设置
// 返回: []PrintSheet 本次产出的完整物理纸张，未凑满窗口或缓冲模式返回nil, *PrintColorPlan 当前页有效色彩计划，跳过或未声明时为nil, error 参数、票据、几何、容量、关闭或取消错误
func (p *StreamPrintPlanner) pushPageWithColorPlan(ctx context.Context, page StreamPlanPage) ([]PrintSheet, *PrintColorPlan, error) {
	if p == nil {
		return nil, nil, fmt.Errorf("%w: nil stream print planner", ErrInvalid)
	}
	if p.flushed {
		return nil, nil, ErrClosed
	}
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	p.builder.settings.context = ctx
	defer func() { p.builder.settings.context = nil }()
	if page.PageIndex < 0 || page.DocumentIndex < 0 || page.DocumentPageIndex < 0 {
		return nil, nil, fmt.Errorf("%w: negative stream plan page index", ErrInvalid)
	}
	if !geometryFinite(page.Width, page.Height) || page.Width <= 0 || page.Height <= 0 {
		return nil, nil, fmt.Errorf("%w: stream plan page dimensions", ErrInvalid)
	}
	if p.totalPushed >= p.settings.Limits.MaxPageCount {
		return nil, nil, fmt.Errorf("%w: stream print planner page count", ErrLimit)
	}
	implicitSwitch := !p.activeDocSet || page.DocumentIndex != p.activeDocIndex
	if implicitSwitch && p.seenDocs[page.DocumentIndex] {
		return nil, nil, fmt.Errorf("%w: duplicate stream plan document index %d", ErrInvalid, page.DocumentIndex)
	}
	nextDocPageCount := p.docPageCount
	targetCfg := p.activeDoc
	if implicitSwitch {
		nextDocPageCount = 0
		targetCfg = p.defaultDoc
	}
	if page.DocumentPageIndex != 0 {
		if page.DocumentPageIndex != nextDocPageCount {
			return nil, nil, fmt.Errorf("%w: non-sequential document page index %d", ErrInvalid, page.DocumentPageIndex)
		}
	} else if !implicitSwitch && p.docExplicitPageIdx {
		return nil, nil, fmt.Errorf("%w: non-sequential document page index %d", ErrInvalid, page.DocumentPageIndex)
	}
	localIndex := nextDocPageCount
	applyDocSwitch := func() error {
		if !implicitSwitch {
			return nil
		}
		if p.activeDocSet {
			if err := p.finishActiveDocument(ctx, &targetCfg); err != nil {
				return err
			}
			p.seenDocs[p.activeDocIndex] = true
		}
		p.activeDoc = targetCfg
		p.activeDocIndex = page.DocumentIndex
		p.activeDocSet = true
		p.docExplicitPageIdx = false
		return nil
	}
	commitPage := func() {
		p.docPageCount = nextDocPageCount + 1
		if page.DocumentPageIndex != 0 {
			p.docExplicitPageIdx = true
		}
		p.totalPushed++
	}
	if p.capability.Mode == PrintStreamRandomAccess {
		planPage, err := p.preparePlanPage(ctx, page, targetCfg)
		if err != nil {
			return nil, nil, err
		}
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		if err := applyDocSwitch(); err != nil {
			return nil, nil, err
		}
		if len(p.bufferedDocs) == 0 || p.bufferedDocs[len(p.bufferedDocs)-1].documentIndex != page.DocumentIndex {
			p.bufferedDocs = append(p.bufferedDocs, streamBufferedDocument{documentIndex: page.DocumentIndex, config: p.activeDoc})
		}
		docBuf := &p.bufferedDocs[len(p.bufferedDocs)-1]
		docBuf.pages = append(docBuf.pages, planPage)
		commitPage()
		return nil, planPage.colorPlan, nil
	}
	if targetCfg.needsBuffer {
		planPage, err := p.preparePlanPage(ctx, page, targetCfg)
		if err != nil {
			return nil, nil, err
		}
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		if err := applyDocSwitch(); err != nil {
			return nil, nil, err
		}
		p.activeDocPages = append(p.activeDocPages, planPage)
		commitPage()
		return p.takeReadySheets(), planPage.colorPlan, nil
	}
	hits := 1
	if targetCfg.hasPageRanges {
		hits = streamPageRangeHits(targetCfg.rangeSpans, int64(localIndex)+1)
		if hits == 0 {
			if err := applyDocSwitch(); err != nil {
				return nil, nil, err
			}
			commitPage()
			return p.takeReadySheets(), nil, nil
		}
	}
	planPage, err := p.preparePlanPage(ctx, page, targetCfg)
	if err != nil {
		return nil, nil, err
	}
	docCfg := targetCfg.toWindowDocument()
	if planPage.poster > 1 && docCfg.nup != 1 {
		return nil, nil, fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
	}
	if err := applyDocSwitch(); err != nil {
		return nil, nil, err
	}
	for range hits {
		for range planPage.copies {
			if planPage.poster > 1 {
				if err := p.packer.poster(planPage, docCfg); err != nil {
					return nil, nil, err
				}
				continue
			}
			if err := p.packer.add(planPage, docCfg); err != nil {
				return nil, nil, err
			}
			if p.isActiveSheetFull() {
				if err := p.packer.flush(); err != nil {
					return nil, nil, err
				}
			}
		}
	}
	sheets, err := p.drainBatchSheets(p.activeDoc.sheetCopies)
	if err != nil {
		return nil, nil, err
	}
	commitPage()
	return p.prependReadySheets(sheets), planPage.colorPlan, nil
}

// Flush 结束当前作业并补齐滑动窗口尾张，或对逆序、小册子、逐份多副本及非单调页范围模式一次性输出完整纸张计划
// 重复调用幂等返回nil；调用完成后规划器标记关闭，后续PushPage与BeginDocument将返回ErrClosed
// 入参: ctx 取消Context，nil采用Background
// 返回: []PrintSheet 最终产出的物理纸张列表, error 编排、容量或取消错误
func (p *StreamPrintPlanner) Flush(ctx context.Context) ([]PrintSheet, error) {
	if p == nil {
		return nil, fmt.Errorf("%w: nil stream print planner", ErrInvalid)
	}
	if p.flushed {
		return nil, nil
	}
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p.builder.settings.context = ctx
	defer func() { p.builder.settings.context = nil }()
	if p.capability.Mode != PrintStreamRandomAccess {
		if p.activeDocSet {
			if err := p.finishActiveDocument(ctx, nil); err != nil {
				return nil, err
			}
		} else {
			if err := p.packer.flush(); err != nil {
				return nil, err
			}
			drained, err := p.drainBatchSheets(p.activeDoc.sheetCopies)
			if err != nil {
				return nil, err
			}
			p.readySheets = append(p.readySheets, drained...)
		}
		sheets := p.takeReadySheets()
		p.flushed = true
		return sheets, checkContext(ctx)
	}
	sheets, err := p.flushRandomAccess(ctx)
	if err != nil {
		return nil, err
	}
	p.bufferedDocs = nil
	p.flushed = true
	return sheets, checkContext(ctx)
}

// mergeStreamPrintSettings 在纯内存中按作用域校验增量设置并与基线合并，避免无意义的XML往返
// 入参: ctx 取消Context, base 已校验基线设置, delta 待合并增量设置, cfg 解析与预算配置, scope 增量设置的作用域过滤
// 返回: *PrintSettings 独立合并设置, error 结构、预算或取消错误
func mergeStreamPrintSettings(ctx context.Context, base, delta *PrintSettings, cfg printSettingsConfig, scope PrintScope) (*PrintSettings, error) {
	deltaCfg := cfg
	deltaCfg.context = ctx
	deltaCfg.Scope = scope
	change, err := validatePrintSettingsModel(delta, deltaCfg, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	mergeCfg := cfg
	mergeCfg.context = ctx
	mergeCfg.Scope = PrintScopeUnknown
	merged, err := mergePrintSettingsValidated(printCloneSettings(base), change, mergeCfg)
	if err != nil {
		return nil, err
	}
	result, err := validatePrintSettingsModel(merged, mergeCfg, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsOutputBudget(result, mergeCfg, printDocumentTicket); err != nil {
		return nil, err
	}
	return result, nil
}

// resolveDocumentConfig 在当前作业基线上合并文档级打印设置并解析文档编排参数及流式缓冲策略
// 入参: ctx 已规范化取消Context, docSettings 文档级打印设置，nil沿用作业默认设置
// 返回: streamDocumentConfig 独立文档编排配置, error 票据、冲突、预算或取消错误
func (p *StreamPrintPlanner) resolveDocumentConfig(ctx context.Context, docSettings *PrintSettings) (streamDocumentConfig, error) {
	cfg := p.settings
	cfg.context = ctx
	model := p.jobSettings
	if docSettings != nil {
		merged, err := mergeStreamPrintSettings(ctx, p.jobSettings, docSettings, cfg, PrintScopeDocument)
		if err != nil {
			return streamDocumentConfig{}, err
		}
		if cfg.ignoreUnsupported {
			merged = printStripPrivateExtensions(merged)
		}
		model = merged
	}
	control := newPrintLayoutSettings(model, cfg)
	if err := control.checkBindingConflict(); err != nil {
		return streamDocumentConfig{}, err
	}
	docFinishing, _, err := control.binding("DocumentBinding")
	if err != nil {
		return streamDocumentConfig{}, err
	}
	finishing := p.jobFinishing
	separate := false
	separateCopies := false
	if docFinishing.Binding != PrintBindingNone {
		finishing = docFinishing
		separate = true
		if docFinishing.Binding == PrintBindingBooklet {
			separateCopies = true
		}
	}
	docCopies, err := control.count("DocumentCopiesAllPages", 1, p.options.MaxPlacements)
	if err != nil {
		return streamDocumentConfig{}, err
	}
	docCollate, err := control.choice("DocumentCollate", "Collated", "Collated", "Uncollated")
	if err != nil {
		return streamDocumentConfig{}, err
	}
	docNUp, docDirection, err := control.nup("DocumentNUp", p.options.MaxPlacements)
	if err != nil {
		return streamDocumentConfig{}, err
	}
	nup, direction := p.jobNUp, p.jobDirection
	if docNUp > 1 {
		if p.jobNUp > 1 {
			return streamDocumentConfig{}, fmt.Errorf("%w: simultaneous job and document NUp", ErrUnsupported)
		}
		nup, direction, separate = docNUp, docDirection, true
	} else if p.jobNUp > 1 {
		if option, _, _ := control.option(model.Elements, "DocumentNUp"); option != nil {
			return streamDocumentConfig{}, fmt.Errorf("%w: document NUp conflicts with job NUp", ErrUnsupported)
		}
	}
	if finishing.Binding == PrintBindingBooklet && nup > 1 {
		return streamDocumentConfig{}, fmt.Errorf("%w: booklet binding conflicts with NUp", ErrUnsupported)
	}
	docDuplex, docManual, err := control.duplex("DocumentDuplex")
	if err != nil {
		return streamDocumentConfig{}, err
	}
	docDuplexOpt, _, _ := control.option(model.Elements, "DocumentDuplex")
	duplex, manual := p.jobDuplex, p.jobManual
	if docDuplex != PrintSimplex {
		if p.jobDuplex != PrintSimplex {
			return streamDocumentConfig{}, fmt.Errorf("%w: simultaneous job and document duplex", ErrUnsupported)
		}
		duplex, manual, separate, separateCopies = docDuplex, docManual, true, true
	} else if p.jobDuplex != PrintSimplex {
		if docDuplexOpt != nil {
			return streamDocumentConfig{}, fmt.Errorf("%w: document simplex conflicts with job duplex", ErrUnsupported)
		}
	}
	continuous := p.jobNUp > 1 || p.jobDuplex != PrintSimplex
	if p.jobFinishing.Binding != PrintBindingBooklet && continuous && docCollate == "Uncollated" && (docCopies > 1 || !p.jobCollated && p.jobCopies > 1) {
		return streamDocumentConfig{}, fmt.Errorf("%w: uncollated copies conflict with job-contiguous sheet packing", ErrUnsupported)
	}
	pageRanges := ""
	hasPageRanges := false
	monotonicRange := true
	var rangeSpans []printPageRangeSpan
	if value := printParamValue(control.values, "DocumentPageRanges"); value != nil {
		if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
			return streamDocumentConfig{}, fmt.Errorf("%w: document page ranges type", ErrInvalid)
		}
		monotonic, err := printPageRangesMonotonic(value.Text, cfg)
		if err != nil {
			return streamDocumentConfig{}, err
		}
		pageRanges = value.Text
		hasPageRanges = value.Text != ""
		monotonicRange = monotonic
		if hasPageRanges && monotonicRange {
			rangeSpans, err = parsePrintPageRangeSpans(pageRanges, cfg)
			if err != nil {
				return streamDocumentConfig{}, err
			}
		}
	}
	collated := docCollate == "Collated"
	sheetCopies := 1
	needsBuffer := false
	if p.capability.Mode != PrintStreamRandomAccess {
		if finishing.Binding == PrintBindingBooklet || hasPageRanges && !monotonicRange {
			needsBuffer = true
		}
		if continuous {
			repeats := docCopies
			if !p.jobCollated {
				if p.jobCopies > p.options.MaxPlacements/repeats {
					return streamDocumentConfig{}, fmt.Errorf("%w: stream print planner copy product", ErrLimit)
				}
				repeats *= p.jobCopies
			}
			if repeats > 1 {
				needsBuffer = true
			}
		} else {
			if p.jobCopies > p.options.MaxPlacements/docCopies {
				return streamDocumentConfig{}, fmt.Errorf("%w: stream print planner copy product", ErrLimit)
			}
			totalCopies := p.jobCopies * docCopies
			if totalCopies > 1 && collated {
				needsBuffer = true
			} else if !needsBuffer {
				sheetCopies = totalCopies
			}
		}
	}
	return streamDocumentConfig{
		settings:       model,
		docFinishing:   docFinishing,
		finishing:      finishing,
		copies:         docCopies,
		collated:       collated,
		nup:            nup,
		direction:      direction,
		duplex:         duplex,
		manual:         manual,
		hasDuplex:      docDuplexOpt != nil,
		separate:       separate,
		separateCopies: separateCopies,
		pageRanges:     pageRanges,
		hasPageRanges:  hasPageRanges,
		rangeSpans:     rangeSpans,
		sheetCopies:    sheetCopies,
		needsBuffer:    needsBuffer,
	}, nil
}

// toWindowDocument 构造滑动窗口模式下的单份文档级编排参数快照
// 返回: printPlanDocument 文档级拼版与双面配置
func (c streamDocumentConfig) toWindowDocument() printPlanDocument {
	return printPlanDocument{
		copies:            1,
		collated:          c.collated,
		nup:               c.nup,
		direction:         c.direction,
		duplex:            c.duplex,
		manual:            c.manual,
		hasDuplex:         c.hasDuplex,
		separate:          c.separate,
		separateCopies:    c.separateCopies,
		finishing:         c.finishing,
		documentFinishing: c.docFinishing,
	}
}

// toPlanDocument 构造完整文档编排配置供随机访问或文档级缓冲收尾复用
// 入参: capacity 预分配页面切片容量
// 返回: printPlanDocument 文档级编排配置
func (c streamDocumentConfig) toPlanDocument(capacity int) printPlanDocument {
	return printPlanDocument{
		pages:             make([]printPlanPage, 0, capacity),
		copies:            c.copies,
		collated:          c.collated,
		nup:               c.nup,
		direction:         c.direction,
		duplex:            c.duplex,
		manual:            c.manual,
		hasDuplex:         c.hasDuplex,
		separate:          c.separate,
		separateCopies:    c.separateCopies,
		finishing:         c.finishing,
		documentFinishing: c.docFinishing,
	}
}

// finishActiveDocument 在文档切换或作业结束时结算前一个活跃文档的缓冲或窗口纸张并暂存至就绪队列
// 入参: ctx 已规范化取消Context, next 即将开启的新文档配置，Flush时为nil
// 返回: error 冲突、容量、预算或取消错误
func (p *StreamPrintPlanner) finishActiveDocument(ctx context.Context, next *streamDocumentConfig) error {
	if p.capability.Mode == PrintStreamRandomAccess {
		return nil
	}
	if p.activeDoc.needsBuffer {
		if err := p.flushBufferedDocument(ctx, p.activeDoc, p.activeDocPages); err != nil {
			return err
		}
		p.activeDocPages = nil
		if next == nil || p.activeDoc.separate || next.separate {
			if err := p.packer.flush(); err != nil {
				return err
			}
			drained, err := p.drainBatchSheets(1)
			if err != nil {
				return err
			}
			p.readySheets = append(p.readySheets, drained...)
		}
		return nil
	}
	if next == nil || p.activeDoc.separate || next.separate {
		if err := p.packer.flush(); err != nil {
			return err
		}
	}
	if len(p.batch.Sheets) != 0 {
		drained, err := p.drainBatchSheets(p.activeDoc.sheetCopies)
		if err != nil {
			return err
		}
		p.readySheets = append(p.readySheets, drained...)
	}
	return nil
}

// flushBufferedDocument 在流式作业中对单个含小册子、逐份副本或非单调页范围的文档执行与Reader.PrintPlan等价的编排
// 入参: ctx 已规范化取消Context, docCfg 当前文档配置, pages 当前文档缓冲页面列表
// 返回: error 冲突、容量、预算或取消错误
func (p *StreamPrintPlanner) flushBufferedDocument(ctx context.Context, docCfg streamDocumentConfig, pages []printPlanPage) error {
	if len(pages) == 0 {
		return nil
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	indices, _, err := printPageRanges(docCfg.pageRanges, len(pages), p.options.MaxPlacements-p.builder.selected, p.builder.settings)
	if err != nil {
		return err
	}
	p.builder.selected += len(indices)
	doc := docCfg.toPlanDocument(len(indices))
	for _, local := range indices {
		pg := pages[local]
		if pg.poster > 1 && doc.finishing.Binding == PrintBindingBooklet {
			return fmt.Errorf("%w: booklet binding conflicts with poster", ErrUnsupported)
		}
		if pg.poster > 1 && doc.nup != 1 {
			return fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
		}
		doc.pages = append(doc.pages, pg)
	}
	if len(doc.pages) == 0 {
		return nil
	}
	continuous := p.jobNUp > 1 || p.jobDuplex != PrintSimplex
	if continuous {
		repeats := doc.copies
		if !p.jobCollated {
			if p.jobCopies > p.options.MaxPlacements/repeats {
				return fmt.Errorf("%w: print plan document copies", ErrLimit)
			}
			repeats *= p.jobCopies
		}
		if doc.separate {
			if err := p.packer.flush(); err != nil {
				return err
			}
		}
		for range repeats {
			if doc.separateCopies {
				if err := p.packer.flush(); err != nil {
					return err
				}
			}
			if err := p.packer.document(doc); err != nil {
				return err
			}
			if doc.separateCopies {
				if err := p.packer.flush(); err != nil {
					return err
				}
			}
		}
		if doc.separate {
			if err := p.packer.flush(); err != nil {
				return err
			}
		}
		drained, err := p.drainBatchSheets(1)
		if err != nil {
			return err
		}
		p.readySheets = append(p.readySheets, drained...)
		return nil
	}
	template := &PrintPlan{}
	packer := printSheetPacker{builder: &p.builder, output: template, temporary: true}
	if err := packer.document(doc); err != nil {
		return err
	}
	if err := packer.flush(); err != nil {
		return err
	}
	totalCopies := doc.copies
	if p.jobCopies > 1 {
		if doc.copies > p.options.MaxPlacements/p.jobCopies {
			return fmt.Errorf("%w: print document copy product", ErrLimit)
		}
		totalCopies *= p.jobCopies
	}
	out := &PrintPlan{}
	if err := p.builder.copyDocument(out, template.Sheets, totalCopies, doc.collated); err != nil {
		return err
	}
	p.readySheets = append(p.readySheets, out.Sheets...)
	return nil
}

// takeReadySheets 取出并清空暂存的已就绪物理纸张队列
// 返回: []PrintSheet 已就绪纸张切片
func (p *StreamPrintPlanner) takeReadySheets() []PrintSheet {
	if len(p.readySheets) == 0 {
		return nil
	}
	result := p.readySheets
	p.readySheets = nil
	return result
}

// prependReadySheets 将暂存就绪纸张与本批次新产出纸张按顺序合并并清空暂存队列
// 入参: sheets 本批次新产出的纸张
// 返回: []PrintSheet 合并后的物理纸张切片
func (p *StreamPrintPlanner) prependReadySheets(sheets []PrintSheet) []PrintSheet {
	if len(p.readySheets) == 0 {
		return sheets
	}
	result := append(p.readySheets, sheets...)
	p.readySheets = nil
	return result
}

// isActiveSheetFull 判断当前滑动窗口内的活动物理纸张是否已填满正反两面所有槽位
// 返回: bool 纸张是否已满可立即产出
func (p *StreamPrintPlanner) isActiveSheetFull() bool {
	if p.packer.sheet == nil {
		return false
	}
	frontFull := p.packer.frontDone || len(p.packer.sheet.Front.Pages) == p.packer.nup
	if !frontFull {
		return false
	}
	if p.packer.sheet.Duplex == PrintSimplex {
		return true
	}
	return p.packer.sheet.Back != nil && len(p.packer.sheet.Back.Pages) == p.packer.nup
}

// drainBatchSheets 在预检展开后总纸张、总放置与总工作预算满足上限后，取出本批次完整纸张并按需展开非逐份物理副本
// 入参: copies 当前物理纸张副本倍数
// 返回: []PrintSheet 独立物理纸张切片, error 容量或取消错误
func (p *StreamPrintPlanner) drainBatchSheets(copies int) ([]PrintSheet, error) {
	if len(p.batch.Sheets) == 0 {
		return nil, nil
	}
	raw := p.batch.Sheets
	if copies <= 1 {
		p.batch.Sheets = nil
		return raw, nil
	}
	extraCopies := copies - 1
	if len(raw) > (p.options.MaxSheets-p.builder.sheets)/extraCopies {
		return nil, fmt.Errorf("%w: print plan output capacity", ErrLimit)
	}
	var rawPlacements int
	for _, sheet := range raw {
		rawPlacements += len(sheet.Front.Pages)
		if sheet.Back != nil {
			rawPlacements += len(sheet.Back.Pages)
		}
	}
	if rawPlacements > (p.options.MaxPlacements-p.builder.placements)/extraCopies {
		return nil, fmt.Errorf("%w: print plan output capacity", ErrLimit)
	}
	extraWork := uint64(rawPlacements+len(raw)) * uint64(extraCopies)
	if extraWork > p.builder.remaining {
		return nil, fmt.Errorf("%w: print plan work", ErrLimit)
	}
	p.batch.Sheets = nil
	expanded := &PrintPlan{}
	for _, sheet := range raw {
		for copyIdx := range copies {
			if copyIdx == 0 {
				expanded.Sheets = append(expanded.Sheets, sheet)
				continue
			}
			if err := p.builder.appendSheet(expanded, sheet, false); err != nil {
				return nil, err
			}
		}
	}
	return expanded.Sheets, nil
}

// preparePlanPage 合并单页打印设置并复用preparePrintPageState计算正面及必要时的背面布局、水印、色彩与反相语义
// 入参: ctx 已规范化取消Context, page 输入页面描述, docCfg 当前文档有效配置
// 返回: printPlanPage 轻量可编排页面描述, error 参数、票据、布局或预算错误
func (p *StreamPrintPlanner) preparePlanPage(ctx context.Context, page StreamPlanPage, docCfg streamDocumentConfig) (printPlanPage, error) {
	if err := p.builder.step(1); err != nil {
		return printPlanPage{}, err
	}
	model := docCfg.settings
	if page.Settings != nil {
		merged, err := mergeStreamPrintSettings(ctx, docCfg.settings, page.Settings, p.settings, PrintScopeUnknown)
		if err != nil {
			return printPlanPage{}, err
		}
		if p.settings.ignoreUnsupported {
			merged = printStripPrivateExtensions(merged)
		}
		model = merged
	}
	control := newPrintLayoutSettings(model, p.builder.settings)
	copies, err := control.count("PageCopies", 1, p.options.MaxPlacements)
	if err != nil {
		return printPlanPage{}, err
	}
	front, err := control.choice("PageForceFrontSide", "None", "None", "ForceFrontSide")
	if err != nil {
		return printPlanPage{}, err
	}
	poster, err := control.poster(min(p.options.MaxSheets, p.options.MaxPlacements))
	if err != nil {
		return printPlanPage{}, err
	}
	headerPage, err := streamPlanPageHeader(page)
	if err != nil {
		return printPlanPage{}, err
	}
	state, err := preparePrintPageState(ctx, model, p.builder.settings, headerPage, p.options.Print.Media, printPageStateOptions{
		stripPlanFeatures:    true,
		ignoreUnsupported:    p.settings.ignoreUnsupported,
		ignoreColorPlanError: p.settings.ignoreUnsupported,
		computeBackLayout:    true,
	})
	if err != nil {
		return printPlanPage{}, err
	}
	return printPlanPage{
		index:      page.PageIndex,
		document:   page.DocumentIndex,
		layout:     *state.layout,
		backLayout: state.backLayout,
		rotation:   state.rotation,
		copies:     copies,
		force:      front == "ForceFrontSide",
		poster:     poster,
		watermark:  state.watermark,
		negative:   state.negative,
		color:      state.outputColor,
		colorPlan:  state.colorPlan,
		resolution: state.resolution,
	}, nil
}

// streamPlanPageHeader 将StreamPlanPage尺寸与盒边界转换为PrintLayout计算所需的轻量Page头并校验盒合法性
// 入参: page 流式输入页面描述
// 返回: *Page 仅含尺寸与盒信息的轻量页面对象, error 盒几何非法错误
func streamPlanPageHeader(page StreamPlanPage) (*Page, error) {
	result := &Page{
		Width:         page.Width,
		Height:        page.Height,
		ContentBox:    Rect{Width: page.Width, Height: page.Height},
		BleedBox:      Rect{Width: page.Width, Height: page.Height},
		HasContentBox: page.HasContentBox,
		HasBleedBox:   page.HasBleedBox,
	}
	if page.HasContentBox {
		box := page.ContentBox
		if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
			return nil, fmt.Errorf("%w: stream plan page ContentBox", ErrInvalid)
		}
		result.ContentBox = box
	}
	if page.HasBleedBox {
		box := page.BleedBox
		if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
			return nil, fmt.Errorf("%w: stream plan page BleedBox", ErrInvalid)
		}
		result.BleedBox = box
	}
	return result, nil
}

// flushRandomAccess 对随机访问缓冲模式下的所有缓冲文档执行与Reader.PrintPlan等价的完整选页、小册子、逐份与逆序编排
// 入参: ctx 已规范化取消Context
// 返回: []PrintSheet 最终物理纸张切片, error 冲突、容量或取消错误
func (p *StreamPrintPlanner) flushRandomAccess(ctx context.Context) ([]PrintSheet, error) {
	if len(p.bufferedDocs) == 0 {
		return nil, nil
	}
	var documents []printPlanDocument
	selected := 0
	for _, bufDoc := range p.bufferedDocs {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		indices, _, err := printPageRanges(bufDoc.config.pageRanges, len(bufDoc.pages), p.options.MaxPlacements-selected, p.builder.settings)
		if err != nil {
			return nil, err
		}
		selected += len(indices)
		doc := bufDoc.config.toPlanDocument(len(indices))
		for _, local := range indices {
			pg := bufDoc.pages[local]
			if pg.poster > 1 && doc.finishing.Binding == PrintBindingBooklet {
				return nil, fmt.Errorf("%w: booklet binding conflicts with poster", ErrUnsupported)
			}
			if pg.poster > 1 && doc.nup != 1 {
				return nil, fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
			}
			doc.pages = append(doc.pages, pg)
		}
		documents = append(documents, doc)
	}
	if selected == 0 {
		return nil, nil
	}
	plan := &PrintPlan{}
	if err := p.builder.assembleSheets(plan, documents, p.jobFinishing, p.jobCopies, p.jobCollated, p.reverseOrder, p.jobNUp, p.jobDuplex, p.jobManual, p.jobHasDuplex); err != nil {
		return nil, err
	}
	return plan.Sheets, nil
}

// retainedPages 收集规划器当前窗口、待吐队列与随机缓冲中仍被引用的全部源页面全局序号
// 返回: map[int]bool 仍被引用的源页序号集合
func (p *StreamPrintPlanner) retainedPages() map[int]bool {
	keep := make(map[int]bool)
	recordSheet := func(sheet *PrintSheet) {
		if sheet == nil {
			return
		}
		for _, pl := range sheet.Front.Pages {
			if pl.Page >= 0 {
				keep[pl.Page] = true
			}
		}
		if sheet.Back != nil {
			for _, pl := range sheet.Back.Pages {
				if pl.Page >= 0 {
					keep[pl.Page] = true
				}
			}
		}
	}
	recordSheet(p.packer.sheet)
	for i := range p.batch.Sheets {
		recordSheet(&p.batch.Sheets[i])
	}
	for i := range p.readySheets {
		recordSheet(&p.readySheets[i])
	}
	for _, pg := range p.activeDocPages {
		if pg.index >= 0 {
			keep[pg.index] = true
		}
	}
	for _, bufDoc := range p.bufferedDocs {
		for _, pg := range bufDoc.pages {
			if pg.index >= 0 {
				keep[pg.index] = true
			}
		}
	}
	return keep
}

// streamPageRangeHits 统计指定一基页码在单调页码范围区间列表中被命中的总次数
// 入参: spans 单调闭区间列表, pageNumber 一基文档内页码
// 返回: int 命中次数，未命中返回0
func streamPageRangeHits(spans []printPageRangeSpan, pageNumber int64) int {
	target := big.NewInt(pageNumber)
	hits := 0
	for _, span := range spans {
		if target.Cmp(span.start) >= 0 && target.Cmp(span.end) <= 0 {
			hits++
		}
	}
	return hits
}

// Mode 返回当前流式拼版规划器的执行模式，无效或未初始化返回PrintStreamPassthrough
// 返回: PrintStreamMode 流式执行模式
func (s *StreamPrintSheet) Mode() PrintStreamMode {
	if s == nil || s.view == nil {
		return PrintStreamPassthrough
	}
	return s.view.mode
}

// Format 返回当前文档的XPS或OpenXPS方言，无效或未初始化返回FormatUnknown
// 返回: Format 文档方言
func (s *StreamPrintSheet) Format() Format {
	if s == nil || s.view == nil {
		return FormatUnknown
	}
	return s.view.format
}

// Progress 返回交付当前物理纸张时的流式消费进度快照，无效或未初始化返回零值
// 返回: StreamProgress 流式消费进度快照
func (s *StreamPrintSheet) Progress() StreamProgress {
	if s == nil || s.view == nil {
		return StreamProgress{}
	}
	return s.view.progress
}

// prepareCall 校验临时纸张视图未关闭并合并检查流取消Context，不持有阅读器读锁
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Reader 有效只读阅读器, context.Context 合并后的Context, func() 取消监听清理函数, error 关闭或取消错误
func (s *StreamPrintSheet) prepareCall(ctx context.Context) (*Reader, context.Context, func(), error) {
	if s == nil {
		return nil, nil, nil, ErrClosed
	}
	return s.streamReaderView.prepareCall(ctx)
}

// lockReader 校验临时纸张视图、获取读锁并合并检查Context，成功时调用方须立即通过Defer执行清理函数
// 入参: ctx 取消Context，nil沿用流读取Context
// 返回: *Reader 有效只读阅读器, context.Context 合并后的Context, func() 释放清理函数, error 关闭或取消错误
func (s *StreamPrintSheet) lockReader(ctx context.Context) (*Reader, context.Context, func(), error) {
	if s == nil {
		return nil, nil, nil, ErrClosed
	}
	return s.streamReaderView.lockReader(ctx)
}

// streamPublicKeyEqual 比较两个可选公钥对象是否等价，不依赖reflect包
// 入参: a, b 待比较公钥
// 返回: bool 两公钥是否等价
func streamPublicKeyEqual(a, b any) bool {
	if a == nil && b == nil {
		return true
	}
	if a == nil || b == nil {
		return false
	}
	if eq, ok := a.(interface{ Equal(crypto.PublicKey) bool }); ok {
		return eq.Equal(b)
	}
	return false
}

// streamVerifyOptionsEqual 判断两次数字签名校验选项的公钥、信任池、验证时间、用途与扩展命名空间是否完全一致
// 入参: a, b 待比较的签名验证选项
// 返回: bool 验证选项是否完全一致
func streamVerifyOptionsEqual(a, b SignatureVerifyOptions) bool {
	if !streamPublicKeyEqual(a.PublicKey, b.PublicKey) {
		return false
	}
	if a.Trust.Roots != b.Trust.Roots || a.Trust.Intermediates != b.Trust.Intermediates || a.Trust.DNSName != b.Trust.DNSName || a.Trust.MaxConstraintComparisions != b.Trust.MaxConstraintComparisions {
		return false
	}
	if a.Trust.CurrentTime.IsZero() != b.Trust.CurrentTime.IsZero() || !a.Trust.CurrentTime.Equal(b.Trust.CurrentTime) {
		return false
	}
	if !slices.Equal(a.Trust.KeyUsages, b.Trust.KeyUsages) || !slices.Equal(a.Namespaces, b.Namespaces) {
		return false
	}
	return true
}

// streamSignatureOptionsUnchanged 判断纸面回调传入的签名选项相对完流阶段已通过的验签选项是否存在策略或预算覆盖
// 入参: base 完流验签使用的签名选项, req 回调传入的签名选项
// 返回: bool 是否未引入新的验签覆盖策略
func streamSignatureOptionsUnchanged(base, req *PrintSignatureOptions) bool {
	if req == nil {
		return true
	}
	var b PrintSignatureOptions
	if base != nil {
		b = *base
	}
	if req.ReportPage != "" && req.ReportPage != b.ReportPage {
		return false
	}
	if req.MaxSignatures != 0 && req.MaxSignatures != b.MaxSignatures {
		return false
	}
	if req.MaxBytes != 0 && req.MaxBytes != b.MaxBytes {
		return false
	}
	if req.MaxWork != 0 && req.MaxWork != b.MaxWork {
		return false
	}
	if req.MaxEvidence != 0 && req.MaxEvidence != b.MaxEvidence {
		return false
	}
	return streamVerifyOptionsEqual(b.Verify, req.Verify)
}

// resolveSignatureOptions 结合纸面最低策略与流式状态生成安全签名选项，完流已验签且未变更策略覆盖时跳过重复整包验签
// 入参: side 目标纸面, options 调用方可选签名选项
// 返回: *PrintSignatureOptions 生效签名选项, error 策略非法或未完流错误
func (s *StreamPrintSheet) resolveSignatureOptions(side *PrintSide, options *PrintSignatureOptions) (*PrintSignatureOptions, error) {
	var effective PrintSignaturePolicy
	if options != nil && options.Policy != PrintSignatureFromTicket {
		if options.Policy > PrintSignatureRequireValid {
			return nil, fmt.Errorf("%w: print side signature policy", ErrInvalid)
		}
		effective = options.Policy
	} else {
		effective = s.view.signaturePolicy
		if side != nil && side.SignaturePolicy > effective {
			if side.SignaturePolicy > PrintSignatureRequireValid {
				return nil, fmt.Errorf("%w: print side signature policy", ErrInvalid)
			}
			effective = side.SignaturePolicy
		}
		if effective == PrintSignatureFromTicket {
			effective = PrintSignatureIgnore
		}
	}
	if effective != PrintSignatureIgnore && s.view.streamIncomplete {
		return nil, fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
	}
	if effective != PrintSignatureIgnore && s.view.sigVerified && effective <= s.view.sigVerifiedPolicy && streamSignatureOptionsUnchanged(s.view.sigVerifiedOpts, options) {
		return &PrintSignatureOptions{Policy: PrintSignatureIgnore}, nil
	}
	var copied PrintSignatureOptions
	if options != nil {
		copied = *options
	}
	copied.Policy = effective
	return &copied, nil
}

// WalkPrintSide 在OnSheet回调期间遍历指定拼版纸面场景，回调期间不持有读锁，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, side 纸面布局（通常为&Sheet.Front或Sheet.Back）, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 纸面布局、页面读取、签名、预算、取消、关闭或回调返回的错误
func (s *StreamPrintSheet) WalkPrintSide(ctx context.Context, side *PrintSide, visitor *SceneVisitor, options *WalkOptions) error {
	r, walkCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return err
	}
	defer cleanup()
	var reqSig *PrintSignatureOptions
	if options != nil {
		reqSig = options.Signatures
	}
	sigOpts, err := s.resolveSignatureOptions(side, reqSig)
	if err != nil {
		return err
	}
	effective := WalkOptions{}
	if options != nil {
		effective = *options
	}
	effective.Signatures = sigOpts
	return r.WalkPrintSide(walkCtx, side, visitor, &effective)
}

// RenderPrintSide 在OnSheet回调期间光栅化指定拼版纸面，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, side 纸面布局, options 打印及绘制预算参数，nil采用默认值
// 返回: *image.NRGBA 独立纸面图像, error 布局、资源、签名、绘制、预算、取消或关闭错误
func (s *StreamPrintSheet) RenderPrintSide(ctx context.Context, side *PrintSide, options *PrintRenderOptions) (*image.NRGBA, error) {
	r, renderCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	var reqSig *PrintSignatureOptions
	if options != nil {
		reqSig = options.Signatures
	}
	sigOpts, err := s.resolveSignatureOptions(side, reqSig)
	if err != nil {
		return nil, err
	}
	effective := DefaultPrintRenderOptions()
	if options != nil {
		effective = *options
	}
	effective.Signatures = sigOpts
	return r.RenderPrintSide(renderCtx, side, &effective)
}

// RenderPrintSideDevice 在OnSheet回调期间将指定拼版纸面编码至目标ICC设备图像，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, side 纸面布局, device 必需目标设备配置, options 打印及加载参数，nil采用默认值
// 返回: *DeviceImage 独立纸面设备图像, error 布局、资源、签名、转换、预算、取消或关闭错误
func (s *StreamPrintSheet) RenderPrintSideDevice(ctx context.Context, side *PrintSide, device *DeviceColorTarget, options *PrintRenderOptions) (*DeviceImage, error) {
	r, renderCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	var reqSig *PrintSignatureOptions
	if options != nil {
		reqSig = options.Signatures
	}
	sigOpts, err := s.resolveSignatureOptions(side, reqSig)
	if err != nil {
		return nil, err
	}
	effective := DefaultPrintRenderOptions()
	if options != nil {
		effective = *options
	}
	effective.Signatures = sigOpts
	return r.RenderPrintSideDevice(renderCtx, side, device, &effective)
}

// Font 在OnSheet回调期间读取已到达的包根字体资源，支持#index集合索引，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, fontURI 包根字体URI，可附#index集合索引
// 返回: *FontResource 独立只读字体资源, error URI、读取、格式、取消或关闭错误
func (s *StreamPrintSheet) Font(ctx context.Context, fontURI string) (*FontResource, error) {
	r, fontCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.Font(fontCtx, fontURI)
}

// Image 在OnSheet回调期间读取已到达的包根图像资源，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 包根图像部件URI, options 图像参数，nil采用默认值
// 返回: *ImageResource 独立图像数据, error 输入、解码、资源、取消或关闭错误
func (s *StreamPrintSheet) Image(ctx context.Context, part string, options *ImageOptions) (*ImageResource, error) {
	r, imageCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.Image(imageCtx, part, options)
}

// ImageInfo 在OnSheet回调期间读取已到达图像的轻量文件头元数据，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 包根图像部件URI
// 返回: *ImageInfo 轻量图像头元数据, error URI、媒体类型、文件头、预算、取消或关闭错误
func (s *StreamPrintSheet) ImageInfo(ctx context.Context, part string) (*ImageInfo, error) {
	r, imageCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.ImageInfo(imageCtx, part)
}

// DecodeImageRows 在OnSheet回调期间按行流式解码并色彩管理导出已到达图像为八位非预乘sRGB行字节，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, part 包根图像部件URI, options 图像解码选项，nil采用默认值, convert 色彩转换选项，nil采用默认值, fn 逐行消费回调
// 返回: error 状态、参数、URI、媒体类型、解码、色彩、回调、关闭或取消错误
func (s *StreamPrintSheet) DecodeImageRows(ctx context.Context, part string, options *ImageOptions, convert *ImageConvertOptions, fn func(y int, nrgba []byte) error) error {
	r, imageCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return err
	}
	defer cleanup()
	return r.DecodeImageRows(imageCtx, part, options, convert, fn)
}

// ReadPart 在OnSheet回调期间读取已到达的任意包内部件原始字节，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, name 部件包根URI
// 返回: []byte 独立部件字节, error URI、不存在、预算、取消或关闭错误
func (s *StreamPrintSheet) ReadPart(ctx context.Context, name string) ([]byte, error) {
	r, partCtx, release, err := s.lockReader(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	return r.pkg.readPartContext(partCtx, name)
}

// ColorProfile 在OnSheet回调期间以包根为基准解析URI并读取已到达ICC配置部件原始字节，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, uri 包根或相对包根ICC配置URI
// 返回: []byte 独立ICC配置字节, error URI、类型、不存在、预算、取消或关闭错误
func (s *StreamPrintSheet) ColorProfile(ctx context.Context, uri string) ([]byte, error) {
	if s == nil {
		return nil, ErrClosed
	}
	return s.streamReaderView.colorProfile(ctx, "/", uri)
}

// ResolveColor 在OnSheet回调期间以指定基准部件解析颜色，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, basePart 解析相对ICC的基准部件URI, value 待解析颜色, options 色彩解析选项，nil采用默认值
// 返回: ResolvedColor 多空间颜色结果, error 参数、部件、配置、转换、取消或关闭错误
func (s *StreamPrintSheet) ResolveColor(ctx context.Context, basePart string, value Color, options *ColorResolveOptions) (ResolvedColor, error) {
	r, colorCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return ResolvedColor{}, err
	}
	defer cleanup()
	return r.ResolveColor(colorCtx, basePart, value, options)
}

// ResolveGradientStops 在OnSheet回调期间以指定基准部件规范化解算渐变停靠点与几何，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, brush 线性或径向渐变画刷, basePart 相对资源解析基准部件URI, state 当前图形与打印色彩状态, options 可选解算参数
// 返回: *ResolvedGradient 规范化渐变模型, error 参数、色彩、几何、数值、关闭或取消错误
func (s *StreamPrintSheet) ResolveGradientStops(ctx context.Context, brush *Brush, basePart string, state WalkState, options *GradientResolveOptions) (*ResolvedGradient, error) {
	r, gradCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return ResolveGradientStops(gradCtx, r, brush, basePart, state, options)
}

// NewColorResolver 创建绑定当前临时纸张视图生命周期的有界ICC缓存颜色解析器，回调结束后调用安全返回ErrClosed
// 返回: *ColorResolver 受视图生命周期守卫保护的颜色解析器
func (s *StreamPrintSheet) NewColorResolver() *ColorResolver {
	if s == nil {
		return newStreamColorResolver(&streamPageView{closed: true})
	}
	return s.streamReaderView.newColorResolver()
}

// RenderElement 在OnSheet回调期间隔离光栅化单个元素到透明背景画布，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, basePart 默认资源基准部件URI, elem 单个视觉元素, state 图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 透明背景隔离图像, Rect 包围盒, error 参数、资源、预算、取消或关闭错误
func (s *StreamPrintSheet) RenderElement(ctx context.Context, basePart string, elem Element, state WalkState, options *RenderOptions) (*image.NRGBA, Rect, error) {
	r, renderCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	defer cleanup()
	return r.RenderElement(renderCtx, basePart, elem, state, options)
}

// RenderElementMapped 在OnSheet回调期间隔离光栅化单个元素并返回像素到页面映射矩阵，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, elem 单个视觉元素, state 图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *RenderedElement 含图像、包围盒与映射矩阵的结果, error 参数、资源、预算、取消或关闭错误
func (s *StreamPrintSheet) RenderElementMapped(ctx context.Context, elem Element, state WalkState, options *RenderOptions) (*RenderedElement, error) {
	r, renderCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	return r.RenderElementMapped(renderCtx, elem, state, options)
}

// RenderBrushTileWithState 在OnSheet回调期间按指定图形与打印色彩状态隔离光栅化单个画刷瓦片，回调完成后返回ErrClosed
// 入参: ctx 取消Context，nil沿用流读取Context, brush 待光栅化画刷, basePart 默认资源基准部件URI, state 图形与打印色彩状态, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 透明背景单瓦片图像, Rect 瓦片物理范围矩形, error 参数、画刷、资源、预算、取消或关闭错误
func (s *StreamPrintSheet) RenderBrushTileWithState(ctx context.Context, brush *Brush, basePart string, state WalkState, options *RenderOptions) (*image.NRGBA, Rect, error) {
	r, renderCtx, cleanup, err := s.prepareCall(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	defer cleanup()
	return r.RenderBrushTileWithState(renderCtx, brush, basePart, state, options)
}

// ConsumeStreamPrintPlan 以有界窗口流式消费XPS或OpenXPS输入并实时驱动StreamPrintPlanner产出物理纸张视图
// 在OnSheet回调期间可直接执行WalkPrintSide、RenderPrintSide或RenderPrintSideDevice，窗口滑出后立即释放不再被引用的源页面与资源存储
// 内存占用严格受Stream.MaxMemoryBytes约束；多文档异构票据按文档边界自动切换并与Reader.PrintPlan保持等价
// 入参: ctx 取消Context，nil采用Background, input 前向输入, options 流式读取、打印计划及纸张回调参数，nil采用默认值
// 返回: error 输入、封装、票据、拼版、存储、回调、预算或取消错误
func ConsumeStreamPrintPlan(ctx context.Context, input io.Reader, options *StreamPrintOptions) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	streamOpts := DefaultStreamReadOptions()
	planOpts := DefaultPrintPlanOptions()
	var onSheet func(context.Context, *StreamPrintSheet) error
	var userOnPage func(context.Context, *StreamPage) error
	var pinKeys []string
	if options != nil {
		streamOpts = options.Stream
		userOnPage = options.Stream.OnPage
		planOpts = options.Plan
		if planOpts.MaxSheets == 0 {
			planOpts.MaxSheets = 1 << 16
		}
		if planOpts.MaxPlacements == 0 {
			planOpts.MaxPlacements = 1 << 18
		}
		if planOpts.MaxWork == 0 {
			planOpts.MaxWork = 1 << 28
		}
		onSheet = options.OnSheet
		if len(options.PinParts) != 0 {
			seen := make(map[string]bool, len(options.PinParts))
			for _, part := range options.PinParts {
				canonical, err := opcPartName(part)
				if err != nil {
					return err
				}
				key := strings.ToLower(canonical)
				if !seen[key] {
					seen[key] = true
					pinKeys = append(pinKeys, key)
				}
			}
		}
	}
	if planOpts.MaxSheets < 1 || planOpts.MaxPlacements < 1 || planOpts.Print.Settings.Scope != PrintScopeUnknown {
		return fmt.Errorf("%w: stream print options", ErrInvalid)
	}
	if err := validatePrintMedia(planOpts.Print.Media); err != nil {
		return err
	}
	if planOpts.Signatures != nil && planOpts.Signatures.Policy > PrintSignatureRequireValid {
		return fmt.Errorf("%w: stream print signature policy", ErrInvalid)
	}
	coord := &streamPrintCoordinator{
		planOptions:  planOpts,
		onSheet:      onSheet,
		lastDoc:      -1,
		sigPolicy:    PrintSignatureIgnore,
		pinnedByPage: make(map[int][]string),
	}
	defer coord.releaseAll()
	streamOpts.OnPage = func(pageCtx context.Context, sp *StreamPage) error {
		if userOnPage != nil {
			if err := userOnPage(pageCtx, sp); err != nil {
				return err
			}
			if err := checkContext(pageCtx); err != nil {
				return err
			}
		}
		return coord.handlePage(pageCtx, sp)
	}
	hooks := &streamConsumeHooks{
		pinParts: pinKeys,
		onPartReady: func(key string) error {
			return coord.handlePartReady(ctx, key)
		},
		onFinish: func(source *Reader, complete bool) error {
			return coord.finish(ctx, source, complete)
		},
	}
	return consumeStreamInternal(ctx, input, &streamOpts, hooks)
}

// readSingleScopePrintSettings 仅按指定作用域从单个固定布局部件关系中读取并解析打印票据，未关联时返回nil
// 入参: ctx 取消Context, r 有效只读阅读器, sourcePart 固定序列、文档或页面部件URI, scope 目标作用域, opts 票据解析预算选项
// 返回: *PrintSettings 单层独立打印设置或nil, error 关系、类型、读取、格式、预算或取消错误
func readSingleScopePrintSettings(ctx context.Context, r *Reader, sourcePart string, scope PrintScope, opts PrintSettingsOptions) (*PrintSettings, error) {
	canonical, err := opcPartName(sourcePart)
	if err != nil {
		return nil, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, canonical)
	if err != nil {
		return nil, err
	}
	part, err := printTicketTarget(canonical, relations, r.format)
	if err != nil || part == "" {
		return nil, err
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
	local := opts
	local.Scope = scope
	normalized, err := printSettingsOptions(ctx, &local)
	if err != nil {
		return nil, err
	}
	limit := min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes, r.limits.MaxPackageBytes, normalized.Limits.MaxMetadataBytes, normalized.Limits.MaxPartBytes, normalized.Limits.MaxPackageBytes)
	ticket := PrintTicket{Source: sourceName, Part: partName, Scope: scope, ContentType: typeName}
	if err := r.readPrintTicketData(&ticket, limit, ctx); err != nil {
		return nil, err
	}
	settings, err := ticket.Settings(ctx, &normalized.PrintSettingsOptions)
	if err != nil {
		return nil, &PartError{Part: ticket.Part, Err: err}
	}
	return settings, nil
}

// collectStreamPagePinKeys 收集单个页面及其关系、必需资源与可选颜色计划ICC配置的小写规范部件键
// 入参: owner 流式包状态, pagePart 页面部件URI, resources 已解析必需资源URI列表, colorPlan 可选有效颜色计划
// 返回: []string 去重后的小写规范部件键列表
func collectStreamPagePinKeys(owner *streamPackage, pagePart string, resources []string, colorPlan *PrintColorPlan) []string {
	seen := make(map[string]bool, len(resources)+4)
	var keys []string
	add := func(uri string) {
		if uri == "" {
			return
		}
		key := strings.ToLower(uri)
		if !seen[key] {
			seen[key] = true
			keys = append(keys, key)
		}
	}
	add(pagePart)
	add(createdRelationshipPart(pagePart))
	for _, res := range resources {
		add(res)
		resRels := strings.ToLower(createdRelationshipPart(res))
		if owner != nil && owner.parts[resRels] != nil {
			add(resRels)
		}
	}
	if colorPlan != nil {
		for _, uri := range [4]string{colorPlan.Device.URI, colorPlan.Source.URI, colorPlan.Destination.URI, colorPlan.Blend.URI} {
			if uri != "" {
				if canonical, err := opcPartName(uri); err == nil {
					add(canonical)
				}
			}
		}
	}
	return keys
}

// collectStreamSheetICCKeys 收集单张物理纸张全部放置页颜色计划引用的规范化包内ICC配置小写键列表
// 入参: sheet 待交付物理纸张
// 返回: []string 去重后的包内ICC配置小写键列表
func collectStreamSheetICCKeys(sheet PrintSheet) []string {
	var seen map[string]bool
	var keys []string
	addPlan := func(plan *PrintColorPlan) {
		if plan == nil {
			return
		}
		for _, uri := range [4]string{plan.Device.URI, plan.Source.URI, plan.Destination.URI, plan.Blend.URI} {
			if uri == "" {
				continue
			}
			canonical, err := opcPartName(uri)
			if err != nil {
				continue
			}
			key := strings.ToLower(canonical)
			if seen == nil {
				seen = make(map[string]bool, 4)
			}
			if !seen[key] {
				seen[key] = true
				keys = append(keys, key)
			}
		}
	}
	for _, pl := range sheet.Front.Pages {
		addPlan(pl.Color)
	}
	if sheet.Back != nil {
		for _, pl := range sheet.Back.Pages {
			addPlan(pl.Color)
		}
	}
	return keys
}

// handlePage 处理单页到达事件：按需初始化规划器或切换文档边界、锁定窗口页资源并及时交付已就绪纸张
// 入参: ctx 取消Context, sp 当前到达的临时页面视图
// 返回: error 票据、拼版、签名、回调、预算或取消错误
func (c *streamPrintCoordinator) handlePage(ctx context.Context, sp *StreamPage) error {
	r, pageCtx, release, err := sp.lockReader(ctx)
	if err != nil {
		return err
	}
	owner := sp.view.owner
	if c.owner == nil && owner != nil {
		c.owner = owner
	}
	if c.planner == nil {
		jobTicket, err := readSingleScopePrintSettings(pageCtx, r, r.sequence, PrintScopeJob, c.planOptions.Print.Settings)
		if err != nil {
			release()
			return err
		}
		planner, err := NewStreamPrintPlanner(pageCtx, jobTicket, &c.planOptions)
		if err != nil {
			release()
			return err
		}
		ticketSig, err := printSignaturePolicy(planner.jobSettings, pageCtx)
		if err != nil {
			release()
			return err
		}
		effectiveSig := ticketSig
		if c.planOptions.Signatures != nil && c.planOptions.Signatures.Policy != PrintSignatureFromTicket {
			effectiveSig = c.planOptions.Signatures.Policy
		}
		c.sigPolicy = effectiveSig
		if effectiveSig != PrintSignatureIgnore && owner != nil && (owner.ownedMemory != nil || owner.reclaimed) {
			release()
			return fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
		}
		c.planner = planner
	}
	docIdx := sp.view.documentIndex
	var docTicket *PrintSettings
	needDocSwitch := docIdx != c.lastDoc
	if needDocSwitch {
		docTicket, err = readSingleScopePrintSettings(pageCtx, r, sp.DocumentPart, PrintScopeDocument, c.planOptions.Print.Settings)
		if err != nil {
			release()
			return err
		}
	}
	pageTicket, err := readSingleScopePrintSettings(pageCtx, r, sp.Reference.Part, PrintScopePage, c.planOptions.Print.Settings)
	if err != nil {
		release()
		return err
	}
	header, err := r.readPageHeader(sp.view.index, nil, pageCtx)
	if err != nil {
		release()
		return err
	}
	resources := slices.Clone(sp.view.resources)
	incomplete := sp.view.streamIncomplete
	progress := sp.view.progress
	release()
	if needDocSwitch {
		docSheets, err := c.planner.BeginDocument(ctx, docIdx, docTicket)
		if err != nil {
			return err
		}
		c.lastDoc = docIdx
		if len(docSheets) != 0 {
			if err := c.enqueueOrDeliverSheets(ctx, r, docSheets, progress, incomplete); err != nil {
				return err
			}
		}
	}
	sheets, colorPlan, err := c.planner.pushPageWithColorPlan(ctx, StreamPlanPage{
		PageIndex:         sp.Index,
		DocumentIndex:     docIdx,
		DocumentPageIndex: sp.view.pageIndex,
		Width:             header.Width,
		Height:            header.Height,
		ContentBox:        header.ContentBox,
		BleedBox:          header.BleedBox,
		HasContentBox:     header.HasContentBox,
		HasBleedBox:       header.HasBleedBox,
		Settings:          pageTicket,
	})
	if err != nil {
		return err
	}
	var retained map[int]bool
	if owner != nil {
		retained = c.planner.retainedPages()
		if retained[sp.Index] || streamSheetsContainPage(sheets, sp.Index) {
			keys := collectStreamPagePinKeys(owner, sp.Reference.Part, resources, colorPlan)
			for _, k := range keys {
				owner.pinPart(k)
			}
			c.pinnedByPage[sp.Index] = keys
		}
	}
	if len(sheets) == 0 {
		c.releaseUnusedPages(retained, nil)
		return nil
	}
	return c.enqueueOrDeliverSheets(ctx, r, sheets, progress, incomplete)
}

// enqueueOrDeliverSheets 检查待交付纸张引用的票据包内ICC部件是否均已到达，缺件时锁定并暂存待到达后再交付
// 入参: ctx 取消Context, source 当前只读阅读器, sheets 待交付物理纸张列表, progress 进度快照, incomplete 未完流标志
// 返回: error 签名、回调或取消错误
func (c *streamPrintCoordinator) enqueueOrDeliverSheets(ctx context.Context, source *Reader, sheets []PrintSheet, progress StreamProgress, incomplete bool) error {
	mode := c.planner.Capability().Mode
	for idx, sheet := range sheets {
		if err := checkContext(ctx); err != nil {
			return err
		}
		iccKeys := collectStreamSheetICCKeys(sheet)
		var waitKeys map[string]bool
		if source != nil && source.pkg != nil {
			for _, k := range iccKeys {
				if _, exists := source.pkg.parts[k]; !exists {
					if waitKeys == nil {
						waitKeys = make(map[string]bool)
					}
					waitKeys[k] = true
				}
			}
		}
		if len(c.pendingSheets) == 0 && len(waitKeys) == 0 {
			if incomplete && c.sigPolicy != PrintSignatureIgnore {
				return fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
			}
			sheet.Front.SignaturePolicy = c.sigPolicy
			if sheet.Back != nil {
				sheet.Back.SignaturePolicy = c.sigPolicy
			}
			if c.onSheet != nil {
				if err := c.deliverOneSheet(ctx, source, sheet, mode, progress, incomplete); err != nil {
					return err
				}
			}
			c.sheetIndex++
			c.releaseUnusedPages(nil, sheets[idx+1:])
			continue
		}
		var pinKeys []string
		if c.owner != nil && len(iccKeys) != 0 {
			pinKeys = iccKeys
			for _, k := range pinKeys {
				c.owner.pinPart(k)
			}
		}
		c.pendingSheets = append(c.pendingSheets, streamPendingSheet{
			sheet:    sheet,
			waitKeys: waitKeys,
			pinKeys:  pinKeys,
		})
	}
	c.releaseUnusedPages(nil, nil)
	return nil
}

// handlePartReady 在晚到部件完整就绪后解除对应暂存纸张的等待状态并按序立即交付队头就绪纸张
// 入参: ctx 取消Context, key 已完整到达的小写规范部件键
// 返回: error 签名、回调或取消错误
func (c *streamPrintCoordinator) handlePartReady(ctx context.Context, key string) error {
	if len(c.pendingSheets) == 0 || c.owner == nil || c.owner.index == nil {
		return nil
	}
	for i := range c.pendingSheets {
		delete(c.pendingSheets[i].waitKeys, key)
	}
	source := c.owner.index
	mode := c.planner.Capability().Mode
	for len(c.pendingSheets) != 0 && len(c.pendingSheets[0].waitKeys) == 0 {
		if err := checkContext(ctx); err != nil {
			return err
		}
		item := c.pendingSheets[0]
		incomplete := !c.owner.centralVerified || c.owner.reclaimed
		if incomplete && c.sigPolicy != PrintSignatureIgnore {
			return fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
		}
		c.pendingSheets = c.pendingSheets[1:]
		progress := StreamProgress{
			BytesRead:          c.owner.input.count,
			DeliveredPages:     c.owner.pages,
			DiscoveredPages:    len(source.pages),
			DeliveredDocuments: c.owner.deliveredDocuments,
		}
		item.sheet.Front.SignaturePolicy = c.sigPolicy
		if item.sheet.Back != nil {
			item.sheet.Back.SignaturePolicy = c.sigPolicy
		}
		var deliverErr error
		if c.onSheet != nil {
			deliverErr = c.deliverOneSheet(ctx, source, item.sheet, mode, progress, incomplete)
		}
		for _, k := range item.pinKeys {
			c.owner.unpinPart(k)
		}
		if deliverErr != nil {
			return deliverErr
		}
		c.sheetIndex++
		c.releaseUnusedPages(nil, nil)
	}
	if len(c.pendingSheets) == 0 {
		c.pendingSheets = nil
	}
	return nil
}

// streamSheetsContainPage 判断物理纸张列表中是否包含指定全局序号的源页面
// 入参: sheets 待检查的物理纸张列表, pageIndex 全局零基源页序号
// 返回: bool 是否至少被一张纸面引用
func streamSheetsContainPage(sheets []PrintSheet, pageIndex int) bool {
	for i := range sheets {
		for _, pl := range sheets[i].Front.Pages {
			if pl.Page == pageIndex {
				return true
			}
		}
		if sheets[i].Back != nil {
			for _, pl := range sheets[i].Back.Pages {
				if pl.Page == pageIndex {
					return true
				}
			}
		}
	}
	return false
}

// finish 在全流校验完成后刷出残余等待队列、窗口或随机访问缓冲的全部物理纸张，并在交付后释放全部锁定资源
// 入参: ctx 取消Context, source 完整或终审只读阅读器, complete 整包压缩字节是否完整未回收
// 返回: error 签名、拼版、回调、预算或取消错误
func (c *streamPrintCoordinator) finish(ctx context.Context, source *Reader, complete bool) error {
	defer c.releaseAll()
	if c.planner == nil {
		return nil
	}
	if c.sigPolicy != PrintSignatureIgnore {
		if !complete {
			return fmt.Errorf("%w: digital signature verification requires completed package stream", ErrUnsupported)
		}
		report, err := source.readPrintSignatures(ctx, c.planner.jobSettings, c.planOptions.Signatures)
		if err != nil {
			return err
		}
		if !report.Allowed {
			return &PrintSignatureError{Report: report}
		}
		if report.NeedsErrorSheet {
			return fmt.Errorf("%w: signature error sheet requires Reader.PrintPlan", ErrUnsupported)
		}
		c.sigPolicy = report.Policy
		c.sigVerified = true
		c.sigVerifiedPolicy = report.Policy
		c.sigVerifiedOpts = c.planOptions.Signatures
	}
	tailSheets, err := c.planner.Flush(ctx)
	if err != nil {
		return err
	}
	pending := c.pendingSheets
	c.pendingSheets = nil
	if len(pending) == 0 && len(tailSheets) == 0 {
		return nil
	}
	var progress StreamProgress
	if c.owner != nil {
		progress = StreamProgress{
			BytesRead:          c.owner.input.count,
			DeliveredPages:     c.owner.pages,
			DiscoveredPages:    len(source.pages),
			DeliveredDocuments: c.owner.deliveredDocuments,
		}
	}
	mode := c.planner.Capability().Mode
	incomplete := !complete
	for i := range pending {
		if err := checkContext(ctx); err != nil {
			for j := i; j < len(pending); j++ {
				for _, k := range pending[j].pinKeys {
					c.owner.unpinPart(k)
				}
			}
			return err
		}
		sheet := pending[i].sheet
		sheet.Front.SignaturePolicy = c.sigPolicy
		if sheet.Back != nil {
			sheet.Back.SignaturePolicy = c.sigPolicy
		}
		var deliverErr error
		if c.onSheet != nil {
			deliverErr = c.deliverOneSheet(ctx, source, sheet, mode, progress, incomplete)
		}
		if c.owner != nil {
			for _, k := range pending[i].pinKeys {
				c.owner.unpinPart(k)
			}
		}
		if deliverErr != nil {
			for j := i + 1; j < len(pending); j++ {
				for _, k := range pending[j].pinKeys {
					c.owner.unpinPart(k)
				}
			}
			return deliverErr
		}
		c.sheetIndex++
		remaining := make([]PrintSheet, 0, len(pending)-i-1+len(tailSheets))
		for j := i + 1; j < len(pending); j++ {
			remaining = append(remaining, pending[j].sheet)
		}
		remaining = append(remaining, tailSheets...)
		c.releaseUnusedPages(nil, remaining)
	}
	if len(tailSheets) == 0 {
		return nil
	}
	return c.deliverSheets(ctx, source, tailSheets, progress, incomplete)
}

// deliverSheets 逐张创建临时StreamPrintSheet视图交付OnSheet，并在每张返回后立即释放不再被引用的窗口页面
// 入参: ctx 取消Context, source 当前只读阅读器, sheets 待交付物理纸张列表, progress 消费进度快照, incomplete 流是否未完结或已回收
// 返回: error 回调或取消错误
func (c *streamPrintCoordinator) deliverSheets(ctx context.Context, source *Reader, sheets []PrintSheet, progress StreamProgress, incomplete bool) error {
	mode := c.planner.Capability().Mode
	for idx, sheet := range sheets {
		if err := checkContext(ctx); err != nil {
			return err
		}
		sheet.Front.SignaturePolicy = c.sigPolicy
		if sheet.Back != nil {
			sheet.Back.SignaturePolicy = c.sigPolicy
		}
		if c.onSheet != nil {
			if err := c.deliverOneSheet(ctx, source, sheet, mode, progress, incomplete); err != nil {
				return err
			}
		}
		c.sheetIndex++
		c.releaseUnusedPages(nil, sheets[idx+1:])
	}
	return nil
}

// deliverOneSheet 为单张物理纸张创建受控临时视图并触发OnSheet，返回后立即关闭视图防止泄漏引用
// 入参: ctx 取消Context, source 底层只读阅读器, sheet 物理纸张, mode 规划器执行模式, progress 进度快照, incomplete 未完流标志
// 返回: error 回调或取消错误
func (c *streamPrintCoordinator) deliverOneSheet(ctx context.Context, source *Reader, sheet PrintSheet, mode PrintStreamMode, progress StreamProgress, incomplete bool) error {
	viewReader := &Reader{pkg: source.pkg, limits: source.limits, format: source.format, sequence: source.sequence, documents: source.documents, pages: source.pages, fixedXML: source.fixedXML}
	sheetView := &streamPageView{
		reader:            viewReader,
		format:            source.format,
		mode:              mode,
		progress:          progress,
		signaturePolicy:   c.sigPolicy,
		sigVerified:       c.sigVerified,
		sigVerifiedPolicy: c.sigVerifiedPolicy,
		sigVerifiedOpts:   c.sigVerifiedOpts,
		streamIncomplete:  incomplete,
		context:           ctx,
	}
	defer func() {
		sheetView.close()
		viewReader.Close()
	}()
	item := &StreamPrintSheet{
		Index:            c.sheetIndex,
		Sheet:            sheet,
		streamReaderView: streamReaderView{view: sheetView},
	}
	if err := c.onSheet(ctx, item); err != nil {
		return err
	}
	return checkContext(ctx)
}

// releaseUnusedPages 释放已不再被规划器窗口、暂存队列及本批次后续纸张引用的全部源页面与资源引用计数
// 入参: keep 可选的已计算窗口保留页集合，nil时从规划器查询, remaining 本批次尚未交付给OnSheet的后续纸张
func (c *streamPrintCoordinator) releaseUnusedPages(keep map[int]bool, remaining []PrintSheet) {
	if c.owner == nil || len(c.pinnedByPage) == 0 {
		return
	}
	if keep == nil {
		keep = c.planner.retainedPages()
	}
	markSheet := func(sheet *PrintSheet) {
		for _, pl := range sheet.Front.Pages {
			if pl.Page >= 0 {
				keep[pl.Page] = true
			}
		}
		if sheet.Back != nil {
			for _, pl := range sheet.Back.Pages {
				if pl.Page >= 0 {
					keep[pl.Page] = true
				}
			}
		}
	}
	for i := range c.pendingSheets {
		markSheet(&c.pendingSheets[i].sheet)
	}
	for i := range remaining {
		markSheet(&remaining[i])
	}
	for pageIdx, keys := range c.pinnedByPage {
		if keep[pageIdx] {
			continue
		}
		for _, k := range keys {
			c.owner.unpinPart(k)
		}
		delete(c.pinnedByPage, pageIdx)
	}
}

// releaseAll 释放协调器当前仍持有的全部部件引用计数，保证正常结束与错误路径零内存泄漏
func (c *streamPrintCoordinator) releaseAll() {
	if c.owner == nil {
		c.pendingSheets = nil
		return
	}
	for i := range c.pendingSheets {
		for _, k := range c.pendingSheets[i].pinKeys {
			c.owner.unpinPart(k)
		}
	}
	c.pendingSheets = nil
	for pageIdx, keys := range c.pinnedByPage {
		for _, k := range keys {
			c.owner.unpinPart(k)
		}
		delete(c.pinnedByPage, pageIdx)
	}
}
