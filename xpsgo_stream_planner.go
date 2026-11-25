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
	"errors"
	"fmt"
	"math/big"
	"slices"
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

// streamBufferedDocument 保存随机访问模式下按文档分组缓冲的轻量页面元数据
type streamBufferedDocument struct {
	documentIndex int
	pages         []printPlanPage
}

// StreamPrintPlanner 基于PrintSchema语义提供纯前向直通、滑动窗口与随机访问回退的流式拼版规划器
// 直通或滑动窗口模式下攒满单张物理纸张即刻产出PrintSheet并清空窗口内存，逆序、小册子、逐份多副本或非单调页范围在Flush时统一编排输出
type StreamPrintPlanner struct {
	capability     PrintStreamCapability
	options        PrintPlanOptions
	settings       printSettingsConfig
	jobSettings    *PrintSettings
	jobFinishing   PrintFinishing
	docFinishing   PrintFinishing
	finishing      PrintFinishing
	jobCopies      int
	docCopies      int
	jobCollated    bool
	docCollated    bool
	reverseOrder   bool
	jobNUp         int
	jobDuplex      PrintDuplex
	nup            int
	direction      string
	duplex         PrintDuplex
	manual         bool
	hasDocDuplex   bool
	separate       bool
	separateCopies bool
	pageRanges     string
	rangeSpans     []printPageRangeSpan
	builder        printPlanBuilder
	batch          PrintPlan
	packer         printSheetPacker
	sheetCopies    int
	lastDoc        int
	docPageCount   int
	totalPushed    int
	bufferedDocs   []streamBufferedDocument
	flushed        bool
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
		jobSettings, err = MergePrintSettings(ctx, jobSettings, configuration.Print.Defaults, &settingsCfg.PrintSettingsOptions)
		if err != nil {
			return nil, err
		}
	}
	if defaults != nil {
		jobSettings, err = MergePrintSettings(ctx, jobSettings, defaults, &settingsCfg.PrintSettingsOptions)
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
	docFinishing, _, err := control.binding("DocumentBinding")
	if err != nil {
		return nil, err
	}
	finishing := jobFinishing
	separate := false
	separateCopies := false
	if docFinishing.Binding != PrintBindingNone {
		finishing = docFinishing
		separate = true
		if docFinishing.Binding == PrintBindingBooklet {
			separateCopies = true
		}
	}
	jobCopies, err := control.count("JobCopiesAllDocuments", 1, configuration.MaxPlacements)
	if err != nil {
		return nil, err
	}
	docCopies, err := control.count("DocumentCopiesAllPages", 1, configuration.MaxPlacements)
	if err != nil {
		return nil, err
	}
	jobCollate, err := control.choice("JobCollateAllDocuments", "Collated", "Collated", "Uncollated")
	if err != nil {
		return nil, err
	}
	docCollate, err := control.choice("DocumentCollate", "Collated", "Collated", "Uncollated")
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
	docNUp, docDirection, err := control.nup("DocumentNUp", configuration.MaxPlacements)
	if err != nil {
		return nil, err
	}
	nup, direction := jobNUp, jobDirection
	if docNUp > 1 {
		nup, direction, separate = docNUp, docDirection, true
	}
	jobDuplex, jobManual, err := control.duplex("JobDuplexAllDocumentsContiguously")
	if err != nil {
		return nil, err
	}
	docDuplex, docManual, err := control.duplex("DocumentDuplex")
	if err != nil {
		return nil, err
	}
	docDuplexOpt, _, _ := control.option(jobSettings.Elements, "DocumentDuplex")
	duplex, manual := jobDuplex, jobManual
	if docDuplex != PrintSimplex {
		duplex, manual, separate, separateCopies = docDuplex, docManual, true, true
	}
	continuous := jobNUp > 1 || jobDuplex != PrintSimplex
	if continuous && docCollate == "Uncollated" && (docCopies > 1 || jobCollate == "Uncollated" && jobCopies > 1) {
		return nil, fmt.Errorf("%w: uncollated copies conflict with job-contiguous sheet packing", ErrUnsupported)
	}
	sheetCopies := 1
	if capability.Mode != PrintStreamRandomAccess {
		if jobCopies > configuration.MaxPlacements/docCopies {
			return nil, fmt.Errorf("%w: stream print planner copy product", ErrLimit)
		}
		sheetCopies = jobCopies * docCopies
	}
	var rangeSpans []printPageRangeSpan
	if capability.HasPageRanges && capability.MonotonicPageRange {
		rangeSpans, err = parsePrintPageRangeSpans(capability.PageRanges, settingsCfg)
		if err != nil {
			return nil, err
		}
	}
	settingsCfg.context = nil
	planner := &StreamPrintPlanner{
		capability:     capability,
		options:        configuration,
		settings:       settingsCfg,
		jobSettings:    jobSettings,
		jobFinishing:   jobFinishing,
		docFinishing:   docFinishing,
		finishing:      finishing,
		jobCopies:      jobCopies,
		docCopies:      docCopies,
		jobCollated:    jobCollate == "Collated",
		docCollated:    docCollate == "Collated",
		reverseOrder:   pageOrder == "Reverse",
		jobNUp:         jobNUp,
		jobDuplex:      jobDuplex,
		nup:            nup,
		direction:      direction,
		duplex:         duplex,
		manual:         manual,
		hasDocDuplex:   docDuplexOpt != nil,
		separate:       separate,
		separateCopies: separateCopies,
		pageRanges:     capability.PageRanges,
		rangeSpans:     rangeSpans,
		sheetCopies:    sheetCopies,
		lastDoc:        -1,
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
	return planner, nil
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
	p.builder.settings.context = ctx
	defer func() { p.builder.settings.context = nil }()
	if page.PageIndex < 0 || page.DocumentIndex < 0 || page.DocumentPageIndex < 0 {
		return nil, fmt.Errorf("%w: negative stream plan page index", ErrInvalid)
	}
	if !geometryFinite(page.Width, page.Height) || page.Width <= 0 || page.Height <= 0 {
		return nil, fmt.Errorf("%w: stream plan page dimensions", ErrInvalid)
	}
	if p.totalPushed >= p.settings.Limits.MaxPageCount {
		return nil, fmt.Errorf("%w: stream print planner page count", ErrLimit)
	}
	docSwitched := p.lastDoc >= 0 && page.DocumentIndex != p.lastDoc
	nextDocPageCount := p.docPageCount
	if p.lastDoc < 0 || docSwitched {
		nextDocPageCount = 0
	}
	localIndex := page.DocumentPageIndex
	if localIndex == 0 && nextDocPageCount > 0 {
		localIndex = nextDocPageCount
	}
	commitPage := func() {
		p.lastDoc = page.DocumentIndex
		p.docPageCount = nextDocPageCount + 1
		p.totalPushed++
	}
	if p.capability.Mode == PrintStreamRandomAccess {
		planPage, err := p.preparePlanPage(ctx, page)
		if err != nil {
			return nil, err
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if len(p.bufferedDocs) == 0 || p.bufferedDocs[len(p.bufferedDocs)-1].documentIndex != page.DocumentIndex {
			p.bufferedDocs = append(p.bufferedDocs, streamBufferedDocument{documentIndex: page.DocumentIndex})
		}
		docBuf := &p.bufferedDocs[len(p.bufferedDocs)-1]
		docBuf.pages = append(docBuf.pages, planPage)
		commitPage()
		return nil, nil
	}
	hits := 1
	if p.capability.HasPageRanges {
		hits = streamPageRangeHits(p.rangeSpans, int64(localIndex)+1)
		if hits == 0 {
			if docSwitched && p.separate {
				if err := p.packer.flush(); err != nil {
					return nil, err
				}
				sheets, err := p.drainBatchSheets()
				if err != nil {
					return nil, err
				}
				commitPage()
				return sheets, nil
			}
			commitPage()
			return nil, nil
		}
	}
	planPage, err := p.preparePlanPage(ctx, page)
	if err != nil {
		return nil, err
	}
	docCfg := p.windowDocumentConfig()
	if planPage.poster > 1 && docCfg.nup != 1 {
		return nil, fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
	}
	if docSwitched && p.separate {
		if err := p.packer.flush(); err != nil {
			return nil, err
		}
	}
	for range hits {
		for range planPage.copies {
			if planPage.poster > 1 {
				if err := p.packer.poster(planPage, docCfg); err != nil {
					return nil, err
				}
				continue
			}
			if err := p.packer.add(planPage, docCfg); err != nil {
				return nil, err
			}
			if p.isActiveSheetFull() {
				if err := p.packer.flush(); err != nil {
					return nil, err
				}
			}
		}
	}
	sheets, err := p.drainBatchSheets()
	if err != nil {
		return nil, err
	}
	commitPage()
	return sheets, nil
}

// Flush 结束当前作业并补齐滑动窗口尾张，或对逆序、小册子、逐份多副本及非单调页范围模式一次性输出完整纸张计划
// 重复调用幂等返回nil；调用完成后规划器标记关闭，后续PushPage将返回ErrClosed
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
		if err := p.packer.flush(); err != nil {
			return nil, err
		}
		sheets, err := p.drainBatchSheets()
		if err != nil {
			return nil, err
		}
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

// windowDocumentConfig 构造滑动窗口模式下的文档级编排参数快照
// 返回: printPlanDocument 文档级拼版与双面配置
func (p *StreamPrintPlanner) windowDocumentConfig() printPlanDocument {
	return printPlanDocument{
		copies:            1,
		collated:          p.docCollated,
		nup:               p.nup,
		direction:         p.direction,
		duplex:            p.duplex,
		manual:            p.manual,
		hasDuplex:         p.hasDocDuplex,
		separate:          p.separate,
		separateCopies:    p.separateCopies,
		finishing:         p.finishing,
		documentFinishing: p.docFinishing,
	}
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

// drainBatchSheets 取出滑动窗口本批次已完成的完整物理纸张，按需展开非逐份物理副本并清空内部暂存切片
// 返回: []PrintSheet 独立物理纸张切片, error 容量或取消错误
func (p *StreamPrintPlanner) drainBatchSheets() ([]PrintSheet, error) {
	if len(p.batch.Sheets) == 0 {
		return nil, nil
	}
	raw := p.batch.Sheets
	p.batch.Sheets = nil
	if p.sheetCopies <= 1 {
		return raw, nil
	}
	expanded := &PrintPlan{}
	for _, sheet := range raw {
		for copyIdx := range p.sheetCopies {
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

// preparePlanPage 合并单页打印设置并计算正面及必要时的背面打印布局、水印、色彩与反相语义
// 入参: ctx 已规范化取消Context, page 输入页面描述
// 返回: printPlanPage 轻量可编排页面描述, error 参数、票据、布局或预算错误
func (p *StreamPrintPlanner) preparePlanPage(ctx context.Context, page StreamPlanPage) (printPlanPage, error) {
	if err := p.builder.step(1); err != nil {
		return printPlanPage{}, err
	}
	model := p.jobSettings
	if page.Settings != nil {
		merged, err := MergePrintSettings(ctx, p.jobSettings, page.Settings, &p.settings.PrintSettingsOptions)
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
	model, watermark, err := printWatermarkSettings(model, p.builder.settings)
	if err != nil {
		return printPlanPage{}, err
	}
	model, negative, outputColor, err := printColorSettings(model, p.builder.settings)
	if err != nil {
		return printPlanPage{}, err
	}
	cleaned, colorPlan, err := printColorPlanSettings(ctx, model, &p.settings.PrintSettingsOptions)
	if err != nil {
		if !p.settings.ignoreUnsupported || !errors.Is(err, ErrUnsupported) {
			return printPlanPage{}, err
		}
		model = printStripColorPlanFeatures(model)
		colorPlan = nil
	} else {
		model = cleaned
	}
	layoutSettings, err := printPlanLayoutSettings(model, false, p.settings.ignoreUnsupported)
	if err != nil {
		return printPlanPage{}, err
	}
	headerPage, err := streamPlanPageHeader(page)
	if err != nil {
		return printPlanPage{}, err
	}
	layout, rotation, err := layoutSettings.layoutWithRotation(ctx, headerPage, p.options.Print.Media, &p.settings.PrintSettingsOptions)
	if err != nil {
		return printPlanPage{}, err
	}
	result := printPlanPage{
		index:     page.PageIndex,
		document:  page.DocumentIndex,
		layout:    *layout,
		rotation:  rotation,
		copies:    copies,
		force:     front == "ForceFrontSide",
		poster:    poster,
		watermark: watermark,
		negative:  negative,
		color:     outputColor,
		colorPlan: colorPlan,
	}
	if backClip := printRotateBox180(layout.MediaClip, layout.Width, layout.Height); backClip != layout.MediaClip {
		backMedia := p.options.Print.Media
		backMedia.Width, backMedia.Height = layout.Width, layout.Height
		backMedia.ImageableArea = &backClip
		backLayout, _, err := layoutSettings.layoutWithRotation(ctx, headerPage, backMedia, &p.settings.PrintSettingsOptions)
		if err != nil {
			return printPlanPage{}, err
		}
		result.backLayout = backLayout
	}
	return result, nil
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
		indices, _, err := printPageRanges(p.pageRanges, len(bufDoc.pages), p.options.MaxPlacements-selected, p.builder.settings)
		if err != nil {
			return nil, err
		}
		selected += len(indices)
		doc := printPlanDocument{
			pages:             make([]printPlanPage, 0, len(indices)),
			copies:            p.docCopies,
			collated:          p.docCollated,
			nup:               p.nup,
			direction:         p.direction,
			duplex:            p.duplex,
			manual:            p.manual,
			hasDuplex:         p.hasDocDuplex,
			separate:          p.separate,
			separateCopies:    p.separateCopies,
			finishing:         p.finishing,
			documentFinishing: p.docFinishing,
		}
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
	if err := p.builder.assembleSheets(plan, documents, p.jobFinishing, p.jobCopies, p.jobCollated, p.reverseOrder, p.jobNUp, p.jobDuplex, p.manual, false); err != nil {
		return nil, err
	}
	return plan.Sheets, nil
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
