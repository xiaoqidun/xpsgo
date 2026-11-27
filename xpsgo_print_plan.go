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
	"encoding/hex"
	"encoding/xml"
	"errors"
	"fmt"
	"image"
	"image/color"
	"io/fs"
	"math"
	"math/big"
	"slices"
	"strings"
	"unicode"
	"unicode/utf8"
)

const (
	// PrintSimplex 表示单面打印模式
	PrintSimplex PrintDuplex = iota
	// PrintDuplexLongEdge 表示双面长边翻页打印模式
	PrintDuplexLongEdge
	// PrintDuplexShortEdge 表示双面短边翻页打印模式
	PrintDuplexShortEdge
)

// printWatermarkTextLimit 为Print Schema公共字符串参数允许的最大字符数
const printWatermarkTextLimit = 65535

const (
	// PrintWatermarkLayerUnknown 表示未指定水印叠放层级
	PrintWatermarkLayerUnknown PrintWatermarkLayer = iota
	// PrintWatermarkOverlay 表示水印叠加在页面正文之上
	PrintWatermarkOverlay
	// PrintWatermarkUnderlay 表示水印铺设在页面正文之下
	PrintWatermarkUnderlay
)

const (
	// PrintSignatureFromTicket 表示按有效作业打印票据决定签名策略
	PrintSignatureFromTicket PrintSignaturePolicy = iota
	// PrintSignatureIgnore 表示忽略数字签名并继续打印
	PrintSignatureIgnore
	// PrintSignatureReportError 表示签名异常时生成错误报告页
	PrintSignatureReportError
	// PrintSignatureRequireValid 表示要求全部签名验证有效否则拒绝作业
	PrintSignatureRequireValid
)

const (
	// PrintStreamPassthrough 表示单页纯前向直通输出，无需跨页缓存
	PrintStreamPassthrough PrintStreamMode = iota
	// PrintStreamWindowed 表示需按有界滑动窗口缓存逻辑页（如多合一拼版或双面打印）
	PrintStreamWindowed
	// PrintStreamRandomAccess 表示需整文档或整作业随机访问缓冲（如逆序、小册子、逐份多副本或非单调页范围）
	PrintStreamRandomAccess
)

// ErrPrintSignature 表示打印签名策略拒绝输出
var ErrPrintSignature = errors.New("print signature policy rejected job")

// PrintDuplex 表示物理纸张的单双面及翻页方向
type PrintDuplex uint8

// PrintPlacement 保存单个源页面在纸面中的位置与变换，PageClip位于页面空间，MediaClip位于纸面空间
// DocumentIndex为零基文档序号；Part非空时引用辅助FixedPage且Page须为-1，错误报告页的DocumentIndex也为-1
// Watermark位于源页坐标空间，Negative在源页与水印合成后逐通道反相，Color保存源页独立有效颜色计划，Resolution保存源页有效输出分辨率
type PrintPlacement struct {
	Page          int
	DocumentIndex int
	Part          string
	Transform     Matrix
	PageClip      Rect
	MediaClip     Rect
	Watermark     *PrintWatermark
	Negative      bool
	Color         *PrintColorPlan
	Resolution    *PrintResolution
}

// PrintSide 保存一面物理纸张的尺寸、可打印区域与按绘制顺序排列的页面，单位为九十六分之一英寸
// Gutter为MediaClip内可选的物理留白区域，排除放置内容并保留背景；nil表示无留白
// Color作用于整个纸面（含背景），Resolution保存本纸面汇聚后的有效输出分辨率，SignaturePolicy为本纸面要求的最低签名策略
type PrintSide struct {
	Width, Height   float64
	MediaClip       Rect
	Gutter          *Rect
	Pages           []PrintPlacement
	Color           PrintColor
	Resolution      *PrintResolution
	SignaturePolicy PrintSignaturePolicy
}

// PrintSheet 保存一张物理纸张，Back为nil表示背面为空白，逆序输出不交换正反面，Booklet表示是否为骑马订小册子对折纸
type PrintSheet struct {
	Front        PrintSide
	Back         *PrintSide
	Duplex       PrintDuplex
	ManualDuplex bool
	Booklet      bool
}

// PrintPlan 保存独立的纸张输出计划，同一纸面按Pages顺序绘制，不持有阅读器或页面树
// JobFinishing与DocumentFinishing保存装订意图，DocumentFinishing按原文档序号索引
type PrintPlan struct {
	Sheets            []PrintSheet
	Diagnostics       []Diagnostic
	JobFinishing      PrintFinishing
	DocumentFinishing []PrintFinishing
	Signatures        *PrintSignatureReport
}

// PrintPlanOptions 设置有效票据、介质、作业编排预算及忽略策略，零值预算采用默认上限
// MaxSheets和MaxPlacements限制纸张与页面放置数，MaxWork限制票据与编排步骤，IgnoreUnsupportedFeatures跳过设备控制Feature
// Signatures设置整包签名检查，需要错误报告时须提供包内报告页并在末尾追加独立单面纸
type PrintPlanOptions struct {
	Print                     PrintLayoutOptions
	MaxSheets                 int
	MaxPlacements             int
	MaxWork                   uint64
	Signatures                *PrintSignatureOptions
	IgnoreUnsupportedFeatures bool
}

// printPlanPage 保存可重复编排的轻量页面描述，不保留已解析场景或票据树
type printPlanPage struct {
	index      int
	document   int
	layout     PrintLayout
	backLayout *PrintLayout
	rotation   Matrix
	copies     int
	force      bool
	poster     int
	watermark  *PrintWatermark
	negative   bool
	color      PrintColor
	colorPlan  *PrintColorPlan
	resolution *PrintResolution
}

// printPlanDocument 保存文档选页及编排设置，分别记录文档和副本的整纸边界
type printPlanDocument struct {
	pages             []printPlanPage
	copies            int
	collated          bool
	nup               int
	direction         string
	duplex            PrintDuplex
	manual            bool
	hasDuplex         bool
	separate          bool
	separateCopies    bool
	finishing         PrintFinishing
	documentFinishing PrintFinishing
}

// printPlanBuilder 保存本次计划的私有预算及票据缓存，所有可变结果在返回前独立复制
type printPlanBuilder struct {
	reader         *Reader
	options        PrintPlanOptions
	settings       printSettingsConfig
	remaining      uint64
	metadata       int64
	tickets        map[string]*PrintTicket
	validated      map[*PrintSettings]int64
	placements     int
	sheets         int
	selected       int
	templatePages  int
	templateSheets int
	diagnostics    []Diagnostic
	diagnosticSeen map[Diagnostic]struct{}
	jobFinishing   PrintFinishing
	signatures     *PrintSignatureReport
}

// printSheetPacker 将相邻页面放入纸面和正反面，只有完整纸张才追加到输出或文档模板
type printSheetPacker struct {
	builder   *printPlanBuilder
	output    *PrintPlan
	temporary bool
	sheet     *PrintSheet
	nup       int
	direction string
	finishing PrintFinishing
	frontDone bool
}

// printSidePage 保存可只读复用的源场景及节点数量，不保留整页资源绑定图
type printSidePage struct {
	part     string
	elements []Element
	nodes    int
}

// printSideGeometryBudget 保存单次纸面加载的几何物化预算与只读轮廓缓存
type printSideGeometryBudget struct {
	context context.Context
	edges   int
	work    uint64
	figures map[*xmlElement]*Geometry
}

// PrintWatermarkLayer 表示水印与源页面正文的叠放关系
type PrintWatermarkLayer uint8

// PrintWatermark 保存源页坐标空间的文字水印描述，Origin与FontSize单位为九十六分之一英寸，Angle为逆时针角度
// Transparency取零至一百透明百分比，HasTransparency区分未声明与显式零透明度
type PrintWatermark struct {
	Text            string
	Origin          Point
	FontSize        float64
	Color           color.NRGBA
	Angle           float64
	Transparency    float64
	HasTransparency bool
	Layer           PrintWatermarkLayer
}

// PrintWatermarkOptions 指定水印使用的包内字体URI或外部字体字节（均支持集合索引）与PageImageableSize在源页中的原点
// 默认按单行Unicode行进，Layout可提供重塑形结果并须与Text的UTF16簇范围一致
// Layout在阅读器读锁内调用，不得关闭或重入该阅读器，返回切片在调用期间不得修改
type PrintWatermarkOptions struct {
	FontURI         string
	FontData        []byte
	CollectionIndex uint32
	ImageableOrigin Point
	Layout          func(context.Context, PrintWatermark) ([]GlyphCluster, error)
}

// PrintSignaturePolicy 表示作业的签名处理方式，零值从有效作业票据读取
type PrintSignaturePolicy uint8

// PrintSignatureOptions 设置打印签名策略、验证选项、错误报告页及单次作业验证预算
// Policy非零时覆盖票据选择，缺省采用Ignore；ReportPage指定包内辅助错误报告页URI
// MaxSignatures默认1000，MaxBytes默认阅读器MaxPackageBytes，MaxWork默认1<<28，MaxEvidence默认1<<20
type PrintSignatureOptions struct {
	Policy        PrintSignaturePolicy
	Verify        SignatureVerifyOptions
	ReportPage    string
	MaxSignatures int
	MaxBytes      int64
	MaxWork       uint64
	MaxEvidence   int
}

// PrintSignatureResult 保存单份签名的验证结果，无法验证时保留原始错误
// Verification非nil时须检查Status判断有效性，Err非nil时Verification为空
type PrintSignatureResult struct {
	Part         PartInfo
	Verification *SignatureVerification
	Err          error
}

// PrintSignatureReport 保存打印签名策略判定结果与证据，Checked为false表示按Ignore跳过验证
// 完整检查无签名时允许打印，NeedsErrorSheet为true表示须在作业末尾追加错误报告纸
type PrintSignatureReport struct {
	Policy          PrintSignaturePolicy
	Checked         bool
	Allowed         bool
	NeedsErrorSheet bool
	Signatures      []PrintSignatureResult
}

// PrintSignatureError 表示因打印签名策略被拒绝输出并携带策略报告
type PrintSignatureError struct {
	Report *PrintSignatureReport
}

// printSignatureBudget 累计同次作业的验证工作及返回证据，不按签名重新建立总额度
type printSignatureBudget struct {
	context  context.Context
	work     uint64
	evidence int
}

// PrintResolution 保存打印票据声明的水平与垂直输出分辨率（每英寸点数）及可选质量后缀关键字
type PrintResolution struct {
	X, Y        float64
	Qualitative string
}

// PrintScalingSummary 保存打印票据中PageScaling的摘要类型、比例、微米偏移与对齐方式
type PrintScalingSummary struct {
	Option              string
	ScaleX              float64
	ScaleY              float64
	OffsetWidthMicrons  int64
	OffsetHeightMicrons int64
	Alignment           string
}

// PrintTicketSummary 保存从打印票据中提取的高层语义摘要，供虚拟打印机与驱动统一查询
type PrintTicketSummary struct {
	Resolution            *PrintResolution
	OutputQuality         string
	PhotoPrintingIntent   string
	InputBin              string
	OutputBin             string
	MediaType             string
	MediaSize             *Point
	MediaWidthMicrons     int64
	MediaHeightMicrons    int64
	MediaSizeName         string
	ImageableArea         *Rect
	Borderless            bool
	Scaling               *PrintScalingSummary
	MirrorImage           string
	Orientation           string
	OutputColor           *PrintColor
	Negative              bool
	Watermark             *PrintWatermark
	Copies                int
	JobCopies             int
	DocumentCopies        int
	PageCopies            int
	Collate               string
	JobCollate            string
	DocumentCollate       string
	Duplex                PrintDuplex
	ManualDuplex          bool
	NUp                   int
	PresentationDirection string
	PageOrder             string
	Poster                int
	PageRanges            string
	Finishing             PrintFinishing
	ColorPlan             *PrintColorPlan
}

// PrintPageMapping 保存源页面在打印计划某张纸面中的放置索引、独立放置副本及所在纸面上下文
type PrintPageMapping struct {
	SheetIndex        int
	IsBack            bool
	PlacementIndex    int
	Placement         PrintPlacement
	SideWidth         float64
	SideHeight        float64
	SideMediaClip     Rect
	Gutter            *Rect
	BackFlipTransform Matrix
}

// PrintStreamMode 表示打印票据对应的流式拼版执行模式
type PrintStreamMode uint8

// PrintStreamCapability 保存打印票据的流式处理可行性分析结果、建议窗口页数、有效页码过滤规则及原因
type PrintStreamCapability struct {
	Mode               PrintStreamMode
	WindowPages        int
	Duplex             PrintDuplex
	NUp                int
	Poster             int
	Copies             int
	ReverseOrder       bool
	Booklet            bool
	CollatedMultiCopy  bool
	HasPageRanges      bool
	PageRanges         string
	MonotonicPageRange bool
	Reasons            []string
}

// printPageRangeSpan 保存DocumentPageRanges词法解析后的闭区间端点（一基页号）
type printPageRangeSpan struct {
	start *big.Int
	end   *big.Int
}

// String 返回单双面打印模式名称
// 返回: string 单双面模式名称
func (d PrintDuplex) String() string {
	switch d {
	case PrintSimplex:
		return "OneSided"
	case PrintDuplexLongEdge:
		return "TwoSidedLongEdge"
	case PrintDuplexShortEdge:
		return "TwoSidedShortEdge"
	default:
		return fmt.Sprintf("PrintDuplex(%d)", d)
	}
}

// DefaultPrintPlanOptions 返回默认的打印作业计划参数
// 返回: PrintPlanOptions 打印计划参数
func DefaultPrintPlanOptions() PrintPlanOptions {
	return PrintPlanOptions{Print: DefaultPrintLayoutOptions(), MaxSheets: 1 << 16, MaxPlacements: 1 << 18, MaxWork: 1 << 28}
}

// String 返回水印叠放层级名称
// 返回: string 叠放层级名称
func (l PrintWatermarkLayer) String() string {
	switch l {
	case PrintWatermarkLayerUnknown:
		return "Unknown"
	case PrintWatermarkOverlay:
		return "Overlay"
	case PrintWatermarkUnderlay:
		return "Underlay"
	default:
		return fmt.Sprintf("PrintWatermarkLayer(%d)", l)
	}
}

// String 返回打印签名策略名称
// 返回: string 签名策略名称
func (p PrintSignaturePolicy) String() string {
	switch p {
	case PrintSignatureFromTicket:
		return "FromTicket"
	case PrintSignatureIgnore:
		return "Ignore"
	case PrintSignatureReportError:
		return "ReportError"
	case PrintSignatureRequireValid:
		return "RequireValid"
	default:
		return fmt.Sprintf("PrintSignaturePolicy(%d)", p)
	}
}

// BackFlipTransform 返回双面背面相对正面同向进纸坐标的翻面矩阵，单面或无背面返回单位矩阵
// 正反面页面布局保持正常阅读方向，虚拟打印机驱动可左乘此矩阵完成长边、短边或小册子折脊背面翻转
// 返回: Matrix 恒等或一百八十度旋转矩阵
func (s PrintSheet) BackFlipTransform() Matrix {
	if s.Back == nil || s.Duplex == PrintSimplex || !geometryFinite(s.Back.Width, s.Back.Height) || s.Back.Width <= 0 || s.Back.Height <= 0 {
		return IdentityMatrix()
	}
	duplex := s.Duplex
	if s.Booklet {
		duplex = PrintDuplexShortEdge
	}
	if !printBackRotates(duplex, s.Back.Width, s.Back.Height) {
		return IdentityMatrix()
	}
	return Matrix{A: -1, D: -1, E: s.Back.Width, F: s.Back.Height}
}

// PrintPlan 按有效票据生成选页、份数、逐份、拼版、双面及装订留白的输出计划
// 缺省为全部页面、1份、Collated、1页拼版、OneSided与None装订；仅校验页面头与布局标记，内容错误由绘制方法报告
// 入参: ctx 取消Context，nil采用Background, options 作业、介质及预算参数，nil采用默认值
// 返回: *PrintPlan 独立纸张计划，失败为nil, error 票据、组合、资源、取消或关闭错误
func (r *Reader) PrintPlan(ctx context.Context, options *PrintPlanOptions) (*PrintPlan, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
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
		return nil, fmt.Errorf("%w: print plan options", ErrInvalid)
	}
	if err := validatePrintMedia(configuration.Print.Media); err != nil {
		return nil, err
	}
	settings, err := printSettingsOptions(ctx, &configuration.Print.Settings)
	if err != nil {
		return nil, err
	}
	settings.ignoreUnsupported = configuration.IgnoreUnsupportedFeatures || configuration.Print.IgnoreUnsupportedFeatures
	if len(r.pages) > settings.Limits.MaxPageCount {
		return nil, fmt.Errorf("%w: print plan input page count", ErrLimit)
	}
	builder := printPlanBuilder{reader: r, options: configuration, settings: settings, remaining: configuration.MaxWork, metadata: min(r.limits.MaxMetadataBytes, r.limits.MaxPackageBytes, settings.Limits.MaxMetadataBytes, settings.Limits.MaxPackageBytes), tickets: make(map[string]*PrintTicket), validated: make(map[*PrintSettings]int64)}
	plan, err := builder.build()
	if err != nil {
		return nil, err
	}
	return plan, nil
}

// addDiagnostic 按去重集合记录计划诊断，避免连续多份或重复页面成倍放大诊断数量
// 入参: item 计划诊断条目
func (b *printPlanBuilder) addDiagnostic(item Diagnostic) {
	if b.diagnosticSeen == nil {
		b.diagnosticSeen = make(map[Diagnostic]struct{})
	}
	if _, exists := b.diagnosticSeen[item]; exists {
		return
	}
	b.diagnosticSeen[item] = struct{}{}
	b.diagnostics = append(b.diagnostics, item)
}

// step 在昂贵处理或编排步骤前执行累计预算和取消检查
// 入参: work 本次计费量
// 返回: error 预算或取消错误
func (b *printPlanBuilder) step(work uint64) error {
	if err := checkContext(b.settings.context); err != nil {
		return err
	}
	if work > b.remaining {
		return fmt.Errorf("%w: print plan work", ErrLimit)
	}
	b.remaining -= work
	return nil
}

// build 先生成文档描述，再按纸张级逐份和作业顺序展开，不逆转纸面中的页面
// 返回: *PrintPlan 完整计划, error 读取、设置、预算或编排错误
func (b *printPlanBuilder) build() (*PrintPlan, error) {
	base := b.options.Print.Defaults
	if base == nil {
		base = &PrintSettings{Version: 1}
	}
	job, err := b.merge(b.reader.sequence, base)
	if err != nil {
		return nil, err
	}
	b.signatures, err = b.reader.readPrintSignatures(b.settings.context, job, b.options.Signatures)
	if err != nil {
		return nil, err
	}
	if !b.signatures.Allowed {
		return nil, &PrintSignatureError{Report: b.signatures}
	}
	control := newPrintLayoutSettings(job, b.settings)
	if err := control.checkBindingConflict(); err != nil {
		return nil, err
	}
	jobFinishing, _, err := control.binding("JobBindAllDocuments")
	if err != nil {
		return nil, err
	}
	b.jobFinishing = jobFinishing
	copies, err := control.count("JobCopiesAllDocuments", 1, b.options.MaxPlacements)
	if err != nil {
		return nil, err
	}
	collated, err := control.choice("JobCollateAllDocuments", "Collated", "Collated", "Uncollated")
	if err != nil {
		return nil, err
	}
	order, err := control.choice("JobPageOrder", "Standard", "Standard", "Reverse")
	if err != nil {
		return nil, err
	}
	nup, direction, err := control.nup("JobNUpAllDocumentsContiguously", b.options.MaxPlacements)
	if err != nil {
		return nil, err
	}
	duplex, manual, err := control.duplex("JobDuplexAllDocumentsContiguously")
	if err != nil {
		return nil, err
	}
	jobDuplexOpt, _, _ := control.option(job.Elements, "JobDuplexAllDocumentsContiguously")
	jobHasDuplex := jobDuplexOpt != nil
	var documents []printPlanDocument
	var documentFinishing []PrintFinishing
	first := 0
	for index, source := range b.reader.documents {
		document, err := b.document(index, source, first, job, nup, direction, duplex, manual)
		if err != nil {
			return nil, err
		}
		documents = append(documents, document)
		documentFinishing = append(documentFinishing, document.documentFinishing)
		first += len(source.Pages)
	}
	if b.selected == 0 {
		return b.finish(&PrintPlan{JobFinishing: jobFinishing, DocumentFinishing: documentFinishing})
	}
	plan := &PrintPlan{JobFinishing: jobFinishing, DocumentFinishing: documentFinishing}
	if err := b.assembleSheets(plan, documents, jobFinishing, copies, collated == "Collated", order == "Reverse", nup, duplex, manual, jobHasDuplex); err != nil {
		return nil, err
	}
	return b.finish(plan)
}

// assembleSheets 按作业装订、拼版、双面、份数、逐份与页序编排文档列表并填充输出计划的纸张序列
// 入参: plan 目标输出计划, documents 文档级编排列表, jobFinishing 作业装订配置, copies 作业份数, collated 是否作业级逐份, reverse 是否逆序输出, nup 作业拼版页数, duplex 作业双面模式, manual 是否手动双面, jobHasDuplex 作业票据是否显式声明双面
// 返回: error 冲突、容量、预算或取消错误
func (b *printPlanBuilder) assembleSheets(plan *PrintPlan, documents []printPlanDocument, jobFinishing PrintFinishing, copies int, collated, reverse bool, nup int, duplex PrintDuplex, manual, jobHasDuplex bool) error {
	if jobFinishing.Binding == PrintBindingBooklet {
		var jobPages []printPlanPage
		bookletManual := manual
		seenDocDuplex := false
		var docDuplexMode PrintDuplex
		var docManualMode bool
		for _, document := range documents {
			if len(document.pages) == 0 {
				continue
			}
			if document.hasDuplex {
				if seenDocDuplex && (docDuplexMode != document.duplex || docManualMode != document.manual) {
					return fmt.Errorf("%w: conflicting document duplex in job booklet", ErrUnsupported)
				}
				seenDocDuplex, docDuplexMode, docManualMode = true, document.duplex, document.manual
			}
			if document.collated {
				for range document.copies {
					for _, page := range document.pages {
						for range page.copies {
							if err := b.step(1); err != nil {
								return err
							}
							if len(jobPages) >= b.options.MaxPlacements {
								return fmt.Errorf("%w: booklet page count", ErrLimit)
							}
							jobPages = append(jobPages, page)
						}
					}
				}
			} else {
				for _, page := range document.pages {
					if document.copies > b.options.MaxPlacements/page.copies {
						return fmt.Errorf("%w: booklet page count", ErrLimit)
					}
					for range document.copies * page.copies {
						if err := b.step(1); err != nil {
							return err
						}
						if len(jobPages) >= b.options.MaxPlacements {
							return fmt.Errorf("%w: booklet page count", ErrLimit)
						}
						jobPages = append(jobPages, page)
					}
				}
			}
		}
		if seenDocDuplex {
			if jobHasDuplex && (duplex != docDuplexMode || manual != docManualMode) {
				return fmt.Errorf("%w: job and document duplex conflict in booklet", ErrUnsupported)
			}
			bookletManual = docManualMode
		}
		template := &PrintPlan{}
		packer := printSheetPacker{builder: b, output: template, temporary: true}
		if err := packer.bookletPages(jobPages, jobFinishing, bookletManual); err != nil {
			return err
		}
		if err := b.copyDocument(plan, template.Sheets, copies, collated); err != nil {
			return err
		}
		if reverse {
			slices.Reverse(plan.Sheets)
		}
		return nil
	}
	continuous := nup > 1 || duplex != PrintSimplex
	if continuous {
		for _, document := range documents {
			if len(document.pages) > 0 && !document.collated && (document.copies > 1 || !collated && copies > 1) {
				return fmt.Errorf("%w: uncollated copies conflict with job-contiguous sheet packing", ErrUnsupported)
			}
		}
		rounds := copies
		if !collated {
			rounds = 1
		}
		for range rounds {
			if err := b.step(1); err != nil {
				return err
			}
			packer := printSheetPacker{builder: b, output: plan}
			for _, document := range documents {
				if len(document.pages) == 0 {
					continue
				}
				repeats := document.copies
				if !collated {
					if copies > b.options.MaxPlacements/repeats {
						return fmt.Errorf("%w: print plan document copies", ErrLimit)
					}
					repeats *= copies
				}
				if document.separate {
					if err := packer.flush(); err != nil {
						return err
					}
				}
				for range repeats {
					if document.separateCopies {
						if err := packer.flush(); err != nil {
							return err
						}
					}
					if err := packer.document(document); err != nil {
						return err
					}
					if document.separateCopies {
						if err := packer.flush(); err != nil {
							return err
						}
					}
				}
				if document.separate {
					if err := packer.flush(); err != nil {
						return err
					}
				}
			}
			if err := packer.flush(); err != nil {
				return err
			}
		}
	} else {
		templates := make([][]PrintSheet, len(documents))
		var active []int
		for index, document := range documents {
			if err := checkContext(b.settings.context); err != nil {
				return err
			}
			template := &PrintPlan{}
			packer := printSheetPacker{builder: b, output: template, temporary: true}
			if err := packer.document(document); err != nil {
				return err
			}
			if err := packer.flush(); err != nil {
				return err
			}
			templates[index] = template.Sheets
			if len(template.Sheets) > 0 {
				active = append(active, index)
			}
		}
		if collated {
			for range copies {
				if err := b.step(1); err != nil {
					return err
				}
				for _, index := range active {
					document := documents[index]
					if err := b.copyDocument(plan, templates[index], document.copies, document.collated); err != nil {
						return err
					}
				}
			}
		} else {
			for _, index := range active {
				document := documents[index]
				if document.copies > b.options.MaxPlacements/copies {
					return fmt.Errorf("%w: print document copy product", ErrLimit)
				}
				if err := b.copyDocument(plan, templates[index], document.copies*copies, document.collated); err != nil {
					return err
				}
			}
		}
	}
	if reverse {
		slices.Reverse(plan.Sheets)
	}
	return nil
}

// copyDocument 按整组或逐张复制文档模板，逐张复制不会交换双面纸张的正反面
// 入参: plan 输出计划, sheets 文档纸张, copies 份数, collated 是否逐份
// 返回: error 纸张、放置或工作预算错误
func (b *printPlanBuilder) copyDocument(plan *PrintPlan, sheets []PrintSheet, copies int, collated bool) error {
	if len(sheets) == 0 {
		return b.step(1)
	}
	if collated {
		for range copies {
			if err := b.step(1); err != nil {
				return err
			}
			for _, sheet := range sheets {
				if err := b.appendSheet(plan, sheet, false); err != nil {
					return err
				}
			}
		}
	} else {
		for _, sheet := range sheets {
			for range copies {
				if err := b.appendSheet(plan, sheet, false); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

// appendSheet 检查输出容量并独立复制纸面，不让重复副本共享可变页面列表
// 入参: plan 输出计划, sheet 待追加纸张, temporary 是否为文档模板
// 返回: error 输出或工作预算错误
func (b *printPlanBuilder) appendSheet(plan *PrintPlan, sheet PrintSheet, temporary bool) error {
	count := len(sheet.Front.Pages)
	if sheet.Back != nil {
		count += len(sheet.Back.Pages)
	}
	placements, sheets := &b.placements, &b.sheets
	if temporary {
		placements, sheets = &b.templatePages, &b.templateSheets
	}
	if *sheets >= b.options.MaxSheets || count > b.options.MaxPlacements-*placements {
		return fmt.Errorf("%w: print plan output capacity", ErrLimit)
	}
	if err := b.step(uint64(count + 1)); err != nil {
		return err
	}
	*placements += count
	*sheets++
	sheet.Front.Pages = clonePrintPlacements(sheet.Front.Pages)
	sheet.Front.Resolution = clonePrintResolution(sheet.Front.Resolution)
	if b.signatures != nil {
		sheet.Front.SignaturePolicy = b.signatures.Policy
	}
	if sheet.Front.Gutter != nil {
		gutter := *sheet.Front.Gutter
		sheet.Front.Gutter = &gutter
	}
	if sheet.Back != nil {
		back := *sheet.Back
		if b.signatures != nil {
			back.SignaturePolicy = b.signatures.Policy
		}
		back.Pages = clonePrintPlacements(back.Pages)
		back.Resolution = clonePrintResolution(back.Resolution)
		if back.Gutter != nil {
			gutter := *back.Gutter
			back.Gutter = &gutter
		}
		sheet.Back = &back
	}
	plan.Sheets = append(plan.Sheets, sheet)
	return nil
}

// clonePrintPlacements 复制纸面放置及水印、色彩与分辨率描述，避免不同副本共享可变元数据
// 入参: source 源页面放置
// 返回: []PrintPlacement 独立放置
func clonePrintPlacements(source []PrintPlacement) []PrintPlacement {
	result := append([]PrintPlacement(nil), source...)
	for index := range result {
		result[index].Color = clonePrintColorPlan(result[index].Color)
		result[index].Resolution = clonePrintResolution(result[index].Resolution)
		if result[index].Watermark != nil {
			mark := *result[index].Watermark
			result[index].Watermark = &mark
		}
	}
	return result
}

// parsePrintPageRangeSpans 严格校验并解析DocumentPageRanges词法为闭区间列表，禁止任何空白字符
// 入参: text 原始范围文本, options 数值预算及取消配置
// 返回: []printPageRangeSpan 闭区间列表, error 词法、数值预算或取消错误
func parsePrintPageRangeSpans(text string, options printSettingsConfig) ([]printPageRangeSpan, error) {
	if text == "" {
		return nil, checkContext(options.context)
	}
	for _, r := range text {
		if unicode.IsSpace(r) {
			return nil, fmt.Errorf("%w: print page range whitespace", ErrInvalid)
		}
	}
	var spans []printPageRangeSpan
	for {
		if err := checkContext(options.context); err != nil {
			return nil, err
		}
		item, rest, more := strings.Cut(text, ",")
		startText, endText, ranged := strings.Cut(item, "-")
		if !ranged {
			endText = startText
		}
		var bounds [2]*big.Int
		for index, number := range []string{startText, endText} {
			if number == "" {
				return nil, fmt.Errorf("%w: empty print page range endpoint", ErrInvalid)
			}
			for _, digit := range number {
				if digit < '0' || digit > '9' {
					return nil, fmt.Errorf("%w: print page range syntax", ErrInvalid)
				}
			}
			value, err := printParameterNumber(number, options)
			if err != nil {
				return nil, err
			}
			bounds[index] = new(big.Int).Set(value.Num())
		}
		spans = append(spans, printPageRangeSpan{start: bounds[0], end: bounds[1]})
		if !more {
			break
		}
		text = rest
	}
	return spans, nil
}

// printPageRanges 解析严格范围词法，遵循Print Schema规范禁止任何空白字符，保留列表顺序、重复页和反向区间，先裁至文档范围再展开
// 入参: text 原始范围文本，空表示全部, count 文档页数, maximum 输出选择上限, options 数值及取消参数
// 返回: []int 零基页号, bool 是否含越界页, error 词法、数量、资源或取消错误
func printPageRanges(text string, count, maximum int, options printSettingsConfig) ([]int, bool, error) {
	if text == "" {
		if count > maximum {
			return nil, false, fmt.Errorf("%w: print page selection count", ErrLimit)
		}
		result := make([]int, count)
		for index := range result {
			result[index] = index
		}
		return result, false, checkContext(options.context)
	}
	spans, err := parsePrintPageRangeSpans(text, options)
	if err != nil {
		return nil, false, err
	}
	var result []int
	outside := false
	limit := big.NewInt(int64(count))
	one := big.NewInt(1)
	for _, span := range spans {
		if err := checkContext(options.context); err != nil {
			return nil, false, err
		}
		reverse := span.start.Cmp(span.end) > 0
		low, high := span.start, span.end
		if reverse {
			low, high = high, low
		}
		outside = outside || low.Cmp(one) < 0 || high.Cmp(limit) > 0
		if low.Cmp(one) < 0 {
			low = one
		}
		if high.Cmp(limit) > 0 {
			high = limit
		}
		if low.Cmp(high) <= 0 {
			first, last := int(low.Int64()), int(high.Int64())
			if last-first+1 > maximum-len(result) {
				return nil, false, fmt.Errorf("%w: print page selection count", ErrLimit)
			}
			for offset := 0; offset < last-first+1; offset++ {
				page := first + offset
				if reverse {
					page = last - offset
				}
				result = append(result, page-1)
			}
		}
	}
	return result, outside, nil
}

// document 读取一个文档的页范围和控制设置，只为选中页面解析布局及页面票据
// 入参: index 文档序号, source 文档引用, first 全局起始页号, job 继承设置, jobNUp 作业拼版, direction 作业排列, duplex 作业双面, manual 是否手动双面
// 返回: printPlanDocument 轻量描述, error 设置、页面、组合或预算错误
func (b *printPlanBuilder) document(index int, source Document, first int, job *PrintSettings, jobNUp int, direction string, duplex PrintDuplex, manual bool) (printPlanDocument, error) {
	result := printPlanDocument{nup: jobNUp, direction: direction, duplex: duplex, manual: manual}
	model, err := b.merge(source.Part, job)
	if err != nil {
		return result, err
	}
	control := newPrintLayoutSettings(model, b.settings)
	if err := control.checkBindingConflict(); err != nil {
		return result, err
	}
	result.documentFinishing, _, err = control.binding("DocumentBinding")
	if err != nil {
		return result, err
	}
	result.finishing = b.jobFinishing
	if result.documentFinishing.Binding != PrintBindingNone {
		result.finishing = result.documentFinishing
		result.separate = true
		if result.documentFinishing.Binding == PrintBindingBooklet {
			result.separateCopies = true
		}
	}
	result.copies, err = control.count("DocumentCopiesAllPages", 1, b.options.MaxPlacements)
	if err != nil {
		return result, err
	}
	collation, err := control.choice("DocumentCollate", "Collated", "Collated", "Uncollated")
	if err != nil {
		return result, err
	}
	result.collated = collation == "Collated"
	nup, order, err := control.nup("DocumentNUp", b.options.MaxPlacements)
	if err != nil {
		return result, err
	}
	if nup > 1 {
		if jobNUp > 1 {
			return result, fmt.Errorf("%w: simultaneous job and document NUp", ErrUnsupported)
		}
		result.nup, result.direction, result.separate = nup, order, true
	} else if jobNUp > 1 {
		if option, _, _ := control.option(model.Elements, "DocumentNUp"); option != nil {
			return result, fmt.Errorf("%w: document NUp conflicts with job NUp", ErrUnsupported)
		}
	}
	if result.finishing.Binding == PrintBindingBooklet && result.nup > 1 {
		return result, fmt.Errorf("%w: booklet binding conflicts with NUp", ErrUnsupported)
	}
	documentDuplex, documentManual, err := control.duplex("DocumentDuplex")
	if err != nil {
		return result, err
	}
	docDuplexOpt, _, _ := control.option(model.Elements, "DocumentDuplex")
	result.hasDuplex = docDuplexOpt != nil
	if documentDuplex != PrintSimplex {
		if duplex != PrintSimplex {
			return result, fmt.Errorf("%w: simultaneous job and document duplex", ErrUnsupported)
		}
		result.duplex, result.manual, result.separate, result.separateCopies = documentDuplex, documentManual, true, true
	} else if duplex != PrintSimplex {
		if docDuplexOpt != nil {
			return result, fmt.Errorf("%w: document simplex conflicts with job duplex", ErrUnsupported)
		}
	}
	ranges := ""
	if value := printParamValue(control.values, "DocumentPageRanges"); value != nil {
		if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
			return result, fmt.Errorf("%w: document page ranges type", ErrInvalid)
		}
		ranges = value.Text
	}
	pages, outside, err := printPageRanges(ranges, len(source.Pages), b.options.MaxPlacements-b.selected, b.settings)
	if err != nil {
		return result, &PartError{Part: source.Part, Err: err}
	}
	b.selected += len(pages)
	if outside {
		b.addDiagnostic(Diagnostic{Part: source.Part, Element: "ParameterInit", Attribute: "name", Message: "out-of-range document pages ignored"})
	}
	cache := make(map[int]printPlanPage)
	for _, local := range pages {
		if err := b.step(1); err != nil {
			return result, err
		}
		page, present := cache[local]
		if !present {
			page, err = b.page(first+local, source.Pages[local].Part, model)
			if err != nil {
				return result, err
			}
			page.document = index
			if page.poster > 1 && result.finishing.Binding == PrintBindingBooklet {
				return result, fmt.Errorf("%w: booklet binding conflicts with poster", ErrUnsupported)
			}
			if page.poster > 1 && result.nup != 1 {
				return result, fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
			}
			if page.poster > 1 && result.duplex != PrintSimplex {
				b.addDiagnostic(Diagnostic{Part: source.Pages[local].Part, Element: "PagePoster", Message: "poster sheets use single-sided output"})
			}
			cache[local] = page
		}
		result.pages = append(result.pages, page)
	}
	return result, nil
}

// page 读取单页的有效控制和布局，返回后不保留场景、资源图或票据树
// 入参: index 全局页号, source 页面URI, document 已合并文档设置
// 返回: printPlanPage 页面描述, error 页面、布局、设置或预算错误
func (b *printPlanBuilder) page(index int, source string, document *PrintSettings) (printPlanPage, error) {
	result := printPlanPage{index: index}
	model, err := b.merge(source, document)
	if err != nil {
		return result, err
	}
	control := newPrintLayoutSettings(model, b.settings)
	result.copies, err = control.count("PageCopies", 1, b.options.MaxPlacements)
	if err != nil {
		return result, err
	}
	front, err := control.choice("PageForceFrontSide", "None", "None", "ForceFrontSide")
	if err != nil {
		return result, err
	}
	result.force = front == "ForceFrontSide"
	result.poster, err = control.poster(min(b.options.MaxSheets, b.options.MaxPlacements))
	if err != nil {
		return result, err
	}
	ignoreUnsupported := b.options.IgnoreUnsupportedFeatures || b.options.Print.IgnoreUnsupportedFeatures
	state, err := preparePrintPageState(b.settings.context, model, b.settings, nil, PrintMedia{}, printPageStateOptions{
		stripSignatures:      b.signatures != nil,
		stripPlanFeatures:    true,
		ignoreUnsupported:    ignoreUnsupported,
		ignoreColorPlanError: ignoreUnsupported,
	})
	if err != nil {
		return result, err
	}
	size, err := b.reader.pkg.partSize(strings.ToLower(source))
	if err != nil {
		return result, err
	}
	if err := b.step(size); err != nil {
		return result, err
	}
	root, err := b.reader.readFixedPartLoader(source, "fixedpage", "FixedPage", nil, b.settings.context)
	if err != nil {
		return result, err
	}
	page, err := parsePageHeader(root, source, b.reader.format)
	if err != nil {
		return result, err
	}
	if err := state.computeLayout(b.settings, page, b.options.Print.Media, true); err != nil {
		return result, err
	}
	result.watermark = state.watermark
	result.negative = state.negative
	result.color = state.outputColor
	result.colorPlan = state.colorPlan
	result.resolution = state.resolution
	result.layout = *state.layout
	result.rotation = state.rotation
	result.backLayout = state.backLayout
	return result, nil
}

// merge 复用票据链校验与根设置合并，同一票据载荷仅从封装读取一次，无独立票据时通过纯内存预算校验直接复用基线
// 入参: source 固定布局源部件, base 已继承设置
// 返回: *PrintSettings 独立有效设置, error 读取、合并、预算或取消错误
func (b *printPlanBuilder) merge(source string, base *PrintSettings) (*PrintSettings, error) {
	if err := b.step(1); err != nil {
		return nil, err
	}
	ticket, err := b.reader.printTicketReference(source)
	if err != nil {
		return nil, err
	}
	if ticket == nil {
		if _, ok := b.validated[base]; ok {
			return base, nil
		}
		validated, err := validatePrintSettingsModel(base, b.settings, printDocumentTicket)
		if err != nil {
			return nil, err
		}
		size, err := printSettingsEncodedSize(validated, b.settings, printDocumentTicket)
		if err != nil {
			return nil, err
		}
		if err := b.step(uint64(size) * 3); err != nil {
			return nil, err
		}
		if b.settings.ignoreUnsupported {
			validated = printStripPrivateExtensions(validated)
		}
		b.validated[validated] = size
		return validated, nil
	}
	size, ok := b.validated[base]
	if !ok || size < 0 {
		checked := base
		if !ok {
			checked, err = validatePrintSettingsModel(base, b.settings, printDocumentTicket)
			if err != nil {
				return nil, err
			}
		}
		size, err = printSettingsEncodedSize(checked, b.settings, printDocumentTicket)
		if err != nil {
			return nil, err
		}
		if ok {
			b.validated[base] = size
		}
	}
	if err := b.step(uint64(size) * 3); err != nil {
		return nil, err
	}
	key := strings.ToLower(ticket.Part)
	if cached := b.tickets[key]; cached != nil {
		ticket.Data = cached.Data
	} else {
		if err := b.reader.readPrintTicketData(ticket, min(b.metadata, b.settings.Limits.MaxPartBytes), b.settings.context); err != nil {
			return nil, err
		}
		b.metadata -= int64(len(ticket.Data))
		b.tickets[key] = ticket
	}
	if err := b.step(uint64(len(ticket.Data)) * 3); err != nil {
		return nil, err
	}
	configuration := b.settings.PrintSettingsOptions
	configuration.Scope = ticket.Scope
	delta, err := ticket.Settings(b.settings.context, &configuration)
	if err != nil {
		return nil, &PartError{Part: ticket.Part, Err: err}
	}
	merged, err := MergePrintSettings(b.settings.context, base, delta, &b.settings.PrintSettingsOptions)
	if err != nil {
		return nil, err
	}
	if b.settings.ignoreUnsupported {
		merged = printStripPrivateExtensions(merged)
	}
	b.validated[merged] = -1
	return merged, nil
}

// printParamValue 按Print Schema公共关键字命名空间优先级查找参数值
// 入参: values 参数映射, name 参数本地名称
// 返回: *PrintValue 匹配值，未声明时为nil
func printParamValue(values map[xml.Name]*PrintValue, name string) *PrintValue {
	for _, space := range [4]string{printKeywordsNS, printKeywordsV11NS, printKeywordsV12NS, printKeywords2NS} {
		if value := values[xml.Name{Space: space, Local: name}]; value != nil {
			return value
		}
	}
	return nil
}

// count 读取正整数份数并在乘法或循环展开前检查上限，不截断大整数
// 入参: name 参数名称, fallback 缺省值, maximum 本次容量上限
// 返回: int 份数, error 类型、数值、资源或取消错误
func (s *printLayoutSettings) count(name string, fallback, maximum int) (int, error) {
	value := printParamValue(s.values, name)
	if value == nil {
		return fallback, nil
	}
	return s.integer(value, name, maximum)
}

// integer 将票据整数映射为有界正整数，不用浮点计算页数、份数或拼版数量
// 入参: value 标量值, name 错误位置名称, maximum 容量上限
// 返回: int 数量, error 类型、正值、资源或取消错误
func (s *printLayoutSettings) integer(value *PrintValue, name string, maximum int) (int, error) {
	if value == nil || value.Type != (xml.Name{Space: printValueNS, Local: "integer"}) || !printInteger(strings.Trim(value.Text, " \t\r\n")) {
		return 0, fmt.Errorf("%w: print plan integer %s", ErrInvalid, name)
	}
	number, err := printParameterNumber(value.Text, s.options)
	if err != nil {
		return 0, err
	}
	if number.Sign() < 1 {
		return 0, fmt.Errorf("%w: print plan positive integer %s", ErrInvalid, name)
	}
	if number.Num().Cmp(big.NewInt(int64(maximum))) > 0 {
		return 0, fmt.Errorf("%w: print plan integer capacity %s", ErrLimit, name)
	}
	return int(number.Num().Int64()), nil
}

// choice 读取不含配置描述的已知作业选项，不按相似名称接受私有关键字
// 入参: name Feature名称, fallback 缺省选项, allowed 支持选项
// 返回: string 选项, error 结构、能力或选择错误
func (s *printLayoutSettings) choice(name, fallback string, allowed ...string) (string, error) {
	option, err := s.leafOption(s.model.Elements, name)
	if err != nil {
		return "", err
	}
	value, err := s.keyword(option, fallback)
	if err != nil {
		return "", err
	}
	for _, candidate := range allowed {
		if value == candidate {
			return value, nil
		}
	}
	return "", fmt.Errorf("%w: print plan option %s/%s", ErrUnsupported, name, value)
}

// scored 读取Option中的独立值或显式参数引用，不解析设备默认参数
// 入参: option 已选Option, name 描述值名称
// 返回: *PrintValue 值，未声明为nil, error 未初始化参数错误
func (s *printLayoutSettings) scored(option *PrintSetting, name string) (*PrintValue, error) {
	for _, property := range option.Children {
		if property.Kind != PrintSettingScoredProperty || !printPublicKeywordSpace(property.Name.Space) || property.Name.Local != name {
			continue
		}
		value, reference := printScoredValue(property.Children)
		if reference != (xml.Name{}) {
			value = s.values[printCanonicalKey(reference)]
			if value == nil {
				return nil, fmt.Errorf("%w: print plan parameter not initialized", ErrUnsupported)
			}
		}
		return value, nil
	}
	return nil, nil
}

// nup 读取每面页数和八向排列设置，Option名称由设备定义，不强行要求公共名称
// 入参: name 作业或文档NUp名称, maximum 放置上限
// 返回: int 每面页数, string 排列方向, error 设置、数值或能力错误
func (s *printLayoutSettings) nup(name string, maximum int) (int, string, error) {
	option, feature, err := s.option(s.model.Elements, name)
	if err != nil || option == nil {
		return 1, "RightBottom", err
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature && (!printPublicKeywordSpace(child.Name.Space) || child.Name.Local != "PresentationDirection") {
			return 0, "", fmt.Errorf("%w: unhandled print plan subfeature", ErrUnsupported)
		}
	}
	value, err := s.scored(option, "PagesPerSheet")
	if err != nil {
		return 0, "", err
	}
	if value == nil {
		return 0, "", fmt.Errorf("%w: print NUp requires a page-count description", ErrUnsupported)
	}
	count, err := s.integer(value, "PagesPerSheet", maximum)
	if err != nil {
		return 0, "", err
	}
	if err := printOptionProperties(option, "PagesPerSheet"); err != nil {
		return 0, "", err
	}
	direction, err := s.leafOption(feature.Children, "PresentationDirection")
	if err != nil {
		return 0, "", err
	}
	text, err := s.keyword(direction, "RightBottom")
	if err != nil {
		return 0, "", err
	}
	switch text {
	case "RightBottom", "BottomRight", "LeftBottom", "BottomLeft", "RightTop", "TopRight", "LeftTop", "TopLeft":
		return count, text, nil
	default:
		return 0, "", fmt.Errorf("%w: print presentation direction", ErrUnsupported)
	}
}

// duplex 读取双面翻页方向及手动操作标志，不对设备背面坐标作未经声明的旋转
// 入参: name 作业或文档双面名称
// 返回: PrintDuplex 双面方式, bool 是否手动双面, error 结构、值或能力错误
func (s *printLayoutSettings) duplex(name string) (PrintDuplex, bool, error) {
	option, err := s.leafOption(s.model.Elements, name)
	if err != nil || option == nil {
		return PrintSimplex, false, err
	}
	if !printPublicKeywordSpace(option.Name.Space) {
		return PrintSimplex, false, fmt.Errorf("%w: private duplex option", ErrUnsupported)
	}
	mode := PrintSimplex
	switch option.Name.Local {
	case "OneSided":
		for _, child := range option.Children {
			if child.Kind != PrintSettingProperty {
				return mode, false, fmt.Errorf("%w: OneSided option content", ErrInvalid)
			}
		}
		return mode, false, nil
	case "TwoSidedLongEdge":
		mode = PrintDuplexLongEdge
	case "TwoSidedShortEdge":
		mode = PrintDuplexShortEdge
	default:
		return mode, false, fmt.Errorf("%w: duplex option", ErrUnsupported)
	}
	if err := printOptionProperties(option, "DuplexMode"); err != nil {
		return mode, false, err
	}
	value, err := s.scored(option, "DuplexMode")
	if err != nil || value == nil {
		return mode, false, err
	}
	if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) || value.Text != "Automatic" && value.Text != "Manual" {
		return mode, false, fmt.Errorf("%w: duplex mode", ErrInvalid)
	}
	return mode, value.Text == "Manual", nil
}

// document 按源页面顺序放置页面副本，PageCopies不会被NUp或逐份设置分散，Booklet按骑马订书帖拼版
// 入参: document 文档描述
// 返回: error 纸张、页面、预算或取消错误
func (p *printSheetPacker) document(document printPlanDocument) error {
	if document.finishing.Binding == PrintBindingBooklet {
		if err := p.flush(); err != nil {
			return err
		}
		var pages []printPlanPage
		for _, page := range document.pages {
			for range page.copies {
				if err := p.builder.step(1); err != nil {
					return err
				}
				if len(pages) >= p.builder.options.MaxPlacements {
					return fmt.Errorf("%w: booklet page count", ErrLimit)
				}
				pages = append(pages, page)
			}
		}
		return p.bookletPages(pages, document.finishing, document.manual)
	}
	for _, page := range document.pages {
		for range page.copies {
			var err error
			if page.poster > 1 {
				err = p.poster(page, document)
			} else {
				err = p.add(page, document)
			}
			if err != nil {
				return err
			}
		}
	}
	return nil
}

// bookletPages 按标准骑马订小册子规则将页流补齐至四的倍数并生成双面对折拼版纸张
// 骑马钉折脊始终沿物理介质较短边对折，实际纸张双面轴统一规范为短边双面，正反面页面保持正常阅读方向并由BackFlipTransform承载背面翻转
// 入参: pages 已展开的逻辑页流, finishing 小册子装订参数, manual 是否手动双面
// 返回: error 几何、强制正面冲突、容量或取消错误
func (p *printSheetPacker) bookletPages(pages []printPlanPage, finishing PrintFinishing, manual bool) error {
	if len(pages) == 0 {
		return nil
	}
	padded := ((len(pages) + 3) / 4) * 4
	sheets := padded / 4
	for sheetIndex := range sheets {
		if err := p.builder.step(1); err != nil {
			return err
		}
		backCover, frontCover := padded-1-2*sheetIndex, 2*sheetIndex
		insideFront, insideBack := 2*sheetIndex+1, padded-2-2*sheetIndex
		ref := pages[frontCover]
		frontSlots := [2]int{backCover, frontCover}
		backSlots := [2]int{insideFront, insideBack}
		if printBookletSwapVisual(ref) {
			frontSlots = [2]int{frontCover, backCover}
			backSlots = [2]int{insideBack, insideFront}
		}
		front, err := p.bookletSide(pages, frontSlots, ref, finishing, false)
		if err != nil {
			return err
		}
		var back *PrintSide
		if backSlots[0] < len(pages) || backSlots[1] < len(pages) {
			side, err := p.bookletSide(pages, backSlots, ref, finishing, true)
			if err != nil {
				return err
			}
			back = &side
		}
		sheet := PrintSheet{Front: front, Back: back, Duplex: PrintDuplexShortEdge, ManualDuplex: manual, Booklet: true}
		if err := p.builder.appendSheet(p.output, sheet, p.temporary); err != nil {
			return err
		}
	}
	return nil
}

// printBookletSwapVisual 根据基准页介质折脊方向与纯方向旋转矩阵判断是否需交换物理槽位以保持视觉左封底右封面
// 入参: ref 当前书帖纸张的基准页
// 返回: bool 是否交换槽位0与槽位1
func printBookletSwapVisual(ref printPlanPage) bool {
	rot := ref.rotation
	if rot.A == 0 && rot.B == 0 && rot.C == 0 && rot.D == 0 {
		return false
	}
	if ref.layout.Height > ref.layout.Width {
		return rot.B+rot.D < 0
	}
	return rot.A+rot.C < 0
}

// printColorModeRank 返回输出色彩模式的保真优先级，彩色高于灰度，灰度高于黑白单色
// 入参: mode 输出色彩模式
// 返回: int 优先级分值
func printColorModeRank(mode PrintColorMode) int {
	switch mode {
	case PrintColorPreserve:
		return 4
	case PrintColorOriginal:
		return 3
	case PrintColorGrayscale:
		return 2
	case PrintColorMonochrome:
		return 1
	default:
		return 0
	}
}

// printMergeBookletColor 合并小册子同面两槽位的输出色彩设置，优先保留更高色彩模式及更高位深
// 入参: first 第一槽位色彩设置, second 第二槽位色彩设置
// 返回: PrintColor 合并后的纸面色彩设置
func printMergeBookletColor(first, second PrintColor) PrintColor {
	rankFirst, rankSecond := printColorModeRank(first.Mode), printColorModeRank(second.Mode)
	if rankSecond > rankFirst {
		return second
	}
	if rankFirst > rankSecond {
		return first
	}
	first.DeviceBitsPerPixel = max(first.DeviceBitsPerPixel, second.DeviceBitsPerPixel)
	first.DriverBitsPerPixel = max(first.DriverBitsPerPixel, second.DriverBitsPerPixel)
	return first
}

// bookletSide 将小册子正反面的最多两个书帖槽位按正常阅读方向映射到折脊两侧的有效可打印区域并避开中心装订留白
// 入参: pages 逻辑页流, slots 左右或上下槽位逻辑页序号, ref 纸张介质基准页, finishing 装订设置, back 是否为背面
// 返回: PrintSide 独立纸面, error 强制正面冲突、变换或范围错误
func (p *printSheetPacker) bookletSide(pages []printPlanPage, slots [2]int, ref printPlanPage, finishing PrintFinishing, back bool) (PrintSide, error) {
	mediaClip := ref.layout.MediaClip
	if back && printBackRotates(PrintDuplexShortEdge, ref.layout.Width, ref.layout.Height) {
		mediaClip = printRotateBox180(mediaClip, ref.layout.Width, ref.layout.Height)
	}
	side := PrintSide{Width: ref.layout.Width, Height: ref.layout.Height, MediaClip: mediaClip}
	hasColor := false
	for _, index := range slots {
		if index >= len(pages) {
			continue
		}
		if !hasColor {
			side.Color = pages[index].color
			hasColor = true
		} else {
			side.Color = printMergeBookletColor(side.Color, pages[index].color)
		}
	}
	side.Gutter = printBindingGutter(finishing, side, PrintDuplexShortEdge, back)
	phys, base, usable := printBookletCells(side)
	rot := ref.rotation
	if rot == (Matrix{}) {
		rot = IdentityMatrix()
	}
	orthDir := side.Height > side.Width && rot.A != 0 || side.Width > side.Height && rot.A == 0
	refSrc := ref.layout.MediaClip
	if refSrc.Width <= 0 || refSrc.Height <= 0 {
		refSrc = Rect{Width: ref.layout.Width, Height: ref.layout.Height}
	}
	refTarget := usable[0]
	if refTarget.Width <= 0 || refTarget.Height <= 0 {
		refTarget = base[0]
	}
	if refTarget.Width <= 0 || refTarget.Height <= 0 {
		refTarget = phys[0]
	}
	rotateBooklet := orthDir && refTarget.Width > 0 && refTarget.Height > 0 && refSrc.Width > 0 && refSrc.Height > 0 && min(refTarget.Width/refSrc.Height, refTarget.Height/refSrc.Width) > min(refTarget.Width/refSrc.Width, refTarget.Height/refSrc.Height)
	for slot, index := range slots {
		if index >= len(pages) {
			continue
		}
		page := pages[index]
		if back && page.force {
			return PrintSide{}, fmt.Errorf("%w: PageForceFrontSide conflicts with booklet back side", ErrUnsupported)
		}
		if len(side.Pages) > 0 && !printSideColorTargetEqual(side, page.colorPlan) {
			p.builder.addDiagnostic(Diagnostic{Element: "PageDestinationColorProfile", Message: "different target declarations share a booklet print side"})
		}
		target, clipBound := usable[slot], usable[slot]
		if target.Width <= 0 || target.Height <= 0 {
			target, clipBound = base[slot], base[slot]
		}
		if target.Width <= 0 || target.Height <= 0 {
			target, clipBound = phys[slot], side.MediaClip
		}
		src := page.layout.MediaClip
		if src.Width <= 0 || src.Height <= 0 {
			src = Rect{Width: page.layout.Width, Height: page.layout.Height}
		}
		var factor float64
		var mapping Matrix
		if rotateBooklet {
			factor = min(target.Width/src.Height, target.Height/src.Width)
			mapping = Matrix{
				B: factor,
				C: -factor,
				E: target.X + (target.Width+factor*src.Height)/2 + factor*src.Y,
				F: target.Y + (target.Height-factor*src.Width)/2 - factor*src.X,
			}
		} else {
			factor = min(target.Width/src.Width, target.Height/src.Height)
			mapping = Matrix{
				A: factor,
				D: factor,
				E: target.X + (target.Width-factor*src.Width)/2 - factor*src.X,
				F: target.Y + (target.Height-factor*src.Height)/2 - factor*src.Y,
			}
		}
		placement := PrintPlacement{
			Page:          page.index,
			DocumentIndex: page.document,
			Transform:     mapping.Mul(page.layout.Transform),
			PageClip:      page.layout.PageClip,
			MediaClip:     printClampBox(printTransformBox(page.layout.MediaClip, mapping), clipBound),
			Watermark:     page.watermark,
			Negative:      page.negative,
			Color:         clonePrintColorPlan(page.colorPlan),
			Resolution:    clonePrintResolution(page.resolution),
		}
		if factor <= 0 || !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(placement.MediaClip.X, placement.MediaClip.Y, placement.MediaClip.Width, placement.MediaClip.Height) {
			return PrintSide{}, fmt.Errorf("%w: print booklet mapping", ErrLimit)
		}
		side.Resolution = printMergeSideResolution(side.Resolution, page.resolution)
		side.Pages = append(side.Pages, placement)
	}
	return side, nil
}

// printBookletCells 按纸张居中折脊切分物理半页、可打印半页与扣除中心留白后的有效槽位矩形
// 入参: side 已计算Gutter的纸面
// 返回: [2]Rect 物理半页, [2]Rect 可打印半页, [2]Rect 扣除留白后的有效槽位
func printBookletCells(side PrintSide) ([2]Rect, [2]Rect, [2]Rect) {
	var phys, base, usable [2]Rect
	if side.Height > side.Width {
		mid := side.Height / 2
		phys[0] = Rect{X: 0, Y: 0, Width: side.Width, Height: mid}
		phys[1] = Rect{X: 0, Y: mid, Width: side.Width, Height: side.Height - mid}
		base[0] = printClampBox(phys[0], side.MediaClip)
		base[1] = printClampBox(phys[1], side.MediaClip)
		usable = base
		if side.Gutter != nil && side.Gutter.Height > 0 {
			usable[0].Height = max(0, min(base[0].Y+base[0].Height, side.Gutter.Y)-base[0].Y)
			bottomStart := max(base[1].Y, side.Gutter.Y+side.Gutter.Height)
			usable[1] = Rect{X: base[1].X, Y: bottomStart, Width: base[1].Width, Height: max(0, base[1].Y+base[1].Height-bottomStart)}
		}
	} else {
		mid := side.Width / 2
		phys[0] = Rect{X: 0, Y: 0, Width: mid, Height: side.Height}
		phys[1] = Rect{X: mid, Y: 0, Width: side.Width - mid, Height: side.Height}
		base[0] = printClampBox(phys[0], side.MediaClip)
		base[1] = printClampBox(phys[1], side.MediaClip)
		usable = base
		if side.Gutter != nil && side.Gutter.Width > 0 {
			usable[0].Width = max(0, min(base[0].X+base[0].Width, side.Gutter.X)-base[0].X)
			rightStart := max(base[1].X, side.Gutter.X+side.Gutter.Width)
			usable[1] = Rect{X: rightStart, Y: base[1].Y, Width: max(0, base[1].X+base[1].Width-rightStart), Height: base[1].Height}
		}
	}
	return phys, base, usable
}

// flush 结束当前物理纸张，空背面保持nil，不插入伪造的源页面
// 返回: error 输出容量或取消错误
func (p *printSheetPacker) flush() error {
	if p.sheet == nil {
		return nil
	}
	if err := p.builder.appendSheet(p.output, *p.sheet, p.temporary); err != nil {
		return err
	}
	p.sheet = nil
	p.frontDone = false
	return nil
}

// add 放置一个页面，介质变更、强制正面及不可合并的控制变更会结束当前纸张
// 入参: page 页面描述, document 当前文档控制
// 返回: error 几何、容量、组合或取消错误
func (p *printSheetPacker) add(page printPlanPage, document printPlanDocument) error {
	if err := p.builder.step(1); err != nil {
		return err
	}
	layout := page.layout
	if p.sheet != nil && (page.force || p.finishing != document.finishing || p.sheet.Duplex != document.duplex || p.sheet.ManualDuplex != document.manual || p.nup != document.nup || p.direction != document.direction || p.sheet.Front.Width != layout.Width || p.sheet.Front.Height != layout.Height || p.sheet.Front.MediaClip != layout.MediaClip) {
		if err := p.flush(); err != nil {
			return err
		}
	}
	if p.sheet != nil && (p.frontDone || len(p.sheet.Front.Pages) == p.nup) && (p.sheet.Duplex == PrintSimplex || p.sheet.Back != nil && len(p.sheet.Back.Pages) == p.nup) {
		if err := p.flush(); err != nil {
			return err
		}
	}
	if p.sheet != nil {
		frontDone := p.frontDone || len(p.sheet.Front.Pages) == p.nup
		if !frontDone && !printSideColorTargetEqual(p.sheet.Front, page.colorPlan) || frontDone && p.sheet.Back != nil && !printSideColorTargetEqual(*p.sheet.Back, page.colorPlan) {
			p.builder.addDiagnostic(Diagnostic{Element: "PageDestinationColorProfile", Message: "different target declarations start a separate print side"})
		}
		if !frontDone && (p.sheet.Front.Color != page.color || !printSideColorTargetEqual(p.sheet.Front, page.colorPlan)) {
			if p.sheet.Duplex == PrintSimplex {
				if err := p.flush(); err != nil {
					return err
				}
			} else {
				p.frontDone = true
			}
		} else if frontDone && p.sheet.Back != nil && (p.sheet.Back.Color != page.color || !printSideColorTargetEqual(*p.sheet.Back, page.colorPlan)) {
			if err := p.flush(); err != nil {
				return err
			}
		}
	}
	if p.sheet == nil {
		p.sheet = &PrintSheet{Front: PrintSide{Width: layout.Width, Height: layout.Height, MediaClip: layout.MediaClip, Color: page.color}, Duplex: document.duplex, ManualDuplex: document.manual}
		p.sheet.Front.Gutter = printBindingGutter(document.finishing, p.sheet.Front, document.duplex, false)
		p.nup, p.direction = document.nup, document.direction
		p.finishing = document.finishing
	}
	side := &p.sheet.Front
	isBack := false
	if p.frontDone || len(side.Pages) == p.nup {
		isBack = true
		if p.sheet.Back == nil {
			backClip := layout.MediaClip
			if printBackRotates(document.duplex, layout.Width, layout.Height) {
				backClip = printRotateBox180(layout.MediaClip, layout.Width, layout.Height)
			}
			p.sheet.Back = &PrintSide{Width: layout.Width, Height: layout.Height, MediaClip: backClip, Color: page.color}
			p.sheet.Back.Gutter = printBindingGutter(document.finishing, *p.sheet.Back, document.duplex, true)
		}
		side = p.sheet.Back
	}
	pending := len(p.sheet.Front.Pages)
	if p.sheet.Back != nil {
		pending += len(p.sheet.Back.Pages)
	}
	used := p.builder.placements
	if p.temporary {
		used = p.builder.templatePages
	}
	if pending >= p.builder.options.MaxPlacements-used {
		return fmt.Errorf("%w: pending print placements", ErrLimit)
	}
	placementLayout := layout
	if p.nup == 1 && isBack && printBackRotates(document.duplex, layout.Width, layout.Height) && page.backLayout != nil {
		placementLayout = *page.backLayout
	}
	placement := PrintPlacement{Page: page.index, DocumentIndex: page.document, Transform: placementLayout.Transform, PageClip: placementLayout.PageClip, MediaClip: placementLayout.MediaClip, Watermark: page.watermark, Negative: page.negative, Color: clonePrintColorPlan(page.colorPlan), Resolution: clonePrintResolution(page.resolution)}
	if p.nup > 1 {
		cell := printNUpCell(len(side.Pages), p.nup, side.MediaClip, p.direction)
		src := layout.MediaClip
		if src.Width <= 0 || src.Height <= 0 {
			src = Rect{Width: layout.Width, Height: layout.Height}
		}
		factor := min(cell.Width/src.Width, cell.Height/src.Height)
		rotated := min(cell.Width/src.Height, cell.Height/src.Width)
		var mapping Matrix
		if rotated > factor {
			factor = rotated
			mapping = Matrix{
				B: -factor,
				C: factor,
				E: cell.X + (cell.Width-factor*src.Height)/2 - factor*src.Y,
				F: cell.Y + (cell.Height+factor*src.Width)/2 + factor*src.X,
			}
		} else {
			mapping = Matrix{
				A: factor,
				D: factor,
				E: cell.X + (cell.Width-factor*src.Width)/2 - factor*src.X,
				F: cell.Y + (cell.Height-factor*src.Height)/2 - factor*src.Y,
			}
		}
		placement.Transform = mapping.Mul(layout.Transform)
		placement.MediaClip = printClampBox(printTransformBox(layout.MediaClip, mapping), cell)
		if factor <= 0 || !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(placement.MediaClip.X, placement.MediaClip.Y, placement.MediaClip.Width, placement.MediaClip.Height) {
			return fmt.Errorf("%w: print NUp mapping", ErrLimit)
		}
	}
	side.Resolution = printMergeSideResolution(side.Resolution, page.resolution)
	side.Pages = append(side.Pages, placement)
	return nil
}

// printClampBox 将矩形裁剪在目标容器边界内，消除浮点舍入造成的微小越界
// 入参: box 待约束矩形, bound 外界容器矩形
// 返回: Rect 完整位于bound内的矩形
func printClampBox(box, bound Rect) Rect {
	left := max(box.X, bound.X)
	top := max(box.Y, bound.Y)
	right := min(box.X+box.Width, bound.X+bound.Width)
	bottom := min(box.Y+box.Height, bound.Y+bound.Height)
	return Rect{X: left, Y: top, Width: max(0, right-left), Height: max(0, bottom-top)}
}

// printNUpCell 优先按近方形整除因子对及八向排列选择单元，纸面竖向较长时交换网格行列
// 入参: index 面内顺序, count 每面页数, area 可打印区域, direction 排列方向
// 返回: Rect 纸面坐标中的单元
func printNUpCell(index, count int, area Rect, direction string) Rect {
	columns := 0
	for rows := int(math.Sqrt(float64(count))); rows > 1 && count/rows <= rows*2; rows-- {
		if count%rows == 0 {
			columns = count / rows
			break
		}
	}
	var rows int
	if columns != 0 {
		rows = count / columns
	} else {
		columns = int(math.Ceil(math.Sqrt(float64(count))))
		rows = 1 + (count-1)/columns
	}
	if area.Height > area.Width {
		columns, rows = rows, columns
	}
	x, y := index%columns, index/columns
	switch direction {
	case "BottomRight", "BottomLeft", "TopRight", "TopLeft":
		x, y = index/rows, index%rows
	}
	switch direction {
	case "LeftBottom", "LeftTop", "BottomLeft", "TopLeft":
		x = columns - 1 - x
	}
	switch direction {
	case "RightTop", "LeftTop", "TopRight", "TopLeft":
		y = rows - 1 - y
	}
	width, height := area.Width/float64(columns), area.Height/float64(rows)
	return Rect{X: area.X + float64(x)*width, Y: area.Y + float64(y)*height, Width: width, Height: height}
}

// ContentBounds 计算纸面可打印区域扣除留白后所有已放置页面内容的联合外接矩形
// 纸面、留白或放置几何非法、无放置页或均落于有效区域之外时返回零值矩形；零值placement.MediaClip沿用纸面MediaClip
// 返回: Rect 物理纸面坐标中的有效内容框
func (s PrintSide) ContentBounds() Rect {
	if len(s.Pages) == 0 || !geometryFinite(s.Width, s.Height) || s.Width <= 0 || s.Height <= 0 || !printBoxWithin(s.MediaClip, Rect{Width: s.Width, Height: s.Height}) || s.MediaClip.Width <= 0 || s.MediaClip.Height <= 0 {
		return Rect{}
	}
	visible, ok := printSideVisibleRegions(s.MediaClip, s.Gutter)
	if !ok {
		return Rect{}
	}
	found := false
	var minX, minY, maxX, maxY float64
	for _, placement := range s.Pages {
		if !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(placement.PageClip.X, placement.PageClip.Y, placement.PageClip.Width, placement.PageClip.Height, placement.PageClip.X+placement.PageClip.Width, placement.PageClip.Y+placement.PageClip.Height) || placement.PageClip.Width < 0 || placement.PageClip.Height < 0 || !printBoxWithin(placement.MediaClip, Rect{Width: s.Width, Height: s.Height}) {
			return Rect{}
		}
		mapped := printTransformBox(placement.PageClip, placement.Transform)
		if !geometryFinite(mapped.X, mapped.Y, mapped.Width, mapped.Height, mapped.X+mapped.Width, mapped.Y+mapped.Height) {
			return Rect{}
		}
		if placement.PageClip.Width == 0 || placement.PageClip.Height == 0 || mapped.Width <= 0 || mapped.Height <= 0 {
			continue
		}
		left := max(mapped.X, s.MediaClip.X)
		top := max(mapped.Y, s.MediaClip.Y)
		right := min(mapped.X+mapped.Width, s.MediaClip.X+s.MediaClip.Width)
		bottom := min(mapped.Y+mapped.Height, s.MediaClip.Y+s.MediaClip.Height)
		if placement.MediaClip != (Rect{}) {
			left = max(left, placement.MediaClip.X)
			top = max(top, placement.MediaClip.Y)
			right = min(right, placement.MediaClip.X+placement.MediaClip.Width)
			bottom = min(bottom, placement.MediaClip.Y+placement.MediaClip.Height)
		}
		if right <= left || bottom <= top {
			continue
		}
		for _, region := range visible {
			rl := max(left, region.X)
			rt := max(top, region.Y)
			rr := min(right, region.X+region.Width)
			rb := min(bottom, region.Y+region.Height)
			if rr <= rl || rb <= rt {
				continue
			}
			if !found {
				minX, minY, maxX, maxY, found = rl, rt, rr, rb, true
			} else {
				minX, minY, maxX, maxY = min(minX, rl), min(minY, rt), max(maxX, rr), max(maxY, rb)
			}
		}
	}
	if !found {
		return Rect{}
	}
	return Rect{X: minX, Y: minY, Width: maxX - minX, Height: maxY - minY}
}

// RenderPrintSide 按正常阅读方向绘制单个拼版纸面，可通过PrintRenderOptions.Transform应用背面翻面变换
// 同次调用内重复源页仅解析一次，Gutter排除纸面内容并保留背景，失败时不返回部分图像
// 入参: ctx 取消Context，nil采用Background, side 纸面布局, options 打印及页面加载预算，nil采用默认值
// 返回: *image.NRGBA 独立纸面栅格, error 布局、序号、资源、绘制、预算或取消错误
func (r *Reader) RenderPrintSide(ctx context.Context, side *PrintSide, options *PrintRenderOptions) (*image.NRGBA, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.renderPrintSide(ctx, side, options, nil)
}

// renderPrintSide 共用纸面场景、签名、水印及预算，设备转换只替代最终输出编码
// 入参: ctx 取消Context, side 纸面布局, options 打印及加载参数, device 可选目标状态
// 返回: *image.NRGBA 预览，设备输出时为nil, error 布局、资源、绘制或取消错误
func (r *Reader) renderPrintSide(ctx context.Context, side *PrintSide, options *PrintRenderOptions, device *deviceRenderState) (*image.NRGBA, error) {
	if r.closed {
		return nil, ErrClosed
	}
	configuration := PrintRenderOptions{MaxPages: 4096, MaxPageBytes: 64 << 20, MaxResourceBytes: 64 << 20, MaxXMLNodes: r.limits.MaxXMLNodes}
	if options != nil {
		configuration = *options
		if configuration.MaxPages == 0 {
			configuration.MaxPages = 4096
		}
		if configuration.MaxPageBytes == 0 {
			configuration.MaxPageBytes = 64 << 20
		}
		if configuration.MaxResourceBytes == 0 {
			configuration.MaxResourceBytes = 64 << 20
		}
		if configuration.MaxXMLNodes == 0 {
			configuration.MaxXMLNodes = r.limits.MaxXMLNodes
		}
	}
	if side == nil || configuration.MaxPages < 1 || configuration.MaxPageBytes < 1 || configuration.MaxResourceBytes < 1 || configuration.MaxXMLNodes < 1 || configuration.Render.Transform != nil || !geometryFinite(side.Width, side.Height) || side.Width <= 0 || side.Height <= 0 {
		return nil, fmt.Errorf("%w: print side options or media", ErrInvalid)
	}
	if len(side.Pages) > configuration.MaxPages {
		return nil, fmt.Errorf("%w: print side placement count", ErrLimit)
	}
	colorExecution := configuration.Color != nil
	for _, placement := range side.Pages {
		colorExecution = colorExecution || placement.Color != nil
	}
	if colorExecution && device == nil {
		return nil, fmt.Errorf("%w: print color requires explicit device output", ErrUnsupported)
	}
	colorExecution = colorExecution || device != nil
	if !printBoxWithin(side.MediaClip, Rect{Width: side.Width, Height: side.Height}) {
		return nil, fmt.Errorf("%w: print side media clip", ErrInvalid)
	}
	if err := validatePrintColor(side.Color); err != nil {
		return nil, err
	}
	clip, err := printSideGutterClip(side.MediaClip, side.Gutter)
	if err != nil {
		return nil, err
	}
	if configuration.Render.Background == nil {
		configuration.Render.Background = color.White
	}
	settings, transform, err := configuration.Render.settings(ctx)
	if err != nil {
		return nil, err
	}
	if configuration.Transform != nil {
		if !geometryFillMatrixFinite(*configuration.Transform) {
			return nil, fmt.Errorf("%w: print side transform", ErrInvalid)
		}
		transform = transform.Mul(*configuration.Transform)
		if !geometryFillMatrixFinite(transform) {
			return nil, fmt.Errorf("%w: print side transform range", ErrLimit)
		}
	}
	if device != nil {
		if err := device.apply(&settings); err != nil {
			return nil, err
		}
	}
	settings.outputColor = side.Color.Mode
	if colorExecution {
		settings.printPlan = make(map[*Canvas]*PrintColorPlan)
		settings.printOptions = configuration.Color
		settings.printSide = true
	}
	if err := checkContext(settings.context); err != nil {
		return nil, err
	}
	if err := r.printSideSignatures(settings.context, side.SignaturePolicy, configuration.Signatures); err != nil {
		return nil, err
	}
	var bounds image.Rectangle
	if configuration.Render.Region != nil {
		bounds = *configuration.Render.Region
	} else {
		bounds, err = renderPageBounds(&Page{Width: side.Width, Height: side.Height}, transform, settings.samples)
		if err != nil {
			return nil, err
		}
	}
	if _, err := validateSceneOutput(bounds, transform, settings); err != nil {
		return nil, err
	}
	loader := printSideXMLLoader{
		reader: r, context: settings.context,
		pageBytes: configuration.MaxPageBytes, resourceBytes: configuration.MaxResourceBytes,
		totalBytes: r.limits.MaxPackageBytes, nodes: min(configuration.MaxXMLNodes, r.limits.MaxXMLNodes),
		dictionaries: make(map[string]*xmlElement),
	}
	remainingNodes := settings.elements - 1
	geometryBudget := &printSideGeometryBudget{context: settings.context, edges: settings.edges, work: settings.work, figures: make(map[*xmlElement]*Geometry)}
	cache := make(map[string]printSidePage)
	watermarks := newPrintWatermarkRenderer(r, configuration.Watermark, settings)
	elements := make([]Element, 0, len(side.Pages))
	for _, placement := range side.Pages {
		if err := checkContext(settings.context); err != nil {
			return nil, err
		}
		part, err := r.printPlacementPart(placement)
		if err != nil {
			return nil, err
		}
		if !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(placement.PageClip.X, placement.PageClip.Y, placement.PageClip.Width, placement.PageClip.Height, placement.PageClip.X+placement.PageClip.Width, placement.PageClip.Y+placement.PageClip.Height) || placement.PageClip.Width < 0 || placement.PageClip.Height < 0 || !printBoxWithin(placement.MediaClip, Rect{Width: side.Width, Height: side.Height}) {
			return nil, fmt.Errorf("%w: print placement", ErrInvalid)
		}
		mapped := printTransformBox(placement.PageClip, placement.Transform)
		if !geometryFinite(mapped.X, mapped.Y, mapped.Width, mapped.Height, mapped.X+mapped.Width, mapped.Y+mapped.Height) {
			return nil, fmt.Errorf("%w: print placement transform range", ErrInvalid)
		}
		key := strings.ToLower(part)
		loaded, exists := cache[key]
		if !exists {
			page, err := loader.scenePart(part, geometryBudget)
			if err != nil {
				return nil, err
			}
			nodes, err := countPrintElements(page.Elements, remainingNodes-2, 0, r.limits.MaxXMLDepth)
			if err != nil {
				return nil, err
			}
			loaded = printSidePage{part: page.Part, elements: page.Elements, nodes: nodes}
			cache[key] = loaded
		}
		decorated, err := watermarks.elements(loaded.part, loaded.elements, placement.Watermark)
		if err != nil {
			return nil, err
		}
		nodes := loaded.nodes
		if placement.Watermark != nil {
			nodes, err = countPrintElements(decorated, remainingNodes-2, 0, r.limits.MaxXMLDepth)
			if err != nil {
				return nil, err
			}
		}
		if nodes > remainingNodes-2 {
			return nil, fmt.Errorf("%w: print side elements", ErrLimit)
		}
		remainingNodes -= nodes + 2
		mapping := placement.Transform
		content := &Canvas{ElementProperties: ElementProperties{Part: loaded.part, Opacity: 1, Clip: renderBoxGeometry(placement.PageClip), RenderTransform: &mapping}, Elements: decorated}
		if colorExecution {
			settings.printPlan[content] = placement.Color
		}
		if placement.Negative {
			if settings.negative == nil {
				settings.negative = make(map[*Canvas]bool)
			}
			settings.negative[content] = true
		}
		var placementMediaClip *Geometry
		if placement.MediaClip != (Rect{}) {
			placementMediaClip = renderBoxGeometry(placement.MediaClip)
		}
		clipped := &Canvas{ElementProperties: ElementProperties{Part: loaded.part, Opacity: 1, Clip: placementMediaClip}, Elements: []Element{content}}
		elements = append(elements, clipped)
	}
	root := &Canvas{ElementProperties: ElementProperties{Opacity: 1, Clip: clip}, Elements: elements}
	if colorExecution {
		settings.printPlan[root] = nil
	}
	return r.renderLoadedElementsFonts([]Element{root}, transform, bounds, watermarks.remainingSettings(settings), watermarks.fonts)
}

// countPrintElements 在组合多个页面前约束场景节点数量，避免只在所有页面加载后才发现超限
// 入参: elements 只读源元素, remaining 剩余节点数, depth 当前深度, maximumDepth 深度上限
// 返回: int 节点数, error 节点或深度预算错误
func countPrintElements(elements []Element, remaining, depth, maximumDepth int) (int, error) {
	if remaining < 0 || depth > maximumDepth {
		return 0, fmt.Errorf("%w: print side scene capacity", ErrLimit)
	}
	count := 0
	for _, element := range elements {
		if count >= remaining {
			return 0, fmt.Errorf("%w: print side scene elements", ErrLimit)
		}
		count++
		if canvas, ok := element.(*Canvas); ok {
			children, err := countPrintElements(canvas.Elements, remaining-count, depth+1, maximumDepth)
			if err != nil {
				return 0, err
			}
			count += children
		}
	}
	return count, nil
}

// printSideGutterClip 从纸面裁剪区域排除留白，以最多四个内部不相交的矩形构造独立几何
// 入参: media 已校验的纸面物理裁剪区域, gutter 可选留白，须有限、尺寸非负且完整位于media内
// 返回: *Geometry 非nil裁剪，全覆盖时为空几何，零面积留白无效果, error 非法留白错误
func printSideGutterClip(media Rect, gutter *Rect) (*Geometry, error) {
	regions, ok := printSubtractGutter(media, gutter)
	if !ok {
		return nil, fmt.Errorf("%w: print side gutter", ErrInvalid)
	}
	if len(regions) == 1 && regions[0] == media {
		return renderBoxGeometry(media), nil
	}
	clip := &Geometry{FillRule: GeometryNonZero}
	for _, remaining := range regions {
		clip.Figures = append(clip.Figures, renderBoxGeometry(remaining).Figures...)
	}
	return clip, nil
}

// renderSignedLinearToSRGB 将带符号扩展色域线性分量按对称IEC 61966-2-1曲线编码为sRGB值
// 入参: value 有限线性分量，允许小于零或大于一
// 返回: float64 对应sRGB分量
func renderSignedLinearToSRGB(value float64) float64 {
	magnitude := math.Abs(value)
	if magnitude == 1 {
		return value
	}
	if magnitude <= 0.0031308 {
		return 12.92 * value
	}
	return math.Copysign(1.055*math.Pow(magnitude, 1.0/2.4)-0.055, value)
}

// renderNegativeColor 按指定合成空间执行负片反相，scRGB路径使用对称扩展sRGB曲线无截断反相并返回线性空间，sRGB路径保持预乘alpha与扩展范围
// 入参: value 当前工作空间预乘颜色, space 工作合成空间
// 返回: renderColor 反相颜色, error 非法输入或算术范围错误
func renderNegativeColor(value renderColor, space renderColorSpace) (renderColor, error) {
	if err := value.validate(); err != nil {
		return renderColor{}, err
	}
	var result renderColor
	if space == renderScRGB {
		if value.a == 0 {
			return renderColor{}, nil
		}
		invert := func(channel float64) float64 {
			return renderSignedSRGBToLinear(1-renderSignedLinearToSRGB(channel/value.a)) * value.a
		}
		result = renderColor{r: invert(value.r), g: invert(value.g), b: invert(value.b), a: value.a}
	} else {
		result = renderColor{r: value.a - value.r, g: value.a - value.g, b: value.a - value.b, a: value.a}
	}
	if !geometryFinite(result.r, result.g, result.b) {
		return renderColor{}, fmt.Errorf("%w: negative color arithmetic", ErrLimit)
	}
	return result, nil
}

// negative 在源页内部合成完成后反相其独立表面，不修改相邻页面、纸张背景或透明度掩模
// 入参: surface 单次绘制拥有的源页表面
// 返回: error 工作、取消或颜色错误
func (r *sceneRenderer) negative(surface *renderSurface) error {
	if err := r.charge(uint64(len(surface.pixels))); err != nil {
		return err
	}
	for index, value := range surface.pixels {
		converted, err := renderNegativeColor(value, r.options.space)
		if err != nil {
			return err
		}
		surface.pixels[index] = converted
	}
	return nil
}

// charge 在追加类型化数据前扣除容量，零增量也检查取消，nil预算保持普通页面行为
// 入参: figures 新子路径或资源项数量, segments 新语义段数量
// 返回: error 预算不足或取消错误
func (b *printSideGeometryBudget) charge(figures, segments int) error {
	if b == nil {
		return nil
	}
	if err := checkContext(b.context); err != nil {
		return err
	}
	if segments > b.edges || uint64(figures) > b.work || uint64(segments) > b.work-uint64(figures) {
		return fmt.Errorf("%w: print side geometry materialization", ErrLimit)
	}
	b.edges -= segments
	b.work -= uint64(figures) + uint64(segments)
	return nil
}

// shared 取得同一原始节点已解析的轮廓，不共享Geometry外壳或变换
// 入参: node 几何定义节点
// 返回: *Geometry 只读轮廓，普通页面或首次解析时为nil
func (b *printSideGeometryBudget) shared(node *xmlElement) *Geometry {
	if b == nil {
		return nil
	}
	return b.figures[node]
}

// remember 只缓存不可变轮廓，页面作用域中的Transform仍由各解析器独立绑定
// 入参: node 几何定义节点, value 已完整校验的几何
func (b *printSideGeometryBudget) remember(node *xmlElement, value *Geometry) {
	if b != nil && b.figures[node] == nil {
		b.figures[node] = &Geometry{FillRule: value.FillRule, Figures: value.Figures}
	}
}

// resource 在资源外壳及画刷停止点物化前计费，不扫描或展开其他资源定义
// 入参: node 即将解析的资源或绘制节点
// 返回: error 预算不足或取消错误
func (b *printSideGeometryBudget) resource(node *xmlElement) error {
	if err := b.charge(1, 0); err != nil {
		return err
	}
	if b == nil {
		return nil
	}
	for _, child := range node.Children {
		if child.Name.Local == "GradientStop" {
			if err := b.charge(1, 0); err != nil {
				return err
			}
		}
		if child.Name.Local == node.Name.Local+".GradientStops" {
			if err := b.charge(len(child.Children), 0); err != nil {
				return err
			}
		}
	}
	return nil
}

// watermark 读取标准None禁用选项或Text水印参数与叠放层级
// 返回: *PrintWatermark 独立描述，未声明或None时为nil, error 名称、描述、类型、范围或能力错误
func (s *printLayoutSettings) watermark() (*PrintWatermark, error) {
	option, feature, err := s.option(s.model.Elements, "PageWatermark")
	if err != nil || option == nil {
		return nil, err
	}
	if printPublicKeywordSpace(option.Name.Space) && option.Name.Local == "None" {
		for _, child := range feature.Children {
			if child.Kind == PrintSettingFeature {
				return nil, fmt.Errorf("%w: print watermark subfeature", ErrUnsupported)
			}
		}
		if err := printOptionProperties(option); err != nil {
			return nil, err
		}
		return nil, checkContext(s.options.context)
	}
	if !printPublicKeywordSpace(option.Name.Space) || option.Name.Local != "Text" {
		return nil, fmt.Errorf("%w: print watermark option", ErrUnsupported)
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature && (!printPublicKeywordSpace(child.Name.Space) || child.Name.Local != "Layering") {
			return nil, fmt.Errorf("%w: print watermark subfeature", ErrUnsupported)
		}
	}
	if err := printOptionProperties(option, "OriginWidth", "OriginHeight", "Transparency", "Angle", "FontColor", "FontSize", "Text"); err != nil {
		return nil, err
	}
	result := &PrintWatermark{Layer: PrintWatermarkOverlay}
	layer, layering, err := s.option(feature.Children, "Layering")
	if err != nil {
		return nil, err
	}
	if layer != nil {
		for _, child := range layering.Children {
			if child.Kind == PrintSettingFeature {
				return nil, fmt.Errorf("%w: nested watermark layering", ErrUnsupported)
			}
		}
		name, err := s.keyword(layer, "")
		if err != nil {
			return nil, err
		}
		switch name {
		case "Overlay":
			result.Layer = PrintWatermarkOverlay
		case "Underlay":
			result.Layer = PrintWatermarkUnderlay
		default:
			return nil, fmt.Errorf("%w: watermark layering option %s", ErrUnsupported, name)
		}
	}
	for _, field := range []struct {
		name     string
		value    *float64
		required bool
	}{
		{"OriginWidth", &result.Origin.X, false},
		{"OriginHeight", &result.Origin.Y, false},
		{"Angle", &result.Angle, false},
		{"FontSize", &result.FontSize, true},
	} {
		value, present, err := s.number(option, field.name)
		if err != nil {
			return nil, err
		}
		if !present {
			if field.required {
				return nil, fmt.Errorf("%w: watermark requires %s", ErrUnsupported, field.name)
			}
			continue
		}
		*field.value = value
	}
	result.Transparency, result.HasTransparency, err = s.number(option, "Transparency")
	if err != nil {
		return nil, err
	}
	if result.Angle < 0 || result.Angle > 359 || result.FontSize <= 0 || result.Transparency < 0 || result.Transparency > 100 {
		return nil, fmt.Errorf("%w: watermark numeric range", ErrInvalid)
	}
	text, err := s.watermarkString(option, "Text")
	if err != nil {
		return nil, err
	}
	if utf8.RuneCountInString(text) > printWatermarkTextLimit {
		return nil, fmt.Errorf("%w: watermark text length", ErrInvalid)
	}
	result.Text = text
	text, err = s.watermarkString(option, "FontColor")
	if err != nil {
		return nil, err
	}
	if len(text) != 9 || text[0] != '#' {
		return nil, fmt.Errorf("%w: watermark sRGB color", ErrInvalid)
	}
	value, err := hex.DecodeString(text[1:])
	if err != nil {
		return nil, fmt.Errorf("%w: watermark sRGB digits", ErrInvalid)
	}
	result.Color = color.NRGBA{R: value[1], G: value[2], B: value[3], A: value[0]}
	result.Origin.X *= printMicronUnit
	result.Origin.Y *= printMicronUnit
	result.FontSize *= 96.0 / 72
	if !geometryFinite(result.Origin.X, result.Origin.Y, result.FontSize) {
		return nil, fmt.Errorf("%w: watermark coordinate range", ErrLimit)
	}
	return result, checkContext(s.options.context)
}

// watermarkString 读取水印字符串值并保留正文空白
// 入参: option Text选项, name 描述名称
// 返回: string 显式字符串, error 缺少描述、未初始化或类型错误
func (s *printLayoutSettings) watermarkString(option *PrintSetting, name string) (string, error) {
	value, err := s.scored(option, name)
	if err != nil {
		return "", err
	}
	if value == nil {
		return "", fmt.Errorf("%w: watermark requires %s", ErrUnsupported, name)
	}
	if value.Type != (xml.Name{}) && value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
		return "", fmt.Errorf("%w: watermark string type %s", ErrInvalid, name)
	}
	return value.Text, nil
}

// Error 返回包含策略与签名证据摘要的打印拒绝信息
// 返回: string 错误说明
func (e *PrintSignatureError) Error() string {
	if e == nil || e.Report == nil {
		return ErrPrintSignature.Error()
	}
	for _, result := range e.Report.Signatures {
		if result.Err != nil {
			if result.Part.Name != "" {
				return fmt.Sprintf("%s (%s: %v)", ErrPrintSignature.Error(), result.Part.Name, result.Err)
			}
			return fmt.Sprintf("%s (%v)", ErrPrintSignature.Error(), result.Err)
		}
		if result.Verification != nil && result.Verification.Status != SignatureValid {
			if result.Part.Name != "" {
				return fmt.Sprintf("%s (%s: status=%s)", ErrPrintSignature.Error(), result.Part.Name, result.Verification.Status.String())
			}
			return fmt.Sprintf("%s (status=%s)", ErrPrintSignature.Error(), result.Verification.Status.String())
		}
	}
	if len(e.Report.Signatures) > 0 {
		return fmt.Sprintf("%s (%d signatures)", ErrPrintSignature.Error(), len(e.Report.Signatures))
	}
	return ErrPrintSignature.Error()
}

// Unwrap 返回打印策略错误类别，不混用密码学验证错误
// 返回: error 策略拒绝类别
func (e *PrintSignatureError) Unwrap() error {
	if e == nil {
		return nil
	}
	return ErrPrintSignature
}

// PrintSignatures 读取有效作业策略并检查整个包的数字签名，Policy非零时跳过未使用的作业票据
// 无法验证的签名作为未验证证据保留在报告中，取消、预算或读取故障直接返回错误
// 入参: ctx 取消Context，nil采用Background, defaults 基础设置，nil为空, options 验证选项，nil采用默认值
// 返回: *PrintSignatureReport 独立打印报告，操作失败为空, error 设置、资源、预算、关闭或取消错误
func (r *Reader) PrintSignatures(ctx context.Context, defaults *PrintSettings, options *PrintSignatureOptions) (*PrintSignatureReport, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if options != nil && options.Policy != PrintSignatureFromTicket {
		return r.readPrintSignatures(ctx, &PrintSettings{Version: 1}, options)
	}
	settings, err := r.printSignatureJobSettings(ctx, defaults)
	if err != nil {
		return nil, err
	}
	return r.readPrintSignatures(ctx, settings, options)
}

// printSignatureJobSettings 在已持读锁时合并消费者基础设置与实际作业票据
// 入参: ctx 已规范化取消Context, defaults 基础设置，nil为空
// 返回: *PrintSettings 有效作业设置, error 票据、资源、预算或取消错误
func (r *Reader) printSignatureJobSettings(ctx context.Context, defaults *PrintSettings) (*PrintSettings, error) {
	configuration := PrintSettingsOptions{Limits: r.limits}
	empty := &PrintSettings{Version: 1}
	if defaults == nil {
		defaults = empty
	}
	base, err := MergePrintSettings(ctx, empty, defaults, &configuration)
	if err != nil {
		return nil, err
	}
	ticket, err := r.printTicketReference(r.sequence)
	if err != nil {
		return nil, err
	}
	if ticket == nil {
		return base, nil
	}
	if err := r.readPrintTicketData(ticket, min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes), ctx); err != nil {
		return nil, err
	}
	configuration.Scope = PrintScopeJob
	delta, err := ticket.Settings(ctx, &configuration)
	if err != nil {
		return nil, &PartError{Part: ticket.Part, Err: err}
	}
	configuration.Scope = PrintScopeUnknown
	return MergePrintSettings(ctx, base, delta, &configuration)
}

// printSignaturePolicy 读取标准作业Feature，放行说明性Property并拒绝配置描述
// 入参: settings 已校验的有效设置, ctx 取消Context
// 返回: PrintSignaturePolicy 策略, error 结构、私有选项、能力或取消错误
func printSignaturePolicy(settings *PrintSettings, ctx context.Context) (PrintSignaturePolicy, error) {
	configuration := printSettingsConfig{context: ctx}
	option, err := newPrintLayoutSettings(settings, configuration).leafOption(settings.Elements, "JobDigitalSignatureProcessing")
	if err != nil {
		return PrintSignatureFromTicket, err
	}
	if option == nil {
		return PrintSignatureIgnore, checkContext(ctx)
	}
	if !printPublicKeywordSpace(option.Name.Space) {
		return PrintSignatureFromTicket, fmt.Errorf("%w: private digital signature processing option", ErrUnsupported)
	}
	if err := printOptionProperties(option); err != nil {
		return PrintSignatureFromTicket, err
	}
	switch option.Name.Local {
	case "PrintInvalidSignatures":
		return PrintSignatureIgnore, checkContext(ctx)
	case "PrintInvalidSignaturesWithErrorReport":
		return PrintSignatureReportError, checkContext(ctx)
	case "PrintOnlyValidSignatures":
		return PrintSignatureRequireValid, checkContext(ctx)
	default:
		return PrintSignatureFromTicket, fmt.Errorf("%w: digital signature processing option", ErrUnsupported)
	}
}

// readPrintSignatures 在已持读锁时检查整个作业，所有签名共用关联索引及累计读取预算
// 入参: ctx 非nil取消Context, settings 已合并作业设置, options 验证选项
// 返回: *PrintSignatureReport 完整报告，操作失败为空, error 参数、资源、预算或取消错误
func (r *Reader) readPrintSignatures(ctx context.Context, settings *PrintSettings, options *PrintSignatureOptions) (*PrintSignatureReport, error) {
	configuration := PrintSignatureOptions{}
	if options != nil {
		configuration = *options
	}
	if configuration.MaxSignatures == 0 {
		configuration.MaxSignatures = 1000
	}
	if configuration.MaxBytes == 0 {
		configuration.MaxBytes = r.limits.MaxPackageBytes
	}
	if configuration.MaxWork == 0 {
		configuration.MaxWork = 1 << 28
	}
	if configuration.MaxEvidence == 0 {
		configuration.MaxEvidence = 1 << 20
	}
	if configuration.Policy > PrintSignatureRequireValid || configuration.MaxSignatures < 1 || configuration.MaxBytes < 1 || configuration.MaxEvidence < 1 {
		return nil, fmt.Errorf("%w: print signature options", ErrInvalid)
	}
	if err := validateSignatureVerifyOptions(ctx, configuration.Verify, r.limits); err != nil {
		return nil, err
	}
	policy := configuration.Policy
	if policy == PrintSignatureFromTicket {
		var err error
		policy, err = printSignaturePolicy(settings, ctx)
		if err != nil {
			return nil, err
		}
	}
	report := &PrintSignatureReport{Policy: policy, Allowed: true}
	if policy == PrintSignatureIgnore {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		return report, nil
	}
	budget := printSignatureBudget{context: ctx, work: configuration.MaxWork, evidence: configuration.MaxEvidence}
	if err := budget.step(uint64(len(r.pkg.parts))); err != nil {
		return nil, err
	}
	graph := signaturePartGraph{context: ctx, remaining: configuration.MaxBytes, maximum: configuration.MaxSignatures, work: budget.step}
	pkg := *r.pkg
	pkg.beforeRead, graph.pkg = graph.readAllowance, &pkg
	parts, err := graph.read()
	if err != nil {
		if !printSignatureUnverifiable(err) {
			return nil, err
		}
		part := PartInfo{Name: "/"}
		var location *PartError
		if errors.As(err, &location) {
			part.Name = location.Part
		}
		report.Signatures = []PrintSignatureResult{{Part: part, Err: err}}
	} else {
		if len(parts) > budget.evidence {
			return nil, fmt.Errorf("%w: print signature evidence count", ErrLimit)
		}
		report.Signatures = make([]PrintSignatureResult, 0, len(parts))
		for _, part := range parts {
			if err := budget.step(uint64(len(r.pkg.parts)) + uint64(len(r.pages)) + uint64(len(r.documents))); err != nil {
				return nil, err
			}
			entry := PrintSignatureResult{Part: part.Part}
			info, data, err := r.loadSignaturePart(part.Part, &graph)
			if err == nil {
				if err := budget.step(uint64(len(info.Parts)) + uint64(len(info.References))); err != nil {
					return nil, err
				}
				entry.Verification, err = r.verifyLoadedDocumentSignature(info, data, &graph, configuration.Verify)
			}
			if err != nil {
				if !printSignatureUnverifiable(err) {
					return nil, err
				}
				entry.Err = err
			}
			count := printSignatureEvidence(entry)
			if count > budget.evidence {
				return nil, fmt.Errorf("%w: print signature evidence count", ErrLimit)
			}
			budget.evidence -= count
			report.Signatures = append(report.Signatures, entry)
		}
	}
	valid := true
	for _, entry := range report.Signatures {
		valid = valid && entry.Err == nil && entry.Verification != nil && entry.Verification.Status == SignatureValid
	}
	report.Checked = true
	report.Allowed = policy != PrintSignatureRequireValid || valid
	report.NeedsErrorSheet = policy == PrintSignatureReportError && !valid
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return report, nil
}

// step 在读取及验证工作开始前检查累计额度和取消状态
// 入参: work 本次工作单元
// 返回: error 额度或取消错误
func (b *printSignatureBudget) step(work uint64) error {
	if err := b.context.Err(); err != nil {
		return err
	}
	if work > b.work {
		return fmt.Errorf("%w: print signature work", ErrLimit)
	}
	b.work -= work
	return nil
}

// printSignatureUnverifiable 区分无法建立签名结论与必须终止的取消、资源额度及底层故障
// 入参: err 验证过程中返回的错误
// 返回: bool 是否应保留为无法验证的证据
func printSignatureUnverifiable(err error) bool {
	var failure *packageReadError
	if errors.As(err, &failure) {
		return false
	}
	if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) || errors.Is(err, ErrLimit) || errors.Is(err, ErrClosed) {
		return false
	}
	return errors.Is(err, ErrUnsupported) || errors.Is(err, ErrInvalid) || errors.Is(err, ErrNotFound) || errors.Is(err, fs.ErrNotExist)
}

// printSignatureEvidence 统计返回的签名及其覆盖和命名空间证据，不把未执行步骤计为有效结论
// 入参: entry 单份签名结果
// 返回: int 累计证据项数
func printSignatureEvidence(entry PrintSignatureResult) int {
	count := 1
	if value := entry.Verification; value != nil {
		count += len(value.UnknownNamespaces)
		if coverage := value.Coverage; coverage != nil {
			count += len(coverage.MissingParts) + len(coverage.MissingRelationships) + len(coverage.UnexpectedParts) + len(coverage.UnexpectedRelationships) + len(coverage.UngroupedSignatures)
		}
	}
	return count
}

// finish 在正文编排完成后按需在计划末尾追加独立错误报告纸
// 入参: plan 已完成正文编排的私有计划
// 返回: *PrintPlan 完整计划，失败为空, error 报告页、容量或取消错误
func (b *printPlanBuilder) finish(plan *PrintPlan) (*PrintPlan, error) {
	if b.signatures != nil && b.signatures.NeedsErrorSheet {
		if b.options.Signatures == nil || b.options.Signatures.ReportPage == "" {
			return nil, fmt.Errorf("%w: signature error report requires a FixedPage", ErrUnsupported)
		}
		part, err := opcPartName(b.options.Signatures.ReportPage)
		if err != nil {
			return nil, err
		}
		size, err := b.reader.pkg.partSize(strings.ToLower(part))
		if err != nil {
			return nil, err
		}
		if err := b.step(size); err != nil {
			return nil, err
		}
		if actual := b.reader.pkg.names[strings.ToLower(part)]; actual != "" {
			part = actual
		}
		root, err := b.reader.readFixedPartLoader(part, "fixedpage", "FixedPage", nil, b.settings.context)
		if err != nil {
			return nil, err
		}
		page, err := parsePageHeader(root, part, b.reader.format)
		if err != nil {
			return nil, err
		}
		layout, err := (&PrintSettings{Version: 1}).Layout(b.settings.context, page, b.options.Print.Media, &b.settings.PrintSettingsOptions)
		if err != nil {
			return nil, err
		}
		placement := PrintPlacement{Page: -1, DocumentIndex: -1, Part: part, Transform: layout.Transform, PageClip: layout.PageClip, MediaClip: layout.MediaClip}
		sheet := PrintSheet{Front: PrintSide{Width: layout.Width, Height: layout.Height, MediaClip: layout.MediaClip, Pages: []PrintPlacement{placement}}, Duplex: PrintSimplex}
		if err := b.appendSheet(plan, sheet, false); err != nil {
			return nil, err
		}
	}
	if err := checkContext(b.settings.context); err != nil {
		return nil, err
	}
	plan.Signatures = b.signatures
	plan.Diagnostics = append([]Diagnostic(nil), b.diagnostics...)
	return plan, nil
}

// printSideSignatures 在加载场景及分配图像前重新检查签名，不依赖调用方可改写的计划报告
// 入参: ctx 取消Context, minimum 纸面要求的最低策略, options 显式替代及验证预算
// 返回: error 策略拒绝、签名读取、参数或取消错误
func (r *Reader) printSideSignatures(ctx context.Context, minimum PrintSignaturePolicy, options *PrintSignatureOptions) error {
	if minimum > PrintSignatureRequireValid {
		return fmt.Errorf("%w: print side signature policy", ErrInvalid)
	}
	settings := &PrintSettings{Version: 1}
	configuration := PrintSignatureOptions{}
	if options != nil {
		configuration = *options
	}
	if configuration.Policy == PrintSignatureFromTicket {
		var err error
		settings, err = r.printSignatureJobSettings(ctx, nil)
		if err != nil {
			return err
		}
		policy, err := printSignaturePolicy(settings, ctx)
		if err != nil {
			return err
		}
		configuration.Policy = max(policy, minimum)
	}
	report, err := r.readPrintSignatures(ctx, settings, &configuration)
	if err != nil {
		return err
	}
	if !report.Allowed {
		return &PrintSignatureError{Report: report}
	}
	return nil
}

// printPlacementPart 区分主索引页面与辅助FixedPage，保留严格URI及页号边界
// 入参: placement 纸面放置
// 返回: string 规范化页面URI, error URI或索引错误
func (r *Reader) printPlacementPart(placement PrintPlacement) (string, error) {
	if placement.Part != "" {
		if placement.Page != -1 {
			return "", fmt.Errorf("%w: auxiliary print page index", ErrInvalid)
		}
		return opcPartName(placement.Part)
	}
	if placement.Page < 0 || placement.Page >= len(r.pages) {
		return "", fmt.Errorf("%w: print page index", ErrInvalid)
	}
	return opcPartName(r.pages[placement.Page].Part)
}

// printRotateBox180 将纸面坐标中的矩形绕纸张中心旋转180度并约束在物理纸面范围内
// 入参: box 原矩形, width, height 纸张物理宽高
// 返回: Rect 旋转180度后的矩形
func printRotateBox180(box Rect, width, height float64) Rect {
	return printClampBox(Rect{
		X:      width - (box.X + box.Width),
		Y:      height - (box.Y + box.Height),
		Width:  box.Width,
		Height: box.Height,
	}, Rect{Width: width, Height: height})
}

// Summary 提取打印票据的高层语义摘要，包括分辨率DPI、质量、介质微米尺寸、缩放、镜像、色彩、水印、份数、双面、拼版、海报、页序、页范围与装订
// 入参: ctx 取消Context，nil采用Background, opts 布局与解析选项，nil采用默认值
// 返回: *PrintTicketSummary 独立票据语义摘要, error 票据、选项、数值或取消错误
func (s *PrintSettings) Summary(ctx context.Context, opts *PrintLayoutOptions) (*PrintTicketSummary, error) {
	layoutOpts := DefaultPrintLayoutOptions()
	if opts != nil {
		layoutOpts = *opts
	}
	configuration, err := printSettingsOptions(ctx, &layoutOpts.Settings)
	if err != nil {
		return nil, err
	}
	if configuration.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print ticket summary", ErrInvalid)
	}
	media := layoutOpts.Media
	if err := validatePrintMedia(media); err != nil {
		return nil, err
	}
	var model *PrintSettings
	if layoutOpts.Defaults != nil && s != nil {
		model, err = MergePrintSettings(configuration.context, layoutOpts.Defaults, s, &configuration.PrintSettingsOptions)
	} else if s != nil {
		model, err = validatePrintSettingsModel(s, configuration, printDocumentTicket)
		if err == nil {
			err = validatePrintSettingsOutputBudget(model, configuration, printDocumentTicket)
		}
	} else if layoutOpts.Defaults != nil {
		model, err = validatePrintSettingsModel(layoutOpts.Defaults, configuration, printDocumentTicket)
		if err == nil {
			err = validatePrintSettingsOutputBudget(model, configuration, printDocumentTicket)
		}
	} else {
		model = &PrintSettings{Version: 1}
	}
	if err != nil {
		return nil, err
	}
	if layoutOpts.IgnoreUnsupportedFeatures {
		model = printStripPrivateExtensions(model)
	}
	control := newPrintLayoutSettings(model, configuration)
	summary := &PrintTicketSummary{Orientation: "Portrait", MirrorImage: "None", Copies: 1, JobCopies: 1, DocumentCopies: 1, PageCopies: 1, Collate: "Collated", NUp: 1, PresentationDirection: "RightBottom", PageOrder: "Standard", Poster: 1}
	summary.Resolution, err = control.resolution()
	if err != nil {
		return nil, err
	}
	if quality, err := control.strictSummaryChoice("PageOutputQuality", "Automatic", "Draft", "Fax", "High", "Normal", "Photographic", "Text"); err != nil {
		if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
			return nil, err
		}
	} else {
		summary.OutputQuality = quality
	}
	if intent, err := control.strictSummaryChoice("PagePhotoPrintingIntent", "None", "PhotoBest", "PhotoDraft", "PhotoStandard"); err != nil {
		if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
			return nil, err
		}
	} else {
		summary.PhotoPrintingIntent = intent
	}
	for _, binName := range []string{"PageInputBin", "DocumentInputBin", "JobInputBin"} {
		if val, err := control.summaryPublicKeyword(binName); err != nil {
			if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
				return nil, err
			}
		} else if val != "" {
			summary.InputBin = val
			break
		}
	}
	for _, binName := range []string{"PageOutputBin", "DocumentOutputBin", "JobOutputBin"} {
		if val, err := control.summaryPublicKeyword(binName); err != nil {
			if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
				return nil, err
			}
		} else if val != "" {
			summary.OutputBin = val
			break
		}
	}
	if mediaType, err := control.summaryPublicKeyword("PageMediaType"); err != nil {
		if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
			return nil, err
		}
	} else {
		summary.MediaType = mediaType
	}
	if placement, err := control.mediaSize(&media); err != nil {
		if placement.rollNoLength {
			summary.MediaSizeName = placement.mediaName
			summary.MediaWidthMicrons = placement.widthMicrons
		} else if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
			return nil, err
		}
	} else {
		summary.MediaSizeName = placement.mediaName
		if media.Width > 0 && media.Height > 0 {
			summary.MediaSize = &Point{X: media.Width, Y: media.Height}
			if placement.hasMicrons {
				summary.MediaWidthMicrons, summary.MediaHeightMicrons = placement.widthMicrons, placement.heightMicrons
			} else {
				summary.MediaWidthMicrons = placement.widthMicrons
				if summary.MediaWidthMicrons <= 0 {
					summary.MediaWidthMicrons = printUnitsToMicrons(media.Width)
				}
				summary.MediaHeightMicrons = printUnitsToMicrons(media.Height)
			}
		}
	}
	borderOption, _, err := control.option(model.Elements, "PageBorderless")
	if err != nil {
		return nil, err
	}
	if borderOption != nil {
		border, err := control.keyword(borderOption, "None")
		if err != nil {
			return nil, err
		}
		if border != "None" && border != "Borderless" {
			return nil, fmt.Errorf("%w: print border option %s", ErrUnsupported, border)
		}
		summary.Borderless = border == "Borderless"
	}
	if summary.Borderless && media.Width > 0 && media.Height > 0 {
		area := Rect{Width: media.Width, Height: media.Height}
		summary.ImageableArea = &area
	} else if media.ImageableArea != nil {
		area := *media.ImageableArea
		summary.ImageableArea = &area
	} else if media.Width > 0 && media.Height > 0 {
		area := Rect{Width: media.Width, Height: media.Height}
		summary.ImageableArea = &area
	}
	summary.Scaling, err = control.scalingSummary()
	if err != nil {
		return nil, err
	}
	summary.MirrorImage, err = control.choice("PageMirrorImage", "None", "None", "MirrorImageWidth", "MirrorImageHeight")
	if err != nil {
		return nil, err
	}
	if opt, _, err := control.option(model.Elements, "PageOrientation"); err != nil {
		return nil, err
	} else if opt != nil {
		orientation, err := control.keyword(opt, "Portrait")
		if err != nil {
			return nil, err
		}
		if _, err := printOrientation(orientation, PrintMedia{Width: 1, Height: 1, LandscapeReverse: media.LandscapeReverse}); err != nil {
			return nil, err
		}
		summary.Orientation = orientation
	}
	negative, outputColor, err := control.printColors()
	if err != nil {
		return nil, err
	}
	summary.Negative = negative
	if outputColor.Mode != PrintColorOriginal {
		colorCopy := outputColor
		summary.OutputColor = &colorCopy
	}
	if colorPlan, _, err := control.extractColorPlan(); err != nil {
		if !layoutOpts.IgnoreUnsupportedFeatures || !errors.Is(err, ErrUnsupported) {
			return nil, err
		}
	} else {
		summary.ColorPlan = clonePrintColorPlan(colorPlan)
	}
	summary.Watermark, err = control.watermark()
	if err != nil {
		return nil, err
	}
	maxInt := int(^uint(0) >> 1)
	jobCopies, err := control.count("JobCopiesAllDocuments", 1, maxInt)
	if err != nil {
		return nil, err
	}
	docCopies, err := control.count("DocumentCopiesAllPages", 1, maxInt)
	if err != nil {
		return nil, err
	}
	pageCopies, err := control.count("PageCopies", 1, maxInt)
	if err != nil {
		return nil, err
	}
	if jobCopies > maxInt/docCopies || jobCopies*docCopies > maxInt/pageCopies {
		return nil, fmt.Errorf("%w: print summary copy count", ErrLimit)
	}
	summary.JobCopies, summary.DocumentCopies, summary.PageCopies = jobCopies, docCopies, pageCopies
	summary.Copies = jobCopies * docCopies * pageCopies
	jobCollateOpt, _, err := control.option(model.Elements, "JobCollateAllDocuments")
	if err != nil {
		return nil, err
	}
	jobCollate, err := control.choice("JobCollateAllDocuments", "Collated", "Collated", "Uncollated")
	if err != nil {
		return nil, err
	}
	if jobCollateOpt != nil {
		summary.JobCollate = jobCollate
	}
	docCollateOpt, _, err := control.option(model.Elements, "DocumentCollate")
	if err != nil {
		return nil, err
	}
	if docCollateOpt != nil {
		summary.DocumentCollate, err = control.choice("DocumentCollate", "Collated", "Collated", "Uncollated")
		if err != nil {
			return nil, err
		}
		summary.Collate = summary.DocumentCollate
	} else {
		summary.Collate = jobCollate
	}
	summary.PageOrder, err = control.choice("JobPageOrder", "Standard", "Standard", "Reverse")
	if err != nil {
		return nil, err
	}
	summary.Poster, err = control.poster(maxInt)
	if err != nil {
		return nil, err
	}
	summary.Duplex, summary.ManualDuplex, err = control.effectiveDuplex()
	if err != nil {
		return nil, err
	}
	summary.NUp, summary.PresentationDirection, err = control.effectiveNUp(maxInt)
	if err != nil {
		return nil, err
	}
	if value := printParamValue(control.values, "DocumentPageRanges"); value != nil {
		if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
			return nil, fmt.Errorf("%w: document page ranges type", ErrInvalid)
		}
		if _, err := parsePrintPageRangeSpans(value.Text, configuration); err != nil {
			return nil, err
		}
		summary.PageRanges = value.Text
	}
	if err := control.checkBindingConflict(); err != nil {
		return nil, err
	}
	if finishing, declared, err := control.binding("DocumentBinding"); err != nil {
		return nil, err
	} else if declared {
		summary.Finishing = finishing
	} else if finishing, declared, err := control.binding("JobBindAllDocuments"); err != nil {
		return nil, err
	} else if declared {
		summary.Finishing = finishing
	}
	return summary, checkContext(configuration.context)
}

// summaryPublicKeyword 读取公共叶子Feature的公共关键字Option名称，拒绝匿名或私有选项
// 入参: name 公共Feature本地名称
// 返回: string 公共Option名称，未声明为空字符串, error 结构、匿名或私有选项错误
func (s *printLayoutSettings) summaryPublicKeyword(name string) (string, error) {
	option, err := s.leafOption(s.model.Elements, name)
	if err != nil || option == nil {
		return "", err
	}
	if option.Name == (xml.Name{}) {
		return "", fmt.Errorf("%w: anonymous print option for %s", ErrInvalid, name)
	}
	return s.keyword(option, "")
}

// strictSummaryChoice 严格校验公共叶子枚举Feature的命名空间、非匿名Option、禁止子Feature与合法枚举值
// 入参: name 公共Feature名称, allowed 允许的公共Option名称集合
// 返回: string 命中的枚举名，未声明时为空字符串, error 非法结构、匿名Option或未支持枚举错误
func (s *printLayoutSettings) strictSummaryChoice(name string, allowed ...string) (string, error) {
	option, err := s.leafOption(s.model.Elements, name)
	if err != nil || option == nil {
		return "", err
	}
	if option.Name == (xml.Name{}) {
		return "", fmt.Errorf("%w: anonymous print option for %s", ErrInvalid, name)
	}
	value, err := s.keyword(option, "")
	if err != nil {
		return "", err
	}
	for _, candidate := range allowed {
		if value == candidate {
			return value, nil
		}
	}
	return "", fmt.Errorf("%w: print summary option %s/%s", ErrUnsupported, name, value)
}

// scalingSummary 从PageScaling提取缩放类型、自定义缩放比、微米偏移与九点对齐方式摘要
// 返回: *PrintScalingSummary 缩放摘要，未声明PageScaling时为nil, error 结构、参数或枚举错误
func (s *printLayoutSettings) scalingSummary() (*PrintScalingSummary, error) {
	option, feature, err := s.option(s.model.Elements, "PageScaling")
	if err != nil || option == nil {
		return nil, err
	}
	if !printPublicKeywordSpace(option.Name.Space) {
		return nil, fmt.Errorf("%w: private print scaling option", ErrUnsupported)
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature && (!printPublicKeywordSpace(child.Name.Space) || child.Name.Local != "ScaleOffsetAlignment") {
			return nil, fmt.Errorf("%w: print scaling subfeature", ErrUnsupported)
		}
	}
	alignOpt, err := s.leafOption(feature.Children, "ScaleOffsetAlignment")
	if err != nil {
		return nil, err
	}
	alignName := ""
	if alignOpt != nil {
		alignName, err = s.keyword(alignOpt, "")
		if err != nil {
			return nil, err
		}
		if _, _, err := s.alignment(feature); err != nil {
			return nil, err
		}
	}
	name := option.Name.Local
	result := &PrintScalingSummary{Option: name, Alignment: alignName}
	switch name {
	case "None":
		if err := printOptionProperties(option); err != nil {
			return nil, err
		}
		result.ScaleX, result.ScaleY = 1, 1
	case "Custom", "CustomSquare":
		xName, yName := "ScaleWidth", "ScaleHeight"
		if name == "CustomSquare" {
			xName, yName = "Scale", "Scale"
		}
		x, _, hasX, err := s.numberExact(option, xName)
		if err != nil {
			return nil, err
		}
		y, _, hasY, err := s.numberExact(option, yName)
		if err != nil {
			return nil, err
		}
		_, ox, _, err := s.numberExact(option, "OffsetWidth")
		if err != nil {
			return nil, err
		}
		_, oy, _, err := s.numberExact(option, "OffsetHeight")
		if err != nil {
			return nil, err
		}
		if !hasX || !hasY || x < 0 || y < 0 {
			return nil, fmt.Errorf("%w: invalid custom print scaling", ErrInvalid)
		}
		if err := printOptionProperties(option, xName, yName, "OffsetWidth", "OffsetHeight"); err != nil {
			return nil, err
		}
		result.ScaleX, result.ScaleY = x/100, y/100
		result.OffsetWidthMicrons, result.OffsetHeightMicrons = ox, oy
	case "FitApplicationBleedSizeToPageImageableSize", "FitApplicationContentSizeToPageImageableSize", "FitApplicationMediaSizeToPageImageableSize", "FitApplicationMediaSizeToPageMediaSize":
		if err := printOptionProperties(option); err != nil {
			return nil, err
		}
	default:
		return nil, fmt.Errorf("%w: print scaling option %s", ErrUnsupported, name)
	}
	return result, nil
}

// resolution 从PageResolution提取水平、垂直输出分辨率DPI及可选QualitativeResolution质量关键字，支持跨公共关键字命名空间与参数引用
// 返回: *PrintResolution 输出分辨率，未提供数值与质量分辨率时为nil, error 数值、未初始化或范围错误
func (s *printLayoutSettings) resolution() (*PrintResolution, error) {
	option, _, err := s.option(s.model.Elements, "PageResolution")
	if err != nil || option == nil {
		return nil, err
	}
	rx, hasX, err := s.resolutionNumber(option, "ResolutionX")
	if err != nil {
		return nil, err
	}
	ry, hasY, err := s.resolutionNumber(option, "ResolutionY")
	if err != nil {
		return nil, err
	}
	qualitative := ""
	if qVal, err := s.scored(option, "QualitativeResolution"); err != nil {
		return nil, err
	} else if qVal != nil {
		if qVal.QName != (xml.Name{}) {
			if !printPublicKeywordSpace(qVal.QName.Space) {
				return nil, fmt.Errorf("%w: private print QualitativeResolution", ErrUnsupported)
			}
			qualitative = qVal.QName.Local
		} else if qVal.Type == (xml.Name{}) || qVal.Type == (xml.Name{Space: printValueNS, Local: "string"}) {
			qualitative = strings.TrimSpace(qVal.Text)
		} else {
			return nil, fmt.Errorf("%w: print QualitativeResolution type", ErrInvalid)
		}
	}
	if !hasX && !hasY && qualitative == "" {
		return nil, nil
	}
	if hasX || hasY {
		if !hasX {
			rx = ry
		}
		if !hasY {
			ry = rx
		}
	}
	return &PrintResolution{X: rx, Y: ry, Qualitative: qualitative}, nil
}

// resolutionNumber 读取PageResolution中的正数分辨率分量，支持xs:integer、xs:decimal及ParameterRef
// 入参: option 已选PageResolution选项, name 描述值本地名称
// 返回: float64 正有限DPI值, bool 是否声明, error 类型、正值、缺失参数或范围错误
func (s *printLayoutSettings) resolutionNumber(option *PrintSetting, name string) (float64, bool, error) {
	value, err := s.scored(option, name)
	if err != nil {
		return 0, true, err
	}
	if value == nil {
		return 0, false, nil
	}
	text := strings.Trim(value.Text, " \t\r\n")
	if value.Type == (xml.Name{Space: printValueNS, Local: "integer"}) {
		if !printInteger(text) {
			return 0, true, fmt.Errorf("%w: print resolution %s", ErrInvalid, name)
		}
	} else if value.Type == (xml.Name{Space: printValueNS, Local: "decimal"}) {
		if !printDecimal(text) {
			return 0, true, fmt.Errorf("%w: print resolution %s", ErrInvalid, name)
		}
	} else {
		return 0, true, fmt.Errorf("%w: print resolution type %s", ErrInvalid, name)
	}
	number, err := printParameterNumber(text, s.options)
	if err != nil {
		return 0, true, err
	}
	if number.Sign() <= 0 {
		return 0, true, fmt.Errorf("%w: print resolution must be positive %s", ErrInvalid, name)
	}
	result, _ := number.Float64()
	if !geometryFinite(result) || result <= 0 {
		return 0, true, fmt.Errorf("%w: print resolution range %s", ErrLimit, name)
	}
	return result, true, nil
}

// effectiveDuplex 合并并校验作业级与文档级双面打印的互斥语义
// 返回: PrintDuplex 有效双面模式, bool 是否手动双面, error 冲突或配置错误
func (s *printLayoutSettings) effectiveDuplex() (PrintDuplex, bool, error) {
	jobDuplex, jobManual, err := s.duplex("JobDuplexAllDocumentsContiguously")
	if err != nil {
		return PrintSimplex, false, err
	}
	docDuplex, docManual, err := s.duplex("DocumentDuplex")
	if err != nil {
		return PrintSimplex, false, err
	}
	docDuplexOpt, _, _ := s.option(s.model.Elements, "DocumentDuplex")
	if docDuplex != PrintSimplex {
		if jobDuplex != PrintSimplex {
			return PrintSimplex, false, fmt.Errorf("%w: simultaneous job and document duplex", ErrUnsupported)
		}
		return docDuplex, docManual, nil
	}
	if jobDuplex != PrintSimplex {
		if docDuplexOpt != nil {
			return PrintSimplex, false, fmt.Errorf("%w: document simplex conflicts with job duplex", ErrUnsupported)
		}
		return jobDuplex, jobManual, nil
	}
	return PrintSimplex, false, nil
}

// effectiveNUp 合并并校验作业级与文档级拼版页数及排列方向的互斥语义
// 入参: maximum 拼版页数上限
// 返回: int 有效每面拼版页数, string 排列方向名称, error 冲突或配置错误
func (s *printLayoutSettings) effectiveNUp(maximum int) (int, string, error) {
	jobNUp, jobDir, err := s.nup("JobNUpAllDocumentsContiguously", maximum)
	if err != nil {
		return 0, "", err
	}
	docNUp, docDir, err := s.nup("DocumentNUp", maximum)
	if err != nil {
		return 0, "", err
	}
	docNUpOpt, _, _ := s.option(s.model.Elements, "DocumentNUp")
	jobNUpOpt, _, _ := s.option(s.model.Elements, "JobNUpAllDocumentsContiguously")
	if docNUp > 1 {
		if jobNUp > 1 {
			return 0, "", fmt.Errorf("%w: simultaneous job and document NUp", ErrUnsupported)
		}
		return docNUp, docDir, nil
	}
	if jobNUp > 1 {
		if docNUpOpt != nil {
			return 0, "", fmt.Errorf("%w: document NUp conflicts with job NUp", ErrUnsupported)
		}
		return jobNUp, jobDir, nil
	}
	if docNUpOpt != nil {
		return 1, docDir, nil
	}
	if jobNUpOpt != nil {
		return 1, jobDir, nil
	}
	return 1, "RightBottom", nil
}

// clonePrintResolution 独立复制可选输出分辨率指针，避免计划返回结果共享可变状态
// 入参: src 源输出分辨率指针
// 返回: *PrintResolution 独立副本，输入为nil时返回nil
func clonePrintResolution(src *PrintResolution) *PrintResolution {
	if src == nil {
		return nil
	}
	copied := *src
	return &copied
}

// printMergeSideResolution 汇聚同一纸面多个放置页的有效输出分辨率，保留更高水平与垂直DPI
// 入参: current 纸面当前分辨率, next 新放置页分辨率
// 返回: *PrintResolution 汇聚后的独立分辨率指针
func printMergeSideResolution(current, next *PrintResolution) *PrintResolution {
	if next == nil {
		return current
	}
	if current == nil {
		return clonePrintResolution(next)
	}
	merged := *current
	if next.X*next.Y > merged.X*merged.Y {
		if next.Qualitative != "" {
			merged.Qualitative = next.Qualitative
		}
	} else if merged.Qualitative == "" && next.Qualitative != "" {
		merged.Qualitative = next.Qualitative
	}
	if next.X > merged.X {
		merged.X = next.X
	}
	if next.Y > merged.Y {
		merged.Y = next.Y
	}
	return &merged
}

// clonePrintPlacement 复制单个纸面放置及其可变颜色、水印与分辨率指针
// 入参: source 源放置项
// 返回: PrintPlacement 独立放置副本
func clonePrintPlacement(source PrintPlacement) PrintPlacement {
	source.Color = clonePrintColorPlan(source.Color)
	source.Resolution = clonePrintResolution(source.Resolution)
	if source.Watermark != nil {
		mark := *source.Watermark
		source.Watermark = &mark
	}
	return source
}

// printCloneRectPtr 独立复制可选矩形指针，避免返回模型共享可变状态
// 入参: src 源矩形指针
// 返回: *Rect 独立副本，输入为nil时返回nil
func printCloneRectPtr(src *Rect) *Rect {
	if src == nil {
		return nil
	}
	copied := *src
	return &copied
}

// printSubtractGutter 计算mediaClip扣除合法gutter后的最多四个非空互补矩形，零面积或全覆盖返回空切片与true，几何非法返回false
// 入参: mediaClip 纸面可打印区域, gutter 可选装订留白区域
// 返回: []Rect 互补可见子区域切片, bool 纸面与留白几何是否合法
func printSubtractGutter(mediaClip Rect, gutter *Rect) ([]Rect, bool) {
	if !geometryFinite(mediaClip.X, mediaClip.Y, mediaClip.Width, mediaClip.Height, mediaClip.X+mediaClip.Width, mediaClip.Y+mediaClip.Height) || mediaClip.Width < 0 || mediaClip.Height < 0 {
		return nil, false
	}
	if gutter != nil && !printBoxWithin(*gutter, mediaClip) {
		return nil, false
	}
	if mediaClip.Width == 0 || mediaClip.Height == 0 {
		return nil, true
	}
	if gutter == nil || gutter.Width == 0 || gutter.Height == 0 {
		return []Rect{mediaClip}, true
	}
	box := *gutter
	right, bottom := box.X+box.Width, box.Y+box.Height
	var visible []Rect
	for _, region := range [4]Rect{
		{X: mediaClip.X, Y: mediaClip.Y, Width: mediaClip.Width, Height: box.Y - mediaClip.Y},
		{X: mediaClip.X, Y: bottom, Width: mediaClip.Width, Height: mediaClip.Y + mediaClip.Height - bottom},
		{X: mediaClip.X, Y: box.Y, Width: box.X - mediaClip.X, Height: box.Height},
		{X: right, Y: box.Y, Width: mediaClip.X + mediaClip.Width - right, Height: box.Height},
	} {
		if region.Width > 0 && region.Height > 0 {
			visible = append(visible, region)
		}
	}
	return visible, true
}

// printSideVisibleRegions 计算纸面MediaClip扣除Gutter留白后的最多四个非空可见互补矩形
// 入参: mediaClip 纸面可打印区域, gutter 可选装订留白区域
// 返回: []Rect 可见子区域列表, bool 纸面与留白几何是否合法且存在可见区域
func printSideVisibleRegions(mediaClip Rect, gutter *Rect) ([]Rect, bool) {
	visible, ok := printSubtractGutter(mediaClip, gutter)
	return visible, ok && len(visible) > 0
}

// MapPage 查找指定零基源页面在打印计划全部纸张正反面中的所有放置映射，返回含所在纸面上下文的独立副本列表
// 入参: sourcePage 零基源页面序号
// 返回: []PrintPageMapping 按纸张与面顺序排列的放置映射切片
func (p *PrintPlan) MapPage(sourcePage int) []PrintPageMapping {
	if p == nil || sourcePage < 0 {
		return nil
	}
	var result []PrintPageMapping
	for sheetIndex, sheet := range p.Sheets {
		for placementIndex, placement := range sheet.Front.Pages {
			if placement.Part == "" && placement.Page == sourcePage {
				result = append(result, PrintPageMapping{
					SheetIndex:        sheetIndex,
					IsBack:            false,
					PlacementIndex:    placementIndex,
					Placement:         clonePrintPlacement(placement),
					SideWidth:         sheet.Front.Width,
					SideHeight:        sheet.Front.Height,
					SideMediaClip:     sheet.Front.MediaClip,
					Gutter:            printCloneRectPtr(sheet.Front.Gutter),
					BackFlipTransform: IdentityMatrix(),
				})
			}
		}
		if sheet.Back != nil {
			flip := sheet.BackFlipTransform()
			for placementIndex, placement := range sheet.Back.Pages {
				if placement.Part == "" && placement.Page == sourcePage {
					result = append(result, PrintPageMapping{
						SheetIndex:        sheetIndex,
						IsBack:            true,
						PlacementIndex:    placementIndex,
						Placement:         clonePrintPlacement(placement),
						SideWidth:         sheet.Back.Width,
						SideHeight:        sheet.Back.Height,
						SideMediaClip:     sheet.Back.MediaClip,
						Gutter:            printCloneRectPtr(sheet.Back.Gutter),
						BackFlipTransform: flip,
					})
				}
			}
		}
	}
	return result
}

// MapPoint 结合纸面MediaClip与装订留白Gutter将指定放置项中的源页面坐标点映射至纸面坐标并判定可见性
// 入参: point 源页面空间坐标点, placementIndex 纸面内放置索引
// 返回: Point 纸面空间坐标点, bool 映射后点在纸面有效可打印区域内是否可见
func (s *PrintSide) MapPoint(point Point, placementIndex int) (Point, bool) {
	if s == nil || placementIndex < 0 || placementIndex >= len(s.Pages) || !geometryFinite(s.Width, s.Height) || s.Width <= 0 || s.Height <= 0 || !printBoxWithin(s.MediaClip, Rect{Width: s.Width, Height: s.Height}) {
		return Point{}, false
	}
	visible, ok := printSideVisibleRegions(s.MediaClip, s.Gutter)
	if !ok {
		return Point{}, false
	}
	placement := s.Pages[placementIndex]
	if !printBoxWithin(placement.MediaClip, Rect{Width: s.Width, Height: s.Height}) {
		return Point{}, false
	}
	mapped, ok := placement.MapPoint(point)
	if !ok {
		return Point{}, false
	}
	for _, region := range visible {
		if mapped.X >= region.X && mapped.X <= region.X+region.Width && mapped.Y >= region.Y && mapped.Y <= region.Y+region.Height {
			return mapped, true
		}
	}
	return Point{}, false
}

// MapRect 结合纸面MediaClip与装订留白Gutter将指定放置项中的源页面矩形映射至纸面坐标并计算可见外接矩形
// 入参: rect 源页面空间矩形, placementIndex 纸面内放置索引
// 返回: Rect 扣除不可打印边距与装订留白后的纸面可见外接矩形, bool 裁切后是否非空可见
func (s *PrintSide) MapRect(rect Rect, placementIndex int) (Rect, bool) {
	if s == nil || placementIndex < 0 || placementIndex >= len(s.Pages) || !geometryFinite(s.Width, s.Height) || s.Width <= 0 || s.Height <= 0 || !printBoxWithin(s.MediaClip, Rect{Width: s.Width, Height: s.Height}) {
		return Rect{}, false
	}
	visible, ok := printSideVisibleRegions(s.MediaClip, s.Gutter)
	if !ok {
		return Rect{}, false
	}
	placement := s.Pages[placementIndex]
	if !printBoxWithin(placement.MediaClip, Rect{Width: s.Width, Height: s.Height}) {
		return Rect{}, false
	}
	mapped, ok := placement.MapRect(rect)
	if !ok {
		return Rect{}, false
	}
	mapped = printClampBox(mapped, s.MediaClip)
	if mapped.Width <= 0 || mapped.Height <= 0 {
		return Rect{}, false
	}
	found := false
	var minX, minY, maxX, maxY float64
	for _, region := range visible {
		part := printClampBox(mapped, region)
		if part.Width <= 0 || part.Height <= 0 {
			continue
		}
		if !found {
			minX, minY, maxX, maxY, found = part.X, part.Y, part.X+part.Width, part.Y+part.Height, true
		} else {
			minX, minY = min(minX, part.X), min(minY, part.Y)
			maxX, maxY = max(maxX, part.X+part.Width), max(maxY, part.Y+part.Height)
		}
	}
	if !found {
		return Rect{}, false
	}
	return Rect{X: minX, Y: minY, Width: maxX - minX, Height: maxY - minY}, true
}

// MapPoint 结合当前映射记录所在纸面的MediaClip与Gutter将源页面坐标点映射至纸面坐标并判定可见性
// 入参: point 源页面空间坐标点
// 返回: Point 纸面空间坐标点, bool 映射后点是否可见
func (m PrintPageMapping) MapPoint(point Point) (Point, bool) {
	side := PrintSide{Width: m.SideWidth, Height: m.SideHeight, MediaClip: m.SideMediaClip, Gutter: m.Gutter, Pages: []PrintPlacement{m.Placement}}
	return side.MapPoint(point, 0)
}

// MapRect 结合当前映射记录所在纸面的MediaClip与Gutter将源页面矩形映射至纸面坐标并计算可见外接矩形
// 入参: rect 源页面空间矩形
// 返回: Rect 纸面可见外接矩形, bool 裁切后是否非空可见
func (m PrintPageMapping) MapRect(rect Rect) (Rect, bool) {
	side := PrintSide{Width: m.SideWidth, Height: m.SideHeight, MediaClip: m.SideMediaClip, Gutter: m.Gutter, Pages: []PrintPlacement{m.Placement}}
	return side.MapRect(rect, 0)
}

// MapPoint 将源页面坐标点按PageClip裁切、经Transform映射至纸面坐标并按MediaClip判定可见性
// 入参: point 源页面空间坐标点
// 返回: Point 纸面空间坐标点, bool 映射后点是否可见
func (p PrintPlacement) MapPoint(point Point) (Point, bool) {
	if !geometryFinite(point.X, point.Y) || !geometryFillMatrixFinite(p.Transform) {
		return Point{}, false
	}
	if !geometryFinite(p.PageClip.X, p.PageClip.Y, p.PageClip.Width, p.PageClip.Height, p.PageClip.X+p.PageClip.Width, p.PageClip.Y+p.PageClip.Height) || p.PageClip.Width <= 0 || p.PageClip.Height <= 0 {
		return Point{}, false
	}
	if point.X < p.PageClip.X || point.X > p.PageClip.X+p.PageClip.Width || point.Y < p.PageClip.Y || point.Y > p.PageClip.Y+p.PageClip.Height {
		return Point{}, false
	}
	mapped := p.Transform.Transform(point)
	if !geometryFinite(mapped.X, mapped.Y) {
		return Point{}, false
	}
	if p.MediaClip != (Rect{}) {
		if !geometryFinite(p.MediaClip.X, p.MediaClip.Y, p.MediaClip.Width, p.MediaClip.Height, p.MediaClip.X+p.MediaClip.Width, p.MediaClip.Y+p.MediaClip.Height) || p.MediaClip.Width <= 0 || p.MediaClip.Height <= 0 {
			return Point{}, false
		}
		if mapped.X < p.MediaClip.X || mapped.X > p.MediaClip.X+p.MediaClip.Width || mapped.Y < p.MediaClip.Y || mapped.Y > p.MediaClip.Y+p.MediaClip.Height {
			return Point{}, false
		}
	}
	return mapped, true
}

// MapRect 将源页面矩形先按PageClip裁切、经Transform映射至纸面坐标再按MediaClip裁切并判断可见性
// 入参: rect 源页面空间矩形
// 返回: Rect 纸面空间可见外接矩形, bool 裁切后是否非空可见
func (p PrintPlacement) MapRect(rect Rect) (Rect, bool) {
	if !geometryFinite(rect.X, rect.Y, rect.Width, rect.Height, rect.X+rect.Width, rect.Y+rect.Height) || rect.Width <= 0 || rect.Height <= 0 {
		return Rect{}, false
	}
	if !geometryFillMatrixFinite(p.Transform) {
		return Rect{}, false
	}
	if !geometryFinite(p.PageClip.X, p.PageClip.Y, p.PageClip.Width, p.PageClip.Height, p.PageClip.X+p.PageClip.Width, p.PageClip.Y+p.PageClip.Height) || p.PageClip.Width <= 0 || p.PageClip.Height <= 0 {
		return Rect{}, false
	}
	clipped := printClampBox(rect, p.PageClip)
	if clipped.Width <= 0 || clipped.Height <= 0 {
		return Rect{}, false
	}
	mapped := printTransformBox(clipped, p.Transform)
	if !geometryFinite(mapped.X, mapped.Y, mapped.Width, mapped.Height, mapped.X+mapped.Width, mapped.Y+mapped.Height) || mapped.Width <= 0 || mapped.Height <= 0 {
		return Rect{}, false
	}
	if p.MediaClip != (Rect{}) {
		if !geometryFinite(p.MediaClip.X, p.MediaClip.Y, p.MediaClip.Width, p.MediaClip.Height, p.MediaClip.X+p.MediaClip.Width, p.MediaClip.Y+p.MediaClip.Height) || p.MediaClip.Width <= 0 || p.MediaClip.Height <= 0 {
			return Rect{}, false
		}
		mapped = printClampBox(mapped, p.MediaClip)
		if mapped.Width <= 0 || mapped.Height <= 0 {
			return Rect{}, false
		}
	}
	return mapped, true
}

// String 返回流式拼版执行模式名称
// 返回: string 模式名称
func (m PrintStreamMode) String() string {
	switch m {
	case PrintStreamPassthrough:
		return "Passthrough"
	case PrintStreamWindowed:
		return "Windowed"
	case PrintStreamRandomAccess:
		return "RandomAccess"
	default:
		return fmt.Sprintf("PrintStreamMode(%d)", m)
	}
}

// AnalyzePrintStreamCapability 分析给定打印票据的流式拼版可行性，判定纯前向直通、滑动窗口或整作业随机访问模式并给出建议窗口页数与原因
// 入参: ctx 取消Context，nil采用Background, settings 有效打印票据，nil按默认设置分析, opts 校验与资源预算选项，Scope须为Unknown
// 返回: PrintStreamCapability 流式可行性分析结果, error 票据、冲突、预算或取消错误
func AnalyzePrintStreamCapability(ctx context.Context, settings *PrintSettings, opts *PrintSettingsOptions) (PrintStreamCapability, error) {
	configuration, err := printSettingsOptions(ctx, opts)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	if configuration.Scope != PrintScopeUnknown {
		return PrintStreamCapability{}, fmt.Errorf("%w: scope on print stream capability analysis", ErrInvalid)
	}
	if settings == nil {
		settings = &PrintSettings{Version: 1}
	}
	model, err := validatePrintSettingsModel(settings, configuration, printDocumentTicket)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	control := newPrintLayoutSettings(model, configuration)
	if err := control.checkBindingConflict(); err != nil {
		return PrintStreamCapability{}, err
	}
	maxInt := int(^uint(0) >> 1)
	jobCopies, err := control.count("JobCopiesAllDocuments", 1, maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	docCopies, err := control.count("DocumentCopiesAllPages", 1, maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	pageCopies, err := control.count("PageCopies", 1, maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	if jobCopies > maxInt/docCopies || jobCopies*docCopies > maxInt/pageCopies {
		return PrintStreamCapability{}, fmt.Errorf("%w: print stream capability copy count", ErrLimit)
	}
	jobCollate, err := control.choice("JobCollateAllDocuments", "Collated", "Collated", "Uncollated")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	docCollate, err := control.choice("DocumentCollate", "Collated", "Collated", "Uncollated")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	pageOrder, err := control.choice("JobPageOrder", "Standard", "Standard", "Reverse")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	jobDuplex, _, err := control.duplex("JobDuplexAllDocumentsContiguously")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	duplex, _, err := control.effectiveDuplex()
	if err != nil {
		return PrintStreamCapability{}, err
	}
	jobNUp, _, err := control.nup("JobNUpAllDocumentsContiguously", maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	nup, _, err := control.effectiveNUp(maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	poster, err := control.poster(maxInt)
	if err != nil {
		return PrintStreamCapability{}, err
	}
	jobFin, _, err := control.binding("JobBindAllDocuments")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	docFin, _, err := control.binding("DocumentBinding")
	if err != nil {
		return PrintStreamCapability{}, err
	}
	booklet := jobFin.Binding == PrintBindingBooklet || docFin.Binding == PrintBindingBooklet
	if booklet && nup > 1 {
		return PrintStreamCapability{}, fmt.Errorf("%w: booklet binding conflicts with NUp", ErrUnsupported)
	}
	if poster > 1 && (booklet || nup > 1) {
		return PrintStreamCapability{}, fmt.Errorf("%w: poster conflicts with booklet or NUp", ErrUnsupported)
	}
	continuous := jobNUp > 1 || jobDuplex != PrintSimplex
	if jobFin.Binding != PrintBindingBooklet && continuous && docCollate == "Uncollated" && (docCopies > 1 || jobCollate == "Uncollated" && jobCopies > 1) {
		return PrintStreamCapability{}, fmt.Errorf("%w: uncollated copies conflict with job-contiguous sheet packing", ErrUnsupported)
	}
	result := PrintStreamCapability{
		Mode:               PrintStreamPassthrough,
		WindowPages:        1,
		Duplex:             duplex,
		NUp:                nup,
		Poster:             poster,
		Copies:             jobCopies * docCopies * pageCopies,
		ReverseOrder:       pageOrder == "Reverse",
		Booklet:            booklet,
		MonotonicPageRange: true,
	}
	if value := printParamValue(control.values, "DocumentPageRanges"); value != nil {
		if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
			return PrintStreamCapability{}, fmt.Errorf("%w: document page ranges type", ErrInvalid)
		}
		monotonic, err := printPageRangesMonotonic(value.Text, configuration)
		if err != nil {
			return PrintStreamCapability{}, err
		}
		result.HasPageRanges = value.Text != ""
		result.PageRanges = value.Text
		result.MonotonicPageRange = monotonic
	}
	randomAccess := false
	if result.ReverseOrder {
		randomAccess = true
		result.Reasons = append(result.Reasons, "reverse job page order requires full-job buffering")
	}
	if result.Booklet {
		randomAccess = true
		result.Reasons = append(result.Reasons, "booklet binding requires full-signature random access")
	}
	if jobCopies > 1 && jobCollate == "Collated" {
		result.CollatedMultiCopy = true
		randomAccess = true
		result.Reasons = append(result.Reasons, "collated job copies require full-job replay")
	}
	if (docCopies > 1 || jobCopies > 1 && jobCollate == "Uncollated") && docCollate == "Collated" {
		result.CollatedMultiCopy = true
		randomAccess = true
		result.Reasons = append(result.Reasons, "collated document copies require full-document replay")
	}
	if result.HasPageRanges && !result.MonotonicPageRange {
		randomAccess = true
		result.Reasons = append(result.Reasons, "non-monotonic page ranges require random access")
	}
	if randomAccess {
		result.Mode = PrintStreamRandomAccess
		result.WindowPages = 0
		return result, checkContext(configuration.context)
	}
	sides := 1
	if duplex != PrintSimplex {
		sides = 2
	}
	if nup > maxInt/sides {
		return PrintStreamCapability{}, fmt.Errorf("%w: print stream window size", ErrLimit)
	}
	window := nup * sides
	if window > 1 {
		result.Mode = PrintStreamWindowed
		result.WindowPages = window
		if nup > 1 {
			result.Reasons = append(result.Reasons, "N-up imposition requires multi-page sliding window")
		}
		if duplex != PrintSimplex {
			result.Reasons = append(result.Reasons, "duplex printing requires front-and-back sheet window")
		}
	}
	return result, checkContext(configuration.context)
}

// printPageRangesMonotonic 校验DocumentPageRanges词法并判断其展开页序是否单调非递减（可纯前向流式过滤）
// 入参: text 页范围字符串, options 数值预算及取消配置
// 返回: bool 是否单调非递减, error 词法、数值预算或取消错误
func printPageRangesMonotonic(text string, options printSettingsConfig) (bool, error) {
	spans, err := parsePrintPageRangeSpans(text, options)
	if err != nil {
		return false, err
	}
	var prevEnd *big.Int
	for _, span := range spans {
		if span.start.Cmp(span.end) > 0 {
			return false, nil
		}
		if prevEnd != nil && span.start.Cmp(prevEnd) < 0 {
			return false, nil
		}
		prevEnd = span.end
	}
	return true, nil
}
