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
	"encoding/xml"
	"fmt"
	"image"
	"image/color"
	"math"
	"slices"
	"strings"
	"unicode/utf8"
)

// printResourceProfile 等常量表示打印流程额外依赖的资源类别
const (
	printResourceProfile printResourceKind = iota + 1
	printResourceContent
)

// printResourceRules 保存Print Schema定义的资源参数与选项路径规则
var printResourceRules = [...]struct {
	parameter string
	feature   string
	options   []string
	property  string
	kind      printResourceKind
}{
	{"PageDeviceColorSpaceProfileURI", "", nil, "", printResourceProfile},
	{"PageBlendColorSpaceICCProfileURI", "PageBlendColorSpace", []string{"ICCProfile"}, "URI", printResourceProfile},
	{"PageDestinationColorProfileURI", "PageDestinationColorProfile", []string{"Application"}, "DestinationColorProfileURI", printResourceProfile},
	{"PageSourceColorProfileURI", "PageSourceColorProfile", []string{"RGB", "CMYK"}, "SourceColorProfileURI", printResourceProfile},
	{"JobPrimaryBannerSheetSource", "JobPrimaryBannerSheet", []string{"Custom"}, "BannerSheetSource", printResourceContent},
	{"DocumentBannerSheetSource", "DocumentBannerSheet", []string{"Custom"}, "BannerSheetSource", printResourceContent},
	{"JobErrorSheetSource", "JobErrorSheet", []string{"Custom"}, "ErrorSheetSource", printResourceContent},
	{"JobPrimaryCoverFrontSource", "JobPrimaryCoverFront", []string{"PrintFront", "PrintBack", "PrintBoth"}, "CoverFrontSource", printResourceContent},
	{"JobPrimaryCoverBackSource", "JobPrimaryCoverBack", []string{"PrintFront", "PrintBack", "PrintBoth"}, "CoverBackSource", printResourceContent},
	{"DocumentCoverFrontSource", "DocumentCoverFront", []string{"PrintFront", "PrintBack", "PrintBoth"}, "CoverFrontSource", printResourceContent},
	{"DocumentCoverBackSource", "DocumentCoverBack", []string{"PrintFront", "PrintBack", "PrintBoth"}, "CoverBackSource", printResourceContent},
}

// PrintRenderOptions 设置单页或拼版纸面的打印绘制、水印、签名、色彩与加载预算，默认白色背景且Render.Transform须为nil
// Print用于单页打印入口；Transform在DPI缩放前应用于介质输出，MaxPages、MaxPageBytes、MaxResourceBytes与MaxXMLNodes用于拼版纸面入口
// MaxPages默认4096，MaxPageBytes与MaxResourceBytes默认64MiB，MaxXMLNodes零值采用阅读器上限
type PrintRenderOptions struct {
	Print            PrintLayoutOptions
	Render           RenderOptions
	Transform        *Matrix
	Watermark        *PrintWatermarkOptions
	Signatures       *PrintSignatureOptions
	Color            *PrintColorOptions
	MaxPages         int
	MaxPageBytes     int64
	MaxResourceBytes int64
	MaxXMLNodes      int
}

// printSideXMLLoader 保存单次纸面绘制的XML预算及只读字典树，不与其他调用共享可变状态
type printSideXMLLoader struct {
	reader        *Reader
	context       context.Context
	pageBytes     int64
	resourceBytes int64
	totalBytes    int64
	nodes         int
	dictionaries  map[string]*xmlElement
}

// printWatermarkRenderer 保存源页水印的字体缓存与累计几何物化预算
type printWatermarkRenderer struct {
	fonts     *fontCache
	options   *PrintWatermarkOptions
	context   context.Context
	glyphs    int
	edges     int
	resources int
	work      uint64
}

// printResourceKind 区分独立ICC配置文件和由打印消费者解释的辅助内容
type printResourceKind uint8

// printResourceDocument 指定Microsoft票据或能力模型及其关联层级，part仅用于错误定位
type printResourceDocument struct {
	model        *PrintSettings
	capabilities bool
	scope        PrintScope
	part         string
}

// printResourceReference 保存原模型Value路径、规范化包根URI及资源用途
type printResourceReference struct {
	path []int
	uri  string
	kind printResourceKind
}

// printResourceCollector 累计约束完整输入树、参数索引及输出引用，不访问包、文件或网络
type printResourceCollector struct {
	document   printResourceDocument
	options    printSettingsConfig
	nodes      int
	bytes      int64
	namespaces map[string]bool
	parameters map[xml.Name][]int
	references []printResourceReference
}

// DefaultPrintRenderOptions 返回白色背景及默认打印设置、绘制与拼版加载预算的打印绘制配置
// 返回: PrintRenderOptions 打印绘制参数
func DefaultPrintRenderOptions() PrintRenderOptions {
	render := DefaultRenderOptions()
	render.Background = color.White
	limits := DefaultLimits()
	return PrintRenderOptions{
		Print:            PrintLayoutOptions{Settings: DefaultPrintSettingsOptions()},
		Render:           render,
		MaxPages:         4096,
		MaxPageBytes:     64 << 20,
		MaxResourceBytes: 64 << 20,
		MaxXMLNodes:      limits.MaxXMLNodes,
	}
}

// RenderPrint 按有效票据映射页面到物理介质，并同时应用页面边界和可打印区域裁剪
// 不执行设备约束求解、作业编排、设备色彩管理或通道打包；相关Feature须由上层处理后移除
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页号, options 打印及绘制参数，nil采用默认值
// 返回: *image.NRGBA 独立打印栅格，错误为nil, error 设置、页面、资源、绘制或取消错误
func (r *Reader) RenderPrint(ctx context.Context, pageIndex int, options *PrintRenderOptions) (*image.NRGBA, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.renderPrint(ctx, pageIndex, options, nil)
}

// renderPrint 在调用方持有读锁时共用打印场景，设备输出不改写预览契约
// 入参: ctx 取消Context, pageIndex 从零开始的全局页号, options 打印参数, device 可选目标状态
// 返回: *image.NRGBA 预览，设备输出时为nil, error 设置、资源、绘制或取消错误
func (r *Reader) renderPrint(ctx context.Context, pageIndex int, options *PrintRenderOptions, device *deviceRenderState) (*image.NRGBA, error) {
	if r.closed {
		return nil, ErrClosed
	}
	configuration := PrintRenderOptions{}
	if options != nil {
		configuration = *options
	}
	if configuration.Render.Transform != nil {
		return nil, fmt.Errorf("%w: transform on print rendering", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
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
			return nil, fmt.Errorf("%w: print transform", ErrInvalid)
		}
		transform = transform.Mul(*configuration.Transform)
		if !geometryFillMatrixFinite(transform) {
			return nil, fmt.Errorf("%w: print transform range", ErrLimit)
		}
	}
	if device != nil {
		if err := device.apply(&settings); err != nil {
			return nil, err
		}
	}
	page, ticket, layout, err := r.readPrintPageHeader(ctx, pageIndex, configuration.Print)
	if err != nil {
		return nil, err
	}
	signatures, err := r.readPrintSignatures(settings.context, ticket, configuration.Signatures)
	if err != nil {
		return nil, err
	}
	if !signatures.Allowed {
		return nil, &PrintSignatureError{Report: signatures}
	}
	if signatures.NeedsErrorSheet {
		return nil, fmt.Errorf("%w: signature error sheet requires a print job plan", ErrUnsupported)
	}
	printConfig := printSettingsConfig{PrintSettingsOptions: configuration.Print.Settings, context: ctx}
	ticket = printSignatureLayoutSettings(ticket)
	ticket, err = printSinglePosterSettings(ticket, printConfig)
	if err != nil {
		return nil, err
	}
	ticket, mark, err := printWatermarkSettings(ticket, printConfig)
	if err != nil {
		return nil, err
	}
	ticket, negative, outputColor, err := printColorSettings(ticket, printConfig)
	if err != nil {
		return nil, err
	}
	settings.outputColor = outputColor.Mode
	ticket, colorPlan, err := printColorPlanSettings(ctx, ticket, &configuration.Print.Settings)
	if err != nil {
		return nil, err
	}
	if device == nil && (colorPlan != nil || configuration.Color != nil) {
		return nil, fmt.Errorf("%w: print color requires explicit device output", ErrUnsupported)
	}
	if err := validatePrintLayoutFeatures(ticket, configuration.Print.IgnoreUnsupportedFeatures); err != nil {
		return nil, err
	}
	var bounds image.Rectangle
	if configuration.Render.Region != nil {
		bounds = *configuration.Render.Region
	} else {
		bounds, err = renderPageBounds(&Page{Width: layout.Width, Height: layout.Height}, transform, settings.samples)
		if err != nil {
			return nil, err
		}
	}
	if _, err := validateSceneOutput(bounds, transform, settings); err != nil {
		return nil, err
	}
	page, err = r.readPageSceneContent(page, false, nil, settings.context)
	if err != nil {
		return nil, err
	}
	watermarks := newPrintWatermarkRenderer(r, configuration.Watermark, settings)
	elements, err := watermarks.elements(page.Part, page.Elements, mark)
	if err != nil {
		return nil, err
	}
	content := &Canvas{ElementProperties: ElementProperties{Part: page.Part, Opacity: 1, Clip: renderBoxGeometry(layout.PageClip), RenderTransform: &layout.Transform}, Elements: elements}
	if device != nil {
		settings.printPlan = map[*Canvas]*PrintColorPlan{content: colorPlan}
		settings.printOptions = configuration.Color
	}
	if negative {
		settings.negative = map[*Canvas]bool{content: true}
	}
	media := &Canvas{ElementProperties: ElementProperties{Part: page.Part, Opacity: 1, Clip: renderBoxGeometry(layout.MediaClip)}, Elements: []Element{content}}
	return r.renderLoadedElementsFonts([]Element{media}, transform, bounds, watermarks.remainingSettings(settings), watermarks.fonts)
}

// RenderPrintDevice 按打印布局将单页编码至目标ICC设备图像，未支持的票据Feature返回ErrUnsupported
// 原生分量透传须在Color中声明设备条件，显式意图与票据冲突时须设置Color.Override，默认白色背景
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页号, device 必需目标配置, options 打印及绘制参数
// 返回: *DeviceImage 独立设备图像，失败为nil, error 设置、资源、转换或取消错误
func (r *Reader) RenderPrintDevice(ctx context.Context, pageIndex int, device *DeviceColorTarget, options *PrintRenderOptions) (*DeviceImage, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	var configuration PrintRenderOptions
	if options != nil {
		configuration = *options
	}
	configuration.Render = deviceRenderConfiguration(&configuration.Render)
	state, err := newDeviceRenderStateMode(ctx, device, configuration.Render, true)
	if err != nil {
		return nil, err
	}
	_, err = r.renderPrint(ctx, pageIndex, &configuration, state)
	return state.output(err)
}

// RenderPrintSideDevice 将完整拼版纸面的高精度合成结果编码至指定目标ICC，共享全部源页资源预算
// 各放置保留独立源页颜色政策，目标冲突须显式设置覆盖，默认白色背景
// 入参: ctx 取消Context，nil采用Background, side 纸面布局, device 必需目标配置, options 打印及页面加载预算
// 返回: *DeviceImage 独立纸面设备图像，失败为nil, error 布局、资源、转换或取消错误
func (r *Reader) RenderPrintSideDevice(ctx context.Context, side *PrintSide, device *DeviceColorTarget, options *PrintRenderOptions) (*DeviceImage, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	var configuration PrintRenderOptions
	if options != nil {
		configuration = *options
	}
	configuration.Render = deviceRenderConfiguration(&configuration.Render)
	state, err := newDeviceRenderStateMode(ctx, device, configuration.Render, true)
	if err != nil {
		return nil, err
	}
	_, err = r.renderPrintSide(ctx, side, &configuration, state)
	return state.output(err)
}

// scenePart 按严格包内URI加载普通页或辅助页，沿用相同的类型、资源及累计预算校验
// 入参: part 页面部件URI, budget 本次纸面共用的几何及资源容量
// 返回: *Page 独立页面, error URI、读取、绑定、必需资源、预算或取消错误
func (l *printSideXMLLoader) scenePart(part string, budget *printSideGeometryBudget) (*Page, error) {
	r := l.reader
	part, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	root, err := r.readFixedPartLoader(part, "fixedpage", "FixedPage", func(name string) (*xmlElement, error) {
		return l.read(name, false)
	}, l.context)
	if err != nil {
		return nil, err
	}
	page, err := parsePageHeader(root, part, r.format)
	if err != nil {
		return nil, err
	}
	page.resources, err = parseResourceGraphContext(part, root, r.format, r.limits, l.dictionary, l.context)
	if err != nil {
		return nil, err
	}
	if err := checkContext(l.context); err != nil {
		return nil, err
	}
	parser := newSceneParser(r.format, page.resources)
	parser.budget = budget
	page.Elements, err = parser.parse(root)
	if err != nil {
		return nil, err
	}
	if _, err := r.validateRequiredResources(part, page.resources); err != nil {
		return nil, err
	}
	if err := checkContext(l.context); err != nil {
		return nil, err
	}
	return page, nil
}

// dictionary 每个不同字典只读取和预处理一次，跨页面复用不可变树
// 入参: part 字典部件URI
// 返回: *xmlElement 只读预处理字典, error 读取、校验、预算或取消错误
func (l *printSideXMLLoader) dictionary(part string) (*xmlElement, error) {
	if err := checkContext(l.context); err != nil {
		return nil, err
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	key := strings.ToLower(canonical)
	if root := l.dictionaries[key]; root != nil {
		return root, nil
	}
	root, err := l.reader.readResourceDictionaryLoader(canonical, func(name string) (*xmlElement, error) {
		return l.read(name, true)
	}, l.context)
	if err != nil {
		return nil, err
	}
	l.dictionaries[key] = root
	return root, nil
}

// read 先核对声明字节与剩余容量，再用剩余节点上限解析全部原始XML
// 入参: part 部件URI, dictionary 是否计入远程字典字节预算
// 返回: *xmlElement 原始树, error 读取、CRC、XML、预算或取消错误
func (l *printSideXMLLoader) read(part string, dictionary bool) (*xmlElement, error) {
	if err := checkContext(l.context); err != nil {
		return nil, err
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	size, err := l.reader.pkg.partSize(strings.ToLower(canonical))
	if err != nil {
		return nil, err
	}
	remaining := l.pageBytes
	if dictionary {
		remaining = l.resourceBytes
	}
	limits := l.reader.limits
	limits.MaxPartBytes = min(limits.MaxPartBytes, remaining, l.totalBytes)
	limits.MaxXMLNodes = min(limits.MaxXMLNodes, l.nodes)
	if limits.MaxPartBytes < 1 || limits.MaxXMLNodes < 1 || size > uint64(limits.MaxPartBytes) {
		return nil, &PartError{Part: canonical, Err: fmt.Errorf("%w: print side XML capacity", ErrLimit)}
	}
	nodes := 0
	root, err := l.reader.pkg.readXMLPartLimits(canonical, l.context, limits, func(token xml.Token, node *xmlElement, start, end int64) error {
		if _, ok := token.(xml.StartElement); ok {
			nodes++
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	l.nodes -= nodes
	l.totalBytes -= int64(size)
	if dictionary {
		l.resourceBytes -= int64(size)
	} else {
		l.pageBytes -= int64(size)
	}
	return root, nil
}

// newPrintWatermarkRenderer 创建单次打印操作的水印物化器，不提前校验未使用的配置
// 入参: r 持有读锁的阅读器, options 显式字体及内容原点配置, settings 绘制预算和取消Context
// 返回: *printWatermarkRenderer 串行使用且字体缓存不跨请求共享的物化器
func newPrintWatermarkRenderer(r *Reader, options *PrintWatermarkOptions, settings sceneRenderOptions) *printWatermarkRenderer {
	fonts := &fontCache{data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: settings.fontBytes, maxFaces: settings.fonts}
	if r != nil {
		fonts.pkg = r.pkg
	}
	var configuration *PrintWatermarkOptions
	if options != nil {
		copy := *options
		configuration = &copy
	}
	return &printWatermarkRenderer{fonts: fonts, options: configuration, context: settings.context, glyphs: settings.glyphs, edges: settings.edges, resources: settings.elements, work: settings.work}
}

// remainingSettings 将物化水印已消费的字形预算从最终正文绘制预算中扣除
// 入参: settings 原场景绘制参数，几何物化和最终栅格工作分别计费
// 返回: sceneRenderOptions 保留色彩及其他设置、使用剩余字形容量的绘制参数
func (r *printWatermarkRenderer) remainingSettings(settings sceneRenderOptions) sceneRenderOptions {
	settings.glyphs = min(settings.glyphs, r.glyphs)
	return settings
}

// elements 在源页空间物化并按叠放层级组合水印元素，不修改正文切片及调用方描述
// 入参: part 源页面部件, elements 原正文, watermark 水印描述，nil原样返回正文
// 返回: []Element 完整组合，错误时为nil, error 描述、字体、排版、物化预算或取消错误
func (r *printWatermarkRenderer) elements(part string, elements []Element, watermark *PrintWatermark) ([]Element, error) {
	if watermark == nil {
		return elements, nil
	}
	mark := *watermark
	if err := validatePrintWatermarkDescriptor(mark); err != nil {
		return nil, err
	}
	if err := r.charge(0); err != nil {
		return nil, err
	}
	if r.options == nil || r.options.FontURI == "" {
		return nil, fmt.Errorf("%w: watermark needs an explicit package font and imageable origin", ErrUnsupported)
	}
	if !geometryFinite(r.options.ImageableOrigin.X, r.options.ImageableOrigin.Y) || !utf8.ValidString(r.options.FontURI) {
		return nil, fmt.Errorf("%w: watermark configuration", ErrInvalid)
	}
	if r.options.Layout == nil {
		count := utf8.RuneCountInString(mark.Text)
		if count > r.glyphs || uint64(count) > r.work/2 {
			return nil, fmt.Errorf("%w: watermark nominal layout capacity", ErrLimit)
		}
	}
	uri, index, hasIndex, err := ParseFontURI(r.options.FontURI)
	if err != nil {
		return nil, fmt.Errorf("watermark font URI: %w", err)
	}
	fontPart, err := resolvePart(part, uri)
	if err != nil {
		return nil, fmt.Errorf("watermark font part: %w", err)
	}
	if r.fonts.pkg == nil {
		return nil, fmt.Errorf("%w: watermark reader", ErrInvalid)
	}
	glyphs := &Glyphs{ElementProperties: ElementProperties{Part: part, Opacity: 1}, FontURI: r.options.FontURI, FontPart: fontPart, CollectionIndex: index, HasCollectionIndex: hasIndex, FontRenderingEmSize: mark.FontSize, Text: mark.Text}
	source, err := r.fonts.load(glyphs)
	if err != nil {
		return nil, err
	}
	if err := r.charge(0); err != nil {
		return nil, err
	}
	glyphs.Indices, err = r.layout(mark, source)
	if err != nil {
		return nil, err
	}
	var run *glyphRun
	if mark.Text != "" || len(glyphs.Indices) != 0 {
		run, err = resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, source.glyphYMax, r.glyphs, func() error {
			if err := r.charge(1); err != nil {
				return err
			}
			r.glyphs--
			return nil
		})
		if err != nil {
			return nil, err
		}
	} else {
		run = &glyphRun{}
	}
	if err := r.resource(); err != nil {
		return nil, err
	}
	brush := &Brush{Kind: BrushSolidColor, Part: part, Opacity: 1, Color: Color{Space: ColorSRGB, Alpha: 1, Components: []float64{float64(mark.Color.R) / 255, float64(mark.Color.G) / 255, float64(mark.Color.B) / 255}}}
	var paths []Element
	var ink Point
	hasInk := false
	for _, glyph := range run.glyphs {
		if fontIsBitmapOnly(source.face) {
			items, left, present, err := r.bitmapPaths(source, glyph, mark.FontSize, part, brush)
			if err != nil {
				return nil, &PartError{Part: fontPart, Element: "Glyphs", Err: err}
			}
			paths = append(paths, items...)
			if present {
				if !hasInk {
					ink, hasInk = left, true
				} else {
					ink.X, ink.Y = min(ink.X, left.X), min(ink.Y, left.Y)
				}
			}
			continue
		}
		geometry, err := r.outline(source, glyph.gid)
		if err != nil {
			return nil, &PartError{Part: fontPart, Element: "Glyphs", Err: err}
		}
		figures := geometry.Figures[:0]
		var minX, maxY float64
		for _, figure := range geometry.Figures {
			if figure.IsFilled && len(figure.Segments) != 0 {
				box, err := (&Geometry{Figures: []GeometryFigure{figure}}).Bounds()
				if err != nil {
					return nil, err
				}
				if box.Width == 0 || box.Height == 0 {
					continue
				}
				top := box.Y + box.Height
				if len(figures) == 0 {
					minX, maxY = box.X, top
				} else {
					minX, maxY = min(minX, box.X), max(maxY, top)
				}
				figures = append(figures, figure)
			}
		}
		if len(figures) == 0 {
			continue
		}
		geometry.Figures = figures
		left := glyph.matrix.Transform(Point{X: minX, Y: maxY})
		if !geometryFinite(left.X, left.Y) {
			return nil, fmt.Errorf("%w: watermark ink position", ErrLimit)
		}
		if !hasInk {
			ink, hasInk = left, true
		} else {
			ink.X, ink.Y = min(ink.X, left.X), min(ink.Y, left.Y)
		}
		if err := r.resource(); err != nil {
			return nil, err
		}
		matrix := glyph.matrix
		paths = append(paths, &Path{ElementProperties: ElementProperties{Part: part, Opacity: 1, RenderTransform: &matrix}, Data: &geometry, Fill: brush})
	}
	sine, cosine := math.Sincos(mark.Angle * math.Pi / 180)
	rotation := Matrix{A: cosine, B: -sine, C: sine, D: cosine, E: r.options.ImageableOrigin.X + mark.Origin.X, F: r.options.ImageableOrigin.Y + mark.Origin.Y}
	matrix := rotation.Mul(Matrix{A: 1, D: 1, E: -ink.X, F: -ink.Y})
	if !geometryFillMatrixFinite(matrix) {
		return nil, fmt.Errorf("%w: watermark positioning transform", ErrLimit)
	}
	alpha := float64(mark.Color.A) / 255
	if mark.HasTransparency {
		alpha *= 1 - mark.Transparency/100
	}
	if err := r.resource(); err != nil {
		return nil, err
	}
	canvas := &Canvas{ElementProperties: ElementProperties{Part: part, Opacity: alpha, RenderTransform: &matrix}, Elements: paths}
	if err := r.charge(uint64(len(elements)) + 1); err != nil {
		return nil, err
	}
	result := make([]Element, 0, len(elements)+1)
	if mark.Layer == PrintWatermarkUnderlay {
		result = append(result, canvas)
	}
	result = append(result, elements...)
	if mark.Layer == PrintWatermarkOverlay {
		result = append(result, canvas)
	}
	return result, nil
}

// validatePrintWatermarkDescriptor 独立校验公开水印值，不假定其一定来自票据解析器
// 入参: mark 标量水印描述，字号和原点已换算为内容单位
// 返回: error 非有限数值、范围、字符或层次错误
func validatePrintWatermarkDescriptor(mark PrintWatermark) error {
	if !geometryFinite(mark.Origin.X, mark.Origin.Y, mark.FontSize, mark.Angle, mark.Transparency) || mark.FontSize <= 0 || mark.Angle < 0 || mark.Angle > 359 || math.Trunc(mark.Angle) != mark.Angle || mark.Transparency < 0 || mark.Transparency > 100 || math.Trunc(mark.Transparency) != mark.Transparency {
		return fmt.Errorf("%w: watermark numeric descriptor", ErrInvalid)
	}
	if mark.Layer != PrintWatermarkOverlay && mark.Layer != PrintWatermarkUnderlay {
		return fmt.Errorf("%w: watermark layer descriptor", ErrInvalid)
	}
	if !utf8.ValidString(mark.Text) || !xmlTextValid(mark.Text) || len(mark.Text) > 4*printWatermarkTextLimit || utf8.RuneCountInString(mark.Text) > printWatermarkTextLimit {
		return fmt.Errorf("%w: watermark text descriptor", ErrInvalid)
	}
	return nil
}

// layout 获取并复制同一字体的簇映射，缺省只按Unicode选择字形而不重塑形
// 入参: mark 值副本, source 所选字体
// 返回: []GlyphCluster 独立且与Text一致的字形簇, error 回调、映射、预算或取消错误
func (r *printWatermarkRenderer) layout(mark PrintWatermark, source *fontSource) ([]GlyphCluster, error) {
	if r.options.Layout == nil {
		count := utf8.RuneCountInString(mark.Text)
		if count > r.glyphs {
			return nil, fmt.Errorf("%w: watermark nominal glyph count", ErrLimit)
		}
		if err := r.charge(uint64(count)); err != nil {
			return nil, err
		}
		clusters := make([]GlyphCluster, 0, count)
		for _, character := range mark.Text {
			if err := r.charge(0); err != nil {
				return nil, err
			}
			lookup := character
			switch character {
			case '\t', '\r', '\n', 0x85, 0x2028, 0x2029:
				lookup = ' '
			}
			gid, err := source.glyphIndex(lookup)
			if err != nil {
				return nil, err
			}
			units := 1
			if character > 0xffff {
				units = 2
			}
			clusters = append(clusters, GlyphCluster{CodeUnitCount: units, HasMapping: true, Glyphs: []GlyphIndex{{Index: gid, HasIndex: true}}})
		}
		return clusters, nil
	}
	clusters, err := r.options.Layout(r.context, mark)
	if canceled := r.charge(0); canceled != nil {
		return nil, canceled
	}
	if err != nil {
		return nil, err
	}
	if len(clusters) > r.glyphs {
		return nil, fmt.Errorf("%w: watermark layout cluster count", ErrLimit)
	}
	count := 0
	for _, cluster := range clusters {
		if len(cluster.Glyphs) > r.glyphs-count {
			return nil, fmt.Errorf("%w: watermark layout glyph count", ErrLimit)
		}
		count += len(cluster.Glyphs)
		if err := r.charge(uint64(len(cluster.Glyphs)) + 1); err != nil {
			return nil, err
		}
	}
	if mark.Text == "" && len(clusters) != 0 {
		return nil, fmt.Errorf("%w: watermark layout has glyphs without text", ErrInvalid)
	}
	if mark.Text != "" {
		if _, err := glyphRunCount(&Glyphs{Text: mark.Text, Indices: clusters, FontRenderingEmSize: mark.FontSize}, r.glyphs); err != nil {
			return nil, err
		}
	}
	owned := make([]GlyphCluster, len(clusters))
	for i, cluster := range clusters {
		owned[i] = cluster
		owned[i].Glyphs = append([]GlyphIndex(nil), cluster.Glyphs...)
	}
	return owned, nil
}

// outline 用既有字体解码器展开轮廓，并将解码工作计入整个打印请求的累计预算
// 入参: source 当前字体, gid 原始字形编号，保留缺字GID0
// 返回: Geometry 独立设计单位轮廓, error 字体、位图能力、预算或取消错误
func (r *printWatermarkRenderer) outline(source *fontSource, gid uint16) (Geometry, error) {
	if err := r.charge(1); err != nil {
		return Geometry{}, err
	}
	source.outlineOnce.Do(source.loadOutline)
	if source.outlineErr != nil {
		return Geometry{}, source.outlineErr
	}
	limit := int(min(r.work, uint64(^uint(0)>>1)))
	if limit == 0 {
		return Geometry{}, fmt.Errorf("%w: watermark outline work", ErrLimit)
	}
	if source.trueType != nil {
		budget := &trueTypeBudget{context: r.context, workLimit: limit}
		glyph, err := source.trueType.load(gid, budget)
		r.work -= uint64(budget.work)
		if err != nil {
			return Geometry{}, err
		}
		geometry, err := trueTypeGeometryWithStep(glyph.points, glyph.endPoints, r.reserveGeometry)
		if err != nil {
			return Geometry{}, err
		}
		_, bearing, err := source.metrics.horizontal(glyph.metricsGlyph)
		if err != nil {
			return Geometry{}, err
		}
		if err := fontTransformOutline(&geometry, Matrix{A: 1, D: 1, E: float64(bearing) - glyph.metricsBounds.X}); err != nil {
			return Geometry{}, err
		}
		return geometry, nil
	}
	if source.cff.paintType != 0 {
		return Geometry{}, fmt.Errorf("%w: watermark CFF PaintType", ErrUnsupported)
	}
	glyph, err := r.cffGlyph(source.cff, gid, &limit)
	consumed := min(r.work, uint64(^uint(0)>>1)) - uint64(limit)
	r.work -= consumed
	if err != nil {
		return Geometry{}, err
	}
	matrix, err := source.cff.designMatrix(gid, source.metrics.unitsPerEm)
	if err != nil {
		return Geometry{}, err
	}
	if err := fontTransformOutline(&glyph.geometry, matrix); err != nil {
		return Geometry{}, err
	}
	return glyph.geometry, nil
}

// bitmapPaths 按内容字号解码嵌入式位图字形并转换为像素行程路径元素
// 入参: source 字体, glyph 已定位字形, size 九十六dpi内容字号, part 源页面部件, brush 不透明颜色
// 返回: []Element 像素行程路径, Point 实际非零像素左上角, bool 是否有墨迹, error 尺寸、字体或预算错误
func (r *printWatermarkRenderer) bitmapPaths(source *fontSource, glyph positionedGlyph, size float64, part string, brush *Brush) ([]Element, Point, bool, error) {
	if err := r.charge(1); err != nil {
		return nil, Point{}, false, err
	}
	if size < 1 || size > 255 || math.Trunc(size) != size {
		return nil, Point{}, false, fmt.Errorf("%w: bitmap watermark requires integral content ppem in 1..255", ErrUnsupported)
	}
	ppem := uint16(size)
	selection, present, err := source.selectBitmapStrikeWithWork(ppem, ppem, r.charge)
	if err != nil {
		return nil, Point{}, false, err
	}
	if !present {
		return nil, Point{}, false, fmt.Errorf("%w: no matching watermark bitmap strike", ErrUnsupported)
	}
	decoder := fontBitmapDecode{font: source.bitmaps, strike: &source.bitmaps.strikes[selection.strike], path: make(map[uint16]bool), cache: make(map[uint16]fontBitmapDecoded), components: min(fontBitmapMaxComponents, int(min(r.work, uint64(^uint(0)>>1)))), pixels: min(fontBitmapMaxPixels, int(min(r.work, uint64(^uint(0)>>1))))}
	components, pixels := decoder.components, decoder.pixels
	decoded, present, err := decoder.decode(glyph.gid)
	if charged := r.charge(uint64(components-decoder.components) + uint64(pixels-decoder.pixels)); charged != nil {
		return nil, Point{}, false, charged
	}
	if err != nil {
		return nil, Point{}, false, err
	}
	if !present {
		return nil, Point{}, false, fmt.Errorf("%w: watermark bitmap glyph %d is absent", ErrUnsupported, glyph.gid)
	}
	if !decoded.metrics.hasHorizontal {
		return nil, Point{}, false, fmt.Errorf("%w: watermark bitmap has no horizontal bearing", ErrUnsupported)
	}
	mask := decoded.mask
	x0 := glyph.origin.X + float64(decoded.metrics.horizontal.bearingX)*selection.scaleX
	y0 := glyph.origin.Y - float64(decoded.metrics.horizontal.bearingY)*selection.scaleY
	if !geometryFinite(x0, y0) {
		return nil, Point{}, false, fmt.Errorf("%w: watermark bitmap bearing overflow", ErrLimit)
	}
	var coverage [256]Geometry
	var ink Point
	hasInk := false
	for y := mask.Rect.Min.Y; y < mask.Rect.Max.Y; y++ {
		if err := r.charge(uint64(mask.Rect.Dx())); err != nil {
			return nil, Point{}, false, err
		}
		for x := mask.Rect.Min.X; x < mask.Rect.Max.X; {
			alpha := mask.AlphaAt(x, y).A
			end := x + 1
			for end < mask.Rect.Max.X && mask.AlphaAt(end, y).A == alpha {
				end++
			}
			if alpha != 0 {
				if r.edges < 3 {
					return nil, Point{}, false, fmt.Errorf("%w: watermark bitmap edges", ErrLimit)
				}
				if err := r.charge(4); err != nil {
					return nil, Point{}, false, err
				}
				r.edges -= 3
				box := Rect{X: x0 + float64(x)*selection.scaleX, Y: y0 + float64(y)*selection.scaleY, Width: float64(end-x) * selection.scaleX, Height: selection.scaleY}
				if !geometryFinite(box.X, box.Y, box.X+box.Width, box.Y+box.Height) {
					return nil, Point{}, false, fmt.Errorf("%w: watermark bitmap pixel overflow", ErrLimit)
				}
				geometry := &coverage[alpha]
				geometry.FillRule = GeometryNonZero
				geometry.Figures = append(geometry.Figures, renderBoxGeometry(box).Figures[0])
				if !hasInk {
					ink, hasInk = Point{X: box.X, Y: box.Y}, true
				} else {
					ink.X, ink.Y = min(ink.X, box.X), min(ink.Y, box.Y)
				}
			}
			x = end
		}
	}
	var paths []Element
	for alpha := 1; alpha < len(coverage); alpha++ {
		if len(coverage[alpha].Figures) == 0 {
			continue
		}
		if err := r.resource(); err != nil {
			return nil, Point{}, false, err
		}
		paths = append(paths, &Path{ElementProperties: ElementProperties{Part: part, Opacity: float64(alpha) / 255}, Data: &coverage[alpha], Fill: brush})
	}
	return paths, ink, hasInk, nil
}

// cffGlyph 在同一Type2累计预算内解析普通字形及合法的非嵌套seac组合
// 入参: font 已解析CFF字体, gid 当前字形, remaining 剩余解码工作
// 返回: *type2Glyph 独立原始轮廓, error 程序、组合或预算错误
func (r *printWatermarkRenderer) cffGlyph(font *cffFont, gid uint16, remaining *int) (*type2Glyph, error) {
	if font.charstringType != 2 {
		return nil, fmt.Errorf("%w: watermark CFF CharstringType %g", ErrUnsupported, font.charstringType)
	}
	geometryStep := func(edges int) error {
		if err := checkContext(r.context); err != nil {
			return err
		}
		if edges > r.edges || *remaining <= 0 {
			return fmt.Errorf("%w: watermark CFF geometry capacity", ErrLimit)
		}
		r.edges -= edges
		*remaining -= 1
		return nil
	}
	decode := func(index uint16) (*type2Glyph, error) {
		private := font.top.private
		if font.cid {
			private = font.fontDict[font.fdSelect[index]].private
		}
		return parseType2(font.charstrings[index], type2Context{globalSubr: font.set.globalSubr, localSubr: private.localSubr, defaultWidth: private.defaultWidth, nominalWidth: private.nominalWidth, randomSeed: private.randomSeed, context: r.context, work: remaining, geometryStep: geometryStep})
	}
	glyph, err := decode(gid)
	if err != nil || glyph.seac == nil {
		return glyph, err
	}
	if font.cid {
		return nil, fmt.Errorf("%w: CID CFF watermark seac", ErrInvalid)
	}
	for i, code := range []byte{glyph.seac.base, glyph.seac.accent} {
		sid := cffStandardSID(code)
		index, present := font.charset.glyph(sid)
		if sid == 0 || !present {
			return nil, fmt.Errorf("%w: missing watermark CFF seac component", ErrInvalid)
		}
		component, err := decode(index)
		if err != nil {
			return nil, err
		}
		if component.seac != nil {
			return nil, fmt.Errorf("%w: nested watermark CFF seac", ErrInvalid)
		}
		if i == 1 {
			if err := cffTranslateGlyph(&component.geometry, glyph.seac.offset); err != nil {
				return nil, err
			}
		}
		glyph.geometry.Figures = append(glyph.geometry.Figures, component.geometry.Figures...)
	}
	glyph.seac = nil
	return glyph, nil
}

// charge 检查取消并扣除累计物化工作，不因透明水印或空输出区域省略验证
// 入参: count 本步骤工作量
// 返回: error 取消或累计预算不足错误
func (r *printWatermarkRenderer) charge(count uint64) error {
	if err := checkContext(r.context); err != nil {
		return err
	}
	if count > r.work {
		return fmt.Errorf("%w: watermark materialization work", ErrLimit)
	}
	r.work -= count
	return nil
}

// resource 在追加画刷或绘制元素前检查累计资源外壳容量
// 返回: error 资源容量、工作或取消错误
func (r *printWatermarkRenderer) resource() error {
	if err := r.charge(1); err != nil {
		return err
	}
	if r.resources <= 0 {
		return fmt.Errorf("%w: watermark materialization resources", ErrLimit)
	}
	r.resources--
	return nil
}

// reserveGeometry 在追加一个子路径或语义段前预留累计容量，包括不产生墨迹的退化轮廓
// 入参: edges 本次语义段数，子路径为零、线段为一
// 返回: error 几何物化预算或取消错误
func (r *printWatermarkRenderer) reserveGeometry(edges int) error {
	if edges > r.edges {
		return fmt.Errorf("%w: watermark materialization edges", ErrLimit)
	}
	if err := r.charge(1); err != nil {
		return err
	}
	r.edges -= edges
	return nil
}

// printResourceMedia 识别Microsoft两代票据及能力媒体类型，不接受参数或猜测自定义票据
// 入参: media 不含参数的部件内容类型
// 返回: known 是否为已知Microsoft格式, capabilities 是否为能力文档
func printResourceMedia(media string) (known bool, capabilities bool) {
	switch strings.ToLower(media) {
	case printTicketType, "application/vnd.ms-printschematicket+xml":
		return true, false
	case "application/vnd.ms-printing.printcapabilities+xml", "application/vnd.ms-printschemacapabilities+xml":
		return true, true
	default:
		return false, false
	}
}

// collectPrintResourceReferences 按标准资源参数与选项路径提取票据或能力模型中的资源引用
// 入参: ctx 取消Context, document 原模型及用途, options 资源参数，Scope不得与document冲突
// 返回: []printResourceReference 独立引用位置，失败为nil, error 结构、资源标识、预算或取消错误
func collectPrintResourceReferences(ctx context.Context, document printResourceDocument, options *PrintSettingsOptions) ([]printResourceReference, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	if document.model == nil || document.scope > PrintScopePage || configuration.Scope != PrintScopeUnknown && document.scope != PrintScopeUnknown && configuration.Scope != document.scope {
		return nil, fmt.Errorf("%w: print resource model or scope", ErrInvalid)
	}
	if document.scope == PrintScopeUnknown {
		document.scope = configuration.Scope
	}
	configuration.Scope = document.scope
	if document.capabilities && document.scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print capabilities resources", ErrInvalid)
	}
	if document.part != "" {
		if _, err := opcPartName(document.part); err != nil {
			return nil, err
		}
	}
	c := &printResourceCollector{document: document, options: configuration, nodes: 1, namespaces: map[string]bool{printFrameworkNS: true}, parameters: make(map[xml.Name][]int)}
	result, err := c.collect()
	if err != nil {
		if document.part != "" {
			err = &PartError{Part: document.part, Err: err}
		}
		return nil, err
	}
	return result, nil
}

// collect 先校验累计输入规模和Framework，再按原始索引建立参数表及标准引用
// 返回: []printResourceReference 完整结果, error 结构、标识、预算或取消错误
func (c *printResourceCollector) collect() ([]printResourceReference, error) {
	if err := c.scan(c.document.model.Elements, 2); err != nil {
		return nil, err
	}
	root, err := printDocumentRoot(c.document.model.Version, c.document.model.Elements, c.options, c.document.capabilities)
	if err != nil {
		return nil, err
	}
	if _, err := parsePrintDocument(root, c.options, c.document.capabilities); err != nil {
		return nil, err
	}
	parameterKind := PrintSettingParameterInit
	if c.document.capabilities {
		parameterKind = PrintSettingParameterDef
	}
	for i := range c.document.model.Elements {
		if err := checkContext(c.options.context); err != nil {
			return nil, err
		}
		element := &c.document.model.Elements[i]
		if c.inScope(element.Name) && element.Kind == parameterKind {
			path := []int{i, 0}
			if c.document.capabilities {
				path = nil
				for j := range element.Children {
					property := &element.Children[j]
					if property.Kind == PrintSettingProperty && property.Name == (xml.Name{Space: printFrameworkNS, Local: "DefaultValue"}) {
						path = []int{i, j, 0}
					}
				}
			}
			if err := c.reserve(int64(len(path)) * 8); err != nil {
				return nil, err
			}
			c.parameters[element.Name] = path
		}
	}
	for i := range c.document.model.Elements {
		if err := checkContext(c.options.context); err != nil {
			return nil, err
		}
		element := &c.document.model.Elements[i]
		if !c.inScope(element.Name) {
			continue
		}
		if element.Kind == parameterKind {
			for _, rule := range printResourceRules {
				parameter := xml.Name{Space: printKeywordsNS, Local: rule.parameter}
				if element.Name == parameter {
					if err := c.parameter(parameter, rule.kind); err != nil {
						return nil, err
					}
					break
				}
			}
			continue
		}
		if err := c.features(element, []int{i}); err != nil {
			return nil, err
		}
	}
	if err := checkContext(c.options.context); err != nil {
		return nil, err
	}
	return c.references, nil
}

// features 递归遍历设置子树并按标准Feature与Option路径收集资源引用
// 入参: element 当前设置, path 当前设置在原模型中的路径
// 返回: error 引用、预算或取消错误
func (c *printResourceCollector) features(element *PrintSetting, path []int) error {
	if err := checkContext(c.options.context); err != nil {
		return err
	}
	if element.Kind == PrintSettingFeature {
		for _, rule := range printResourceRules {
			if rule.feature == "" || element.Name != (xml.Name{Space: printKeywordsNS, Local: rule.feature}) {
				continue
			}
			for i := range element.Children {
				option := &element.Children[i]
				if option.Kind != PrintSettingOption || option.Name.Space != printKeywordsNS || !slices.Contains(rule.options, option.Name.Local) {
					continue
				}
				for j := range option.Children {
					property := &option.Children[j]
					if property.Kind != PrintSettingScoredProperty || property.Name != (xml.Name{Space: printKeywordsNS, Local: rule.property}) {
						continue
					}
					for k := range property.Children {
						value := &property.Children[k]
						if value.Kind == PrintSettingValue {
							if err := c.value(append(path[:len(path):len(path)], i, j, k), rule.kind); err != nil {
								return err
							}
						} else if value.Kind == PrintSettingParameterRef {
							if err := c.parameter(value.Name, rule.kind); err != nil {
								return err
							}
						}
					}
				}
			}
		}
	}
	for i := range element.Children {
		if err := c.features(&element.Children[i], append(path, i)); err != nil {
			return err
		}
	}
	return nil
}

// scan 在复制XML或建立索引前累计计算全部输入，包括被层级过滤的设置与私有内容
// 入参: elements 当前层内容, depth 包含Framework根的XML深度
// 返回: error 节点、深度、字符串总量或取消错误
func (c *printResourceCollector) scan(elements []PrintSetting, depth int) error {
	for i := range elements {
		if err := checkContext(c.options.context); err != nil {
			return err
		}
		if c.nodes >= c.options.Limits.MaxXMLNodes || depth > c.options.Limits.MaxXMLDepth {
			return fmt.Errorf("%w: print resource input complexity", ErrLimit)
		}
		c.nodes++
		element := &elements[i]
		for _, text := range []string{element.Name.Space, element.Name.Local} {
			if err := c.reserve(int64(len(text))); err != nil {
				return err
			}
		}
		if err := c.namespace(element.Name.Space); err != nil {
			return err
		}
		if element.Value != nil {
			for _, text := range []string{element.Value.Type.Space, element.Value.Type.Local, element.Value.Text, element.Value.QName.Space, element.Value.QName.Local} {
				if err := c.reserve(int64(len(text))); err != nil {
					return err
				}
			}
			for _, space := range []string{printValueNS, xsiNamespace, element.Value.Type.Space, element.Value.QName.Space} {
				if err := c.namespace(space); err != nil {
					return err
				}
			}
		}
		if len(element.Children) != 0 {
			if err := c.scan(element.Children, depth+1); err != nil {
				return err
			}
		}
	}
	return nil
}

// namespace 累计约束模型编码所需的不同命名空间，不为每个子树重置绑定限额
// 入参: space 已计入字符串总量的命名空间，空值不占绑定
// 返回: error 绑定预算错误
func (c *printResourceCollector) namespace(space string) error {
	if space == "" || c.namespaces[space] {
		return nil
	}
	if len(c.namespaces) >= c.options.Limits.MaxXMLBindings {
		return fmt.Errorf("%w: print resource namespace budget", ErrLimit)
	}
	c.namespaces[space] = true
	return nil
}

// reserve 累计输入字符串及输出URI和路径的存储量，采用减法避免整数溢出
// 入参: size 本次新增字节数
// 返回: error 总量错误
func (c *printResourceCollector) reserve(size int64) error {
	limit := min(c.options.Limits.MaxMetadataBytes, c.options.Limits.MaxPartBytes, c.options.Limits.MaxPackageBytes)
	if size < 0 || size > limit-c.bytes {
		return fmt.Errorf("%w: print resource byte budget", ErrLimit)
	}
	c.bytes += size
	return nil
}

// inScope 按关键字约定的作用域前缀过滤根设置，与现有票据解析保持一致
// 入参: name 根设置的展开名称
// 返回: bool 是否保留该设置
func (c *printResourceCollector) inScope(name xml.Name) bool {
	scope := printKeywordScope(name)
	return c.document.capabilities || c.document.scope == PrintScopeUnknown || scope == PrintScopeUnknown || scope >= c.document.scope
}

// parameter 定位显式初始化或能力默认值，不补造设备参数，不把空值解释为包根
// 入参: name 实际参数名称, kind 标准位置确定的资源用途
// 返回: error 未初始化参数、定义、资源或预算错误
func (c *printResourceCollector) parameter(name xml.Name, kind printResourceKind) error {
	path, exists := c.parameters[name]
	if !exists {
		return fmt.Errorf("%w: print resource parameter {%s}%s is not initialized", ErrUnsupported, name.Space, name.Local)
	}
	if len(path) == 0 {
		return fmt.Errorf("%w: missing print resource default", ErrInvalid)
	}
	return c.value(path, kind)
}

// value 校验资源字符串和严格OPC部件名，并保存独立定位路径，不合并共享初始化值
// 入参: path 原模型中的Value路径, kind 资源用途
// 返回: error 字符串类型、能力默认值、部件名或引用预算错误
func (c *printResourceCollector) value(path []int, kind printResourceKind) error {
	elements := c.document.model.Elements
	var element *PrintSetting
	for _, index := range path {
		if index < 0 || index >= len(elements) {
			return fmt.Errorf("%w: print resource value path", ErrInvalid)
		}
		element = &elements[index]
		elements = element.Children
	}
	if element == nil || element.Kind != PrintSettingValue || element.Value == nil {
		return fmt.Errorf("%w: print resource value", ErrInvalid)
	}
	value := element.Value
	if value.Type != (xml.Name{}) && value.Type != (xml.Name{Space: printValueNS, Local: "string"}) || value.QName != (xml.Name{}) {
		return fmt.Errorf("%w: print resource string type", ErrInvalid)
	}
	if value.Text == "" {
		return nil
	}
	uri, err := opcPartName(value.Text)
	if err != nil {
		return err
	}
	if len(c.references) >= c.options.Limits.MaxPartCount {
		return fmt.Errorf("%w: print resource reference budget", ErrLimit)
	}
	if err := c.reserve(int64(len(uri)) + int64(len(path))*8); err != nil {
		return err
	}
	c.references = append(c.references, printResourceReference{path: slices.Clone(path), uri: uri, kind: kind})
	return nil
}
