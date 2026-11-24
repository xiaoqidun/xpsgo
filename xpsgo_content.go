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
	"fmt"
	"strconv"
	"strings"
	"unicode/utf8"
)

const (
	// ReadingPage 表示按固定页面顺序组织文档内容
	ReadingPage ReadingOrder = iota
	// ReadingStory 表示按文档故事结构顺序组织文档内容
	ReadingStory
)

const (
	// LineCapFlat 表示平头线帽样式
	LineCapFlat LineCap = "Flat"
	// LineCapRound 表示圆头线帽样式
	LineCapRound LineCap = "Round"
	// LineCapSquare 表示方头线帽样式
	LineCapSquare LineCap = "Square"
	// LineCapTriangle 表示三角线帽样式
	LineCapTriangle LineCap = "Triangle"
)

const (
	// LineJoinMiter 表示尖角线段连接样式
	LineJoinMiter LineJoin = "Miter"
	// LineJoinBevel 表示斜切线段连接样式
	LineJoinBevel LineJoin = "Bevel"
	// LineJoinRound 表示圆角线段连接样式
	LineJoinRound LineJoin = "Round"
)

const (
	// EdgeModeAliased 表示禁用抗锯齿的像素对齐边缘模式
	EdgeModeAliased EdgeMode = "Aliased"
)

const (
	// StyleSimulationNone 表示不启用字体样式模拟
	StyleSimulationNone StyleSimulation = "None"
	// StyleSimulationBold 表示启用粗体样式模拟
	StyleSimulationBold StyleSimulation = "BoldSimulation"
	// StyleSimulationItalic 表示启用斜体样式模拟
	StyleSimulationItalic StyleSimulation = "ItalicSimulation"
	// StyleSimulationBoldItalic 表示同时启用粗体与斜体样式模拟
	StyleSimulationBoldItalic StyleSimulation = "BoldItalicSimulation"
)

// ReadingOrder 选择按页面或按故事组织内容，不从版面位置覆盖作者指定的顺序
type ReadingOrder uint8

// LineCap 表示路径描边端点及虚线帽样式
type LineCap string

// LineJoin 表示路径描边折角连接样式
type LineJoin string

// EdgeMode 表示画布渲染边缘对齐模式
type EdgeMode string

// StyleSimulation 表示字形合成样式模拟选项
type StyleSimulation string

// ContentLimits 规定单次内容读取的解压字节、节点、关联及字形字体预算，零值采用默认值
// Text输出的UTF-8字节数另受MaxBytes约束，XML解析同时受阅读器上限约束
type ContentLimits struct {
	MaxBytes  int64
	MaxNodes  int
	MaxWork   uint64
	MaxGlyphs int
	MaxFonts  int
}

// ContentOptions 设置阅读顺序与资源上限，零值按页面组织
// ResolveGlyphs启用字形定位并读取所需字体；未启用时保留声明数据，不解码字体
type ContentOptions struct {
	Order         ReadingOrder
	Limits        ContentLimits
	ResolveGlyphs bool
}

// ContentReference 保存已绑定的页面及名称，Page为阅读器的零基全局页号
type ContentReference struct {
	Page int
	Part string
	Name string
}

// ContentSegment 保存续接节点在各源片段中的属性，不丢弃跨页属性差异
type ContentSegment struct {
	Page       int
	RowSpan    int32
	ColumnSpan int32
}

// ContentNode 保存绑定后的语义结构，命名元素与列表标记的来源在跨页合并后仍可追溯
type ContentNode struct {
	Kind       StructureKind
	RowSpan    int32
	ColumnSpan int32
	References []ContentReference
	Markers    []ContentReference
	Segments   []ContentSegment
	Children   []ContentNode
}

// ContentFragment 保存已绑定的单页片段及断点，Part为原故事片段部件
type ContentFragment struct {
	Page         int
	Part         string
	StoryName    *string
	FragmentName *string
	Type         FragmentType
	BreakBefore  bool
	BreakAfter   bool
	Content      []ContentNode
}

// ContentStory 保存作者指定的片段顺序及按断点规则续接的完整语义结构
type ContentStory struct {
	Name      string
	Fragments []ContentFragment
	Content   []ContentNode
}

// ContentPage 保存指定文档内的页面及其声明顺序的片段，Page为零基全局页号
type ContentPage struct {
	Page      int
	Part      string
	Fragments []ContentFragment
}

// ContentItem 保存阅读顺序中的绘制元素及有效变换、语言与链接，画布子内容作为独立条目出现
// VisualSource标记视觉画刷源引用，此时Transform为定义坐标变换
// Glyphs仅在启用ResolveGlyphs后填充定位结果，不同调用不共享可变数据
type ContentItem struct {
	Page         int
	Part         string
	Element      Element
	Transform    Matrix
	Language     string
	NavigateURI  *string
	StoryName    *string
	FragmentName *string
	FragmentType FragmentType
	VisualSource bool
	Glyphs       []GlyphPosition
}

// DocumentContent 保存文档的页面、故事及实际阅读顺序，不对缺少的语义结构进行版面猜测
type DocumentContent struct {
	Part        string
	Pages       []ContentPage
	Stories     []ContentStory
	Items       []ContentItem
	Diagnostics []Diagnostic
}

// contentGraph 保存单次内容读取的私有索引与预算，不修改原阅读器的状态
type contentGraph struct {
	reader    *Reader
	document  Document
	options   ContentOptions
	context   context.Context
	bytes     int64
	nodes     int
	work      uint64
	glyphs    int
	pages     []*contentPage
	structure *DocumentStructure
	result    DocumentContent
}

// GlyphPosition 保存字形编号、UTF-16半开簇范围及页面坐标定位
// 无Unicode文字时TextStart和TextEnd为-1，Origin为锚点，Nominal为未偏移行进原点
// Advance为页面步进向量，Transform将字体设计单位映射到页面并含斜体模拟变换
type GlyphPosition struct {
	Index           uint16
	Cluster         int
	TextStart       int
	TextEnd         int
	ExplicitIndex   bool
	ExplicitAdvance bool
	Nominal         Point
	Origin          Point
	Advance         Point
	Transform       Matrix
}

// Element 表示页面或画布中的绘制元素
type Element interface {
	element()
}

// ElementProperties 保存元素的局部变换、透明度、链接与语言声明
// Language和NavigateURI为nil时沿用父级或使用位置的环境值
type ElementProperties struct {
	Part            string
	Name            string
	RenderTransform *Matrix
	Clip            *Geometry
	Opacity         float64
	OpacityMask     *Brush
	Language        *string
	NavigateURI     *string
	source          *xmlElement
}

// Canvas 保存按声明顺序绘制并作为整体合成的子元素，坐标与变换均采用1/96英寸设备无关单位
// EdgeMode省略为空字符串时默认启用抗锯齿，非空合法取值为EdgeModeAliased
type Canvas struct {
	ElementProperties
	Elements           []Element
	EdgeMode           EdgeMode
	AutomationName     string
	AutomationHelpText string
}

// Path 保存路径几何、填充画刷及描边参数，几何坐标与StrokeThickness采用1/96英寸单位
// StrokeDashArray与StrokeDashOffset以StrokeThickness为倍数单位
// 线帽取值为LineCap*常量，线段连接取值为LineJoin*常量
type Path struct {
	ElementProperties
	Data                *Geometry
	Fill                *Brush
	Stroke              *Brush
	StrokeThickness     float64
	StrokeDashArray     []float64
	StrokeDashOffset    float64
	StrokeDashCap       LineCap
	StrokeStartLineCap  LineCap
	StrokeEndLineCap    LineCap
	StrokeLineJoin      LineJoin
	StrokeMiterLimit    float64
	SnapsToDevicePixels *bool
	AutomationName      string
	AutomationHelpText  string
}

// Glyphs 保存嵌入字体引用、字形映射及局部定位参数，不重新排版已有字形
// FontRenderingEmSize与Origin采用1/96英寸设备无关单位，Text为已去除XML前导{}转义的纯文本
// StyleSimulations合法取值为StyleSimulationNone、StyleSimulationBold、StyleSimulationItalic、StyleSimulationBoldItalic
type Glyphs struct {
	ElementProperties
	FontURI             string
	FontPart            string
	CollectionIndex     uint32
	HasCollectionIndex  bool
	FontRenderingEmSize float64
	Origin              Point
	Fill                *Brush
	BidiLevel           int
	IsSideways          bool
	Text                string
	Indices             []GlyphCluster
	StyleSimulations    StyleSimulation
	CaretStops          string
	DeviceFontName      string
}

// contentRange 表示页面索引中一个元素及其画布子内容的半开范围
type contentRange struct {
	first int
	last  int
}

// contentSource 保存非直接页面元素的定义变换、语言与链接状态
type contentSource struct {
	element   Element
	transform Matrix
	language  string
	link      *string
}

// contentPage 保存一次读取的页面内容、名称索引和已输出标记
type contentPage struct {
	page      *Page
	number    int
	items     []ContentItem
	names     map[string]contentRange
	extras    map[string]contentSource
	seen      []bool
	fragments []ContentFragment
}

// contentFragmentKey 区分页面、故事及片段名称的省略状态，不把空名称折叠为未命名
type contentFragmentKey struct {
	page  int
	story string
	name  string
	named bool
}

// GlyphIndex 表示字形条目，Has字段保留省略状态，度量单位为em的百分之一
type GlyphIndex struct {
	Index           uint16
	HasIndex        bool
	AdvanceWidth    float64
	HasAdvanceWidth bool
	UOffset         float64
	HasUOffset      bool
	VOffset         float64
	HasVOffset      bool
}

// GlyphCluster 表示UTF-16字形簇，HasMapping标记显式前缀，HasGlyphCount区分(n)与(n:1)
type GlyphCluster struct {
	CodeUnitCount int
	Glyphs        []GlyphIndex
	HasMapping    bool
	HasGlyphCount bool
}

// String 返回阅读顺序的可读名称
// 返回: string 阅读顺序名称
func (o ReadingOrder) String() string {
	switch o {
	case ReadingPage:
		return "page"
	case ReadingStory:
		return "story"
	default:
		return "unknown"
	}
}

// DefaultContentLimits 返回默认内容读取预算
// 返回: ContentLimits 资源上限
func DefaultContentLimits() ContentLimits {
	limits := DefaultLimits()
	return ContentLimits{MaxBytes: limits.MaxPackageBytes, MaxNodes: limits.MaxXMLNodes, MaxWork: 1 << 26, MaxGlyphs: 1 << 20, MaxFonts: 256}
}

// DefaultContentOptions 返回按页面组织内容的默认参数
// 返回: ContentOptions 内容参数
func DefaultContentOptions() ContentOptions {
	return ContentOptions{Order: ReadingPage, Limits: DefaultContentLimits()}
}

// Content 读取固定文档的绑定内容和阅读顺序，出错或取消时不返回部分结果
// 调用期间保持阅读器读锁，Context在各处理步骤间检查取消状态
// 入参: ctx 取消Context，nil采用Background, docIndex 零基固定文档序号, options 内容参数，nil采用默认值
// 返回: *DocumentContent 独立内容结果, error 读取、关联、预算或取消错误
func (r *Reader) Content(ctx context.Context, docIndex int, options *ContentOptions) (*DocumentContent, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	configuration, err := contentConfiguration(options)
	if err != nil {
		return nil, err
	}
	return r.readContent(ctx, docIndex, configuration)
}

// readContent 在调用方持有阅读器读锁时构建绑定内容和阅读顺序
// 入参: ctx 取消Context, index 零基固定文档序号, configuration 已校验的内容参数
// 返回: *DocumentContent 独立内容结果, error 读取、关联、预算或取消错误
func (r *Reader) readContent(ctx context.Context, index int, configuration ContentOptions) (*DocumentContent, error) {
	if index < 0 || index >= len(r.documents) {
		return nil, fmt.Errorf("%w: document index out of range: %d", ErrInvalid, index)
	}
	g := contentGraph{document: r.documents[index], options: configuration, context: ctx, bytes: configuration.Limits.MaxBytes, nodes: configuration.Limits.MaxNodes, work: configuration.Limits.MaxWork, glyphs: configuration.Limits.MaxGlyphs}
	pkg := *r.pkg
	pkg.beforeRead = g.readAllowance
	g.reader = &Reader{pkg: &pkg, format: r.format, limits: r.limits, sequence: r.sequence, documents: r.documents, pages: r.pages, fixedXML: r.fixedXML}
	if err := g.charge(0); err != nil {
		return nil, err
	}
	structure, err := g.reader.readDocumentStructureContext(g.context, index)
	if err != nil {
		return nil, err
	}
	g.structure, g.result.Part = structure, g.document.Part
	first := 0
	for _, document := range r.documents[:index] {
		first += len(document.Pages)
	}
	for local := range len(g.document.Pages) {
		if err := g.loadPage(first + local); err != nil {
			return nil, err
		}
	}
	if err := g.bindStories(); err != nil {
		return nil, err
	}
	if err := g.readingOrder(); err != nil {
		return nil, err
	}
	if configuration.ResolveGlyphs {
		if err := g.positionGlyphs(); err != nil {
			return nil, err
		}
	}
	if err := g.charge(0); err != nil {
		return nil, err
	}
	return &g.result, nil
}

// contentConfiguration 补齐零值预算并校验内容参数，不修改调用方参数
// 入参: options 内容参数，nil采用默认值
// 返回: ContentOptions 独立参数, error 非法参数错误
func contentConfiguration(options *ContentOptions) (ContentOptions, error) {
	configuration := DefaultContentOptions()
	if options != nil {
		configuration.Order = options.Order
		configuration.ResolveGlyphs = options.ResolveGlyphs
		if options.Limits.MaxBytes != 0 {
			configuration.Limits.MaxBytes = options.Limits.MaxBytes
		}
		if options.Limits.MaxNodes != 0 {
			configuration.Limits.MaxNodes = options.Limits.MaxNodes
		}
		if options.Limits.MaxWork != 0 {
			configuration.Limits.MaxWork = options.Limits.MaxWork
		}
		if options.Limits.MaxGlyphs != 0 {
			configuration.Limits.MaxGlyphs = options.Limits.MaxGlyphs
		}
		if options.Limits.MaxFonts != 0 {
			configuration.Limits.MaxFonts = options.Limits.MaxFonts
		}
	}
	if configuration.Order != ReadingPage && configuration.Order != ReadingStory || configuration.Limits.MaxBytes < 1 || configuration.Limits.MaxNodes < 1 || configuration.Limits.MaxGlyphs < 1 || configuration.Limits.MaxFonts < 1 {
		return ContentOptions{}, fmt.Errorf("%w: content options", ErrInvalid)
	}
	return configuration, nil
}

// charge 检查取消并扣除整次处理的关联及遍历工作预算
// 入参: count 待处理的操作数量
// 返回: error 取消或预算不足错误
func (g *contentGraph) charge(count uint64) error {
	if err := checkContext(g.context); err != nil {
		return err
	}
	if count > g.work {
		return fmt.Errorf("%w: content work budget", ErrLimit)
	}
	g.work -= count
	return nil
}

// node 扣除索引、绑定或输出节点预算，不把多次引用展开视为免费操作
// 返回: error 取消或节点预算不足错误
func (g *contentGraph) node() error {
	if err := g.charge(1); err != nil {
		return err
	}
	if g.nodes == 0 {
		return fmt.Errorf("%w: content node budget", ErrLimit)
	}
	g.nodes--
	return nil
}

// readAllowance 在解压前计入每次逻辑部件读取，并将实际解压上限收紧到已计费的声明尺寸
// 入参: key 逻辑部件键, size 声明解压量, limit 原读取上限
// 返回: int64 实际读取上限, error 取消或字节预算错误
func (g *contentGraph) readAllowance(key string, size uint64, limit int64) (int64, error) {
	if err := g.charge(1); err != nil {
		return 0, err
	}
	if size > uint64(g.bytes) {
		return 0, fmt.Errorf("%w: content part %s exceeds byte budget", ErrLimit, key)
	}
	g.bytes -= int64(size)
	return min(limit, int64(size)), nil
}

// positionGlyphs 为实际阅读条目解析字形位置，共用渲染字体后端但不绘制或导出字体程序
// 返回: error 字体、定位、资源或取消错误
func (g *contentGraph) positionGlyphs() error {
	fonts := fontCache{pkg: g.reader.pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: g.options.Limits.MaxBytes, maxFaces: g.options.Limits.MaxFonts}
	for index := range g.result.Items {
		if err := g.charge(1); err != nil {
			return err
		}
		item := &g.result.Items[index]
		glyphs, ok := item.Element.(*Glyphs)
		if !ok {
			continue
		}
		count, err := glyphRunCount(glyphs, min(g.glyphs, g.nodes))
		if err != nil {
			return &PartError{Part: item.Part, Element: "Glyphs", Err: err}
		}
		font, err := fonts.load(glyphs)
		if err != nil {
			return err
		}
		run, err := resolveGlyphRunWithStep(glyphs, font.metrics, font.glyphIndex, font.glyphYMax, count, func() error { return g.charge(1) })
		if err != nil {
			return &PartError{Part: item.Part, Element: "Glyphs", Err: err}
		}
		g.glyphs -= count
		positions := make([]GlyphPosition, 0, count)
		for _, glyph := range run.glyphs {
			if err := g.node(); err != nil {
				return err
			}
			position, err := contentGlyphPosition(glyph, item.Transform, run.rtl)
			if err != nil {
				return &PartError{Part: item.Part, Element: "Glyphs", Err: err}
			}
			positions = append(positions, position)
		}
		item.Glyphs = positions
	}
	return nil
}

// contentGlyphPosition 将局部定位结果映射到有效页面坐标，步进向量不通过巨大平移坐标相减求得
// 入参: glyph 已定位字形, transform 元素到页面的变换, rtl 是否从右向左行进
// 返回: GlyphPosition 页面坐标定位, error 数值范围错误
func contentGlyphPosition(glyph positionedGlyph, transform Matrix, rtl bool) (GlyphPosition, error) {
	advance := glyph.advance
	if rtl {
		advance = -advance
	}
	nominal, err := geometryFillPoint(transform, glyph.nominal)
	if err != nil {
		return GlyphPosition{}, err
	}
	origin, err := geometryFillPoint(transform, glyph.origin)
	if err != nil {
		return GlyphPosition{}, err
	}
	position := GlyphPosition{Index: glyph.gid, Cluster: glyph.cluster, TextStart: glyph.clusterStart, TextEnd: glyph.clusterEnd, ExplicitIndex: glyph.explicitIndex, ExplicitAdvance: glyph.explicitAdvance, Nominal: nominal, Origin: origin, Advance: Point{X: transform.A * advance, Y: transform.B * advance}, Transform: strokePathCompose(transform, glyph.matrix)}
	if !geometryFinite(position.Nominal.X, position.Nominal.Y, position.Origin.X, position.Origin.Y, position.Advance.X, position.Advance.Y) || !geometryFillMatrixFinite(position.Transform) {
		return GlyphPosition{}, fmt.Errorf("%w: content glyph position range", ErrLimit)
	}
	return position, nil
}

// EscapeUnicodeString 为纯文本补齐XPS/OpenXPS规定的前导{}转义以生成UnicodeString原始属性值
// 以左花括号开头的文本添加前导{}转义，其余文本原样返回
// 入参: text 纯文本
// 返回: string XML原始UnicodeString属性值
func EscapeUnicodeString(text string) string {
	if strings.HasPrefix(text, "{") {
		return "{}" + text
	}
	return text
}

// UnescapeUnicodeString 校验并去除XML原始UnicodeString属性的前导{}转义
// 若输入为非法UTF-8或以左花括号开头但缺少前导{}转义则返回ErrInvalid
// 入参: rawUnicodeString XML解码后尚未去除前导{}转义的原始UnicodeString属性值
// 返回: string 去除前导{}转义后的纯文本, error 编码或转义错误
func UnescapeUnicodeString(rawUnicodeString string) (string, error) {
	if !utf8.ValidString(rawUnicodeString) {
		return "", fmt.Errorf("%w: invalid UnicodeString UTF-8", ErrInvalid)
	}
	if strings.HasPrefix(rawUnicodeString, "{}") {
		return rawUnicodeString[2:], nil
	}
	if strings.HasPrefix(rawUnicodeString, "{") {
		return "", fmt.Errorf("%w: UnicodeString requires a leading {} escape", ErrInvalid)
	}
	return rawUnicodeString, nil
}

// ParseCaretStops 解析逻辑光标停靠位置，要求传入尚未去除{}转义的原始UnicodeString属性值
// 返回长度为去转义后UTF-16单元数加一，空串及未覆盖位置默认为true，多余位或非零填充位返回错误
// 入参: text CaretStops属性文本，缺省传空串, rawUnicodeString 尚未去除{}前缀的原始UnicodeString属性值
// 返回: []bool 逻辑光标停靠标志, error 词法或长度错误
func ParseCaretStops(text, rawUnicodeString string) ([]bool, error) {
	unicodeString, err := UnescapeUnicodeString(rawUnicodeString)
	if err != nil {
		return nil, err
	}
	count := 0
	for _, r := range unicodeString {
		count++
		if r > 0xffff {
			count++
		}
	}
	if count == int(^uint(0)>>1) {
		return nil, fmt.Errorf("%w: caret position count exceeds int range", ErrLimit)
	}
	count++
	text = strings.Trim(text, " \t\r\n")
	digits := count / 4
	if count%4 != 0 {
		digits++
	}
	if len(text) > digits {
		return nil, fmt.Errorf("%w: CaretStops exceeds UnicodeString UTF-16 length plus one", ErrInvalid)
	}
	for i := range len(text) {
		n, ok := caretHexDigit(text[i])
		if !ok {
			return nil, fmt.Errorf("%w: CaretStops contains a non-hexadecimal byte at %d", ErrInvalid, i)
		}
		if i == digits-1 && count%4 != 0 && n&byte((1<<uint(4-count%4))-1) != 0 {
			return nil, fmt.Errorf("%w: CaretStops has nonzero trailing padding bits", ErrInvalid)
		}
	}
	stops := make([]bool, count)
	for i := range stops {
		if i/4 >= len(text) {
			stops[i] = true
		} else {
			n, _ := caretHexDigit(text[i/4])
			stops[i] = n&(8>>uint(i%4)) != 0
		}
	}
	return stops, nil
}

// caretHexDigit 解析单个ASCII十六进制数字
// 入参: c 待解析字节
// 返回: byte 四位数值, bool 是否为合法数字
func caretHexDigit(c byte) (byte, bool) {
	n := opcHex(c)
	if n < 0 {
		return 0, false
	}
	return byte(n), true
}

// element 标记画布为绘制元素
func (*Canvas) element() {}

// element 标记路径为绘制元素
func (*Path) element() {}

// element 标记字形序列为绘制元素
func (*Glyphs) element() {}

// readingOrder 采用明确选择的页面或故事顺序，并按标记顺序追加所有尚未引用的页面内容
// 返回: error 名称索引或资源错误
func (g *contentGraph) readingOrder() error {
	if g.options.Order == ReadingStory {
		for _, story := range g.result.Stories {
			for _, fragment := range story.Fragments {
				if err := g.emitContent(fragment.Content, fragment, 0); err != nil {
					return err
				}
			}
		}
	} else {
		for _, page := range g.pages {
			for _, fragment := range page.fragments {
				if err := g.emitContent(fragment.Content, fragment, 0); err != nil {
					return err
				}
			}
			if err := g.emitUnreferenced(page); err != nil {
				return err
			}
		}
		return nil
	}
	for _, page := range g.pages {
		if err := g.emitUnreferenced(page); err != nil {
			return err
		}
	}
	return nil
}

// emitContent 按语义树声明顺序输出列表标记和命名元素，重复的作者引用保留为重复内容
// 入参: nodes 绑定节点, fragment 来源片段, depth 当前深度
// 返回: error 引用、深度或资源错误
func (g *contentGraph) emitContent(nodes []ContentNode, fragment ContentFragment, depth int) error {
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: reading order depth", ErrLimit)
	}
	for _, node := range nodes {
		if err := g.charge(1); err != nil {
			return err
		}
		for _, references := range [][]ContentReference{node.Markers, node.References} {
			for _, reference := range references {
				if err := g.emitReference(reference, fragment); err != nil {
					return err
				}
			}
		}
		if len(node.Children) != 0 {
			if err := g.emitContent(node.Children, fragment, depth+1); err != nil {
				return err
			}
		}
	}
	return nil
}

// emitReference 展开命名画布的标记顺序子内容，已输出标记只用于未引用内容的追加，不消除显式重复引用
// 入参: reference 已绑定引用, fragment 来源片段
// 返回: error 预算或取消错误
func (g *contentGraph) emitReference(reference ContentReference, fragment ContentFragment) error {
	page := g.pages[reference.Page-g.pages[0].number]
	span := page.names[reference.Name]
	for index := span.first; index < span.last; index++ {
		if err := g.node(); err != nil {
			return err
		}
		item := page.items[index]
		item.StoryName, item.FragmentName, item.FragmentType = fragment.StoryName, fragment.FragmentName, fragment.Type
		g.result.Items = append(g.result.Items, item)
		page.seen[index] = true
	}
	return nil
}

// emitUnreferenced 按页内标记顺序追加未被作者引用覆盖的元素，不因缺少结构标记丢弃内容
// 入参: page 页面索引
// 返回: error 资源或取消错误
func (g *contentGraph) emitUnreferenced(page *contentPage) error {
	for index, item := range page.items {
		if err := g.charge(1); err != nil {
			return err
		}
		if !page.seen[index] {
			if err := g.node(); err != nil {
				return err
			}
			g.result.Items = append(g.result.Items, item)
			page.seen[index] = true
		}
	}
	return nil
}

// Text 按指定阅读顺序连接Glyphs声明的Unicode文字，跳过合法省略UnicodeString的字形元素
// 入参: ctx 取消Context，nil采用Background, docIndex 零基固定文档序号, options 内容参数，nil采用默认值
// 返回: string 完整声明文字，失败时为空字符串, error 读取、预算或取消错误
func (r *Reader) Text(ctx context.Context, docIndex int, options *ContentOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return "", err
	}
	defer r.mu.RUnlock()
	configuration, err := contentConfiguration(options)
	if err != nil {
		return "", err
	}
	configuration.ResolveGlyphs = false
	content, err := r.readContent(ctx, docIndex, configuration)
	if err != nil {
		return "", err
	}
	var text strings.Builder
	remaining := configuration.Limits.MaxBytes
	for _, item := range content.Items {
		if err := checkContext(ctx); err != nil {
			return "", err
		}
		if glyphs, ok := item.Element.(*Glyphs); ok {
			if _, present := glyphs.source.attribute("UnicodeString"); !present {
				continue
			}
			if int64(len(glyphs.Text)) > remaining || len(glyphs.Text) > int(^uint(0)>>1)-text.Len() {
				return "", fmt.Errorf("%w: content text byte budget", ErrLimit)
			}
			remaining -= int64(len(glyphs.Text))
			text.WriteString(glyphs.Text)
		}
	}
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	return text.String(), nil
}

// loadPage 读取完整页面和片段并建立独立内容索引，不用几何位置重排文字
// 入参: number 全局零基页号
// 返回: error 页面、索引或片段绑定错误
func (g *contentGraph) loadPage(number int) error {
	if err := g.node(); err != nil {
		return err
	}
	page, err := g.reader.readPageSceneLoaders(number, true, nil, nil, g.context)
	if err != nil {
		return err
	}
	index := &contentPage{page: page, number: number, names: make(map[string]contentRange), extras: make(map[string]contentSource)}
	for _, element := range page.Elements {
		if err := g.indexElement(index, element, IdentityMatrix(), page.Language, nil, false, 0); err != nil {
			return err
		}
	}
	if page.Name != "" {
		index.names[page.Name] = contentRange{0, len(index.items)}
	}
	if err := g.indexSources(index, page.root, IdentityMatrix(), page.Language, nil, false, 0); err != nil {
		return err
	}
	fragments, err := g.reader.readStoryFragmentsContext(g.context, number)
	if err != nil {
		return err
	}
	if fragments != nil {
		for _, fragment := range fragments.Fragments {
			content, err := g.bindContent(index, fragment.Content, 0)
			if err != nil {
				return &PartError{Part: fragments.Part, Element: "StoryFragment", Err: err}
			}
			index.fragments = append(index.fragments, ContentFragment{Page: number, Part: fragments.Part, StoryName: fragment.StoryName, FragmentName: fragment.FragmentName, Type: fragment.Type, BreakBefore: fragment.BreakBefore, BreakAfter: fragment.BreakAfter, Content: content})
		}
	}
	index.seen = make([]bool, len(index.items))
	g.pages = append(g.pages, index)
	g.result.Pages = append(g.result.Pages, ContentPage{Page: number, Part: page.Part, Fragments: index.fragments})
	g.result.Diagnostics = append(g.result.Diagnostics, page.Diagnostics...)
	return nil
}

// indexElement 保存绘制元素的有效语言、链接和变换，画布及其子元素保持声明顺序
// 入参: page 页面索引, element 绘制元素, transform 祖先变换, language 有效语言, link 祖先链接, visual 是否为视觉源, depth 当前深度
// 返回: error 上限、变换或元素错误
func (g *contentGraph) indexElement(page *contentPage, element Element, transform Matrix, language string, link *string, visual bool, depth int) error {
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: content visual depth", ErrLimit)
	}
	if err := g.node(); err != nil {
		return err
	}
	properties := contentProperties(element)
	if properties == nil {
		return fmt.Errorf("%w: content visual element", ErrInvalid)
	}
	if properties.RenderTransform != nil {
		transform = strokePathCompose(transform, *properties.RenderTransform)
		if !geometryFillMatrixFinite(transform) {
			return fmt.Errorf("%w: content transform range", ErrLimit)
		}
	}
	if properties.Language != nil {
		language = *properties.Language
	}
	if properties.NavigateURI != nil {
		link = properties.NavigateURI
	}
	start := len(page.items)
	page.items = append(page.items, ContentItem{Page: page.number, Part: page.page.Part, Element: element, Transform: transform, Language: language, NavigateURI: link, VisualSource: visual})
	if canvas, ok := element.(*Canvas); ok {
		for _, child := range canvas.Elements {
			if err := g.indexElement(page, child, transform, language, link, visual, depth+1); err != nil {
				return err
			}
		}
	}
	rangeValue := contentRange{start, len(page.items)}
	if properties.Name != "" && strings.EqualFold(properties.Part, page.page.Part) {
		page.names[properties.Name] = rangeValue
	}
	return nil
}

// indexSources 为作者可能引用的页内视觉源建立一次性名称索引，避免每个引用重新扫描整个视觉图
// 入参: page 页面索引, node 原始页内节点, transform 祖先变换, language 有效语言, link 祖先链接, visual 是否为定义源, depth 当前深度
// 返回: error 取消、深度、变换或预算错误
func (g *contentGraph) indexSources(page *contentPage, node *xmlElement, transform Matrix, language string, link *string, visual bool, depth int) error {
	if err := g.charge(1); err != nil {
		return err
	}
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: content source depth", ErrLimit)
	}
	if node.Name.Local == "ResourceDictionary" || node.Name.Local == "VisualBrush.Visual" {
		transform, link, visual = IdentityMatrix(), nil, true
	}
	if element := page.page.visuals[node]; element != nil {
		properties := contentProperties(element)
		if properties != nil {
			if visual && properties.Name != "" && strings.EqualFold(properties.Part, page.page.Part) {
				if err := g.node(); err != nil {
					return err
				}
				page.extras[properties.Name] = contentSource{element, transform, language, link}
			}
			if properties.RenderTransform != nil {
				transform = strokePathCompose(transform, *properties.RenderTransform)
				if !geometryFillMatrixFinite(transform) {
					return fmt.Errorf("%w: content source transform range", ErrLimit)
				}
			}
			if properties.Language != nil {
				language = *properties.Language
			}
			if properties.NavigateURI != nil {
				link = properties.NavigateURI
			}
		}
	}
	for _, child := range node.Children {
		if err := g.indexSources(page, child, transform, language, link, visual, depth+1); err != nil {
			return err
		}
	}
	return nil
}

// contentProperties 返回绘制元素的局部属性指针
// 入参: element 绘制元素
// 返回: *ElementProperties 局部属性，未知或空元素返回nil
func contentProperties(element Element) *ElementProperties {
	switch element := element.(type) {
	case *Canvas:
		if element != nil {
			return &element.ElementProperties
		}
	case *Path:
		if element != nil {
			return &element.ElementProperties
		}
	case *Glyphs:
		if element != nil {
			return &element.ElementProperties
		}
	}
	return nil
}

// reference 绑定本页名称，显式引用视觉画刷子内容时保留该合法但不推荐的来源
// 入参: page 页面索引, name 规范化名称
// 返回: ContentReference 绑定目标, error 缺少目标或索引错误
func (g *contentGraph) reference(page *contentPage, name string) (ContentReference, error) {
	if err := g.charge(1); err != nil {
		return ContentReference{}, err
	}
	if _, exists := page.names[name]; !exists {
		source, exists := page.extras[name]
		if !exists {
			return ContentReference{}, fmt.Errorf("%w: named element %q is absent from page %s", ErrInvalid, name, page.page.Part)
		}
		if err := g.indexElement(page, source.element, source.transform, source.language, source.link, true, 0); err != nil {
			return ContentReference{}, err
		}
		g.result.Diagnostics = append(g.result.Diagnostics, Diagnostic{Part: page.page.Part, Element: "NamedElement", Attribute: "NameReference", Message: "document structure explicitly references visual-brush content"})
	}
	return ContentReference{Page: page.number, Part: page.page.Part, Name: name}, nil
}

// bindContent 将语义树中的命名元素和标记绑定到真实页面，保留空单元格及原始节点顺序
// 入参: page 页面索引, source 原始语义节点, depth 当前深度
// 返回: []ContentNode 独立绑定节点, error 名称、深度或预算错误
func (g *contentGraph) bindContent(page *contentPage, source []ContentStructure, depth int) ([]ContentNode, error) {
	if depth >= g.reader.limits.MaxXMLDepth {
		return nil, fmt.Errorf("%w: bound content depth", ErrLimit)
	}
	var result []ContentNode
	for _, node := range source {
		if err := g.node(); err != nil {
			return nil, err
		}
		value := ContentNode{Kind: node.Kind, RowSpan: node.RowSpan, ColumnSpan: node.ColumnSpan, Segments: []ContentSegment{{Page: page.number, RowSpan: node.RowSpan, ColumnSpan: node.ColumnSpan}}}
		if node.Kind == StructureNamedElement {
			reference, err := g.reference(page, node.NameReference)
			if err != nil {
				return nil, err
			}
			value.References = []ContentReference{reference}
		}
		if node.Marker != nil {
			reference, err := g.reference(page, *node.Marker)
			if err != nil {
				return nil, err
			}
			value.Markers = []ContentReference{reference}
		}
		if len(node.Children) != 0 {
			children, err := g.bindContent(page, node.Children, depth+1)
			if err != nil {
				return nil, err
			}
			value.Children = children
		}
		result = append(result, value)
	}
	return result, nil
}

// bindStories 按作者的片段引用顺序绑定故事，允许从后页返回前页的另一片段
// 返回: error 缺少、歧义或预算错误
func (g *contentGraph) bindStories() error {
	known := make(map[string]map[string]bool)
	if g.structure != nil {
		for _, story := range g.structure.Stories {
			if err := g.node(); err != nil {
				return err
			}
			known[story.Name] = nil
		}
	}
	locations := make(map[contentFragmentKey]*ContentFragment)
	for local, page := range g.pages {
		for index := range page.fragments {
			if err := g.node(); err != nil {
				return err
			}
			fragment := &page.fragments[index]
			if fragment.StoryName == nil {
				continue
			}
			fragmentNames, defined := known[*fragment.StoryName]
			if !defined {
				return &PartError{Part: fragment.Part, Element: "StoryFragment", Err: fmt.Errorf("%w: story %q is not defined in its fixed document", ErrInvalid, *fragment.StoryName)}
			}
			key := contentFragmentKey{page: local, story: *fragment.StoryName}
			if _, exists := locations[key]; exists {
				locations[key] = nil
			} else {
				locations[key] = fragment
			}
			if fragment.FragmentName != nil {
				key.named, key.name = true, *fragment.FragmentName
				if fragmentNames[key.name] {
					return &PartError{Part: fragment.Part, Element: "StoryFragment", Err: fmt.Errorf("%w: duplicate fragment name %q in story %q", ErrInvalid, key.name, key.story)}
				}
				if err := g.node(); err != nil {
					return err
				}
				if fragmentNames == nil {
					fragmentNames = make(map[string]bool)
					known[key.story] = fragmentNames
				}
				fragmentNames[key.name] = true
				locations[key] = fragment
			}
		}
	}
	if g.structure == nil {
		return nil
	}
	for _, story := range g.structure.Stories {
		if err := g.node(); err != nil {
			return err
		}
		result := ContentStory{Name: story.Name}
		previousBreak := true
		for _, reference := range story.Fragments {
			if err := g.node(); err != nil {
				return err
			}
			key := contentFragmentKey{page: reference.PageNumber - 1, story: story.Name}
			if reference.FragmentName != nil {
				key.named, key.name = true, *reference.FragmentName
			}
			candidate := locations[key]
			if candidate == nil {
				return &PartError{Part: g.structure.Part, Element: "StoryFragmentReference", Err: fmt.Errorf("%w: story %q page %d does not identify exactly one fragment", ErrInvalid, story.Name, reference.PageNumber)}
			}
			fragment := *candidate
			result.Fragments = append(result.Fragments, fragment)
			content, err := g.cloneContent(fragment.Content, 0)
			if err != nil {
				return err
			}
			if previousBreak || fragment.BreakBefore {
				result.Content = append(result.Content, content...)
			} else if err := g.mergeContent(&result.Content, content, 0); err != nil {
				return err
			}
			previousBreak = fragment.BreakAfter
		}
		g.result.Stories = append(g.result.Stories, result)
	}
	return nil
}

// cloneContent 为合并建立独占语义树，不修改页面片段或重用缓存中的子切片
// 入参: source 绑定节点, depth 当前深度
// 返回: []ContentNode 独立节点, error 深度或资源错误
func (g *contentGraph) cloneContent(source []ContentNode, depth int) ([]ContentNode, error) {
	if depth >= g.reader.limits.MaxXMLDepth {
		return nil, fmt.Errorf("%w: content copy depth", ErrLimit)
	}
	var result []ContentNode
	for _, node := range source {
		if err := g.node(); err != nil {
			return nil, err
		}
		value := node
		value.References = append([]ContentReference(nil), node.References...)
		value.Markers = append([]ContentReference(nil), node.Markers...)
		value.Segments = append([]ContentSegment(nil), node.Segments...)
		if len(node.Children) != 0 {
			children, err := g.cloneContent(node.Children, depth+1)
			if err != nil {
				return nil, err
			}
			value.Children = children
		}
		result = append(result, value)
	}
	return result, nil
}

// mergeContent 按首尾同名结构逐层续接，命名元素保持独立引用，不按页位置猜测边界
// 入参: previous 已独占的前段, next 已独占的后段, depth 当前深度
// 返回: error 续接深度或资源错误
func (g *contentGraph) mergeContent(previous *[]ContentNode, next []ContentNode, depth int) error {
	if err := g.charge(1); err != nil {
		return err
	}
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: content continuation depth", ErrLimit)
	}
	if len(*previous) == 0 || len(next) == 0 {
		*previous = append(*previous, next...)
		return nil
	}
	left := &(*previous)[len(*previous)-1]
	right := next[0]
	if left.Kind != right.Kind || left.Kind == StructureNamedElement {
		*previous = append(*previous, next...)
		return nil
	}
	if err := g.mergeNode(left, right, depth); err != nil {
		return err
	}
	*previous = append(*previous, next[1:]...)
	return nil
}

// mergeNode 续接匹配的语义节点并保留各段原始属性，表格行按单元格位置对应合并
// 入参: left 独占的前节点, right 独占的后节点, depth 当前深度
// 返回: error 深度或资源错误
func (g *contentGraph) mergeNode(left *ContentNode, right ContentNode, depth int) error {
	if err := g.charge(1); err != nil {
		return err
	}
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: content node continuation depth", ErrLimit)
	}
	left.Segments = append(left.Segments, right.Segments...)
	left.Markers = append(left.Markers, right.Markers...)
	if left.Kind == StructureCell && (left.RowSpan != right.RowSpan || left.ColumnSpan != right.ColumnSpan) {
		g.result.Diagnostics = append(g.result.Diagnostics, Diagnostic{Element: "TableCellStructure", Message: "continuing cell spans differ; per-fragment attributes retained"})
	}
	if left.Kind != StructureRow {
		return g.mergeContent(&left.Children, right.Children, depth+1)
	}
	if len(left.Children) != len(right.Children) {
		g.result.Diagnostics = append(g.result.Diagnostics, Diagnostic{Element: "TableRowStructure", Message: "continuing row cell counts differ; unmatched cells retained"})
	}
	for index := 0; index < min(len(left.Children), len(right.Children)); index++ {
		if err := g.mergeNode(&left.Children[index], right.Children[index], depth+1); err != nil {
			return err
		}
	}
	if len(right.Children) > len(left.Children) {
		left.Children = append(left.Children, right.Children[len(left.Children):]...)
	}
	return nil
}

// ParseGlyphIndices 解析Indices字形索引与度量属性，不执行字体查询或排版
// CodeUnitCount按UTF-16单元计数，省略的索引和字宽需由字体补齐，省略的偏移默认为零
// 入参: text XML解码后的属性值
// 返回: []GlyphCluster 字形簇切片，空属性返回nil, error 语法、范围或簇结构错误
func ParseGlyphIndices(text string) ([]GlyphCluster, error) {
	text = strings.Trim(text, " \t\r\n")
	if text == "" {
		return nil, nil
	}
	entries := strings.Count(text, ";") + 1
	var clusters []GlyphCluster
	for i := 0; i < entries; {
		entry, remaining, _ := strings.Cut(text, ";")
		text = remaining
		cluster := GlyphCluster{CodeUnitCount: 1}
		count := 1
		if strings.HasPrefix(entry, "(") {
			end := strings.IndexByte(entry, ')')
			if end < 0 {
				return nil, fmt.Errorf("%w: glyph entry %d: unclosed cluster mapping", ErrInvalid, i)
			}
			units, glyphs, hasCount := strings.Cut(entry[1:end], ":")
			var err error
			cluster.CodeUnitCount, err = parseGlyphClusterCount(units)
			if err != nil {
				return nil, fmt.Errorf("glyph entry %d: code unit count: %w", i, err)
			}
			if hasCount {
				count, err = parseGlyphClusterCount(glyphs)
				if err != nil {
					return nil, fmt.Errorf("glyph entry %d: glyph count: %w", i, err)
				}
			}
			cluster.HasMapping = true
			cluster.HasGlyphCount = hasCount
			entry = entry[end+1:]
		}
		if count > entries-i {
			return nil, fmt.Errorf("%w: glyph entry %d: incomplete cluster of %d glyphs", ErrInvalid, i, count)
		}
		cluster.Glyphs = make([]GlyphIndex, 0, count)
		for j := 0; j < count; j++ {
			if j > 0 {
				entry, remaining, _ = strings.Cut(text, ";")
				text = remaining
			}
			glyph, err := parseGlyphIndex(entry)
			if err != nil {
				return nil, fmt.Errorf("glyph entry %d: %w", i+j, err)
			}
			if !glyph.HasIndex && count > 1 {
				return nil, fmt.Errorf("%w: glyph entry %d: explicit cluster requires a glyph index", ErrInvalid, i+j)
			}
			cluster.Glyphs = append(cluster.Glyphs, glyph)
		}
		clusters = append(clusters, cluster)
		i += count
	}
	return clusters, nil
}

// ValidateGlyphIndices 校验字形簇与原始UnicodeString属性的UTF-16映射，要求传入尚未去除{}转义的原文
// 校验代理对边界与补充平面显式映射，允许未覆盖的BMP尾部，不检查字体cmap
// 入参: clusters 字形簇切片, rawUnicodeString 尚未去除{}前缀的原始UnicodeString属性值
// 返回: error 结构或映射错误
func ValidateGlyphIndices(clusters []GlyphCluster, rawUnicodeString string) error {
	unicodeString, err := UnescapeUnicodeString(rawUnicodeString)
	if err != nil {
		return err
	}
	if unicodeString == "" && len(clusters) == 0 {
		return fmt.Errorf("%w: neither UnicodeString nor glyph indices are present", ErrInvalid)
	}
	remaining := unicodeString
	for i, cluster := range clusters {
		if cluster.CodeUnitCount <= 0 || len(cluster.Glyphs) == 0 {
			return fmt.Errorf("%w: cluster %d: counts must be positive", ErrInvalid, i)
		}
		if !cluster.HasMapping && (cluster.CodeUnitCount != 1 || len(cluster.Glyphs) != 1 || cluster.HasGlyphCount) {
			return fmt.Errorf("%w: cluster %d: missing cluster mapping", ErrInvalid, i)
		}
		if !cluster.HasGlyphCount && len(cluster.Glyphs) != 1 {
			return fmt.Errorf("%w: cluster %d: missing explicit glyph count", ErrInvalid, i)
		}
		for _, glyph := range cluster.Glyphs {
			if !glyph.HasIndex && (unicodeString == "" || len(cluster.Glyphs) != 1) {
				return fmt.Errorf("%w: cluster %d: glyph index cannot be inferred", ErrInvalid, i)
			}
			if glyph.HasAdvanceWidth && (!geometryFinite(glyph.AdvanceWidth) || glyph.AdvanceWidth < 0) {
				return fmt.Errorf("%w: cluster %d: invalid advance width", ErrInvalid, i)
			}
			if glyph.HasUOffset && !geometryFinite(glyph.UOffset) || glyph.HasVOffset && !geometryFinite(glyph.VOffset) {
				return fmt.Errorf("%w: cluster %d: invalid offset", ErrInvalid, i)
			}
		}
		if unicodeString == "" {
			continue
		}
		scalars := 0
		for units := cluster.CodeUnitCount; units > 0; {
			if remaining == "" {
				return fmt.Errorf("%w: cluster %d: exceeds UnicodeString UTF-16 length", ErrInvalid, i)
			}
			r, size := utf8.DecodeRuneInString(remaining)
			width := 1
			if r > 0xffff {
				width = 2
				if !cluster.HasMapping || units < width {
					return fmt.Errorf("%w: cluster %d: surrogate pair requires an unsplit explicit mapping", ErrInvalid, i)
				}
			}
			units -= width
			remaining = remaining[size:]
			scalars++
		}
		if len(cluster.Glyphs) == 1 && !cluster.Glyphs[0].HasIndex && scalars != 1 {
			return fmt.Errorf("%w: cluster %d: glyph index cannot be inferred", ErrInvalid, i)
		}
	}
	for _, r := range remaining {
		if r > 0xffff {
			return fmt.Errorf("%w: supplementary Unicode character requires an explicit cluster mapping", ErrInvalid)
		}
	}
	return nil
}

// parseGlyphClusterCount 读取ST_Indices的正整数计数
// 入参: text 不含前导零的十进制计数
// 返回: int 正整数, error 错误信息
func parseGlyphClusterCount(text string) (int, error) {
	if !glyphDecimalDigits(text) || text[0] == '0' {
		return 0, fmt.Errorf("%w: invalid positive decimal count %q", ErrInvalid, text)
	}
	n, err := strconv.ParseUint(text, 10, strconv.IntSize-1)
	if err != nil {
		return 0, fmt.Errorf("%w: cluster count out of range: %w", ErrInvalid, err)
	}
	return int(n), nil
}

// parseGlyphIndex 解析去除簇前缀后的单个字形条目
// 入参: text 索引及最多三个逗号分隔的度量
// 返回: GlyphIndex 保留省略状态的条目, error 错误信息
func parseGlyphIndex(text string) (GlyphIndex, error) {
	var glyph GlyphIndex
	var fields [4]string
	n := 0
	for {
		field, remaining, more := strings.Cut(text, ",")
		fields[n] = field
		n++
		if !more {
			break
		}
		if n == len(fields) {
			return glyph, fmt.Errorf("%w: too many glyph metric fields", ErrInvalid)
		}
		text = remaining
	}
	if fields[0] != "" {
		if !glyphDecimalDigits(fields[0]) {
			return glyph, fmt.Errorf("%w: invalid glyph index %q", ErrInvalid, fields[0])
		}
		index, err := strconv.ParseUint(fields[0], 10, 16)
		if err != nil {
			return glyph, fmt.Errorf("%w: glyph index out of range: %w", ErrInvalid, err)
		}
		glyph.Index = uint16(index)
		glyph.HasIndex = true
	}
	values := []*float64{&glyph.AdvanceWidth, &glyph.UOffset, &glyph.VOffset}
	flags := []*bool{&glyph.HasAdvanceWidth, &glyph.HasUOffset, &glyph.HasVOffset}
	for i, field := range fields[1:n] {
		if field == "" {
			if i == 2 {
				return glyph, fmt.Errorf("%w: vOffset cannot be empty after its comma", ErrInvalid)
			}
			continue
		}
		if !glyphMetricSyntax(field) || i == 0 && field[0] == '-' {
			return glyph, fmt.Errorf("%w: invalid glyph metric %q", ErrInvalid, field)
		}
		value, err := strconv.ParseFloat(field, 64)
		if err != nil || !geometryFinite(value) {
			return glyph, fmt.Errorf("%w: glyph metric out of range %q", ErrInvalid, field)
		}
		*values[i] = value
		*flags[i] = true
	}
	return glyph, nil
}

// glyphMetricSyntax 校验ST_Indices中度量的十进制及指数词法
// 入参: text 不含空白的度量字段
// 返回: bool 是否符合带可选符号的度量词法
func glyphMetricSyntax(text string) bool {
	if len(text) > 0 && (text[0] == '+' || text[0] == '-') {
		text = text[1:]
	}
	i := 0
	for i < len(text) && text[i] >= '0' && text[i] <= '9' {
		i++
	}
	if i < len(text) && text[i] == '.' {
		start := i + 1
		i = start
		for i < len(text) && text[i] >= '0' && text[i] <= '9' {
			i++
		}
		if i == start {
			return false
		}
	} else if i == 0 {
		return false
	}
	if i == len(text) {
		return true
	}
	if text[i] != 'e' && text[i] != 'E' {
		return false
	}
	text = text[i+1:]
	if len(text) > 0 && (text[0] == '+' || text[0] == '-') {
		text = text[1:]
	}
	return glyphDecimalDigits(text)
}

// glyphDecimalDigits 检查非空ASCII十进制数字串
// 入参: text 待检查文本
// 返回: bool 是否全部为十进制数字
func glyphDecimalDigits(text string) bool {
	return linkPageNumber(text)
}
