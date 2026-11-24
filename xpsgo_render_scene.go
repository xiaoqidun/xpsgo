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
	"image"
	"image/color"
	"math"
	"math/bits"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"unicode/utf8"
)

// sceneTileSize 等常量定义场景光栅化图块边长、嵌套深度与复用池像素上限
const (
	sceneTileSize       = 32
	sceneScratchPoolMax = 32 * 8 * 32 * 8
	sceneMaxDepth       = 1024
)

// sceneWorkerPool 复用场景多核光栅化工作Goroutine的临时图块缓冲
var sceneWorkerPool sync.Pool

// sceneParser 将资源图中的已绑定定义解析为页面绘制数据
type sceneParser struct {
	format     Format
	resources  *resourceGraph
	geometries map[*xmlElement]*Geometry
	matrices   map[*xmlElement]Matrix
	brushes    map[*xmlElement]*Brush
	elements   map[*xmlElement]Element
	budget     *printSideGeometryBudget
}

// sceneRenderOptions 保存内部场景绘制器的采样精度、合成空间与资源预算
type sceneRenderOptions struct {
	samples       int
	tolerance     float64
	space         renderColorSpace
	pixels        int
	elements      int
	edges         int
	work          uint64
	glyphs        int
	fonts         int
	fontBytes     int64
	format        Format
	font          func(*Glyphs) (*fontSource, error)
	images        int
	imagePixels   uint64
	imageBytes    int64
	image         func(*Brush) (*rasterImage, error)
	profiles      int
	profileBytes  int64
	color         func(string, Color) (Color, error)
	context       context.Context
	background    renderColor
	negative      map[*Canvas]bool
	outputColor   PrintColorMode
	bitmapDensity *Matrix
	device        *deviceRenderState
	printPlan     map[*Canvas]*PrintColorPlan
	printOptions  *PrintColorOptions
	printProfiles *sceneColorCache
	printSide     bool
	workers       int
	hdrPeakNits   float64
	pageSubClip   *image.Rectangle
}

// sceneSample 同时接收当前覆盖采样点和所属设备像素中心，保持嵌套图块的采样相位
type sceneSample func(point, center Point) (renderColor, error)

// sceneSampleCached 使用工作Goroutine独占缓存执行并发安全画刷采样
type sceneSampleCached func(point, center Point, cache *imageSampleCache) (renderColor, error)

// sceneBrushMeta 记录最近构造画刷的快速路径与并发特性
type sceneBrushMeta struct {
	solid        bool
	solidColor   renderColor
	gradient     *gradientSampler
	image        *imageSampler
	visual       bool
	sampleCached sceneSampleCached
}

// scenePaint 保存设备空间绘制区域及包含画刷透明度的颜色采样器
type scenePaint struct {
	regions      []rasterRegion
	regionBounds []image.Rectangle
	bounds       image.Rectangle
	sample       sceneSample
	sampleCached sceneSampleCached
	aliased      bool
	native       printNativeSample
	solid        bool
	solidColor   renderColor
	gradient     *gradientSampler
	image        *imageSampler
	visual       bool
}

// sceneNode 保存已解析局部绘制状态的隔离合成节点，不引用可变的源几何
type sceneNode struct {
	part         string
	kind         string
	bounds       image.Rectangle
	opacity      float64
	aliased      bool
	mask         sceneSample
	maskCached   sceneSampleCached
	maskVisual   bool
	maskGradient *gradientSampler
	maskImage    *imageSampler
	clip         *rasterRegion
	paints       []scenePaint
	children     []*sceneNode
	negative     bool
	color        *printColorRuntime
	nativeMask   printNativeSample
}

// sceneWorkerState 保存单个工作Goroutine独占的可复用扫描线、掩模及隔离表面缓冲
type sceneWorkerState struct {
	raster        rasterScratch
	regions       []rasterRegion
	mask          image.Alpha
	coarse        image.Alpha
	part          image.Alpha
	clip          image.Alpha
	imageCache    imageSampleCache
	isolated      []*renderSurface
	printIsolated []*printSurfaceBuffer
}

// sceneRenderer 保存一次绘制的独立状态及共享预算
type sceneRenderer struct {
	options        sceneRenderOptions
	active         map[Element]bool
	elements       int
	edges          int
	work           uint64
	live           int
	glyphs         int
	exact          int
	printRuntime   *printColorRuntime
	nativeSample   printNativeSample
	printContext   map[*Canvas]*printColorRuntime
	printSideSpace *printWorkingSpace
	brushMeta      sceneBrushMeta
	visualCount    int
	hasFiltered    bool
	concurrent     bool
	cancelled      atomic.Bool
	budgetMu       sync.Mutex
	visualMu       sync.Mutex
	cleanups       []func()
}

// newSceneParser 创建独立页面的绘制数据解析器
// 入参: format 文档格式, resources 已完成引用绑定的资源图
// 返回: *sceneParser 页面解析器
func newSceneParser(format Format, resources *resourceGraph) *sceneParser {
	return &sceneParser{format: format, resources: resources, geometries: make(map[*xmlElement]*Geometry), matrices: make(map[*xmlElement]Matrix), brushes: make(map[*xmlElement]*Brush), elements: make(map[*xmlElement]Element)}
}

// parse 按依赖顺序解析资源定义，再读取页面绘制元素
// 入参: root 页面根元素
// 返回: []Element 绘制元素, error 错误信息
func (p *sceneParser) parse(root *xmlElement) ([]Element, error) {
	for _, definition := range p.resources.Definitions {
		switch resourceKind(definition.Kind) {
		case "geometry":
			if _, err := p.geometry(definition.Element, true); err != nil {
				return nil, err
			}
		case "matrix":
			if _, err := p.matrix(definition.Element, true); err != nil {
				return nil, err
			}
		case "brush":
			if _, err := p.brush(definition.Element, true); err != nil {
				return nil, err
			}
		case "visual":
			if _, err := p.elementValue(definition.Element); err != nil {
				return nil, err
			}
		}
	}
	var elements []Element
	for _, child := range root.Children {
		if child.Name.Local == "FixedPage.Resources" {
			continue
		}
		value, err := p.elementValue(child)
		if err != nil {
			return nil, err
		}
		elements = append(elements, value)
	}
	return elements, nil
}

// elementValue 将绘制节点转换为保留局部属性的类型化元素
// 入参: node 绘制节点
// 返回: Element 绘制元素, error 错误信息
func (p *sceneParser) elementValue(node *xmlElement) (Element, error) {
	if value := p.elements[node]; value != nil {
		return value, nil
	}
	if err := p.budget.resource(node); err != nil {
		return nil, p.elementError(node, err)
	}
	if err := validateVisual(node, p.format); err != nil {
		return nil, p.elementError(node, err)
	}
	properties, err := p.elementProperties(node)
	if err != nil {
		return nil, err
	}
	var result Element
	switch node.Name.Local {
	case "Canvas":
		value := NewCanvas()
		value.ElementProperties = properties
		edgeMode, _ := node.attribute("RenderOptions.EdgeMode")
		value.EdgeMode = EdgeMode(edgeMode)
		value.AutomationName, _ = node.attribute("AutomationProperties.Name")
		value.AutomationHelpText, _ = node.attribute("AutomationProperties.HelpText")
		for _, child := range node.Children {
			if strings.HasPrefix(child.Name.Local, "Canvas.") {
				continue
			}
			element, err := p.elementValue(child)
			if err != nil {
				return nil, err
			}
			value.Elements = append(value.Elements, element)
		}
		result = value
	case "Path":
		result, err = p.pathValue(node, properties)
	case "Glyphs":
		result, err = p.glyphValue(node, properties)
	}
	if err != nil {
		return nil, err
	}
	p.elements[node] = result
	return result, nil
}

// elementProperties 读取绘制元素的公共局部属性，不合并祖先状态
// 入参: node 绘制节点
// 返回: ElementProperties 局部属性, error 错误信息
func (p *sceneParser) elementProperties(node *xmlElement) (ElementProperties, error) {
	value := ElementProperties{Part: p.resources.Parts[node], Opacity: 1, source: node}
	value.Name, _ = node.attribute("Name")
	if text, present := node.attributeNS(xmlNamespace, "lang"); present {
		text = strings.Trim(text, " \t\r\n")
		value.Language = &text
	}
	if text, present := node.attribute("FixedPage.NavigateUri"); present {
		value.NavigateURI = &text
	}
	if text, present := node.attribute("Opacity"); present {
		value.Opacity, _ = xmlNumber(text)
	}
	var err error
	value.RenderTransform, err = p.matrixProperty(node, "RenderTransform")
	if err != nil {
		return value, err
	}
	value.Clip, err = p.geometryProperty(node, "Clip")
	if err != nil {
		return value, err
	}
	value.OpacityMask, err = p.brushProperty(node, "OpacityMask")
	return value, err
}

// pathValue 读取已校验路径的填充、描边及缺省参数
// 入参: node 路径节点, properties 公共局部属性
// 返回: *Path 路径元素, error 错误信息
func (p *sceneParser) pathValue(node *xmlElement, properties ElementProperties) (*Path, error) {
	value := NewPath(nil)
	value.ElementProperties = properties
	var err error
	value.Data, err = p.geometryProperty(node, "Data")
	if err != nil {
		return nil, err
	}
	value.Fill, err = p.brushProperty(node, "Fill")
	if err != nil {
		return nil, err
	}
	value.Stroke, err = p.brushProperty(node, "Stroke")
	if err != nil {
		return nil, err
	}
	for _, item := range []struct {
		name   string
		target *float64
	}{{"StrokeThickness", &value.StrokeThickness}, {"StrokeMiterLimit", &value.StrokeMiterLimit}, {"StrokeDashOffset", &value.StrokeDashOffset}} {
		if text, present := node.attribute(item.name); present {
			*item.target, _ = xmlNumber(text)
		}
	}
	for _, item := range []struct {
		name   string
		target *LineCap
	}{{"StrokeDashCap", &value.StrokeDashCap}, {"StrokeStartLineCap", &value.StrokeStartLineCap}, {"StrokeEndLineCap", &value.StrokeEndLineCap}} {
		if text, present := node.attribute(item.name); present {
			*item.target = LineCap(text)
		}
	}
	if text, present := node.attribute("StrokeLineJoin"); present {
		value.StrokeLineJoin = LineJoin(text)
	}
	for _, item := range []struct {
		name   string
		target *string
	}{{"AutomationProperties.Name", &value.AutomationName}, {"AutomationProperties.HelpText", &value.AutomationHelpText}} {
		if text, present := node.attribute(item.name); present {
			*item.target = text
		}
	}
	if text, present := node.attribute("StrokeDashArray"); present {
		value.StrokeDashArray, _ = parseStrokeDashArray(text)
	}
	if text, present := node.attribute("SnapsToDevicePixels"); present {
		flag := strings.Trim(text, " \t\r\n") == "true"
		value.SnapsToDevicePixels = &flag
	}
	return value, nil
}

// glyphValue 读取已校验字形序列并确定嵌入字体的包内位置
// 入参: node 字形节点, properties 公共局部属性
// 返回: *Glyphs 字形序列, error 错误信息
func (p *sceneParser) glyphValue(node *xmlElement, properties ElementProperties) (*Glyphs, error) {
	value := NewGlyphs("", 0, "")
	value.ElementProperties = properties
	value.FontURI, _ = node.attribute("FontUri")
	font, index, hasIndex, err := ParseFontURI(strings.Trim(value.FontURI, " \t\r\n"))
	if err != nil {
		return nil, p.elementError(node, err)
	}
	value.FontPart, err = resolvePart(value.Part, font)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	value.CollectionIndex, value.HasCollectionIndex = index, hasIndex
	for _, item := range []struct {
		name   string
		target *float64
	}{{"FontRenderingEmSize", &value.FontRenderingEmSize}, {"OriginX", &value.Origin.X}, {"OriginY", &value.Origin.Y}} {
		text, _ := node.attribute(item.name)
		*item.target, _ = xmlNumber(text)
	}
	if text, present := node.attribute("BidiLevel"); present {
		value.BidiLevel, _ = strconv.Atoi(strings.Trim(text, " \t\r\n"))
	}
	if text, present := node.attribute("IsSideways"); present {
		value.IsSideways = strings.Trim(text, " \t\r\n") == "true"
	}
	if text, present := node.attribute("StyleSimulations"); present {
		value.StyleSimulations = StyleSimulation(text)
	}
	text, _ := node.attribute("UnicodeString")
	value.Text = strings.TrimPrefix(text, "{}")
	text, _ = node.attribute("DeviceFontName")
	value.DeviceFontName = strings.TrimPrefix(text, "{}")
	text, _ = node.attribute("Indices")
	value.Indices, _ = ParseGlyphIndices(text)
	text, _ = node.attribute("CaretStops")
	value.CaretStops = strings.Trim(text, " \t\r\n")
	value.Fill, err = p.brushProperty(node, "Fill")
	return value, err
}

// brushProperty 读取颜色、画刷引用或内联画刷属性
// 入参: node 属性所属节点, name 属性名称
// 返回: *Brush 画刷，未指定时为nil, error 错误信息
func (p *sceneParser) brushProperty(node *xmlElement, name string) (*Brush, error) {
	inline, err := p.property(node, name)
	if err != nil {
		return nil, err
	}
	if inline != nil {
		return p.brush(inline, false)
	}
	text, present := node.attribute(name)
	if !present {
		return nil, nil
	}
	key, reference, err := parseResourceReference(text)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	if reference {
		definition := p.resources.Bindings[node][name]
		if definition == nil || definition.Key != key || resourceKind(definition.Kind) != "brush" {
			return nil, p.elementError(node, fmt.Errorf("%w: unresolved brush %q", ErrInvalid, key))
		}
		return p.brush(definition.Element, true)
	}
	if name == "OpacityMask" {
		return nil, p.elementError(node, fmt.Errorf("%w: OpacityMask requires a brush", ErrInvalid))
	}
	color, err := parseBrushColor(text, formatNamespace(p.format))
	if err != nil {
		return nil, p.elementError(node, err)
	}
	return &Brush{Kind: BrushSolidColor, Part: p.resources.Parts[node], Opacity: 1, Color: color}, nil
}

// brush 解析画刷并在原定义作用域中绑定视觉内容
// 入参: node 画刷节点, resource 是否为字典定义
// 返回: *Brush 类型化画刷, error 错误信息
func (p *sceneParser) brush(node *xmlElement, resource bool) (*Brush, error) {
	if value := p.brushes[node]; value != nil {
		return value, nil
	}
	if err := p.budget.resource(node); err != nil {
		return nil, p.elementError(node, err)
	}
	value, err := parseBrushElement(node, func(key string) (Matrix, error) {
		definition, err := p.binding(node, "Transform", key, "MatrixTransform")
		if err != nil {
			return Matrix{}, err
		}
		return p.matrix(definition.Element, true)
	}, resource)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	value.Part = p.resources.Parts[node]
	if value.VisualReference != "" {
		definition := p.resources.Bindings[node]["Visual"]
		if definition == nil || definition.Key != value.VisualReference || resourceKind(definition.Kind) != "visual" {
			return nil, p.elementError(node, fmt.Errorf("%w: unresolved visual resource", ErrInvalid))
		}
		value.Visual, err = p.elementValue(definition.Element)
	} else if value.visualElement != nil {
		value.Visual, err = p.elementValue(value.visualElement)
	}
	if err != nil {
		return nil, err
	}
	p.brushes[node] = value
	return value, nil
}

// geometry 解析内联或资源几何并复用同一页面中的已解析定义
// 入参: node 几何元素, resource 是否为字典中的定义
// 返回: *Geometry 几何数据, error 错误信息
func (p *sceneParser) geometry(node *xmlElement, resource bool) (*Geometry, error) {
	if value := p.geometries[node]; value != nil {
		return value, nil
	}
	if err := p.budget.charge(1, 0); err != nil {
		return nil, p.elementError(node, err)
	}
	value, err := parseGeometryElementLimited(node, func(key string) (Matrix, error) {
		definition, err := p.binding(node, "Transform", key, "MatrixTransform")
		if err != nil {
			return Matrix{}, err
		}
		return p.matrix(definition.Element, true)
	}, resource, p.budget.charge, p.budget.shared(node))
	if err != nil {
		return nil, p.elementError(node, err)
	}
	p.geometries[node] = value
	p.budget.remember(node, value)
	return value, nil
}

// matrix 读取内联或字典中的矩阵定义
// 入参: node 矩阵元素, resource 是否为字典中的定义
// 返回: Matrix 仿射矩阵, error 错误信息
func (p *sceneParser) matrix(node *xmlElement, resource bool) (Matrix, error) {
	if value, ok := p.matrices[node]; ok {
		return value, nil
	}
	if err := p.budget.charge(1, 0); err != nil {
		return Matrix{}, p.elementError(node, err)
	}
	attrs, err := geometryXMLAttributes(node, formatNamespace(p.format), "MatrixTransform", resource, "Matrix")
	if err != nil {
		return Matrix{}, p.elementError(node, err)
	}
	if len(node.Children) != 0 {
		return Matrix{}, p.elementError(node, fmt.Errorf("%w: MatrixTransform cannot contain children", ErrInvalid))
	}
	text, err := geometryXMLRequired(attrs, "Matrix")
	if err != nil {
		return Matrix{}, p.elementError(node, err)
	}
	value, err := ParseMatrix(text)
	if err != nil {
		return Matrix{}, p.elementError(node, err)
	}
	p.matrices[node] = value
	return value, nil
}

// geometryProperty 读取几何属性的缩写、资源引用或内联元素
// 入参: node 属性所属元素, name 属性名称
// 返回: *Geometry 几何数据，未指定时为nil, error 错误信息
func (p *sceneParser) geometryProperty(node *xmlElement, name string) (*Geometry, error) {
	inline, err := p.property(node, name)
	if err != nil {
		return nil, err
	}
	if inline != nil {
		return p.geometry(inline, false)
	}
	text, present := node.attribute(name)
	if !present {
		return nil, nil
	}
	key, reference, err := parseResourceReference(text)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	if reference {
		definition, err := p.binding(node, name, key, "PathGeometry")
		if err != nil {
			return nil, err
		}
		return p.geometry(definition.Element, true)
	}
	if err := p.budget.charge(1, 0); err != nil {
		return nil, p.elementError(node, err)
	}
	value, err := parseGeometryLimited(text, p.budget.charge)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	return value, nil
}

// matrixProperty 读取矩阵属性的数值、资源引用或内联元素
// 入参: node 属性所属元素, name 属性名称
// 返回: *Matrix 仿射矩阵，未指定时为nil, error 错误信息
func (p *sceneParser) matrixProperty(node *xmlElement, name string) (*Matrix, error) {
	inline, err := p.property(node, name)
	if err != nil {
		return nil, err
	}
	if inline != nil {
		value, err := p.matrix(inline, false)
		if err != nil {
			return nil, err
		}
		return &value, nil
	}
	text, present := node.attribute(name)
	if !present {
		return nil, nil
	}
	key, reference, err := parseResourceReference(text)
	if err != nil {
		return nil, p.elementError(node, err)
	}
	var value Matrix
	if reference {
		definition, err := p.binding(node, name, key, "MatrixTransform")
		if err != nil {
			return nil, err
		}
		value, err = p.matrix(definition.Element, true)
	} else {
		value, err = ParseMatrix(text)
	}
	if err != nil {
		return nil, p.elementError(node, err)
	}
	return &value, nil
}

// property 读取单值属性元素并拒绝重复的属性表示
// 入参: node 属性所属元素, name 属性名称
// 返回: *xmlElement 内联属性值，未指定时为nil, error 错误信息
func (p *sceneParser) property(node *xmlElement, name string) (*xmlElement, error) {
	var value *xmlElement
	_, attribute := node.attribute(name)
	for _, child := range node.Children {
		if child.Name.Local != node.Name.Local+"."+name {
			continue
		}
		if value != nil || attribute || len(child.Children) != 1 {
			return nil, p.elementError(node, fmt.Errorf("%w: invalid or repeated %s property", ErrInvalid, name))
		}
		if _, err := geometryXMLAttributes(child, formatNamespace(p.format), child.Name.Local, false); err != nil {
			return nil, p.elementError(child, err)
		}
		value = child.Children[0]
	}
	return value, nil
}

// binding 取得定义时已解析的资源引用，不在最终字典上重新查找
// 入参: node 属性所属元素, property 属性名称, key 资源键, kind 预期资源类型
// 返回: *resourceDefinition 已绑定定义, error 错误信息
func (p *sceneParser) binding(node *xmlElement, property, key, kind string) (*resourceDefinition, error) {
	definition := p.resources.Bindings[node][property]
	if definition == nil || definition.Key != key || definition.Kind != kind {
		return nil, p.elementError(node, fmt.Errorf("%w: unresolved %s resource %q", ErrInvalid, property, key))
	}
	return definition, nil
}

// wrapPartError 为错误附加部件及元素位置，内层已含同部件PartError时保留最内层定位
// 入参: part 部件URI, element 可选元素名, err 原始错误
// 返回: error 包装后的错误，err为nil时返回nil
func wrapPartError(part, element string, err error) error {
	if err == nil {
		return nil
	}
	var existing *PartError
	if errors.As(err, &existing) && strings.EqualFold(existing.Part, part) {
		return err
	}
	return &PartError{Part: part, Element: element, Err: err}
}

// elementError 为绘制数据错误补充元素所属部件
// 入参: node 出错元素, err 原始错误
// 返回: error 带部件位置的错误信息
func (p *sceneParser) elementError(node *xmlElement, err error) error {
	if node == nil {
		return err
	}
	return wrapPartError(p.resources.Parts[node], node.Name.Local, err)
}

// visualAttributes 校验绘制元素的属性集合和属性元素顺序
// 入参: node 绘制元素, format 文档格式
// 返回: map[string]string 无命名空间属性, error 错误信息
func visualAttributes(node *xmlElement, format Format) (map[string]string, error) {
	common := []string{"RenderTransform", "Clip", "Opacity", "OpacityMask", "Name", "FixedPage.NavigateUri"}
	var properties []string
	switch node.Name.Local {
	case "Canvas":
		common = append(common, "RenderOptions.EdgeMode", "AutomationProperties.Name", "AutomationProperties.HelpText")
		properties = []string{"Resources", "RenderTransform", "Clip", "OpacityMask"}
	case "Path":
		common = append(common, "Data", "Fill", "Stroke", "StrokeDashArray", "StrokeDashCap", "StrokeDashOffset", "StrokeEndLineCap", "StrokeStartLineCap", "StrokeLineJoin", "StrokeMiterLimit", "StrokeThickness", "SnapsToDevicePixels", "AutomationProperties.Name", "AutomationProperties.HelpText")
		properties = []string{"RenderTransform", "Clip", "OpacityMask", "Fill", "Stroke", "Data"}
	case "Glyphs":
		common = append(common, "FontUri", "FontRenderingEmSize", "OriginX", "OriginY", "Fill", "BidiLevel", "IsSideways", "Indices", "UnicodeString", "StyleSimulations", "CaretStops", "DeviceFontName")
		properties = []string{"RenderTransform", "Clip", "OpacityMask", "Fill"}
	default:
		return nil, fmt.Errorf("%w: unknown visual element %s", ErrInvalid, node.Name.Local)
	}
	attrs := make(map[string]string)
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name.Space == "" && attr.Name.Local == "xmlns" || attr.Name.Space == xmlNamespace && attr.Name.Local == "lang" || attr.Name.Space == formatNamespace(format)+"/resourcedictionary-key" && attr.Name.Local == "Key" {
			continue
		}
		allowed := false
		for _, name := range common {
			if attr.Name.Space == "" && attr.Name.Local == name {
				allowed = true
				break
			}
		}
		if !allowed {
			return nil, fmt.Errorf("%w: unexpected attribute {%s}%s on %s", ErrInvalid, attr.Name.Space, attr.Name.Local, node.Name.Local)
		}
		attrs[attr.Name.Local] = attr.Value
	}
	last := -1
	for _, child := range node.Children {
		if child.Name.Space != formatNamespace(format) {
			return nil, fmt.Errorf("%w: visual child namespace %s", ErrInvalid, child.Name.Space)
		}
		if node.Name.Local == "Canvas" && (child.Name.Local == "Path" || child.Name.Local == "Glyphs" || child.Name.Local == "Canvas") {
			last = len(properties)
			continue
		}
		index := -1
		for i, property := range properties {
			if child.Name.Local == node.Name.Local+"."+property {
				index = i
				break
			}
		}
		if index < 0 || index <= last {
			return nil, fmt.Errorf("%w: unexpected or out-of-order child %s", ErrInvalid, child.Name.Local)
		}
		if _, present := attrs[properties[index]]; present {
			return nil, fmt.Errorf("%w: attribute and element both specify %s", ErrInvalid, properties[index])
		}
		last = index
	}
	return attrs, nil
}

// validateVisual 校验绘制元素的数值、枚举及文字属性
// 入参: node 绘制元素, format 文档格式
// 返回: error 错误信息
func validateVisual(node *xmlElement, format Format) error {
	attrs, err := visualAttributes(node, format)
	if err != nil {
		return err
	}
	if language, present := node.attributeNS(xmlNamespace, "lang"); present && language != "" && !fixedLanguageTag(language) {
		return fmt.Errorf("%w: invalid xml:lang on %s", ErrInvalid, node.Name.Local)
	}
	if value, ok := attrs["Opacity"]; ok {
		n, err := xmlNumber(value)
		if err != nil || n < 0 || n > 1 {
			return fmt.Errorf("%w: invalid Opacity %q", ErrInvalid, value)
		}
	}
	switch node.Name.Local {
	case "Canvas":
		if value, ok := attrs["RenderOptions.EdgeMode"]; ok && EdgeMode(value) != EdgeModeAliased {
			return fmt.Errorf("%w: invalid EdgeMode %q", ErrInvalid, value)
		}
	case "Path":
		return validatePathAttributes(attrs)
	case "Glyphs":
		return validateGlyphAttributes(attrs, format)
	}
	return nil
}

// validatePathAttributes 校验描边参数和设备像素对齐提示
// 入参: attrs 路径属性
// 返回: error 错误信息
func validatePathAttributes(attrs map[string]string) error {
	for _, name := range []string{"StrokeDashOffset", "StrokeMiterLimit", "StrokeThickness"} {
		if value, ok := attrs[name]; ok {
			n, err := xmlNumber(value)
			if err != nil || name == "StrokeMiterLimit" && n < 1 || name == "StrokeThickness" && n < 0 {
				return fmt.Errorf("%w: invalid %s %q", ErrInvalid, name, value)
			}
		}
	}
	for _, name := range []string{"StrokeDashCap", "StrokeEndLineCap", "StrokeStartLineCap"} {
		if value, ok := attrs[name]; ok && !strokeOutlineCapValid(LineCap(value)) {
			return fmt.Errorf("%w: invalid %s %q", ErrInvalid, name, value)
		}
	}
	if value, ok := attrs["StrokeLineJoin"]; ok && LineJoin(value) != LineJoinMiter && LineJoin(value) != LineJoinBevel && LineJoin(value) != LineJoinRound {
		return fmt.Errorf("%w: invalid StrokeLineJoin %q", ErrInvalid, value)
	}
	if _, err := geometryXMLBool(attrs, "SnapsToDevicePixels", false); err != nil {
		return err
	}
	if value, ok := attrs["StrokeDashArray"]; ok {
		_, err := parseStrokeDashArray(value)
		return err
	}
	return nil
}

// parseStrokeDashArray 解析由偶数个非负数构成的描边虚线数组
// 入参: text XML属性值
// 返回: []float64 虚线长度数组, error 错误信息
func parseStrokeDashArray(text string) ([]float64, error) {
	items := compatibilityWords(text)
	if len(items) < 2 || len(items)%2 != 0 {
		return nil, fmt.Errorf("%w: StrokeDashArray requires a nonempty even number of values", ErrInvalid)
	}
	values := make([]float64, len(items))
	for i, item := range items {
		value, err := xmlNumber(item)
		if err != nil || value < 0 || strings.HasPrefix(item, "-") {
			return nil, fmt.Errorf("%w: invalid dash length %q", ErrInvalid, item)
		}
		values[i] = value
	}
	return values, nil
}

// validateGlyphAttributes 校验字形放置、方向、文本映射及光标停靠点
// 入参: attrs 字形属性, format 文档格式
// 返回: error 错误信息
func validateGlyphAttributes(attrs map[string]string, format Format) error {
	for _, name := range []string{"FontRenderingEmSize", "OriginX", "OriginY"} {
		value, present := attrs[name]
		n, err := xmlNumber(value)
		if !present || err != nil || name == "FontRenderingEmSize" && n < 0 {
			return fmt.Errorf("%w: missing or invalid %s", ErrInvalid, name)
		}
	}
	uri, present := attrs["FontUri"]
	if !present {
		return fmt.Errorf("%w: missing FontUri", ErrInvalid)
	}
	if _, _, _, err := ParseFontURI(strings.Trim(uri, " \t\r\n")); err != nil {
		return fmt.Errorf("FontUri: %w", err)
	}
	level := int64(0)
	if value, ok := attrs["BidiLevel"]; ok {
		var err error
		level, err = strconv.ParseInt(strings.Trim(value, " \t\r\n"), 10, 8)
		if err != nil || level < 0 || level > 61 {
			return fmt.Errorf("%w: invalid BidiLevel %q", ErrInvalid, value)
		}
	}
	sideways, err := geometryXMLBool(attrs, "IsSideways", false)
	if err != nil {
		return err
	}
	if sideways && level%2 != 0 {
		return fmt.Errorf("%w: sideways Glyphs cannot use an odd BidiLevel", ErrInvalid)
	}
	if value, ok := attrs["StyleSimulations"]; ok {
		switch StyleSimulation(value) {
		case StyleSimulationNone, StyleSimulationItalic, StyleSimulationBold, StyleSimulationBoldItalic:
		default:
			return fmt.Errorf("%w: invalid StyleSimulations %q", ErrInvalid, value)
		}
	}
	for _, name := range []string{"UnicodeString", "DeviceFontName"} {
		if value, ok := attrs[name]; ok {
			if err := validateUnicodeString(value, format); err != nil {
				return fmt.Errorf("%s: %w", name, err)
			}
		}
	}
	indices, err := ParseGlyphIndices(attrs["Indices"])
	if err != nil {
		return fmt.Errorf("Indices: %w", err)
	}
	if err := ValidateGlyphIndices(indices, attrs["UnicodeString"]); err != nil {
		return err
	}
	if value, ok := attrs["CaretStops"]; ok {
		if _, err := ParseCaretStops(value, attrs["UnicodeString"]); err != nil {
			return err
		}
	}
	return nil
}

// validateUnicodeString 校验双格式UnicodeString的转义及换行规则
// 入参: value XML解码后的字符串, format 文档格式
// 返回: error 错误信息
func validateUnicodeString(value string, format Format) error {
	if !utf8.ValidString(value) {
		return fmt.Errorf("%w: invalid UnicodeString encoding", ErrInvalid)
	}
	if value == "" {
		return nil
	}
	var tail string
	if strings.HasPrefix(value, "{}") {
		tail = value[2:]
	} else {
		if value[0] == '{' {
			return fmt.Errorf("%w: leading brace requires {} escape", ErrInvalid)
		}
		_, size := utf8.DecodeRuneInString(value)
		tail = value[size:]
	}
	if format == FormatXPS && strings.ContainsAny(tail, "\r\n") {
		return fmt.Errorf("%w: XPS UnicodeString cannot contain line breaks after its initial character", ErrInvalid)
	}
	return nil
}

// acquireSceneWorker 从有界对象池获取工作Goroutine独占的复用缓冲状态
// 返回: *sceneWorkerState 独立工作状态
func acquireSceneWorker() *sceneWorkerState {
	if pooled, ok := sceneWorkerPool.Get().(*sceneWorkerState); ok && pooled != nil {
		return pooled
	}
	return &sceneWorkerState{}
}

// releaseSceneWorker 清理并归还工作状态，超大临时缓冲交由GC回收
// 入参: state 工作状态
func releaseSceneWorker(state *sceneWorkerState) {
	if state == nil {
		return
	}
	for i, surface := range state.isolated {
		releaseRenderSurface(surface)
		state.isolated[i] = nil
	}
	state.isolated = state.isolated[:0]
	for i, surface := range state.printIsolated {
		releasePrintSurfaceBuffer(surface)
		state.printIsolated[i] = nil
	}
	state.printIsolated = state.printIsolated[:0]
	if cap(state.mask.Pix) > sceneScratchPoolMax {
		state.mask.Pix = nil
	}
	if cap(state.coarse.Pix) > sceneScratchPoolMax {
		state.coarse.Pix = nil
	}
	if cap(state.part.Pix) > sceneScratchPoolMax {
		state.part.Pix = nil
	}
	if cap(state.clip.Pix) > sceneScratchPoolMax {
		state.clip.Pix = nil
	}
	if cap(state.raster.prepared) > 4096 {
		state.raster = rasterScratch{}
	}
	if cap(state.regions) > 4096 {
		state.regions = nil
	} else {
		state.regions = state.regions[:0]
	}
	state.imageCache.sampler = nil
	state.imageCache.valid = false
	state.imageCache.jxr.source = nil
	state.imageCache.jxr.valid = [2]bool{}
	sceneWorkerPool.Put(state)
}

// defaultSceneRenderOptions 返回有界图块绘制的默认参数
// 返回: sceneRenderOptions 八倍线性采样及资源上限
func defaultSceneRenderOptions() sceneRenderOptions {
	return sceneRenderOptions{samples: 8, tolerance: 0.025, space: renderSRGB, pixels: 1 << 24, elements: 1 << 20, edges: 1 << 20, work: 1 << 28, glyphs: 1 << 20, fonts: 256, fontBytes: 64 << 20, format: FormatOpenXPS, images: 256, imagePixels: 1 << 24, imageBytes: 64 << 20, profiles: 256, profileBytes: 64 << 20, context: context.Background()}
}

// renderPageCoversBounds 判断页面矩形经轴对齐有效变换后是否完全覆盖输出像素范围
// 入参: width 页面宽度, height 页面高度, transform 页面到设备的变换, bounds 输出像素范围
// 返回: bool 页面矩形是否完全覆盖输出范围
func renderPageCoversBounds(width, height float64, transform Matrix, bounds image.Rectangle) bool {
	if bounds.Empty() {
		return true
	}
	if !geometryFinite(width, height) || width <= 0 || height <= 0 || !geometryFillMatrixFinite(transform) || geometryMatrixSingular(transform) {
		return false
	}
	if !(transform.B == 0 && transform.C == 0 || transform.A == 0 && transform.D == 0) {
		return false
	}
	p0, err0 := geometryFillPoint(transform, Point{})
	p1, err1 := geometryFillPoint(transform, Point{width, height})
	if err0 != nil || err1 != nil {
		return false
	}
	minX, maxX := min(p0.X, p1.X), max(p0.X, p1.X)
	minY, maxY := min(p0.Y, p1.Y), max(p0.Y, p1.Y)
	return minX <= float64(bounds.Min.X) && minY <= float64(bounds.Min.Y) && maxX >= float64(bounds.Max.X) && maxY >= float64(bounds.Max.Y)
}

// renderSubClipBound 求与光栅化像素中心归属规则一致的半开子像素边界整数索引
// 入参: v 子像素空间有限边界坐标
// 返回: int 满足idx+0.5>=v的最小整数索引
func renderSubClipBound(v float64) int {
	idx := int(math.Ceil(v - 0.5))
	for float64(idx-1)+0.5 >= v {
		idx--
	}
	for float64(idx)+0.5 < v {
		idx++
	}
	return idx
}

// renderSubClipInterval 将子像素实数区间裁剪至目标范围并换算为精确整数半开子像素区间
// 入参: lo 实数下界, hi 实数上界, minBound 目标范围下界, maxBound 目标范围上界
// 返回: int 整数下界, int 整数上界
func renderSubClipInterval(lo, hi float64, minBound, maxBound int) (int, int) {
	if hi <= float64(minBound)-0.5 || lo >= float64(maxBound)+0.5 {
		return minBound, minBound
	}
	start := minBound
	if lo > float64(minBound)-0.5 {
		start = max(minBound, renderSubClipBound(lo))
	}
	end := maxBound
	if hi < float64(maxBound)+0.5 {
		end = min(maxBound, renderSubClipBound(hi))
	}
	if end < start {
		return start, start
	}
	return start, end
}

// renderAxisAlignedPageClip 计算纯轴对齐变换页面矩形对应的精确子像素半开裁剪范围
// 入参: width 页面宽度, height 页面高度, transform 页面到设备的变换, bounds 输出像素范围, samples 线性采样倍率
// 返回: image.Rectangle 子像素半开裁剪范围, bool 变换是否为纯轴对齐且可无隔离裁剪
func renderAxisAlignedPageClip(width, height float64, transform Matrix, bounds image.Rectangle, samples int) (image.Rectangle, bool) {
	if !geometryFinite(width, height) || width <= 0 || height <= 0 || !geometryFillMatrixFinite(transform) || geometryMatrixSingular(transform) || samples < 1 {
		return image.Rectangle{}, false
	}
	if !(transform.B == 0 && transform.C == 0 || transform.A == 0 && transform.D == 0) {
		return image.Rectangle{}, false
	}
	p0, err0 := geometryFillPoint(transform, Point{})
	p1, err1 := geometryFillPoint(transform, Point{width, height})
	if err0 != nil || err1 != nil {
		return image.Rectangle{}, false
	}
	scale := float64(samples)
	sx0, sx1 := min(p0.X, p1.X)*scale, max(p0.X, p1.X)*scale
	sy0, sy1 := min(p0.Y, p1.Y)*scale, max(p0.Y, p1.Y)*scale
	if !geometryFinite(sx0, sx1, sy0, sy1) {
		return image.Rectangle{}, false
	}
	x0, x1 := renderSubClipInterval(sx0, sx1, bounds.Min.X*samples, bounds.Max.X*samples)
	y0, y1 := renderSubClipInterval(sy0, sy1, bounds.Min.Y*samples, bounds.Max.Y*samples)
	return image.Rect(x0, y0, x1, y1), true
}

// renderFloorDiv 计算向下取整的整数商，确保负子像素坐标映射至正确的粗像素索引
// 入参: a 被除数, b 正除数
// 返回: int 向下取整商
func renderFloorDiv(a, b int) int {
	q := a / b
	if a < 0 && a%b != 0 {
		q--
	}
	return q
}

// renderCeilDiv 计算向上取整的整数商，确保非对齐子像素上界覆盖完整粗像素
// 入参: a 被除数, b 正除数
// 返回: int 向上取整商
func renderCeilDiv(a, b int) int {
	q := a / b
	if a > 0 && a%b != 0 {
		q++
	}
	return q
}

// renderLoadedPage 在调用方持有读锁时绘制已经解析的页面，单次调用独占所有资源缓存
// 入参: page 已解析页面, transform 页面到设备的变换, bounds 输出范围, options 绘制参数
// 返回: *image.NRGBA 页面图像, error 资源、绘制或能力错误
func (r *Reader) renderLoadedPage(page *Page, transform Matrix, bounds image.Rectangle, options sceneRenderOptions) (*image.NRGBA, error) {
	var clip *Geometry
	if !renderPageCoversBounds(page.Width, page.Height, transform, bounds) {
		if len(options.printPlan) == 0 {
			if subClip, ok := renderAxisAlignedPageClip(page.Width, page.Height, transform, bounds, options.samples); ok {
				options.pageSubClip = &subClip
			} else {
				clip = renderBoxGeometry(Rect{Width: page.Width, Height: page.Height})
			}
		} else {
			clip = renderBoxGeometry(Rect{Width: page.Width, Height: page.Height})
		}
	}
	root := &Canvas{ElementProperties: ElementProperties{Part: page.Part, Opacity: 1, Clip: clip}, Elements: page.Elements}
	return r.renderLoadedElements([]Element{root}, transform, bounds, options)
}

// renderBoxGeometry 创建用于页面及介质裁剪的矩形路径，不修改调用方区域
// 入参: box 有限非负区域
// 返回: *Geometry 独立裁剪几何
func renderBoxGeometry(box Rect) *Geometry {
	return &Geometry{FillRule: GeometryNonZero, Figures: []GeometryFigure{{StartPoint: Point{box.X, box.Y}, IsFilled: true, IsClosed: true, Segments: []GeometrySegment{
		{Kind: GeometryLine, Point: Point{box.X + box.Width, box.Y}},
		{Kind: GeometryLine, Point: Point{box.X + box.Width, box.Y + box.Height}},
		{Kind: GeometryLine, Point: Point{box.X, box.Y + box.Height}},
	}}}}
}

// renderLoadedElements 为已加载场景建立单次绘制资源缓存，供普通页面及物理介质输出共用
// 入参: elements 已加载元素, transform 场景到设备的变换, bounds 输出范围, options 绘制参数
// 返回: *image.NRGBA 图像, error 资源、绘制或取消错误
func (r *Reader) renderLoadedElements(elements []Element, transform Matrix, bounds image.Rectangle, options sceneRenderOptions) (*image.NRGBA, error) {
	fonts := fontCache{pkg: r.pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: options.fontBytes, maxFaces: options.fonts}
	return r.renderLoadedElementsFonts(elements, transform, bounds, options, &fonts)
}

// renderLoadedElementsFonts 复用本次调用的字体缓存，使生成内容与正文共享字体字节及字体面预算
// 入参: elements 已加载元素, transform 场景到设备的变换, bounds 输出范围, options 绘制参数, fonts 私有字体缓存
// 返回: *image.NRGBA 图像, error 资源、绘制或取消错误
func (r *Reader) renderLoadedElementsFonts(elements []Element, transform Matrix, bounds image.Rectangle, options sceneRenderOptions, fonts *fontCache) (*image.NRGBA, error) {
	options.font, options.format = fonts.load, r.format
	colors := sceneColorCache{pkg: r.pkg, profiles: make(map[string]*iccProfile), transforms: make(map[string][4]*iccTransform), bytes: options.profileBytes, maxProfiles: options.profiles}
	if options.device != nil {
		colors.sourceIntent = options.device.sourceIntent
	}
	options.color = colors.vector
	images := sceneImageCache{pkg: r.pkg, images: make(map[string]*rasterImage), bytes: options.imageBytes, pixels: options.imagePixels, maxImages: options.images, colors: &colors, context: withJXRDecodeWorkers(options.context, options.workers), format: r.format}
	images.deferColor = len(options.printPlan) != 0
	options.image = images.load
	options.printProfiles = &colors
	return renderScene(elements, transform, bounds, options)
}

// sceneMaxIsolatedDepth 计算已准备场景树中同时活跃的最大隔离表面嵌套深度
// 入参: nodes 已准备场景节点列表
// 返回: int 最大隔离深度
func sceneMaxIsolatedDepth(nodes []*sceneNode) int {
	maximum := 0
	for _, node := range nodes {
		if node == nil || node.opacity == 0 {
			continue
		}
		depth := sceneMaxIsolatedDepth(node.children)
		if node.opacity != 1 || node.mask != nil || node.clip != nil || node.negative {
			depth++
		}
		if depth > maximum {
			maximum = depth
		}
	}
	return maximum
}

// renderScene 在统一子像素空间合成并降采样绘制已解析元素，失败时不返回部分图像
// 入参: elements 声明顺序的元素, transform 页面到设备的变换, bounds 输出范围, options 采样及资源参数
// 返回: *image.NRGBA 非预乘sRGB图像，设备模式写入私有目标并返回nil, error 结构、能力或资源错误
func renderScene(elements []Element, transform Matrix, bounds image.Rectangle, options sceneRenderOptions) (*image.NRGBA, error) {
	pixels, err := validateSceneOutput(bounds, transform, options)
	if err != nil {
		return nil, err
	}
	r := sceneRenderer{options: options, active: make(map[Element]bool), elements: options.elements, edges: options.edges, work: options.work, live: pixels, glyphs: options.glyphs, exact: rasterMaxExact}
	defer r.cleanup()
	if len(options.printPlan) != 0 {
		return r.renderPrintColorScene(elements, transform, bounds)
	}
	nodes, err := r.prepare(elements, transform, false, 0)
	if err != nil {
		return nil, err
	}
	var output *image.NRGBA
	if options.device != nil {
		if err := options.device.allocate(bounds); err != nil {
			return nil, err
		}
	} else {
		output = image.NewNRGBA(bounds)
	}
	if bounds.Empty() {
		return output, nil
	}
	samples := options.samples
	cols := (bounds.Dx() + sceneTileSize - 1) / sceneTileSize
	rows := (bounds.Dy() + sceneTileSize - 1) / sceneTileSize
	tileCount := cols * rows
	tileW := min(sceneTileSize, bounds.Dx()) * samples
	tileH := min(sceneTileSize, bounds.Dy()) * samples
	first := image.Rect(bounds.Min.X*samples, bounds.Min.Y*samples, bounds.Min.X*samples+tileW, bounds.Min.Y*samples+tileH)
	workers := resolveXPSWorkers(options.workers, tileCount)
	if options.workers == 0 && (tileCount < 4 || bounds.Dx()*bounds.Dy() < 4096) {
		workers = 1
	}
	if workers > 1 {
		available := uint64(max(0, r.options.pixels-r.live))
		perWorker := uint64(tileW) * uint64(tileH) * uint64(1+sceneMaxIsolatedDepth(nodes))
		if r.hasFiltered {
			if available <= perWorker*2 {
				workers = 1
			} else {
				workers = budgetXPSWorkers(workers, available/2, perWorker)
			}
		} else {
			workers = budgetXPSWorkers(workers, available, perWorker)
		}
	}
	if workers <= 1 {
		surface, err := r.acquireSurface(first)
		if err != nil {
			return nil, err
		}
		defer r.releaseSurface(surface)
		worker := acquireSceneWorker()
		defer releaseSceneWorker(worker)
		for y := bounds.Min.Y; y < bounds.Max.Y; y += sceneTileSize {
			for x := bounds.Min.X; x < bounds.Max.X; x += sceneTileSize {
				tile := image.Rect(x, y, min(x+sceneTileSize, bounds.Max.X), min(y+sceneTileSize, bounds.Max.Y))
				if err := r.tile(nodes, surface, output, tile, worker); err != nil {
					return nil, err
				}
			}
		}
		return output, nil
	}
	surfaces := make([]*renderSurface, workers)
	states := make([]*sceneWorkerState, workers)
	defer func() {
		for i := range workers {
			if states[i] != nil {
				releaseSceneWorker(states[i])
			}
			if surfaces[i] != nil {
				r.releaseSurface(surfaces[i])
			}
		}
	}()
	for i := range workers {
		surface, err := r.acquireSurface(first)
		if err != nil {
			return nil, err
		}
		surfaces[i] = surface
		states[i] = acquireSceneWorker()
	}
	r.concurrent = true
	err = runXPSWorkerSlots(r.options.context, workers, tileCount, func(runCtx context.Context, slot, task int) error {
		if err := runCtx.Err(); err != nil {
			r.cancelled.Store(true)
			return err
		}
		tx := task % cols
		ty := task / cols
		x := bounds.Min.X + tx*sceneTileSize
		y := bounds.Min.Y + ty*sceneTileSize
		tile := image.Rect(x, y, min(x+sceneTileSize, bounds.Max.X), min(y+sceneTileSize, bounds.Max.Y))
		if err := r.tile(nodes, surfaces[slot], output, tile, states[slot]); err != nil {
			r.cancelled.Store(true)
			return err
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	return output, nil
}

// validateSceneOutput 在加载或组合场景前检查输出参数、坐标和像素容量
// 入参: bounds 输出范围, transform 场景变换, options 绘制参数
// 返回: int 输出像素数, error 参数、能力或容量错误
func validateSceneOutput(bounds image.Rectangle, transform Matrix, options sceneRenderOptions) (int, error) {
	if options.outputColor > PrintColorMonochrome {
		return 0, fmt.Errorf("%w: print output color mode", ErrInvalid)
	}
	if options.workers < 0 || !geometryFinite(options.hdrPeakNits) || options.hdrPeakNits < 0 || options.samples != 1 && options.samples != 2 && options.samples != 4 && options.samples != 8 || !geometryFinite(options.tolerance) || options.tolerance <= 0 || options.pixels < 0 || options.elements < 0 || options.edges < 0 || options.glyphs < 0 || options.fonts < 0 || options.fontBytes < 0 || options.images < 0 || options.imageBytes < 0 || options.profiles < 0 || options.profileBytes < 0 || !geometryFillMatrixFinite(transform) {
		return 0, fmt.Errorf("%w: scene render options", ErrInvalid)
	}
	if options.edges > int(^uint(0)>>1)/4 {
		return 0, fmt.Errorf("%w: scene max edges", ErrLimit)
	}
	if options.space != renderSRGB && options.space != renderScRGB {
		return 0, fmt.Errorf("%w: scene color space", ErrUnsupported)
	}
	if err := options.background.validate(); err != nil {
		return 0, err
	}
	if bounds.Min.X > bounds.Max.X || bounds.Min.Y > bounds.Max.Y {
		return 0, fmt.Errorf("%w: scene bounds", ErrInvalid)
	}
	limit := (1 << 30) / options.samples
	width, height := int64(bounds.Max.X)-int64(bounds.Min.X), int64(bounds.Max.Y)-int64(bounds.Min.Y)
	if bounds.Min.X < -limit || bounds.Min.Y < -limit || bounds.Max.X > limit || bounds.Max.Y > limit || width > rasterMaxDimension || height > rasterMaxDimension {
		return 0, fmt.Errorf("%w: scene dimensions", ErrLimit)
	}
	pixels := uint64(width) * uint64(height)
	if pixels > uint64(options.pixels) || pixels > uint64(^uint(0)>>1)/4 {
		return 0, fmt.Errorf("%w: scene output pixels", ErrLimit)
	}
	if options.device != nil {
		if err := options.device.validateBounds(bounds); err != nil {
			return 0, err
		}
	}
	return int(pixels), nil
}

// charge 检查取消并从本次调用的共享工作预算中扣除操作数量
// 入参: count 待执行的操作数量
// 返回: error 取消或预算不足错误
func (r *sceneRenderer) charge(count uint64) error {
	if r.options.context != nil {
		if err := r.options.context.Err(); err != nil {
			return err
		}
	}
	if r.concurrent {
		if r.cancelled.Load() {
			return context.Canceled
		}
		if count == 0 {
			return nil
		}
		r.budgetMu.Lock()
		if count > r.work {
			r.budgetMu.Unlock()
			return fmt.Errorf("%w: scene work budget", ErrLimit)
		}
		r.work -= count
		r.budgetMu.Unlock()
		return nil
	}
	if count > r.work {
		return fmt.Errorf("%w: scene work budget", ErrLimit)
	}
	r.work -= count
	return nil
}

// prepare 按声明顺序准备绘制元素，复用资源按各自使用位置解析状态
// 入参: elements 元素列表, transform 祖先有效变换, aliased 继承的边缘模式, depth 当前深度
// 返回: []*sceneNode 独立绘制节点, error 准备错误
func (r *sceneRenderer) prepare(elements []Element, transform Matrix, aliased bool, depth int) ([]*sceneNode, error) {
	if err := r.charge(0); err != nil {
		return nil, err
	}
	if depth > sceneMaxDepth || len(elements) > r.elements {
		return nil, fmt.Errorf("%w: scene depth or element count", ErrLimit)
	}
	r.elements -= len(elements)
	nodes := make([]*sceneNode, 0, len(elements))
	for _, element := range elements {
		if err := r.charge(0); err != nil {
			return nil, err
		}
		if r.active[element] {
			return nil, fmt.Errorf("%w: cyclic visual tree", ErrInvalid)
		}
		r.active[element] = true
		node, err := r.node(element, transform, aliased, depth)
		delete(r.active, element)
		if err != nil {
			return nil, err
		}
		nodes = append(nodes, node)
	}
	return nodes, nil
}

// node 准备单个元素的变换、画刷、几何及隔离分组
// 入参: element 源元素, transform 祖先有效变换, aliased 继承的边缘模式, depth 当前深度
// 返回: *sceneNode 绘制节点, error 带部件位置的准备错误
func (r *sceneRenderer) node(element Element, transform Matrix, aliased bool, depth int) (result *sceneNode, err error) {
	previous := r.printRuntime
	if canvas, ok := element.(*Canvas); ok {
		if plan, present := r.options.printPlan[canvas]; present {
			r.printRuntime = r.printContext[canvas]
			if r.printRuntime == nil {
				r.printRuntime, err = newPrintColorRuntime(plan, r.options.printOptions, r.options.printProfiles, r)
			}
			if err != nil {
				return nil, err
			}
		}
	}
	defer func() { r.printRuntime = previous }()
	var properties *ElementProperties
	kind := ""
	switch value := element.(type) {
	case *Canvas:
		if value != nil {
			properties, kind = &value.ElementProperties, "Canvas"
		}
	case *Path:
		if value != nil {
			properties, kind = &value.ElementProperties, "Path"
		}
	case *Glyphs:
		if value != nil {
			properties, kind = &value.ElementProperties, "Glyphs"
		}
	}
	if properties == nil {
		return nil, fmt.Errorf("%w: missing scene element", ErrInvalid)
	}
	defer func() {
		if err != nil {
			err = wrapPartError(properties.Part, kind, err)
		}
	}()
	if !geometryFinite(properties.Opacity) || properties.Opacity < 0 || properties.Opacity > 1 {
		return nil, fmt.Errorf("%w: element opacity", ErrInvalid)
	}
	if properties.RenderTransform != nil {
		if !geometryFillMatrixFinite(*properties.RenderTransform) {
			return nil, fmt.Errorf("%w: element transform", ErrInvalid)
		}
		transform = strokePathCompose(transform, *properties.RenderTransform)
		if !geometryFillMatrixFinite(transform) {
			return nil, fmt.Errorf("%w: element transform range", ErrLimit)
		}
	}
	if canvas, ok := element.(*Canvas); ok {
		switch canvas.EdgeMode {
		case "":
		case EdgeModeAliased:
			aliased = true
		default:
			return nil, fmt.Errorf("%w: canvas edge mode", ErrInvalid)
		}
	}
	n := &sceneNode{part: properties.Part, kind: kind, opacity: properties.Opacity, aliased: aliased, color: r.printRuntime}
	if canvas, ok := element.(*Canvas); ok {
		n.negative = r.options.negative[canvas]
	}
	if geometryMatrixSingular(transform) || properties.Opacity == 0 {
		n.opacity = 0
		return n, nil
	}
	if properties.Clip != nil {
		region, err := r.fill(properties.Clip, transform, aliased)
		if err != nil {
			return nil, err
		}
		n.clip = &region
	}
	if properties.OpacityMask != nil {
		n.mask, err = r.brushMode(properties.OpacityMask, transform, aliased, depth, true)
		if err != nil {
			return nil, err
		}
		n.nativeMask = r.nativeSample
		n.maskCached = r.brushMeta.sampleCached
		n.maskVisual = r.brushMeta.visual
		n.maskGradient = r.brushMeta.gradient
		n.maskImage = r.brushMeta.image
	}
	switch value := element.(type) {
	case *Canvas:
		n.children, err = r.prepare(value.Elements, transform, aliased, depth+1)
	case *Path:
		if value.Fill != nil {
			region, e := r.fill(value.Data, transform, aliased)
			if e != nil {
				return nil, e
			}
			sample, e := r.brush(value.Fill, transform, aliased, depth)
			if e != nil {
				return nil, e
			}
			meta := r.brushMeta
			n.paints = append(n.paints, scenePaint{regions: []rasterRegion{region}, sample: sample, sampleCached: meta.sampleCached, aliased: aliased, native: r.nativeSample, solid: meta.solid, solidColor: meta.solidColor, gradient: meta.gradient, image: meta.image, visual: meta.visual})
		}
		if value.Stroke != nil {
			if err := r.geometryWork(value.Data); err != nil {
				return nil, err
			}
			edges, e := pathStrokeEdges(value, transform, r.options.tolerance, r.edges)
			if e != nil {
				return nil, e
			}
			r.edges -= len(edges)
			region, e := r.region(edges, GeometryNonZero, aliased)
			if e != nil {
				return nil, e
			}
			sample, e := r.brush(value.Stroke, transform, aliased, depth)
			if e != nil {
				return nil, e
			}
			meta := r.brushMeta
			n.paints = append(n.paints, scenePaint{regions: []rasterRegion{region}, sample: sample, sampleCached: meta.sampleCached, aliased: aliased, native: r.nativeSample, solid: meta.solid, solidColor: meta.solidColor, gradient: meta.gradient, image: meta.image, visual: meta.visual})
		}
	case *Glyphs:
		n.paints, err = r.glyphPaint(value, transform, aliased, depth)
	}
	if err != nil {
		return nil, err
	}
	for i := range n.paints {
		var paintBounds image.Rectangle
		if len(n.paints[i].regions) > 1 {
			n.paints[i].regionBounds = make([]image.Rectangle, len(n.paints[i].regions))
		}
		for j, region := range n.paints[i].regions {
			rb := r.regionBounds(region, n.paints[i].aliased)
			if n.paints[i].regionBounds != nil {
				n.paints[i].regionBounds[j] = rb
			}
			paintBounds = paintBounds.Union(rb)
		}
		n.paints[i].bounds = paintBounds
		n.bounds = n.bounds.Union(paintBounds)
	}
	for _, child := range n.children {
		n.bounds = n.bounds.Union(child.bounds)
	}
	if n.clip != nil {
		n.bounds = n.bounds.Intersect(r.regionBounds(*n.clip, aliased))
	}
	return n, nil
}

// regionBounds 计算区域在输出像素空间的保守范围，仅用于图块剔除
// 入参: region 已准备的区域, aliased 边集是否使用输出像素坐标
// 返回: image.Rectangle 向外取整并限制到可寻址坐标的范围
func (r *sceneRenderer) regionBounds(region rasterRegion, aliased bool) image.Rectangle {
	if len(region.edges) == 0 {
		return image.Rectangle{}
	}
	lo, hi := region.edges[0].start, region.edges[0].start
	for _, edge := range region.edges {
		lo.X, lo.Y = min(lo.X, edge.start.X, edge.end.X), min(lo.Y, edge.start.Y, edge.end.Y)
		hi.X, hi.Y = max(hi.X, edge.start.X, edge.end.X), max(hi.Y, edge.start.Y, edge.end.Y)
	}
	scale := 1.0
	if !aliased {
		scale = float64(r.options.samples)
	}
	bound := func(value float64) int { return int(max(float64(-1<<30), min(float64(1<<30), value))) }
	return image.Rect(bound(math.Floor(lo.X/scale)), bound(math.Floor(lo.Y/scale)), bound(math.Ceil(hi.X/scale)), bound(math.Ceil(hi.Y/scale)))
}

// geometryWork 将输入几何规模计入共享准备预算，包括不产生可见边的线段
// 入参: geometry 输入几何
// 返回: error 缺失几何或预算不足错误
func (r *sceneRenderer) geometryWork(geometry *Geometry) error {
	if geometry == nil {
		return fmt.Errorf("%w: missing scene geometry", ErrInvalid)
	}
	if err := r.charge(uint64(len(geometry.Figures))); err != nil {
		return err
	}
	for _, figure := range geometry.Figures {
		if err := r.charge(uint64(len(figure.Segments))); err != nil {
			return err
		}
	}
	return nil
}

// fill 将填充或裁剪几何转换为独立采样区域
// 入参: geometry 输入几何, transform 有效设备变换, aliased 是否按输出像素中心判断归属
// 返回: rasterRegion 采样空间区域, error 几何或资源错误
func (r *sceneRenderer) fill(geometry *Geometry, transform Matrix, aliased bool) (rasterRegion, error) {
	if err := r.geometryWork(geometry); err != nil {
		return rasterRegion{}, err
	}
	edges, err := geometryFillEdges(geometry, transform, r.options.tolerance, r.edges)
	if err != nil {
		return rasterRegion{}, err
	}
	r.edges -= len(edges)
	return r.region(edges, geometry.FillRule, aliased)
}

// region 将独立边集转换到子像素空间，标称描边宽度已在输出设备空间确定
// 入参: edges 本次调用独占的设备边集, rule 填充规则, aliased 是否保留输出像素坐标
// 返回: rasterRegion 采样区域, error 坐标范围错误
func (r *sceneRenderer) region(edges []geometryEdge, rule GeometryFillRule, aliased bool) (rasterRegion, error) {
	if !aliased {
		scale := float64(r.options.samples)
		for i := range edges {
			edges[i].start.X *= scale
			edges[i].start.Y *= scale
			edges[i].end.X *= scale
			edges[i].end.Y *= scale
			if !geometryFinite(edges[i].start.X, edges[i].start.Y, edges[i].end.X, edges[i].end.Y) {
				return rasterRegion{}, fmt.Errorf("%w: scene sampling coordinates", ErrLimit)
			}
		}
	}
	return rasterRegion{edges, rule}, nil
}

// brush 创建使用输出设备坐标的画刷采样器，保留渐变插值空间与合成空间的区别
// 入参: brush 输入画刷, transform 所属元素的有效设备变换, aliased 继承的边缘模式, depth 当前元素深度
// 返回: sceneSample 颜色采样器, error 画刷或能力错误
func (r *sceneRenderer) brush(brush *Brush, transform Matrix, aliased bool, depth int) (sceneSample, error) {
	return r.brushMode(brush, transform, aliased, depth, false)
}

// brushMode 按是否用于透明度掩模创建画刷采样器，透明度掩模图像画刷仅读取透明度通道
// 入参: brush 输入画刷, transform 所属元素的有效设备变换, aliased 继承的边缘模式, depth 当前元素深度, maskOnly 是否仅需透明度掩模
// 返回: sceneSample 颜色采样器, error 画刷或能力错误
func (r *sceneRenderer) brushMode(brush *Brush, transform Matrix, aliased bool, depth int, maskOnly bool) (sceneSample, error) {
	r.nativeSample = nil
	r.brushMeta = sceneBrushMeta{}
	if r.printRuntime != nil {
		native, err := r.printRuntime.brush(brush, transform, aliased, depth)
		if err != nil {
			return nil, err
		}
		r.nativeSample = native
		if brush != nil && brush.Kind != BrushSolidColor && brush.Kind != BrushLinearGradient && brush.Kind != BrushRadialGradient {
			r.brushMeta = sceneBrushMeta{visual: true}
			r.hasFiltered = true
			if brush.Kind == BrushImage || brush.Kind == BrushVisual {
				r.visualCount++
			}
		}
		return r.printRuntime.previewSample(native), nil
	}
	if brush == nil || !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 {
		return nil, fmt.Errorf("%w: scene brush", ErrInvalid)
	}
	if err := r.charge(1 + uint64(len(brush.Stops))); err != nil {
		return nil, err
	}
	space := r.options.space
	switch brush.Kind {
	case BrushSolidColor:
		color, err := r.color(brush.Part, brush.Color)
		if err != nil {
			return nil, err
		}
		c, err := renderColorFromColor(color, space)
		if err != nil {
			return nil, err
		}
		c, err = renderColorModulate(c, brush.Opacity, 1)
		if err != nil {
			return nil, err
		}
		r.brushMeta = sceneBrushMeta{solid: true, solidColor: c}
		return func(Point, Point) (renderColor, error) { return c, nil }, nil
	case BrushLinearGradient, BrushRadialGradient:
		brush, err := r.gradientBrush(brush)
		if err != nil {
			return nil, err
		}
		sampler, err := newGradientSampler(brush, transform)
		if err != nil {
			return nil, err
		}
		r.brushMeta = sceneBrushMeta{gradient: sampler}
		return func(point, _ Point) (renderColor, error) {
			return sampler.sampleRenderColor(point, space)
		}, nil
	case BrushImage:
		if r.options.image == nil {
			return nil, fmt.Errorf("%w: scene image source is unavailable", ErrUnsupported)
		}
		data, err := r.options.image(brush)
		if err != nil {
			return nil, err
		}
		sourceIntent := IntentDefault
		if r.options.device != nil {
			sourceIntent = r.options.device.sourceIntent
		}
		sampler, err := newImageSampler(brush, data, transform, space, maskOnly, sourceIntent, r.options.hdrPeakNits)
		if err != nil {
			return nil, err
		}
		sampler.charge = r.charge
		sampler.reserve = r.reservePixels
		sampler.release = r.releaseLive
		if sampler.filterX || sampler.filterY {
			r.hasFiltered = true
		}
		r.registerCleanup(sampler.releaseFilter)
		cached := func(point, center Point, cache *imageSampleCache) (renderColor, error) {
			return sampler.sampleAtCached(point, center, cache, r.concurrent)
		}
		r.brushMeta = sceneBrushMeta{image: sampler, sampleCached: cached}
		return func(point, center Point) (renderColor, error) {
			if !r.concurrent {
				return sampler.sampleAt(point, center)
			}
			return sampler.sampleAtPooled(point, center)
		}, nil
	case BrushVisual:
		sample, err := r.visualBrush(brush, transform, aliased, depth)
		if err != nil {
			return nil, err
		}
		cached := r.brushMeta.sampleCached
		r.visualCount++
		r.hasFiltered = true
		r.brushMeta = sceneBrushMeta{visual: true, sampleCached: cached}
		return sample, nil
	default:
		return nil, fmt.Errorf("%w: scene brush kind %d", ErrUnsupported, brush.Kind)
	}
}

// acquireSurface 在严格扣除存活像素预算后从对象池租用图块表面
// 入参: bounds 子像素范围
// 返回: *renderSurface 可复用透明表面, error 预算或参数错误
func (r *sceneRenderer) acquireSurface(bounds image.Rectangle) (*renderSurface, error) {
	count, err := validateRenderSurface(bounds, r.options.space, r.options.pixels)
	if err != nil {
		return nil, err
	}
	if err := r.reservePixels(count); err != nil {
		return nil, err
	}
	surface := allocRenderSurface(bounds, r.options.space, count)
	surface.reserved = count
	return surface, nil
}

// releaseSurface 归还图块表面到对象池并按原始预留容量精确释放存活像素预算
// 入参: surface 待释放的表面
func (r *sceneRenderer) releaseSurface(surface *renderSurface) {
	if surface == nil {
		return
	}
	count := surface.reserved
	surface.reserved = 0
	releaseRenderSurface(surface)
	r.releaseLive(count)
}

// releaseLive 线程安全地归还已释放的存活像素预算
// 入参: count 已释放的像素数
func (r *sceneRenderer) releaseLive(count int) {
	if count == 0 {
		return
	}
	if r.concurrent {
		r.budgetMu.Lock()
		r.live -= count
		r.budgetMu.Unlock()
		return
	}
	r.live -= count
}

// registerCleanup 线程安全地登记单次绘制结束时执行的资源与存活像素预算清理回调
// 入参: fn 清理回调
func (r *sceneRenderer) registerCleanup(fn func()) {
	if fn == nil {
		return
	}
	if r.concurrent {
		r.budgetMu.Lock()
		r.cleanups = append(r.cleanups, fn)
		r.budgetMu.Unlock()
		return
	}
	r.cleanups = append(r.cleanups, fn)
}

// cleanup 逆序执行已登记的过滤缓存清理回调并归还全部临时存活像素预算
func (r *sceneRenderer) cleanup() {
	for i := len(r.cleanups) - 1; i >= 0; i-- {
		r.cleanups[i]()
	}
	r.cleanups = nil
}

// reservePixels 线程安全地扣减同时存活的像素预算，与隔离表面及预乘缓存共用限额
// 入参: count 待保留的像素数
// 返回: error 像素容量不足错误
func (r *sceneRenderer) reservePixels(count int) error {
	if r.concurrent {
		r.budgetMu.Lock()
		if count < 0 || count > r.options.pixels-r.live {
			r.budgetMu.Unlock()
			return fmt.Errorf("%w: scene live pixel budget", ErrLimit)
		}
		r.live += count
		r.budgetMu.Unlock()
		return nil
	}
	if count < 0 || count > r.options.pixels-r.live {
		return fmt.Errorf("%w: scene live pixel budget", ErrLimit)
	}
	r.live += count
	return nil
}

// acquireIsolatedSurface 在严格检查存活像素预算后按嵌套深度复用工作Goroutine的隔离表面
// 入参: bounds 子像素范围, depth 当前隔离嵌套深度, worker 工作Goroutine独占状态
// 返回: *renderSurface 已清零的隔离表面, error 预算或参数错误
func (r *sceneRenderer) acquireIsolatedSurface(bounds image.Rectangle, depth int, worker *sceneWorkerState) (*renderSurface, error) {
	count, err := validateRenderSurface(bounds, r.options.space, r.options.pixels)
	if err != nil {
		return nil, err
	}
	if err := r.reservePixels(count); err != nil {
		return nil, err
	}
	for len(worker.isolated) <= depth {
		worker.isolated = append(worker.isolated, nil)
	}
	surface := worker.isolated[depth]
	if surface != nil && cap(surface.pixels) >= count {
		surface.bounds = bounds
		surface.space = r.options.space
		surface.pixels = surface.pixels[:count]
		surface.reserved = count
		clear(surface.pixels)
		return surface, nil
	}
	if surface != nil {
		releaseRenderSurface(surface)
		worker.isolated[depth] = nil
	}
	surface = allocRenderSurface(bounds, r.options.space, count)
	surface.reserved = count
	worker.isolated[depth] = surface
	return surface, nil
}

// tile 绘制独立图块并在预乘空间降采样，图块边缘不改变全局采样坐标
// 入参: nodes 已准备的根节点, surface 本次绘制复用的图块表面, output 输出图像, bounds 输出像素范围, worker 工作Goroutine独占状态
// 返回: error 绘制或颜色转换错误
func (r *sceneRenderer) tile(nodes []*sceneNode, surface *renderSurface, output *image.NRGBA, bounds image.Rectangle, worker *sceneWorkerState) error {
	samples := r.options.samples
	surface.bounds = image.Rect(bounds.Min.X*samples, bounds.Min.Y*samples, bounds.Max.X*samples, bounds.Max.Y*samples)
	surface.pixels = surface.pixels[:surface.bounds.Dx()*surface.bounds.Dy()]
	touched := false
	if r.options.background != (renderColor{}) {
		if err := r.charge(uint64(len(surface.pixels))); err != nil {
			return err
		}
		bg := r.options.background
		for i := range surface.pixels {
			surface.pixels[i] = bg
		}
		touched = true
	} else {
		clear(surface.pixels)
	}
	subClip := surface.bounds
	if r.options.pageSubClip != nil {
		subClip = subClip.Intersect(*r.options.pageSubClip)
	}
	if !subClip.Empty() {
		for _, node := range nodes {
			if node.opacity != 0 && node.bounds.Overlaps(bounds) {
				touched = true
			}
			if err := r.draw(node, surface, bounds, subClip, 0, worker); err != nil {
				return err
			}
		}
	}
	if err := r.charge(uint64(len(surface.pixels))); err != nil {
		return err
	}
	if r.options.outputColor == PrintColorGrayscale || r.options.outputColor == PrintColorMonochrome {
		if err := r.charge(uint64(bounds.Dx()) * uint64(bounds.Dy())); err != nil {
			return err
		}
	}
	if !touched && r.options.device == nil {
		return nil
	}
	surfStride := surface.bounds.Dx()
	width := bounds.Dx()
	factor := 1 / float64(samples*samples)
	if r.options.device != nil {
		tilePixels := uint64(width) * uint64(bounds.Dy())
		hi, lo := bits.Mul64(tilePixels, r.options.device.pixelWork)
		if hi != 0 {
			return fmt.Errorf("%w: scene work budget", ErrLimit)
		}
		if err := r.charge(lo); err != nil {
			return err
		}
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			rowBase := (y - bounds.Min.Y) * samples * surfStride
			for x := bounds.Min.X; x < bounds.Max.X; x++ {
				colBase := (x - bounds.Min.X) * samples
				var c renderColor
				if samples == 1 {
					c = surface.pixels[rowBase+colBase]
				} else {
					for j := range samples {
						row := surface.pixels[rowBase+j*surfStride+colBase : rowBase+j*surfStride+colBase+samples]
						for _, p := range row {
							c.r += p.r * factor
							c.g += p.g * factor
							c.b += p.b * factor
							c.a += p.a * factor
						}
					}
				}
				if err := r.options.device.pixel(x, y, c, r.options.space, r.options.outputColor); err != nil {
					return err
				}
			}
		}
		return nil
	}
	fastSRGB := r.options.space == renderSRGB && r.options.outputColor != PrintColorGrayscale && r.options.outputColor != PrintColorMonochrome
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		rowBase := (y - bounds.Min.Y) * samples * surfStride
		outOff := (y-output.Rect.Min.Y)*output.Stride + (bounds.Min.X-output.Rect.Min.X)*4
		outRow := output.Pix[outOff : outOff+width*4]
		for col := range width {
			colBase := col * samples
			var c renderColor
			if samples == 1 {
				c = surface.pixels[rowBase+colBase]
			} else {
				for j := range samples {
					row := surface.pixels[rowBase+j*surfStride+colBase : rowBase+j*surfStride+colBase+samples]
					for _, p := range row {
						c.r += p.r * factor
						c.g += p.g * factor
						c.b += p.b * factor
						c.a += p.a * factor
					}
				}
			}
			if c == (renderColor{}) {
				continue
			}
			var outColor color.NRGBA
			if fastSRGB {
				if err := c.validate(); err != nil {
					return err
				}
				alpha := uint8(math.Floor(c.a*255 + 0.5))
				if alpha == 0 {
					continue
				}
				rv, gv, bv := c.r, c.g, c.b
				if rv <= 0 {
					rv = 0
				} else if rv >= c.a {
					rv = 1
				} else {
					rv /= c.a
				}
				if gv <= 0 {
					gv = 0
				} else if gv >= c.a {
					gv = 1
				} else {
					gv /= c.a
				}
				if bv <= 0 {
					bv = 0
				} else if bv >= c.a {
					bv = 1
				} else {
					bv /= c.a
				}
				outColor = color.NRGBA{
					R: uint8(math.Floor(colorClamp(rv)*255 + 0.5)),
					G: uint8(math.Floor(colorClamp(gv)*255 + 0.5)),
					B: uint8(math.Floor(colorClamp(bv)*255 + 0.5)),
					A: alpha,
				}
			} else {
				var err error
				if r.options.space == renderScRGB && r.options.hdrPeakNits > 0 {
					outColor, err = renderColorToNRGBAToneMapped(c, r.options.hdrPeakNits)
				} else {
					outColor, err = renderColorToNRGBA(c, r.options.space)
				}
				if err != nil {
					return err
				}
				if r.options.outputColor == PrintColorGrayscale || r.options.outputColor == PrintColorMonochrome {
					outColor, err = renderPrintOutputColor(outColor, r.options.outputColor)
					if err != nil {
						return err
					}
				}
			}
			dstOff := col * 4
			outRow[dstOff] = outColor.R
			outRow[dstOff+1] = outColor.G
			outRow[dstOff+2] = outColor.B
			outRow[dstOff+3] = outColor.A
		}
	}
	return nil
}

// sceneRegionEdgeCost 统计区域内落入当前图块纵范围的非水平边数，用于按实际扫描规模计费
// 入参: region 采样空间区域, minY 图块纵范围下界, maxY 图块纵范围上界
// 返回: uint64 落入当前图块纵范围的边数
func sceneRegionEdgeCost(region rasterRegion, minY, maxY float64) uint64 {
	var count uint64
	for _, edge := range region.edges {
		lo, hi := edge.start.Y, edge.end.Y
		if lo == hi {
			continue
		}
		if lo > hi {
			lo, hi = hi, lo
		}
		if lo < maxY && hi > minY {
			count++
		}
	}
	return count
}

// draw 先完成节点内部绘制，再施加节点裁剪、透明度掩模及整体透明度
// 入参: node 绘制节点, target 背景表面, bounds 输出像素范围, subClip 有效子像素半开裁剪范围, isoDepth 当前隔离嵌套深度, worker 工作Goroutine独占状态
// 返回: error 带部件位置的绘制错误
func (r *sceneRenderer) draw(node *sceneNode, target *renderSurface, bounds, subClip image.Rectangle, isoDepth int, worker *sceneWorkerState) (err error) {
	defer func() {
		if err != nil {
			err = wrapPartError(node.part, node.kind, err)
		}
	}()
	if err := r.charge(1); err != nil {
		return err
	}
	nodeTile := node.bounds.Intersect(bounds)
	if node.opacity == 0 || nodeTile.Empty() || subClip.Empty() {
		return nil
	}
	samples := r.options.samples
	isolated := node.opacity != 1 || node.mask != nil || node.clip != nil || node.negative
	surface := target
	nextDepth := isoDepth
	drawBounds := bounds
	childClip := subClip
	if isolated {
		isoBounds := image.Rect(nodeTile.Min.X*samples, nodeTile.Min.Y*samples, nodeTile.Max.X*samples, nodeTile.Max.Y*samples).Intersect(subClip)
		if isoBounds.Empty() {
			return nil
		}
		surface, err = r.acquireIsolatedSurface(isoBounds, isoDepth, worker)
		if err != nil {
			return err
		}
		defer func() {
			count := surface.reserved
			surface.reserved = 0
			r.releaseLive(count)
		}()
		nextDepth = isoDepth + 1
		drawBounds = nodeTile
		childClip = isoBounds
	}
	scale := float64(samples)
	for _, paint := range node.paints {
		paintTile := paint.bounds.Intersect(drawBounds)
		if paintTile.Empty() {
			continue
		}
		subBounds := image.Rect(paintTile.Min.X*samples, paintTile.Min.Y*samples, paintTile.Max.X*samples, paintTile.Max.Y*samples).Intersect(childClip)
		if subBounds.Empty() {
			continue
		}
		regions := paint.regions
		if len(paint.regionBounds) == len(paint.regions) {
			filtered := worker.regions[:0]
			for i, rb := range paint.regionBounds {
				if rb.Overlaps(paintTile) {
					filtered = append(filtered, paint.regions[i])
				}
			}
			worker.regions = filtered
			if len(filtered) == 0 {
				continue
			}
			regions = filtered
		}
		minY, maxY := float64(subBounds.Min.Y), float64(subBounds.Max.Y)
		if paint.aliased {
			minY, maxY = float64(paintTile.Min.Y), float64(paintTile.Max.Y)
		}
		var edgeCost uint64
		for _, region := range regions {
			edgeCost += sceneRegionEdgeCost(region, minY, maxY)
		}
		if err := r.charge(uint64(subBounds.Dx())*uint64(subBounds.Dy()) + edgeCost); err != nil {
			return err
		}
		mask, err := r.coverageScratch(regions, paint.aliased, subBounds, &worker.mask, worker)
		if err != nil {
			return err
		}
		switch {
		case paint.solid:
			err = surface.paintBinarySolid(mask, paint.solidColor)
		case paint.gradient != nil:
			err = surface.paintBinaryGradient(mask, scale, paint.gradient)
		case paint.image != nil:
			err = surface.paintBinaryImage(mask, scale, paint.image, &worker.imageCache, r.concurrent)
		case paint.sampleCached != nil:
			var lock *sync.Mutex
			if paint.visual && r.concurrent {
				lock = &r.visualMu
			}
			err = surface.paintBinarySampleCached(mask, scale, paint.sampleCached, &worker.imageCache, lock)
		default:
			var lock *sync.Mutex
			if paint.visual && r.concurrent {
				lock = &r.visualMu
			}
			err = surface.paintBinarySample(mask, scale, paint.sample, lock)
		}
		if err != nil {
			return err
		}
	}
	for _, child := range node.children {
		if err := r.draw(child, surface, drawBounds, childClip, nextDepth, worker); err != nil {
			return err
		}
	}
	if node.negative {
		if err := r.negative(surface); err != nil {
			return err
		}
	}
	if !isolated {
		return nil
	}
	return r.composite(node, surface, target, drawBounds, worker)
}

// coverageScratch 生成统一采样空间的二值掩模并复用工作Goroutine的扫描与字节缓冲，支持非对齐子像素裁剪范围
// 入参: regions 取并集的绘制区域, aliased 是否使用输出像素中心, bounds 子像素裁剪范围, dst 输出掩模缓冲, worker 工作Goroutine独占状态
// 返回: *image.Alpha 仅含零和满覆盖的掩模, error 光栅化错误
func (r *sceneRenderer) coverageScratch(regions []rasterRegion, aliased bool, bounds image.Rectangle, dst *image.Alpha, worker *sceneWorkerState) (*image.Alpha, error) {
	samples := r.options.samples
	coarse := bounds
	if aliased {
		coarse = image.Rect(renderFloorDiv(bounds.Min.X, samples), renderFloorDiv(bounds.Min.Y, samples), renderCeilDiv(bounds.Max.X, samples), renderCeilDiv(bounds.Max.Y, samples))
	}
	scratch := &worker.raster
	coarseDst := dst
	if aliased && samples != 1 {
		coarseDst = &worker.coarse
	}
	partDst := &worker.part
	maxPixels := max(uint64(rasterMaxPixels), uint64(max(0, r.options.pixels)))
	maxEdges := max(rasterMaxEdges, r.options.edges)
	maxWork := max(uint64(rasterMaxWork), r.options.work)
	var mask *image.Alpha
	for first := 0; first < len(regions) || mask == nil; first += rasterMaxRegions {
		last := min(first+rasterMaxRegions, len(regions))
		target := partDst
		if mask == nil {
			target = coarseDst
		}
		part, err := rasterRegionsCoverageBudget(regions[first:last], coarse, true, 1, maxPixels, maxEdges, maxWork, target, scratch)
		if err != nil {
			return nil, err
		}
		if mask == nil {
			mask = part
		} else {
			for i, value := range part.Pix {
				mask.Pix[i] |= value
			}
		}
	}
	if !aliased || samples == 1 {
		return mask, nil
	}
	count := bounds.Dx() * bounds.Dy()
	if cap(dst.Pix) < count {
		dst.Pix = make([]byte, count)
	} else {
		dst.Pix = dst.Pix[:count]
	}
	dst.Stride = bounds.Dx()
	dst.Rect = bounds
	full := dst
	cw, ch := coarse.Dx(), coarse.Dy()
	fullStride := full.Stride
	for cy := range ch {
		gy := coarse.Min.Y + cy
		yStart := max(bounds.Min.Y, gy*samples)
		yEnd := min(bounds.Max.Y, (gy+1)*samples)
		if yStart >= yEnd {
			continue
		}
		srcRow := mask.Pix[cy*mask.Stride : cy*mask.Stride+cw]
		firstRowOff := (yStart - bounds.Min.Y) * fullStride
		firstRow := full.Pix[firstRowOff : firstRowOff+fullStride]
		for cx, value := range srcRow {
			gx := coarse.Min.X + cx
			xStart := max(bounds.Min.X, gx*samples) - bounds.Min.X
			xEnd := min(bounds.Max.X, (gx+1)*samples) - bounds.Min.X
			for x := xStart; x < xEnd; x++ {
				firstRow[x] = value
			}
		}
		for y := yStart + 1; y < yEnd; y++ {
			dstOff := (y - bounds.Min.Y) * fullStride
			copy(full.Pix[dstOff:dstOff+fullStride], firstRow)
		}
	}
	return full, nil
}

// composite 在统一采样位置施加裁剪及画刷掩模，不量化中间透明度
// 入参: node 隔离节点, source 内部绘制完成的表面, target 背景表面, bounds 当前图块输出像素范围, worker 工作Goroutine独占状态
// 返回: error 裁剪、采样或合成错误
func (r *sceneRenderer) composite(node *sceneNode, source, target *renderSurface, bounds image.Rectangle, worker *sceneWorkerState) error {
	samples := r.options.samples
	compTile := node.bounds.Intersect(bounds)
	if compTile.Empty() {
		return nil
	}
	subBounds := image.Rect(compTile.Min.X*samples, compTile.Min.Y*samples, compTile.Max.X*samples, compTile.Max.Y*samples).Intersect(source.bounds).Intersect(target.bounds)
	if subBounds.Empty() {
		return nil
	}
	cost := uint64(subBounds.Dx()) * uint64(subBounds.Dy())
	if node.clip != nil {
		minY, maxY := float64(subBounds.Min.Y), float64(subBounds.Max.Y)
		if node.aliased {
			minY, maxY = float64(compTile.Min.Y), float64(compTile.Max.Y)
		}
		cost += sceneRegionEdgeCost(*node.clip, minY, maxY)
	}
	if err := r.charge(cost); err != nil {
		return err
	}
	var clip *image.Alpha
	if node.clip != nil {
		var err error
		clip, err = r.coverageScratch([]rasterRegion{*node.clip}, node.aliased, subBounds, &worker.clip, worker)
		if err != nil {
			return err
		}
	}
	width := subBounds.Dx()
	srcStride := source.bounds.Dx()
	srcColOff := subBounds.Min.X - source.bounds.Min.X
	dstStride := target.bounds.Dx()
	dstColOff := subBounds.Min.X - target.bounds.Min.X
	scale := float64(samples)
	if node.mask == nil && node.opacity == 1 && r.options.space == renderSRGB {
		for y := subBounds.Min.Y; y < subBounds.Max.Y; y++ {
			sOff := (y-source.bounds.Min.Y)*srcStride + srcColOff
			tOff := (y-target.bounds.Min.Y)*dstStride + dstColOff
			srcRow := source.pixels[sOff : sOff+width]
			dstRow := target.pixels[tOff : tOff+width]
			if clip != nil {
				cOff := (y-clip.Rect.Min.Y)*clip.Stride + (subBounds.Min.X - clip.Rect.Min.X)
				clipRow := clip.Pix[cOff : cOff+width]
				for col, m := range clipRow {
					if m == 0 {
						continue
					}
					src := srcRow[col]
					if src.a == 0 {
						continue
					}
					if src.a == 1 {
						dstRow[col] = src
					} else {
						rem := 1 - src.a
						dst := dstRow[col]
						dstRow[col] = renderColor{src.r + dst.r*rem, src.g + dst.g*rem, src.b + dst.b*rem, src.a + dst.a*rem}
					}
				}
			} else {
				for col, src := range srcRow {
					if src.a == 0 {
						continue
					}
					if src.a == 1 {
						dstRow[col] = src
					} else {
						rem := 1 - src.a
						dst := dstRow[col]
						dstRow[col] = renderColor{src.r + dst.r*rem, src.g + dst.g*rem, src.b + dst.b*rem, src.a + dst.a*rem}
					}
				}
			}
		}
		return nil
	}
	if node.maskImage != nil {
		worker.imageCache.valid = false
	}
	visualLocked := false
	if node.mask != nil && node.maskVisual && r.concurrent {
		defer func() {
			if visualLocked {
				r.visualMu.Unlock()
			}
		}()
	}
	for y := subBounds.Min.Y; y < subBounds.Max.Y; y++ {
		sOff := (y-source.bounds.Min.Y)*srcStride + srcColOff
		tOff := (y-target.bounds.Min.Y)*dstStride + dstColOff
		srcRow := source.pixels[sOff : sOff+width]
		dstRow := target.pixels[tOff : tOff+width]
		var clipRow []byte
		if clip != nil {
			cOff := (y-clip.Rect.Min.Y)*clip.Stride + (subBounds.Min.X - clip.Rect.Min.X)
			clipRow = clip.Pix[cOff : cOff+width]
		}
		py := (float64(y) + 0.5) / scale
		cy := math.Floor(py) + 0.5
		for col := range width {
			src := srcRow[col]
			if src.a == 0 || clipRow != nil && clipRow[col] == 0 {
				continue
			}
			alpha := 1.0
			if node.mask != nil {
				px := (float64(subBounds.Min.X+col) + 0.5) / scale
				point := Point{px, py}
				var c renderColor
				var err error
				switch {
				case node.maskGradient != nil:
					c, err = node.maskGradient.sampleRenderColor(point, r.options.space)
				case node.maskImage != nil:
					c, err = node.maskImage.sampleAtCached(point, Point{math.Floor(px) + 0.5, cy}, &worker.imageCache, r.concurrent)
				case node.maskVisual && r.concurrent:
					if !visualLocked {
						r.visualMu.Lock()
						visualLocked = true
					}
					if node.maskCached != nil {
						c, err = node.maskCached(point, Point{math.Floor(px) + 0.5, cy}, &worker.imageCache)
					} else {
						c, err = node.mask(point, Point{math.Floor(px) + 0.5, cy})
					}
				case node.maskCached != nil:
					c, err = node.maskCached(point, Point{math.Floor(px) + 0.5, cy}, &worker.imageCache)
				default:
					c, err = node.mask(point, Point{math.Floor(px) + 0.5, cy})
				}
				if err != nil {
					return err
				}
				alpha = c.a
			}
			c, err := renderColorModulate(src, node.opacity, alpha)
			if err != nil {
				return err
			}
			c, err = renderSourceOver(c, dstRow[col])
			if err != nil {
				return err
			}
			dstRow[col] = c
		}
	}
	return nil
}
