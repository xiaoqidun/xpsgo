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
	"bytes"
	"context"
	"encoding/xml"
	"fmt"
	"io"
	"math"
	"net/url"
	"strconv"
	"strings"
)

// EncodeOptions 设置页面、资源字典或释放提示编码的方言、部件名、紧凑输出及资源上限，零值字段采用默认值
// Format未指定时页面编码沿用Page.Format，缺省采用OpenXPS；Part用于EncodeDiscardControl或EncodeResourceDictionary
// Compact启用后连ContextColor实色画刷也按属性简写输出；MaxPartBytes、MaxXMLDepth与MaxXMLNodes分别约束输出字节、嵌套深度与模型展开工作量
type EncodeOptions struct {
	Format  Format
	Limits  Limits
	Part    string
	Compact bool
}

// pageEncoder 构造独立的固定页面或资源字典标记，限制展开工作量、检测引用循环并隔离共享元素与VisualBrush内联命名冲突
type pageEncoder struct {
	format          Format
	ns              string
	part            string
	limits          Limits
	compact         bool
	ctx             context.Context
	active          map[any]bool
	elemCount       map[Element]int
	mainElemCount   map[Element]int
	emittedName     map[Element]bool
	inVisualBrush   int
	prescanWork     int
	work            int
	bytes           int64
	scope           map[string]string
	hasResourceKeys bool
	hasRemoteDict   bool
}

// DefaultEncodeOptions 返回默认编码选项
// 返回: EncodeOptions 编码选项
func DefaultEncodeOptions() EncodeOptions {
	return EncodeOptions{Format: FormatOpenXPS, Limits: DefaultLimits()}
}

// EncodePage 将页面模型编码为UTF-8固定页面XML，不验证外部资源二进制内容，调用期间模型不得修改
// 资源URI按所属模型Part转为页面相对路径，Page.Part为空时以包根为基准，FontPart非空时优先于FontURI
// 入参: ctx 取消Context，nil采用Background, output 输出流, page 页面模型, options 编码选项，nil采用默认值
// 返回: int64 已写字节数，输出失败时可能部分写入, error 模型、资源、取消或写出错误
func EncodePage(ctx context.Context, output io.Writer, page *Page, options *EncodeOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if output == nil || page == nil {
		return 0, fmt.Errorf("%w: missing page or output", ErrInvalid)
	}
	root, limits, err := encodePageRoot(ctx, page, options)
	if err != nil {
		return 0, err
	}
	return writeEncodedXMLNode(ctx, output, root, limits.MaxPartBytes)
}

// encodePageTree 编码并校验页面模型，同时返回已校验XML节点树与UTF-8序列化字节，消除写侧二次解码
// 入参: ctx 取消Context，nil采用Background, page 页面模型, options 编码选项，nil采用默认值
// 返回: *xmlElement 已校验FixedPage根节点, []byte UTF-8页面XML字节, error 模型、资源、取消或编码错误
func encodePageTree(ctx context.Context, page *Page, options *EncodeOptions) (*xmlElement, []byte, error) {
	ctx = normalizeContext(ctx)
	if page == nil {
		return nil, nil, fmt.Errorf("%w: missing page", ErrInvalid)
	}
	root, limits, err := encodePageRoot(ctx, page, options)
	if err != nil {
		return nil, nil, err
	}
	var output bytes.Buffer
	if _, err := writeEncodedXMLNode(ctx, &output, root, limits.MaxPartBytes); err != nil {
		return nil, nil, err
	}
	return root, output.Bytes(), nil
}

// encodePageRoot 构造并校验页面XML节点树，编码期间同步验证视觉、画刷、几何与字形属性并完成资源图检查
// 入参: ctx 已规范化取消Context, page 页面模型, options 编码选项，nil采用默认值
// 返回: *xmlElement 已校验FixedPage根节点, Limits 生效资源上限, error 模型、资源、取消或预算错误
func encodePageRoot(ctx context.Context, page *Page, options *EncodeOptions) (*xmlElement, Limits, error) {
	configuration := EncodeOptions{Format: page.Format, Limits: DefaultLimits()}
	if options != nil {
		if options.Format != FormatUnknown {
			configuration.Format = options.Format
		}
		configuration.Limits = mergeLimits(configuration.Limits, options.Limits)
		configuration.Compact = options.Compact
	}
	if configuration.Format == FormatUnknown {
		configuration.Format = FormatOpenXPS
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return nil, Limits{}, err
	}
	if formatNamespace(configuration.Format) == "" {
		return nil, Limits{}, fmt.Errorf("%w: invalid page format", ErrInvalid)
	}
	p := pageEncoder{format: configuration.Format, ns: formatNamespace(configuration.Format), part: page.Part, limits: configuration.Limits, compact: configuration.Compact, ctx: ctx, active: make(map[any]bool), elemCount: make(map[Element]int), mainElemCount: make(map[Element]int), emittedName: make(map[Element]bool)}
	p.scope = map[string]string{"": p.ns, "xml": xmlNamespace}
	var err error
	if p.part == "" {
		p.part = "/"
	} else if p.part, err = opcPartName(p.part); err != nil {
		return nil, Limits{}, err
	}
	if err := p.prescanPage(page); err != nil {
		return nil, Limits{}, err
	}
	if p.hasResourceKeys {
		p.scope["r"] = p.ns + "/resourcedictionary-key"
	}
	root, err := p.page(page)
	if err != nil {
		return nil, Limits{}, err
	}
	if err := validateFixedStructure(root, p.format); err != nil {
		return nil, Limits{}, err
	}
	if err := validateFixedNames(root, p.format); err != nil {
		return nil, Limits{}, err
	}
	part := p.part
	if part == "/" {
		part = "/FixedPage.fpage"
	}
	graph, err := parseResourceGraphMode(part, root, p.format, p.limits, nil, p.ctx, p.hasRemoteDict)
	if err != nil {
		return nil, Limits{}, err
	}
	if _, err := collectRequiredResources(graph, p.format); err != nil {
		return nil, Limits{}, err
	}
	if err := checkContext(p.ctx); err != nil {
		return nil, Limits{}, err
	}
	return root, p.limits, nil
}

// encodeResourceDictionaryTree 编码并校验独立远程资源字典，同时返回XML节点树与UTF-8序列化字节
// 入参: ctx 取消Context，nil采用Background, dict 资源字典模型，Source必须为空, options 编码选项，nil采用默认值
// 返回: *xmlElement 已校验ResourceDictionary根节点, []byte UTF-8字典XML字节, error 模型、校验、取消或编码错误
func encodeResourceDictionaryTree(ctx context.Context, dict *ResourceDictionary, options *EncodeOptions) (*xmlElement, []byte, error) {
	ctx = normalizeContext(ctx)
	if dict == nil {
		return nil, nil, fmt.Errorf("%w: missing resource dictionary", ErrInvalid)
	}
	root, limits, err := encodeResourceDictionaryRoot(ctx, dict, options)
	if err != nil {
		return nil, nil, err
	}
	var output bytes.Buffer
	if _, err := writeEncodedXMLNode(ctx, &output, root, limits.MaxPartBytes); err != nil {
		return nil, nil, err
	}
	return root, output.Bytes(), nil
}

// encodeResourceDictionaryRoot 构造并校验独立远程资源字典XML节点树
// 入参: ctx 已规范化取消Context, dict 资源字典模型，Source必须为空, options 编码选项，nil采用默认值
// 返回: *xmlElement 已校验ResourceDictionary根节点, Limits 生效资源上限, error 模型、校验、取消或预算错误
func encodeResourceDictionaryRoot(ctx context.Context, dict *ResourceDictionary, options *EncodeOptions) (*xmlElement, Limits, error) {
	if dict.Source != "" {
		return nil, Limits{}, fmt.Errorf("%w: remote resource dictionary cannot specify Source", ErrInvalid)
	}
	configuration := DefaultEncodeOptions()
	if options != nil {
		if options.Format != FormatUnknown {
			configuration.Format = options.Format
		}
		configuration.Limits = mergeLimits(configuration.Limits, options.Limits)
		configuration.Part = options.Part
		configuration.Compact = options.Compact
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return nil, Limits{}, err
	}
	if formatNamespace(configuration.Format) == "" {
		return nil, Limits{}, fmt.Errorf("%w: invalid resource dictionary format", ErrInvalid)
	}
	part := configuration.Part
	var err error
	if part == "" {
		part = "/Resources/Dictionary.dict"
	} else if part, err = opcPartName(part); err != nil {
		return nil, Limits{}, err
	}
	p := pageEncoder{format: configuration.Format, ns: formatNamespace(configuration.Format), part: part, limits: configuration.Limits, compact: configuration.Compact, ctx: ctx, active: make(map[any]bool), elemCount: make(map[Element]int), mainElemCount: make(map[Element]int), emittedName: make(map[Element]bool)}
	p.scope = map[string]string{"": p.ns, "xml": xmlNamespace, "r": p.ns + "/resourcedictionary-key"}
	if err := p.prescanDictionary(dict, 1); err != nil {
		return nil, Limits{}, err
	}
	root, err := p.resourceDictionary(dict, 1, true)
	if err != nil {
		return nil, Limits{}, err
	}
	if err := validateFixedNames(root, p.format); err != nil {
		return nil, Limits{}, err
	}
	checker := &resourceParser{
		format: p.format, limits: p.limits, context: ctx,
		graph:  &resourceGraph{PagePart: part, Bindings: make(map[*xmlElement]map[string]*resourceDefinition), Parts: make(map[*xmlElement]string)},
		remote: make(map[string]*resourceScope),
	}
	if _, err := checker.dictionary(root, part, nil, true, 1); err != nil {
		return nil, Limits{}, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, Limits{}, err
	}
	return root, p.limits, nil
}

// writeEncodedXMLNode 将已校验XML节点树受预算约束地序列化到目标输出流
// 入参: ctx 已规范化取消Context, output 输出流, root 根节点, maxBytes 字节上限
// 返回: int64 已写字节数, error 预算、取消或输出错误
func writeEncodedXMLNode(ctx context.Context, output io.Writer, root *xmlElement, maxBytes int64) (int64, error) {
	counted := packageOutput{writer: output, context: ctx, limit: maxBytes}
	encoder := xml.NewEncoder(&counted)
	if err := encodePageNode(encoder, root, ctx); err != nil {
		return counted.count, err
	}
	if err := encoder.Flush(); err != nil {
		return counted.count, err
	}
	return counted.count, checkContext(ctx)
}

// prescanStep 累计预扫描工作量并检查深度、复杂度与取消信号
// 入参: depth 当前对象图深度
// 返回: error 取消或复杂度错误
func (p *pageEncoder) prescanStep(depth int) error {
	if err := checkContext(p.ctx); err != nil {
		return err
	}
	if depth > p.limits.MaxXMLDepth || p.prescanWork >= p.limits.MaxXMLNodes {
		return fmt.Errorf("%w: page encoding complexity", ErrLimit)
	}
	p.prescanWork++
	return nil
}

// prescanPage 预扫描整页资源字典、元素与VisualBrush指针引用计数，区分正文主树与画刷内联展开位置
// 入参: value 页面模型
// 返回: error 循环引用、复杂度或取消错误
func (p *pageEncoder) prescanPage(value *Page) error {
	if err := p.prescanStep(1); err != nil {
		return err
	}
	if value.Resources != nil {
		if err := p.prescanDictionary(value.Resources, 2); err != nil {
			return err
		}
	}
	for _, element := range value.Elements {
		if err := p.prescanElement(element, 2, false); err != nil {
			return err
		}
	}
	return nil
}

// prescanDictionary 预扫描资源字典中的远程引用标志、内联键标志与嵌套元素循环
// 入参: dict 资源字典, depth 当前深度
// 返回: error 循环引用、复杂度或取消错误
func (p *pageEncoder) prescanDictionary(dict *ResourceDictionary, depth int) error {
	if dict == nil {
		return nil
	}
	if p.active[dict] {
		return fmt.Errorf("%w: cyclic resource dictionary", ErrInvalid)
	}
	if err := p.prescanStep(depth); err != nil {
		return err
	}
	p.active[dict] = true
	defer delete(p.active, dict)
	if dict.Source != "" {
		p.hasRemoteDict = true
		return nil
	}
	if len(dict.Entries) != 0 {
		p.hasResourceKeys = true
	}
	for _, entry := range dict.Entries {
		switch typed := entry.Value.(type) {
		case *Brush:
			if err := p.prescanBrush(typed, depth+1); err != nil {
				return err
			}
		case Element:
			if err := p.prescanElement(typed, depth+1, true); err != nil {
				return err
			}
		}
	}
	return nil
}

// prescanElement 递归统计元素指针在全页与正文主树的出现次数，并检测循环引用
// 入参: value 绘制元素, depth 当前深度, inBrush 是否位于VisualBrush内联展开中
// 返回: error 循环引用、复杂度或取消错误
func (p *pageEncoder) prescanElement(value Element, depth int, inBrush bool) error {
	var props ElementProperties
	switch typed := value.(type) {
	case *Canvas:
		if typed == nil {
			return nil
		}
		props = typed.ElementProperties
	case *Path:
		if typed == nil {
			return nil
		}
		props = typed.ElementProperties
	case *Glyphs:
		if typed == nil {
			return nil
		}
		props = typed.ElementProperties
	default:
		return nil
	}
	if p.active[value] {
		return fmt.Errorf("%w: cyclic drawing model", ErrInvalid)
	}
	if err := p.prescanStep(depth); err != nil {
		return err
	}
	p.active[value] = true
	defer delete(p.active, value)
	p.elemCount[value]++
	if !inBrush {
		p.mainElemCount[value]++
	}
	if err := p.prescanBrush(props.OpacityMask, depth+2); err != nil {
		return err
	}
	switch typed := value.(type) {
	case *Canvas:
		if typed.Resources != nil {
			if err := p.prescanDictionary(typed.Resources, depth+1); err != nil {
				return err
			}
		}
		for _, child := range typed.Elements {
			if err := p.prescanElement(child, depth+1, inBrush); err != nil {
				return err
			}
		}
	case *Path:
		if err := p.prescanBrush(typed.Fill, depth+2); err != nil {
			return err
		}
		if err := p.prescanBrush(typed.Stroke, depth+2); err != nil {
			return err
		}
	case *Glyphs:
		if err := p.prescanBrush(typed.Fill, depth+2); err != nil {
			return err
		}
	}
	return nil
}

// prescanBrush 预扫描画刷中的VisualBrush子树并检测画刷循环引用
// 入参: value 画刷模型, depth 当前深度
// 返回: error 循环引用、复杂度或取消错误
func (p *pageEncoder) prescanBrush(value *Brush, depth int) error {
	if value == nil {
		return nil
	}
	if p.active[value] {
		return fmt.Errorf("%w: cyclic brush model", ErrInvalid)
	}
	p.active[value] = true
	defer delete(p.active, value)
	if value.Kind == BrushVisual && value.Visual != nil {
		return p.prescanElement(value.Visual, depth+2, true)
	}
	return nil
}

// step 累计一次模型展开工作，不以共享对象数量代替实际输出复杂度
// 入参: depth 当前XML深度
// 返回: error 取消或复杂度错误
func (p *pageEncoder) step(depth int) error {
	if err := checkContext(p.ctx); err != nil {
		return err
	}
	if depth > p.limits.MaxXMLDepth || p.work >= p.limits.MaxXMLNodes {
		return fmt.Errorf("%w: page encoding complexity", ErrLimit)
	}
	p.work++
	return nil
}

// node 创建具有正确展开名称的元素，声明词法命名空间由最终写出步骤统一处理
// 入参: name 元素名称, depth 元素深度
// 返回: *xmlElement 新元素, error 取消或复杂度错误
func (p *pageEncoder) node(name string, depth int) (*xmlElement, error) {
	if err := p.step(depth); err != nil {
		return nil, err
	}
	if err := p.reserve(int64(len(name)*2 + 5)); err != nil {
		return nil, err
	}
	return &xmlElement{Name: xml.Name{Space: p.ns, Local: name}, Namespaces: p.scope}, nil
}

// reserve 累计编码后的字节量，不在输出前消耗调用方的Writer
// 入参: size 待计入的字节数
// 返回: error 字节预算错误
func (p *pageEncoder) reserve(size int64) error {
	if size > p.limits.MaxPartBytes-p.bytes {
		return fmt.Errorf("%w: page encoding byte budget", ErrLimit)
	}
	p.bytes += size
	return nil
}

// attribute 添加经字符检查的属性并累计实际转义字节量，不允许编码器替换非法字符
// 入参: node 属性所属节点, name 属性展开名称, value 属性值
// 返回: error 字符或字节预算错误
func (p *pageEncoder) attribute(node *xmlElement, name xml.Name, value string) error {
	if !xmlTextValid(value) {
		return fmt.Errorf("%w: invalid XML text in %s", ErrInvalid, name.Local)
	}
	size := int64(len(value))
	for _, character := range value {
		switch character {
		case '&', '\'', '"', '\t', '\n', '\r':
			size += 4
		case '<', '>':
			size += 3
		}
	}
	size += int64(len(name.Local) + 4)
	switch name.Space {
	case "":
	case xmlNamespace:
		size += 4
	case xmlnsNamespace:
		size += 6
	case p.ns + "/resourcedictionary-key":
		size += 2
	default:
		return fmt.Errorf("%w: encoding attribute namespace", ErrInvalid)
	}
	if err := p.reserve(size); err != nil {
		return err
	}
	node.Attr = append(node.Attr, xml.Attr{Name: name, Value: value})
	return nil
}

// attr 添加无命名空间的属性
// 入参: node 属性所属节点, name 本地名称, value 属性值
// 返回: error 字符或字节预算错误
func (p *pageEncoder) attr(node *xmlElement, name, value string) error {
	return p.attribute(node, xml.Name{Local: name}, value)
}

// page 构造页面尺寸、区域和绘制内容，不将非法区域替换为另一块区域后写出
// 入参: value 页面模型
// 返回: *xmlElement 页面节点, error 模型或预算错误
func (p *pageEncoder) page(value *Page) (*xmlElement, error) {
	if !geometryFinite(value.Width, value.Height) || value.Width < 1 || value.Height < 1 || !fixedLanguageTag(value.Language) {
		return nil, fmt.Errorf("%w: page dimensions or language", ErrInvalid)
	}
	root, err := p.node("FixedPage", 1)
	if err != nil {
		return nil, err
	}
	if err := p.attr(root, "xmlns", p.ns); err != nil {
		return nil, err
	}
	if p.hasResourceKeys {
		if err := p.attribute(root, xml.Name{Space: xmlnsNamespace, Local: "r"}, p.ns+"/resourcedictionary-key"); err != nil {
			return nil, err
		}
	}
	for _, attr := range []struct{ name, value string }{{"Width", encodeNumber(value.Width)}, {"Height", encodeNumber(value.Height)}} {
		if err := p.attr(root, attr.name, attr.value); err != nil {
			return nil, err
		}
	}
	if err := p.attribute(root, xml.Name{Space: xmlNamespace, Local: "lang"}, value.Language); err != nil {
		return nil, err
	}
	if value.Name != "" {
		if err := p.attr(root, "Name", value.Name); err != nil {
			return nil, err
		}
	}
	for _, box := range []struct {
		name    string
		value   Rect
		present bool
	}{{"ContentBox", value.ContentBox, value.HasContentBox}, {"BleedBox", value.BleedBox, value.HasBleedBox}} {
		if !box.present && (box.value == (Rect{}) || box.value == (Rect{Width: value.Width, Height: value.Height})) {
			continue
		}
		b := box.value
		valid := geometryFinite(b.X, b.Y, b.Width, b.Height) && b.Width >= 0 && b.Height >= 0
		if box.name == "ContentBox" {
			valid = valid && b.X >= 0 && b.Y >= 0 && b.X < value.Width && b.Y < value.Height && b.Width <= value.Width-b.X && b.Height <= value.Height-b.Y
		} else {
			valid = valid && b.X <= 0 && b.Y <= 0 && b.Width >= value.Width-b.X && b.Height >= value.Height-b.Y
		}
		if !valid {
			return nil, fmt.Errorf("%w: invalid page %s", ErrInvalid, box.name)
		}
		if err := p.attr(root, box.name, encodeRect(b)); err != nil {
			return nil, err
		}
	}
	if value.Resources != nil {
		dictNode, err := p.resourceDictionary(value.Resources, 3, false)
		if err != nil {
			return nil, err
		}
		if err := p.property(root, "Resources", dictNode, 2); err != nil {
			return nil, err
		}
	}
	for _, element := range value.Elements {
		child, err := p.element(element, 2)
		if err != nil {
			return nil, err
		}
		root.Children = append(root.Children, child)
	}
	return root, nil
}

// resourceDictionary 编码页面内联字典、远程字典引用或独立远程资源字典节点
// 入参: dict 资源字典模型, depth 节点深度, remoteRoot 是否为独立远程资源字典根元素
// 返回: *xmlElement 资源字典节点, error 键名、类型、循环或预算错误
func (p *pageEncoder) resourceDictionary(dict *ResourceDictionary, depth int, remoteRoot bool) (*xmlElement, error) {
	if dict == nil {
		return nil, fmt.Errorf("%w: nil resource dictionary", ErrInvalid)
	}
	if p.active[dict] {
		return nil, fmt.Errorf("%w: cyclic resource dictionary", ErrInvalid)
	}
	p.active[dict] = true
	defer delete(p.active, dict)
	node, err := p.node("ResourceDictionary", depth)
	if err != nil {
		return nil, err
	}
	if remoteRoot {
		if err := p.attr(node, "xmlns", p.ns); err != nil {
			return nil, err
		}
		if len(dict.Entries) != 0 {
			if err := p.attribute(node, xml.Name{Space: xmlnsNamespace, Local: "r"}, p.ns+"/resourcedictionary-key"); err != nil {
				return nil, err
			}
		}
	}
	if dict.Source != "" {
		if remoteRoot || len(dict.Entries) != 0 {
			return nil, fmt.Errorf("%w: resource dictionary Source conflicts with local entries or remote root", ErrInvalid)
		}
		source, err := p.reference("", dict.Source)
		if err != nil {
			return nil, err
		}
		p.hasRemoteDict = true
		return node, p.attr(node, "Source", source)
	}
	seen := make(map[string]bool, len(dict.Entries))
	keyAttr := xml.Name{Space: p.ns + "/resourcedictionary-key", Local: "Key"}
	for _, entry := range dict.Entries {
		if !fixedNamePattern(entry.Key) || seen[entry.Key] {
			return nil, fmt.Errorf("%w: invalid or duplicate resource key %q", ErrInvalid, entry.Key)
		}
		seen[entry.Key] = true
		var child *xmlElement
		switch typed := entry.Value.(type) {
		case *Brush:
			if typed == nil || typed.ResourceKey != "" {
				return nil, fmt.Errorf("%w: invalid brush resource definition %q", ErrInvalid, entry.Key)
			}
			child, err = p.brush(typed, depth+1)
		case *Geometry:
			if typed == nil || typed.ResourceKey != "" {
				return nil, fmt.Errorf("%w: invalid geometry resource definition %q", ErrInvalid, entry.Key)
			}
			child, err = p.geometry(typed, depth+1)
		case *Matrix:
			if typed == nil || !geometryFillMatrixFinite(*typed) {
				return nil, fmt.Errorf("%w: invalid matrix resource definition %q", ErrInvalid, entry.Key)
			}
			child, err = p.node("MatrixTransform", depth+1)
			if err == nil {
				err = p.attr(child, "Matrix", encodeMatrix(*typed))
			}
		case Matrix:
			if !geometryFillMatrixFinite(typed) {
				return nil, fmt.Errorf("%w: invalid matrix resource definition %q", ErrInvalid, entry.Key)
			}
			child, err = p.node("MatrixTransform", depth+1)
			if err == nil {
				err = p.attr(child, "Matrix", encodeMatrix(typed))
			}
		case *Canvas:
			if typed == nil || typed.Name != "" {
				return nil, fmt.Errorf("%w: visual resource definition cannot be nil or carry Name", ErrInvalid)
			}
			p.inVisualBrush++
			child, err = p.element(typed, depth+1)
			p.inVisualBrush--
		case *Path:
			if typed == nil || typed.Name != "" {
				return nil, fmt.Errorf("%w: visual resource definition cannot be nil or carry Name", ErrInvalid)
			}
			p.inVisualBrush++
			child, err = p.element(typed, depth+1)
			p.inVisualBrush--
		case *Glyphs:
			if typed == nil || typed.Name != "" {
				return nil, fmt.Errorf("%w: visual resource definition cannot be nil or carry Name", ErrInvalid)
			}
			p.inVisualBrush++
			child, err = p.element(typed, depth+1)
			p.inVisualBrush--
		default:
			return nil, fmt.Errorf("%w: unsupported resource definition value for %q", ErrInvalid, entry.Key)
		}
		if err != nil {
			return nil, err
		}
		if err := p.attribute(child, keyAttr, entry.Key); err != nil {
			return nil, err
		}
		node.Children = append(node.Children, child)
	}
	return node, nil
}

// source 返回模型的有效来源部件，缺省时采用当前页面来源
// 入参: part 模型记录的来源部件
// 返回: string 来源URI
func (p *pageEncoder) source(part string) string {
	if part == "" {
		return p.part
	}
	return part
}

// reference 按模型定义部件绑定资源，生成相对于输出页面的引用
// 入参: part 模型定义部件，空值使用页面地址, uri 模型资源引用
// 返回: string 页面相对引用, error 定义地址或资源引用错误
func (p *pageEncoder) reference(part, uri string) (string, error) {
	target, err := resolvePart(p.source(part), uri)
	if err != nil {
		return "", err
	}
	return relativePart(p.part, target)
}

// encodeNumber 输出无多余精度损失的标准实数，将负零规范为零以适配无符号类型
// 入参: value 有限数值
// 返回: string 十进制实数
func encodeNumber(value float64) string {
	if value == 0 {
		return "0"
	}
	return strconv.FormatFloat(value, 'g', -1, 64)
}

// encodePoint 输出标准点坐标
// 入参: value 二维点
// 返回: string 逗号分隔坐标
func encodePoint(value Point) string {
	return encodeNumber(value.X) + "," + encodeNumber(value.Y)
}

// encodeRect 输出标准矩形坐标
// 入参: value 矩形
// 返回: string 逗号分隔矩形
func encodeRect(value Rect) string {
	return strings.Join([]string{encodeNumber(value.X), encodeNumber(value.Y), encodeNumber(value.Width), encodeNumber(value.Height)}, ",")
}

// encodeMatrix 输出标准仿射矩阵
// 入参: value 矩阵
// 返回: string 逗号分隔六个系数
func encodeMatrix(value Matrix) string {
	return strings.Join([]string{encodeNumber(value.A), encodeNumber(value.B), encodeNumber(value.C), encodeNumber(value.D), encodeNumber(value.E), encodeNumber(value.F)}, ",")
}

// encodePageNode 写出已校验的生成节点及标量文本，使用调用方提供的命名空间声明
// 入参: encoder XML编码器, node 当前节点, ctx 取消Context
// 返回: error 取消或输出错误
func encodePageNode(encoder *xml.Encoder, node *xmlElement, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	start := xml.StartElement{Name: xml.Name{Local: node.Name.Local}}
	for _, attr := range node.Attr {
		switch attr.Name.Space {
		case xmlnsNamespace:
			if err := xmlNamespaceOutput(attr.Name.Local, attr.Value); err != nil {
				return err
			}
			attr.Name = xml.Name{Local: "xmlns:" + attr.Name.Local}
		case xmlNamespace:
			attr.Name = xml.Name{Local: "xml:" + attr.Name.Local}
		case node.Name.Space + "/resourcedictionary-key":
			attr.Name = xml.Name{Local: "r:" + attr.Name.Local}
		case "":
			if attr.Name.Local == "xmlns" {
				if err := xmlNamespaceOutput("", attr.Value); err != nil {
					return err
				}
			}
		}
		start.Attr = append(start.Attr, attr)
	}
	if err := encoder.EncodeToken(start); err != nil {
		return err
	}
	if node.Text != "" {
		if !xmlTextValid(node.Text) {
			return fmt.Errorf("%w: invalid generated XML text", ErrInvalid)
		}
		if err := encoder.EncodeToken(xml.CharData(node.Text)); err != nil {
			return err
		}
	}
	for _, child := range node.Children {
		if err := encodePageNode(encoder, child, ctx); err != nil {
			return err
		}
	}
	return encoder.EncodeToken(start.End())
}

// color 按源色彩空间编码颜色分量，sRGB分量校验[0,1]后四舍五入量化为8位，其余保留浮点精度
// 入参: value 源颜色, part 颜色的定义部件
// 返回: string 标准颜色表达式, error 颜色、URI或表示范围错误
func (p *pageEncoder) color(value Color, part string) (string, error) {
	if !geometryFinite(value.Alpha) || value.Alpha < 0 || value.Alpha > 1 {
		return "", fmt.Errorf("%w: color alpha", ErrInvalid)
	}
	switch value.Space {
	case ColorSRGB, ColorScRGB:
		if len(value.Components) != 3 {
			return "", fmt.Errorf("%w: RGB channel count", ErrInvalid)
		}
	case ColorContext:
		minimum := 1
		if p.format == FormatXPS {
			minimum = 3
		}
		if len(value.Components) < minimum || len(value.Components) > 8 {
			return "", fmt.Errorf("%w: ICC color channel count", ErrInvalid)
		}
	default:
		return "", fmt.Errorf("%w: unknown color space", ErrInvalid)
	}
	for _, component := range value.Components {
		if !geometryFinite(component) {
			return "", fmt.Errorf("%w: non-finite color component", ErrInvalid)
		}
	}
	if value.Space == ColorSRGB {
		var bytes [4]uint8
		for index, component := range append([]float64{value.Alpha}, value.Components...) {
			if component < 0 || component > 1 {
				return "", fmt.Errorf("%w: sRGB component range", ErrInvalid)
			}
			bytes[index] = uint8(math.Round(component * 255))
		}
		if bytes[0] == 0xff {
			return fmt.Sprintf("#%02X%02X%02X", bytes[1], bytes[2], bytes[3]), nil
		}
		return fmt.Sprintf("#%02X%02X%02X%02X", bytes[0], bytes[1], bytes[2], bytes[3]), nil
	}
	prefix := "sc#"
	if value.Space == ColorContext {
		for _, component := range value.Components {
			if component < 0 || component > 1 {
				return "", fmt.Errorf("%w: ICC color component range", ErrInvalid)
			}
		}
		profile, err := p.reference(part, value.ProfileURI)
		if err != nil {
			return "", err
		}
		prefix = "ContextColor " + profile + " "
	}
	fields := make([]string, 1, len(value.Components)+1)
	fields[0] = encodeDecimal(value.Alpha)
	for _, component := range value.Components {
		fields = append(fields, encodeDecimal(component))
	}
	return prefix + strings.Join(fields, ","), nil
}

// encodeDecimal 输出不含指数的十进制数，满足颜色模式的词法要求
// 入参: value 有限数值
// 返回: string 十进制文本
func encodeDecimal(value float64) string {
	if value == 0 {
		return "0"
	}
	return strconv.FormatFloat(value, 'f', -1, 64)
}

// brush 编码五类画刷的实际参数，支持StaticResource变换及视觉引用，内联视觉输出VisualBrush.Visual属性元素
// 入参: value 画刷模型, depth 画刷节点深度
// 返回: *xmlElement 画刷节点, error 属性、资源、循环或预算错误
func (p *pageEncoder) brush(value *Brush, depth int) (*xmlElement, error) {
	if value == nil || value.Kind < BrushSolidColor || value.Kind > BrushVisual || !geometryFinite(value.Opacity) || value.Opacity < 0 || value.Opacity > 1 {
		return nil, fmt.Errorf("%w: brush model", ErrInvalid)
	}
	if p.active[value] {
		return nil, fmt.Errorf("%w: cyclic brush model", ErrInvalid)
	}
	p.active[value] = true
	defer delete(p.active, value)
	name := []string{"", "SolidColorBrush", "LinearGradientBrush", "RadialGradientBrush", "ImageBrush", "VisualBrush"}[value.Kind]
	node, err := p.node(name, depth)
	if err != nil {
		return nil, err
	}
	if value.Opacity != 1 {
		if err := p.attr(node, "Opacity", encodeNumber(value.Opacity)); err != nil {
			return nil, err
		}
	}
	if value.Transform != nil && value.TransformResource != "" {
		return nil, fmt.Errorf("%w: conflicting brush transform and transform resource", ErrInvalid)
	}
	if value.TransformResource != "" {
		if value.Kind == BrushSolidColor || !fixedNamePattern(value.TransformResource) {
			return nil, fmt.Errorf("%w: brush transform resource", ErrInvalid)
		}
		if err := p.attr(node, "Transform", "{StaticResource "+value.TransformResource+"}"); err != nil {
			return nil, err
		}
	} else if value.Transform != nil {
		if value.Kind == BrushSolidColor || !geometryFillMatrixFinite(*value.Transform) {
			return nil, fmt.Errorf("%w: brush matrix", ErrInvalid)
		}
		if err := p.attr(node, "Transform", encodeMatrix(*value.Transform)); err != nil {
			return nil, err
		}
	}
	if value.Kind == BrushSolidColor {
		text, err := p.color(value.Color, value.Part)
		if err != nil {
			return nil, err
		}
		return node, p.attr(node, "Color", text)
	}
	if value.Kind == BrushLinearGradient || value.Kind == BrushRadialGradient {
		return node, p.gradient(node, value, depth)
	}
	if value.TileMode > TileFlipXY {
		return nil, fmt.Errorf("%w: tile brush mode", ErrInvalid)
	}
	for _, box := range []struct {
		name  string
		value Rect
	}{{"Viewbox", value.Viewbox}, {"Viewport", value.Viewport}} {
		if !geometryFinite(box.value.X, box.value.Y, box.value.Width, box.value.Height) || box.value.Width < 0 || box.value.Height < 0 {
			return nil, fmt.Errorf("%w: invalid brush %s", ErrInvalid, box.name)
		}
		if err := p.attr(node, box.name, encodeRect(box.value)); err != nil {
			return nil, err
		}
	}
	for _, attr := range []struct{ name, value string }{{"ViewboxUnits", "Absolute"}, {"ViewportUnits", "Absolute"}} {
		if err := p.attr(node, attr.name, attr.value); err != nil {
			return nil, err
		}
	}
	if value.TileMode != TileNone {
		if err := p.attr(node, "TileMode", []string{"None", "Tile", "FlipX", "FlipY", "FlipXY"}[value.TileMode]); err != nil {
			return nil, err
		}
	}
	if value.Kind == BrushImage {
		image, err := p.reference(value.Part, value.ImageSource)
		if err != nil {
			return nil, err
		}
		if value.ImageProfileURI != "" {
			profile, err := p.reference(value.Part, value.ImageProfileURI)
			if err != nil {
				return nil, err
			}
			image = "{ColorConvertedBitmap " + image + " " + profile + "}"
		}
		return node, p.attr(node, "ImageSource", image)
	}
	if value.VisualReference != "" {
		if value.Visual != nil || !fixedNamePattern(value.VisualReference) {
			return nil, fmt.Errorf("%w: visual brush reference conflict or invalid key", ErrInvalid)
		}
		return node, p.attr(node, "Visual", "{StaticResource "+value.VisualReference+"}")
	}
	if contentProperties(value.Visual) == nil {
		return nil, fmt.Errorf("%w: missing or unknown brush visual", ErrInvalid)
	}
	p.inVisualBrush++
	defer func() { p.inVisualBrush-- }()
	visual, err := p.element(value.Visual, depth+2)
	if err != nil {
		return nil, err
	}
	return node, p.property(node, "Visual", visual, depth+1)
}

// brushProperty 按属性简写、StaticResource引用或属性元素形式编码画刷属性
// 入参: node 属性所属节点, name 属性名, value 画刷模型, depth 所属节点深度
// 返回: error 属性、颜色、引用或预算错误
func (p *pageEncoder) brushProperty(node *xmlElement, name string, value *Brush, depth int) error {
	if value == nil {
		return nil
	}
	if value.ResourceKey != "" {
		if !fixedNamePattern(value.ResourceKey) {
			return fmt.Errorf("%w: invalid brush resource key %q", ErrInvalid, value.ResourceKey)
		}
		return p.attr(node, name, "{StaticResource "+value.ResourceKey+"}")
	}
	if name != "OpacityMask" && value.Kind == BrushSolidColor && value.Opacity == 1 && value.Transform == nil && value.TransformResource == "" {
		if value.Color.Space == ColorSRGB || value.Color.Space == ColorScRGB || value.Color.Space == ColorContext && p.compact {
			text, err := p.color(value.Color, value.Part)
			if err != nil {
				return err
			}
			return p.attr(node, name, text)
		}
	}
	brush, err := p.brush(value, depth+2)
	if err != nil {
		return err
	}
	return p.property(node, name, brush, depth+1)
}

// gradient 编码渐变参数与停靠点，省略标准默认插值空间与延展方式并保留停靠点顺序
// 入参: node 画刷节点, value 渐变模型, depth 节点深度
// 返回: error 属性、颜色或预算错误
func (p *pageEncoder) gradient(node *xmlElement, value *Brush, depth int) error {
	if value.ColorInterpolationMode > ColorInterpolationScRGB || value.SpreadMethod > SpreadRepeat || len(value.Stops) < 2 {
		return fmt.Errorf("%w: gradient model", ErrInvalid)
	}
	if err := p.attr(node, "MappingMode", "Absolute"); err != nil {
		return err
	}
	if value.ColorInterpolationMode != ColorInterpolationSRGB {
		if err := p.attr(node, "ColorInterpolationMode", []string{"SRgbLinearInterpolation", "ScRgbLinearInterpolation"}[value.ColorInterpolationMode]); err != nil {
			return err
		}
	}
	if value.SpreadMethod != SpreadPad {
		if err := p.attr(node, "SpreadMethod", []string{"Pad", "Reflect", "Repeat"}[value.SpreadMethod]); err != nil {
			return err
		}
	}
	points := []struct {
		name  string
		value Point
	}{{"StartPoint", value.StartPoint}, {"EndPoint", value.EndPoint}}
	if value.Kind == BrushRadialGradient {
		points = []struct {
			name  string
			value Point
		}{{"Center", value.Center}, {"GradientOrigin", value.GradientOrigin}}
		for _, radius := range []struct {
			name  string
			value float64
		}{{"RadiusX", value.RadiusX}, {"RadiusY", value.RadiusY}} {
			if !geometryFinite(radius.value) || radius.value < 0 {
				return fmt.Errorf("%w: invalid gradient %s", ErrInvalid, radius.name)
			}
			if err := p.attr(node, radius.name, encodeNumber(radius.value)); err != nil {
				return err
			}
		}
	}
	for _, point := range points {
		if !geometryFinite(point.value.X, point.value.Y) {
			return fmt.Errorf("%w: invalid gradient %s", ErrInvalid, point.name)
		}
		if err := p.attr(node, point.name, encodePoint(point.value)); err != nil {
			return err
		}
	}
	container, err := p.node(node.Name.Local+".GradientStops", depth+1)
	if err != nil {
		return err
	}
	for _, stop := range value.Stops {
		if !geometryFinite(stop.Offset) {
			return fmt.Errorf("%w: invalid gradient stop offset", ErrInvalid)
		}
		child, err := p.node("GradientStop", depth+2)
		if err != nil {
			return err
		}
		text, err := p.color(stop.Color, value.Part)
		if err != nil {
			return err
		}
		if err := p.attr(child, "Color", text); err != nil {
			return err
		}
		if err := p.attr(child, "Offset", encodeNumber(stop.Offset)); err != nil {
			return err
		}
		container.Children = append(container.Children, child)
	}
	node.Children = append(node.Children, container)
	return nil
}

// element 编码三类绘制元素，保持局部属性和子元素顺序，不把共享模型视为可重复声明的XML标识
// 入参: value 绘制模型, depth 当前XML深度
// 返回: *xmlElement 绘制节点, error 模型、循环或预算错误
func (p *pageEncoder) element(value Element, depth int) (*xmlElement, error) {
	var name string
	var properties ElementProperties
	switch value := value.(type) {
	case *Canvas:
		if value == nil {
			return nil, fmt.Errorf("%w: nil Canvas", ErrInvalid)
		}
		name, properties = "Canvas", value.ElementProperties
	case *Path:
		if value == nil {
			return nil, fmt.Errorf("%w: nil Path", ErrInvalid)
		}
		name, properties = "Path", value.ElementProperties
	case *Glyphs:
		if value == nil {
			return nil, fmt.Errorf("%w: nil Glyphs", ErrInvalid)
		}
		name, properties = "Glyphs", value.ElementProperties
	default:
		return nil, fmt.Errorf("%w: unknown drawing model", ErrInvalid)
	}
	if p.active[value] {
		return nil, fmt.Errorf("%w: cyclic drawing model", ErrInvalid)
	}
	p.active[value] = true
	defer delete(p.active, value)
	node, err := p.node(name, depth)
	if err != nil {
		return nil, err
	}
	if canvas, ok := value.(*Canvas); ok && canvas.Resources != nil {
		dictNode, err := p.resourceDictionary(canvas.Resources, depth+2, false)
		if err != nil {
			return nil, err
		}
		if err := p.property(node, "Resources", dictNode, depth+1); err != nil {
			return nil, err
		}
	}
	if err := p.properties(node, value, properties, depth); err != nil {
		return nil, err
	}
	switch value := value.(type) {
	case *Canvas:
		if value.EdgeMode != "" && value.EdgeMode != EdgeModeAliased {
			return nil, fmt.Errorf("%w: invalid EdgeMode %q", ErrInvalid, value.EdgeMode)
		}
		for _, attr := range []struct{ name, value string }{{"RenderOptions.EdgeMode", string(value.EdgeMode)}, {"AutomationProperties.Name", value.AutomationName}, {"AutomationProperties.HelpText", value.AutomationHelpText}} {
			if attr.value != "" {
				if err := p.attr(node, attr.name, attr.value); err != nil {
					return nil, err
				}
			}
		}
		for _, child := range value.Elements {
			element, err := p.element(child, depth+1)
			if err != nil {
				return nil, err
			}
			node.Children = append(node.Children, element)
		}
	case *Path:
		if err := p.path(node, value, depth); err != nil {
			return nil, err
		}
	case *Glyphs:
		if err := p.glyphs(node, value, depth); err != nil {
			return nil, err
		}
	}
	return node, nil
}

// properties 编码所有绘制元素的共同局部属性，显式零透明度不会被当作缺省值，共享指针仅在主树或首次展开保留唯一Name
// 入参: node 目标节点, owner 当前元素指针, value 局部属性, depth 节点深度
// 返回: error 属性、循环或预算错误
func (p *pageEncoder) properties(node *xmlElement, owner Element, value ElementProperties, depth int) error {
	if !geometryFinite(value.Opacity) || value.Opacity < 0 || value.Opacity > 1 {
		return fmt.Errorf("%w: element opacity", ErrInvalid)
	}
	if value.Opacity != 1 {
		if err := p.attr(node, "Opacity", encodeNumber(value.Opacity)); err != nil {
			return err
		}
	}
	if value.Name != "" {
		emitName := p.elemCount[owner] <= 1
		if !emitName && !p.emittedName[owner] {
			if p.mainElemCount[owner] > 0 {
				emitName = p.inVisualBrush == 0
			} else {
				emitName = true
			}
		}
		if emitName {
			if err := p.attr(node, "Name", value.Name); err != nil {
				return err
			}
			p.emittedName[owner] = true
		}
	}
	if value.Language != nil {
		if *value.Language != "" && !fixedLanguageTag(*value.Language) {
			return fmt.Errorf("%w: invalid xml:lang on %s", ErrInvalid, node.Name.Local)
		}
		if err := p.attribute(node, xml.Name{Space: xmlNamespace, Local: "lang"}, *value.Language); err != nil {
			return err
		}
	}
	if value.NavigateURI != nil {
		normalized := structureURI(*value.NavigateURI)
		if normalized != "" {
			if _, err := url.Parse(normalized); err != nil {
				return fmt.Errorf("%w: invalid FixedPage.NavigateUri: %w", ErrInvalid, err)
			}
		}
		if err := p.attr(node, "FixedPage.NavigateUri", *value.NavigateURI); err != nil {
			return err
		}
	}
	if value.RenderTransform != nil && value.RenderTransformResource != "" {
		return fmt.Errorf("%w: conflicting element transform and transform resource", ErrInvalid)
	}
	if value.RenderTransformResource != "" {
		if !fixedNamePattern(value.RenderTransformResource) {
			return fmt.Errorf("%w: element transform resource", ErrInvalid)
		}
		if err := p.attr(node, "RenderTransform", "{StaticResource "+value.RenderTransformResource+"}"); err != nil {
			return err
		}
	} else if value.RenderTransform != nil {
		if !geometryFillMatrixFinite(*value.RenderTransform) {
			return fmt.Errorf("%w: element matrix", ErrInvalid)
		}
		if err := p.attr(node, "RenderTransform", encodeMatrix(*value.RenderTransform)); err != nil {
			return err
		}
	}
	if value.Clip != nil {
		if err := p.geometryProperty(node, "Clip", value.Clip, depth); err != nil {
			return err
		}
	}
	if value.OpacityMask != nil {
		if err := p.brushProperty(node, "OpacityMask", value.OpacityMask, depth); err != nil {
			return err
		}
	}
	return nil
}

// property 将已构造的值放入唯一的属性元素
// 入参: node 属性所属节点, name 属性名称, value 属性值节点, depth 属性元素深度
// 返回: error 复杂度或预算错误
func (p *pageEncoder) property(node *xmlElement, name string, value *xmlElement, depth int) error {
	container, err := p.node(node.Name.Local+"."+name, depth)
	if err != nil {
		return err
	}
	container.Children = []*xmlElement{value}
	node.Children = append(node.Children, container)
	return nil
}

// geometryProperty 按StaticResource引用、紧凑缩写属性或PathGeometry属性元素形式编码几何属性
// 入参: node 所属元素节点, name 属性名, value 几何模型, depth 所属节点深度
// 返回: error 几何、引用或预算错误
func (p *pageEncoder) geometryProperty(node *xmlElement, name string, value *Geometry, depth int) error {
	if value == nil {
		return nil
	}
	if value.ResourceKey != "" {
		if !fixedNamePattern(value.ResourceKey) {
			return fmt.Errorf("%w: invalid geometry resource key %q", ErrInvalid, value.ResourceKey)
		}
		return p.attr(node, name, "{StaticResource "+value.ResourceKey+"}")
	}
	if value.FillRule > GeometryNonZero {
		return fmt.Errorf("%w: geometry model", ErrInvalid)
	}
	allowAbbreviated := true
	if value.Transform == nil && value.TransformResource == "" && len(value.Figures) != 0 {
		abbreviated, err := p.geometryCanAbbreviate(value.Figures, depth)
		if err != nil {
			return err
		}
		if abbreviated {
			text, err := p.geometryFigures(value.Figures, depth)
			if err != nil {
				return err
			}
			if value.FillRule == GeometryNonZero {
				text = "F1 " + text
			}
			return p.attr(node, name, text)
		}
		allowAbbreviated = false
	}
	geometry, err := p.geometryWithMode(value, depth+2, allowAbbreviated)
	if err != nil {
		return err
	}
	return p.property(node, name, geometry, depth+1)
}

// path 编码路径描边、画刷及几何，省略标准默认描边属性并在无描边时省略零值描边参数
// 入参: node 路径节点, value 路径模型, depth 节点深度
// 返回: error 属性、几何或预算错误
func (p *pageEncoder) path(node *xmlElement, value *Path, depth int) error {
	if !geometryFinite(value.StrokeThickness) || value.StrokeThickness < 0 {
		return fmt.Errorf("%w: invalid StrokeThickness", ErrInvalid)
	}
	if value.Stroke != nil && value.StrokeThickness != 1 || value.Stroke == nil && value.StrokeThickness != 0 && value.StrokeThickness != 1 {
		if err := p.attr(node, "StrokeThickness", encodeNumber(value.StrokeThickness)); err != nil {
			return err
		}
	}
	if value.StrokeMiterLimit != 0 {
		if !geometryFinite(value.StrokeMiterLimit) || value.StrokeMiterLimit < 1 {
			return fmt.Errorf("%w: invalid StrokeMiterLimit", ErrInvalid)
		}
		if value.StrokeMiterLimit != 10 {
			if err := p.attr(node, "StrokeMiterLimit", encodeNumber(value.StrokeMiterLimit)); err != nil {
				return err
			}
		}
	}
	if !geometryFinite(value.StrokeDashOffset) {
		return fmt.Errorf("%w: invalid StrokeDashOffset", ErrInvalid)
	}
	if value.StrokeDashOffset != 0 {
		if err := p.attr(node, "StrokeDashOffset", encodeNumber(value.StrokeDashOffset)); err != nil {
			return err
		}
	}
	for _, capItem := range []struct {
		name  string
		value LineCap
	}{{"StrokeDashCap", value.StrokeDashCap}, {"StrokeStartLineCap", value.StrokeStartLineCap}, {"StrokeEndLineCap", value.StrokeEndLineCap}} {
		if capItem.value != "" && !strokeOutlineCapValid(capItem.value) {
			return fmt.Errorf("%w: invalid %s %q", ErrInvalid, capItem.name, capItem.value)
		}
	}
	if value.StrokeLineJoin != "" && value.StrokeLineJoin != LineJoinMiter && value.StrokeLineJoin != LineJoinBevel && value.StrokeLineJoin != LineJoinRound {
		return fmt.Errorf("%w: invalid StrokeLineJoin %q", ErrInvalid, value.StrokeLineJoin)
	}
	for _, attr := range []struct {
		name  string
		value string
		def   string
	}{
		{"StrokeDashCap", string(value.StrokeDashCap), string(LineCapFlat)},
		{"StrokeStartLineCap", string(value.StrokeStartLineCap), string(LineCapFlat)},
		{"StrokeEndLineCap", string(value.StrokeEndLineCap), string(LineCapFlat)},
		{"StrokeLineJoin", string(value.StrokeLineJoin), string(LineJoinMiter)},
		{"AutomationProperties.Name", value.AutomationName, ""},
		{"AutomationProperties.HelpText", value.AutomationHelpText, ""},
	} {
		if attr.value != "" && attr.value != attr.def {
			if err := p.attr(node, attr.name, attr.value); err != nil {
				return err
			}
		}
	}
	if value.SnapsToDevicePixels != nil {
		if err := p.attr(node, "SnapsToDevicePixels", strconv.FormatBool(*value.SnapsToDevicePixels)); err != nil {
			return err
		}
	}
	if len(value.StrokeDashArray) != 0 {
		if len(value.StrokeDashArray) < 2 || len(value.StrokeDashArray)%2 != 0 {
			return fmt.Errorf("%w: StrokeDashArray requires a nonempty even number of values", ErrInvalid)
		}
		if len(value.StrokeDashArray) > p.limits.MaxXMLNodes-p.work {
			return fmt.Errorf("%w: dash encoding complexity", ErrLimit)
		}
		values := make([]string, 0, len(value.StrokeDashArray))
		for _, item := range value.StrokeDashArray {
			if err := p.step(depth); err != nil {
				return err
			}
			if !geometryFinite(item) || item < 0 {
				return fmt.Errorf("%w: invalid dash length", ErrInvalid)
			}
			values = append(values, encodeNumber(item))
		}
		if err := p.attr(node, "StrokeDashArray", strings.Join(values, " ")); err != nil {
			return err
		}
	}
	for _, property := range []struct {
		name  string
		value *Brush
	}{{"Fill", value.Fill}, {"Stroke", value.Stroke}} {
		if err := p.brushProperty(node, property.name, property.value, depth); err != nil {
			return err
		}
	}
	if value.Data != nil {
		if err := p.geometryProperty(node, "Data", value.Data, depth); err != nil {
			return err
		}
	}
	return nil
}

// glyphs 编码字形簇、原始文字和定位信息，省略标准默认属性且不从Unicode重新推断显式字形索引
// 入参: node 字形节点, value 字形模型, depth 节点深度
// 返回: error 字形、资源或预算错误
func (p *pageEncoder) glyphs(node *xmlElement, value *Glyphs, depth int) error {
	if !geometryFinite(value.FontRenderingEmSize, value.Origin.X, value.Origin.Y) || value.FontRenderingEmSize < 0 {
		return fmt.Errorf("%w: invalid glyphs font size or origin", ErrInvalid)
	}
	if value.BidiLevel < 0 || value.BidiLevel > 61 || value.IsSideways && value.BidiLevel%2 != 0 {
		return fmt.Errorf("%w: invalid glyphs BidiLevel or IsSideways", ErrInvalid)
	}
	switch value.StyleSimulations {
	case "", StyleSimulationNone, StyleSimulationItalic, StyleSimulationBold, StyleSimulationBoldItalic:
	default:
		return fmt.Errorf("%w: invalid StyleSimulations %q", ErrInvalid, value.StyleSimulations)
	}
	font := value.FontPart
	index, present := value.CollectionIndex, value.HasCollectionIndex
	var err error
	if font != "" {
		font, err = relativePart(p.part, font)
	} else {
		var uriIndex uint32
		var uriPresent bool
		font, uriIndex, uriPresent, err = ParseFontURI(value.FontURI)
		if !present {
			index, present = uriIndex, uriPresent
		}
		if err == nil {
			font, err = p.reference(value.Part, font)
		}
	}
	if err != nil {
		return err
	}
	if !value.HasCollectionIndex && value.CollectionIndex != 0 {
		return fmt.Errorf("%w: collection index needs an explicit presence flag", ErrInvalid)
	}
	if present {
		font += "#" + strconv.FormatUint(uint64(index), 10)
	}
	rawUnicode := ""
	if value.Text != "" {
		rawUnicode = EscapeUnicodeString(value.Text)
		if err := validateUnicodeString(rawUnicode, p.format); err != nil {
			return fmt.Errorf("UnicodeString: %w", err)
		}
	}
	rawDeviceFont := ""
	if value.DeviceFontName != "" {
		rawDeviceFont = EscapeUnicodeString(value.DeviceFontName)
		if err := validateUnicodeString(rawDeviceFont, p.format); err != nil {
			return fmt.Errorf("DeviceFontName: %w", err)
		}
	}
	if value.CaretStops != "" {
		if _, err := ParseCaretStops(value.CaretStops, rawUnicode); err != nil {
			return err
		}
	}
	if err := ValidateGlyphIndices(value.Indices, rawUnicode); err != nil {
		return err
	}
	for _, attr := range []struct{ name, value string }{{"FontUri", font}, {"FontRenderingEmSize", encodeNumber(value.FontRenderingEmSize)}, {"OriginX", encodeNumber(value.Origin.X)}, {"OriginY", encodeNumber(value.Origin.Y)}, {"CaretStops", value.CaretStops}} {
		if attr.value != "" {
			if err := p.attr(node, attr.name, attr.value); err != nil {
				return err
			}
		}
	}
	if value.BidiLevel != 0 {
		if err := p.attr(node, "BidiLevel", strconv.Itoa(value.BidiLevel)); err != nil {
			return err
		}
	}
	if value.IsSideways {
		if err := p.attr(node, "IsSideways", "true"); err != nil {
			return err
		}
	}
	if value.StyleSimulations != "" && value.StyleSimulations != StyleSimulationNone {
		if err := p.attr(node, "StyleSimulations", string(value.StyleSimulations)); err != nil {
			return err
		}
	}
	for _, attr := range []struct{ name, value string }{{"UnicodeString", rawUnicode}, {"DeviceFontName", rawDeviceFont}} {
		if attr.value != "" {
			if err := p.attr(node, attr.name, attr.value); err != nil {
				return err
			}
		}
	}
	if len(value.Indices) != 0 {
		indices, err := p.glyphIndices(value.Indices, depth)
		if err != nil {
			return err
		}
		if strings.Trim(indices, ";") == "" {
			if value.Text == "" {
				return fmt.Errorf("%w: glyphs requires UnicodeString or non-empty Indices", ErrInvalid)
			}
		} else if err := p.attr(node, "Indices", indices); err != nil {
			return err
		}
	}
	if value.Fill != nil {
		return p.brushProperty(node, "Fill", value.Fill, depth)
	}
	return nil
}

// glyphIndices 保留簇前缀及各个度量的省略状态，按最终模式编码实数，不将省略的度量补为零
// 入参: values 字形簇, depth 所属节点深度
// 返回: string Indices属性, error 簇结构或预算错误
func (p *pageEncoder) glyphIndices(values []GlyphCluster, depth int) (string, error) {
	var output strings.Builder
	entries := 0
	for _, cluster := range values {
		if cluster.CodeUnitCount < 1 || len(cluster.Glyphs) == 0 || !cluster.HasMapping && (cluster.CodeUnitCount != 1 || len(cluster.Glyphs) != 1 || cluster.HasGlyphCount) || !cluster.HasGlyphCount && len(cluster.Glyphs) != 1 {
			return "", fmt.Errorf("%w: glyph cluster structure", ErrInvalid)
		}
		for index, glyph := range cluster.Glyphs {
			if err := p.step(depth); err != nil {
				return "", err
			}
			if glyph.HasAdvanceWidth && (!geometryFinite(glyph.AdvanceWidth) || glyph.AdvanceWidth < 0) || glyph.HasUOffset && !geometryFinite(glyph.UOffset) || glyph.HasVOffset && !geometryFinite(glyph.VOffset) {
				return "", fmt.Errorf("%w: invalid glyph index metrics", ErrInvalid)
			}
			if entries != 0 {
				output.WriteByte(';')
			}
			entries++
			if index == 0 && cluster.HasMapping {
				output.WriteByte('(')
				output.WriteString(strconv.Itoa(cluster.CodeUnitCount))
				if cluster.HasGlyphCount {
					output.WriteByte(':')
					output.WriteString(strconv.Itoa(len(cluster.Glyphs)))
				}
				output.WriteByte(')')
			}
			if glyph.HasIndex {
				output.WriteString(strconv.FormatUint(uint64(glyph.Index), 10))
			}
			fields := []struct {
				value   float64
				present bool
			}{{glyph.AdvanceWidth, glyph.HasAdvanceWidth}, {glyph.UOffset, glyph.HasUOffset}, {glyph.VOffset, glyph.HasVOffset}}
			last := -1
			for index, field := range fields {
				if field.present {
					last = index
				}
			}
			for _, field := range fields[:last+1] {
				output.WriteByte(',')
				if field.present {
					output.WriteString(encodeNumber(field.value))
				}
			}
			if int64(output.Len()) > p.limits.MaxPartBytes-p.bytes {
				return "", fmt.Errorf("%w: glyph encoding bytes", ErrLimit)
			}
		}
	}
	return output.String(), nil
}

// geometry 编码所有路径段及填充、描边标志，缺省标志统一时使用紧凑几何，其余采用显式段元素
// 入参: value 几何模型, depth 几何节点深度
// 返回: *xmlElement 几何节点, error 模型或预算错误
func (p *pageEncoder) geometry(value *Geometry, depth int) (*xmlElement, error) {
	return p.geometryWithMode(value, depth, true)
}

// geometryWithMode 按可选缩写判定编码PathGeometry节点，避免非紧凑路径在属性预检后重复消耗预算
// 入参: value 几何模型, depth 几何节点深度, allowAbbreviated 是否检查并允许紧凑Figures缩写
// 返回: *xmlElement 几何节点, error 模型或预算错误
func (p *pageEncoder) geometryWithMode(value *Geometry, depth int, allowAbbreviated bool) (*xmlElement, error) {
	if value == nil || value.FillRule > GeometryNonZero {
		return nil, fmt.Errorf("%w: geometry model", ErrInvalid)
	}
	node, err := p.node("PathGeometry", depth)
	if err != nil {
		return nil, err
	}
	if value.FillRule == GeometryNonZero {
		if err := p.attr(node, "FillRule", "NonZero"); err != nil {
			return nil, err
		}
	}
	if value.Transform != nil && value.TransformResource != "" {
		return nil, fmt.Errorf("%w: conflicting geometry transform and transform resource", ErrInvalid)
	}
	if value.TransformResource != "" {
		if !fixedNamePattern(value.TransformResource) {
			return nil, fmt.Errorf("%w: geometry transform resource", ErrInvalid)
		}
		if err := p.attr(node, "Transform", "{StaticResource "+value.TransformResource+"}"); err != nil {
			return nil, err
		}
	} else if value.Transform != nil {
		if !geometryFillMatrixFinite(*value.Transform) {
			return nil, fmt.Errorf("%w: geometry matrix", ErrInvalid)
		}
		if err := p.attr(node, "Transform", encodeMatrix(*value.Transform)); err != nil {
			return nil, err
		}
	}
	if allowAbbreviated && len(value.Figures) != 0 {
		abbreviated, err := p.geometryCanAbbreviate(value.Figures, depth)
		if err != nil {
			return nil, err
		}
		if abbreviated {
			text, err := p.geometryFigures(value.Figures, depth)
			if err != nil {
				return nil, err
			}
			if err := p.attr(node, "Figures", text); err != nil {
				return nil, err
			}
			return node, nil
		}
	}
	for _, figure := range value.Figures {
		if len(figure.Segments) == 0 {
			return nil, fmt.Errorf("%w: explicit PathFigure requires a segment", ErrInvalid)
		}
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return nil, fmt.Errorf("%w: non-finite geometry StartPoint", ErrInvalid)
		}
		child, err := p.node("PathFigure", depth+1)
		if err != nil {
			return nil, err
		}
		if err := p.attr(child, "StartPoint", encodePoint(figure.StartPoint)); err != nil {
			return nil, err
		}
		if figure.IsClosed {
			if err := p.attr(child, "IsClosed", "true"); err != nil {
				return nil, err
			}
		}
		if !figure.IsFilled {
			if err := p.attr(child, "IsFilled", "false"); err != nil {
				return nil, err
			}
		}
		for _, segment := range figure.Segments {
			entry, err := p.geometrySegment(segment, depth+2)
			if err != nil {
				return nil, err
			}
			child.Children = append(child.Children, entry)
		}
		node.Children = append(node.Children, child)
	}
	return node, nil
}

// geometryCanAbbreviate 判断子路径列表是否全部采用默认填充与描边标志，校验深度与上限但不重复扣减节点工作量
// 入参: figures 子路径切片, depth 节点深度
// 返回: bool 是否可缩写编码, error 深度、复杂度或取消错误
func (p *pageEncoder) geometryCanAbbreviate(figures []GeometryFigure, depth int) (bool, error) {
	if depth > p.limits.MaxXMLDepth {
		return false, fmt.Errorf("%w: page encoding complexity", ErrLimit)
	}
	scanned := 0
	remaining := p.limits.MaxXMLNodes - p.work
	for _, figure := range figures {
		if err := checkContext(p.ctx); err != nil {
			return false, err
		}
		scanned++
		if scanned > remaining {
			return false, fmt.Errorf("%w: page encoding complexity", ErrLimit)
		}
		if !figure.IsFilled {
			return false, nil
		}
		for _, segment := range figure.Segments {
			if err := checkContext(p.ctx); err != nil {
				return false, err
			}
			scanned++
			if scanned > remaining {
				return false, fmt.Errorf("%w: page encoding complexity", ErrLimit)
			}
			if !segment.IsStroked {
				return false, nil
			}
		}
	}
	return true, nil
}

// geometryFigures 输出不改变标志语义的绝对坐标缩写，不将圆弧转换为曲线或直线
// 入参: values 全部采用缺省填充和描边标志的子路径, depth 所属节点深度
// 返回: string Figures属性, error 类型或预算错误
func (p *pageEncoder) geometryFigures(values []GeometryFigure, depth int) (string, error) {
	var output strings.Builder
	for _, figure := range values {
		if err := p.step(depth); err != nil {
			return "", err
		}
		if len(figure.Segments) == 0 {
			return "", fmt.Errorf("%w: geometry figure requires a segment", ErrInvalid)
		}
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return "", fmt.Errorf("%w: non-finite geometry StartPoint", ErrInvalid)
		}
		output.WriteString("M")
		output.WriteString(encodePoint(figure.StartPoint))
		for _, segment := range figure.Segments {
			if err := p.step(depth); err != nil {
				return "", err
			}
			if !geometryFinite(segment.Point.X, segment.Point.Y) {
				return "", fmt.Errorf("%w: non-finite geometry point", ErrInvalid)
			}
			switch segment.Kind {
			case GeometryLine:
				output.WriteString(" L")
			case GeometryCubic:
				if !geometryFinite(segment.Control1.X, segment.Control1.Y, segment.Control2.X, segment.Control2.Y) {
					return "", fmt.Errorf("%w: non-finite geometry control point", ErrInvalid)
				}
				output.WriteString(" C")
				output.WriteString(encodePoint(segment.Control1))
				output.WriteByte(' ')
				output.WriteString(encodePoint(segment.Control2))
				output.WriteByte(' ')
			case GeometryQuadratic:
				if !geometryFinite(segment.Control1.X, segment.Control1.Y) {
					return "", fmt.Errorf("%w: non-finite geometry control point", ErrInvalid)
				}
				output.WriteString(" Q")
				output.WriteString(encodePoint(segment.Control1))
				output.WriteByte(' ')
			case GeometryArc:
				if !geometryFinite(segment.RadiusX, segment.RadiusY, segment.RotationAngle) || segment.RadiusX < 0 || segment.RadiusY < 0 {
					return "", fmt.Errorf("%w: invalid geometry arc parameters", ErrInvalid)
				}
				output.WriteString(" A")
				output.WriteString(encodeNumber(segment.RadiusX))
				output.WriteByte(',')
				output.WriteString(encodeNumber(segment.RadiusY))
				output.WriteByte(' ')
				output.WriteString(encodeNumber(segment.RotationAngle))
				output.WriteByte(' ')
				output.WriteString(encodeFlag(segment.IsLargeArc))
				output.WriteByte(' ')
				output.WriteString(encodeFlag(segment.SweepClockwise))
				output.WriteByte(' ')
			default:
				return "", fmt.Errorf("%w: unknown geometry segment", ErrInvalid)
			}
			output.WriteString(encodePoint(segment.Point))
			if int64(output.Len()) > p.limits.MaxPartBytes-p.bytes {
				return "", fmt.Errorf("%w: geometry encoding bytes", ErrLimit)
			}
		}
		if figure.IsClosed {
			output.WriteString(" Z")
		}
		output.WriteByte(' ')
	}
	return strings.TrimSpace(output.String()), nil
}

// geometrySegment 编码单个显式段，保留段级描边标志及圆弧方向
// 入参: value 路径段, depth 段节点深度
// 返回: *xmlElement 段元素, error 类型或预算错误
func (p *pageEncoder) geometrySegment(value GeometrySegment, depth int) (*xmlElement, error) {
	if !geometryFinite(value.Point.X, value.Point.Y) {
		return nil, fmt.Errorf("%w: non-finite geometry point", ErrInvalid)
	}
	name, points := "", ""
	switch value.Kind {
	case GeometryLine:
		name, points = "PolyLineSegment", encodePoint(value.Point)
	case GeometryCubic:
		if !geometryFinite(value.Control1.X, value.Control1.Y, value.Control2.X, value.Control2.Y) {
			return nil, fmt.Errorf("%w: non-finite geometry control point", ErrInvalid)
		}
		name, points = "PolyBezierSegment", encodePoint(value.Control1)+" "+encodePoint(value.Control2)+" "+encodePoint(value.Point)
	case GeometryQuadratic:
		if !geometryFinite(value.Control1.X, value.Control1.Y) {
			return nil, fmt.Errorf("%w: non-finite geometry control point", ErrInvalid)
		}
		name, points = "PolyQuadraticBezierSegment", encodePoint(value.Control1)+" "+encodePoint(value.Point)
	case GeometryArc:
		if !geometryFinite(value.RadiusX, value.RadiusY, value.RotationAngle) || value.RadiusX < 0 || value.RadiusY < 0 {
			return nil, fmt.Errorf("%w: invalid geometry arc parameters", ErrInvalid)
		}
		name = "ArcSegment"
	default:
		return nil, fmt.Errorf("%w: unknown geometry segment", ErrInvalid)
	}
	node, err := p.node(name, depth)
	if err != nil {
		return nil, err
	}
	if err := p.attr(node, "IsStroked", strconv.FormatBool(value.IsStroked)); err != nil {
		return nil, err
	}
	if value.Kind != GeometryArc {
		return node, p.attr(node, "Points", points)
	}
	sweep := "Counterclockwise"
	if value.SweepClockwise {
		sweep = "Clockwise"
	}
	for _, attr := range []struct{ name, value string }{{"Point", encodePoint(value.Point)}, {"Size", encodeNumber(value.RadiusX) + "," + encodeNumber(value.RadiusY)}, {"RotationAngle", encodeNumber(value.RotationAngle)}, {"IsLargeArc", strconv.FormatBool(value.IsLargeArc)}, {"SweepDirection", sweep}} {
		if err := p.attr(node, attr.name, attr.value); err != nil {
			return nil, err
		}
	}
	return node, nil
}

// encodeFlag 输出紧凑几何使用的单字符布尔标志
// 入参: value 标志值
// 返回: string 零或一
func encodeFlag(value bool) string {
	if value {
		return "1"
	}
	return "0"
}
