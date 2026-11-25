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
	"crypto/sha256"
	"encoding/xml"
	"errors"
	"fmt"
	"maps"
	"mime"
	"net/url"
	"slices"
	"strings"
)

// resourceDictionaryContentType 定义XPS远程资源字典的OPC内容类型
const resourceDictionaryContentType = "application/vnd.ms-package.xps-resourcedictionary+xml"

// openXPS3DNamespace 定义OpenXPS 3D模型扩展命名空间
const openXPS3DNamespace = "http://schemas.openxps.org/oxps-3d/v1.0"

// resourceDefinition 保存带类型的资源定义及其原始定义位置
type resourceDefinition struct {
	Key     string
	Kind    string
	Part    string
	Element *xmlElement
}

// resourceScope 保存当前字典与外层查找作用域
type resourceScope struct {
	Parent  *resourceScope
	Entries map[string]*resourceDefinition
	remote  bool
}

// resourceGraph 保存按定义顺序绑定的资源引用和部件来源
type resourceGraph struct {
	PagePart    string
	Nodes       []*xmlElement
	Definitions []*resourceDefinition
	Bindings    map[*xmlElement]map[string]*resourceDefinition
	Parts       map[*xmlElement]string
	RemoteParts []string
}

// resourceLoader 从包内加载已完成命名空间校验和MCE处理的远程字典
type resourceLoader func(part string) (*xmlElement, error)

// resourceParser 保存单页资源图的解析状态与累计限制
type resourceParser struct {
	format     Format
	limits     Limits
	context    context.Context
	load       resourceLoader
	graph      *resourceGraph
	remote     map[string]*resourceScope
	nodes      int
	skipRemote bool
}

// resourceModelContext 保存原始画刷的逻辑父节点及所在Path，不跨兼容分支继承兄弟状态
type resourceModelContext struct {
	parent     *xmlElement
	path       *xmlElement
	alternate  *xmlElement
	choicePath *xmlElement
}

// resourceAttributeReference 保存属性语义值中的部件URI范围，不包含集合索引、表达式或颜色分量
type resourceAttributeReference struct {
	xmlAttributeRange
	uri  string
	kind requiredResourceKind
}

// resourceReachability 保存部件引用、保留根及不透明模型的潜在依赖身份
type resourceReachability struct {
	edges  map[string]map[string]bool
	roots  map[string]bool
	budget *resourceMergeBudget
	models map[string]bool
	parts  []string
}

// OptimizationOptions 设置资源优化的扫描字节、遍历、比对、重写工作上限及紧凑字体字形重映射，零值采用包上限
// 快照校验及字体使用预检沿用阅读器上限，CompactGIDs仅作用于Package.SubsetFonts
type OptimizationOptions struct {
	MaxBytes    int64
	MaxWork     int
	CompactGIDs bool
}

// ResourceOptimization 记录字体子集化或图像重压缩前后的逻辑字节数及替换状态
// Bytes不表示ZIP压缩后的大小，Err说明因格式能力或编辑许可而保留的资源；整次操作失败时返回nil且不修改包
type ResourceOptimization struct {
	Part          string
	OriginalBytes int64
	Bytes         int64
	Changed       bool
	Err           error
}

// ResourceMerge 记录被合并部件、保留目标及移除的逻辑资源字节数，不表示ZIP压缩后大小
type ResourceMerge struct {
	Part   string
	Target string
	Bytes  int64
}

// resourceMergeKey 按类型、保留身份、比较长度及摘要索引候选，最终仍逐字节确认比较数据相同
type resourceMergeKey struct {
	media  string
	scope  string
	length int
	digest [32]byte
}

// resourceMergeCandidate 保存候选资源、比较类别及已解除字体混淆的数据视图
type resourceMergeCandidate struct {
	part packagePart
	data []byte
	kind requiredResourceKind
}

// resourceMergeBudget 累计资源优化扫描及工作单元，同一部件重复读取不重复计入扫描字节
type resourceMergeBudget struct {
	bytes   int64
	work    int
	seen    map[string]bool
	context context.Context
}

// resourceAlternateState 保存单个mc:AlternateContent块在词元遍历期间的分支选择与ProcessContent包装深度
type resourceAlternateState struct {
	depth         int
	selected      bool
	sawFallback   bool
	choices       int
	contentDepths []int
}

// resourceMarkupScopeTracker 在词元遍历期间维护MCE作用域栈，识别合法可忽略及保留扩展
type resourceMarkupScopeTracker struct {
	format          Format
	models          bool
	selectAlternate bool
	ignoreOnly      bool
	processor       compatibilityProcessor
	scopes          []compatibilityScope
	ignoredDepth    int
	preservedDepth  int
	alternates      []resourceAlternateState
}

// ResourceRemoval 记录移除的标准资源及其逻辑字节数，包含一并移除的附属关系标记
// Bytes不是ZIP压缩后的节省量；不会把非资源附件或签名部件当作清理候选
type ResourceRemoval struct {
	Part  string
	Bytes int64
}

// DefaultOptimizationOptions 返回资源优化的默认扫描字节及工作量上限
// 返回: OptimizationOptions 资源优化选项
func DefaultOptimizationOptions() OptimizationOptions {
	limits := DefaultLimits()
	return OptimizationOptions{MaxBytes: limits.MaxPackageBytes, MaxWork: limits.MaxXMLNodes}
}

// parseResourceGraph 按文档格式建立单页资源图，并将引用绑定固定于定义时的查找结果
// 入参: part 页面部件URI, root 预处理页面, format 文档格式, limits 累计节点与深度上限, load 包内字典加载器
// 返回: *resourceGraph 资源图, error 结构、引用或资源限制错误
func parseResourceGraph(part string, root *xmlElement, format Format, limits Limits, load resourceLoader) (*resourceGraph, error) {
	return parseResourceGraphContext(part, root, format, limits, load, nil)
}

// parseResourceGraphContext 共用资源图绑定，在每个节点及字典读取前检查取消
// 入参: part 页面URI, root 预处理页面, format 格式, limits 单页资源图上限, load 字典读取器, ctx 取消Context
// 返回: *resourceGraph 独立资源图, error 结构、引用、预算或取消错误
func parseResourceGraphContext(part string, root *xmlElement, format Format, limits Limits, load resourceLoader, ctx context.Context) (*resourceGraph, error) {
	return parseResourceGraphMode(part, root, format, limits, load, ctx, false)
}

// parseResourceGraphMode 按可选跳过远程字典模式建立单页资源图，skipRemote为真时仅校验远程字典Source与本地可解析绑定
// 入参: part 页面URI, root 预处理页面, format 格式, limits 单页资源图上限, load 字典读取器, ctx 取消Context, skipRemote 是否跳过未加载的远程字典
// 返回: *resourceGraph 独立资源图, error 结构、引用、预算或取消错误
func parseResourceGraphMode(part string, root *xmlElement, format Format, limits Limits, load resourceLoader, ctx context.Context, skipRemote bool) (*resourceGraph, error) {
	if formatNamespace(format) == "" || limits.MaxXMLNodes < 1 || limits.MaxXMLDepth < 1 || limits.MaxPartCount < 1 {
		return nil, fmt.Errorf("%w: invalid resource parser configuration", ErrInvalid)
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	if root == nil || root.Name != (xml.Name{Space: formatNamespace(format), Local: "FixedPage"}) {
		return nil, fmt.Errorf("%w: resource graph requires a FixedPage", ErrInvalid)
	}
	p := &resourceParser{
		format: format, limits: limits, load: load, context: ctx, skipRemote: skipRemote,
		graph:  &resourceGraph{PagePart: canonical, Bindings: make(map[*xmlElement]map[string]*resourceDefinition), Parts: make(map[*xmlElement]string)},
		remote: make(map[string]*resourceScope),
	}
	if err := p.walk(root, canonical, nil, false, false, 1); err != nil {
		return nil, err
	}
	return p.graph, nil
}

// lookup 从内到外查找已加入字典的资源，键名按字符精确匹配
// 入参: key 资源键
// 返回: *resourceDefinition 匹配定义，未找到时为nil
func (s *resourceScope) lookup(key string) *resourceDefinition {
	for current := s; current != nil; current = current.Parent {
		if value := current.Entries[key]; value != nil {
			return value
		}
	}
	return nil
}

// hasRemote 判断当前作用域链上是否存在未加载的远程资源字典占位作用域
// 返回: bool 是否含远程字典作用域
func (s *resourceScope) hasRemote() bool {
	for current := s; current != nil; current = current.Parent {
		if current.remote {
			return true
		}
	}
	return false
}

// enter 校验节点的基础结构并累计页面和远程字典的处理量
// 入参: node 当前元素, part 所属部件, depth 当前递归深度
// 返回: error 基础结构或复杂度错误
func (p *resourceParser) enter(node *xmlElement, part string, depth int) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	if node == nil {
		return &PartError{Part: part, Err: fmt.Errorf("%w: nil resource element", ErrInvalid)}
	}
	p.nodes++
	if depth > p.limits.MaxXMLDepth || p.nodes > p.limits.MaxXMLNodes {
		return &PartError{Part: part, Element: node.Name.Local, Err: fmt.Errorf("%w: resource graph complexity", ErrLimit)}
	}
	if node.Name.Space != formatNamespace(p.format) {
		return &PartError{Part: part, Element: node.Name.Local, Err: fmt.Errorf("%w: resource namespace %q", ErrUnsupported, node.Name.Space)}
	}
	if !xmlWhitespace(node.Text) {
		return &PartError{Part: part, Element: node.Name.Local, Err: fmt.Errorf("%w: text in resource markup", ErrInvalid)}
	}
	p.graph.Parts[node] = part
	p.graph.Nodes = append(p.graph.Nodes, node)
	return nil
}

// walk 遍历定义和页面内容并在声明位置绑定资源引用
// 入参: node 当前元素, part 定义部件, scope 当前作用域, definition 是否为字典直接定义, remote 是否位于远程字典, depth 当前深度
// 返回: error 资源声明或引用错误
func (p *resourceParser) walk(node *xmlElement, part string, scope *resourceScope, definition, remote bool, depth int) error {
	if err := p.enter(node, part, depth); err != nil {
		return err
	}
	key, keyed := node.attributeNS(formatNamespace(p.format)+"/resourcedictionary-key", "Key")
	if keyed != definition || keyed && !fixedNamePattern(key) {
		return resourceError(part, node, "Key must occur exactly on a dictionary definition and match the key pattern")
	}
	if definition {
		if resourceKind(node.Name.Local) == "" {
			return resourceError(part, node, "element cannot be a resource definition")
		}
		if _, named := node.attribute("Name"); named {
			return resourceError(part, node, "resource definition cannot carry Name")
		}
	}
	if node.Name.Local == "ResourceDictionary" || strings.HasSuffix(node.Name.Local, ".Resources") {
		return resourceError(part, node, "misplaced resource dictionary or container")
	}
	for _, attr := range node.Attr {
		if attr.Name.Space != "" {
			if attr.Name.Local == "Key" && attr.Name.Space != formatNamespace(p.format)+"/resourcedictionary-key" {
				return resourceError(part, node, "Key uses an unsupported namespace")
			}
			continue
		}
		expected := resourcePropertyKind(node.Name.Local, attr.Name.Local)
		if expected == "" {
			if attr.Name.Local == "Key" || strings.HasPrefix(strings.TrimLeft(attr.Value, " \t\r\n"), "{StaticResource") && attr.Name.Local != "UnicodeString" && attr.Name.Local != "AutomationProperties.Name" && attr.Name.Local != "AutomationProperties.HelpText" {
				return resourceError(part, node, "unqualified Key or resource reference on an unsupported property")
			}
			continue
		}
		key, reference, err := parseResourceReference(attr.Value)
		if err != nil {
			return &PartError{Part: part, Element: node.Name.Local, Err: fmt.Errorf("%s: %w", attr.Name.Local, err)}
		}
		if !reference {
			if attr.Name.Local == "Visual" || attr.Name.Local == "OpacityMask" {
				return resourceError(part, node, "property requires a resource reference or a property element")
			}
			continue
		}
		value := scope.lookup(key)
		if value == nil {
			if p.skipRemote && scope.hasRemote() {
				continue
			}
			return resourceError(part, node, "unresolved or incompatible resource "+key+" for "+attr.Name.Local)
		}
		if resourceKind(value.Kind) != expected {
			return resourceError(part, node, "unresolved or incompatible resource "+key+" for "+attr.Name.Local)
		}
		if p.graph.Bindings[node] == nil {
			p.graph.Bindings[node] = make(map[string]*resourceDefinition)
		}
		p.graph.Bindings[node][attr.Name.Local] = value
	}
	childScope := scope
	properties := make(map[string]bool)
	for i, child := range node.Children {
		if child == nil {
			return resourceError(part, node, "nil child element")
		}
		owner, property, isProperty := strings.Cut(child.Name.Local, ".")
		if isProperty && property == "Resources" {
			if (node.Name.Local != "FixedPage" && node.Name.Local != "Canvas") || owner != node.Name.Local || i != 0 {
				return resourceError(part, child, "resource container must precede all other content on its owner")
			}
			if err := p.enter(child, part, depth+1); err != nil {
				return err
			}
			if err := resourceContainerAttributes(child, false); err != nil {
				return &PartError{Part: part, Element: child.Name.Local, Err: err}
			}
			if len(child.Children) != 1 {
				return resourceError(part, child, "resource container requires exactly one dictionary")
			}
			var err error
			childScope, err = p.dictionary(child.Children[0], part, scope, remote, depth+2)
			if err != nil {
				return err
			}
			continue
		}
		if isProperty {
			expected := resourcePropertyKind(owner, property)
			if expected != "" {
				_, attribute := node.attribute(property)
				if owner != node.Name.Local || properties[property] || attribute || len(child.Children) != 1 || child.Children[0] == nil || resourceKind(child.Children[0].Name.Local) != expected {
					return resourceError(part, child, "invalid or duplicate resource-valued property")
				}
				properties[property] = true
				if err := resourceContainerAttributes(child, false); err != nil {
					return &PartError{Part: part, Element: child.Name.Local, Err: err}
				}
			}
		}
		if err := p.walk(child, part, childScope, false, remote, depth+1); err != nil {
			return err
		}
	}
	return nil
}

// dictionary 顺序解析资源字典，定义的引用解析完成后才将其键加入作用域
// 入参: node 字典元素, part 定义部件, parent 外层作用域, remote 是否为远程内容, depth 当前深度
// 返回: *resourceScope 已完成的字典作用域, error 字典或引用错误
func (p *resourceParser) dictionary(node *xmlElement, part string, parent *resourceScope, remote bool, depth int) (*resourceScope, error) {
	if err := p.enter(node, part, depth); err != nil {
		return nil, err
	}
	if node.Name.Local != "ResourceDictionary" {
		return nil, resourceError(part, node, "expected ResourceDictionary")
	}
	if err := resourceContainerAttributes(node, true); err != nil {
		return nil, &PartError{Part: part, Element: node.Name.Local, Err: err}
	}
	if source, ok := node.attribute("Source"); ok {
		if len(node.Children) != 0 || remote {
			return nil, resourceError(part, node, "Source forbids local definitions and remote resource dictionaries cannot specify Source")
		}
		target, err := resolvePart(part, strings.Trim(source, " \t\r\n"))
		if err != nil {
			return nil, &PartError{Part: part, Element: node.Name.Local, Err: err}
		}
		if p.skipRemote {
			key := strings.ToLower(target)
			if p.remote[key] == nil {
				if len(p.graph.RemoteParts) >= p.limits.MaxPartCount || depth+1 > p.limits.MaxXMLDepth {
					return nil, &PartError{Part: target, Err: fmt.Errorf("%w: remote dictionary count or depth", ErrLimit)}
				}
				p.graph.RemoteParts = append(p.graph.RemoteParts, target)
				p.remote[key] = &resourceScope{remote: true}
			}
			return &resourceScope{Parent: parent, remote: true}, nil
		}
		loaded, err := p.loadRemote(target, depth+1)
		if err != nil {
			return nil, err
		}
		return &resourceScope{Parent: parent, Entries: loaded.Entries}, nil
	}
	scope := &resourceScope{Parent: parent, Entries: make(map[string]*resourceDefinition)}
	for _, child := range node.Children {
		if child == nil {
			return nil, resourceError(part, node, "nil resource definition")
		}
		key, present := child.attributeNS(formatNamespace(p.format)+"/resourcedictionary-key", "Key")
		if !present || !fixedNamePattern(key) || scope.Entries[key] != nil {
			return nil, resourceError(part, child, "missing, invalid or duplicate resource Key")
		}
		if err := p.walk(child, part, scope, true, remote, depth+1); err != nil {
			return nil, err
		}
		value := &resourceDefinition{Key: key, Kind: child.Name.Local, Part: part, Element: child}
		scope.Entries[key] = value
		p.graph.Definitions = append(p.graph.Definitions, value)
	}
	return scope, nil
}

// loadRemote 隔离页面作用域加载远程字典并按部件名缓存解析结果
// 入参: part 规范化部件URI, depth 当前深度
// 返回: *resourceScope 独立远程作用域, error 部件、加载或预算错误
func (p *resourceParser) loadRemote(part string, depth int) (*resourceScope, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	key := strings.ToLower(part)
	if cached := p.remote[key]; cached != nil {
		return cached, nil
	}
	if len(p.graph.RemoteParts) >= p.limits.MaxPartCount || depth > p.limits.MaxXMLDepth {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: remote dictionary count or depth", ErrLimit)}
	}
	if p.load == nil {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: remote dictionary loader unavailable", ErrUnsupported)}
	}
	p.graph.RemoteParts = append(p.graph.RemoteParts, part)
	node, err := p.load(part)
	if err != nil {
		return nil, err
	}
	scope, err := p.dictionary(node, part, nil, true, depth)
	if err != nil {
		return nil, err
	}
	p.remote[key] = scope
	return scope, nil
}

// readResourceDictionaryLoader 共用字典媒体类型、MCE及名称校验，支持调用私有读取策略
// 入参: part 字典部件URI, load 可选XML读取器, ctx 取消Context
// 返回: *xmlElement 只读预处理字典, error 读取、类型、XML或取消错误
func (r *Reader) readResourceDictionaryLoader(part string, load xmlPartLoader, ctx context.Context) (*xmlElement, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if !requiredResourceMedia(requiredDictionary, media) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: unexpected resource dictionary content type %q", ErrInvalid, media)}
	}
	if load == nil {
		load = func(name string) (*xmlElement, error) { return r.pkg.readXMLPart(name, ctx) }
	}
	root, err := load(part)
	if err == nil {
		ns := formatNamespace(r.format)
		root, err = preprocessXMLContext(root, []string{ns, ns + "/resourcedictionary-key"}, ctx)
	}
	if err == nil {
		err = fixedChild(root, r.format, "ResourceDictionary")
	}
	if err == nil {
		err = validateFixedNames(root, r.format)
	}
	if err == nil {
		err = checkContext(ctx)
	}
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	return root, nil
}

// parseResourceReference 按ST_RscRef解析静态资源引用，不修剪键名或接受前导空白
// 入参: value 属性原值
// 返回: string 资源键, bool 是否为资源引用, error 引用词法错误
func parseResourceReference(value string) (string, bool, error) {
	if !strings.HasPrefix(strings.TrimLeft(value, " \t\r\n"), "{") {
		return "", false, nil
	}
	const prefix = "{StaticResource"
	if !strings.HasPrefix(value, prefix) || len(value) <= len(prefix) || !xmlSpace(value[len(prefix)]) {
		return "", true, fmt.Errorf("%w: invalid static resource expression %q", ErrInvalid, value)
	}
	rest := strings.TrimLeft(value[len(prefix):], " \t\r\n")
	key, suffix, closed := strings.Cut(rest, "}")
	if !closed || !fixedNamePattern(key) || !xmlWhitespace(suffix) {
		return "", true, fmt.Errorf("%w: invalid static resource key or terminator %q", ErrInvalid, value)
	}
	return key, true, nil
}

// resourceKind 返回字典允许的资源类型分组
// 入参: element 元素本地名称
// 返回: string 资源类型分组，不允许的元素返回空字符串
func resourceKind(element string) string {
	switch element {
	case "SolidColorBrush", "ImageBrush", "LinearGradientBrush", "RadialGradientBrush", "VisualBrush":
		return "brush"
	case "MatrixTransform":
		return "matrix"
	case "PathGeometry":
		return "geometry"
	case "Path", "Glyphs", "Canvas":
		return "visual"
	}
	return ""
}

// resourcePropertyKind 返回允许静态资源引用的属性所需类型
// 入参: element 所属元素本地名称, property 属性本地名称
// 返回: string 所需资源类型，不支持引用的属性返回空字符串
func resourcePropertyKind(element, property string) string {
	switch element {
	case "Canvas", "Path", "Glyphs":
		switch property {
		case "RenderTransform":
			return "matrix"
		case "Clip":
			return "geometry"
		case "OpacityMask":
			return "brush"
		case "Fill":
			if element != "Canvas" {
				return "brush"
			}
		case "Stroke":
			if element == "Path" {
				return "brush"
			}
		case "Data":
			if element == "Path" {
				return "geometry"
			}
		}
	case "ImageBrush", "VisualBrush", "LinearGradientBrush", "RadialGradientBrush", "PathGeometry":
		if property == "Transform" {
			return "matrix"
		}
		if element == "VisualBrush" && property == "Visual" {
			return "visual"
		}
	}
	return ""
}

// resourceContainerAttributes 校验字典和资源属性容器的属性集合
// 入参: node 容器元素, dictionary 是否允许Source属性
// 返回: error 非法属性错误
func resourceContainerAttributes(node *xmlElement, dictionary bool) error {
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) || dictionary && attr.Name == (xml.Name{Local: "Source"}) {
			continue
		}
		return fmt.Errorf("%w: attribute %s on resource container", ErrInvalid, attr.Name.Local)
	}
	return nil
}

// resourceError 生成带定义位置的资源结构错误
// 入参: part 所属部件, node 当前元素, message 错误描述
// 返回: error 可定位的资源错误
func resourceError(part string, node *xmlElement, message string) error {
	return &PartError{Part: part, Element: node.Name.Local, Err: fmt.Errorf("%w: %s", ErrInvalid, message)}
}

// resourceModelBrushAttributes 核对OpenXPS 3D模型画刷的属性及词法形式，不解析模型或资源键目标
// 入参: node 原始模型画刷
// 返回: error 未知属性、必选项、矩形或变换错误
func resourceModelBrushAttributes(node *xmlElement) error {
	if node.Name != (xml.Name{Space: openXPS3DNamespace, Local: "Brush3D"}) {
		return fmt.Errorf("%w: preserved 3D element %s", ErrUnsupported, node.Name.Local)
	}
	values := make(map[string]string)
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if attr.Name.Space == mcNamespace {
			if !slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attr.Name.Local) {
				return fmt.Errorf("%w: model brush compatibility attribute %s", ErrUnsupported, attr.Name.Local)
			}
			continue
		}
		if attr.Name == (xml.Name{Space: openXPSNamespace + "/resourcedictionary-key", Local: "Key"}) {
			if !fixedNamePattern(attr.Value) {
				return fmt.Errorf("%w: model brush resource key", ErrInvalid)
			}
			continue
		}
		if attr.Name.Space != "" || !slices.Contains([]string{"Source3D", "Transform", "Viewbox", "Viewport", "ViewboxUnits", "ViewportUnits"}, attr.Name.Local) {
			return fmt.Errorf("%w: preserved model brush attribute {%s}%s", ErrUnsupported, attr.Name.Space, attr.Name.Local)
		}
		values[attr.Name.Local] = attr.Value
	}
	for _, name := range []string{"Source3D", "Viewbox", "Viewport", "ViewboxUnits", "ViewportUnits"} {
		if _, found := values[name]; !found {
			return fmt.Errorf("%w: missing model brush %s", ErrInvalid, name)
		}
	}
	if _, err := resourceAttributeReferences(node, xml.Attr{Name: xml.Name{Local: "Source3D"}, Value: values["Source3D"]}); err != nil {
		return err
	}
	if values["ViewboxUnits"] != "Absolute" || values["ViewportUnits"] != "Absolute" {
		return fmt.Errorf("%w: model brush units must be Absolute", ErrInvalid)
	}
	for _, name := range []string{"Viewbox", "Viewport"} {
		if _, err := brushViewbox(values[name]); err != nil {
			return err
		}
	}
	if transform, found := values["Transform"]; found {
		if _, reference, err := parseResourceReference(transform); err != nil {
			return err
		} else if !reference {
			if _, err := ParseMatrix(transform); err != nil {
				return err
			}
		}
	}
	return nil
}

// validateResourceModelTree 校验保留画刷的位置、字典键及属性元素，不将3D能力加入消费理解集
// 入参: root 未过滤原树, format 包格式, budget 累计遍历预算
// 返回: error 画刷位置、回退、字典键、变换或预算错误
func validateResourceModelTree(root *xmlElement, format Format, budget *resourceMergeBudget) error {
	if format != FormatOpenXPS {
		return fmt.Errorf("%w: model brush format", ErrUnsupported)
	}
	var walk func(*xmlElement, *xmlElement, resourceModelContext) error
	walk = func(node, rawParent *xmlElement, context resourceModelContext) error {
		if err := budget.charge(1 + len(node.Attr)); err != nil {
			return err
		}
		if node.Name == (xml.Name{Space: mcNamespace, Local: "Choice"}) {
			requires, _ := node.attribute("Requires")
			for _, prefix := range compatibilityWords(requires) {
				if node.Namespaces[prefix] == openXPS3DNamespace {
					context.alternate, context.choicePath = rawParent, context.path
				}
			}
		}
		if node.Name.Space == openXPSNamespace && node.Name.Local == "Path" {
			context.path = node
		}
		if node.Name.Space == openXPS3DNamespace {
			if err := resourceModelBrushAttributes(node); err != nil {
				return err
			}
			if !xmlWhitespace(node.Text) {
				return fmt.Errorf("%w: model brush character data", ErrInvalid)
			}
			dictionary := context.parent != nil && context.parent.Name == (xml.Name{Space: openXPSNamespace, Local: "ResourceDictionary"})
			_, keyed := node.attributeNS(openXPSNamespace+"/resourcedictionary-key", "Key")
			if keyed != dictionary {
				return fmt.Errorf("%w: model brush key scope", ErrInvalid)
			}
			if !dictionary {
				if context.parent == nil || context.parent.Name != (xml.Name{Space: openXPSNamespace, Local: "Path.Fill"}) || context.path == nil || context.choicePath != context.path || context.alternate == nil || context.alternate.Name != (xml.Name{Space: mcNamespace, Local: "AlternateContent"}) {
					return fmt.Errorf("%w: model brush requires compatible Path.Fill", ErrInvalid)
				}
				fallback := false
				for _, child := range context.alternate.Children {
					fallback = fallback || child.Name == (xml.Name{Space: mcNamespace, Local: "Fallback"})
				}
				if !fallback {
					return fmt.Errorf("%w: model brush requires a 2D fallback", ErrInvalid)
				}
				if _, present := context.path.attribute("Fill"); present {
					return fmt.Errorf("%w: model brush duplicates Path.Fill", ErrInvalid)
				}
			}
			_, maximum, err := resourceModelChildBounds(node, "ImageBrush.Transform", budget)
			if err != nil {
				return err
			}
			_, transform := node.attribute("Transform")
			if maximum > 1 || transform && maximum != 0 {
				return fmt.Errorf("%w: duplicate model brush transform", ErrInvalid)
			}
		}
		if node.Name.Space != mcNamespace {
			context.parent = node
		}
		for _, child := range node.Children {
			if err := walk(child, node, context); err != nil {
				return err
			}
		}
		return nil
	}
	return walk(root, nil, resourceModelContext{})
}

// resourceModelChildBounds 核对各兼容分支的逻辑属性元素数量，不将备选分支的元素数相加
// 入参: node 属性拥有节点, expected 允许的固定布局子元素, budget 累计遍历预算
// 返回: int 最少数量, int 至多数量，超过一个时截为二, error 属性元素、矩阵、兼容结构或预算错误
func resourceModelChildBounds(node *xmlElement, expected string, budget *resourceMergeBudget) (int, int, error) {
	if err := budget.charge(1 + len(node.Children)); err != nil {
		return 0, 0, err
	}
	if !xmlWhitespace(node.Text) {
		return 0, 0, fmt.Errorf("%w: model transform character data", ErrInvalid)
	}
	minimum, maximum := 0, 0
	for _, child := range node.Children {
		low, high := 1, 1
		if child.Name == (xml.Name{Space: mcNamespace, Local: "AlternateContent"}) {
			low, high = 2, 0
			guaranteed := false
			for _, branch := range child.Children {
				if branch.Name.Space != mcNamespace || branch.Name.Local != "Choice" && branch.Name.Local != "Fallback" {
					return 0, 0, fmt.Errorf("%w: model transform compatibility branch", ErrInvalid)
				}
				if branch.Name.Local == "Fallback" {
					guaranteed = true
				} else {
					requires, _ := branch.attribute("Requires")
					words := compatibilityWords(requires)
					known := len(words) != 0
					for _, prefix := range words {
						uri := branch.Namespaces[prefix]
						known = known && (uri == openXPSNamespace || uri == openXPSNamespace+"/resourcedictionary-key" || uri == openXPS3DNamespace || uri == mcNamespace || uri == xmlNamespace)
					}
					guaranteed = guaranteed || known
				}
				a, b, err := resourceModelChildBounds(branch, expected, budget)
				if err != nil {
					return 0, 0, err
				}
				low, high = min(low, a), max(high, b)
			}
			if !guaranteed {
				low = 0
			}
		} else {
			if expected == "" || child.Name != (xml.Name{Space: openXPSNamespace, Local: expected}) {
				return 0, 0, fmt.Errorf("%w: model brush property element", ErrInvalid)
			}
			value := *child
			value.Attr = slices.DeleteFunc(slices.Clone(child.Attr), func(attr xml.Attr) bool { return attr.Name.Space == mcNamespace })
			allowed := []string(nil)
			if expected == "MatrixTransform" {
				allowed = []string{"Matrix"}
			}
			attrs, err := geometryXMLAttributes(&value, openXPSNamespace, expected, false, allowed...)
			if err != nil {
				return 0, 0, err
			}
			next := "MatrixTransform"
			if expected == "MatrixTransform" {
				text, err := geometryXMLRequired(attrs, "Matrix")
				if err != nil {
					return 0, 0, err
				}
				if _, err := ParseMatrix(text); err != nil {
					return 0, 0, err
				}
				next = ""
			}
			a, b, err := resourceModelChildBounds(child, next, budget)
			if err != nil || expected == "ImageBrush.Transform" && (a != 1 || b != 1) || expected == "MatrixTransform" && b != 0 {
				if err == nil {
					err = fmt.Errorf("%w: model brush transform cardinality", ErrInvalid)
				}
				return 0, 0, err
			}
		}
		minimum, maximum = min(2, minimum+low), min(2, maximum+high)
	}
	return minimum, maximum, nil
}

// resourceAttributeReferences 从固定布局及3D画刷属性中提取部件URI范围，忽略静态资源键
// 入参: node 属性所属元素, attribute 已展开命名空间的属性
// 返回: []resourceAttributeReference 属性内引用, error 引用语法错误
func resourceAttributeReferences(node *xmlElement, attribute xml.Attr) ([]resourceAttributeReference, error) {
	if node != nil && node.Name == (xml.Name{Space: openXPS3DNamespace, Local: "Brush3D"}) && attribute.Name == (xml.Name{Local: "Source3D"}) {
		value := strings.Trim(attribute.Value, " \t\r\n")
		if value == "" || strings.HasPrefix(value, "{") || !uriReference(value) {
			return nil, fmt.Errorf("%w: model Source3D URI", ErrInvalid)
		}
		start := len(attribute.Value) - len(strings.TrimLeft(attribute.Value, " \t\r\n"))
		uri := value
		if end := strings.IndexAny(uri, "?#"); end >= 0 {
			uri = uri[:end]
		}
		if uri == "" {
			return nil, fmt.Errorf("%w: model Source3D part", ErrInvalid)
		}
		return []resourceAttributeReference{{xmlAttributeRange{start, start + len(uri)}, uri, requiredModel}}, nil
	}
	if node == nil || node.Name.Space != xpsNamespace && node.Name.Space != openXPSNamespace || attribute.Name.Space != "" {
		return nil, nil
	}
	value := attribute.Value
	trimmed := strings.Trim(value, " \t\r\n")
	start := len(value) - len(strings.TrimLeft(value, " \t\r\n"))
	switch {
	case node.Name.Local == "ResourceDictionary" && attribute.Name.Local == "Source":
		if trimmed == "" {
			return nil, fmt.Errorf("%w: empty resource dictionary Source", ErrInvalid)
		}
		return []resourceAttributeReference{{xmlAttributeRange{start, start + len(trimmed)}, trimmed, requiredDictionary}}, nil
	case node.Name.Local == "Glyphs" && attribute.Name.Local == "FontUri":
		uri, _, _, err := ParseFontURI(trimmed)
		if err != nil {
			return nil, err
		}
		return []resourceAttributeReference{{xmlAttributeRange{start, start + len(uri)}, uri, requiredFont}}, nil
	case node.Name.Local == "ImageBrush" && attribute.Name.Local == "ImageSource":
		uri, profile, err := parseBrushImageSource(value)
		if err != nil {
			return nil, err
		}
		if profile == "" {
			return []resourceAttributeReference{{xmlAttributeRange{start, start + len(trimmed)}, uri, requiredImage}}, nil
		}
		start += len("{ColorConvertedBitmap")
		start += len(value[start:]) - len(strings.TrimLeft(value[start:], " \t\r\n"))
		end := start + len(uri)
		profileStart := end + len(value[end:]) - len(strings.TrimLeft(value[end:], " \t\r\n"))
		return []resourceAttributeReference{{xmlAttributeRange{start, end}, uri, requiredImage}, {xmlAttributeRange{profileStart, profileStart + len(profile)}, profile, requiredProfile}}, nil
	case requiredColorAttribute(node.Name.Local, attribute.Name.Local):
		if _, reference, err := parseResourceReference(value); reference || err != nil {
			return nil, err
		}
		color, err := parseBrushColor(value, node.Name.Space)
		if err != nil {
			return nil, err
		}
		if color.ProfileURI == "" {
			return nil, nil
		}
		start = strings.Index(value, "ContextColor") + len("ContextColor")
		start += len(value[start:]) - len(strings.TrimLeft(value[start:], " \t\r\n"))
		return []resourceAttributeReference{{xmlAttributeRange{start, start + len(color.ProfileURI)}, color.ProfileURI, requiredProfile}}, nil
	}
	return nil, nil
}

// rewriteResourceAttribute 按别名表重写属性内的部件引用并保持相对路径，保留字体索引与颜色表达式
// 入参: source 定义部件, node 属性所属元素, attribute 原属性, aliases 资源别名
// 返回: string 新属性值, bool 是否改变, error 引用或目标URI错误
func rewriteResourceAttribute(source string, node *xmlElement, attribute xml.Attr, aliases map[string]string) (string, bool, error) {
	references, err := resourceAttributeReferences(node, attribute)
	if err != nil {
		return "", false, err
	}
	var output strings.Builder
	position := 0
	changed := false
	for _, reference := range references {
		part, err := resolvePart(source, reference.uri)
		if err != nil {
			return "", false, err
		}
		target, present := aliases[strings.ToLower(part)]
		if !present || strings.EqualFold(part, target) {
			continue
		}
		target, err = relativePart(source, target)
		if err != nil {
			return "", false, err
		}
		output.WriteString(attribute.Value[position:reference.start])
		output.WriteString(target)
		position = reference.end
		changed = true
	}
	if !changed {
		return attribute.Value, false, nil
	}
	output.WriteString(attribute.Value[position:])
	return output.String(), true, nil
}

// resourceDictionaryIdentity 生成用于等价比较的字典规范副本，解析包内引用并保留未知属性与原部件身份
// 入参: part 原部件, format 包格式, limits 包上限, budget 累计工作及取消预算, aliases 已确认的资源别名
// 返回: []byte 比较数据, string 需保留的部件身份，空值可跨部件比较, error XML、引用或预算错误
func resourceDictionaryIdentity(part packagePart, format Format, limits Limits, budget *resourceMergeBudget, aliases map[string]string) ([]byte, string, error) {
	scope := ""
	tracker := newResourceMarkupScopeTracker(format, format == FormatOpenXPS, budget.context)
	_, err := decodeXMLVisit(part.data, limits, func(token xml.Token, node *xmlElement) error {
		skip, mceScope, err := tracker.visit(token, node)
		if err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := budget.charge(1); err != nil {
			return err
		}
		if skip {
			scope = strings.ToLower(part.name)
			return nil
		}
		for _, a := range node.Attr {
			if a.Name.Space != "" && mceScope.ignorable[a.Name.Space] {
				scope = strings.ToLower(part.name)
				continue
			}
			if !dictionaryKnownAttribute(node, a, format) {
				scope = strings.ToLower(part.name)
			}
		}
		return nil
	})
	if err != nil {
		return nil, "", err
	}
	rewriteTracker := newResourceMarkupScopeTracker(format, format == FormatOpenXPS, budget.context)
	data, _, err := rewriteXMLAttributes(part.data, limits, budget.context, nil, func(token xml.Token, node *xmlElement) (bool, error) {
		skip, _, err := rewriteTracker.visit(token, node)
		return skip, err
	}, func(node *xmlElement, a xml.Attr) (string, bool, error) {
		if err := budget.charge(1); err != nil {
			return "", false, err
		}
		refs, err := resourceAttributeReferences(node, a)
		if err != nil {
			return "", false, err
		}
		if resourceIdentityAttribute(node, a, format) {
			scope = strings.ToLower(part.name)
		}
		if len(refs) == 0 {
			return a.Value, false, nil
		}
		var output strings.Builder
		position := 0
		for _, ref := range refs {
			target, err := resolvePart(part.name, ref.uri)
			if err != nil {
				return "", false, err
			}
			for {
				alias, present := aliases[strings.ToLower(target)]
				if !present {
					break
				}
				if err := budget.charge(1); err != nil {
					return "", false, err
				}
				target = alias
			}
			output.WriteString(a.Value[position:ref.start])
			output.WriteString(strings.ToLower(target))
			position = ref.end
		}
		output.WriteString(a.Value[position:])
		value := output.String()
		return value, value != a.Value, nil
	})
	if err != nil {
		return nil, "", err
	}
	data, err = canonicalXML(data, canonicalXMLOptions{limits: limits, context: budget.context, maxBytes: min(limits.MaxPartBytes, limits.MaxPackageBytes), comments: true})
	if err != nil {
		return nil, "", err
	}
	if err := budget.charge(1 + max(0, len(data)-1)/4096); err != nil {
		return nil, "", err
	}
	return data, scope, nil
}

// dictionaryKnownAttribute 识别已掌握引用语义的属性，不推测同命名空间中的未知属性
// 入参: node 所属元素, attribute 已展开属性, format 包格式
// 返回: bool 是否已理解其引用语义
func dictionaryKnownAttribute(node *xmlElement, attribute xml.Attr, format Format) bool {
	if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) || attribute.Name == (xml.Name{Space: xmlNamespace, Local: "lang"}) || attribute.Name == (xml.Name{Space: formatNamespace(format) + "/resourcedictionary-key", Local: "Key"}) {
		return true
	}
	if attribute.Name.Space == mcNamespace {
		return slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attribute.Name.Local)
	}
	if node.Name.Space == mcNamespace {
		return node.Name.Local == "Choice" && attribute.Name == (xml.Name{Local: "Requires"})
	}
	if attribute.Name.Space != "" {
		return false
	}
	if slices.Contains([]string{"Canvas", "Path", "Glyphs"}, node.Name.Local) {
		return true
	}
	var allowed []string
	switch node.Name.Local {
	case "ResourceDictionary":
		allowed = []string{"Source"}
	case "SolidColorBrush":
		allowed = []string{"Opacity", "Color"}
	case "ImageBrush":
		allowed = []string{"Opacity", "Transform", "Viewbox", "Viewport", "ViewboxUnits", "ViewportUnits", "TileMode", "ImageSource"}
	case "VisualBrush":
		allowed = []string{"Opacity", "Transform", "Viewbox", "Viewport", "ViewboxUnits", "ViewportUnits", "TileMode", "Visual"}
	case "LinearGradientBrush":
		allowed = []string{"Opacity", "Transform", "ColorInterpolationMode", "SpreadMethod", "MappingMode", "StartPoint", "EndPoint"}
	case "RadialGradientBrush":
		allowed = []string{"Opacity", "Transform", "ColorInterpolationMode", "SpreadMethod", "MappingMode", "Center", "GradientOrigin", "RadiusX", "RadiusY"}
	case "GradientStop":
		allowed = []string{"Offset", "Color"}
	case "MatrixTransform":
		allowed = []string{"Matrix"}
	case "PathGeometry":
		allowed = []string{"Figures", "FillRule", "Transform"}
	case "PathFigure":
		allowed = []string{"StartPoint", "IsClosed", "IsFilled", "Segments"}
	case "PolyLineSegment", "PolyBezierSegment", "PolyQuadraticBezierSegment":
		allowed = []string{"Points", "IsStroked"}
	case "ArcSegment":
		allowed = []string{"Point", "Size", "RotationAngle", "IsLargeArc", "SweepDirection", "IsStroked"}
	}
	return slices.Contains(allowed, attribute.Name.Local)
}

// resourceReachability 汇总原始标记、内部关系与签名引用，返回保留根可达的全部部件集合
// 入参: budget 扫描及遍历预算
// 返回: map[string]bool 可达部件键, error 标记、引用、预算或取消错误
func (r *Reader) resourceReachability(budget *resourceMergeBudget) (map[string]bool, error) {
	g, err := r.resourceReferenceGraph(budget)
	if err != nil {
		return nil, err
	}
	return g.reachable()
}

// standardResourceMedia 返回标准资源媒体类型对应的资源种类，非标准资源返回零值
// 入参: media 部件内容类型
// 返回: requiredResourceKind 标准资源种类
func standardResourceMedia(media string) requiredResourceKind {
	for _, kind := range []requiredResourceKind{requiredFont, requiredImage, requiredProfile, requiredDictionary} {
		if requiredResourceMedia(kind, media) {
			return kind
		}
	}
	return 0
}

// resourceDictionaryHosts 沿字典引用链展开每个远程字典的宿主页面集合，使用迭代遍历防止环路
// 入参: pages 已排序固定页面列表, dictEdges 部件到远程字典的引用边, budget 累计预算
// 返回: map[string][]string 小写字典键对应的排序宿主页面列表, error 预算或取消错误
func resourceDictionaryHosts(pages []string, dictEdges map[string]map[string]bool, budget *resourceMergeBudget) (map[string][]string, error) {
	hosts := make(map[string][]string)
	for _, page := range pages {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		seen := map[string]bool{strings.ToLower(page): true}
		queue := []string{strings.ToLower(page)}
		for index := 0; index < len(queue); index++ {
			if err := budget.charge(1); err != nil {
				return nil, err
			}
			for _, target := range slices.Sorted(maps.Keys(dictEdges[queue[index]])) {
				if err := budget.charge(1); err != nil {
					return nil, err
				}
				if !seen[target] {
					seen[target] = true
					queue = append(queue, target)
					hosts[target] = append(hosts[target], page)
				}
			}
		}
	}
	return hosts, nil
}

// resolveDictionaryNavigations 按宿主页面集合解析远程字典内导航目标，绝对路径不依赖宿主页面
// 入参: dictPart 远程字典部件名, values 导航URI列表, pageHosts 宿主页面列表, allowOrphan 是否跳过孤立字典的相对导航, budget 累计预算, emit 绑定回调
// 返回: error 导航URI、缺少页面归属、预算或取消错误
func resolveDictionaryNavigations(dictPart string, values, pageHosts []string, allowOrphan bool, budget *resourceMergeBudget, emit func(source, target string) error) error {
	for _, value := range values {
		if err := budget.charge(1); err != nil {
			return err
		}
		normalized := structureURI(value)
		if linkExternal(normalized) {
			continue
		}
		uri, err := url.Parse(normalized)
		if err != nil {
			return &PartError{Part: dictPart, Err: fmt.Errorf("%w: resource navigation URI", ErrInvalid)}
		}
		if uri.RawQuery != "" || uri.ForceQuery {
			return &PartError{Part: dictPart, Err: fmt.Errorf("%w: query in resource navigation", ErrUnsupported)}
		}
		if uri.Path == "" {
			continue
		}
		if strings.HasPrefix(uri.EscapedPath(), "/") {
			target, err := resolvePart("/", uri.EscapedPath())
			if err != nil {
				return &PartError{Part: dictPart, Err: err}
			}
			if len(pageHosts) == 0 {
				if err := emit(dictPart, target); err != nil {
					return err
				}
				continue
			}
			for _, host := range pageHosts {
				if err := emit(host, target); err != nil {
					return err
				}
			}
			continue
		}
		if len(pageHosts) == 0 {
			if allowOrphan {
				continue
			}
			return &PartError{Part: dictPart, Err: fmt.Errorf("%w: dictionary navigation lacks page context", ErrUnsupported)}
		}
		for _, host := range pageHosts {
			target, err := resolvePart(host, uri.EscapedPath())
			if err != nil {
				return &PartError{Part: dictPart, Err: err}
			}
			if err := emit(host, target); err != nil {
				return err
			}
		}
	}
	return nil
}

// resourceReferenceGraph 构造原始部件引用图，包含资源、关系及导航引用边
// 入参: budget 扫描及遍历预算
// 返回: *resourceReachability 已校验引用图, error 标记、引用或预算错误
func (r *Reader) resourceReferenceGraph(budget *resourceMergeBudget) (*resourceReachability, error) {
	return r.resourceReferenceGraphMode(budget, true, false)
}

// resourceReferenceGraphMode 构造原始部件引用图，可按需排除超链接导航边并启用MCE分支选择供资源生存期校验使用
// 入参: budget 扫描及遍历预算, includeNavigation 是否纳入FixedPage.NavigateUri及OutlineTarget导航边, selectAlternate 是否按标准MCE执行AlternateContent分支选择
// 返回: *resourceReachability 已校验引用图, error 标记、引用或预算错误
func (r *Reader) resourceReferenceGraphMode(budget *resourceMergeBudget, includeNavigation, selectAlternate bool) (*resourceReachability, error) {
	if err := budget.charge(len(r.pkg.parts)); err != nil {
		return nil, err
	}
	keys := slices.Sorted(maps.Keys(r.pkg.parts))
	g := resourceReachability{edges: make(map[string]map[string]bool), roots: map[string]bool{"/": true}, budget: budget, parts: keys}
	var pages []string
	dictEdges := make(map[string]map[string]bool)
	dictNavigations := make(map[string][]string)
	for _, key := range keys {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		part := r.pkg.names[key]
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := r.pkg.contentType(part)
		if err != nil {
			return nil, err
		}
		model, err := resourceModelMedia(media)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if standardResourceMedia(media) == 0 && !opcRelationshipName(part) {
			g.roots[key] = true
		}
		if strings.EqualFold(media, fixedContentType("fixedpage")) {
			pages = append(pages, part)
		}
		if model {
			if g.models == nil {
				g.models = make(map[string]bool)
			}
			g.models[key] = true
			continue
		}
		markup := false
		if !opcRelationshipName(part) {
			markup, err = fontUsageMarkup(media)
			if err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
		}
		discard := strings.EqualFold(media, fixedContentType("discard-control"))
		signature := strings.EqualFold(media, opcSignatureType)
		if !markup && !discard && !signature && !opcRelationshipName(part) {
			continue
		}
		data, err := budget.readPart(r.pkg, key)
		if err != nil {
			return nil, err
		}
		if signature {
			references, err := resourceSignatureReferences(data, r.limits, budget)
			if err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			for _, target := range references {
				if err := g.add(part, target); err != nil {
					return nil, err
				}
			}
			continue
		}
		if opcRelationshipName(part) {
			source := relationshipSource(part)
			if err := g.add(source, part); err != nil {
				return nil, err
			}
			if err := g.add(part, source); err != nil {
				return nil, err
			}
			if _, err := decodeXMLVisit(data, r.limits, func(token xml.Token, node *xmlElement) error {
				if _, start := token.(xml.StartElement); !start {
					return nil
				}
				if err := budget.charge(1); err != nil {
					return err
				}
				if err := resourceRelationshipNode(node); err != nil {
					return err
				}
				if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
					return nil
				}
				mode, present := node.attribute("TargetMode")
				if present && TargetMode(mode) == TargetModeExternal {
					return nil
				}
				if present && TargetMode(mode) != TargetModeInternal {
					return fmt.Errorf("%w: resource relationship target mode", ErrInvalid)
				}
				uri, present := node.attribute("Target")
				if !present {
					return fmt.Errorf("%w: resource relationship target", ErrInvalid)
				}
				target, err := resolvePart(source, uri)
				if err != nil {
					return err
				}
				return g.add(source, target)
			}); err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			continue
		}
		dictionary := strings.EqualFold(media, resourceDictionaryContentType)
		modelMarkup := false
		tracker := newResourceMarkupScopeTrackerWithAlternate(r.format, true, selectAlternate, budget.context)
		root, err := decodeXMLVisit(data, r.limits, func(token xml.Token, node *xmlElement) error {
			if discard {
				if _, start := token.(xml.StartElement); !start {
					return nil
				}
				return budget.charge(1)
			}
			skip, _, err := tracker.visit(token, node)
			if err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := budget.charge(1); err != nil {
				return err
			}
			if skip {
				return nil
			}
			modelMarkup = modelMarkup || node.Name.Space == openXPS3DNamespace
			for _, a := range node.Attr {
				if err := budget.charge(1); err != nil {
					return err
				}
				references, err := resourceAttributeReferences(node, a)
				if err != nil {
					return err
				}
				for _, ref := range references {
					target, err := resolvePart(part, ref.uri)
					if err != nil {
						return err
					}
					if ref.kind == requiredDictionary {
						if dictEdges[key] == nil {
							dictEdges[key] = make(map[string]bool)
						}
						dictEdges[key][strings.ToLower(target)] = true
					}
					if ref.kind == requiredModel {
						media, err := r.pkg.contentType(target)
						if err != nil {
							return err
						}
						if !requiredResourceMedia(requiredModel, media) {
							return fmt.Errorf("%w: Source3D target content type", ErrInvalid)
						}
					}
					if err := g.add(part, target); err != nil {
						return err
					}
				}
				if includeNavigation && resourceIdentityAttribute(node, a, r.format) {
					if dictionary && a.Name.Local == "FixedPage.NavigateUri" {
						dictNavigations[key] = append(dictNavigations[key], a.Value)
						continue
					}
					target, err := resourceNavigationPart(part, a.Value)
					if err != nil {
						return err
					}
					if target != "" {
						if err := g.add(part, target); err != nil {
							return err
						}
					}
				}
			}
			return nil
		})
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if modelMarkup {
			if err := validateResourceModelTree(root, r.format, budget); err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
		}
		if discard {
			targets := make(map[string]bool)
			if err := resourceDiscardIdentities(root, part, r.format, targets, budget); err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			for _, target := range slices.Sorted(maps.Keys(targets)) {
				if err := g.add(part, target); err != nil {
					return nil, err
				}
			}
		} else if _, err := preprocessXMLContext(root, []string{formatNamespace(r.format), formatNamespace(r.format) + "/resourcedictionary-key", structureNamespace(r.format)}, budget.context); err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
	}
	if len(dictNavigations) != 0 {
		hosts, err := resourceDictionaryHosts(pages, dictEdges, budget)
		if err != nil {
			return nil, err
		}
		for _, dictKey := range slices.Sorted(maps.Keys(dictNavigations)) {
			if err := resolveDictionaryNavigations(r.pkg.names[dictKey], dictNavigations[dictKey], hosts[dictKey], true, budget, g.add); err != nil {
				return nil, err
			}
		}
	}
	return &g, nil
}

// add 添加规范化引用边，预算检查在分配引用集合之前执行
// 入参: source 引用来源, target 引用目标
// 返回: error 预算或取消错误
func (g *resourceReachability) add(source, target string) error {
	if err := g.budget.charge(1); err != nil {
		return err
	}
	source, target = strings.ToLower(source), strings.ToLower(target)
	if g.edges[source] == nil {
		g.edges[source] = make(map[string]bool)
	}
	g.edges[source][target] = true
	return nil
}

// reachable 使用迭代遍历处理环形引用，仅展开从保留根可达的引用边
// 返回: map[string]bool 可达部件集合, error 预算或取消错误
func (g *resourceReachability) reachable() (map[string]bool, error) {
	return g.reachableFrom(g.roots, true)
}

// reachableFrom 从指定根遍历引用，可选择纳入不透明模型的潜在依赖，不重复展开虚拟闭包
// 入参: roots 本次保留根, potential 是否纳入模型的潜在依赖
// 返回: map[string]bool 可达部件集合, error 预算或取消错误
func (g *resourceReachability) reachableFrom(roots map[string]bool, potential bool) (map[string]bool, error) {
	seen := maps.Clone(roots)
	queue := slices.Sorted(maps.Keys(seen))
	expanded := false
	for index := 0; index < len(queue); index++ {
		if err := g.budget.charge(1); err != nil {
			return nil, err
		}
		if potential && !expanded && g.models[queue[index]] {
			expanded = true
			for _, target := range g.parts {
				if err := g.budget.charge(1); err != nil {
					return nil, err
				}
				if !seen[target] {
					seen[target] = true
					queue = append(queue, target)
				}
			}
		}
		for _, target := range slices.Sorted(maps.Keys(g.edges[queue[index]])) {
			if err := g.budget.charge(1); err != nil {
				return nil, err
			}
			if !seen[target] {
				seen[target] = true
				queue = append(queue, target)
			}
		}
	}
	return seen, nil
}

// resourceIdentityReferences 汇总导航、目录与释放提示中须保持原身份的资源部件集合
// 入参: budget 累计扫描和遍历预算
// 返回: map[string]bool 不应合并的部件键, error 标记、引用或预算错误
func (r *Reader) resourceIdentityReferences(budget *resourceMergeBudget) (map[string]bool, error) {
	result := make(map[string]bool)
	var pages []string
	dictEdges := make(map[string]map[string]bool)
	dictNavigations := make(map[string][]string)
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		part := r.pkg.names[key]
		if key == strings.ToLower(opcTypesName) || opcRelationshipName(part) {
			continue
		}
		media, err := r.pkg.contentType(part)
		if err != nil {
			return nil, err
		}
		if strings.EqualFold(media, fixedContentType("fixedpage")) {
			pages = append(pages, part)
		}
		markup, err := fontUsageMarkup(media)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		discard := strings.EqualFold(media, fixedContentType("discard-control"))
		signature := strings.EqualFold(media, opcSignatureType)
		if !markup && !discard && !signature {
			continue
		}
		data, err := budget.readPart(r.pkg, key)
		if err != nil {
			return nil, err
		}
		if signature {
			if _, err := resourceSignatureReferences(data, r.limits, budget); err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			continue
		}
		dictionary := strings.EqualFold(media, resourceDictionaryContentType)
		root, err := decodeXMLVisit(data, r.limits, func(token xml.Token, node *xmlElement) error {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := budget.charge(1); err != nil {
				return err
			}
			if discard {
				return nil
			}
			for _, a := range node.Attr {
				if a.Name.Space != "" {
					continue
				}
				if node.Name.Space == formatNamespace(r.format) && node.Name.Local == "ResourceDictionary" && a.Name.Local == "Source" {
					references, err := resourceAttributeReferences(node, a)
					if err != nil {
						return err
					}
					for _, ref := range references {
						target, err := resolvePart(part, ref.uri)
						if err != nil {
							return err
						}
						if dictEdges[key] == nil {
							dictEdges[key] = make(map[string]bool)
						}
						dictEdges[key][strings.ToLower(target)] = true
					}
					continue
				}
				if !resourceIdentityAttribute(node, a, r.format) {
					continue
				}
				if dictionary && a.Name.Local == "FixedPage.NavigateUri" {
					dictNavigations[key] = append(dictNavigations[key], a.Value)
					continue
				}
				target, err := resourceNavigationPart(part, a.Value)
				if err != nil {
					return err
				}
				if target != "" {
					result[strings.ToLower(target)] = true
				}
			}
			return nil
		})
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if discard {
			if err := resourceDiscardIdentities(root, part, r.format, result, budget); err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
		}
	}
	if len(dictNavigations) != 0 {
		hosts, err := resourceDictionaryHosts(pages, dictEdges, budget)
		if err != nil {
			return nil, err
		}
		for _, dictKey := range slices.Sorted(maps.Keys(dictNavigations)) {
			if err := resolveDictionaryNavigations(r.pkg.names[dictKey], dictNavigations[dictKey], hosts[dictKey], false, budget, func(_, target string) error {
				result[strings.ToLower(target)] = true
				return nil
			}); err != nil {
				return nil, err
			}
		}
	}
	return result, nil
}

// resourceIdentityAttribute 判断布局导航及目录目标属性，不把一般文字当作部件URI
// 入参: node 属性所属元素, attribute 原始属性, format 包格式
// 返回: bool 是否承载独立身份引用
func resourceIdentityAttribute(node *xmlElement, attribute xml.Attr, format Format) bool {
	if attribute.Name.Space != "" {
		return false
	}
	layout := node.Name.Space == formatNamespace(format) && slices.Contains([]string{"Canvas", "Path", "Glyphs"}, node.Name.Local) && attribute.Name.Local == "FixedPage.NavigateUri"
	outline := node.Name == (xml.Name{Space: structureNamespace(format), Local: "OutlineEntry"}) && attribute.Name.Local == "OutlineTarget"
	return layout || outline
}

// resourceNavigationPart 分离内部导航的部件路径，拒绝内部查询并保留片段的上层处理，不访问外部目标
// 入参: source 定义部件, value 导航URI
// 返回: string 包内目标，外部URI为空, error 内部路径或查询错误
func resourceNavigationPart(source, value string) (string, error) {
	value = structureURI(value)
	if linkExternal(value) {
		return "", nil
	}
	uri, err := url.Parse(value)
	if err != nil {
		return "", fmt.Errorf("%w: resource navigation URI", ErrInvalid)
	}
	if uri.RawQuery != "" || uri.ForceQuery {
		return "", fmt.Errorf("%w: query in resource navigation", ErrUnsupported)
	}
	if uri.Path == "" {
		return source, nil
	}
	return resolvePart(source, uri.EscapedPath())
}

// resourceDiscardIdentities 校验释放提示并保留目标与哨兵部件身份，放行合法可忽略扩展并拒绝未声明未知语义
// 入参: root 原始提示标记, part 提示部件, format 当前格式, reserved 保留身份集合, budget 累计预算
// 返回: error 标记、未理解扩展或预算错误
func resourceDiscardIdentities(root *xmlElement, part string, format Format, reserved map[string]bool, budget *resourceMergeBudget) error {
	if _, err := processDiscardControl(root, part, format, budget.context); err != nil {
		return err
	}
	namespace := formatNamespace(format) + "/discard-control"
	processor := compatibilityProcessor{understood: map[string]bool{namespace: true, mcNamespace: true, xmlNamespace: true}, context: budget.context}
	var visit func(*xmlElement, compatibilityScope) error
	visit = func(node *xmlElement, inherited compatibilityScope) error {
		if err := budget.charge(1); err != nil {
			return err
		}
		scope := inherited
		if format == FormatOpenXPS {
			for _, attr := range node.Attr {
				if attr.Name.Space == mcNamespace && !slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attr.Name.Local) {
					return fmt.Errorf("%w: preserved discard compatibility attribute %s", ErrUnsupported, attr.Name.Local)
				}
			}
			isBranch := node.Name.Space == mcNamespace && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
			var err error
			scope, err = processor.rulesChecked(node, inherited, !isBranch)
			if err != nil {
				if errors.Is(err, ErrInvalid) {
					return fmt.Errorf("%w: %v", ErrUnsupported, err)
				}
				return err
			}
		}
		if node.Name.Space != namespace && node.Name.Space != mcNamespace {
			if format == FormatOpenXPS && scope.ignorable[node.Name.Space] {
				if scope.processes(node.Name) {
					for _, child := range node.Children {
						if err := visit(child, scope); err != nil {
							return err
						}
					}
				}
				return nil
			}
			return fmt.Errorf("%w: preserved discard namespace %q", ErrUnsupported, node.Name.Space)
		}
		if !xmlWhitespace(node.Text) {
			return fmt.Errorf("%w: preserved discard text", ErrUnsupported)
		}
		if node.Name.Space == namespace {
			if node.Name.Local != "DiscardControl" && node.Name.Local != "Discard" {
				return fmt.Errorf("%w: preserved discard element %s", ErrUnsupported, node.Name.Local)
			}
		} else if !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
			return fmt.Errorf("%w: preserved discard namespace %q", ErrUnsupported, node.Name.Space)
		}
		for _, attr := range node.Attr {
			if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
				continue
			}
			if attr.Name.Space == mcNamespace {
				if !slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attr.Name.Local) {
					return fmt.Errorf("%w: preserved discard compatibility attribute %s", ErrUnsupported, attr.Name.Local)
				}
				continue
			}
			if format == FormatOpenXPS && attr.Name.Space != "" && scope.ignorable[attr.Name.Space] {
				continue
			}
			known := node.Name.Space == namespace && node.Name.Local == "Discard" && (attr.Name.Local == "Target" || attr.Name.Local == "SentinelPage") || node.Name.Space == mcNamespace && node.Name.Local == "Choice" && attr.Name.Local == "Requires"
			if attr.Name.Space != "" || !known {
				return fmt.Errorf("%w: preserved discard attribute {%s}%s", ErrUnsupported, attr.Name.Space, attr.Name.Local)
			}
		}
		if node.Name == (xml.Name{Space: namespace, Local: "Discard"}) {
			for _, attribute := range []string{"Target", "SentinelPage"} {
				if value, present := node.attribute(attribute); present {
					if target, err := resolvePart("/", structureURI(value)); err == nil {
						reserved[strings.ToLower(target)] = true
					}
				}
			}
		}
		for _, child := range node.Children {
			if err := visit(child, scope); err != nil {
				return err
			}
		}
		return nil
	}
	return visit(root, compatibilityScope{})
}

// resourceModelMedia 识别OpenXPS定义的X3D媒体类型，不按文件后缀猜测模型或接受类型参数
// 入参: media 内容类型
// 返回: bool 是否为标准模型类型, error 标准类型的参数错误
func resourceModelMedia(media string) (bool, error) {
	if strings.EqualFold(media, "model/x3d+xml") || strings.EqualFold(media, "model/x3d+binary") {
		return true, nil
	}
	if len(media) < len("model/") || !strings.EqualFold(media[:len("model/")], "model/") {
		return false, nil
	}
	kind, parameters, err := mime.ParseMediaType(media)
	if err != nil {
		return false, fmt.Errorf("%w: model content type", ErrInvalid)
	}
	known := kind == "model/x3d+xml" || kind == "model/x3d+binary"
	if known && len(parameters) != 0 {
		return false, fmt.Errorf("%w: parameters on X3D content type", ErrInvalid)
	}
	return known, nil
}

// hasResourceModels 检查包内是否存在未解析的3D模型部件，调用方须持有阅读器读锁或独占快照
// 入参: budget 累计工作及取消预算
// 返回: bool 是否存在模型部件, error 内容类型、工作或取消错误
func (r *Reader) hasResourceModels(budget *resourceMergeBudget) (bool, error) {
	if err := budget.charge(len(r.pkg.parts)); err != nil {
		return false, err
	}
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := budget.charge(0); err != nil {
			return false, err
		}
		if key == strings.ToLower(opcTypesName) || opcRelationshipName(key) {
			continue
		}
		media, err := r.pkg.contentType(r.pkg.names[key])
		if err != nil {
			return false, err
		}
		model, err := resourceModelMedia(media)
		if err != nil {
			return false, &PartError{Part: r.pkg.names[key], Err: err}
		}
		if model {
			return true, nil
		}
	}
	return false, nil
}

// newResourceMarkupScopeTracker 创建用于词元遍历的MCE作用域跟踪器，支持合法可忽略及保留扩展校验
// 入参: format 包格式, models 是否识别3D模型画刷, ctx 取消Context
// 返回: *resourceMarkupScopeTracker 作用域跟踪器
func newResourceMarkupScopeTracker(format Format, models bool, ctx context.Context) *resourceMarkupScopeTracker {
	return newResourceMarkupScopeTrackerWithAlternate(format, models, false, ctx)
}

// newResourceMarkupScopeTrackerWithAlternate 创建可按标准MCE选择AlternateContent分支的词元级作用域跟踪器
// 入参: format 包格式, models 是否识别3D模型画刷, selectAlternate 是否执行标准MCE分支选择跳过未选子树, ctx 取消Context
// 返回: *resourceMarkupScopeTracker 作用域跟踪器
func newResourceMarkupScopeTrackerWithAlternate(format Format, models, selectAlternate bool, ctx context.Context) *resourceMarkupScopeTracker {
	namespace := formatNamespace(format)
	understood := map[string]bool{
		namespace:                             true,
		namespace + "/resourcedictionary-key": true,
		structureNamespace(format):            true,
		mcNamespace:                           true,
		xmlNamespace:                          true,
	}
	if models && format == FormatOpenXPS {
		understood[openXPS3DNamespace] = true
	}
	return &resourceMarkupScopeTracker{format: format, models: models, selectAlternate: selectAlternate, processor: compatibilityProcessor{understood: understood, context: ctx}}
}

// newResourceMarkupIgnoreTracker 创建仅跳过mc:Ignorable与mc:PreserveElements子树的词元级作用域跟踪器，保留全部AlternateContent分支供已校验主索引遍历与重写
// 入参: format 包格式, models 是否识别3D模型画刷, ctx 取消Context
// 返回: *resourceMarkupScopeTracker 作用域跟踪器
func newResourceMarkupIgnoreTracker(format Format, models bool, ctx context.Context) *resourceMarkupScopeTracker {
	tracker := newResourceMarkupScopeTrackerWithAlternate(format, models, false, ctx)
	tracker.ignoreOnly = true
	return tracker
}

// visit 跟踪词元进出栈的MCE作用域，放行合法可忽略扩展并校验保留元素内部MustUnderstand及属性规则
// 入参: token 当前XML词元, node 当前元素节点
// 返回: bool 是否应跳过消费标记语义扫描, compatibilityScope 当前元素生效作用域, error 兼容性或未支持语义错误
func (t *resourceMarkupScopeTracker) visit(token xml.Token, node *xmlElement) (bool, compatibilityScope, error) {
	if _, end := token.(xml.EndElement); end {
		if len(t.scopes) != 0 {
			curDepth := len(t.scopes)
			if t.ignoredDepth == curDepth {
				t.ignoredDepth = 0
			}
			if t.preservedDepth == curDepth {
				t.preservedDepth = 0
			}
			if t.selectAlternate && len(t.alternates) != 0 {
				top := &t.alternates[len(t.alternates)-1]
				if top.depth == curDepth {
					choices := top.choices
					t.alternates = t.alternates[:len(t.alternates)-1]
					t.scopes = t.scopes[:curDepth-1]
					if choices == 0 {
						return false, compatibilityScope{}, fmt.Errorf("%w: AlternateContent requires a Choice", ErrInvalid)
					}
					return true, compatibilityScope{}, nil
				}
				if top.contentDepths[len(top.contentDepths)-1] == curDepth {
					top.contentDepths = top.contentDepths[:len(top.contentDepths)-1]
				}
			}
			t.scopes = t.scopes[:curDepth-1]
		}
		return true, compatibilityScope{}, nil
	}
	if data, ok := token.(xml.CharData); ok {
		if t.selectAlternate && t.ignoredDepth == 0 && len(t.alternates) != 0 {
			top := &t.alternates[len(t.alternates)-1]
			if len(t.scopes) == top.contentDepths[len(top.contentDepths)-1] && len(compatibilityWords(string(data))) != 0 {
				return false, compatibilityScope{}, fmt.Errorf("%w: text directly inside AlternateContent", ErrInvalid)
			}
		}
		return true, compatibilityScope{}, nil
	}
	if _, start := token.(xml.StartElement); !start {
		return true, compatibilityScope{}, nil
	}
	inherited := compatibilityScope{}
	if len(t.scopes) != 0 {
		inherited = t.scopes[len(t.scopes)-1]
	}
	if t.ignoredDepth > 0 {
		scope := inherited
		if t.preservedDepth > 0 {
			isControl := node.Name.Space == mcNamespace
			isBranch := isControl && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
			var err error
			scope, err = t.processor.rulesChecked(node, inherited, !isBranch)
			if err != nil {
				return false, scope, err
			}
			if isControl && node.Name.Local != "AlternateContent" && !isBranch {
				return false, scope, fmt.Errorf("%w: unexpected MCE element %s", ErrInvalid, node.Name.Local)
			}
			if err := t.processor.validateAttributes(node, scope, isControl); err != nil {
				return false, scope, err
			}
		}
		t.scopes = append(t.scopes, scope)
		return true, scope, nil
	}
	if t.selectAlternate && len(t.alternates) != 0 {
		top := &t.alternates[len(t.alternates)-1]
		if len(t.scopes) == top.contentDepths[len(top.contentDepths)-1] {
			isBranch := node.Name.Space == mcNamespace && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
			scope, err := t.processor.rulesChecked(node, inherited, !isBranch)
			if err != nil {
				return false, scope, err
			}
			t.scopes = append(t.scopes, scope)
			if !t.processor.understood[node.Name.Space] {
				if !scope.ignorable[node.Name.Space] {
					return false, scope, fmt.Errorf("%w: AlternateContent child namespace %q", ErrUnsupported, node.Name.Space)
				}
				if scope.processes(node.Name) {
					if err := compatibilityNoXMLContext(node); err != nil {
						return false, scope, err
					}
					if err := t.processor.validateAttributes(node, scope, false); err != nil {
						return false, scope, err
					}
					top.contentDepths = append(top.contentDepths, len(t.scopes))
					return true, scope, nil
				}
				if scope.preservesElement(node.Name) {
					if err := t.processor.validateAttributes(node, scope, false); err != nil {
						return false, scope, err
					}
					t.preservedDepth = len(t.scopes)
				}
				t.ignoredDepth = len(t.scopes)
				return true, scope, nil
			}
			if !isBranch {
				return false, scope, fmt.Errorf("%w: unexpected AlternateContent child %s", ErrInvalid, node.Name.Local)
			}
			if err := t.processor.validateAttributes(node, scope, true); err != nil {
				return false, scope, err
			}
			selectable := true
			if node.Name.Local == "Choice" {
				if top.sawFallback {
					return false, scope, fmt.Errorf("%w: Choice follows Fallback", ErrInvalid)
				}
				top.choices++
				requires, ok := node.attributeNS("", "Requires")
				if !ok {
					return false, scope, fmt.Errorf("%w: Choice requires an unqualified Requires attribute", ErrInvalid)
				}
				uris, err := compatibilityPrefixes(node, requires)
				if err != nil {
					return false, scope, err
				}
				if len(uris) == 0 {
					return false, scope, fmt.Errorf("%w: empty Choice Requires", ErrInvalid)
				}
				for _, uri := range uris {
					if !t.processor.understood[uri] {
						selectable = false
					}
				}
			} else {
				if top.sawFallback || top.choices == 0 {
					return false, scope, fmt.Errorf("%w: Fallback must occur once after all Choices", ErrInvalid)
				}
				top.sawFallback = true
			}
			if !top.selected && selectable {
				if value, ok := node.attributeNS(mcNamespace, "MustUnderstand"); ok {
					if err := t.processor.checkMustUnderstand(node, value); err != nil {
						return false, scope, err
					}
				}
				top.selected = true
				return true, scope, nil
			}
			t.ignoredDepth = len(t.scopes)
			return true, scope, nil
		}
	}
	if t.selectAlternate && node.Name.Space == mcNamespace {
		if node.Name.Local != "AlternateContent" {
			return false, compatibilityScope{}, fmt.Errorf("%w: unexpected MCE element %s", ErrInvalid, node.Name.Local)
		}
		scope, err := t.processor.rulesChecked(node, inherited, true)
		if err != nil {
			return false, scope, err
		}
		if err := t.processor.validateAttributes(node, scope, true); err != nil {
			return false, scope, err
		}
		t.scopes = append(t.scopes, scope)
		t.alternates = append(t.alternates, resourceAlternateState{depth: len(t.scopes), contentDepths: []int{len(t.scopes)}})
		return true, scope, nil
	}
	isControl := node.Name.Space == mcNamespace
	isBranch := isControl && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
	scope, err := t.processor.rulesChecked(node, inherited, !isBranch)
	if err != nil {
		return false, scope, err
	}
	t.scopes = append(t.scopes, scope)
	if !t.processor.understood[node.Name.Space] {
		if !scope.ignorable[node.Name.Space] {
			return false, scope, fmt.Errorf("%w: preserved resource namespace %q", ErrUnsupported, node.Name.Space)
		}
		if scope.processes(node.Name) {
			if err := compatibilityNoXMLContext(node); err != nil {
				return false, scope, err
			}
			if err := t.processor.validateAttributes(node, scope, false); err != nil {
				return false, scope, err
			}
			return true, scope, nil
		}
		if scope.preservesElement(node.Name) {
			if err := t.processor.validateAttributes(node, scope, false); err != nil {
				return false, scope, err
			}
			t.preservedDepth = len(t.scopes)
		}
		t.ignoredDepth = len(t.scopes)
		return true, scope, nil
	}
	if t.ignoreOnly {
		return false, scope, nil
	}
	if err := validateResourceMarkupScope(node, t.format, t.models, scope); err != nil {
		return false, scope, err
	}
	return false, scope, nil
}

// validateResourceMarkupScope 在已知MCE作用域下校验原始布局标记，放行当前作用域合法可忽略扩展属性与元素
// 入参: node 原始元素, format 包格式, models 是否识别模型画刷的保留语义, scope 当前生效MCE作用域
// 返回: error 未理解标记、属性或XML作用域错误
func validateResourceMarkupScope(node *xmlElement, format Format, models bool, scope compatibilityScope) error {
	namespace := formatNamespace(format)
	if models && node.Name.Space == openXPS3DNamespace {
		return resourceModelBrushAttributes(node)
	}
	if node.Name.Space != namespace && node.Name.Space != structureNamespace(format) && node.Name.Space != mcNamespace {
		if scope.ignorable[node.Name.Space] {
			return nil
		}
		return fmt.Errorf("%w: preserved resource namespace %q", ErrUnsupported, node.Name.Space)
	}
	if node.Name.Space == namespace && !fontUsageElement(node.Name.Local) {
		return fmt.Errorf("%w: preserved resource element %s", ErrUnsupported, node.Name.Local)
	}
	if node.Name.Space == structureNamespace(format) && !resourceStructureElement(node.Name.Local) {
		return fmt.Errorf("%w: preserved structure element %s", ErrUnsupported, node.Name.Local)
	}
	isControl := node.Name.Space == mcNamespace
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) || attr.Name.Space == mcNamespace {
			continue
		}
		if attr.Name.Space != "" && scope.ignorable[attr.Name.Space] {
			continue
		}
		if isControl {
			if attr.Name.Space == "" && node.Name.Local == "Choice" && attr.Name.Local == "Requires" {
				continue
			}
			if attr.Name.Space == "" || attr.Name.Space == xmlNamespace || attr.Name.Space == namespace || attr.Name.Space == structureNamespace(format) || attr.Name.Space == namespace+"/resourcedictionary-key" {
				return fmt.Errorf("%w: attribute {%s}%s on MCE %s", ErrInvalid, attr.Name.Space, attr.Name.Local, node.Name.Local)
			}
			return fmt.Errorf("%w: preserved resource attribute {%s}%s", ErrUnsupported, attr.Name.Space, attr.Name.Local)
		}
		if attr.Name.Space != "" && attr.Name.Space != xmlNamespace && attr.Name.Space != namespace+"/resourcedictionary-key" {
			return fmt.Errorf("%w: preserved resource attribute {%s}%s", ErrUnsupported, attr.Name.Space, attr.Name.Local)
		}
		if attr.Name.Space == xmlNamespace && attr.Name.Local != "lang" {
			return fmt.Errorf("%w: resource XML context %s", ErrUnsupported, attr.Name.Local)
		}
	}
	if node.Name.Space == mcNamespace && node.Name.Local == "Choice" {
		requires, _ := node.attribute("Requires")
		for _, prefix := range compatibilityWords(requires) {
			uri := node.Namespaces[prefix]
			if uri != namespace && uri != structureNamespace(format) && uri != namespace+"/resourcedictionary-key" && uri != xmlNamespace && uri != mcNamespace && !(models && format == FormatOpenXPS && uri == openXPS3DNamespace) {
				return fmt.Errorf("%w: preserved resource requirement %q", ErrUnsupported, uri)
			}
		}
	}
	if node.Name.Space == namespace && slices.Contains([]string{"Canvas", "Path", "Glyphs"}, node.Name.Local) {
		value := *node
		value.Children = nil
		value.Attr = slices.DeleteFunc(slices.Clone(node.Attr), func(a xml.Attr) bool {
			return a.Name.Space == mcNamespace || a.Name.Space != "" && scope.ignorable[a.Name.Space]
		})
		if _, err := visualAttributes(&value, format); err != nil {
			return err
		}
	}
	return nil
}

// resourceStructureElement 判断已理解的文档结构元素，不忽略同一命名空间中的未知扩展
// 入参: name 元素本地名称
// 返回: bool 是否理解元素的资源引用语义
func resourceStructureElement(name string) bool {
	switch name {
	case "DocumentStructure", "DocumentStructure.Outline", "DocumentOutline", "OutlineEntry", "Story", "StoryFragmentReference", "StoryFragments", "StoryFragment", "StoryBreak", "SectionStructure", "ParagraphStructure", "TableStructure", "TableRowGroupStructure", "TableRowStructure", "TableCellStructure", "ListStructure", "ListItemStructure", "FigureStructure", "NamedElement":
		return true
	}
	return false
}

// resourceRelationshipTargets 重定向关系中的资源别名，未修改时保留原字节，修改时移除忽略内容
// 入参: source 关系来源, data 原关系标记, aliases 资源别名, limits 资源上限, budget 累计工作预算
// 返回: []byte 关系标记, bool 是否修改, error 标记、预算或取消错误
func resourceRelationshipTargets(source string, data []byte, aliases map[string]string, limits Limits, budget *resourceMergeBudget) ([]byte, bool, error) {
	if err := budget.charge(1); err != nil {
		return nil, false, err
	}
	relations, err := parseRelationshipMarkup(source, data, limits, budget.context)
	if err != nil {
		return nil, false, err
	}
	changed := false
	for index := range relations {
		if err := budget.charge(1); err != nil {
			return nil, false, err
		}
		relation := &relations[index]
		if relation.TargetMode != TargetModeInternal {
			continue
		}
		part, err := resolvePart(source, relation.Target)
		if err != nil {
			return nil, false, err
		}
		if target, exists := aliases[strings.ToLower(part)]; exists && !strings.EqualFold(part, target) {
			relation.Target, err = opcPartName(target)
			if err != nil {
				return nil, false, err
			}
			changed = true
		}
	}
	var uncovered error
	if _, err := decodeXMLVisit(data, limits, func(token xml.Token, node *xmlElement) error {
		if _, start := token.(xml.StartElement); !start {
			return budget.charge(1)
		}
		if err := budget.charge(len(node.Attr) + 1); err != nil {
			return err
		}
		if err := resourceRelationshipNode(node); err != nil && uncovered == nil {
			uncovered = err
		}
		if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
			return nil
		}
		if mode, _ := node.attribute("TargetMode"); TargetMode(mode) == TargetModeExternal {
			return nil
		}
		value, _ := node.attribute("Target")
		part, err := resolvePart(source, value)
		if err == nil {
			if target, exists := aliases[strings.ToLower(part)]; exists && !strings.EqualFold(part, target) {
				changed = true
			}
		}
		return nil
	}); err != nil {
		return nil, false, err
	}
	if !changed {
		if uncovered != nil {
			return nil, false, uncovered
		}
		return data, false, checkContext(budget.context)
	}
	type requiredRelationKey struct {
		kind   string
		target string
		mode   TargetMode
	}
	seenRequired := make(map[requiredRelationKey]bool)
	deduped := relations[:0]
	for _, relation := range relations {
		if relation.Type == xpsNamespace+"/required-resource" || relation.Type == openXPSNamespace+"/required-resource" {
			target := strings.ToLower(relation.Target)
			if relation.TargetMode == TargetModeInternal {
				if resolved, resolveErr := resolvePart(source, relation.Target); resolveErr == nil {
					target = strings.ToLower(resolved)
				}
			}
			key := requiredRelationKey{kind: relation.Type, target: target, mode: relation.TargetMode}
			if seenRequired[key] {
				continue
			}
			seenRequired[key] = true
		}
		deduped = append(deduped, relation)
	}
	relations = deduped
	output, err := createdRelationshipMarkup(relations, limits, budget.context)
	if err != nil {
		return nil, false, err
	}
	maximum := min(limits.MaxMetadataBytes, limits.MaxPartBytes, limits.MaxPackageBytes)
	output, err = restoreXMLEncoding(data, output, maximum, budget.context)
	if err != nil {
		return nil, false, err
	}
	return output, true, checkContext(budget.context)
}

// resourceSignatureReferences 读取包签名清单中的部件引用，遇到未知自定义对象或证书检索语义时返回错误
// 入参: data 原签名XML, limits 包上限, budget 遍历及取消预算
// 返回: []string 签名清单中的部件名, error 声明、语义、预算或取消错误
func resourceSignatureReferences(data []byte, limits Limits, budget *resourceMergeBudget) ([]string, error) {
	if _, err := decodeXMLVisit(data, limits, func(token xml.Token, node *xmlElement) error {
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := budget.charge(1); err != nil {
			return err
		}
		if node.Name.Space != xmlSignatureNamespace && node.Name.Space != opcSignatureNamespace {
			return fmt.Errorf("%w: preserved signature resource namespace %q", ErrUnsupported, node.Name.Space)
		}
		if node.Name == (xml.Name{Space: xmlSignatureNamespace, Local: "Object"}) {
			id, _ := node.attribute("Id")
			if strings.Trim(id, " \t\r\n") != "idPackageObject" {
				return fmt.Errorf("%w: resource use in custom signature object", ErrUnsupported)
			}
		}
		if node.Name == (xml.Name{Space: xmlSignatureNamespace, Local: "RetrievalMethod"}) {
			return fmt.Errorf("%w: resource use in signature retrieval method", ErrUnsupported)
		}
		for _, a := range node.Attr {
			if a.Name.Space != "" && a.Name.Space != xmlnsNamespace && a.Name.Space != xmlNamespace {
				return fmt.Errorf("%w: preserved signature resource attribute", ErrUnsupported)
			}
			if a.Name.Space == xmlNamespace && a.Name.Local != "id" && a.Name.Local != "lang" {
				return fmt.Errorf("%w: signature resource XML context", ErrUnsupported)
			}
		}
		return nil
	}); err != nil {
		return nil, err
	}
	info, err := readSignatureXML(data, limits, budget.context)
	if err != nil {
		return nil, err
	}
	result := make([]string, 0, len(info.Parts))
	for _, reference := range info.Parts {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		result = append(result, reference.Part)
	}
	return result, nil
}

// resourceOptimizationBudget 校验资源优化选项并构造累计扫描与遍历预算
// 入参: ctx 取消Context, options 优化选项，nil采用包上限, label 错误标识
// 返回: resourceMergeBudget 独立优化预算, error 上限参数错误
func (p *Package) resourceOptimizationBudget(ctx context.Context, options *OptimizationOptions, label string) (resourceMergeBudget, error) {
	configuration := OptimizationOptions{MaxBytes: p.limits.MaxPackageBytes, MaxWork: p.limits.MaxXMLNodes}
	if options != nil {
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxWork != 0 {
			configuration.MaxWork = options.MaxWork
		}
	}
	if configuration.MaxBytes < 1 || configuration.MaxWork < 1 {
		return resourceMergeBudget{}, fmt.Errorf("%w: %s", ErrInvalid, label)
	}
	return resourceMergeBudget{bytes: configuration.MaxBytes, work: configuration.MaxWork, seen: make(map[string]bool), context: ctx}, nil
}

// DeduplicateResources 合并内容等价的标准字体、图像、ICC及远程字典并原子更新引用，失败不修改包
// 混淆字体按解混淆内容比较，保留导航、释放提示、附属关系及含X3D模型包的原身份，不自动重签
// 入参: ctx 取消Context，nil采用Background, options 扫描及工作参数，nil采用默认值
// 返回: []ResourceMerge 按原部件名排列的合并记录，失败为nil, error 结构、许可、资源或取消错误
func (p *Package) DeduplicateResources(ctx context.Context, options *OptimizationOptions) ([]ResourceMerge, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	budget, err := p.resourceOptimizationBudget(ctx, options, "resource merge limits")
	if err != nil {
		return nil, err
	}
	r, err := p.reader(ctx)
	if err != nil {
		return nil, err
	}
	defer r.Close()
	models, err := r.hasResourceModels(&budget)
	if err != nil {
		return nil, err
	}
	if models {
		if _, err := r.resourceReferenceGraph(&budget); err != nil {
			return nil, err
		}
		return nil, checkContext(ctx)
	}
	if _, err := r.FontUsage(ctx, nil); err != nil {
		return nil, err
	}
	reserved, err := r.resourceIdentityReferences(&budget)
	if err != nil {
		return nil, err
	}
	aliases, result, err := p.resourceAliases(r, &budget, reserved)
	if err != nil {
		return nil, err
	}
	if len(aliases) == 0 {
		return result, checkContext(ctx)
	}
	q := p.signingCopy()
	q.layout = maps.Clone(p.layout)
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		if aliases[key] != "" {
			continue
		}
		name := r.pkg.names[key]
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := r.pkg.contentType(name)
		if err != nil {
			return nil, err
		}
		markup := false
		if !opcRelationshipName(name) {
			markup, err = fontUsageMarkup(media)
			if err != nil {
				return nil, &PartError{Part: name, Err: err}
			}
		}
		if !markup && !opcRelationshipName(name) {
			continue
		}
		data, err := budget.readPart(r.pkg, key)
		if err != nil {
			return nil, err
		}
		var updated []byte
		var changed bool
		if opcRelationshipName(name) {
			updated, changed, err = resourceRelationshipTargets(relationshipSource(name), data, aliases, p.limits, &budget)
		} else {
			rewriteTracker := newResourceMarkupScopeTracker(p.format, p.format == FormatOpenXPS, ctx)
			updated, changed, err = rewriteXMLAttributes(data, p.limits, ctx, nil, func(token xml.Token, node *xmlElement) (bool, error) {
				skip, _, err := rewriteTracker.visit(token, node)
				return skip, err
			}, func(node *xmlElement, attribute xml.Attr) (string, bool, error) {
				if err := budget.charge(1); err != nil {
					return "", false, err
				}
				return rewriteResourceAttribute(name, node, attribute, aliases)
			})
		}
		if err != nil {
			return nil, &PartError{Part: name, Err: err}
		}
		if !changed {
			continue
		}
		if opcRelationshipName(name) {
			if err := q.setRelationshipMarkup(relationshipSource(name), updated, ctx); err != nil {
				return nil, err
			}
		} else {
			if err := q.editable(name); err != nil {
				return nil, err
			}
			wasDirty := q.dirty[key]
			if err := q.store(name, media, updated); err != nil {
				return nil, err
			}
			q.dirty[key] = wasDirty
		}
	}
	for _, merge := range result {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		if err := q.editable(merge.Part); err != nil {
			return nil, err
		}
		q.removePart(merge.Part)
	}
	verified, err := q.reader(ctx)
	if err != nil {
		return nil, err
	}
	verified.Close()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.layout = q.names, q.parents, q.allocated, q.layout
	p.dirty, p.dirtyRels = q.dirty, q.dirtyRels
	return result, nil
}

// resourceAliases 选择无附属关系的相同资源，按部件名确定稳定目标，不把摘要相等当作字节相等
// 入参: r 已校验当前快照, budget 累计预算, reserved 需要保持原身份的资源
// 返回: map[string]string 合并别名, []ResourceMerge 记录, error 数据、许可或预算错误
func (p *Package) resourceAliases(r *Reader, budget *resourceMergeBudget, reserved map[string]bool) (map[string]string, []ResourceMerge, error) {
	aliases := make(map[string]string)
	var candidates []resourceMergeCandidate
	var result []ResourceMerge
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		if err := budget.charge(1); err != nil {
			return nil, nil, err
		}
		part := p.parts[key]
		kind := standardResourceMedia(part.media)
		if kind == 0 || reserved[key] {
			continue
		}
		if _, attached := r.pkg.parts[strings.ToLower(createdRelationshipPart(part.name))]; attached {
			continue
		}
		if err := budget.part(key, len(part.data)); err != nil {
			return nil, nil, err
		}
		data := part.data
		blocks := 1 + max(0, len(data)-1)/4096
		if err := budget.charge(blocks); err != nil {
			return nil, nil, err
		}
		if kind == requiredFont {
			face, err := r.pkg.readFontFaceLimit(part.name, 0, int64(len(data)))
			if err != nil {
				return nil, nil, err
			}
			data = face.data
		}
		candidates = append(candidates, resourceMergeCandidate{part: part, data: data, kind: kind})
	}
	slices.SortFunc(candidates, func(a, b resourceMergeCandidate) int {
		ap, bp := p.protected[strings.ToLower(a.part.name)], p.protected[strings.ToLower(b.part.name)]
		if ap != bp {
			if ap {
				return -1
			}
			return 1
		}
		return strings.Compare(strings.ToLower(a.part.name), strings.ToLower(b.part.name))
	})
	for {
		groups := make(map[resourceMergeKey][]resourceMergeCandidate)
		count := len(aliases)
		for _, candidate := range candidates {
			if err := budget.charge(1); err != nil {
				return nil, nil, err
			}
			part := candidate.part
			key := strings.ToLower(part.name)
			if _, removed := aliases[key]; removed {
				continue
			}
			data, scope := candidate.data, ""
			if candidate.kind == requiredDictionary {
				var err error
				data, scope, err = resourceDictionaryIdentity(part, p.format, p.limits, budget, aliases)
				if err != nil {
					return nil, nil, &PartError{Part: part.name, Err: fmt.Errorf("dictionary comparison: %w", err)}
				}
			}
			blocks := 1 + max(0, len(data)-1)/4096
			if err := budget.charge(blocks); err != nil {
				return nil, nil, err
			}
			identity := resourceMergeKey{media: strings.ToLower(part.media), scope: scope, length: len(data), digest: sha256.Sum256(data)}
			found := false
			for _, previous := range groups[identity] {
				if err := budget.charge(blocks); err != nil {
					return nil, nil, err
				}
				if !bytes.Equal(data, previous.data) {
					continue
				}
				if p.protected[key] {
					found = true
					break
				}
				aliases[key] = previous.part.name
				result = append(result, ResourceMerge{Part: part.name, Target: previous.part.name, Bytes: int64(len(part.data))})
				found = true
				break
			}
			if !found {
				candidate.data = data
				groups[identity] = append(groups[identity], candidate)
			}
		}
		if len(aliases) == count {
			break
		}
		candidates = slices.DeleteFunc(candidates, func(candidate resourceMergeCandidate) bool { return candidate.kind != requiredDictionary })
	}
	for index := range result {
		target := result[index].Target
		for {
			alias, present := aliases[strings.ToLower(target)]
			if !present {
				break
			}
			if err := budget.charge(1); err != nil {
				return nil, nil, err
			}
			target = alias
		}
		result[index].Target = target
		aliases[strings.ToLower(result[index].Part)] = target
	}
	slices.SortFunc(result, func(a, b ResourceMerge) int { return strings.Compare(a.Part, b.Part) })
	return aliases, result, nil
}

// resourceRelationshipNode 检查原始关系分支的语义覆盖，不推测未知元素或属性中的资源身份
// 入参: node 未过滤的原始节点
// 返回: error 未理解的保留标记错误
func resourceRelationshipNode(node *xmlElement) error {
	switch node.Name.Space {
	case opcRelsNS:
		if node.Name.Local != "Relationships" && node.Name.Local != "Relationship" {
			return fmt.Errorf("%w: preserved relationship element %s", ErrUnsupported, node.Name.Local)
		}
	case mcNamespace:
		if node.Name.Local != "AlternateContent" && node.Name.Local != "Choice" && node.Name.Local != "Fallback" {
			return fmt.Errorf("%w: preserved relationship compatibility element %s", ErrUnsupported, node.Name.Local)
		}
		if node.Name.Local == "Choice" {
			requires, _ := node.attribute("Requires")
			if _, err := compatibilityPrefixes(node, requires); err != nil {
				return err
			}
		}
	default:
		return fmt.Errorf("%w: preserved relationship namespace %q", ErrUnsupported, node.Name.Space)
	}
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) || attribute.Name.Space == mcNamespace {
			continue
		}
		allowed := attribute.Name.Space == "" && node.Name.Space == opcRelsNS && node.Name.Local == "Relationship" && slices.Contains([]string{"Id", "Type", "Target", "TargetMode"}, attribute.Name.Local)
		allowed = allowed || attribute.Name == (xml.Name{Local: "Requires"}) && node.Name.Space == mcNamespace && node.Name.Local == "Choice"
		if !allowed {
			return fmt.Errorf("%w: preserved relationship attribute {%s}%s", ErrUnsupported, attribute.Name.Space, attribute.Name.Local)
		}
	}
	return nil
}

// charge 在计费前检查取消和剩余工作预算
// 入参: count 工作单元数
// 返回: error 预算或取消错误
func (b *resourceMergeBudget) charge(count int) error {
	if err := checkContext(b.context); err != nil {
		return err
	}
	if count > b.work {
		return fmt.Errorf("%w: resource merge work budget", ErrLimit)
	}
	b.work -= count
	return nil
}

// part 在首次扫描部件前检查累计字节，之后只计算访问工作
// 入参: key 规范化部件键, size 部件字节数
// 返回: error 扫描预算或取消错误
func (b *resourceMergeBudget) part(key string, size int) error {
	if err := b.charge(1); err != nil {
		return err
	}
	if b.seen[key] {
		return nil
	}
	if int64(size) > b.bytes {
		return fmt.Errorf("%w: resource merge scan byte budget", ErrLimit)
	}
	b.bytes -= int64(size)
	b.seen[key] = true
	return nil
}

// readPart 在读取前应用剩余扫描限额，当前包快照的不可变数据直接用于内部校验及改写
// 入参: pkg 当前只读快照, key 部件键
// 返回: []byte 不可修改的数据视图, error 读取、预算或取消错误
func (b *resourceMergeBudget) readPart(pkg *packageReader, key string) ([]byte, error) {
	limit := pkg.limits.MaxPartBytes
	media, _ := pkg.contentType(pkg.names[key])
	if opcMetadataPart(pkg.names[key], media) {
		limit = min(limit, pkg.limits.MaxMetadataBytes)
	}
	if !b.seen[key] {
		limit = min(limit, b.bytes)
	}
	data, owned := pkg.data[key]
	if owned {
		if int64(len(data)) > limit {
			return nil, fmt.Errorf("%w: resource merge markup byte budget", ErrLimit)
		}
	} else {
		var err error
		data, err = pkg.readItems(key, limit)
		if err != nil {
			return nil, err
		}
	}
	if err := b.part(key, len(data)); err != nil {
		return nil, err
	}
	return data, nil
}

// PruneResources 清理从保留根不可达的标准字体、图像、ICC与远程字典，失败不修改包
// 保留全部非资源部件、兼容分支、导航、释放提示、签名清单及含X3D模型包的潜在依赖，不自动重签
// 入参: ctx 取消Context，nil采用Background, options 累计扫描及遍历参数，nil采用包上限
// 返回: []ResourceRemoval 按部件名排列的清理记录，失败为nil, error 标记、引用、许可或资源错误
func (p *Package) PruneResources(ctx context.Context, options *OptimizationOptions) ([]ResourceRemoval, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	budget, err := p.resourceOptimizationBudget(ctx, options, "resource pruning limits")
	if err != nil {
		return nil, err
	}
	r, err := p.reader(ctx)
	if err != nil {
		return nil, err
	}
	defer r.Close()
	reachable, err := r.resourceReachability(&budget)
	if err != nil {
		return nil, err
	}
	var result []ResourceRemoval
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		if reachable[key] {
			continue
		}
		part := p.parts[key]
		if standardResourceMedia(part.media) == 0 {
			continue
		}
		if err := p.editable(part.name); err != nil {
			return nil, err
		}
		if err := budget.part(key, len(part.data)); err != nil {
			return nil, err
		}
		size := int64(len(part.data))
		if name := strings.ToLower(createdRelationshipPart(part.name)); r.pkg.data[name] != nil {
			if _, err := budget.readPart(r.pkg, name); err != nil {
				return nil, err
			}
			size += int64(len(r.pkg.data[name]))
		}
		result = append(result, ResourceRemoval{Part: part.name, Bytes: size})
	}
	if len(result) == 0 {
		return nil, checkContext(ctx)
	}
	q := p.signingCopy()
	q.layout = maps.Clone(p.layout)
	for _, removal := range result {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		q.removePart(removal.Part)
	}
	verified, err := q.reader(ctx)
	if err != nil {
		return nil, err
	}
	verified.Close()
	slices.SortFunc(result, func(a, b ResourceRemoval) int { return strings.Compare(a.Part, b.Part) })
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.layout = q.names, q.parents, q.allocated, q.layout
	p.dirty, p.dirtyRels = q.dirty, q.dirtyRels
	return result, nil
}
