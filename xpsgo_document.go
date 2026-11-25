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
	"net/url"
	"slices"
	"strconv"
	"strings"
	"unicode"
)

const (
	// FragmentUnknown 表示未知的故事片段类型
	FragmentUnknown FragmentType = iota
	// FragmentContent 表示页面正文故事片段
	FragmentContent
	// FragmentHeader 表示页眉故事片段
	FragmentHeader
	// FragmentFooter 表示页脚故事片段
	FragmentFooter
)

const (
	// StructureUnknown 表示未知语义结构节点类型
	StructureUnknown StructureKind = iota
	// StructureSection 表示章节结构节点
	StructureSection
	// StructureParagraph 表示段落结构节点
	StructureParagraph
	// StructureTable 表示表格结构节点
	StructureTable
	// StructureRowGroup 表示表格行组结构节点
	StructureRowGroup
	// StructureRow 表示表格行结构节点
	StructureRow
	// StructureCell 表示表格单元格结构节点
	StructureCell
	// StructureList 表示列表结构节点
	StructureList
	// StructureListItem 表示列表项结构节点
	StructureListItem
	// StructureFigure 表示图形或插图结构节点
	StructureFigure
	// StructureNamedElement 表示命名元素引用结构节点
	StructureNamedElement
)

// nameStartRanges 保存固定布局和文档结构名称共用的首字符Unicode类别表
var nameStartRanges = []*unicode.RangeTable{unicode.Lu, unicode.Ll, unicode.Lt, unicode.Lo, unicode.Nl}

// structureNameContinueRanges 保存文档结构名称允许的后续Unicode类别表
var structureNameContinueRanges = []*unicode.RangeTable{unicode.Mn, unicode.Mc, unicode.Nd, unicode.Lm}

// fixedNameContinueRanges 保存固定布局名称允许的后续Unicode类别表
var fixedNameContinueRanges = []*unicode.RangeTable{unicode.Mn, unicode.Mc, unicode.Nd}

// Document 保存固定文档及其页面索引
type Document struct {
	Part  string
	Pages []PageReference
}

// PageReference 保存页面部件、建议尺寸及链接目标
type PageReference struct {
	Part        string
	Width       float64
	Height      float64
	LinkTargets []string
}

// Page 保存固定页面的方言、尺寸、区域及内容，Has字段保留区域属性的显式声明状态
// Width、Height、ContentBox与BleedBox均采用XPS标准的1/96英寸设备无关单位
type Page struct {
	Format        Format
	Part          string
	Width         float64
	Height        float64
	Language      string
	Name          string
	ContentBox    Rect
	BleedBox      Rect
	HasContentBox bool
	HasBleedBox   bool
	Diagnostics   []Diagnostic
	Elements      []Element
	root          *xmlElement
	resources     *resourceGraph
	visuals       map[*xmlElement]Element
}

// Diagnostic 记录文档或打印校验的非致命诊断信息，按场景可选填充部件、元素、属性及说明
type Diagnostic struct {
	Part      string
	Element   string
	Attribute string
	Message   string
}

// DocumentStructure 保存固定文档关联的目录与故事定义，不推断页面布局的阅读顺序
type DocumentStructure struct {
	Part    string
	Outline *DocumentOutline
	Stories []Story
}

// DocumentOutline 保存目录语言及声明顺序的条目，层级不限制为逐级递增
type DocumentOutline struct {
	Language string
	Entries  []OutlineEntry
}

// OutlineEntry 保存目录层级、目标及描述，Language为nil时继承目录语言
type OutlineEntry struct {
	Level       int32
	Target      string
	Description string
	Language    *string
}

// Story 保存同一固定文档内的故事名称及作者指定的片段顺序
type Story struct {
	Name      string
	Fragments []StoryFragmentReference
}

// StoryFragmentReference 以一基的文档内页码定位片段，FragmentName保留省略与空值的区别
type StoryFragmentReference struct {
	PageNumber   int
	FragmentName *string
}

// FragmentType 表示故事片段的正文、页眉或页脚类型
type FragmentType uint8

// StructureKind 表示内容结构中的语义节点类型
type StructureKind uint8

// StoryFragments 保存单个固定页面关联的片段，顺序保持作者声明顺序
type StoryFragments struct {
	Part      string
	Fragments []StoryFragment
}

// StoryFragment 保存故事关联、片段标识、前后断点及内容结构，名称指针保留省略语义
type StoryFragment struct {
	StoryName    *string
	FragmentName *string
	Type         FragmentType
	BreakBefore  bool
	BreakAfter   bool
	Content      []ContentStructure
}

// ContentStructure 保存有序的语义结构，跨片段表格续接所需的空单元格不被丢弃
// Marker用于列表项目，RowSpan和ColumnSpan用于单元格，NameReference用于命名元素
type ContentStructure struct {
	Kind          StructureKind
	NameReference string
	Marker        *string
	RowSpan       int32
	ColumnSpan    int32
	Children      []ContentStructure
}

// LinkTarget 保存解析后的链接目标，不执行外部访问
// Page为主阅读索引的零基页号，未列入主索引时为-1；页面定位以Part为准，Element为nil时定位页首
// Name保存已声明的命名地址，Transform将目标元素局部坐标映射到页面坐标
type LinkTarget struct {
	URI       string
	Part      string
	Page      int
	Name      string
	Element   Element
	Transform Matrix
	External  bool
}

// String 返回故事片段类型的可读名称
// 返回: string 片段类型名称
func (t FragmentType) String() string {
	switch t {
	case FragmentContent:
		return "content"
	case FragmentHeader:
		return "header"
	case FragmentFooter:
		return "footer"
	default:
		return "unknown"
	}
}

// String 返回语义结构节点类型的可读名称
// 返回: string 节点类型名称
func (k StructureKind) String() string {
	switch k {
	case StructureSection:
		return "section"
	case StructureParagraph:
		return "paragraph"
	case StructureTable:
		return "table"
	case StructureRowGroup:
		return "rowgroup"
	case StructureRow:
		return "row"
	case StructureCell:
		return "cell"
	case StructureList:
		return "list"
	case StructureListItem:
		return "listitem"
	case StructureFigure:
		return "figure"
	case StructureNamedElement:
		return "namedelement"
	default:
		return "unknown"
	}
}

// readSequence 读取包级关系、文档序列及页面索引
// 返回: error 错误信息
func (r *Reader) readSequence() error {
	return r.readSequenceContext(nil)
}

// readSequenceContext 在取消检查下读取包级关系、文档序列及页面索引
// 入参: ctx 取消Context
// 返回: error 错误信息
func (r *Reader) readSequenceContext(ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	parts, err := r.readDocumentPartsContext(ctx)
	if err != nil {
		return err
	}
	seenPages := make(map[string]bool)
	for _, part := range parts {
		if err := checkContext(ctx); err != nil {
			return err
		}
		doc, err := r.readDocumentContext(ctx, part, seenPages)
		if err != nil {
			return err
		}
		r.documents = append(r.documents, doc)
	}
	return checkContext(ctx)
}

// readDocumentPartsContext 在取消检查下校验固定表示关联及文档序列，按声明顺序返回唯一文档URI
// 入参: ctx 取消Context
// 返回: []string 文档部件URI, error 关联、序列、引用、取消或读取错误
func (r *Reader) readDocumentPartsContext(ctx context.Context) ([]string, error) {
	if err := r.readFixedRepresentationContext(ctx); err != nil {
		return nil, err
	}
	return r.readDocumentReferencesContext(ctx)
}

// readFixedRepresentation 校验包根中的唯一内部固定表示关联，不要求序列部件已经到达
// 返回: error 关联、URI或读取错误
func (r *Reader) readFixedRepresentation() error {
	return r.readFixedRepresentationContext(nil)
}

// readFixedRepresentationContext 在取消检查下校验包根中的唯一内部固定表示关联，不要求序列部件已经到达
// 入参: ctx 取消Context
// 返回: error 关联、URI、取消或读取错误
func (r *Reader) readFixedRepresentationContext(ctx context.Context) error {
	rels, err := r.pkg.relationshipsContext(ctx, "/")
	if err != nil {
		return err
	}
	sequence := ""
	var selected Format
	for _, rel := range rels {
		var format Format
		switch rel.Type {
		case xpsNamespace + "/fixedrepresentation":
			format = FormatXPS
		case openXPSNamespace + "/fixedrepresentation":
			format = FormatOpenXPS
		default:
			continue
		}
		if sequence != "" {
			return fmt.Errorf("%w: multiple fixed representations", ErrInvalid)
		}
		if rel.TargetMode == TargetModeExternal {
			return fmt.Errorf("%w: external fixed representation", ErrInvalid)
		}
		sequence, err = resolvePart("/", rel.Target)
		if err != nil {
			return err
		}
		selected = format
	}
	if sequence == "" {
		return fmt.Errorf("%w: missing fixed representation relationship", ErrInvalid)
	}
	r.sequence, r.format = sequence, selected
	return nil
}

// readDocumentReferences 按已确认的固定表示读取完整文档序列，不重新解析包根关联
// 返回: []string 唯一文档URI, error 序列、引用或读取错误
func (r *Reader) readDocumentReferences() ([]string, error) {
	return r.readDocumentReferencesContext(nil)
}

// readDocumentReferencesContext 在取消检查下按已确认的固定表示读取完整文档序列
// 入参: ctx 取消Context
// 返回: []string 唯一文档URI, error 序列、引用、取消或读取错误
func (r *Reader) readDocumentReferencesContext(ctx context.Context) ([]string, error) {
	root, err := r.readFixedPartLoader(r.sequence, "fixeddocumentsequence", "FixedDocumentSequence", nil, ctx)
	if err != nil {
		return nil, err
	}
	var parts []string
	seenDocuments := make(map[string]bool)
	for _, child := range root.Children {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		part, err := r.readDocumentReference(r.sequence, child)
		if err != nil {
			return nil, err
		}
		key := strings.ToLower(part)
		if seenDocuments[key] {
			return nil, &PartError{Part: r.sequence, Element: child.Name.Local, Err: fmt.Errorf("%w: duplicate document reference %s", ErrInvalid, part)}
		}
		seenDocuments[key] = true
		parts = append(parts, part)
	}
	return parts, nil
}

// readDocumentReference 解析已完成结构校验的文档引用内部部件URI
// 入参: source 来源序列URI, node 已完成结构校验的文档引用
// 返回: string 文档URI, error URI错误
func (r *Reader) readDocumentReference(source string, node *xmlElement) (string, error) {
	return referencePart(source, node)
}

// readDocument 读取单个固定文档并收集页面索引
// 入参: part 文档部件, seenPages 已引用页面
// 返回: Document 文档索引, error 错误信息
func (r *Reader) readDocument(part string, seenPages map[string]bool) (Document, error) {
	return r.readDocumentContext(nil, part, seenPages)
}

// readDocumentContext 在取消检查下读取单个固定文档并收集页面索引
// 入参: ctx 取消Context, part 文档部件, seenPages 已引用页面
// 返回: Document 文档索引, error 错误信息
func (r *Reader) readDocumentContext(ctx context.Context, part string, seenPages map[string]bool) (Document, error) {
	root, err := r.readFixedPartLoader(part, "fixeddocument", "FixedDocument", nil, ctx)
	if err != nil {
		return Document{}, err
	}
	doc := Document{Part: part}
	for _, child := range root.Children {
		if err := checkContext(ctx); err != nil {
			return Document{}, err
		}
		page, err := r.readPageReference(part, child)
		if err != nil {
			return doc, err
		}
		if err := r.appendDocumentPage(&doc, page, seenPages); err != nil {
			return doc, err
		}
	}
	return doc, nil
}

// appendDocumentPage 将已校验引用加入文档及全局索引，限制总页数并排除跨文档重复页面
// 入参: document 所属文档, page 页面引用, seenPages 已引用页面
// 返回: error 页数预算或引用重复错误
func (r *Reader) appendDocumentPage(document *Document, page PageReference, seenPages map[string]bool) error {
	if len(r.pages) >= r.limits.MaxPageCount {
		return fmt.Errorf("%w: page count", ErrLimit)
	}
	key := strings.ToLower(page.Part)
	if seenPages[key] {
		return &PartError{Part: document.Part, Element: "PageContent", Err: fmt.Errorf("%w: duplicate page reference %s", ErrInvalid, page.Part)}
	}
	seenPages[key] = true
	document.Pages = append(document.Pages, page)
	r.pages = append(r.pages, page)
	return nil
}

// readPageReference 读取页面引用及其链接目标
// 入参: source 来源文档部件, node 已完成结构与名称校验的页面引用元素
// 返回: PageReference 页面引用, error 错误信息
func (r *Reader) readPageReference(source string, node *xmlElement) (PageReference, error) {
	page := PageReference{}
	part, err := referencePart(source, node)
	if err != nil {
		return page, err
	}
	page.Part = part
	for _, attribute := range []struct {
		name  string
		value *float64
	}{{"Width", &page.Width}, {"Height", &page.Height}} {
		if text, ok := node.attribute(attribute.name); ok {
			value, err := xmlNumber(text)
			if err != nil || value < 1 {
				return page, &PartError{Part: source, Element: node.Name.Local, Err: fmt.Errorf("%w: invalid %s", ErrInvalid, attribute.name)}
			}
			*attribute.value = value
		}
	}
	for _, container := range node.Children {
		for _, target := range container.Children {
			name, _ := target.attribute("Name")
			page.LinkTargets = append(page.LinkTargets, name)
		}
	}
	return page, nil
}

// Page 按文档序列中的顺序加载页面，尺寸以页面部件为准
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的页面序号
// 返回: *Page 页面内容, error 错误信息
func (r *Reader) Page(ctx context.Context, pageIndex int) (*Page, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readPageSceneLoaders(pageIndex, false, nil, nil, ctx)
}

// PagePart 按包内部件URI加载固定页面及资源，包括未列入主索引的辅助页面，不改变主阅读页序
// 入参: ctx 取消Context，nil采用Background, part 页面部件的包根URI，不含查询或片段
// 返回: *Page 独立页面内容，失败为nil, error 状态、URI、类型、结构、取消或资源错误
func (r *Reader) PagePart(ctx context.Context, part string) (*Page, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	page, err := r.readPagePartHeader(part, nil, ctx)
	if err != nil {
		return nil, err
	}
	return r.readPageSceneContent(page, false, nil, ctx)
}

// pageLocation 按全局零基页号查找所属固定文档部件、文档序号与文档内局部零基页号
// 入参: index 全局零基页号
// 返回: string 所属固定文档部件URI, int 文档序号, int 文档内局部页号，未命中时返回空串及两个-1
func (r *Reader) pageLocation(index int) (string, int, int) {
	if index < 0 {
		return "", -1, -1
	}
	offset := 0
	for docIndex, doc := range r.documents {
		if index < offset+len(doc.Pages) {
			return doc.Part, docIndex, index - offset
		}
		offset += len(doc.Pages)
	}
	return "", -1, -1
}

// readPage 在调用方持有阅读器读锁时加载页面及绑定资源
// 入参: index 页面序号
// 返回: *Page 独立页面, error 读取或解析错误
func (r *Reader) readPage(index int) (*Page, error) {
	return r.readPageSceneLoaders(index, false, nil, nil, nil)
}

// readPageSceneLoaders 共用页面解析流程，允许调用方提供私有XML读取与字典缓存
// 入参: index 页面序号, retainVisuals 是否保留视觉索引, load 页面XML读取器, dictionaries 字典读取器, ctx 取消Context
// 返回: *Page 独立页面, error 读取、解析、预算或取消错误
func (r *Reader) readPageSceneLoaders(index int, retainVisuals bool, load xmlPartLoader, dictionaries resourceLoader, ctx context.Context) (*Page, error) {
	page, err := r.readPageHeader(index, load, ctx)
	if err != nil {
		return nil, err
	}
	return r.readPageSceneContent(page, retainVisuals, dictionaries, ctx)
}

// readPageHeader 加载并校验页面树及尺寸，不解析资源或物化场景
// 入参: index 页面序号, load 页面XML读取器, ctx 取消Context
// 返回: *Page 私有页面头及源树, error 状态、读取、结构或尺寸错误
func (r *Reader) readPageHeader(index int, load xmlPartLoader, ctx context.Context) (*Page, error) {
	if r.closed {
		return nil, ErrClosed
	}
	if index < 0 || index >= len(r.pages) {
		return nil, fmt.Errorf("%w: page index out of range: %d", ErrInvalid, index)
	}
	return r.readPagePartHeader(r.pages[index].Part, load, ctx)
}

// readPagePartHeader 共用按部件URI加载的页面头校验，不通过临时主索引读取辅助页面
// 入参: part 页面部件URI, load 页面XML读取器, ctx 取消Context
// 返回: *Page 私有页面头及源树，失败为nil, error 状态、URI、读取、结构或尺寸错误
func (r *Reader) readPagePartHeader(part string, load xmlPartLoader, ctx context.Context) (*Page, error) {
	if r.closed {
		return nil, ErrClosed
	}
	if r.pkg == nil {
		return nil, fmt.Errorf("%w: uninitialized reader", ErrInvalid)
	}
	part, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	root, err := r.readFixedPartLoader(part, "fixedpage", "FixedPage", load, ctx)
	if err != nil {
		return nil, err
	}
	return parsePageHeader(root, part, r.format)
}

// readPageSceneContent 复用已校验的页面树绑定资源并构建场景，不重复读取页面部件
// 入参: page 私有页面头及源树, retainVisuals 是否保留视觉索引, dictionaries 字典读取器, ctx 取消Context
// 返回: *Page 完整页面, error 资源、场景或取消错误
func (r *Reader) readPageSceneContent(page *Page, retainVisuals bool, dictionaries resourceLoader, ctx context.Context) (*Page, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if dictionaries == nil {
		dictionaries = func(part string) (*xmlElement, error) {
			return r.readResourceDictionaryLoader(part, nil, ctx)
		}
	}
	resources, err := parseResourceGraphContext(page.Part, page.root, r.format, r.limits, dictionaries, ctx)
	if err != nil {
		return nil, err
	}
	page.resources = resources
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	parser := newSceneParser(r.format, page.resources)
	page.Elements, err = parser.parse(page.root)
	if err != nil {
		return nil, err
	}
	if retainVisuals {
		page.visuals = parser.elements
	}
	if _, err := r.validateRequiredResources(page.Part, page.resources); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return page, nil
}

// parsePageHeader 共用页面尺寸、语言和区域值处理，不把页面引用中的建议尺寸作为页面尺寸
// 入参: root 已完成兼容处理及结构校验的页面根, part 页面URI, format 格式
// 返回: *Page 页面头信息, error 数值、区域词法或尺寸错误
func parsePageHeader(root *xmlElement, part string, format Format) (*Page, error) {
	page := &Page{Format: format, Part: part, root: root}
	for _, attribute := range []struct {
		name  string
		value *float64
	}{{"Width", &page.Width}, {"Height", &page.Height}} {
		text, ok := root.attribute(attribute.name)
		value, err := xmlNumber(text)
		if !ok || err != nil || value < 1 {
			return nil, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%w: invalid %s", ErrInvalid, attribute.name)}
		}
		*attribute.value = value
	}
	language, _ := root.attributeNS(xmlNamespace, "lang")
	page.Language = strings.Trim(language, " \t\r\n")
	page.Name, _ = root.attribute("Name")
	page.ContentBox = Rect{Width: page.Width, Height: page.Height}
	page.BleedBox = page.ContentBox
	for _, attribute := range []struct {
		name  string
		value *Rect
	}{{"ContentBox", &page.ContentBox}, {"BleedBox", &page.BleedBox}} {
		if text, ok := root.attribute(attribute.name); ok {
			box, err := parsePageBox(text, attribute.name == "BleedBox")
			if err != nil {
				return nil, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%s: %w", attribute.name, err)}
			}
			var valid bool
			if attribute.name == "BleedBox" {
				valid = box.X <= 0 && box.Y <= 0 && box.Width >= page.Width-box.X && box.Height >= page.Height-box.Y
			} else {
				valid = box.X >= 0 && box.Y >= 0 && box.X < page.Width && box.Y < page.Height && box.Width <= page.Width-box.X && box.Height <= page.Height-box.Y
			}
			if !valid {
				page.Diagnostics = append(page.Diagnostics, Diagnostic{Part: part, Element: root.Name.Local, Attribute: attribute.name, Message: "invalid page box; page bounds used"})
				continue
			}
			*attribute.value = box
			if attribute.name == "ContentBox" {
				page.HasContentBox = true
			} else {
				page.HasBleedBox = true
			}
		}
	}
	return page, nil
}

// readFixedPart 读取并核对固定布局部件的类型与根元素
// 入参: part 部件名称, kind 部件种类, rootName 根元素名称
// 返回: *xmlElement 根元素, error 错误信息
func (r *Reader) readFixedPart(part, kind, rootName string) (*xmlElement, error) {
	return r.readFixedPartLoader(part, kind, rootName, nil, nil)
}

// readFixedPartLoader 共用固定布局校验，私有读取器不调用StreamPage专用的fixedXML钩子
// 入参: part 部件URI, kind 媒体类型种类, rootName 根名称, load 可选XML读取器, ctx 取消Context
// 返回: *xmlElement 预处理根元素, error 读取、结构或取消错误
func (r *Reader) readFixedPartLoader(part, kind, rootName string, load xmlPartLoader, ctx context.Context) (*xmlElement, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	var root *xmlElement
	var handled bool
	var err error
	if load == nil && kind == "fixedpage" && r.fixedXML != nil {
		root, handled, err = r.fixedXML(part)
		if err != nil {
			return nil, err
		}
	}
	var typeName string
	if handled {
		typeName = r.pkg.declaredContentType(part)
	} else {
		typeName, err = r.pkg.contentType(part)
	}
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if !strings.EqualFold(opcMediaTypeBase(typeName), fixedContentType(kind)) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: unexpected content type %q", ErrInvalid, typeName)}
	}
	if !handled {
		if load != nil {
			root, err = load(part)
		} else {
			root, err = r.pkg.readXMLPart(part, ctx)
		}
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
	}
	namespace := formatNamespace(r.format)
	root, err = preprocessXMLContext(root, []string{namespace, namespace + "/resourcedictionary-key"}, ctx)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if root.Name.Space != formatNamespace(r.format) || root.Name.Local != rootName {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%w: unexpected root {%s}%s", ErrInvalid, root.Name.Space, root.Name.Local)}
	}
	if err := validateFixedStructure(root, r.format); err != nil {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: err}
	}
	if err := validateFixedNames(root, r.format); err != nil {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: err}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return root, nil
}

// fixedChild 核对固定布局子元素的展开名称
// 入参: node 子元素, format 文档格式, name 预期名称
// 返回: error 错误信息
func fixedChild(node *xmlElement, format Format, name string) error {
	if node.Name.Space != formatNamespace(format) {
		return fmt.Errorf("%w: namespace %s", ErrUnsupported, node.Name.Space)
	}
	if node.Name.Local != name {
		return fmt.Errorf("%w: expected %s, got %s", ErrInvalid, name, node.Name.Local)
	}
	if !xmlWhitespace(node.Text) {
		return fmt.Errorf("%w: unexpected text in %s", ErrInvalid, name)
	}
	return nil
}

// referencePart 将Source属性解析为包内部件名称
// 入参: source 来源部件, node 引用元素
// 返回: string 部件名称, error 错误信息
func referencePart(source string, node *xmlElement) (string, error) {
	target, ok := node.attribute("Source")
	if !ok || target == "" {
		return "", &PartError{Part: source, Element: node.Name.Local, Err: fmt.Errorf("%w: missing Source", ErrInvalid)}
	}
	part, err := resolvePart(source, target)
	if err != nil {
		return "", &PartError{Part: source, Element: node.Name.Local, Err: err}
	}
	return part, nil
}

// parsePageBox 解析页面区域的四个坐标值
// 入参: text 区域文本, bleed 是否为出血区域
// 返回: Rect 页面区域, error 错误信息
func parsePageBox(text string, bleed bool) (Rect, error) {
	items := strings.Split(text, ",")
	if len(items) != 4 {
		return Rect{}, fmt.Errorf("%w: expected four page box coordinates", ErrInvalid)
	}
	var values [4]float64
	for i, item := range items {
		if (!bleed || i >= 2) && strings.HasPrefix(strings.Trim(item, " \t\r\n"), "-") {
			return Rect{}, fmt.Errorf("%w: negative sign in page box", ErrInvalid)
		}
		value, err := xmlNumber(item)
		if err != nil {
			return Rect{}, err
		}
		values[i] = value
	}
	if values[2] < 0 || values[3] < 0 {
		return Rect{}, fmt.Errorf("%w: negative page box size", ErrInvalid)
	}
	return Rect{X: values[0], Y: values[1], Width: values[2], Height: values[3]}, nil
}

// DocumentStructure 读取指定固定文档的结构，未关联结构部件时返回nil
// 入参: ctx 取消Context，nil采用Background, docIndex 从零开始的固定文档序号
// 返回: *DocumentStructure 独立结构数据, error 读取、模式、取消或页码错误
func (r *Reader) DocumentStructure(ctx context.Context, docIndex int) (*DocumentStructure, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readDocumentStructureContext(ctx, docIndex)
}

// readDocumentStructure 在调用方持有读锁时读取固定文档关联的结构
// 入参: index 文档序号
// 返回: *DocumentStructure 独立结构数据, error 读取或结构错误
func (r *Reader) readDocumentStructure(index int) (*DocumentStructure, error) {
	return r.readDocumentStructureContext(nil, index)
}

// readDocumentStructureContext 在调用方持有读锁且响应取消时读取固定文档关联的结构
// 入参: ctx 取消Context, index 文档序号
// 返回: *DocumentStructure 独立结构数据, error 读取、取消或结构错误
func (r *Reader) readDocumentStructureContext(ctx context.Context, index int) (*DocumentStructure, error) {
	if r.closed {
		return nil, ErrClosed
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.documents) {
		return nil, fmt.Errorf("%w: document index out of range: %d", ErrInvalid, index)
	}
	document := r.documents[index]
	part, root, err := r.readStructurePartContext(ctx, document.Part, "documentstructure", "DocumentStructure")
	if err != nil || root == nil {
		return nil, err
	}
	result, err := parseDocumentStructure(root, structureNamespace(r.format), len(document.Pages))
	if err != nil {
		return nil, &PartError{Part: part, Element: root.Name.Local, Err: err}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	result.Part = part
	return result, nil
}

// parseDocumentStructure 校验可选目录与故事的顺序，不把普通故事字符串当作XML标识符
// 入参: root 结构根节点, namespace 结构命名空间, pages 所属固定文档的页面数量
// 返回: *DocumentStructure 完整结构数据, error 模式或引用错误
func parseDocumentStructure(root *xmlElement, namespace string, pages int) (*DocumentStructure, error) {
	if _, err := structureAttributes(root, namespace); err != nil {
		return nil, err
	}
	result := &DocumentStructure{}
	names := make(map[string]bool)
	for index, child := range root.Children {
		switch child.Name.Local {
		case "DocumentStructure.Outline":
			if index != 0 || result.Outline != nil {
				return nil, fmt.Errorf("%w: outline must precede stories and occur once", ErrInvalid)
			}
			if _, err := structureAttributes(child, namespace); err != nil {
				return nil, err
			}
			if len(child.Children) != 1 || child.Children[0].Name.Local != "DocumentOutline" {
				return nil, fmt.Errorf("%w: document outline container", ErrInvalid)
			}
			outline, err := parseDocumentOutline(child.Children[0], namespace)
			if err != nil {
				return nil, err
			}
			result.Outline = outline
		case "Story":
			story, err := parseStory(child, namespace, pages)
			if err != nil {
				return nil, err
			}
			if names[story.Name] {
				return nil, fmt.Errorf("%w: duplicate story name %q", ErrInvalid, story.Name)
			}
			names[story.Name] = true
			result.Stories = append(result.Stories, story)
		default:
			return nil, fmt.Errorf("%w: document structure child %s", ErrInvalid, child.Name.Local)
		}
	}
	return result, nil
}

// parseDocumentOutline 读取必需语言及至少一个目录条目，保留原始描述文字
// 入参: root 目录根节点, namespace 结构命名空间
// 返回: *DocumentOutline 目录, error 模式或属性错误
func parseDocumentOutline(root *xmlElement, namespace string) (*DocumentOutline, error) {
	attrs, err := structureAttributes(root, namespace, "xml:lang")
	if err != nil {
		return nil, err
	}
	language, err := structureLanguage(attrs, true)
	if err != nil {
		return nil, err
	}
	if len(root.Children) == 0 {
		return nil, fmt.Errorf("%w: empty document outline", ErrInvalid)
	}
	result := &DocumentOutline{Language: *language}
	for _, child := range root.Children {
		if child.Name.Local != "OutlineEntry" || len(child.Children) != 0 {
			return nil, fmt.Errorf("%w: outline entry content", ErrInvalid)
		}
		attrs, err := structureAttributes(child, namespace, "OutlineLevel", "OutlineTarget", "Description", "xml:lang")
		if err != nil {
			return nil, err
		}
		level, err := structureInt(attrs, "OutlineLevel", 1)
		if err != nil {
			return nil, err
		}
		target, hasTarget := attrs["OutlineTarget"]
		description, hasDescription := attrs["Description"]
		if !hasTarget || !hasDescription {
			return nil, fmt.Errorf("%w: missing outline target or description", ErrInvalid)
		}
		target = structureURI(target)
		if target == "" || !uriReference(target) {
			return nil, fmt.Errorf("%w: invalid outline target %q", ErrInvalid, target)
		}
		language, err := structureLanguage(attrs, false)
		if err != nil {
			return nil, err
		}
		result.Entries = append(result.Entries, OutlineEntry{Level: level, Target: target, Description: description, Language: language})
	}
	return result, nil
}

// parseStory 校验必需名称、片段序列及文档内页码，仅显式片段名参与名称唯一性检查
// 入参: root 故事节点, namespace 结构命名空间, pages 所属文档页面数
// 返回: Story 故事定义, error 模式或页码错误
func parseStory(root *xmlElement, namespace string, pages int) (Story, error) {
	attrs, err := structureAttributes(root, namespace, "StoryName")
	if err != nil {
		return Story{}, err
	}
	name, present := attrs["StoryName"]
	if !present || len(root.Children) == 0 {
		return Story{}, fmt.Errorf("%w: story name or fragments missing", ErrInvalid)
	}
	result := Story{Name: name}
	names := make(map[string]bool)
	for _, child := range root.Children {
		if child.Name.Local != "StoryFragmentReference" || len(child.Children) != 0 {
			return Story{}, fmt.Errorf("%w: story fragment reference content", ErrInvalid)
		}
		attrs, err := structureAttributes(child, namespace, "Page", "FragmentName")
		if err != nil {
			return Story{}, err
		}
		page, err := structureInt(attrs, "Page", 0)
		if err != nil {
			return Story{}, err
		}
		if int64(page) > int64(pages) {
			return Story{}, fmt.Errorf("%w: story page %d outside its fixed document", ErrInvalid, page)
		}
		fragment := structureString(attrs, "FragmentName")
		if fragment != nil {
			if names[*fragment] {
				return Story{}, fmt.Errorf("%w: duplicate fragment name %q in story", ErrInvalid, *fragment)
			}
			names[*fragment] = true
		}
		result.Fragments = append(result.Fragments, StoryFragmentReference{PageNumber: int(page), FragmentName: fragment})
	}
	return result, nil
}

// validateFixedStructure 校验完成MCE处理后的固定布局结构、属性白名单及页面语言，不展开视觉树和资源字典
// 入参: root 结构根元素, format 文档格式
// 返回: error 结构或属性错误，尺寸、URI和名称值语义由对应解析器校验
func validateFixedStructure(root *xmlElement, format Format) error {
	return validateFixedStructureElement(root, format, true)
}

// validateFixedStructureElement 共用固定布局属性及子结构校验，未结束根元素暂缓最少子元素数量检查
// 入参: root 当前结构根, format 文档格式, complete 根元素是否已经结束
// 返回: error 结构、属性或数量错误
func validateFixedStructureElement(root *xmlElement, format Format, complete bool) error {
	namespace := formatNamespace(format)
	if namespace == "" || root == nil || root.Name.Space != namespace {
		return fmt.Errorf("%w: invalid fixed structure namespace", ErrInvalid)
	}
	name := root.Name.Local
	var allowed, required []string
	var childName string
	minimum, maximum := 0, 0
	switch name {
	case "FixedDocumentSequence":
		childName, minimum, maximum = "DocumentReference", 1, -1
	case "DocumentReference":
		allowed, required = []string{"Source"}, []string{"Source"}
	case "FixedDocument":
		childName, minimum, maximum = "PageContent", 1, -1
	case "PageContent":
		allowed, required = []string{"Source", "Width", "Height"}, []string{"Source"}
		childName, maximum = "PageContent.LinkTargets", 1
	case "PageContent.LinkTargets":
		childName, minimum, maximum = "LinkTarget", 1, -1
	case "LinkTarget":
		allowed, required = []string{"Name"}, []string{"Name"}
	case "FixedPage":
		allowed = []string{"Width", "Height", "ContentBox", "BleedBox", "Name"}
		required = []string{"Width", "Height"}
		maximum = -1
	case "FixedPage.Resources":
		childName, minimum, maximum = "ResourceDictionary", 1, 1
	default:
		return fmt.Errorf("%w: unexpected fixed structure element %s", ErrInvalid, name)
	}
	if !xmlWhitespace(root.Text) {
		return fmt.Errorf("%w: unexpected text in %s", ErrInvalid, name)
	}
	seen := make(map[xml.Name]bool, len(root.Attr))
	for _, attr := range root.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if seen[attr.Name] {
			return fmt.Errorf("%w: duplicate attribute {%s}%s on %s", ErrInvalid, attr.Name.Space, attr.Name.Local, name)
		}
		seen[attr.Name] = true
		if name == "FixedPage" && attr.Name == (xml.Name{Space: xmlNamespace, Local: "lang"}) {
			if !fixedLanguageTag(attr.Value) {
				return fmt.Errorf("%w: invalid xml:lang on FixedPage", ErrInvalid)
			}
			continue
		}
		if attr.Name.Space != "" || !slices.Contains(allowed, attr.Name.Local) {
			return fmt.Errorf("%w: unexpected attribute {%s}%s on %s", ErrInvalid, attr.Name.Space, attr.Name.Local, name)
		}
	}
	for _, attr := range required {
		if !seen[xml.Name{Local: attr}] {
			return fmt.Errorf("%w: missing %s on %s", ErrInvalid, attr, name)
		}
	}
	if name == "FixedPage" && !seen[xml.Name{Space: xmlNamespace, Local: "lang"}] {
		return fmt.Errorf("%w: missing xml:lang on FixedPage", ErrInvalid)
	}
	if complete && len(root.Children) < minimum || maximum >= 0 && len(root.Children) > maximum {
		return fmt.Errorf("%w: invalid child count in %s", ErrInvalid, name)
	}
	for i, child := range root.Children {
		if child == nil || child.Name.Space != namespace {
			return fmt.Errorf("%w: invalid child namespace in %s", ErrInvalid, name)
		}
		if name == "FixedPage" {
			switch child.Name.Local {
			case "Path", "Glyphs", "Canvas":
				continue
			case "FixedPage.Resources":
				if i != 0 {
					return fmt.Errorf("%w: page resources must precede drawing elements", ErrInvalid)
				}
			default:
				return fmt.Errorf("%w: unexpected child %s in FixedPage", ErrInvalid, child.Name.Local)
			}
		} else if child.Name.Local != childName {
			return fmt.Errorf("%w: unexpected child %s in %s", ErrInvalid, child.Name.Local, name)
		}
		if name != "FixedPage.Resources" {
			if err := validateFixedStructure(child, format); err != nil {
				return err
			}
		}
	}
	return nil
}

// fixedLanguageTag 校验固定布局非空语言标签词法，允许首尾XML空白折叠
// 入参: value 语言属性值
// 返回: bool 是否符合语言标签词法
func fixedLanguageTag(value string) bool {
	value = strings.Trim(value, " \t\r\n")
	for i, subtag := range strings.Split(value, "-") {
		if len(subtag) < 1 || len(subtag) > 8 {
			return false
		}
		for j := range len(subtag) {
			c := subtag[j]
			if c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z' || i > 0 && c >= '0' && c <= '9' {
				continue
			}
			return false
		}
	}
	return true
}

// structureNamespace 返回文档结构和故事片段使用的命名空间
// 入参: format 文档格式
// 返回: string 命名空间，未知格式返回空字符串
func structureNamespace(format Format) string {
	if namespace := formatNamespace(format); namespace != "" {
		return namespace + "/documentstructure"
	}
	return ""
}

// readStructurePartContext 在持有读锁下加载包内关联的结构部件，未关联返回nil，多目标报错
// 入参: ctx 取消Context, source 来源文档或页面部件, kind 关联类型, rootName 根元素名
// 返回: string 目标部件, *xmlElement 预处理后的根元素，未关联时为nil, error 读取、取消或结构错误
func (r *Reader) readStructurePartContext(ctx context.Context, source, kind, rootName string) (string, *xmlElement, error) {
	if err := checkContext(ctx); err != nil {
		return "", nil, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, source)
	if err != nil {
		return "", nil, &PartError{Part: source, Err: err}
	}
	part := ""
	for _, relation := range relations {
		if relation.Type != formatNamespace(r.format)+"/"+kind {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return "", nil, &PartError{Part: source, Err: fmt.Errorf("%w: external %s part", ErrInvalid, rootName)}
		}
		target, err := resolvePart(source, relation.Target)
		if err != nil {
			return "", nil, &PartError{Part: source, Err: err}
		}
		if part != "" && !strings.EqualFold(part, target) {
			return "", nil, &PartError{Part: source, Err: fmt.Errorf("%w: multiple distinct %s parts", ErrInvalid, rootName)}
		}
		part = target
	}
	if part == "" {
		return "", nil, nil
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return "", nil, &PartError{Part: part, Err: err}
	}
	if !strings.EqualFold(opcMediaTypeBase(media), fixedContentType(kind)) {
		return "", nil, &PartError{Part: part, Err: fmt.Errorf("%w: %s content type %q", ErrInvalid, rootName, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, strings.ToLower(part), r.limits.MaxPartBytes)
	if err != nil {
		return "", nil, &PartError{Part: part, Err: err}
	}
	root, err := decodeXMLVisit(data, r.limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err == nil {
		root, err = preprocessXMLContext(root, []string{structureNamespace(r.format)}, ctx)
	}
	if err != nil {
		return "", nil, &PartError{Part: part, Err: err}
	}
	if root.Name.Space != structureNamespace(r.format) || root.Name.Local != rootName {
		return "", nil, &PartError{Part: part, Element: root.Name.Local, Err: fmt.Errorf("%w: expected %s root", ErrInvalid, rootName)}
	}
	return part, root, nil
}

// structureAttributes 校验结构节点的命名空间、空白文本及属性集合，不合并不同命名空间中的同名属性
// 入参: node 已完成兼容性处理的节点, namespace 结构命名空间, allowed 允许的属性名，xml:lang单独列出
// 返回: map[string]string 属性值, error 节点或属性错误
func structureAttributes(node *xmlElement, namespace string, allowed ...string) (map[string]string, error) {
	if node == nil || node.Name.Space != namespace || !xmlWhitespace(node.Text) {
		return nil, fmt.Errorf("%w: document structure node or text", ErrInvalid)
	}
	attrs := make(map[string]string, len(node.Attr))
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name.Space == "" && attribute.Name.Local == "xmlns" {
			continue
		}
		name := attribute.Name.Local
		if attribute.Name.Space == xmlNamespace && name == "lang" {
			name = "xml:lang"
		} else if attribute.Name.Space != "" {
			return nil, fmt.Errorf("%w: namespaced structure attribute %s", ErrInvalid, name)
		}
		if !slices.Contains(allowed, name) {
			return nil, fmt.Errorf("%w: unexpected %s attribute on %s", ErrInvalid, name, node.Name.Local)
		}
		if _, exists := attrs[name]; exists {
			return nil, fmt.Errorf("%w: duplicate structure attribute %s", ErrInvalid, name)
		}
		attrs[name] = attribute.Value
	}
	return attrs, nil
}

// structureInt 解析结构模式要求的正32位XML整数，省略可选字段时使用指定默认值
// 入参: attrs 已校验的属性, name 属性名, fallback 默认值，零表示必需属性
// 返回: int32 正整数, error 词法、范围或缺少属性错误
func structureInt(attrs map[string]string, name string, fallback int32) (int32, error) {
	text, present := attrs[name]
	if !present {
		if fallback > 0 {
			return fallback, nil
		}
		return 0, fmt.Errorf("%w: missing structure attribute %s", ErrInvalid, name)
	}
	value, err := strconv.ParseInt(strings.Trim(text, " \t\r\n"), 10, 32)
	if err != nil || value < 1 {
		return 0, fmt.Errorf("%w: invalid structure integer %s", ErrInvalid, name)
	}
	return int32(value), nil
}

// structureString 保留可选字符串属性的存在性，空字符串不等同于省略
// 入参: attrs 已校验属性, name 属性名
// 返回: *string 独立字符串值，省略时为nil
func structureString(attrs map[string]string, name string) *string {
	if value, present := attrs[name]; present {
		return &value
	}
	return nil
}

// structureLanguage 校验并折叠结构元素的语言属性，不改动故事名称或普通字符串
// 入参: attrs 已校验属性, required 是否要求语言属性
// 返回: *string 规范化语言，省略可选属性时为nil, error 缺少或非法语言错误
func structureLanguage(attrs map[string]string, required bool) (*string, error) {
	value, present := attrs["xml:lang"]
	if !present && !required {
		return nil, nil
	}
	if present && !required && value == "" {
		return &value, nil
	}
	value = strings.Trim(value, " \t\r\n")
	if !present || !fixedLanguageTag(value) {
		return nil, fmt.Errorf("%w: document outline language", ErrInvalid)
	}
	return &value, nil
}

// structureURI 折叠目录目标URI的XML空白并原样保留声明文本
// 入参: value 原始属性值
// 返回: string 折叠后的URI声明
func structureURI(value string) string {
	return strings.Join(compatibilityWords(value), " ")
}

// structureName 校验结构模式的ST_Name，不套用固定页面名称的不同字符规则
// 入参: value 未折叠的名称
// 返回: bool 是否符合结构名称模式
func structureName(value string) bool {
	if value == "" {
		return false
	}
	for index, character := range value {
		if unicode.IsOneOf(nameStartRanges, character) {
			continue
		}
		if index == 0 || character != '_' && !unicode.IsOneOf(structureNameContinueRanges, character) {
			return false
		}
	}
	return true
}

// StoryFragments 读取指定页面关联的全部故事片段，未关联部件时返回nil
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页面序号
// 返回: *StoryFragments 独立片段数据, error 读取、取消或模式错误
func (r *Reader) StoryFragments(ctx context.Context, pageIndex int) (*StoryFragments, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readStoryFragmentsContext(ctx, pageIndex)
}

// readStoryFragments 在调用方持有读锁时读取页面关联的故事片段
// 入参: index 全局页面序号
// 返回: *StoryFragments 独立片段数据, error 读取或模式错误
func (r *Reader) readStoryFragments(index int) (*StoryFragments, error) {
	return r.readStoryFragmentsContext(nil, index)
}

// readStoryFragmentsContext 在调用方持有读锁且响应取消时读取页面关联的故事片段
// 入参: ctx 取消Context, index 全局页面序号
// 返回: *StoryFragments 独立片段数据, error 读取、取消或模式错误
func (r *Reader) readStoryFragmentsContext(ctx context.Context, index int) (*StoryFragments, error) {
	if r.closed {
		return nil, ErrClosed
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.pages) {
		return nil, fmt.Errorf("%w: page index out of range: %d", ErrInvalid, index)
	}
	part, root, err := r.readStructurePartContext(ctx, r.pages[index].Part, "storyfragments", "StoryFragments")
	if err != nil || root == nil {
		return nil, err
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

// parseStoryFragments 读取至少一个片段，并按XML部件范围校验列表标记的ID唯一性
// 入参: root 片段根节点, namespace 结构命名空间, maxDepth 结构深度上限
// 返回: *StoryFragments 完整片段集合, error 模式或标识错误
func parseStoryFragments(root *xmlElement, namespace string, maxDepth int) (*StoryFragments, error) {
	if _, err := structureAttributes(root, namespace); err != nil {
		return nil, err
	}
	if len(root.Children) == 0 {
		return nil, fmt.Errorf("%w: empty story fragments", ErrInvalid)
	}
	result := &StoryFragments{}
	identifiers := make(map[string]bool)
	for _, child := range root.Children {
		if child.Name.Local != "StoryFragment" {
			return nil, fmt.Errorf("%w: story fragments child %s", ErrInvalid, child.Name.Local)
		}
		fragment, err := parseStoryFragment(child, namespace, identifiers, maxDepth)
		if err != nil {
			return nil, err
		}
		result.Fragments = append(result.Fragments, fragment)
	}
	return result, nil
}

// parseStoryFragment 保留首尾断点，不将中间StoryBreak当作有效内容或补入缺少的FragmentType
// 入参: root 片段节点, namespace 结构命名空间, identifiers 当前部件的XML标识集合, maxDepth 结构深度上限
// 返回: StoryFragment 片段, error 模式或标识错误
func parseStoryFragment(root *xmlElement, namespace string, identifiers map[string]bool, maxDepth int) (StoryFragment, error) {
	attrs, err := structureAttributes(root, namespace, "StoryName", "FragmentName", "FragmentType")
	if err != nil {
		return StoryFragment{}, err
	}
	result := StoryFragment{StoryName: structureString(attrs, "StoryName"), FragmentName: structureString(attrs, "FragmentName")}
	switch attrs["FragmentType"] {
	case "Content":
		result.Type = FragmentContent
	case "Header":
		result.Type = FragmentHeader
	case "Footer":
		result.Type = FragmentFooter
	default:
		return StoryFragment{}, fmt.Errorf("%w: missing or invalid fragment type", ErrInvalid)
	}
	for index, child := range root.Children {
		if child.Name.Local == "StoryBreak" {
			if _, err := structureAttributes(child, namespace); err != nil {
				return StoryFragment{}, err
			}
			if len(child.Children) != 0 {
				return StoryFragment{}, fmt.Errorf("%w: story break content", ErrInvalid)
			}
			if index == 0 {
				result.BreakBefore = true
			} else if index == len(root.Children)-1 {
				result.BreakAfter = true
			} else {
				return StoryFragment{}, fmt.Errorf("%w: story break must be first or last", ErrInvalid)
			}
			continue
		}
		node, err := parseContentStructure(child, namespace, identifiers, 0, maxDepth)
		if err != nil {
			return StoryFragment{}, err
		}
		if node.Kind != StructureSection && node.Kind != StructureParagraph && node.Kind != StructureList && node.Kind != StructureTable && node.Kind != StructureFigure {
			return StoryFragment{}, fmt.Errorf("%w: story fragment block type", ErrInvalid)
		}
		result.Content = append(result.Content, node)
	}
	if len(result.Content) == 0 {
		return StoryFragment{}, fmt.Errorf("%w: story fragment requires a content block", ErrInvalid)
	}
	return result, nil
}

// parseContentStructure 按文档结构模式读取语义树，空段落、图形、列表项目及单元格保持为空
// 入参: root 语义节点, namespace 结构命名空间, identifiers 当前部件ID集合, depth 当前结构深度, maxDepth 深度上限
// 返回: ContentStructure 独立语义节点, error 模式、标识或深度错误
func parseContentStructure(root *xmlElement, namespace string, identifiers map[string]bool, depth, maxDepth int) (ContentStructure, error) {
	if depth >= maxDepth {
		return ContentStructure{}, fmt.Errorf("%w: content structure depth", ErrLimit)
	}
	result := ContentStructure{}
	minimum := 1
	var allowed []string
	switch root.Name.Local {
	case "SectionStructure":
		result.Kind = StructureSection
	case "ParagraphStructure":
		result.Kind, minimum = StructureParagraph, 0
	case "TableStructure":
		result.Kind = StructureTable
	case "TableRowGroupStructure":
		result.Kind = StructureRowGroup
	case "TableRowStructure":
		result.Kind = StructureRow
	case "TableCellStructure":
		result.Kind, minimum, allowed = StructureCell, 0, []string{"RowSpan", "ColumnSpan"}
	case "ListStructure":
		result.Kind = StructureList
	case "ListItemStructure":
		result.Kind, minimum, allowed = StructureListItem, 0, []string{"Marker"}
	case "FigureStructure":
		result.Kind, minimum = StructureFigure, 0
	case "NamedElement":
		result.Kind, minimum, allowed = StructureNamedElement, 0, []string{"NameReference"}
	default:
		return ContentStructure{}, fmt.Errorf("%w: content structure element %s", ErrInvalid, root.Name.Local)
	}
	attrs, err := structureAttributes(root, namespace, allowed...)
	if err != nil {
		return ContentStructure{}, err
	}
	if len(root.Children) < minimum || result.Kind == StructureNamedElement && len(root.Children) != 0 {
		return ContentStructure{}, fmt.Errorf("%w: content structure child count", ErrInvalid)
	}
	if result.Kind == StructureNamedElement {
		result.NameReference = attrs["NameReference"]
		if !structureName(result.NameReference) {
			return ContentStructure{}, fmt.Errorf("%w: structure name reference", ErrInvalid)
		}
	}
	if result.Kind == StructureCell {
		result.RowSpan, err = structureInt(attrs, "RowSpan", 1)
		if err == nil {
			result.ColumnSpan, err = structureInt(attrs, "ColumnSpan", 1)
		}
		if err != nil {
			return ContentStructure{}, err
		}
	}
	if marker, present := attrs["Marker"]; present {
		marker = strings.Trim(marker, " \t\r\n")
		if !structureName(marker) || !xmlNCName(marker) || identifiers[marker] {
			return ContentStructure{}, fmt.Errorf("%w: invalid or duplicate list marker ID %q", ErrInvalid, marker)
		}
		identifiers[marker] = true
		result.Marker = &marker
	}
	for _, child := range root.Children {
		node, err := parseContentStructure(child, namespace, identifiers, depth+1, maxDepth)
		if err != nil {
			return ContentStructure{}, err
		}
		if !structureChild(result.Kind, node.Kind) {
			return ContentStructure{}, fmt.Errorf("%w: %s child of %s", ErrInvalid, child.Name.Local, root.Name.Local)
		}
		result.Children = append(result.Children, node)
	}
	return result, nil
}

// structureChild 判断模式允许的直接父子关系，不把段落、分节或表格层次互换
// 入参: parent 父节点类型, child 子节点类型
// 返回: bool 是否允许该直接子节点
func structureChild(parent, child StructureKind) bool {
	switch parent {
	case StructureSection, StructureCell, StructureListItem:
		return child == StructureParagraph || child == StructureList || child == StructureTable || child == StructureFigure
	case StructureParagraph, StructureFigure:
		return child == StructureNamedElement
	case StructureTable:
		return child == StructureRowGroup
	case StructureRowGroup:
		return child == StructureRow
	case StructureRow:
		return child == StructureCell
	case StructureList:
		return child == StructureListItem
	}
	return false
}

// ResolveLink 相对于源部件解析包内或外部链接，按声明顺序定位命名元素或页号，忽略未识别片段
// 未列入主阅读索引的页面Page为-1，外部目标保留原始声明且不执行网络访问
// 入参: ctx 取消Context，nil采用Background, source 源部件的包根URI, target 链接声明
// 返回: LinkTarget 目标及页面定位, error 输入、目标部件、取消或页面读取错误
func (r *Reader) ResolveLink(ctx context.Context, source, target string) (LinkTarget, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return LinkTarget{}, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return LinkTarget{}, err
	}
	source, err := opcPartName(source)
	if err != nil {
		return LinkTarget{}, err
	}
	if _, exists := r.pkg.parts[strings.ToLower(source)]; !exists {
		return LinkTarget{}, fmt.Errorf("%w: link source part %s is absent", ErrInvalid, source)
	}
	target = structureURI(target)
	result := LinkTarget{URI: target, Page: -1, Transform: IdentityMatrix()}
	if linkExternal(target) {
		result.External = true
		return result, nil
	}
	uri, err := url.Parse(target)
	if err != nil {
		return LinkTarget{}, fmt.Errorf("%w: link URI: %w", ErrInvalid, err)
	}
	if uri.RawQuery != "" || uri.ForceQuery {
		return LinkTarget{}, fmt.Errorf("%w: query in package link", ErrUnsupported)
	}
	part := source
	if uri.Path != "" {
		part, err = resolvePart(source, uri.EscapedPath())
		if err != nil {
			return LinkTarget{}, err
		}
	}
	if _, exists := r.pkg.parts[strings.ToLower(part)]; !exists {
		return LinkTarget{}, fmt.Errorf("%w: link target part %s is absent", ErrInvalid, part)
	}
	result.Part = part
	document, first, count := r.linkScope(part)
	if count == 0 {
		return r.resolveAuxiliaryLink(ctx, source, result, uri.Fragment)
	}
	result.Page, result.Part = first, r.pages[first].Part
	fragment := uri.Fragment
	if fragment == "" {
		return result, nil
	}
	if linkPageNumber(fragment) {
		if !strings.EqualFold(part, r.sequence) {
			return LinkTarget{}, fmt.Errorf("%w: internal page address must target the fixed document sequence", ErrInvalid)
		}
		number, err := strconv.ParseUint(fragment, 10, 64)
		if err == nil && number > 0 && number <= uint64(len(r.pages)) {
			result.Page = int(number) - 1
			result.Part = r.pages[result.Page].Part
		}
		return result, nil
	}
	if document < 0 {
		if !strings.EqualFold(part, r.sequence) {
			return LinkTarget{}, fmt.Errorf("%w: internal named address must target a fixed document", ErrInvalid)
		}
		return r.resolveNamedLink(ctx, result, fragment, 0, len(r.pages))
	}
	return r.resolveNamedLink(ctx, result, fragment, first, count)
}

// validateLinkFragment 按实际布局类型检查片段，不把未索引的辅助布局当作普通资源
// 入参: media 目标部件类型, fragment 已解码片段, indexed 是否具有主阅读索引中的地址范围
// 返回: error 地址形式错误或辅助布局范围尚未索引
func validateLinkFragment(media, fragment string, indexed bool) error {
	if fragment == "" {
		return nil
	}
	base := opcMediaTypeBase(media)
	page := strings.EqualFold(base, fixedContentType("fixedpage"))
	document := strings.EqualFold(base, fixedContentType("fixeddocument"))
	sequence := strings.EqualFold(base, fixedContentType("fixeddocumentsequence"))
	if page || document && linkPageNumber(fragment) {
		return fmt.Errorf("%w: internal fragment address targets the wrong fixed layout type", ErrInvalid)
	}
	if !indexed && (document || sequence) {
		return fmt.Errorf("%w: auxiliary fixed layout address scope is not indexed", ErrUnsupported)
	}
	return nil
}

// linkExternal 按URI方案名或网络路径前缀区分外部声明，不将所有方案的授权部分当作服务器地址
// 入参: value 已折叠XML空白的URI声明
// 返回: bool 是否为外部目标
func linkExternal(value string) bool {
	if strings.HasPrefix(value, "//") {
		return true
	}
	scheme, _, present := strings.Cut(value, ":")
	return present && uriScheme(scheme)
}

// linkScope 返回目标部件对应的文档序号及页面范围，非固定布局资源返回空范围
// 入参: part 已校验的包内部件
// 返回: int 文档序号，序列或页面为-1, int 首页号, int 页面数量
func (r *Reader) linkScope(part string) (int, int, int) {
	if strings.EqualFold(part, r.sequence) {
		return -1, 0, len(r.pages)
	}
	first := 0
	for index, document := range r.documents {
		if strings.EqualFold(part, document.Part) {
			return index, first, len(document.Pages)
		}
		first += len(document.Pages)
	}
	for index, page := range r.pages {
		if strings.EqualFold(part, page.Part) {
			return -1, index, 1
		}
	}
	return -1, 0, 0
}

// linkPageNumber 判断片段是否只含十进制页号字符，数值范围由序列检查
// 入参: value 已解码的片段
// 返回: bool 是否为页号形式
func linkPageNumber(value string) bool {
	if value == "" {
		return false
	}
	for i := range len(value) {
		if value[i] < '0' || value[i] > '9' {
			return false
		}
	}
	return true
}

// resolveNamedLink 只检索已声明的地址，重复地址取首次声明，声明后缺少元素时返回对应页首
// 入参: ctx 取消Context, result 默认目标, name 命名地址, first 范围首张页面, count 页面数量
// 返回: LinkTarget 页面定位, error 页面、取消或变换错误
func (r *Reader) resolveNamedLink(ctx context.Context, result LinkTarget, name string, first, count int) (LinkTarget, error) {
	for index := first; index < first+count; index++ {
		if err := checkContext(ctx); err != nil {
			return LinkTarget{}, err
		}
		for _, declared := range r.pages[index].LinkTargets {
			if declared != name {
				continue
			}
			page, err := r.readPageSceneLoaders(index, false, nil, nil, ctx)
			if err != nil {
				return LinkTarget{}, err
			}
			result.Page, result.Part, result.Name = index, page.Part, name
			if page.Name == name {
				return result, nil
			}
			element, transform, err := linkElement(page.Elements, name, IdentityMatrix(), 0, r.limits.MaxXMLDepth)
			if err != nil {
				return LinkTarget{}, err
			}
			if element != nil {
				result.Element, result.Transform = element, transform
			}
			return result, nil
		}
	}
	return result, nil
}

// linkElement 按标记顺序查找直接页面元素，不进入视觉画刷或资源定义
// 入参: elements 绘制元素, name 名称, parent 祖先变换, depth 当前深度, maxDepth 深度上限
// 返回: Element 独立元素，未找到返回nil, Matrix 有效页面变换, error 深度或变换错误
func linkElement(elements []Element, name string, parent Matrix, depth, maxDepth int) (Element, Matrix, error) {
	if depth >= maxDepth {
		return nil, Matrix{}, fmt.Errorf("%w: link target depth", ErrLimit)
	}
	for _, element := range elements {
		properties := contentProperties(element)
		if properties == nil {
			return nil, Matrix{}, fmt.Errorf("%w: link target element", ErrInvalid)
		}
		transform := parent
		if properties.RenderTransform != nil {
			transform = strokePathCompose(parent, *properties.RenderTransform)
			if !geometryFillMatrixFinite(transform) {
				return nil, Matrix{}, fmt.Errorf("%w: link target transform range", ErrLimit)
			}
		}
		if properties.Name == name {
			return element, transform, nil
		}
		if canvas, ok := element.(*Canvas); ok && len(canvas.Elements) != 0 {
			value, matrix, err := linkElement(canvas.Elements, name, transform, depth+1, maxDepth)
			if err != nil || value != nil {
				return value, matrix, err
			}
		}
	}
	return nil, Matrix{}, nil
}

// resolveAuxiliaryLink 在独立索引中解析辅助布局地址，调用方须持有阅读器读锁
// 入参: ctx 取消Context, source 源部件URI, result 已解析的内部目标, fragment 已解码片段
// 返回: LinkTarget 实际页面及主索引页号, error 目标结构、读取、取消或预算错误
func (r *Reader) resolveAuxiliaryLink(ctx context.Context, source string, result LinkTarget, fragment string) (LinkTarget, error) {
	if err := checkContext(ctx); err != nil {
		return LinkTarget{}, err
	}
	media, err := r.pkg.contentType(result.Part)
	if err != nil {
		return LinkTarget{}, err
	}
	if err := validateLinkFragment(media, fragment, true); err != nil {
		return LinkTarget{}, err
	}
	base := opcMediaTypeBase(media)
	document := strings.EqualFold(base, fixedContentType("fixeddocument"))
	sequence := strings.EqualFold(base, fixedContentType("fixeddocumentsequence"))
	if !document && !sequence {
		return result, nil
	}
	view := &Reader{pkg: r.pkg, format: r.format, limits: r.limits, fixedXML: r.fixedXML}
	parts := []string{result.Part}
	if sequence {
		view.sequence = result.Part
		parts, err = view.readDocumentReferencesContext(ctx)
		if err != nil {
			return LinkTarget{}, err
		}
	}
	seen := make(map[string]bool)
	for _, part := range parts {
		if err := checkContext(ctx); err != nil {
			return LinkTarget{}, err
		}
		doc, err := view.readDocumentContext(ctx, part, seen)
		if err != nil {
			return LinkTarget{}, err
		}
		view.documents = append(view.documents, doc)
	}
	resolved, err := view.ResolveLink(ctx, source, result.URI)
	if err != nil {
		return LinkTarget{}, err
	}
	media, err = r.pkg.contentType(resolved.Part)
	if err != nil {
		return LinkTarget{}, err
	}
	if !strings.EqualFold(opcMediaTypeBase(media), fixedContentType("fixedpage")) {
		return LinkTarget{}, fmt.Errorf("%w: auxiliary link target is not a fixed page", ErrInvalid)
	}
	resolved.Page = -1
	for index, page := range r.pages {
		if strings.EqualFold(page.Part, resolved.Part) {
			resolved.Page = index
			break
		}
	}
	return resolved, nil
}

// fixedNamePattern 校验固定布局名称和资源键允许的Unicode字符类别
// 入参: value 待校验名称
// 返回: bool 是否符合名称模式
func fixedNamePattern(value string) bool {
	if value == "" {
		return false
	}
	for i, c := range value {
		if c == '_' || unicode.IsOneOf(nameStartRanges, c) {
			continue
		}
		if i == 0 || !unicode.IsOneOf(fixedNameContinueRanges, c) {
			return false
		}
	}
	return true
}

// validateFixedNames 规范化固定布局名称并校验部件内的标识唯一性
// 入参: root 部件根元素, format 文档格式
// 返回: error 错误信息
func validateFixedNames(root *xmlElement, format Format) error {
	return validateFixedNamesSeen(root, format, make(map[string]bool))
}

// validateFixedNamesSeen 共用名称校验并累积部件内标识，用于已闭合引用的增量处理
// 入参: root 当前元素树, format 文档格式, seen 本部件已经使用的标识
// 返回: error 名称或重复标识错误
func validateFixedNamesSeen(root *xmlElement, format Format, seen map[string]bool) error {
	namespace := formatNamespace(format)
	var visit func(*xmlElement, bool) error
	visit = func(node *xmlElement, resource bool) error {
		if node.Name.Space != namespace {
			return nil
		}
		switch node.Name.Local {
		case "FixedPage", "Canvas", "Path", "Glyphs", "LinkTarget":
			for i, attr := range node.Attr {
				if attr.Name.Space != "" || attr.Name.Local != "Name" {
					continue
				}
				identifier := format != FormatOpenXPS || node.Name.Local != "LinkTarget"
				value := attr.Value
				if identifier {
					value = strings.Trim(value, " \t\r\n")
				}
				if resource || !fixedNamePattern(value) || identifier && (!xmlNCName(value) || seen[value]) {
					return fmt.Errorf("%w: invalid or duplicate Name %q on %s", ErrInvalid, attr.Value, node.Name.Local)
				}
				if identifier {
					seen[value] = true
				}
				node.Attr[i].Value = value
			}
		}
		for _, child := range node.Children {
			if err := visit(child, resource || node.Name.Local == "ResourceDictionary"); err != nil {
				return err
			}
		}
		return nil
	}
	return visit(root, false)
}
