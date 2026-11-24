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
	"slices"
	"strings"
)

// opcCoreNS 等常量定义OPC核心属性与Dublin Core元数据命名空间及内容类型
const (
	opcCoreNS    = "http://schemas.openxmlformats.org/package/2006/metadata/core-properties"
	opcCoreRel   = opcRelsNS + "/metadata/core-properties"
	opcCoreType  = "application/vnd.openxmlformats-package.core-properties+xml"
	dcNamespace  = "http://purl.org/dc/elements/1.1/"
	dcTermsNS    = "http://purl.org/dc/terms/"
	xsiNamespace = "http://www.w3.org/2001/XMLSchema-instance"
)

// thumbnailRelationship 定义OPC缩略图关系类型
const thumbnailRelationship = opcRelsNS + "/metadata/thumbnail"

// corePropertyNames 保存固定写出顺序，读取时仍接受模式允许的任意属性顺序
var corePropertyNames = []xml.Name{
	{Space: opcCoreNS, Local: "category"}, {Space: opcCoreNS, Local: "contentStatus"}, {Space: opcCoreNS, Local: "contentType"},
	{Space: dcTermsNS, Local: "created"}, {Space: dcNamespace, Local: "creator"}, {Space: dcNamespace, Local: "description"},
	{Space: dcNamespace, Local: "identifier"}, {Space: opcCoreNS, Local: "keywords"}, {Space: dcNamespace, Local: "language"},
	{Space: opcCoreNS, Local: "lastModifiedBy"}, {Space: opcCoreNS, Local: "lastPrinted"}, {Space: dcTermsNS, Local: "modified"},
	{Space: opcCoreNS, Local: "revision"}, {Space: dcNamespace, Local: "subject"}, {Space: dcNamespace, Local: "title"}, {Space: opcCoreNS, Local: "version"},
}

// CoreKeyword 表示核心属性keywords中的词条，IsText为true表示直接混合文本，否则表示cp:value子元素
type CoreKeyword struct {
	Value    string
	Language *string
	IsText   bool
}

// CoreProperties 保存OPC核心属性，nil字段表示省略，非nil空字符串表示显式空值
// Languages映射允许xml:lang的元素本地名到语言标签，KeywordValues保存cp:keywords中的混合cp:value结构
// 日期保留已校验的声明精度与时区，不补入当前用户、软件名称或时间
type CoreProperties struct {
	Part           string
	Category       *string
	ContentStatus  *string
	ContentType    *string
	Created        *string
	Creator        *string
	Description    *string
	Identifier     *string
	Keywords       *string
	KeywordValues  []CoreKeyword
	Language       *string
	Languages      map[string]string
	LastModifiedBy *string
	LastPrinted    *string
	Modified       *string
	Revision       *string
	Subject        *string
	Title          *string
	Version        *string
}

// DiscardHint 保存资源释放提示，SentinelPage为首次不再需要Target的固定页面，仅作流式消费提示
type DiscardHint struct {
	Target       string
	SentinelPage string
}

// DiscardControl 保存包级资源释放提示及忽略的无效引用数量，Hints采用规范化绝对部件URI
type DiscardControl struct {
	Part    PartInfo
	Hints   []DiscardHint
	Ignored int
}

// MarshalXML 按OPC核心属性模式编码非nil字段，支持允许元素的xml:lang及cp:keywords混合cp:value结构
// 所有字段在输出前校验，不写入Part位置或自动补造身份、时间及软件信息，底层写入错误原样返回
// 入参: encoder XML编码器, start 标准库提供的起始标记，根名称按OPC规范固定
// 返回: error 属性、编码或写入错误
func (p *CoreProperties) MarshalXML(encoder *xml.Encoder, start xml.StartElement) error {
	if p == nil {
		return fmt.Errorf("%w: nil core properties", ErrInvalid)
	}
	if encoder == nil {
		return fmt.Errorf("%w: nil XML encoder", ErrInvalid)
	}
	languages, err := corePropertyEncodeLanguages(p)
	if err != nil {
		return err
	}
	keywordValues, err := corePropertyEncodeKeywords(p)
	if err != nil {
		return err
	}
	root := &xmlElement{Name: xml.Name{Space: opcCoreNS, Local: "coreProperties"}, Namespaces: map[string]string{"t": dcTermsNS}}
	for _, name := range corePropertyNames {
		isKeywords := name == (xml.Name{Space: opcCoreNS, Local: "keywords"})
		if isKeywords && len(keywordValues) != 0 {
			child := &xmlElement{Name: name, Namespaces: root.Namespaces}
			if lang, ok := languages[name.Local]; ok {
				child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Space: xmlNamespace, Local: "lang"}, Value: lang})
			}
			for _, item := range keywordValues {
				if item.IsText {
					child.Text += item.Value
					continue
				}
				sub := &xmlElement{Name: xml.Name{Space: opcCoreNS, Local: "value"}, Text: item.Value, Namespaces: root.Namespaces}
				if item.Language != nil {
					sub.Attr = []xml.Attr{{Name: xml.Name{Space: xmlNamespace, Local: "lang"}, Value: *item.Language}}
				}
				child.Children = append(child.Children, sub)
			}
			root.Children = append(root.Children, child)
			continue
		}
		field := corePropertyField(p, name)
		if field == nil || *field == nil {
			continue
		}
		value := **field
		if !xmlTextValid(value) {
			return fmt.Errorf("%w: core property %s XML text", ErrInvalid, name.Local)
		}
		child := &xmlElement{Name: name, Text: value, Namespaces: root.Namespaces}
		if name.Space == dcTermsNS {
			child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Space: xsiNamespace, Local: "type"}, Value: "t:W3CDTF"})
		}
		if lang, ok := languages[name.Local]; ok {
			child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Space: xmlNamespace, Local: "lang"}, Value: lang})
		}
		root.Children = append(root.Children, child)
	}
	if _, err := parseCorePropertiesContent(root, nil); err != nil {
		return err
	}
	start = xml.StartElement{Name: xml.Name{Local: "coreProperties"}, Attr: []xml.Attr{
		{Name: xml.Name{Local: "xmlns"}, Value: opcCoreNS},
		{Name: xml.Name{Local: "xmlns:dc"}, Value: dcNamespace},
		{Name: xml.Name{Local: "xmlns:t"}, Value: dcTermsNS},
		{Name: xml.Name{Local: "xmlns:xsi"}, Value: xsiNamespace},
	}}
	if err := encoder.EncodeToken(start); err != nil {
		return err
	}
	for _, node := range root.Children {
		name := node.Name.Local
		var attributes []xml.Attr
		if node.Name.Space == dcNamespace {
			name = "dc:" + name
		} else if node.Name.Space == dcTermsNS {
			name = "t:" + name
			attributes = append(attributes, xml.Attr{Name: xml.Name{Local: "xsi:type"}, Value: "t:W3CDTF"})
		}
		if lang, ok := node.attributeNS(xmlNamespace, "lang"); ok {
			attributes = append(attributes, xml.Attr{Name: xml.Name{Local: "xml:lang"}, Value: lang})
		}
		child := xml.StartElement{Name: xml.Name{Local: name}, Attr: attributes}
		if node.Name == (xml.Name{Space: opcCoreNS, Local: "keywords"}) && len(keywordValues) != 0 {
			if err := encoder.EncodeToken(child); err != nil {
				return err
			}
			for _, item := range keywordValues {
				if item.IsText {
					if err := encoder.EncodeToken(xml.CharData(item.Value)); err != nil {
						return err
					}
					continue
				}
				var subAttrs []xml.Attr
				if item.Language != nil {
					subAttrs = []xml.Attr{{Name: xml.Name{Local: "xml:lang"}, Value: *item.Language}}
				}
				if err := encoder.EncodeElement(item.Value, xml.StartElement{Name: xml.Name{Local: "value"}, Attr: subAttrs}); err != nil {
					return err
				}
			}
			if err := encoder.EncodeToken(child.End()); err != nil {
				return err
			}
			continue
		}
		if err := encoder.EncodeElement(node.Text, child); err != nil {
			return err
		}
	}
	return encoder.EncodeToken(start.End())
}

// corePropertyEncodeLanguages 校验核心属性语言映射的允许元素与语言标签词法
// 入参: p 核心属性
// 返回: map[string]string 规范化后的语言映射, error 元素不支持、属性省略或标签错误
func corePropertyEncodeLanguages(p *CoreProperties) (map[string]string, error) {
	if len(p.Languages) == 0 {
		return nil, nil
	}
	allowed := make(map[string]xml.Name, 7)
	for _, name := range corePropertyNames {
		if corePropertyAllowsLanguage(name) {
			allowed[name.Local] = name
		}
	}
	result := make(map[string]string, len(p.Languages))
	for local, raw := range p.Languages {
		name, ok := allowed[local]
		if !ok {
			return nil, fmt.Errorf("%w: xml:lang not allowed on core property %q", ErrInvalid, local)
		}
		present := false
		if local == "keywords" {
			present = p.Keywords != nil || len(p.KeywordValues) != 0
		} else if field := corePropertyField(p, name); field != nil && *field != nil {
			present = true
		}
		if !present {
			return nil, fmt.Errorf("%w: xml:lang specified for omitted core property %q", ErrInvalid, local)
		}
		lang, err := corePropertyLanguage(raw)
		if err != nil {
			return nil, err
		}
		result[local] = lang
	}
	return result, nil
}

// corePropertyEncodeKeywords 校验cp:keywords混合词条并核对与Keywords聚合文本的一致性
// 入参: p 核心属性
// 返回: []CoreKeyword 规范化词条副本, error 文本、语言或聚合冲突错误
func corePropertyEncodeKeywords(p *CoreProperties) ([]CoreKeyword, error) {
	if len(p.KeywordValues) == 0 {
		return nil, nil
	}
	result := make([]CoreKeyword, len(p.KeywordValues))
	var combined strings.Builder
	for index, item := range p.KeywordValues {
		if !xmlTextValid(item.Value) {
			return nil, fmt.Errorf("%w: core property keywords XML text", ErrInvalid)
		}
		if item.IsText {
			if item.Language != nil {
				return nil, fmt.Errorf("%w: core property keywords text fragment cannot carry xml:lang", ErrInvalid)
			}
			result[index] = CoreKeyword{Value: item.Value, IsText: true}
		} else {
			entry := CoreKeyword{Value: item.Value}
			if item.Language != nil {
				lang, err := corePropertyLanguage(*item.Language)
				if err != nil {
					return nil, err
				}
				entry.Language = &lang
			}
			result[index] = entry
		}
		combined.WriteString(item.Value)
	}
	if p.Keywords != nil && *p.Keywords != combined.String() {
		return nil, fmt.Errorf("%w: core property keywords text conflicts with KeywordValues", ErrInvalid)
	}
	return result, nil
}

// SetCoreProperties 编码并写入包级OPC核心属性，复用已有或分配/docProps/core.xml并保留其他根关系
// 入参: props 核心属性数据，nil字段表示省略
// 返回: error 属性校验、编辑许可、关系或预算错误，失败时不改变包
func (p *Package) SetCoreProperties(props CoreProperties) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	var output bytes.Buffer
	encoder := xml.NewEncoder(&output)
	if err := props.MarshalXML(encoder, xml.StartElement{}); err != nil {
		return err
	}
	if err := encoder.Flush(); err != nil {
		return err
	}
	data := output.Bytes()
	if int64(len(data)) > min(p.limits.MaxPartBytes, p.limits.MaxMetadataBytes) {
		return fmt.Errorf("%w: core properties byte budget", ErrLimit)
	}
	relations := slices.Clone(p.relations["/"])
	part, id, pattern := "", "", ""
	retained := make([]Relationship, 0, len(relations)+1)
	for _, relation := range relations {
		if relation.Type != opcCoreRel {
			retained = append(retained, relation)
			continue
		}
		if part != "" {
			return fmt.Errorf("%w: multiple package core properties relationships", ErrInvalid)
		}
		if relation.TargetMode != "" && relation.TargetMode != TargetModeInternal {
			return fmt.Errorf("%w: external package core properties", ErrInvalid)
		}
		target, err := resolvePart("/", relation.Target)
		if err != nil {
			return err
		}
		if p.managed(target) || opcRelationshipName(target) {
			return fmt.Errorf("%w: managed package part", ErrInvalid)
		}
		part, id = target, relation.ID
	}
	if part == "" {
		part = "/docProps/core.xml"
		if err := p.available(part); err != nil {
			pattern = "/docProps/core%d.xml"
			part, err = p.newName(pattern, nil)
			if err != nil {
				return err
			}
		}
	}
	if id == "" {
		id = createdRelationshipIDs(append(slices.Clone(relations), p.originalRels["/"]...))()
	}
	retained = append(retained, Relationship{ID: id, Type: opcCoreRel, Target: part, TargetMode: TargetModeInternal})
	q := p.signingCopy()
	if err := q.editable(part); err != nil {
		return err
	}
	if err := q.store(part, opcCoreType, data); err != nil {
		return err
	}
	if err := q.setRelationships("/", retained); err != nil {
		return err
	}
	q.commitName(pattern, part)
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.dirty, p.dirtyRels = q.names, q.parents, q.allocated, q.dirty, q.dirtyRels
	return nil
}

// CoreProperties 读取包级关系指向的核心属性，未关联时返回nil，不访问外部Schema或属性扩展
// 入参: ctx 取消Context，nil采用Background
// 返回: *CoreProperties 独立属性数据, error 关系、模式、日期、取消或资源错误
func (r *Reader) CoreProperties(ctx context.Context) (*CoreProperties, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, "/")
	if err != nil {
		return nil, &PartError{Part: "/", Err: err}
	}
	part := ""
	for _, relation := range relations {
		if relation.Type != opcCoreRel {
			continue
		}
		if part != "" {
			return nil, fmt.Errorf("%w: multiple package core properties relationships", ErrInvalid)
		}
		if relation.TargetMode != TargetModeInternal {
			return nil, fmt.Errorf("%w: external package core properties", ErrInvalid)
		}
		part, err = resolvePart("/", relation.Target)
		if err != nil {
			return nil, err
		}
	}
	if part == "" {
		return nil, nil
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if !strings.EqualFold(media, opcCoreType) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: core properties content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, strings.ToLower(part), min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes))
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	root, content, err := decodeXMLContent(data, r.limits, ctx)
	if err == nil {
		var result *CoreProperties
		result, err = parseCorePropertiesContent(root, content)
		if err == nil {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			result.Part = part
			return result, nil
		}
	}
	return nil, &PartError{Part: part, Err: err}
}

// parseCorePropertiesContent 按OPC模式解析核心属性及cp:keywords混合内容顺序，保留允许元素的xml:lang
// 入参: root 部件根节点, content 可选有序内容索引
// 返回: *CoreProperties 独立核心属性, error 根节点、属性、语言、重复或日期错误
func parseCorePropertiesContent(root *xmlElement, content *xmlContentReader) (*CoreProperties, error) {
	if root == nil || root.Name != (xml.Name{Space: opcCoreNS, Local: "coreProperties"}) || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: core properties root or text", ErrInvalid)
	}
	if _, err := corePropertyAttributes(root, false, false); err != nil {
		return nil, err
	}
	result := &CoreProperties{}
	for _, child := range root.Children {
		field := corePropertyField(result, child.Name)
		isKeywords := child.Name == (xml.Name{Space: opcCoreNS, Local: "keywords"})
		if field == nil || *field != nil || !isKeywords && len(child.Children) != 0 {
			return nil, fmt.Errorf("%w: unknown, repeated or nested core property {%s}%s", ErrInvalid, child.Name.Space, child.Name.Local)
		}
		date := child.Name.Space == dcTermsNS && (child.Name.Local == "created" || child.Name.Local == "modified")
		lang, err := corePropertyAttributes(child, date, corePropertyAllowsLanguage(child.Name))
		if err != nil {
			return nil, err
		}
		if lang != nil {
			if result.Languages == nil {
				result.Languages = make(map[string]string)
			}
			result.Languages[child.Name.Local] = *lang
		}
		if isKeywords && len(child.Children) != 0 {
			combined, values, err := parseCoreKeywords(child, content)
			if err != nil {
				return nil, err
			}
			*field = &combined
			result.KeywordValues = values
			continue
		}
		value := child.Text
		printed := child.Name == (xml.Name{Space: opcCoreNS, Local: "lastPrinted"})
		if date || printed {
			value = strings.Trim(value, " \t\r\n")
			if !xmlDateValue(value, printed) {
				return nil, fmt.Errorf("%w: core property %s date declaration", ErrInvalid, child.Name.Local)
			}
		}
		*field = &value
	}
	return result, nil
}

// parseCoreKeywords 解析cp:keywords内的混合文本及cp:value子元素，并保持文档顺序
// 入参: node keywords元素, content 可选有序内容索引
// 返回: string 聚合关键词文本, []CoreKeyword 有序混合条目, error 非法子元素或属性错误
func parseCoreKeywords(node *xmlElement, content *xmlContentReader) (string, []CoreKeyword, error) {
	byNode := make(map[*xmlElement]CoreKeyword, len(node.Children))
	for _, child := range node.Children {
		if child.Name != (xml.Name{Space: opcCoreNS, Local: "value"}) || len(child.Children) != 0 {
			return "", nil, fmt.Errorf("%w: invalid cp:keywords child {%s}%s", ErrInvalid, child.Name.Space, child.Name.Local)
		}
		lang, err := corePropertyAttributes(child, false, true)
		if err != nil {
			return "", nil, err
		}
		byNode[child] = CoreKeyword{Value: child.Text, Language: lang}
	}
	var combined strings.Builder
	var values []CoreKeyword
	appendText := func(text string) {
		if text == "" {
			return
		}
		combined.WriteString(text)
		if len(values) != 0 && values[len(values)-1].IsText {
			values[len(values)-1].Value += text
			return
		}
		values = append(values, CoreKeyword{Value: text, IsText: true})
	}
	if content != nil {
		if items, ok := content.nodes[node]; ok {
			for _, item := range items {
				if item.element != nil {
					entry := byNode[item.element]
					combined.WriteString(entry.Value)
					values = append(values, entry)
				} else if data, ok := item.token.(xml.CharData); ok {
					appendText(string(data))
				}
			}
			return combined.String(), values, nil
		}
	}
	appendText(node.Text)
	for _, child := range node.Children {
		entry := byNode[child]
		combined.WriteString(entry.Value)
		values = append(values, entry)
	}
	return combined.String(), values, nil
}

// corePropertyAllowsLanguage 判断核心属性元素是否允许携带xml:lang属性
// 入参: name 元素展开名称
// 返回: bool 是否允许xml:lang
func corePropertyAllowsLanguage(name xml.Name) bool {
	return name.Space == dcNamespace || name == (xml.Name{Space: opcCoreNS, Local: "keywords"}) || name == (xml.Name{Space: opcCoreNS, Local: "value"})
}

// corePropertyLanguage 校验核心属性xml:lang标签词法，允许空字符串以清除继承语言
// 入参: value 语言属性值
// 返回: string 规范化语言标签, error 非法文本或语言标签错误
func corePropertyLanguage(value string) (string, error) {
	if !xmlTextValid(value) {
		return "", fmt.Errorf("%w: core property xml:lang XML text", ErrInvalid)
	}
	if value == "" {
		return "", nil
	}
	trimmed := strings.Trim(value, " \t\r\n")
	if !fixedLanguageTag(trimmed) {
		return "", fmt.Errorf("%w: invalid core property xml:lang %q", ErrInvalid, value)
	}
	return trimmed, nil
}

// corePropertyField 将扩展名称映射到对应字段，不合并不同命名空间中的同名属性
// 入参: properties 目标属性, name 元素扩展名称
// 返回: **string 字段位置，非核心属性返回nil
func corePropertyField(properties *CoreProperties, name xml.Name) **string {
	switch name.Space {
	case opcCoreNS:
		switch name.Local {
		case "category":
			return &properties.Category
		case "contentStatus":
			return &properties.ContentStatus
		case "contentType":
			return &properties.ContentType
		case "keywords":
			return &properties.Keywords
		case "lastModifiedBy":
			return &properties.LastModifiedBy
		case "lastPrinted":
			return &properties.LastPrinted
		case "revision":
			return &properties.Revision
		case "version":
			return &properties.Version
		}
	case dcNamespace:
		switch name.Local {
		case "creator":
			return &properties.Creator
		case "description":
			return &properties.Description
		case "identifier":
			return &properties.Identifier
		case "language":
			return &properties.Language
		case "subject":
			return &properties.Subject
		case "title":
			return &properties.Title
		}
	case dcTermsNS:
		switch name.Local {
		case "created":
			return &properties.Created
		case "modified":
			return &properties.Modified
		}
	}
	return nil
}

// corePropertyAttributes 校验OPC核心属性允许的属性集合、可选xml:lang及日期字段必需的QName类型
// 入参: node 属性节点, date 是否为创建或修改日期, allowLanguage 是否允许xml:lang
// 返回: *string 可选语言标签, error 属性、语言或类型声明错误
func corePropertyAttributes(node *xmlElement, date, allowLanguage bool) (*string, error) {
	typed := false
	var language *string
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if attribute.Name == (xml.Name{Space: xmlNamespace, Local: "lang"}) {
			if !allowLanguage {
				return nil, fmt.Errorf("%w: xml:lang not allowed on core property %s", ErrInvalid, node.Name.Local)
			}
			lang, err := corePropertyLanguage(attribute.Value)
			if err != nil {
				return nil, err
			}
			language = &lang
			continue
		}
		if attribute.Name.Space != xsiNamespace {
			return nil, fmt.Errorf("%w: core property attribute {%s}%s", ErrInvalid, attribute.Name.Space, attribute.Name.Local)
		}
		switch attribute.Name.Local {
		case "type":
			if !date || !coreDateType(node, attribute.Value) {
				return nil, fmt.Errorf("%w: core property date type", ErrInvalid)
			}
			typed = true
		case "nil":
			return nil, fmt.Errorf("%w: xsi:nil on a non-nillable core property", ErrInvalid)
		case "schemaLocation", "noNamespaceSchemaLocation":
		default:
			return nil, fmt.Errorf("%w: core property schema attribute %s", ErrInvalid, attribute.Name.Local)
		}
	}
	if date && !typed {
		return nil, fmt.Errorf("%w: missing core property date type", ErrInvalid)
	}
	return language, nil
}

// coreDateType 按节点的命名空间作用域解析日期类型，不固定dcterms前缀名称
// 入参: node 日期节点, value QName类型声明
// 返回: bool 是否解析为Dublin Core的W3CDTF
func coreDateType(node *xmlElement, value string) bool {
	value = strings.Trim(value, " \t\r\n")
	prefix, local := "", value
	if colon := strings.IndexByte(value, ':'); colon >= 0 {
		prefix, local = value[:colon], value[colon+1:]
		if !xmlNCName(prefix) {
			return false
		}
	}
	return xmlNCName(local) && local == "W3CDTF" && node.Namespaces[prefix] == dcTermsNS
}

// DiscardControl 读取唯一包级释放提示关联，不执行资源释放或外部访问
// 结构错误单独报告，不影响调用方继续随机访问页面；包外及无效部件引用按规则忽略
// 入参: ctx 取消Context，nil采用Background
// 返回: *DiscardControl 独立提示，未关联时为nil, error 关联、结构、类型、资源、关闭或取消错误
func (r *Reader) DiscardControl(ctx context.Context) (*DiscardControl, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	relations, err := r.pkg.relationshipsContext(ctx, "/")
	if err != nil {
		return nil, err
	}
	part, err := discardControlTarget(relations, r.format)
	if err != nil || part == "" {
		return nil, err
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, err
	}
	if !strings.EqualFold(media, fixedContentType("discard-control")) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: discard control content type", ErrInvalid)}
	}
	data, err := r.pkg.readItemsContext(ctx, strings.ToLower(part), min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes, r.limits.MaxPackageBytes))
	if err != nil {
		return nil, err
	}
	result, err := readDiscardControl(data, part, r.format, r.limits, ctx)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	result.Part = PartInfo{Name: r.pkg.names[strings.ToLower(part)], ContentType: media, Size: int64(len(data))}
	return result, nil
}

// discardControlTarget 校验释放提示的单一包级关系，不把同目标的重复关系视为合法合并
// 入参: relations 包根关系, format 包格式
// 返回: string 规范化部件名，未关联为空, error 数量、模式或目标错误
func discardControlTarget(relations []Relationship, format Format) (string, error) {
	kind := formatNamespace(format) + "/discard-control"
	part := ""
	for _, relation := range relations {
		if relation.Type != kind {
			continue
		}
		if part != "" {
			return "", fmt.Errorf("%w: multiple discard control relationships", ErrInvalid)
		}
		if relation.TargetMode != "" && relation.TargetMode != TargetModeInternal {
			return "", fmt.Errorf("%w: external discard control relationship", ErrInvalid)
		}
		var err error
		part, err = resolvePart("/", relation.Target)
		if err != nil {
			return "", err
		}
	}
	return part, nil
}

// readDiscardControl 校验释放提示结构，以包根解析引用，保留顺序、重复提示及空列表
// 入参: data 原始XML, part 提示部件名，用于自引用检查, format 格式, limits 包上限, ctx 取消Context
// 返回: *DiscardControl 独立结果, error XML、结构、自引用或取消错误
func readDiscardControl(data []byte, part string, format Format, limits Limits, ctx context.Context) (*DiscardControl, error) {
	if formatNamespace(format) == "" {
		return nil, fmt.Errorf("%w: discard control format", ErrInvalid)
	}
	if int64(len(data)) > min(limits.MaxMetadataBytes, limits.MaxPartBytes, limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: discard control byte budget", ErrLimit)
	}
	root, err := decodeXMLVisit(data, limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err != nil {
		return nil, err
	}
	return processDiscardControl(root, part, format, ctx)
}

// processDiscardControl 按格式预处理释放提示兼容标记并校验结构，OpenXPS启用MCE，XPS 1.0按严格模式校验
// 入参: root 原始根节点, part 提示部件名, format 格式, ctx 取消Context
// 返回: *DiscardControl 独立提示, error 兼容性、结构、自引用或取消错误
func processDiscardControl(root *xmlElement, part string, format Format, ctx context.Context) (*DiscardControl, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	namespace := formatNamespace(format) + "/discard-control"
	if format == FormatOpenXPS {
		var err error
		root, err = preprocessXMLContext(root, []string{namespace}, ctx)
		if err != nil {
			return nil, err
		}
	}
	result, err := parseDiscardControl(root, part, namespace, func() error { return checkContext(ctx) })
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// parseDiscardControl 解析两套正式模式共有的结构及包根引用语义，不解释未知扩展
// 入参: root 已完成相应格式兼容处理的根节点, part 提示部件名, namespace 提示命名空间, step 逐提示取消或预算检查
// 返回: *DiscardControl 已解析提示, error 结构、自引用或检查错误
func parseDiscardControl(root *xmlElement, part, namespace string, step func() error) (*DiscardControl, error) {
	if root.Name != (xml.Name{Space: namespace, Local: "DiscardControl"}) || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: discard control root", ErrInvalid)
	}
	for _, a := range root.Attr {
		if a.Name.Space != xmlnsNamespace && a.Name != (xml.Name{Local: "xmlns"}) {
			return nil, fmt.Errorf("%w: discard control attribute", ErrInvalid)
		}
	}
	result := &DiscardControl{}
	for _, node := range root.Children {
		if err := step(); err != nil {
			return nil, err
		}
		if node.Name != (xml.Name{Space: namespace, Local: "Discard"}) || len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return nil, fmt.Errorf("%w: discard hint element", ErrInvalid)
		}
		for _, a := range node.Attr {
			if a.Name.Space == xmlnsNamespace || a.Name == (xml.Name{Local: "xmlns"}) {
				continue
			}
			if a.Name.Space != "" || a.Name.Local != "Target" && a.Name.Local != "SentinelPage" {
				return nil, fmt.Errorf("%w: discard hint attribute", ErrInvalid)
			}
		}
		target, hasTarget := node.attribute("Target")
		sentinel, hasSentinel := node.attribute("SentinelPage")
		if !hasTarget || !hasSentinel {
			return nil, fmt.Errorf("%w: missing discard hint reference", ErrInvalid)
		}
		target, targetErr := resolvePart("/", structureURI(target))
		sentinel, sentinelErr := resolvePart("/", structureURI(sentinel))
		if targetErr != nil || sentinelErr != nil {
			result.Ignored++
			continue
		}
		if part != "" && (strings.EqualFold(part, target) || strings.EqualFold(part, sentinel)) {
			return nil, fmt.Errorf("%w: discard control references itself", ErrInvalid)
		}
		result.Hints = append(result.Hints, DiscardHint{Target: target, SentinelPage: sentinel})
	}
	return result, nil
}

// validateDiscardLifetime 校验图形资源在哨兵页及后续页面不再被引用，无法证明安全时返回ErrUnsupported
// 入参: control 已解析提示, ctx 取消Context
// 返回: error 过早释放、未知引用语义、预算或取消错误
func (r *Reader) validateDiscardLifetime(control *DiscardControl, ctx context.Context) error {
	budget := resourceMergeBudget{bytes: r.limits.MaxPackageBytes, work: r.limits.MaxXMLNodes, seen: make(map[string]bool), context: ctx}
	graph, err := r.resourceReferenceGraph(&budget)
	if err != nil {
		return err
	}
	last := make(map[string]int)
	uncertain := -1
	pages := make(map[string]int)
	for index, page := range r.pages {
		pages[strings.ToLower(page.Part)] = index
		seen, err := graph.reachableFrom(map[string]bool{strings.ToLower(page.Part): true}, false)
		if err != nil {
			return err
		}
		for key := range seen {
			last[key] = index
			if graph.models[key] {
				uncertain = index
			}
		}
	}
	for _, hint := range control.Hints {
		if err := budget.charge(1); err != nil {
			return err
		}
		media, err := r.pkg.contentType(hint.Target)
		if err != nil {
			return err
		}
		if !graphicResourceMedia(media) && !graph.models[strings.ToLower(hint.Target)] {
			continue
		}
		sentinel, exists := pages[strings.ToLower(hint.SentinelPage)]
		if !exists {
			return fmt.Errorf("%w: discard sentinel is not a fixed page", ErrInvalid)
		}
		if index, used := last[strings.ToLower(hint.Target)]; used && index >= sentinel {
			return &PartError{Part: hint.Target, Err: fmt.Errorf("%w: discard precedes last resource use", ErrInvalid)}
		}
		if uncertain >= sentinel {
			return &PartError{Part: hint.Target, Err: fmt.Errorf("%w: resource lifetime depends on opaque X3D content", ErrUnsupported)}
		}
	}
	return checkContext(ctx)
}

// EncodeDiscardControl 输出独立UTF-8释放提示，按包根规范化两项URI，允许空提示列表
// 模型及预算错误不写入输出，底层写入错误可能留下部分字节，不关闭调用方输出流
// 入参: ctx 取消Context，nil采用Background, output 输出流, hints 提示顺序, options 方言及预算，nil采用默认值
// 返回: int64 已写字节数, error 模型、资源、取消或写入错误
func EncodeDiscardControl(ctx context.Context, output io.Writer, hints []DiscardHint, options *EncodeOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if output == nil {
		return 0, fmt.Errorf("%w: missing discard control output", ErrInvalid)
	}
	configuration := DefaultEncodeOptions()
	if options != nil {
		configuration = *options
		if configuration.Format == FormatUnknown {
			configuration.Format = FormatOpenXPS
		}
		configuration.Limits = mergeLimits(DefaultLimits(), configuration.Limits)
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return 0, err
	}
	namespace := formatNamespace(configuration.Format)
	if namespace == "" {
		return 0, fmt.Errorf("%w: discard control format", ErrInvalid)
	}
	if configuration.Part != "" {
		part, err := opcPartName(configuration.Part)
		if err != nil {
			return 0, err
		}
		configuration.Part = part
	}
	limits := configuration.Limits
	limits.MaxPartBytes = min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes)
	p := pageEncoder{ns: namespace + "/discard-control", limits: limits, ctx: ctx, scope: map[string]string{"": namespace + "/discard-control", "xml": xmlNamespace}}
	root, err := p.node("DiscardControl", 1)
	if err != nil {
		return 0, err
	}
	for _, hint := range hints {
		if err := checkContext(p.ctx); err != nil {
			return 0, err
		}
		target, err := resolvePart("/", structureURI(hint.Target))
		if err != nil {
			return 0, err
		}
		sentinel, err := resolvePart("/", structureURI(hint.SentinelPage))
		if err != nil {
			return 0, err
		}
		node, err := p.node("Discard", 2)
		if err != nil {
			return 0, err
		}
		if err := p.attr(node, "Target", target); err != nil {
			return 0, err
		}
		if err := p.attr(node, "SentinelPage", sentinel); err != nil {
			return 0, err
		}
		root.Children = append(root.Children, node)
	}
	data, err := createdMarkup(root, limits, p.ctx)
	if err != nil {
		return 0, err
	}
	control, err := readDiscardControl(data, configuration.Part, configuration.Format, limits, p.ctx)
	if err != nil {
		return 0, err
	}
	if control.Ignored != 0 {
		return 0, fmt.Errorf("%w: invalid produced discard reference", ErrInvalid)
	}
	counted := packageOutput{writer: output, context: p.ctx, limit: limits.MaxPartBytes}
	if _, err := counted.Write(data); err != nil {
		return counted.count, err
	}
	return counted.count, nil
}

// ThumbnailParts 枚举包级或页面缩略图并按部件身份去重，不读取图像内容
// 空来源或斜线表示包根，其他非页面部件关联的缩略图予以忽略
// 入参: ctx 取消Context，nil采用Background, source 来源部件
// 返回: []PartInfo 独立目标索引，未关联为空, error 来源、关联、类型、数量、资源或关闭错误
func (r *Reader) ThumbnailParts(ctx context.Context, source string) ([]PartInfo, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.thumbnailParts(source, ctx)
}

// Thumbnail 读取单一缩略图并保留原图数据，沿用Image的解码与资源上限
// 包根存在多个不同缩略图时返回ErrUnsupported，调用方可先枚举目标再使用Image明确选择
// 入参: ctx 取消Context，nil采用Background, source 包根或页面, options 图像参数，nil采用默认值
// 返回: *ImageResource 独立图像，未关联为nil, error 关联、选择、解码、资源或关闭错误
func (r *Reader) Thumbnail(ctx context.Context, source string, options *ImageOptions) (*ImageResource, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	parts, err := r.thumbnailParts(source, ctx)
	if err != nil || len(parts) == 0 {
		return nil, err
	}
	if len(parts) > 1 {
		return nil, fmt.Errorf("%w: multiple package thumbnails require explicit selection", ErrUnsupported)
	}
	return r.readImage(ctx, parts[0].Name, options)
}

// thumbnailParts 在读锁内校验缩略图来源及目标，不通过文件扩展名推断媒体类型
// 入参: source 包根或来源部件, ctx 取消Context
// 返回: []PartInfo 按部件名排序的不同目标, error 元数据或取消错误
func (r *Reader) thumbnailParts(source string, ctx context.Context) ([]PartInfo, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if source == "" {
		source = "/"
	}
	page := false
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return nil, err
		}
		source = canonical
		if _, exists := r.pkg.parts[strings.ToLower(source)]; !exists {
			return nil, fmt.Errorf("%w: missing thumbnail source", ErrInvalid)
		}
		for _, value := range r.pages {
			if strings.EqualFold(value.Part, source) {
				page = true
				break
			}
		}
		if !page {
			return nil, nil
		}
	}
	relations, err := r.pkg.relationshipsContext(ctx, source)
	if err != nil {
		return nil, err
	}
	targets, err := thumbnailTargets(source, relations, page)
	if err != nil {
		return nil, err
	}
	var result []PartInfo
	for _, part := range targets {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		media, err := r.pkg.contentType(part)
		if err != nil {
			return nil, err
		}
		if !thumbnailMedia(media) {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: thumbnail requires JPEG or PNG", ErrInvalid)}
		}
		size, err := r.pkg.partSize(strings.ToLower(part))
		if err != nil {
			return nil, err
		}
		result = append(result, PartInfo{Name: r.pkg.names[strings.ToLower(part)], ContentType: media, Size: int64(size)})
	}
	slices.SortFunc(result, func(a, b PartInfo) int { return strings.Compare(strings.ToLower(a.Name), strings.ToLower(b.Name)) })
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// thumbnailTargets 校验内部缩略图关系，页面只允许一个不同目标，包根不虚设额外数量限制
// 入参: source 来源部件, relations 原始关系, page 是否为固定页面
// 返回: []string 去重目标，保留首次声明顺序, error 模式、URI或页面数量错误
func thumbnailTargets(source string, relations []Relationship, page bool) ([]string, error) {
	seen := make(map[string]bool)
	var result []string
	for _, relation := range relations {
		if relation.Type != thumbnailRelationship {
			continue
		}
		if relation.TargetMode != "" && relation.TargetMode != TargetModeInternal {
			return nil, fmt.Errorf("%w: external thumbnail relationship", ErrInvalid)
		}
		part, err := resolvePart(source, relation.Target)
		if err != nil {
			return nil, err
		}
		key := strings.ToLower(part)
		if seen[key] {
			continue
		}
		seen[key] = true
		result = append(result, part)
		if page && len(result) > 1 {
			return nil, fmt.Errorf("%w: multiple page thumbnail parts", ErrInvalid)
		}
	}
	return result, nil
}

// thumbnailMedia 判断内容类型是否为允许的JPEG或PNG缩略图格式
// 入参: media 无参数内容类型
// 返回: bool 是否为JPEG或PNG
func thumbnailMedia(media string) bool {
	return strings.EqualFold(media, "image/jpeg") || strings.EqualFold(media, "image/png")
}

// validateThumbnailLinks 校验包快照的缩略图关联并对新增或修改的缩略图图像执行解码检查
// 入参: r 当前快照, ctx 取消Context
// 返回: error 关联、图像、资源或取消错误
func (p *Package) validateThumbnailLinks(r *Reader, ctx context.Context) error {
	sources := []string{"/"}
	for _, page := range r.pages {
		sources = append(sources, page.Part)
	}
	checked := make(map[string]bool)
	remaining := p.limits.MaxPackageBytes
	pixels := p.maxImagePixels
	for _, source := range sources {
		parts, err := r.thumbnailParts(source, ctx)
		if err != nil {
			return err
		}
		for _, part := range parts {
			if err := checkContext(ctx); err != nil {
				return err
			}
			key := strings.ToLower(part.Name)
			changed := p.original == nil || p.dirty[key] || p.dirtyRels[strings.ToLower(source)]
			if checked[key] || !changed {
				continue
			}
			data, err := r.pkg.readItemsContext(ctx, key, min(remaining, p.limits.MaxPartBytes))
			if err != nil {
				return err
			}
			image, err := decodeRasterImageContext(ctx, data, part.ContentType, pixels)
			if err != nil {
				return &PartError{Part: part.Name, Err: err}
			}
			units := image.pixelUnits()
			if units > pixels {
				return fmt.Errorf("%w: thumbnail decode capacity", ErrLimit)
			}
			pixels -= units
			remaining -= int64(len(data))
			checked[key] = true
		}
	}
	return checkContext(ctx)
}
