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
	"bufio"
	"bytes"
	"cmp"
	"context"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"io"
	"maps"
	"math"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"unicode/utf16"
	"unicode/utf8"
)

// xpsNamespace 等常量定义XPS、OpenXPS、XML及标记兼容性命名空间
const (
	xpsNamespace     = "http://schemas.microsoft.com/xps/2005/06"
	openXPSNamespace = "http://schemas.openxps.org/oxps/v1.0"
	xmlNamespace     = "http://www.w3.org/XML/1998/namespace"
	xmlnsNamespace   = "http://www.w3.org/2000/xmlns/"
	mcNamespace      = "http://schemas.openxmlformats.org/markup-compatibility/2006"
)

// xmlDateTimePattern 匹配XML Schema dateTime词法结构，数值范围由xmlDateValue校验
var xmlDateTimePattern = regexp.MustCompile(`^-?([0-9]{4,})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})(?:\.([0-9]+))?(Z|[+-][0-9]{2}:[0-9]{2})?$`)

// xmlW3CDTFPattern 严格匹配W3CDTF六种标准日期时间粒度，不含负年份或无时间时区
var xmlW3CDTFPattern = regexp.MustCompile(`^([0-9]{4})(?:-([0-9]{2})(?:-([0-9]{2})(?:T([0-9]{2}):([0-9]{2})(?::([0-9]{2})(?:\.([0-9]+))?)?(Z|[+-][0-9]{2}:[0-9]{2}))?)?)?$`)

// canonicalLineFeeds 规范化注释和处理指令中的字面换行，不解释实体或字符引用
var canonicalLineFeeds = strings.NewReplacer("\r\n", "\n", "\r", "\n")

// xmlElement 保存已解析的元素、属性及命名空间作用域
type xmlElement struct {
	Name                xml.Name
	Attr                []xml.Attr
	Children            []*xmlElement
	Text                string
	Namespaces          map[string]string
	PreservedElements   []*xmlElement
	PreservedAttributes []xml.Attr
	namespaceOwner      *xmlElement
	rawName             xml.Name
	text                []byte
}

// xmlTokenVisitor 接收已校验的XML词元及所属元素，起始词元保留原始前缀和规范化后的属性值
type xmlTokenVisitor func(xml.Token, *xmlElement) error

// xmlTokenSpanVisitor 接收已校验词元及其UTF-8原始数据范围，用于保留原标记的定点修改
type xmlTokenSpanVisitor func(xml.Token, *xmlElement, int64, int64) error

// xmlContent 保存单个子元素或非元素词元，不以聚合文本替代混合内容顺序
type xmlContent struct {
	element *xmlElement
	token   xml.Token
}

// xmlContentReader 按需保存XML元素内容顺序，不增加普通XML模型的字段
type xmlContentReader struct {
	context context.Context
	limit   int
	count   int
	nodes   map[*xmlElement][]xmlContent
	stack   []*xmlElement
}

// xmlAttributeRange 保存已校验起始标签中属性值的UTF-8半开范围，不含引号
type xmlAttributeRange struct {
	start int
	end   int
}

// xmlValueReplacement 保存单个属性值替换，不改写属性名、引号或其他标记
type xmlValueReplacement struct {
	start int
	end   int
	data  []byte
}

// xmlAttributeRewrite 为指定节点属性提供新语义值，changed为false时保留原始字节
type xmlAttributeRewrite func(*xmlElement, xml.Attr) (value string, changed bool, err error)

// xmlRewriteBuffer 限制属性转义缓冲区容量，并在写入时响应取消
type xmlRewriteBuffer struct {
	bytes.Buffer
	maximum int64
	context context.Context
}

// xmlTokenInput 为XML校验器提供当前词元的UTF-8原文视图，流式输入仅保留预读未提交字节
type xmlTokenInput struct {
	reader io.ByteReader
	data   []byte
	buffer []byte
	base   int64
}

// xmlUTF8Stream 按字符校验并转换UTF编码，保留跨读取的代理对及UTF-8字节
type xmlUTF8Stream struct {
	reader   *bufio.Reader
	context  context.Context
	encoding string
	pending  [4]byte
	position int
	count    int
	limit    int64
	consumed int64
}

// compatibilityScope 保存按命名空间URI解析的可忽略、内容处理及保留规则
type compatibilityScope struct {
	ignorable          map[string]bool
	process            map[xml.Name]bool
	preserveElements   map[xml.Name]bool
	preserveAttributes map[xml.Name]bool
}

// compatibilityProcessor 保存调用方声明理解的命名空间集合
type compatibilityProcessor struct {
	understood         map[string]bool
	content            map[*xmlElement][]xmlContent
	includePreserved   bool
	ignorePreservation bool
	context            context.Context
	namespaceCopies    map[*xmlElement]map[string]string
}

// compatibilityFragment 保存移除兼容性包装后得到的元素、保留扩展及聚合文本
type compatibilityFragment struct {
	elements  []*xmlElement
	preserved []*xmlElement
	text      string
	ordered   []xmlContent
}

// compatibilitySelection 保存候选分支的结构状态及首个可用分支
type compatibilitySelection struct {
	choices   int
	fallback  bool
	selected  *xmlElement
	scope     compatibilityScope
	preserved []*xmlElement
}

// canonicalXMLOptions 指定C14N1.0、Exclusive C14N1.0或C14N1.1处理方式，selectElement仅选择一个完整子树
type canonicalXMLOptions struct {
	limits        Limits
	maxBytes      int64
	comments      bool
	exclusive     bool
	version11     bool
	inclusive     map[string]bool
	context       context.Context
	selectElement func(*xmlElement, []xml.Name) bool
}

// canonicalAttribute 保存原始QName、展开名称及规范化后的属性值
type canonicalAttribute struct {
	raw   xml.Name
	name  xml.Name
	value string
}

// canonicalWriter 保存规范化输出的命名空间、祖先及选定子树状态
type canonicalWriter struct {
	options       canonicalXMLOptions
	output        packageOutput
	ancestors     []*xmlElement
	path          []xml.Name
	rendered      []map[string]string
	selected      bool
	selectedDepth int
	rootPassed    bool
	nodes         int
}

// decodeXML 解析UTF编码的XML并限制深度与节点数量
// 入参: data XML数据, limits 资源上限
// 返回: *xmlElement 根元素, error 错误信息
func decodeXML(data []byte, limits Limits) (*xmlElement, error) {
	return decodeXMLVisit(data, limits, nil)
}

// decodeXMLVisit 共用XML校验及命名空间处理，按文档顺序访问词元及解析中的元素
// 入参: data XML数据, limits 资源上限, visit 可选词元访问函数
// 返回: *xmlElement 根元素, error 解析、校验或访问错误
func decodeXMLVisit(data []byte, limits Limits, visit xmlTokenVisitor) (*xmlElement, error) {
	if visit == nil {
		return decodeXMLVisitSpan(data, limits, nil)
	}
	return decodeXMLVisitSpan(data, limits, func(token xml.Token, node *xmlElement, _, _ int64) error { return visit(token, node) })
}

// decodeXMLVisitSpan 沿用XML校验及命名空间处理，同时提供词元在解码后原始UTF-8中的范围
// 入参: data XML数据, limits 资源上限, visit 可选范围访问函数
// 返回: *xmlElement 根元素, error XML、资源或访问错误
func decodeXMLVisitSpan(data []byte, limits Limits, visit xmlTokenSpanVisitor) (*xmlElement, error) {
	decoded, encoding, err := xmlDecodedUTF8(data)
	if err != nil {
		return nil, err
	}
	return parseXMLTokens(&xmlTokenInput{reader: bytes.NewReader(decoded), data: decoded}, encoding, limits, visit, true)
}

// xmlDecodedUTF8 校验输入编码与字节序标记并转换为合法XML字符的UTF-8字节
// 入参: data 原始XML数据
// 返回: []byte UTF-8数据, string 编码名称, error 编码或非法字符错误
func xmlDecodedUTF8(data []byte) ([]byte, string, error) {
	encoding, bom := xmlInputEncoding(data)
	if encoding != "utf-8" && bom == 0 {
		return nil, "", fmt.Errorf("%w: UTF-16 requires a byte order mark", ErrInvalid)
	}
	decoded, err := xmlUTF8(data)
	if err != nil {
		return nil, "", err
	}
	for _, c := range string(decoded) {
		if c < 0x20 && c != '\t' && c != '\r' && c != '\n' || c == 0xfffe || c == 0xffff {
			return nil, "", fmt.Errorf("%w: forbidden XML character U+%04X", ErrInvalid, c)
		}
	}
	return decoded, encoding, nil
}

// parseXMLTokens 共用完整及前向输入的词元、命名空间、属性规范化和复杂度校验
// 入参: input 已转换UTF-8的输入, encoding 原编码, limits 资源上限, visit 可选范围访问函数, tree 是否保留完整树
// 返回: *xmlElement 根元素，词元模式不保留子元素及文本，失败为nil, error XML、资源、输入或访问错误
func parseXMLTokens(input *xmlTokenInput, encoding string, limits Limits, visit xmlTokenSpanVisitor, tree bool) (*xmlElement, error) {
	namespaceLimit := limits.MaxXMLBindings
	if namespaceLimit == 0 {
		namespaceLimit = DefaultLimits().MaxXMLBindings
	}
	if namespaceLimit < 1 {
		return nil, fmt.Errorf("%w: XML namespace binding limit", ErrInvalid)
	}
	namespaceWork := 0
	d := xml.NewDecoder(input)
	d.CharsetReader = func(charset string, input io.Reader) (io.Reader, error) {
		if encoding != "utf-8" && strings.EqualFold(charset, "utf-16") {
			return input, nil
		}
		if encoding == "utf-8" && strings.EqualFold(charset, "utf-16") {
			return nil, fmt.Errorf("%w: XML encoding declaration differs from input", ErrInvalid)
		}
		return nil, fmt.Errorf("%w: XML encoding %q", ErrUnsupported, charset)
	}
	var root *xmlElement
	var stack []*xmlElement
	count := 0
	started := false
	for {
		start := d.InputOffset()
		token, err := d.RawToken()
		if err == io.EOF {
			break
		}
		if err != nil {
			if errors.Is(err, ErrLimit) || errors.Is(err, ErrUnsupported) || errors.Is(err, ErrInvalid) || errors.Is(err, ErrClosed) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
				return nil, err
			}
			return nil, fmt.Errorf("%w: %w", ErrInvalid, err)
		}
		event := token
		var current *xmlElement
		switch token := token.(type) {
		case xml.StartElement:
			fixed, err := normalizeXMLStart(input.span(start, d.InputOffset()))
			if err != nil {
				return nil, err
			}
			if fixed != nil {
				reparsed, err := xml.NewDecoder(bytes.NewReader(fixed)).RawToken()
				if err != nil {
					return nil, fmt.Errorf("%w: invalid normalized start tag", ErrInvalid)
				}
				token = reparsed.(xml.StartElement)
			}
			count++
			if count > limits.MaxXMLNodes || len(stack) >= limits.MaxXMLDepth {
				return nil, fmt.Errorf("%w: XML complexity", ErrLimit)
			}
			if visit != nil {
				event = xml.CopyToken(token)
			}
			node := &xmlElement{rawName: token.Name, Attr: token.Attr}
			current = node
			if len(stack) > 0 {
				parent := stack[len(stack)-1]
				node.Namespaces = parent.Namespaces
				node.namespaceOwner = parent.namespaceOwner
				if tree {
					parent.Children = append(parent.Children, node)
				}
			} else if root != nil {
				return nil, fmt.Errorf("%w: multiple XML roots", ErrInvalid)
			} else {
				node.Namespaces = map[string]string{"xml": xmlNamespace}
				node.namespaceOwner = node
				namespaceWork++
				root = node
			}
			seen := make(map[xml.Name]bool, len(node.Attr))
			declarations := false
			for _, attr := range node.Attr {
				if seen[attr.Name] {
					return nil, fmt.Errorf("%w: duplicate XML attribute %s", ErrInvalid, attr.Name.Local)
				}
				seen[attr.Name] = true
				if attr.Name.Space == "xmlns" || attr.Name.Space == "" && attr.Name.Local == "xmlns" {
					if !declarations && len(stack) > 0 {
						parent := node.Namespaces
						if len(parent) > namespaceLimit-namespaceWork {
							return nil, fmt.Errorf("%w: XML namespace copy budget", ErrLimit)
						}
						namespaceWork += len(parent)
						node.Namespaces = make(map[string]string, len(parent)+1)
						node.namespaceOwner = node
						maps.Copy(node.Namespaces, parent)
					}
					declarations = true
					prefix := attr.Name.Local
					if attr.Name.Space == "" {
						prefix = ""
					}
					if _, exists := node.Namespaces[prefix]; !exists {
						if namespaceWork == namespaceLimit {
							return nil, fmt.Errorf("%w: XML namespace binding budget", ErrLimit)
						}
						namespaceWork++
					}
					if err := xmlBindNamespace(node.Namespaces, prefix, attr.Value); err != nil {
						return nil, err
					}
				}
			}
			node.Name, err = xmlExpandedName(node.Namespaces, token.Name, true)
			if err != nil {
				return nil, err
			}
			clear(seen)
			for i, attr := range node.Attr {
				if attr.Name.Space == "xmlns" {
					node.Attr[i].Name.Space = xmlnsNamespace
					continue
				}
				if attr.Name.Space == "" && attr.Name.Local == "xmlns" {
					continue
				}
				name, err := xmlExpandedName(node.Namespaces, attr.Name, false)
				if err != nil {
					return nil, err
				}
				if seen[name] {
					return nil, fmt.Errorf("%w: duplicate expanded attribute %s", ErrInvalid, name.Local)
				}
				seen[name] = true
				node.Attr[i].Name = name
			}
			stack = append(stack, node)
		case xml.EndElement:
			if len(stack) == 0 || stack[len(stack)-1].rawName != token.Name {
				return nil, fmt.Errorf("%w: mismatched XML end element", ErrInvalid)
			}
			node := stack[len(stack)-1]
			current = node
			node.Text = string(node.text)
			node.text = nil
			stack[len(stack)-1] = nil
			stack = stack[:len(stack)-1]
		case xml.CharData:
			if len(stack) == 0 {
				if !xmlWhitespace(string(input.span(start, d.InputOffset()))) {
					return nil, fmt.Errorf("%w: text outside XML root", ErrInvalid)
				}
			} else if tree {
				node := stack[len(stack)-1]
				node.text = append(node.text, token...)
			}
		case xml.Directive:
			return nil, fmt.Errorf("%w: XML document type declarations are forbidden", ErrInvalid)
		case xml.ProcInst:
			raw := input.span(start, d.InputOffset())
			separator := 2 + len(token.Target)
			if !xmlNCName(token.Target) || separator >= len(raw) || !xmlSpace(raw[separator]) && string(raw[separator:]) != "?>" {
				return nil, fmt.Errorf("%w: invalid XML processing instruction", ErrInvalid)
			}
			if strings.EqualFold(token.Target, "xml") {
				if started || token.Target != "xml" {
					return nil, fmt.Errorf("%w: misplaced XML declaration", ErrInvalid)
				}
				if err := xmlDeclaration(token.Inst, encoding); err != nil {
					return nil, err
				}
			}
		}
		if visit != nil {
			if current == nil && len(stack) > 0 {
				current = stack[len(stack)-1]
			}
			if err := visit(event, current, start, d.InputOffset()); err != nil {
				return nil, err
			}
		}
		started = true
		input.discard(d.InputOffset())
	}
	if root == nil {
		return nil, fmt.Errorf("%w: empty XML", ErrInvalid)
	}
	if len(stack) != 0 {
		return nil, fmt.Errorf("%w: unclosed XML element", ErrInvalid)
	}
	return root, nil
}

// xmlBindNamespace 检查并设置命名空间绑定
// 入参: scope 命名空间作用域, prefix 前缀, namespace 命名空间URI
// 返回: error 错误信息
func xmlBindNamespace(scope map[string]string, prefix, namespace string) error {
	if err := xmlNamespaceBinding(prefix, namespace); err != nil {
		return err
	}
	scope[prefix] = namespace
	return nil
}

// xmlNamespaceBinding 校验命名空间前缀、保留名称及取消默认绑定的规则，不改写URI
// 入参: prefix 前缀, namespace 命名空间URI
// 返回: error 绑定错误
func xmlNamespaceBinding(prefix, namespace string) error {
	if prefix == "xmlns" || namespace == xmlnsNamespace || prefix == "xml" && namespace != xmlNamespace || prefix != "xml" && namespace == xmlNamespace || prefix != "" && namespace == "" {
		return fmt.Errorf("%w: illegal namespace binding %q", ErrInvalid, prefix)
	}
	if prefix != "" && !xmlNCName(prefix) {
		return fmt.Errorf("%w: invalid namespace prefix %q", ErrInvalid, prefix)
	}
	return nil
}

// xmlNamespaceOutput 校验新生成的命名空间声明，不将非法URI转义为另一个标识
// 入参: prefix 前缀，空值表示默认命名空间, namespace 声明值，空值仅用于取消默认绑定
// 返回: error 绑定或URI语法错误
func xmlNamespaceOutput(prefix, namespace string) error {
	if err := xmlNamespaceBinding(prefix, namespace); err != nil {
		return err
	}
	if !uriReference(namespace) {
		return fmt.Errorf("%w: invalid output namespace URI %q", ErrInvalid, namespace)
	}
	return nil
}

// xmlNamespaceTreeOutput 校验已解析XML中的全部声明，不改变未使用或继承的命名空间标识
// 入参: node 已解析节点, ctx 取消Context
// 返回: error 绑定、URI或取消错误
func xmlNamespaceTreeOutput(node *xmlElement, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace {
			if err := xmlNamespaceOutput(attribute.Name.Local, attribute.Value); err != nil {
				return err
			}
		} else if attribute.Name == (xml.Name{Local: "xmlns"}) {
			if err := xmlNamespaceOutput("", attribute.Value); err != nil {
				return err
			}
		}
	}
	for _, child := range node.Children {
		if err := xmlNamespaceTreeOutput(child, ctx); err != nil {
			return err
		}
	}
	return nil
}

// xmlExpandedName 将限定名称展开为命名空间URI和本地名称
// 入参: scope 命名空间作用域, name 限定名称, element 是否为元素
// 返回: xml.Name 展开名称, error 错误信息
func xmlExpandedName(scope map[string]string, name xml.Name, element bool) (xml.Name, error) {
	if !xmlNCName(name.Local) {
		return xml.Name{}, fmt.Errorf("%w: invalid XML name %q", ErrInvalid, name.Local)
	}
	if name.Space == "" && !element {
		return name, nil
	}
	namespace, ok := scope[name.Space]
	if name.Space != "" && (!ok || name.Space == "xmlns") {
		return xml.Name{}, fmt.Errorf("%w: undeclared namespace prefix %q", ErrInvalid, name.Space)
	}
	return xml.Name{Space: namespace, Local: name.Local}, nil
}

// xmlInputEncoding 识别XML字节序及字节序标记长度
// 入参: data XML数据
// 返回: string 编码名称, int 字节序标记长度
func xmlInputEncoding(data []byte) (string, int) {
	if bytes.HasPrefix(data, []byte{0xff, 0xfe}) {
		return "utf-16le", 2
	}
	if bytes.HasPrefix(data, []byte{0xfe, 0xff}) {
		return "utf-16be", 2
	}
	if bytes.HasPrefix(data, []byte{'<', 0}) {
		return "utf-16le", 0
	}
	if bytes.HasPrefix(data, []byte{0, '<'}) {
		return "utf-16be", 0
	}
	if bytes.HasPrefix(data, []byte{0xef, 0xbb, 0xbf}) {
		return "utf-8", 3
	}
	return "utf-8", 0
}

// xmlDeclaration 核对XML声明的版本、编码和独立性属性
// 入参: text 声明内容, encoding 实际编码
// 返回: error 错误信息
func xmlDeclaration(text []byte, encoding string) error {
	if bytes.ContainsAny(text, "&<>") {
		return fmt.Errorf("%w: invalid XML declaration syntax", ErrInvalid)
	}
	markup := []byte("<declaration " + string(text) + "/>")
	if _, err := normalizeXMLStart(markup); err != nil {
		return err
	}
	d := xml.NewDecoder(bytes.NewReader(markup))
	token, err := d.Token()
	if err != nil {
		return fmt.Errorf("%w: XML declaration", ErrInvalid)
	}
	element, ok := token.(xml.StartElement)
	if !ok || len(element.Attr) == 0 || element.Attr[0].Name != (xml.Name{Local: "version"}) || element.Attr[0].Value != "1.0" {
		return fmt.Errorf("%w: XML version declaration", ErrInvalid)
	}
	declared, standalone := false, false
	for _, attr := range element.Attr[1:] {
		if attr.Name.Space != "" {
			return fmt.Errorf("%w: XML declaration attribute", ErrInvalid)
		}
		switch attr.Name.Local {
		case "encoding":
			if declared || standalone {
				return fmt.Errorf("%w: XML declaration order", ErrInvalid)
			}
			value := strings.ToLower(attr.Value)
			if !(value == "utf-8" && encoding == "utf-8") && !(value == "utf-16" && encoding != "utf-8") {
				return fmt.Errorf("%w: XML encoding declaration differs from input", ErrInvalid)
			}
			declared = true
		case "standalone":
			if standalone || attr.Value != "yes" && attr.Value != "no" {
				return fmt.Errorf("%w: XML standalone declaration", ErrInvalid)
			}
			standalone = true
		default:
			return fmt.Errorf("%w: unknown XML declaration attribute", ErrInvalid)
		}
	}
	return nil
}

// xmlWhitespace 检查文本是否只包含XML定义的空白字符
// 入参: text 待检查文本
// 返回: bool 是否全部为空白
func xmlWhitespace(text string) bool {
	for i := range len(text) {
		if !xmlSpace(text[i]) {
			return false
		}
	}
	return true
}

// xmlSpace 检查单个字节是否为XML空白字符
// 入参: value 待检查字节
// 返回: bool 是否为空白
func xmlSpace(value byte) bool {
	return value == ' ' || value == '\t' || value == '\r' || value == '\n'
}

// normalizeXMLStart 校验起始标签的属性分隔并规范化字面空白，保留字符引用
// 入参: data 完整起始标签
// 返回: []byte 规范化后的标签，无须转换时为nil, error 错误信息
func normalizeXMLStart(data []byte) ([]byte, error) {
	i := 1
	for i < len(data) && !xmlSpace(data[i]) && data[i] != '>' && data[i] != '/' {
		i++
	}
	var output []byte
	last := 0
	for i < len(data) {
		before := i
		for i < len(data) && xmlSpace(data[i]) {
			i++
		}
		if i >= len(data) {
			return nil, fmt.Errorf("%w: incomplete start tag", ErrInvalid)
		}
		if data[i] == '>' || data[i] == '/' {
			if output != nil {
				output = append(output, data[last:]...)
			}
			return output, nil
		}
		if i == before {
			return nil, fmt.Errorf("%w: missing whitespace between XML attributes", ErrInvalid)
		}
		for i < len(data) && !xmlSpace(data[i]) && data[i] != '=' {
			i++
		}
		for i < len(data) && xmlSpace(data[i]) {
			i++
		}
		if i >= len(data) || data[i] != '=' {
			return nil, fmt.Errorf("%w: missing XML attribute assignment", ErrInvalid)
		}
		i++
		for i < len(data) && xmlSpace(data[i]) {
			i++
		}
		if i >= len(data) || data[i] != '\'' && data[i] != '"' {
			return nil, fmt.Errorf("%w: unquoted XML attribute", ErrInvalid)
		}
		quote := data[i]
		i++
		start := i
		for i < len(data) && data[i] != quote {
			i++
		}
		if i >= len(data) {
			return nil, fmt.Errorf("%w: incomplete XML attribute", ErrInvalid)
		}
		value := data[start:i]
		if bytes.ContainsAny(value, "\t\r\n") {
			output = append(output, data[last:start]...)
			for j := 0; j < len(value); j++ {
				ch := value[j]
				if ch == '\r' {
					if j+1 < len(value) && value[j+1] == '\n' {
						j++
					}
					ch = ' '
				} else if ch == '\t' || ch == '\n' {
					ch = ' '
				}
				output = append(output, ch)
			}
			last = i
		}
		i++
	}
	return nil, fmt.Errorf("%w: incomplete start tag", ErrInvalid)
}

// attribute 查找未限定命名空间的属性
// 入参: name 属性名称
// 返回: string 属性值, bool 是否存在
func (e *xmlElement) attribute(name string) (string, bool) {
	return e.attributeNS("", name)
}

// attributeNS 按展开名称查找属性
// 入参: namespace 命名空间, name 属性名称
// 返回: string 属性值, bool 是否存在
func (e *xmlElement) attributeNS(namespace, name string) (string, bool) {
	for _, attr := range e.Attr {
		if attr.Name.Space == namespace && attr.Name.Local == name {
			return attr.Value, true
		}
	}
	return "", false
}

// xmlUTF8 将XML的UTF-16编码转换为UTF-8并检查字符序列
// 入参: data XML数据
// 返回: []byte UTF-8数据, error 错误信息
func xmlUTF8(data []byte) ([]byte, error) {
	little, wide, start := false, false, 0
	if len(data) >= 2 {
		switch {
		case data[0] == 0xff && data[1] == 0xfe:
			little, wide, start = true, true, 2
		case data[0] == 0xfe && data[1] == 0xff:
			wide, start = true, 2
		case data[0] == '<' && data[1] == 0:
			little, wide = true, true
		case data[0] == 0 && data[1] == '<':
			wide = true
		}
	}
	if !wide {
		data = bytes.TrimPrefix(data, []byte{0xef, 0xbb, 0xbf})
		if !utf8.Valid(data) {
			return nil, fmt.Errorf("%w: invalid UTF-8", ErrInvalid)
		}
		return data, nil
	}
	if (len(data)-start)%2 != 0 {
		return nil, fmt.Errorf("%w: truncated UTF-16", ErrInvalid)
	}
	output := make([]byte, 0, len(data))
	var high rune
	for i := start; i < len(data); i += 2 {
		value := rune(data[i])<<8 | rune(data[i+1])
		if little {
			value = rune(data[i+1])<<8 | rune(data[i])
		}
		if high != 0 {
			if value < 0xdc00 || value > 0xdfff {
				return nil, fmt.Errorf("%w: invalid UTF-16 surrogate", ErrInvalid)
			}
			value = 0x10000 + (high-0xd800)*0x400 + value - 0xdc00
			high = 0
		} else if value >= 0xd800 && value <= 0xdbff {
			high = value
			continue
		} else if value >= 0xdc00 && value <= 0xdfff {
			return nil, fmt.Errorf("%w: invalid UTF-16 surrogate", ErrInvalid)
		}
		output = utf8.AppendRune(output, value)
	}
	if high != 0 {
		return nil, fmt.Errorf("%w: incomplete UTF-16 surrogate", ErrInvalid)
	}
	return output, nil
}

// formatNamespace 返回格式使用的页面命名空间
// 入参: format 文档格式
// 返回: string 命名空间
func formatNamespace(format Format) string {
	if format == FormatXPS {
		return xpsNamespace
	}
	if format == FormatOpenXPS {
		return openXPSNamespace
	}
	return ""
}

// fixedContentType 返回XPS和OpenXPS共用的固定布局部件媒体类型，格式由主关系及XML命名空间识别
// 入参: kind 部件种类
// 返回: string 媒体类型
func fixedContentType(kind string) string {
	return "application/vnd.ms-package.xps-" + kind + "+xml"
}

// xmlNumber 解析XML Schema实数词法，支持尾随小数点，不接受无数字小数点、非有限值或Go专用数值语法
// 入参: text 属性文本
// 返回: float64 数值, error 错误信息
func xmlNumber(text string) (float64, error) {
	text = strings.Trim(text, " \t\r\n")
	if text == "" {
		return 0, fmt.Errorf("%w: empty number", ErrInvalid)
	}
	i := 0
	if text[i] == '+' || text[i] == '-' {
		i++
	}
	intStart := i
	for i < len(text) && text[i] >= '0' && text[i] <= '9' {
		i++
	}
	intDigits := i - intStart
	fracDigits := 0
	if i < len(text) && text[i] == '.' {
		i++
		fracStart := i
		for i < len(text) && text[i] >= '0' && text[i] <= '9' {
			i++
		}
		fracDigits = i - fracStart
	}
	if intDigits == 0 && fracDigits == 0 {
		return 0, fmt.Errorf("%w: invalid number %q", ErrInvalid, text)
	}
	if i < len(text) && (text[i] == 'e' || text[i] == 'E') {
		i++
		if i < len(text) && (text[i] == '+' || text[i] == '-') {
			i++
		}
		expStart := i
		for i < len(text) && text[i] >= '0' && text[i] <= '9' {
			i++
		}
		if i == expStart {
			return 0, fmt.Errorf("%w: invalid exponent in %q", ErrInvalid, text)
		}
	}
	if i != len(text) {
		return 0, fmt.Errorf("%w: invalid number %q", ErrInvalid, text)
	}
	value, err := strconv.ParseFloat(text, 64)
	if err != nil || math.IsNaN(value) || math.IsInf(value, 0) {
		return 0, fmt.Errorf("%w: invalid number %q", ErrInvalid, text)
	}
	return value, nil
}

// xmlNCName 校验XML 1.0第四版NCName，不执行空白规范化
// 入参: value 待校验名称
// 返回: bool 是否为合法名称
func xmlNCName(value string) bool {
	if value == "" {
		return false
	}
	ascii := true
	for i := 0; i < len(value); i++ {
		c := value[i]
		if c >= 0x80 {
			ascii = false
			continue
		}
		start := c == '_' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z'
		if !start && (i == 0 || !(c == '-' || c == '.' || c >= '0' && c <= '9')) {
			return false
		}
	}
	if ascii {
		return true
	}
	d := xml.NewDecoder(io.MultiReader(strings.NewReader("<"), strings.NewReader(value), strings.NewReader("/>")))
	token, err := d.RawToken()
	if err != nil {
		return false
	}
	start, ok := token.(xml.StartElement)
	if !ok || start.Name != (xml.Name{Local: value}) || len(start.Attr) != 0 {
		return false
	}
	token, err = d.RawToken()
	if err != nil {
		return false
	}
	end, ok := token.(xml.EndElement)
	if !ok || end.Name != start.Name {
		return false
	}
	token, err = d.RawToken()
	return token == nil && err == io.EOF
}

// xmlTextValid 检查XML1.0允许的字符，不让标准库转义函数静默替换非法输入
// 入参: value 待编码文字
// 返回: bool 是否为合法UTF-8及XML文字
func xmlTextValid(value string) bool {
	if !utf8.ValidString(value) {
		return false
	}
	for _, character := range value {
		if character < 0x20 && character != '\t' && character != '\r' && character != '\n' || character == 0xfffe || character == 0xffff {
			return false
		}
	}
	return true
}

// xmlDateValue 校验W3CDTF或XML Schema dateTime词法与公历约束，不用time.Time的年份或精度范围缩小合法声明
// 入参: value 已去除首尾XML空白的日期, full 为true时必须为xs:dateTime，否则严格校验W3CDTF
// 返回: bool 是否为合法声明
func xmlDateValue(value string, full bool) bool {
	pattern := xmlW3CDTFPattern
	if full {
		pattern = xmlDateTimePattern
	}
	fields := pattern.FindStringSubmatch(value)
	if fields == nil || fields[1] == "0000" || full && len(fields[1]) > 4 && fields[1][0] == '0' {
		return false
	}
	if zone := fields[8]; zone != "" && zone != "Z" {
		hour, minute := xmlDatePair(zone[1:3]), xmlDatePair(zone[4:6])
		if hour > 14 || minute > 59 || hour == 14 && minute != 0 {
			return false
		}
	}
	if fields[2] != "" {
		month := xmlDatePair(fields[2])
		if month < 1 || month > 12 {
			return false
		}
		if fields[3] != "" {
			maximum := [12]int{31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31}[month-1]
			if month == 2 {
				year := 0
				for _, digit := range fields[1] {
					year = (year*10 + int(digit-'0')) % 400
				}
				if year%4 == 0 && (year%100 != 0 || year == 0) {
					maximum++
				}
			}
			day := xmlDatePair(fields[3])
			if day < 1 || day > maximum {
				return false
			}
		}
	}
	if fields[4] != "" {
		hour, minute := xmlDatePair(fields[4]), xmlDatePair(fields[5])
		second := 0
		if fields[6] != "" {
			second = xmlDatePair(fields[6])
		}
		if !full {
			return hour <= 23 && minute <= 59 && second <= 59
		}
		if hour > 24 || minute > 59 || second > 59 || hour == 24 && (minute != 0 || second != 0 || strings.Trim(fields[7], "0") != "") {
			return false
		}
	}
	return true
}

// xmlDatePair 读取已由日期模式确认的两位十进制数
// 入参: value 两位ASCII数字
// 返回: int 数值
func xmlDatePair(value string) int {
	return int(value[0]-'0')*10 + int(value[1]-'0')
}

// restoreXMLEncoding 按已校验原XML的编码输出UTF-8修改结果，保留编码声明及字节序标记
// 入参: original 原XML, data UTF-8结果, maximum 字节上限, ctx 取消Context
// 返回: []byte 原编码结果, error 预算或取消错误
func restoreXMLEncoding(original, data []byte, maximum int64, ctx context.Context) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	encoding, bom := xmlInputEncoding(original)
	if encoding == "utf-8" {
		if int64(len(data))+int64(bom) > maximum {
			return nil, fmt.Errorf("%w: encoded XML byte budget", ErrLimit)
		}
		if bom == 0 {
			return data, nil
		}
		return append(append([]byte(nil), original[:bom]...), data...), nil
	}
	output := append(make([]byte, 0, len(original)), original[:bom]...)
	nextCheck := 0
	for index, character := range string(data) {
		if index >= nextCheck {
			nextCheck = index + 2048
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
		}
		units := [2]rune{character}
		count := 1
		if character > 0xffff {
			units[0], units[1] = utf16.EncodeRune(character)
			count = 2
		}
		if int64(len(output))+int64(count*2) > maximum {
			return nil, fmt.Errorf("%w: encoded XML byte budget", ErrLimit)
		}
		for _, value := range units[:count] {
			if encoding == "utf-16le" {
				output = append(output, byte(value), byte(value>>8))
			} else {
				output = append(output, byte(value>>8), byte(value))
			}
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return output, nil
}

// decodeXMLContent 共用XML校验并保存内容顺序，失败不返回树或部分词元
// 入参: data 原始XML字节, limits 输入及复杂度上限, ctx 取消Context
// 返回: *xmlElement 根元素, *xmlContentReader 内容索引, error 解析、预算或取消错误
func decodeXMLContent(data []byte, limits Limits, ctx context.Context) (*xmlElement, *xmlContentReader, error) {
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	r := &xmlContentReader{context: ctx, limit: limits.MaxXMLNodes, nodes: make(map[*xmlElement][]xmlContent)}
	root, err := decodeXMLVisit(data, limits, r.visit)
	if err != nil {
		return nil, nil, err
	}
	return root, r, nil
}

// visit 记录子元素与文本、注释、处理指令的原始顺序，不保存XML声明或输入缓冲的共享视图
// 入参: token 已校验词元, node 当前词元所属元素
// 返回: error 复杂度或取消错误
func (r *xmlContentReader) visit(token xml.Token, node *xmlElement) error {
	if err := checkContext(r.context); err != nil {
		return err
	}
	if _, end := token.(xml.EndElement); !end {
		r.count++
		if r.count > r.limit {
			return fmt.Errorf("%w: ordered XML token count", ErrLimit)
		}
	}
	switch token := token.(type) {
	case xml.StartElement:
		if len(r.stack) != 0 {
			parent := r.stack[len(r.stack)-1]
			r.nodes[parent] = append(r.nodes[parent], xmlContent{element: node})
		}
		r.nodes[node] = nil
		r.stack = append(r.stack, node)
	case xml.EndElement:
		r.stack = r.stack[:len(r.stack)-1]
	case xml.ProcInst:
		if token.Target == "xml" {
			return nil
		}
		r.append(node, xml.CopyToken(token))
	case xml.CharData, xml.Comment:
		r.append(node, xml.CopyToken(token))
	}
	return nil
}

// append 将非元素词元加入所属元素的内容列表，忽略根外词元并保持相对位置
// 入参: node 所属元素，根外词元为nil, token 独立词元
func (r *xmlContentReader) append(node *xmlElement, token xml.Token) {
	if node != nil {
		r.nodes[node] = append(r.nodes[node], xmlContent{token: token})
	}
}

// rewriteXMLAttributes 在可选命名空间白名单与词元作用域过滤下定点改写XML属性，跳过被忽略或保留扩展子树并保留原编码
// 入参: original 原始XML, limits 资源上限, ctx 取消Context, namespaces 允许的原URI到目标URI映射, filter 可选词元级跳过回调, rewrite 属性改写回调
// 返回: []byte 原编码XML, bool 是否实际修改, error XML、绑定、作用域、资源或取消错误
func rewriteXMLAttributes(original []byte, limits Limits, ctx context.Context, namespaces map[string]string, filter func(xml.Token, *xmlElement) (bool, error), rewrite xmlAttributeRewrite) ([]byte, bool, error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, err
	}
	if rewrite == nil {
		return nil, false, fmt.Errorf("%w: missing XML attribute rewriter", ErrInvalid)
	}
	maximum := min(limits.MaxPartBytes, limits.MaxPackageBytes)
	if maximum < 1 {
		return nil, false, fmt.Errorf("%w: XML attribute rewrite byte limit", ErrInvalid)
	}
	maximum = min(maximum, int64(int(^uint(0)>>1)))
	if int64(len(original)) > maximum {
		return nil, false, fmt.Errorf("%w: XML attribute rewrite input budget", ErrLimit)
	}
	input, encoding, err := xmlDecodedUTF8(original)
	if err != nil {
		return nil, false, err
	}
	var changes []xmlValueReplacement
	outputSize := int64(len(input))
	intermediateLimit := maximum
	if encoding != "utf-8" {
		intermediateLimit += min(maximum/2, int64(math.MaxInt)-maximum)
	}
	var replacementBytes int64
	_, err = parseXMLTokens(&xmlTokenInput{reader: bytes.NewReader(input), data: input}, encoding, limits, func(token xml.Token, node *xmlElement, start, end int64) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if filter != nil {
			skip, err := filter(token, node)
			if err != nil {
				return err
			}
			if skip {
				return nil
			}
		}
		if _, present := token.(xml.StartElement); !present {
			return nil
		}
		ranges, err := xmlStartAttributeRanges(input[start:end])
		if err != nil {
			return err
		}
		if len(ranges) != len(node.Attr) {
			return fmt.Errorf("%w: XML attribute range count", ErrInvalid)
		}
		for index, attribute := range node.Attr {
			value, changed, err := rewrite(node, attribute)
			if err != nil {
				return err
			}
			if !changed || value == attribute.Value {
				continue
			}
			if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
				if target, allowed := namespaces[attribute.Value]; !allowed || target != value {
					return fmt.Errorf("%w: XML namespace rewrite is not permitted", ErrInvalid)
				}
			}
			if int64(len(value)) > intermediateLimit-replacementBytes {
				return fmt.Errorf("%w: XML attribute replacement byte budget", ErrLimit)
			}
			if !xmlTextValid(value) {
				return fmt.Errorf("%w: XML attribute replacement text", ErrInvalid)
			}
			escaped := xmlRewriteBuffer{maximum: intermediateLimit - replacementBytes, context: ctx}
			if err := xml.EscapeText(&escaped, []byte(value)); err != nil {
				return err
			}
			span := ranges[index]
			outputSize += int64(escaped.Len() - (span.end - span.start))
			replacementBytes += int64(escaped.Len())
			changes = append(changes, xmlValueReplacement{start: int(start) + span.start, end: int(start) + span.end, data: escaped.Bytes()})
		}
		return nil
	}, true)
	if err != nil {
		return nil, false, err
	}
	if len(changes) == 0 {
		output := bytes.Clone(original)
		if err := checkContext(ctx); err != nil {
			return nil, false, err
		}
		return output, false, nil
	}
	if outputSize > intermediateLimit || outputSize > int64(int(^uint(0)>>1)) {
		return nil, false, fmt.Errorf("%w: XML attribute rewrite output budget", ErrLimit)
	}
	output := make([]byte, 0, int(outputSize))
	position := 0
	for _, change := range changes {
		if err := checkContext(ctx); err != nil {
			return nil, false, err
		}
		output = append(output, input[position:change.start]...)
		output = append(output, change.data...)
		position = change.end
	}
	output = append(output, input[position:]...)
	output, err = restoreXMLEncoding(original, output, maximum, ctx)
	if err != nil {
		return nil, false, err
	}
	if _, err := decodeXMLVisit(output, limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) }); err != nil {
		return nil, false, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, false, err
	}
	return output, true, nil
}

// Write 在扩展属性转义缓冲区前检查剩余字节与取消状态
// 入参: data 转义片段
// 返回: int 已写入字节数, error 资源或取消错误
func (b *xmlRewriteBuffer) Write(data []byte) (int, error) {
	if err := checkContext(b.context); err != nil {
		return 0, err
	}
	if int64(len(data)) > b.maximum-int64(b.Len()) {
		return 0, fmt.Errorf("%w: XML attribute escape byte budget", ErrLimit)
	}
	if len(data) > b.Available() {
		capacity := int(b.maximum)
		if int64(b.Cap()) <= b.maximum/2 {
			capacity = max(b.Len()+len(data), b.Cap()*2)
		}
		buffer := make([]byte, b.Len(), capacity)
		copy(buffer, b.Bytes())
		b.Buffer = *bytes.NewBuffer(buffer)
	}
	return b.Buffer.Write(data)
}

// xmlStartAttributeRanges 从已校验的起始标签提取属性值范围，识别两种引号及自闭合标记
// 入参: tag 一个完整起始标签
// 返回: []xmlAttributeRange 按属性顺序排列的范围, error 标签范围错误
func xmlStartAttributeRanges(tag []byte) ([]xmlAttributeRange, error) {
	if len(tag) < 3 || tag[0] != '<' {
		return nil, fmt.Errorf("%w: XML start tag range", ErrInvalid)
	}
	position := 1
	for position < len(tag) && !xmlSpace(tag[position]) && tag[position] != '/' && tag[position] != '>' {
		position++
	}
	var ranges []xmlAttributeRange
	for position < len(tag) {
		for position < len(tag) && xmlSpace(tag[position]) {
			position++
		}
		if position == len(tag) {
			break
		}
		if tag[position] == '/' || tag[position] == '>' {
			return ranges, nil
		}
		for position < len(tag) && !xmlSpace(tag[position]) && tag[position] != '=' {
			position++
		}
		for position < len(tag) && xmlSpace(tag[position]) {
			position++
		}
		if position == len(tag) || tag[position] != '=' {
			break
		}
		position++
		for position < len(tag) && xmlSpace(tag[position]) {
			position++
		}
		if position == len(tag) || tag[position] != '\'' && tag[position] != '"' {
			break
		}
		quote := tag[position]
		position++
		start := position
		for position < len(tag) && tag[position] != quote {
			position++
		}
		if position == len(tag) {
			break
		}
		ranges = append(ranges, xmlAttributeRange{start: start, end: position})
		position++
	}
	return nil, fmt.Errorf("%w: XML attribute range", ErrInvalid)
}

// decodeXMLReader 从前向流解码并校验XML树，按需向回调流式交付已校验词元范围
// 入参: input 原始XML输入, limits 资源上限, ctx 取消Context, visit 可选范围访问函数
// 返回: *xmlElement 完整根元素，失败为nil, error 编码、XML、输入、预算、访问或取消错误
func decodeXMLReader(input io.Reader, limits Limits, ctx context.Context, visit xmlTokenSpanVisitor) (*xmlElement, error) {
	return decodeXMLInput(input, limits, ctx, visit, true)
}

// scanXMLReader 校验前向XML并交付词元，不保留已处理的子元素和文本
// 入参: input 原始XML输入, limits 资源上限, ctx 取消Context, visit 可选范围访问函数
// 返回: error 编码、XML、输入、预算、访问或取消错误
func scanXMLReader(input io.Reader, limits Limits, ctx context.Context, visit xmlTokenSpanVisitor) error {
	_, err := decodeXMLInput(input, limits, ctx, visit, false)
	return err
}

// decodeXMLInput 共用前向编码转换及XML校验，按用途选择完整树或仅词元处理
// 入参: input 原始XML输入, limits 资源上限, ctx 取消Context, visit 可选范围访问函数, tree 是否保留完整树
// 返回: *xmlElement 根元素，词元模式不保留子元素及文本，失败为nil, error 编码、XML、输入、预算、访问或取消错误
func decodeXMLInput(input io.Reader, limits Limits, ctx context.Context, visit xmlTokenSpanVisitor, tree bool) (*xmlElement, error) {
	if input == nil || limits.MaxPartBytes < 1 || limits.MaxPackageBytes < 1 || limits.MaxXMLDepth < 1 || limits.MaxXMLNodes < 1 {
		return nil, fmt.Errorf("%w: forward XML parameters", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	maximum := min(limits.MaxPartBytes, limits.MaxPackageBytes)
	probe := int64(math.MaxInt64)
	if maximum <= math.MaxInt64-4 {
		probe = maximum + 4
	}
	reader := bufio.NewReaderSize(io.LimitReader(input, probe), streamBufferBytes)
	prefix, err := reader.Peek(4)
	if err != nil && err != io.EOF {
		return nil, err
	}
	encoding, bom := xmlInputEncoding(prefix)
	if encoding != "utf-8" && bom == 0 {
		return nil, fmt.Errorf("%w: UTF-16 requires a byte order mark", ErrInvalid)
	}
	if bom != 0 {
		if _, err := reader.Discard(bom); err != nil {
			return nil, err
		}
	}
	stream := &xmlUTF8Stream{reader: reader, context: ctx, encoding: encoding, limit: maximum, consumed: int64(bom)}
	if stream.consumed > maximum {
		return nil, fmt.Errorf("%w: forward XML byte budget", ErrLimit)
	}
	var visitor xmlTokenSpanVisitor
	if visit != nil {
		visitor = func(token xml.Token, node *xmlElement, start, end int64) error {
			if err := checkContext(ctx); err != nil {
				return err
			}
			return visit(token, node, start, end)
		}
	}
	root, err := parseXMLTokens(&xmlTokenInput{reader: stream}, encoding, limits, visitor, tree)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return root, nil
}

// Read 为标准库XML解码器提供字节读取能力，不跨过当前调用要求的范围
// 入参: output 接收缓冲
// 返回: int 已读字节数, error 输入、编码或结束信息
func (s *xmlTokenInput) Read(output []byte) (int, error) {
	for index := range output {
		value, err := s.ReadByte()
		if err != nil {
			return index, err
		}
		output[index] = value
	}
	return len(output), nil
}

// ReadByte 保存前向词元的原始字节，完整字节输入不额外复制
// 返回: byte UTF-8字节, error 输入或结束信息
func (s *xmlTokenInput) ReadByte() (byte, error) {
	value, err := s.reader.ReadByte()
	if err == nil && s.data == nil {
		s.buffer = append(s.buffer, value)
	}
	return value, err
}

// span 返回当前词元已经确认的UTF-8原文，仅供同步校验使用
// 入参: start, end 解码器确认的字节范围
// 返回: []byte 原始词元
func (s *xmlTokenInput) span(start, end int64) []byte {
	if s.data != nil {
		return s.data[start:end]
	}
	return s.buffer[start-s.base : end-s.base]
}

// discard 丢弃已经提交的词元原文，保留解码器预读并待下次使用的字节
// 入参: end 已经提交的UTF-8范围末尾
func (s *xmlTokenInput) discard(end int64) {
	if s.data != nil {
		return
	}
	remaining := copy(s.buffer, s.buffer[end-s.base:])
	s.buffer = s.buffer[:remaining]
	s.base = end
}

// ReadByte 转换一个完整Unicode字符后逐字节输出UTF-8，拒绝非法编码和XML禁止字符
// 返回: byte 已校验UTF-8字节, error 输入、编码、预算、取消或结束信息
func (s *xmlUTF8Stream) ReadByte() (byte, error) {
	if err := checkContext(s.context); err != nil {
		return 0, err
	}
	if s.position == s.count {
		if s.encoding == "utf-8" {
			value, err := s.reader.ReadByte()
			if err != nil {
				return 0, err
			}
			s.consumed++
			if s.consumed > s.limit {
				return 0, fmt.Errorf("%w: forward XML byte budget", ErrLimit)
			}
			if value < utf8.RuneSelf {
				if value < 0x20 && value != '\t' && value != '\r' && value != '\n' {
					return 0, fmt.Errorf("%w: forbidden XML character U+%04X", ErrInvalid, value)
				}
				return value, nil
			}
			if err := s.reader.UnreadByte(); err != nil {
				return 0, err
			}
			s.consumed--
		}
		character, err := s.readRune()
		if err != nil {
			return 0, err
		}
		if character < 0x20 && character != '\t' && character != '\r' && character != '\n' || character == 0xfffe || character == 0xffff {
			return 0, fmt.Errorf("%w: forbidden XML character U+%04X", ErrInvalid, character)
		}
		s.position, s.count = 0, utf8.EncodeRune(s.pending[:], character)
	}
	value := s.pending[s.position]
	s.position++
	return value, nil
}

// readRune 读取原编码中的完整字符，不把分片结束处的半个字符当作替代字符
// 返回: rune Unicode字符, error 输入、代理对、编码、预算或结束信息
func (s *xmlUTF8Stream) readRune() (rune, error) {
	if s.encoding == "utf-8" {
		character, count, err := s.reader.ReadRune()
		s.consumed += int64(count)
		if s.consumed > s.limit {
			return 0, fmt.Errorf("%w: forward XML byte budget", ErrLimit)
		}
		if err != nil {
			return 0, err
		}
		if character == utf8.RuneError && count == 1 {
			return 0, fmt.Errorf("%w: invalid UTF-8", ErrInvalid)
		}
		return character, nil
	}
	first, err := s.readUnit()
	if err != nil {
		return 0, err
	}
	if first >= 0xdc00 && first <= 0xdfff {
		return 0, fmt.Errorf("%w: unmatched UTF-16 low surrogate", ErrInvalid)
	}
	if first < 0xd800 || first > 0xdbff {
		return rune(first), nil
	}
	second, err := s.readUnit()
	if err != nil {
		if errors.Is(err, ErrLimit) || errors.Is(err, ErrClosed) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
			return 0, err
		}
		return 0, fmt.Errorf("%w: UTF-16 surrogate pair: %w", ErrInvalid, err)
	}
	if second < 0xdc00 || second > 0xdfff {
		return 0, fmt.Errorf("%w: invalid UTF-16 surrogate pair", ErrInvalid)
	}
	return utf16.DecodeRune(rune(first), rune(second)), nil
}

// readUnit 读取一个原始UTF-16编码单元并检查实际输入预算
// 返回: uint16 编码单元, error 输入、截断、预算或结束信息
func (s *xmlUTF8Stream) readUnit() (uint16, error) {
	var data [2]byte
	n, err := io.ReadFull(s.reader, data[:])
	s.consumed += int64(n)
	if s.consumed > s.limit {
		return 0, fmt.Errorf("%w: forward XML byte budget", ErrLimit)
	}
	if err != nil {
		return 0, err
	}
	if s.encoding == "utf-16le" {
		return binary.LittleEndian.Uint16(data[:]), nil
	}
	return binary.BigEndian.Uint16(data[:]), nil
}

// preprocessXMLContext 在兼容性处理步骤检查取消信号，不改变普通预处理的分支选择规则
// 入参: root 原始元素树, understood 明确理解的命名空间, ctx 取消Context
// 返回: *xmlElement 唯一过滤根元素, error 兼容性或取消错误
func preprocessXMLContext(root *xmlElement, understood []string, ctx context.Context) (*xmlElement, error) {
	p := compatibilityProcessor{understood: map[string]bool{mcNamespace: true, xmlNamespace: true}, context: ctx}
	for _, namespace := range understood {
		p.understood[namespace] = true
	}
	fragment, err := p.element(root, compatibilityScope{})
	if err != nil {
		return nil, err
	}
	if len(fragment.elements) != 1 || len(compatibilityWords(fragment.text)) != 0 {
		return nil, fmt.Errorf("%w: MCE preprocessing must retain exactly one root element", ErrInvalid)
	}
	return fragment.elements[0], nil
}

// preprocessXMLContentContext 在兼容性处理步骤保留元素与保留扩展的文档相对顺序，供XML重写透传使用
// 入参: data 原始XML字节, understood 明确理解的命名空间, limits 资源上限, ctx 取消Context
// 返回: *xmlElement 唯一过滤根元素, map[*xmlElement][]xmlContent 含保留扩展的有序内容索引, error 解码、兼容性或取消错误
func preprocessXMLContentContext(data []byte, understood []string, limits Limits, ctx context.Context) (*xmlElement, map[*xmlElement][]xmlContent, error) {
	root, content, err := decodeXMLContent(data, limits, ctx)
	if err != nil {
		return nil, nil, err
	}
	p := compatibilityProcessor{understood: map[string]bool{mcNamespace: true, xmlNamespace: true}, content: content.nodes, includePreserved: true, context: ctx}
	for _, namespace := range understood {
		p.understood[namespace] = true
	}
	fragment, err := p.element(root, compatibilityScope{})
	if err != nil {
		return nil, nil, err
	}
	if len(fragment.elements) != 1 || len(compatibilityWords(fragment.text)) != 0 {
		return nil, nil, fmt.Errorf("%w: MCE preprocessing must retain exactly one root element", ErrInvalid)
	}
	return fragment.elements[0], content.nodes, nil
}

// element 处理单个元素并移除不参与消费的包装
// 入参: node 当前元素, inherited 祖先兼容性作用域
// 返回: compatibilityFragment 过滤后的片段, error 错误信息
func (p *compatibilityProcessor) element(node *xmlElement, inherited compatibilityScope) (compatibilityFragment, error) {
	if err := checkContext(p.context); err != nil {
		return compatibilityFragment{}, err
	}
	if node == nil {
		return compatibilityFragment{}, fmt.Errorf("%w: nil XML element", ErrInvalid)
	}
	scope, err := p.rulesChecked(node, inherited, !p.ignorePreservation)
	if err != nil {
		return compatibilityFragment{}, err
	}
	if !p.understood[node.Name.Space] {
		if !scope.ignorable[node.Name.Space] {
			return compatibilityFragment{}, fmt.Errorf("%w: element namespace %q", ErrUnsupported, node.Name.Space)
		}
		if scope.processes(node.Name) {
			if p.ignorePreservation {
				if value, ok := node.attributeNS(mcNamespace, "MustUnderstand"); ok {
					if err := p.checkMustUnderstand(node, value); err != nil {
						return compatibilityFragment{}, err
					}
				}
			}
			if err := compatibilityNoXMLContext(node); err != nil {
				return compatibilityFragment{}, err
			}
			return p.contents(node, scope)
		}
		if !p.ignorePreservation && scope.preservesElement(node.Name) {
			preserved, err := p.preserveElement(node, scope)
			if err != nil {
				return compatibilityFragment{}, err
			}
			result := compatibilityFragment{preserved: []*xmlElement{preserved}}
			if p.content != nil && p.includePreserved {
				result.ordered = []xmlContent{{element: preserved}}
			}
			return result, nil
		}
		return compatibilityFragment{}, nil
	}
	if p.ignorePreservation {
		if value, ok := node.attributeNS(mcNamespace, "MustUnderstand"); ok {
			if err := p.checkMustUnderstand(node, value); err != nil {
				return compatibilityFragment{}, err
			}
		}
	}
	if node.Name.Space == mcNamespace {
		if node.Name.Local != "AlternateContent" {
			return compatibilityFragment{}, fmt.Errorf("%w: unexpected MCE element %s", ErrInvalid, node.Name.Local)
		}
		return p.alternate(node, scope)
	}
	attrs, preservedAttrs, err := p.attributesWithPreserved(node, scope)
	if err != nil {
		return compatibilityFragment{}, err
	}
	if len(node.PreservedAttributes) != 0 {
		mergedAttrs := make([]xml.Attr, 0, len(node.PreservedAttributes)+len(preservedAttrs))
		mergedAttrs = append(mergedAttrs, node.PreservedAttributes...)
		mergedAttrs = append(mergedAttrs, preservedAttrs...)
		preservedAttrs = mergedAttrs
	}
	content, err := p.contents(node, scope)
	if err != nil {
		return compatibilityFragment{}, err
	}
	var preservedElements []*xmlElement
	if len(node.PreservedElements) != 0 || len(content.preserved) != 0 {
		preservedElements = make([]*xmlElement, 0, len(node.PreservedElements)+len(content.preserved))
		for _, item := range node.PreservedElements {
			clonedItem, err := cloneXMLElement(item, p.context)
			if err != nil {
				return compatibilityFragment{}, err
			}
			preservedElements = append(preservedElements, clonedItem)
		}
		preservedElements = append(preservedElements, content.preserved...)
	}
	cloned := &xmlElement{
		Name:                node.Name,
		Attr:                attrs,
		Children:            content.elements,
		Text:                content.text,
		Namespaces:          p.namespaceScope(node),
		PreservedElements:   preservedElements,
		PreservedAttributes: preservedAttrs,
	}
	result := compatibilityFragment{elements: []*xmlElement{cloned}}
	if p.content != nil {
		p.content[cloned] = content.ordered
		result.ordered = []xmlContent{{element: cloned}}
	}
	return result, nil
}

// preserveElement 校验命中PreserveElements的元素属性及内部后代MustUnderstand与属性规则，返回独立深拷贝
// 入参: node 命中的保留元素, scope 已解析的当前兼容性作用域
// 返回: *xmlElement 校验并深拷贝后的保留元素, error 兼容性或取消错误
func (p *compatibilityProcessor) preserveElement(node *xmlElement, scope compatibilityScope) (*xmlElement, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	if err := p.validateAttributes(node, scope, false); err != nil {
		return nil, err
	}
	return p.clonePreservedSubtree(node, scope)
}

// clonePreservedSubtree 递归校验保留子树内部的MustUnderstand与属性规则并构造独立副本，同步映射有序内容索引
// 入参: node 当前保留子树节点, scope 当前作用域
// 返回: *xmlElement 独立副本, error 兼容性或取消错误
func (p *compatibilityProcessor) clonePreservedSubtree(node *xmlElement, scope compatibilityScope) (*xmlElement, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	cloned := &xmlElement{
		Name:                node.Name,
		Attr:                slices.Clone(node.Attr),
		Text:                node.Text,
		Namespaces:          maps.Clone(node.Namespaces),
		PreservedAttributes: slices.Clone(node.PreservedAttributes),
	}
	childMap := make(map[*xmlElement]*xmlElement, len(node.Children))
	if len(node.Children) != 0 {
		cloned.Children = make([]*xmlElement, len(node.Children))
		for i, child := range node.Children {
			copyChild, err := p.preserveDescendant(child, scope)
			if err != nil {
				return nil, err
			}
			cloned.Children[i] = copyChild
			childMap[child] = copyChild
		}
	}
	if len(node.PreservedElements) != 0 {
		cloned.PreservedElements = make([]*xmlElement, len(node.PreservedElements))
		for i, item := range node.PreservedElements {
			copyItem, err := p.preserveDescendant(item, scope)
			if err != nil {
				return nil, err
			}
			cloned.PreservedElements[i] = copyItem
			childMap[item] = copyItem
		}
	}
	if p.content != nil && p.includePreserved {
		if items, ok := p.content[node]; ok {
			mapped := make([]xmlContent, 0, len(items))
			for _, item := range items {
				if item.element != nil {
					if copyChild, exists := childMap[item.element]; exists {
						mapped = append(mapped, xmlContent{element: copyChild})
					}
					continue
				}
				mapped = append(mapped, item)
			}
			p.content[cloned] = mapped
		}
	}
	return cloned, nil
}

// preserveDescendant 校验保留元素内部单个后代节点的MCE规则、控制属性及属性命名空间，返回深拷贝
// 入参: node 后代元素, inherited 祖先兼容性作用域
// 返回: *xmlElement 独立后代副本, error 兼容性或取消错误
func (p *compatibilityProcessor) preserveDescendant(node *xmlElement, inherited compatibilityScope) (*xmlElement, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	if node == nil {
		return nil, fmt.Errorf("%w: nil XML element", ErrInvalid)
	}
	isControl := node.Name.Space == mcNamespace
	isBranch := isControl && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
	scope, err := p.rulesChecked(node, inherited, !isBranch)
	if err != nil {
		return nil, err
	}
	if isControl && node.Name.Local != "AlternateContent" && !isBranch {
		return nil, fmt.Errorf("%w: unexpected MCE element %s", ErrInvalid, node.Name.Local)
	}
	if err := p.validateAttributes(node, scope, isControl); err != nil {
		return nil, err
	}
	if isControl && node.Name.Local == "AlternateContent" {
		var selection compatibilitySelection
		for _, child := range node.Children {
			if err := p.alternative(child, scope, &selection); err != nil {
				return nil, err
			}
		}
		if selection.choices == 0 {
			return nil, fmt.Errorf("%w: AlternateContent requires a Choice", ErrInvalid)
		}
	}
	return p.clonePreservedSubtree(node, scope)
}

// cloneXMLElement 深拷贝被MCE保留的未知扩展元素子树，避免输出与原始树共享可变状态
// 入参: node 原始元素, ctx 取消Context
// 返回: *xmlElement 独立元素副本, error 取消错误
func cloneXMLElement(node *xmlElement, ctx context.Context) (*xmlElement, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if node == nil {
		return nil, nil
	}
	cloned := &xmlElement{
		Name:                node.Name,
		Attr:                slices.Clone(node.Attr),
		Text:                node.Text,
		Namespaces:          maps.Clone(node.Namespaces),
		PreservedAttributes: slices.Clone(node.PreservedAttributes),
	}
	if len(node.Children) != 0 {
		cloned.Children = make([]*xmlElement, len(node.Children))
		for i, child := range node.Children {
			copyChild, err := cloneXMLElement(child, ctx)
			if err != nil {
				return nil, err
			}
			cloned.Children[i] = copyChild
		}
	}
	if len(node.PreservedElements) != 0 {
		cloned.PreservedElements = make([]*xmlElement, len(node.PreservedElements))
		for i, item := range node.PreservedElements {
			copyItem, err := cloneXMLElement(item, ctx)
			if err != nil {
				return nil, err
			}
			cloned.PreservedElements[i] = copyItem
		}
	}
	return cloned, nil
}

// namespaceScope 为解析器标识的只读作用域创建独立副本，避免每个节点重复复制全部绑定
// 入参: node 原始节点，解析完成后不得修改其命名空间作用域
// 返回: map[string]string 本次处理的只读作用域，手工构造节点仍逐节点复制
func (p *compatibilityProcessor) namespaceScope(node *xmlElement) map[string]string {
	if node.namespaceOwner == nil {
		return maps.Clone(node.Namespaces)
	}
	if p.namespaceCopies == nil {
		p.namespaceCopies = make(map[*xmlElement]map[string]string)
	}
	if scope, present := p.namespaceCopies[node.namespaceOwner]; present {
		return scope
	}
	scope := maps.Clone(node.Namespaces)
	p.namespaceCopies[node.namespaceOwner] = scope
	return scope
}

// contents 处理子元素并保留当前数据模型中的聚合文本
// 入参: node 内容所属元素, scope 当前兼容性作用域
// 返回: compatibilityFragment 已处理内容, error 错误信息
func (p *compatibilityProcessor) contents(node *xmlElement, scope compatibilityScope) (compatibilityFragment, error) {
	if p.content != nil {
		return p.orderedContents(node, scope)
	}
	var result compatibilityFragment
	var text strings.Builder
	text.WriteString(node.Text)
	for _, child := range node.Children {
		fragment, err := p.element(child, scope)
		if err != nil {
			return compatibilityFragment{}, err
		}
		result.elements = append(result.elements, fragment.elements...)
		result.preserved = append(result.preserved, fragment.preserved...)
		text.WriteString(fragment.text)
	}
	result.text = text.String()
	return result, nil
}

// rules 校验当前元素的兼容性属性并构造不会修改祖先的作用域
// 入参: node 当前元素, inherited 祖先兼容性作用域
// 返回: compatibilityScope 当前作用域, error 错误信息
func (p *compatibilityProcessor) rules(node *xmlElement, inherited compatibilityScope) (compatibilityScope, error) {
	return p.rulesChecked(node, inherited, true)
}

// rulesChecked 按需校验MustUnderstand并按写时复制构造不修改祖先的作用域，消除无用克隆分配
// 入参: node 当前元素, inherited 祖先兼容性作用域, checkMustUnderstand 是否立即校验MustUnderstand
// 返回: compatibilityScope 当前作用域, error 错误信息
func (p *compatibilityProcessor) rulesChecked(node *xmlElement, inherited compatibilityScope, checkMustUnderstand bool) (compatibilityScope, error) {
	scope := inherited
	var local map[string]bool
	processCloned, preserveElemCloned, preserveAttrCloned := false, false, false
	resetRule := func(rules map[xml.Name]bool, cloned *bool) map[xml.Name]bool {
		for name := range rules {
			if local[name.Space] {
				if !*cloned {
					rules = maps.Clone(rules)
					*cloned = true
				}
				delete(rules, name)
			}
		}
		return rules
	}
	if value, ok := node.attributeNS(mcNamespace, "Ignorable"); ok {
		uris, err := compatibilityPrefixes(node, value)
		if err != nil {
			return scope, err
		}
		if len(uris) > 0 {
			local = make(map[string]bool, len(uris))
			scope.ignorable = maps.Clone(inherited.ignorable)
			if scope.ignorable == nil {
				scope.ignorable = make(map[string]bool, len(uris))
			}
			for _, uri := range uris {
				local[uri] = true
				scope.ignorable[uri] = true
			}
			scope.process = resetRule(scope.process, &processCloned)
			scope.preserveElements = resetRule(scope.preserveElements, &preserveElemCloned)
			scope.preserveAttributes = resetRule(scope.preserveAttributes, &preserveAttrCloned)
		}
	}
	for _, attr := range node.Attr {
		if attr.Name.Space != mcNamespace {
			continue
		}
		switch attr.Name.Local {
		case "Ignorable":
		case "MustUnderstand":
			if checkMustUnderstand {
				if err := p.checkMustUnderstand(node, attr.Value); err != nil {
					return scope, err
				}
			}
		case "ProcessContent", "PreserveElements", "PreserveAttributes":
			for _, word := range compatibilityWords(attr.Value) {
				name, err := compatibilityQName(node, word)
				if err != nil {
					return scope, err
				}
				if !local[name.Space] {
					return scope, fmt.Errorf("%w: %s name %q requires Ignorable on the same element", ErrInvalid, attr.Name.Local, word)
				}
				switch attr.Name.Local {
				case "ProcessContent":
					if !processCloned {
						scope.process = maps.Clone(scope.process)
						if scope.process == nil {
							scope.process = make(map[xml.Name]bool)
						}
						processCloned = true
					}
					scope.process[name] = true
				case "PreserveElements":
					if p.ignorePreservation {
						continue
					}
					if !preserveElemCloned {
						scope.preserveElements = maps.Clone(scope.preserveElements)
						if scope.preserveElements == nil {
							scope.preserveElements = make(map[xml.Name]bool)
						}
						preserveElemCloned = true
					}
					scope.preserveElements[name] = true
				case "PreserveAttributes":
					if p.ignorePreservation {
						continue
					}
					if !preserveAttrCloned {
						scope.preserveAttributes = maps.Clone(scope.preserveAttributes)
						if scope.preserveAttributes == nil {
							scope.preserveAttributes = make(map[xml.Name]bool)
						}
						preserveAttrCloned = true
					}
					scope.preserveAttributes[name] = true
				}
			}
		default:
			return scope, fmt.Errorf("%w: unknown MCE attribute %s", ErrInvalid, attr.Name.Local)
		}
	}
	return scope, nil
}

// checkMustUnderstand 校验MustUnderstand属性中的前缀列表是否全部属于已理解命名空间
// 入参: node 当前元素, value 前缀列表文本
// 返回: error 未声明前缀或未理解命名空间错误
func (p *compatibilityProcessor) checkMustUnderstand(node *xmlElement, value string) error {
	uris, err := compatibilityPrefixes(node, value)
	if err != nil {
		return err
	}
	for _, uri := range uris {
		if !p.understood[uri] {
			return fmt.Errorf("%w: MustUnderstand namespace %q", ErrUnsupported, uri)
		}
	}
	return nil
}

// processes 判断展开名称是否命中内容处理规则
// 入参: name 元素展开名称
// 返回: bool 是否处理被忽略元素的内容
func (s compatibilityScope) processes(name xml.Name) bool {
	return s.process[name] || s.process[xml.Name{Space: name.Space, Local: "*"}]
}

// preservesElement 判断被忽略元素是否命中保留规则
// 入参: name 元素展开名称
// 返回: bool 是否保留该扩展元素
func (s compatibilityScope) preservesElement(name xml.Name) bool {
	return s.preserveElements[name] || s.preserveElements[xml.Name{Space: name.Space, Local: "*"}]
}

// preservesAttribute 判断被忽略属性是否命中保留规则
// 入参: name 属性展开名称
// 返回: bool 是否保留该扩展属性
func (s compatibilityScope) preservesAttribute(name xml.Name) bool {
	return s.preserveAttributes[name] || s.preserveAttributes[xml.Name{Space: name.Space, Local: "*"}]
}

// validateAttributes 零分配校验属性命名空间与MCE控制元素属性规则
// 入参: node 当前元素, scope 当前兼容性作用域, control 是否为MCE控制元素
// 返回: error 错误信息
func (p *compatibilityProcessor) validateAttributes(node *xmlElement, scope compatibilityScope, control bool) error {
	if control {
		if err := compatibilityNoXMLContext(node); err != nil {
			return err
		}
	}
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name.Space == "" && attr.Name.Local == "xmlns" || attr.Name.Space == mcNamespace {
			continue
		}
		if attr.Name.Space == "" {
			if control && (node.Name.Local != "Choice" || attr.Name.Local != "Requires") {
				return fmt.Errorf("%w: unqualified attribute %s on MCE %s", ErrInvalid, attr.Name.Local, node.Name.Local)
			}
		} else if control {
			if !scope.ignorable[attr.Name.Space] {
				if attr.Name.Space == xmlNamespace || p.understood[attr.Name.Space] {
					return fmt.Errorf("%w: attribute {%s}%s on MCE %s", ErrInvalid, attr.Name.Space, attr.Name.Local, node.Name.Local)
				}
				return fmt.Errorf("%w: attribute namespace %q", ErrUnsupported, attr.Name.Space)
			}
		} else if !p.understood[attr.Name.Space] && !scope.ignorable[attr.Name.Space] {
			return fmt.Errorf("%w: attribute namespace %q", ErrUnsupported, attr.Name.Space)
		}
	}
	return nil
}

// attributesWithPreserved 校验属性命名空间并分别返回消费属性副本与命中的保留扩展属性副本
// 入参: node 当前元素, scope 当前兼容性作用域
// 返回: []xml.Attr 消费属性副本, []xml.Attr 保留扩展属性副本, error 错误信息
func (p *compatibilityProcessor) attributesWithPreserved(node *xmlElement, scope compatibilityScope) ([]xml.Attr, []xml.Attr, error) {
	var result []xml.Attr
	var preserved []xml.Attr
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name.Space == "" && attr.Name.Local == "xmlns" {
			result = append(result, attr)
			continue
		}
		if attr.Name.Space == mcNamespace {
			continue
		}
		if attr.Name.Space != "" && !p.understood[attr.Name.Space] {
			if scope.ignorable[attr.Name.Space] {
				if !p.ignorePreservation && scope.preservesAttribute(attr.Name) {
					preserved = append(preserved, attr)
				}
				continue
			}
			return nil, nil, fmt.Errorf("%w: attribute namespace %q", ErrUnsupported, attr.Name.Space)
		}
		result = append(result, attr)
	}
	return result, preserved, nil
}

// alternate 校验候选分支并处理首个可用选择或回退内容
// 入参: node AlternateContent元素, scope 当前兼容性作用域
// 返回: compatibilityFragment 被选择的内容，无可用分支时为空, error 错误信息
func (p *compatibilityProcessor) alternate(node *xmlElement, scope compatibilityScope) (compatibilityFragment, error) {
	if err := p.validateAttributes(node, scope, true); err != nil {
		return compatibilityFragment{}, err
	}
	if len(compatibilityWords(node.Text)) != 0 {
		return compatibilityFragment{}, fmt.Errorf("%w: text directly inside AlternateContent", ErrInvalid)
	}
	var selection compatibilitySelection
	for _, child := range node.Children {
		if err := p.alternative(child, scope, &selection); err != nil {
			return compatibilityFragment{}, err
		}
	}
	if selection.choices == 0 {
		return compatibilityFragment{}, fmt.Errorf("%w: AlternateContent requires a Choice", ErrInvalid)
	}
	var result compatibilityFragment
	if selection.selected != nil {
		var err error
		result, err = p.contents(selection.selected, selection.scope)
		if err != nil {
			return compatibilityFragment{}, err
		}
	}
	if len(selection.preserved) != 0 {
		preserved := make([]*xmlElement, 0, len(selection.preserved)+len(result.preserved))
		preserved = append(preserved, selection.preserved...)
		preserved = append(preserved, result.preserved...)
		result.preserved = preserved
		if p.content != nil && p.includePreserved {
			ordered := make([]xmlContent, 0, len(selection.preserved)+len(result.ordered))
			for _, item := range selection.preserved {
				ordered = append(ordered, xmlContent{element: item})
			}
			ordered = append(ordered, result.ordered...)
			result.ordered = ordered
		}
	}
	return result, nil
}

// alternative 校验候选分支的属性与顺序，仅对选中分支校验MustUnderstand且不解释未选分支内部内容
// 入参: node 当前候选或可忽略包装, inherited 祖先作用域, selection 选择状态
// 返回: error 错误信息
func (p *compatibilityProcessor) alternative(node *xmlElement, inherited compatibilityScope, selection *compatibilitySelection) error {
	if node == nil {
		return fmt.Errorf("%w: nil AlternateContent child", ErrInvalid)
	}
	branch := node.Name.Space == mcNamespace && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
	scope, err := p.rulesChecked(node, inherited, !branch)
	if err != nil {
		return err
	}
	if !p.understood[node.Name.Space] {
		if !scope.ignorable[node.Name.Space] {
			return fmt.Errorf("%w: AlternateContent child namespace %q", ErrUnsupported, node.Name.Space)
		}
		if !scope.processes(node.Name) {
			if !p.ignorePreservation && scope.preservesElement(node.Name) {
				preserved, err := p.preserveElement(node, scope)
				if err != nil {
					return err
				}
				selection.preserved = append(selection.preserved, preserved)
			}
			return nil
		}
		if err := compatibilityNoXMLContext(node); err != nil {
			return err
		}
		if len(compatibilityWords(node.Text)) != 0 {
			return fmt.Errorf("%w: processed text directly inside AlternateContent", ErrInvalid)
		}
		for _, child := range node.Children {
			if err := p.alternative(child, scope, selection); err != nil {
				return err
			}
		}
		return nil
	}
	if !branch {
		return fmt.Errorf("%w: unexpected AlternateContent child %s", ErrInvalid, node.Name.Local)
	}
	if err := p.validateAttributes(node, scope, true); err != nil {
		return err
	}
	selectable := true
	if node.Name.Local == "Choice" {
		if selection.fallback {
			return fmt.Errorf("%w: Choice follows Fallback", ErrInvalid)
		}
		selection.choices++
		requires, ok := node.attributeNS("", "Requires")
		if !ok {
			return fmt.Errorf("%w: Choice requires an unqualified Requires attribute", ErrInvalid)
		}
		uris, err := compatibilityPrefixes(node, requires)
		if err != nil {
			return err
		}
		if len(uris) == 0 {
			return fmt.Errorf("%w: empty Choice Requires", ErrInvalid)
		}
		for _, uri := range uris {
			if !p.understood[uri] {
				selectable = false
			}
		}
	} else {
		if selection.fallback || selection.choices == 0 {
			return fmt.Errorf("%w: Fallback must occur once after all Choices", ErrInvalid)
		}
		selection.fallback = true
	}
	if selection.selected == nil && selectable {
		if value, ok := node.attributeNS(mcNamespace, "MustUnderstand"); ok {
			if err := p.checkMustUnderstand(node, value); err != nil {
				return err
			}
		}
		selection.selected = node
		selection.scope = scope
	}
	return nil
}

// compatibilityPrefixes 将当前元素上的前缀列表解析为命名空间URI
// 入参: node 提供命名空间作用域的元素, value XML空白分隔的前缀列表
// 返回: []string 命名空间URI列表, error 未声明前缀或词法错误
func compatibilityPrefixes(node *xmlElement, value string) ([]string, error) {
	var result []string
	for _, prefix := range compatibilityWords(value) {
		uri, ok := node.Namespaces[prefix]
		if !xmlNCName(prefix) || !ok || uri == "" || prefix == "xmlns" {
			return nil, fmt.Errorf("%w: invalid or undeclared MCE prefix %q", ErrInvalid, prefix)
		}
		result = append(result, uri)
	}
	return result, nil
}

// compatibilityQName 解析元素或属性规则中的带前缀QName及命名空间通配符，禁止无前缀默认命名空间绑定
// 入参: node 提供命名空间作用域的元素, value 单个限定名
// 返回: xml.Name 展开名称，星号仅允许作为带前缀名称的本地部分, error 错误信息
func compatibilityQName(node *xmlElement, value string) (xml.Name, error) {
	prefix, local, qualified := strings.Cut(value, ":")
	if !qualified || !xmlNCName(prefix) || local != "*" && !xmlNCName(local) {
		return xml.Name{}, fmt.Errorf("%w: invalid MCE QName %q", ErrInvalid, value)
	}
	uri, ok := node.Namespaces[prefix]
	if !ok || uri == "" || prefix == "xmlns" {
		return xml.Name{}, fmt.Errorf("%w: undeclared MCE QName prefix %q", ErrInvalid, prefix)
	}
	return xml.Name{Space: uri, Local: local}, nil
}

// compatibilityWords 按第一版MCE规则分割XML空白，不接受其他Unicode空白作为分隔符
// 入参: value 属性值或待检查文本
// 返回: []string 去除XML空白后的词项
func compatibilityWords(value string) []string {
	return strings.FieldsFunc(value, func(r rune) bool { return r == ' ' || r == '\t' || r == '\r' || r == '\n' })
}

// compatibilityNoXMLContext 检查移除兼容性包装时禁止出现的xml:lang或xml:space属性
// 入参: node 将被移除的元素
// 返回: error 存在xml:lang或xml:space时的结构错误
func compatibilityNoXMLContext(node *xmlElement) error {
	for _, name := range []string{"lang", "space"} {
		if _, ok := node.attributeNS(xmlNamespace, name); ok {
			return fmt.Errorf("%w: xml:%s on MCE or ProcessContent wrapper", ErrInvalid, name)
		}
	}
	return nil
}

// orderedContents 在内容索引启用时保留MCE过滤后的词元顺序，不把包装中的文本移到其他元素前后
// 入参: node 当前元素, scope 当前兼容性作用域
// 返回: compatibilityFragment 过滤后的有序内容, error 索引或兼容性错误
func (p *compatibilityProcessor) orderedContents(node *xmlElement, scope compatibilityScope) (compatibilityFragment, error) {
	items, present := p.content[node]
	if !present {
		return compatibilityFragment{}, fmt.Errorf("%w: missing ordered XML content", ErrInvalid)
	}
	var result compatibilityFragment
	var text strings.Builder
	for _, item := range items {
		if err := checkContext(p.context); err != nil {
			return compatibilityFragment{}, err
		}
		if item.element == nil {
			result.ordered = append(result.ordered, item)
			if data, ok := item.token.(xml.CharData); ok {
				text.Write(data)
			}
			continue
		}
		fragment, err := p.element(item.element, scope)
		if err != nil {
			return compatibilityFragment{}, err
		}
		result.elements = append(result.elements, fragment.elements...)
		result.preserved = append(result.preserved, fragment.preserved...)
		result.ordered = append(result.ordered, fragment.ordered...)
		text.WriteString(fragment.text)
	}
	result.text = text.String()
	return result, nil
}

// canonicalXML 按C14N1.0、Exclusive C14N1.0或C14N1.1生成文档或单个子树的UTF-8字节，遵循OPC输入限制并拒绝DTD与相对命名空间
// 入参: data XML原始字节, options 输入、算法、输出及取消选项
// 返回: []byte 独立规范化数据, error 解析、选择、命名空间或预算错误，失败无部分结果
func canonicalXML(data []byte, options canonicalXMLOptions) ([]byte, error) {
	options.limits = mergeLimits(DefaultLimits(), options.limits)
	if err := validateLimits(options.limits); err != nil {
		return nil, err
	}
	limit := min(options.limits.MaxPartBytes, options.limits.MaxPackageBytes)
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("%w: canonical XML input bytes", ErrLimit)
	}
	if options.maxBytes == 0 {
		options.maxBytes = limit
	}
	if options.maxBytes < 0 {
		return nil, fmt.Errorf("%w: canonical XML output limit", ErrInvalid)
	}
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	var output bytes.Buffer
	w := canonicalWriter{options: options, output: packageOutput{writer: &output, context: options.context, limit: min(limit, options.maxBytes)}}
	if _, err := decodeXMLVisit(data, options.limits, w.token); err != nil {
		return nil, err
	}
	if options.selectElement != nil && !w.selected {
		return nil, fmt.Errorf("%w: canonical element not found", ErrInvalid)
	}
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// token 按已校验词元输出C14N1.0、Exclusive C14N1.0或C14N1.1，不将显示层的属性默认值或MCE改写用于摘要
// 入参: token 保留原始前缀的词元, node 当前元素或词元所属元素
// 返回: error 选择、命名空间、取消或输出错误
func (w *canonicalWriter) token(token xml.Token, node *xmlElement) error {
	if err := checkContext(w.options.context); err != nil {
		return err
	}
	if _, end := token.(xml.EndElement); !end {
		w.nodes++
		if w.nodes > w.options.limits.MaxXMLNodes {
			return fmt.Errorf("%w: canonical XML token count", ErrLimit)
		}
	}
	switch token := token.(type) {
	case xml.StartElement:
		for _, attr := range token.Attr {
			if attr.Name.Space != "xmlns" && attr.Name != (xml.Name{Local: "xmlns"}) {
				continue
			}
			namespace := attr.Value
			if namespace != "" {
				uri, err := opcURI(namespace)
				if err != nil || uri.Scheme == "" {
					return fmt.Errorf("%w: relative or invalid canonical namespace", ErrInvalid)
				}
			}
		}
		w.path = append(w.path, node.Name)
		selected := w.options.selectElement != nil && w.options.selectElement(node, w.path)
		if selected {
			if w.selected {
				return fmt.Errorf("%w: multiple canonical elements", ErrInvalid)
			}
			w.selected, w.selectedDepth = true, len(w.path)
		}
		if w.options.selectElement == nil || w.selectedDepth != 0 {
			if err := w.start(token, node, selected); err != nil {
				return err
			}
		}
		w.ancestors = append(w.ancestors, node)
	case xml.EndElement:
		if w.options.selectElement == nil || w.selectedDepth != 0 {
			if err := w.write("</" + canonicalQName(token.Name) + ">"); err != nil {
				return err
			}
			w.rendered = w.rendered[:len(w.rendered)-1]
		}
		if len(w.path) == w.selectedDepth {
			w.selectedDepth = 0
		}
		if len(w.path) == 1 {
			w.rootPassed = true
		}
		w.path = w.path[:len(w.path)-1]
		w.ancestors = w.ancestors[:len(w.ancestors)-1]
	case xml.CharData:
		if len(w.path) != 0 && (w.options.selectElement == nil || w.selectedDepth != 0) {
			return w.escaped(string(token), false)
		}
	case xml.Comment:
		if w.options.comments && (w.options.selectElement == nil || w.selectedDepth != 0) {
			return w.misc("<!--" + canonicalLineFeeds.Replace(string(token)) + "-->")
		}
	case xml.ProcInst:
		if token.Target != "xml" && (w.options.selectElement == nil || w.selectedDepth != 0) {
			value := "<?" + token.Target
			if len(token.Inst) != 0 {
				value += " " + canonicalLineFeeds.Replace(string(token.Inst))
			}
			return w.misc(value + "?>")
		}
	}
	return nil
}

// start 按C14N1.0、Exclusive C14N1.0或C14N1.1规则输出起始标签、命名空间声明及排序属性
// 入参: token 起始词元, node 当前元素, selected 是否为选定子树根
// 返回: error 名称、URI合并或输出错误
func (w *canonicalWriter) start(token xml.StartElement, node *xmlElement, selected bool) error {
	if err := w.write("<" + canonicalQName(token.Name)); err != nil {
		return err
	}
	var parent map[string]string
	if len(w.rendered) != 0 {
		parent = w.rendered[len(w.rendered)-1]
	}
	var prefixes []string
	var nextRendered map[string]string
	if w.options.exclusive {
		visiblyUtilized := map[string]bool{token.Name.Space: true}
		for _, attr := range token.Attr {
			if attr.Name.Space != "" && attr.Name.Space != "xmlns" && attr.Name.Space != "xml" {
				visiblyUtilized[attr.Name.Space] = true
			}
		}
		nextRendered = make(map[string]string, len(parent)+len(node.Namespaces))
		maps.Copy(nextRendered, parent)
		if visiblyUtilized[""] || w.options.inclusive[""] {
			defaultNS := node.Namespaces[""]
			if defaultNS != parent[""] {
				prefixes = append(prefixes, "")
				nextRendered[""] = defaultNS
			}
		}
		for prefix, namespace := range node.Namespaces {
			if prefix == "" || prefix == "xml" {
				continue
			}
			if (visiblyUtilized[prefix] || w.options.inclusive[prefix]) && namespace != parent[prefix] {
				prefixes = append(prefixes, prefix)
				nextRendered[prefix] = namespace
			}
		}
	} else {
		nextRendered = node.Namespaces
		for prefix, namespace := range node.Namespaces {
			if prefix != "xml" && namespace != parent[prefix] {
				prefixes = append(prefixes, prefix)
			}
		}
	}
	slices.Sort(prefixes)
	for _, prefix := range prefixes {
		name := xml.Name{Local: "xmlns"}
		if prefix != "" {
			name = xml.Name{Space: "xmlns", Local: prefix}
		}
		if err := w.attribute(name, nextRendered[prefix]); err != nil {
			return err
		}
	}
	var attributes []canonicalAttribute
	inherited := make(map[string]string)
	ancestorBase, hasBase := "", false
	if selected && !w.options.exclusive {
		for _, ancestor := range w.ancestors {
			for _, attr := range ancestor.Attr {
				if attr.Name.Space != xmlNamespace {
					continue
				}
				if !w.options.version11 {
					inherited[attr.Name.Local] = attr.Value
					continue
				}
				switch attr.Name.Local {
				case "lang", "space":
					inherited[attr.Name.Local] = attr.Value
				case "base":
					var err error
					ancestorBase, err = c14n11JoinURI(ancestorBase, attr.Value)
					if err != nil {
						return err
					}
					hasBase = true
				}
			}
		}
	}
	for _, attr := range token.Attr {
		if attr.Name.Space == "xmlns" || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		name, err := xmlExpandedName(node.Namespaces, attr.Name, false)
		if err != nil {
			return err
		}
		value := attr.Value
		if selected && !w.options.exclusive && w.options.version11 && name == (xml.Name{Space: xmlNamespace, Local: "base"}) && hasBase {
			value, err = c14n11JoinURI(ancestorBase, value)
			if err != nil {
				return err
			}
			hasBase = false
			if value == "" {
				continue
			}
		}
		attributes = append(attributes, canonicalAttribute{attr.Name, name, value})
		if name.Space == xmlNamespace {
			delete(inherited, name.Local)
		}
	}
	if selected && !w.options.exclusive && w.options.version11 && hasBase && ancestorBase != "" {
		attributes = append(attributes, canonicalAttribute{xml.Name{Space: "xml", Local: "base"}, xml.Name{Space: xmlNamespace, Local: "base"}, ancestorBase})
	}
	for local, value := range inherited {
		attributes = append(attributes, canonicalAttribute{xml.Name{Space: "xml", Local: local}, xml.Name{Space: xmlNamespace, Local: local}, value})
	}
	slices.SortFunc(attributes, func(a, b canonicalAttribute) int {
		if order := cmp.Compare(a.name.Space, b.name.Space); order != 0 {
			return order
		}
		return cmp.Compare(a.name.Local, b.name.Local)
	})
	for _, attr := range attributes {
		if err := w.attribute(attr.raw, attr.value); err != nil {
			return err
		}
	}
	w.rendered = append(w.rendered, nextRendered)
	return w.write(">")
}

// canonicalQName 返回原始前缀对应的QName，不选择别名或生成新前缀
// 入参: name 原始XML名称，Space字段为前缀
// 返回: string QName
func canonicalQName(name xml.Name) string {
	if name.Space == "" {
		return name.Local
	}
	return name.Space + ":" + name.Local
}

// attribute 以双引号及C14N字符引用输出单个属性或命名空间声明
// 入参: name 原始QName, value 已完成XML输入规范化的值
// 返回: error 输出错误
func (w *canonicalWriter) attribute(name xml.Name, value string) error {
	if err := w.write(" " + canonicalQName(name) + "=\""); err != nil {
		return err
	}
	if err := w.escaped(value, true); err != nil {
		return err
	}
	return w.write("\"")
}

// escaped 按C14N规则逐段转义，输出超限前不分配完整扩张字符串
// 入参: value XML解析后的内容, attribute 是否为属性值
// 返回: error 输出或取消错误
func (w *canonicalWriter) escaped(value string, attribute bool) error {
	start := 0
	for i := range len(value) {
		escape := ""
		switch value[i] {
		case '&':
			escape = "&amp;"
		case '<':
			escape = "&lt;"
		case '>':
			if !attribute {
				escape = "&gt;"
			}
		case '"':
			if attribute {
				escape = "&quot;"
			}
		case '\t':
			if attribute {
				escape = "&#x9;"
			}
		case '\n':
			if attribute {
				escape = "&#xA;"
			}
		case '\r':
			escape = "&#xD;"
		}
		if escape != "" {
			if err := w.write(value[start:i]); err != nil {
				return err
			}
			if err := w.write(escape); err != nil {
				return err
			}
			start = i + 1
		}
	}
	return w.write(value[start:])
}

// misc 按处理指令或注释相对文档根的位置添加规范化换行
// 入参: value 完整标记
// 返回: error 输出错误
func (w *canonicalWriter) misc(value string) error {
	if len(w.path) == 0 && w.rootPassed {
		if err := w.write("\n"); err != nil {
			return err
		}
	}
	if err := w.write(value); err != nil {
		return err
	}
	if len(w.path) == 0 && !w.rootPassed {
		return w.write("\n")
	}
	return nil
}

// write 在统一输出预算及取消检查下写入规范化片段
// 入参: value 输出片段
// 返回: error 输出错误
func (w *canonicalWriter) write(value string) error {
	_, err := io.WriteString(&w.output, value)
	return err
}
