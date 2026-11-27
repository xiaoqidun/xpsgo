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
	"maps"
	"slices"
	"strconv"
	"strings"
)

const (
	// PrintSelectionUnknown 表示未知的Feature选择方式
	PrintSelectionUnknown PrintSelection = iota
	// PrintSelectionOne 表示同一Feature仅允许选择一个Option
	PrintSelectionOne
	// PrintSelectionMany 表示同一Feature允许同时选择多个Option
	PrintSelectionMany
)

const (
	// PrintScopeUnknown 表示未知打印票据作用域
	PrintScopeUnknown PrintScope = iota
	// PrintScopeJob 表示作业级打印票据作用域
	PrintScopeJob
	// PrintScopeDocument 表示文档级打印票据作用域
	PrintScopeDocument
	// PrintScopePage 表示页面级打印票据作用域
	PrintScopePage
)

// printFrameworkNS 等常量定义Print Schema命名空间、关键字与票据内容类型
const (
	printFrameworkNS   = "http://schemas.microsoft.com/windows/2003/08/printing/printschemaframework"
	printFramework2NS  = "http://schemas.microsoft.com/windows/2013/12/printing/printschemaframework2"
	printKeywordsNS    = "http://schemas.microsoft.com/windows/2003/08/printing/printschemakeywords"
	printKeywordsV11NS = "http://schemas.microsoft.com/windows/2013/05/printing/printschemakeywordsv11"
	printKeywordsV12NS = "http://schemas.microsoft.com/windows/2013/12/printing/printschemakeywordsv12"
	printKeywords2NS   = "http://schemas.microsoft.com/windows/2015/02/printing/printschemakeywords2"
	printValueNS       = "http://www.w3.org/2001/XMLSchema"
	printTicketType    = "application/vnd.ms-printing.printticket+xml"
	printTicket2Type   = "application/vnd.ms-printschematicket+xml"
	printBuilderNS     = "http://schemas.xpsgo.dev/printing/keywords"
)

const (
	// PrintSettingUnknown 表示未知的Print Schema框架元素类型
	PrintSettingUnknown PrintSettingKind = iota
	// PrintSettingFeature 表示Feature元素
	PrintSettingFeature
	// PrintSettingOption 表示Option元素
	PrintSettingOption
	// PrintSettingParameterInit 表示ParameterInit元素
	PrintSettingParameterInit
	// PrintSettingParameterRef 表示ParameterRef元素
	PrintSettingParameterRef
	// PrintSettingProperty 表示Property元素
	PrintSettingProperty
	// PrintSettingScoredProperty 表示ScoredProperty元素
	PrintSettingScoredProperty
	// PrintSettingValue 表示Value元素
	PrintSettingValue
	// PrintSettingParameterDef 表示ParameterDef元素
	PrintSettingParameterDef
)

const (
	// PrintConstraintUnknown 表示未声明选项约束状态
	PrintConstraintUnknown PrintConstraint = iota
	// PrintConstraintNone 表示选项在当前配置下无约束
	PrintConstraintNone
	// PrintConstraintSettings 表示选项受当前打印票据设置约束
	PrintConstraintSettings
	// PrintConstraintAdministrator 表示选项受管理员策略约束
	PrintConstraintAdministrator
	// PrintConstraintDevice 表示选项受打印设备硬件配置约束
	PrintConstraintDevice
)

const (
	// printDocumentTicket 表示打印票据文档类别
	printDocumentTicket printDocumentMode = iota
	// printDocumentCapabilities 表示PrintCapabilities能力文档类别
	printDocumentCapabilities
	// printDocumentDeviceCapabilities 表示PrintDeviceCapabilities设备能力文档类别
	printDocumentDeviceCapabilities
)

// printSettingNames 保存Framework元素名称，索引对应公开元素类型
var printSettingNames = [...]string{"", "Feature", "Option", "ParameterInit", "ParameterRef", "Property", "ScoredProperty", "Value", "ParameterDef"}

// printConstraintNames 保存约束枚举对应的关键字名称，Unknown表示未声明
var printConstraintNames = [...]string{"", "None", "PrintTicketSettings", "AdminSettings", "DeviceSettings"}

// PrintSelection 表示Feature允许同时选择一个或多个Option
type PrintSelection uint8

// PrintScope 表示打印票据所关联的作业、文档或页面层级
type PrintScope uint8

// PrintTicket 保存打印票据的关联位置、内容类型及独立数据，不推断设备能力或合并打印参数
// OpenXPS允许实现自定义票据格式，Data不限定为XML
type PrintTicket struct {
	Source      string
	Part        string
	Scope       PrintScope
	ContentType string
	Data        []byte
}

// PrintSettingKind 表示打印票据及设备能力文档的Framework元素类型
type PrintSettingKind uint8

// PrintConstraint 表示Option在当前设备配置下的选择约束
type PrintConstraint uint8

// PrintSettings 保存Framework版本、可选PDC变更标识及打印票据根元素列表
type PrintSettings struct {
	Version              uint32
	CapabilitiesChangeID string
	Elements             []PrintSetting
}

// PrintSetting 保存展开后的关键字名称、子元素或值，不依赖输入XML的前缀拼写
// Option允许省略Name，只有Value元素使用Value，Constraint仅适用于能力文档的Option
// Default与HasDefault保存Print Schema v2选项的psf2:default声明
type PrintSetting struct {
	Kind       PrintSettingKind
	Name       xml.Name
	Children   []PrintSetting
	Value      *PrintValue
	Constraint PrintConstraint
	Default    bool
	HasDefault bool
}

// PrintValue 保存值类型和字符数据，QName保存QName值或QName参数字符串默认值中的展开名称
// 空Type采用xs:string，空字符数据允许表示未赋值，字符串或QName类型的非空QName优先用于编码
type PrintValue struct {
	Type  xml.Name
	Text  string
	QName xml.Name
}

// PrintSettingsOptions 设置资源预算及票据关联层级，参数算术默认最多处理4096位数字
// Option匹配默认最多执行100000次比较，预算不足返回ErrLimit，不改为近似匹配
// 非Unknown层级会在Framework校验前移除更宽作用域的根设置，不推断私有设备约束
type PrintSettingsOptions struct {
	Limits               Limits
	Scope                PrintScope
	MaxNumericDigits     int
	MaxOptionComparisons int
}

// printSettingsConfig 保存已校验的打印设置预算、关联层级、忽略策略与取消Context
type printSettingsConfig struct {
	PrintSettingsOptions
	context           context.Context
	ignoreUnsupported bool
}

// printSettingsBuilder 将展开名称绑定到确定性前缀，并约束生成结构的规模
type printSettingsBuilder struct {
	options      printSettingsConfig
	framework    string
	prefixes     map[string]string
	scope        map[string]string
	nodes        int
	bytes        int64
	nextPrefix   int
	capabilities bool
}

// printDocumentMode 表示内部校验与编码的Print Schema文档类别
type printDocumentMode uint8

// printPrefixKey 标识同一父级作用域下同类元素的命名空间与去前缀关键字族
type printPrefixKey struct {
	kind  PrintSettingKind
	space string
	local string
}

// String 返回Feature选择方式的名称
// 返回: string 选择方式名称
func (s PrintSelection) String() string {
	switch s {
	case PrintSelectionUnknown:
		return "Unknown"
	case PrintSelectionOne:
		return "PickOne"
	case PrintSelectionMany:
		return "PickMany"
	default:
		return fmt.Sprintf("PrintSelection(%d)", s)
	}
}

// String 返回打印票据作用域的名称
// 返回: string 作用域名称
func (s PrintScope) String() string {
	switch s {
	case PrintScopeUnknown:
		return "Unknown"
	case PrintScopeJob:
		return "Job"
	case PrintScopeDocument:
		return "Document"
	case PrintScopePage:
		return "Page"
	default:
		return fmt.Sprintf("PrintScope(%d)", s)
	}
}

// String 返回Framework元素类型的名称
// 返回: string 元素类型名称
func (k PrintSettingKind) String() string {
	if k == PrintSettingUnknown {
		return "Unknown"
	}
	if int(k) < len(printSettingNames) {
		return printSettingNames[k]
	}
	return fmt.Sprintf("PrintSettingKind(%d)", k)
}

// String 返回Option选择约束的名称
// 返回: string 约束状态名称
func (c PrintConstraint) String() string {
	if c == PrintConstraintUnknown {
		return "Unknown"
	}
	if int(c) < len(printConstraintNames) {
		return printConstraintNames[c]
	}
	return fmt.Sprintf("PrintConstraint(%d)", c)
}

// DefaultPrintSettingsOptions 返回默认的打印设置解析与校验参数
// 返回: PrintSettingsOptions 打印设置参数
func DefaultPrintSettingsOptions() PrintSettingsOptions {
	return PrintSettingsOptions{Limits: DefaultLimits(), MaxNumericDigits: 4096, MaxOptionComparisons: 100000}
}

// printFrameworkSpace 判断命名空间是否属于Print Schema v1或v2框架命名空间
// 入参: space 展开命名空间URI
// 返回: bool 是否为框架命名空间
func printFrameworkSpace(space string) bool {
	return space == printFrameworkNS || space == printFramework2NS
}

// printPublicKeywordSpace 判断命名空间是否属于Print Schema公共关键字命名空间（v1.0/v1.1/v1.2/v2）
// 入参: space 展开命名空间URI
// 返回: bool 是否为公共关键字命名空间
func printPublicKeywordSpace(space string) bool {
	return space == printKeywordsNS || space == printKeywordsV11NS || space == printKeywordsV12NS || space == printKeywords2NS
}

// printCanonicalKey 将公共关键字与框架命名空间分别归并到规范命名空间用于合并与查重，私有命名空间保持原样
// 入参: name 展开关键字名称
// 返回: xml.Name 规范化后的展开名称
func printCanonicalKey(name xml.Name) xml.Name {
	if printPublicKeywordSpace(name.Space) {
		return xml.Name{Space: printKeywordsNS, Local: name.Local}
	}
	if printFrameworkSpace(name.Space) {
		return xml.Name{Space: printFrameworkNS, Local: name.Local}
	}
	return name
}

// Selection 返回Feature的选择方式，能力文档省略声明时默认为PickOne
// 返回: PrintSelection 选择方式, error 元素或属性错误
func (p PrintSetting) Selection() (PrintSelection, error) {
	if p.Kind != PrintSettingFeature {
		return PrintSelectionUnknown, fmt.Errorf("%w: selection on non-Feature", ErrInvalid)
	}
	for _, property := range p.Children {
		if property.Kind != PrintSettingProperty || !printFrameworkSpace(property.Name.Space) || property.Name.Local != "SelectionType" {
			continue
		}
		value, err := printCommonValue(property)
		if err != nil || value.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || !printPublicKeywordSpace(value.QName.Space) {
			return PrintSelectionUnknown, fmt.Errorf("%w: print SelectionType value", ErrInvalid)
		}
		switch value.QName.Local {
		case "PickOne":
			return PrintSelectionOne, nil
		case "PickMany":
			return PrintSelectionMany, nil
		default:
			return PrintSelectionUnknown, fmt.Errorf("%w: print SelectionType keyword", ErrInvalid)
		}
	}
	return PrintSelectionOne, nil
}

// Identity 返回Option是否声明为恒等选项，省略时默认为false
// 返回: bool 恒等选项声明, error 元素或属性错误
func (p PrintSetting) Identity() (bool, error) {
	if p.Kind != PrintSettingOption {
		return false, fmt.Errorf("%w: identity on non-Option", ErrInvalid)
	}
	for _, property := range p.Children {
		if property.Kind != PrintSettingProperty || !printFrameworkSpace(property.Name.Space) || property.Name.Local != "IdentityOption" {
			continue
		}
		value, err := printCommonValue(property)
		if err != nil || value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
			return false, fmt.Errorf("%w: print IdentityOption value", ErrInvalid)
		}
		switch value.Text {
		case "True":
			return true, nil
		case "False":
			return false, nil
		default:
			return false, fmt.Errorf("%w: print IdentityOption keyword", ErrInvalid)
		}
	}
	return false, nil
}

// printCommonValue 读取公共Property唯一的直接标量Value
// 入参: property 公共属性
// 返回: *PrintValue 值, error 结构错误
func printCommonValue(property PrintSetting) (*PrintValue, error) {
	if len(property.Children) != 1 || property.Children[0].Kind != PrintSettingValue || property.Children[0].Value == nil {
		return nil, fmt.Errorf("%w: print common property structure", ErrInvalid)
	}
	if property.Children[0].Value.Type == (xml.Name{}) {
		value := *property.Children[0].Value
		value.Type = xml.Name{Space: printValueNS, Local: "string"}
		return &value, nil
	}
	return property.Children[0].Value, nil
}

// validatePrintCommon 检查公共关键字的位置、文档类别及基本值，不约束私有同名属性
// 入参: settings 当前层级内容, parent 父元素类型，根使用Unknown, capabilities 是否为能力文档
// 返回: error 公共关键字错误
func validatePrintCommon(settings []PrintSetting, parent PrintSettingKind, capabilities bool) error {
	for _, setting := range settings {
		if setting.Kind == PrintSettingProperty {
			selection := printFrameworkSpace(setting.Name.Space) && setting.Name.Local == "SelectionType"
			identity := printFrameworkSpace(setting.Name.Space) && setting.Name.Local == "IdentityOption"
			displayUI := printPublicKeywordSpace(setting.Name.Space) && setting.Name.Local == "DisplayUI"
			displayName := printPublicKeywordSpace(setting.Name.Space) && setting.Name.Local == "DisplayName"
			if selection || identity || displayUI || displayName {
				if !capabilities || selection && parent != PrintSettingFeature || identity && parent != PrintSettingOption {
					return fmt.Errorf("%w: print common property context", ErrInvalid)
				}
				value, err := printCommonValue(setting)
				if err != nil {
					return err
				}
				if selection {
					if _, err := (PrintSetting{Kind: PrintSettingFeature, Children: []PrintSetting{setting}}).Selection(); err != nil {
						return err
					}
				} else {
					if value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
						return fmt.Errorf("%w: print common property value type", ErrInvalid)
					}
					if identity && value.Text != "True" && value.Text != "False" || displayUI && value.Text != "Show" && value.Text != "Hide" {
						return fmt.Errorf("%w: print common property value", ErrInvalid)
					}
				}
			}
		}
		if err := validatePrintCommon(setting.Children, setting.Kind, capabilities); err != nil {
			return err
		}
	}
	return nil
}

// PrintTicket 读取指定固定布局部件的打印票据，没有关联时返回nil
// 入参: ctx 取消Context，nil采用Background, source 源部件名称，空字符串表示当前文档序列
// 返回: *PrintTicket 独立票据数据, error 关联、读取、资源或取消错误
func (r *Reader) PrintTicket(ctx context.Context, source string) (*PrintTicket, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if source == "" {
		source = r.sequence
	}
	return r.readPrintTicket(ctx, source)
}

// PrintTicketHierarchy 依次读取指定页面的作业、文档及页面票据，省略没有票据的层级
// 关联层级不等同于参数合并，具体打印语义由票据格式和打印设备决定
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页号
// 返回: []PrintTicket 独立票据数据, error 序号、关联、读取、资源或取消错误
func (r *Reader) PrintTicketHierarchy(ctx context.Context, pageIndex int) ([]PrintTicket, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readPrintTicketHierarchyOptions(pageIndex, r.limits, ctx)
}

// readPrintTicketHierarchyOptions 按调用方和阅读器的共同预算读取票据链，在读取步骤检查取消
// 入参: index 页面序号, limits 本次读取预算, ctx 取消Context
// 返回: []PrintTicket 独立票据链, error 状态、关联、读取、资源或取消错误
func (r *Reader) readPrintTicketHierarchyOptions(index int, limits Limits, ctx context.Context) ([]PrintTicket, error) {
	if r.closed {
		return nil, ErrClosed
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.pages) {
		return nil, fmt.Errorf("%w: page index out of range: %d", ErrInvalid, index)
	}
	page := r.pages[index].Part
	document, _, _ := r.pageLocation(index)
	var result []PrintTicket
	remaining := min(r.limits.MaxPackageBytes, r.limits.MaxMetadataBytes, limits.MaxPackageBytes, limits.MaxMetadataBytes)
	for _, source := range []string{r.sequence, document, page} {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		value, err := r.printTicketReference(source)
		if err != nil {
			return nil, err
		}
		if value == nil {
			continue
		}
		if err := r.readPrintTicketData(value, min(remaining, r.limits.MaxPartBytes, limits.MaxPartBytes), ctx); err != nil {
			return nil, err
		}
		remaining -= int64(len(value.Data))
		result = append(result, *value)
	}
	return result, nil
}

// readPrintTicketData 在给定载荷预算内读取已定位的票据，供层级读取和作业缓存共用
// 入参: ticket 票据位置及数据接收者, maximum 字节上限, ctx 取消Context
// 返回: error 输入、资源或取消错误
func (r *Reader) readPrintTicketData(ticket *PrintTicket, maximum int64, ctx context.Context) error {
	if maximum <= 0 {
		return &PartError{Part: ticket.Part, Err: fmt.Errorf("%w: print ticket bytes", ErrLimit)}
	}
	input, err := r.pkg.openPartStream(ctx, strings.ToLower(ticket.Part), PartReadOptions{MaxBytes: maximum})
	if err != nil {
		return &PartError{Part: ticket.Part, Err: err}
	}
	data, err := io.ReadAll(input)
	closeErr := input.Close()
	if err != nil {
		return &PartError{Part: ticket.Part, Err: err}
	}
	if closeErr != nil {
		return &PartError{Part: ticket.Part, Err: closeErr}
	}
	if r.pkg.cache != nil {
		r.pkg.cache.mark(strings.ToLower(ticket.Part))
	}
	ticket.Data = data
	return nil
}

// readPrintTicket 在调用方持有读锁时读取一个层级的独立票据数据
// 入参: ctx 取消Context, source 源部件名称
// 返回: *PrintTicket 票据数据, error 关联、读取、预算或取消错误
func (r *Reader) readPrintTicket(ctx context.Context, source string) (*PrintTicket, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	value, err := r.printTicketReference(source)
	if err != nil || value == nil {
		return value, err
	}
	if err := r.readPrintTicketData(value, min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes, r.limits.MaxPackageBytes), ctx); err != nil {
		return nil, err
	}
	return value, nil
}

// printTicketReference 校验源部件及唯一的内部票据关联，不读取票据载荷
// 入参: source 源部件名称
// 返回: *PrintTicket 票据位置，没有关联时为nil, error 来源或关系错误
func (r *Reader) printTicketReference(source string) (*PrintTicket, error) {
	canonical, err := opcPartName(source)
	if err != nil {
		return nil, err
	}
	media, err := r.pkg.contentType(canonical)
	if err != nil {
		return nil, err
	}
	scope := printTicketScope(media)
	if scope == PrintScopeUnknown {
		return nil, &PartError{Part: canonical, Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
	}
	relations, err := r.pkg.relationships(canonical)
	if err != nil {
		return nil, err
	}
	part, err := printTicketTarget(canonical, relations, r.format)
	if err != nil || part == "" {
		return nil, err
	}
	typeName, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	return &PrintTicket{Source: r.pkg.names[strings.ToLower(canonical)], Part: r.pkg.names[strings.ToLower(part)], Scope: scope, ContentType: typeName}, nil
}

// printTicketScope 根据固定布局部件的内容类型确定关联层级
// 入参: media 内容类型
// 返回: PrintScope 关联层级，其他内容类型返回Unknown
func printTicketScope(media string) PrintScope {
	switch {
	case strings.EqualFold(media, fixedContentType("fixeddocumentsequence")):
		return PrintScopeJob
	case strings.EqualFold(media, fixedContentType("fixeddocument")):
		return PrintScopeDocument
	case strings.EqualFold(media, fixedContentType("fixedpage")):
		return PrintScopePage
	default:
		return PrintScopeUnknown
	}
}

// printTicketTarget 校验当前方言的票据关系数量及内部目标URI
// 入参: source 源部件, relations 关系列表, format 文档方言
// 返回: string 票据部件，没有关联时为空, error 重复、外部或非法目标错误
func printTicketTarget(source string, relations []Relationship, format Format) (string, error) {
	var part string
	for _, relation := range relations {
		if relation.Type != formatNamespace(format)+"/printticket" {
			continue
		}
		if part != "" {
			return "", &PartError{Part: source, Err: fmt.Errorf("%w: multiple print ticket relationships", ErrInvalid)}
		}
		if relation.TargetMode != "" && relation.TargetMode != TargetModeInternal {
			return "", &PartError{Part: source, Err: fmt.Errorf("%w: external print ticket relationship", ErrInvalid)}
		}
		var err error
		part, err = resolvePart(source, relation.Target)
		if err != nil {
			return "", &PartError{Part: source, Err: err}
		}
		if opcRelationshipName(part) {
			return "", &PartError{Part: source, Err: fmt.Errorf("%w: relationship part as print ticket", ErrInvalid)}
		}
	}
	return part, nil
}

// validatePrintTicketLinks 校验输出包中当前方言的票据关联及已识别Microsoft票据的Framework结构
// 入参: ctx 取消Context
// 返回: error 来源、关系、缺失目标或取消错误
func (r *Reader) validatePrintTicketLinks(ctx context.Context) error {
	checked := make(map[string]map[PrintScope]bool)
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if !opcRelationshipName(key) {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return err
		}
		source := relationshipSource(r.pkg.names[key])
		relations, err := r.pkg.relationships(source)
		if err != nil {
			return err
		}
		part, err := printTicketTarget(source, relations, r.format)
		if err != nil {
			return err
		}
		if part == "" {
			continue
		}
		if source == "/" {
			return &PartError{Part: source, Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
		}
		media, err := r.pkg.contentType(source)
		scope := printTicketScope(media)
		if err != nil || scope == PrintScopeUnknown {
			return &PartError{Part: source, Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
		}
		typeName, err := r.pkg.contentType(part)
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
		if r.format == FormatXPS && !matchStandardContentType(FormatXPS, typeName, printTicketType) {
			return &PartError{Part: part, Err: fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)}
		}
		baseType := opcMediaTypeBase(typeName)
		known, capabilities := printResourceMedia(baseType)
		profile := known && !capabilities
		partKey := strings.ToLower(part)
		if !profile || checked[partKey][scope] {
			continue
		}
		data, err := r.pkg.readItems(partKey, min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes))
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
		configuration, err := printSettingsOptions(ctx, &PrintSettingsOptions{Limits: r.limits, Scope: scope})
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
		root, err := decodeXML(data, configuration.Limits)
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
		if _, err := parsePrintSettings(root, configuration); err != nil {
			return &PartError{Part: part, Err: err}
		}
		if err := xmlNamespaceTreeOutput(root, ctx); err != nil {
			return &PartError{Part: part, Err: err}
		}
		if checked[partKey] == nil {
			checked[partKey] = make(map[PrintScope]bool)
		}
		checked[partKey][scope] = true
	}
	return nil
}

// ParsePrintSettings 解析Microsoft PrintTicket并校验Framework结构、QName及基本值类型
// 保留未知关键字，不验证关键字专属参数、设备能力或ParameterRef的设备默认值
// 入参: ctx 取消Context，nil采用Background, data UTF-8或UTF-16票据XML, options 解析参数，nil采用默认值
// 返回: *PrintSettings 独立设置结构, error XML、Framework、资源或取消错误
func ParsePrintSettings(ctx context.Context, data []byte, options *PrintSettingsOptions) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	if int64(len(data)) > min(configuration.Limits.MaxPartBytes, configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: print settings byte budget", ErrLimit)
	}
	root, err := decodeXML(data, configuration.Limits)
	if err != nil {
		return nil, err
	}
	return parsePrintSettings(root, configuration)
}

// printSettingsOptions 合并默认资源上限并检查作用域和上限
// 入参: ctx 取消Context, options 调用方参数
// 返回: printSettingsConfig 独立内部配置, error 参数错误
func printSettingsOptions(ctx context.Context, options *PrintSettingsOptions) (printSettingsConfig, error) {
	value := DefaultPrintSettingsOptions()
	if options != nil {
		value = *options
		value.Limits = mergeLimits(DefaultLimits(), options.Limits)
		if value.MaxNumericDigits == 0 {
			value.MaxNumericDigits = 4096
		}
		if value.MaxOptionComparisons == 0 {
			value.MaxOptionComparisons = 100000
		}
	}
	config := printSettingsConfig{PrintSettingsOptions: value, context: normalizeContext(ctx)}
	if value.Scope > PrintScopePage {
		return config, fmt.Errorf("%w: print settings scope", ErrInvalid)
	}
	if value.MaxNumericDigits < 1 || value.MaxOptionComparisons < 1 {
		return config, fmt.Errorf("%w: print settings parameter budget", ErrInvalid)
	}
	return config, validateLimits(value.Limits)
}

// parsePrintSettings 校验根版本并在作用域过滤后解析根设置
// 入参: root 已解析XML根, options 已校验参数
// 返回: *PrintSettings 设置结构, error Framework、作用域或取消错误
func parsePrintSettings(root *xmlElement, options printSettingsConfig) (*PrintSettings, error) {
	return parsePrintDocument(root, options, false)
}

// parsePrintDocument 按票据或能力文档规则校验根结构，支持Print Schema v1与v2框架，只有票据执行关联层级过滤
// 入参: root 已解析XML根, options 已校验参数, capabilities 是否为设备能力文档
// 返回: *PrintSettings 独立Framework结构, error 结构、资源或取消错误
func parsePrintDocument(root *xmlElement, options printSettingsConfig, capabilities bool) (*PrintSettings, error) {
	mode := printDocumentTicket
	if capabilities {
		mode = printDocumentCapabilities
	}
	return parsePrintDocumentMode(root, options, mode)
}

// parsePrintDocumentMode 按票据、PrintCapabilities或PrintDeviceCapabilities模式校验根结构与子元素
// 入参: root 已解析XML根, options 已校验参数, mode 文档类别模式
// 返回: *PrintSettings 独立Framework结构, error 结构、资源或取消错误
func parsePrintDocumentMode(root *xmlElement, options printSettingsConfig, mode printDocumentMode) (*PrintSettings, error) {
	capabilities := mode != printDocumentTicket
	rootName := "PrintTicket"
	if mode == printDocumentCapabilities {
		rootName = "PrintCapabilities"
	} else if mode == printDocumentDeviceCapabilities {
		rootName = "PrintDeviceCapabilities"
	}
	validSpace := printFrameworkSpace(root.Name.Space)
	if mode == printDocumentDeviceCapabilities {
		validSpace = root.Name.Space == printFramework2NS
	}
	if !validSpace || root.Name.Local != rootName || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: print settings root", ErrInvalid)
	}
	if err := printSettingsElementAttributes(root, true, "version"); err != nil {
		return nil, err
	}
	version, exists := root.attribute("version")
	version = strings.Trim(version, " \t\r\n")
	var parsedVersion uint32
	if mode == printDocumentDeviceCapabilities && !exists {
		parsedVersion = 2
	} else {
		if !exists || !printInteger(version) || strings.HasPrefix(version, "-") {
			return nil, fmt.Errorf("%w: print settings version", ErrInvalid)
		}
		version = strings.TrimLeft(strings.TrimPrefix(version, "+"), "0")
		if version == "" {
			return nil, fmt.Errorf("%w: print settings version", ErrInvalid)
		}
		if root.Name.Space == printFrameworkNS {
			if version != "1" {
				return nil, fmt.Errorf("%w: print settings framework version", ErrUnsupported)
			}
			parsedVersion = 1
		} else {
			if version != "2" {
				return nil, fmt.Errorf("%w: print settings framework version", ErrUnsupported)
			}
			parsedVersion = 2
		}
	}
	value := &PrintSettings{Version: parsedVersion}
	seen := make(map[xml.Name]bool)
	seenChangeID := false
	for _, child := range root.Children {
		if err := checkContext(options.context); err != nil {
			return nil, err
		}
		if mode == printDocumentDeviceCapabilities && (child.Name.Space == "" || child.Name.Space == printFramework2NS) && child.Name.Local == "CapabilitiesChangeID" {
			if _, hasPSFType := child.attributeNS(printFramework2NS, "psftype"); !hasPSFType {
				if seenChangeID {
					return nil, fmt.Errorf("%w: duplicate print device capabilities CapabilitiesChangeID", ErrInvalid)
				}
				changeID, err := parsePrintCapabilitiesChangeID(child)
				if err != nil {
					return nil, err
				}
				seenChangeID = true
				value.CapabilitiesChangeID = changeID
				continue
			}
		}
		if mode == printDocumentDeviceCapabilities && child.Name == (xml.Name{Space: printFrameworkNS, Local: "ParameterDef"}) {
			name, err := printSettingsName(child, true)
			if err != nil {
				return nil, err
			}
			key := printCanonicalKey(name)
			if seen[key] {
				return nil, fmt.Errorf("%w: duplicate print setting {%s}%s", ErrInvalid, name.Space, name.Local)
			}
			seen[key] = true
			setting, err := parsePrintSetting(child, 1, [len(printSettingNames)]uint8{}, options.context, true)
			if err != nil {
				return nil, err
			}
			if _, err := printParameterDefinition(setting, options); err != nil {
				return nil, fmt.Errorf("print parameter {%s}%s: %w", setting.Name.Space, setting.Name.Local, err)
			}
			value.Elements = append(value.Elements, setting)
			continue
		}
		kind, psf2, err := printSettingKindForVersion(child, parsedVersion)
		if err != nil {
			return nil, err
		}
		parameterKind := PrintSettingParameterInit
		if capabilities {
			parameterKind = PrintSettingParameterDef
		}
		if kind != PrintSettingFeature && kind != parameterKind && kind != PrintSettingProperty {
			return nil, fmt.Errorf("%w: print settings root child %s", ErrInvalid, child.Name.Local)
		}
		var name xml.Name
		if psf2 {
			name = child.Name
		} else {
			name, err = printSettingsName(child, true)
			if err != nil {
				return nil, err
			}
		}
		scope := printKeywordScope(name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		key := printCanonicalKey(name)
		if seen[key] {
			return nil, fmt.Errorf("%w: duplicate print setting {%s}%s", ErrInvalid, name.Space, name.Local)
		}
		seen[key] = true
		setting, err := parsePrintSetting(child, parsedVersion, [len(printSettingNames)]uint8{}, options.context, capabilities)
		if err != nil {
			return nil, err
		}
		if setting.Kind == PrintSettingParameterDef {
			if _, err := printParameterDefinition(setting, options); err != nil {
				return nil, fmt.Errorf("print parameter {%s}%s: %w", setting.Name.Space, setting.Name.Local, err)
			}
		}
		value.Elements = append(value.Elements, setting)
	}
	if err := printSettingsPrefixConflicts(value.Elements); err != nil {
		return nil, err
	}
	if err := validatePrintCommon(value.Elements, PrintSettingUnknown, capabilities); err != nil {
		return nil, err
	}
	return value, nil
}

// parsePrintCapabilitiesChangeID 解析并校验Windows V4 PDC根级CapabilitiesChangeID元素
// 入参: node CapabilitiesChangeID XML元素
// 返回: string 非空变更标识文本, error 结构、属性或类型错误
func parsePrintCapabilitiesChangeID(node *xmlElement) (string, error) {
	if len(node.Children) != 0 {
		return "", fmt.Errorf("%w: print device capabilities CapabilitiesChangeID children", ErrInvalid)
	}
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if handled, err := printSettingsXMLAttribute(attribute, false); handled {
			if err != nil {
				return "", err
			}
			continue
		}
		if attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			typeName, err := printSettingsQName(node, attribute.Value)
			if err != nil || typeName != (xml.Name{Space: printValueNS, Local: "string"}) {
				return "", fmt.Errorf("%w: print device capabilities CapabilitiesChangeID type", ErrInvalid)
			}
			continue
		}
		return "", fmt.Errorf("%w: print device capabilities CapabilitiesChangeID attribute {%s}%s", ErrInvalid, attribute.Name.Space, attribute.Name.Local)
	}
	if strings.TrimSpace(node.Text) == "" {
		return "", fmt.Errorf("%w: empty print device capabilities CapabilitiesChangeID", ErrInvalid)
	}
	return node.Text, nil
}

// printPrefixFamily 提取可参与作用域前缀族比对的键与作用域，仅限声明类Framework元素
// 入参: value 设置元素
// 返回: printPrefixKey 关键字族键, PrintScope 作用域层级, bool 是否具备有效作用域前缀族
func printPrefixFamily(value PrintSetting) (printPrefixKey, PrintScope, bool) {
	switch value.Kind {
	case PrintSettingFeature, PrintSettingProperty, PrintSettingScoredProperty, PrintSettingParameterInit, PrintSettingParameterDef:
	default:
		return printPrefixKey{}, PrintScopeUnknown, false
	}
	scope := printKeywordScope(value.Name)
	if scope == PrintScopeUnknown {
		return printPrefixKey{}, PrintScopeUnknown, false
	}
	prefix := "Job"
	if scope == PrintScopeDocument {
		prefix = "Document"
	} else if scope == PrintScopePage {
		prefix = "Page"
	}
	suffix := strings.TrimPrefix(value.Name.Local, prefix)
	if suffix == "" {
		return printPrefixKey{}, PrintScopeUnknown, false
	}
	canonical := printCanonicalKey(value.Name)
	return printPrefixKey{kind: value.Kind, space: canonical.Space, local: suffix}, scope, true
}

// printSettingsPrefixConflicts 检查同一父级作用域内同类元素中仅作用域前缀不同的关键字冲突
// 入参: settings 当前父级作用域下的直接子元素列表
// 返回: error 作用域前缀冲突错误
func printSettingsPrefixConflicts(settings []PrintSetting) error {
	seen := make(map[printPrefixKey]xml.Name)
	for _, value := range settings {
		if key, _, ok := printPrefixFamily(value); ok {
			canonical := printCanonicalKey(value.Name)
			if previous, exists := seen[key]; exists && previous != canonical {
				return fmt.Errorf("%w: print settings scope prefix conflict {%s}%s and %s", ErrInvalid, value.Name.Space, previous.Local, value.Name.Local)
			}
			seen[key] = canonical
		}
		if err := printSettingsPrefixConflicts(value.Children); err != nil {
			return err
		}
	}
	return nil
}

// parsePrintSetting 校验单个Framework元素及其子结构，按根版本严格区分PSF1与PSF2节点语法，能力文档同类型元素及票据Feature不得嵌套超过十层
// 入参: node XML元素, version 框架版本号, nesting 各类型已包含的层数, ctx 取消Context, capabilities 是否为设备能力文档
// 返回: PrintSetting 独立设置元素, error 结构、值或取消错误
func parsePrintSetting(node *xmlElement, version uint32, nesting [len(printSettingNames)]uint8, ctx context.Context, capabilities bool) (PrintSetting, error) {
	kind, psf2, err := printSettingKindForVersion(node, version)
	if err != nil {
		return PrintSetting{}, err
	}
	value := PrintSetting{Kind: kind}
	if err := checkContext(ctx); err != nil {
		return value, err
	}
	if value.Kind == PrintSettingUnknown {
		return value, fmt.Errorf("%w: print settings element {%s}%s", ErrInvalid, node.Name.Space, node.Name.Local)
	}
	nesting[value.Kind]++
	if (capabilities || value.Kind == PrintSettingFeature) && nesting[value.Kind] > 10 {
		return value, fmt.Errorf("%w: print settings element nesting", ErrInvalid)
	}
	if value.Kind == PrintSettingValue {
		value.Value, err = parsePrintValue(node)
		return value, err
	}
	inlineCapable := psf2 && (value.Kind == PrintSettingProperty || value.Kind == PrintSettingScoredProperty || value.Kind == PrintSettingParameterInit)
	xsiTypeText, hasXSIType := node.attributeNS(xsiNamespace, "type")
	inlineRef := false
	if psf2 && value.Kind == PrintSettingScoredProperty && hasXSIType {
		typeName, err := printSettingsQName(node, xsiTypeText)
		if err != nil {
			return value, err
		}
		if printFrameworkSpace(typeName.Space) && typeName.Local == "ParameterRef" {
			inlineRef = true
		}
	}
	inlineValue := inlineCapable && !inlineRef && (len(node.Children) == 0 || hasXSIType || !xmlWhitespace(node.Text))
	if !inlineValue && !inlineRef && !xmlWhitespace(node.Text) {
		return value, fmt.Errorf("%w: text in print settings %s", ErrInvalid, node.Name.Local)
	}
	var selectionProp *PrintSetting
	if psf2 {
		if err := printSettingsPSF2Attributes(node, value.Kind, capabilities, inlineCapable, &value.Constraint, &value.HasDefault, &value.Default, &selectionProp); err != nil {
			return value, err
		}
		value.Name = node.Name
	} else {
		allowedAttributes := []string{"name"}
		if capabilities && value.Kind == PrintSettingOption {
			allowedAttributes = append(allowedAttributes, "constrained")
			if text, present := node.attribute("constrained"); present {
				value.Constraint, err = printConstraint(node, text)
				if err != nil {
					return value, err
				}
			}
		}
		if err := printSettingsAttributes(node, allowedAttributes...); err != nil {
			return value, err
		}
		value.Name, err = printSettingsName(node, value.Kind != PrintSettingOption)
		if err != nil {
			return value, err
		}
	}
	seen := make(map[xml.Name]bool)
	values, choices := 0, 0
	if selectionProp != nil {
		seen[printCanonicalKey(selectionProp.Name)] = true
		value.Children = append(value.Children, *selectionProp)
	}
	if inlineRef {
		refName, err := printSettingsQName(node, node.Text)
		if err != nil || refName.Space == "" {
			return value, fmt.Errorf("%w: print settings inline ParameterRef %q", ErrInvalid, node.Text)
		}
		values++
		value.Children = append(value.Children, PrintSetting{Kind: PrintSettingParameterRef, Name: refName})
	} else if inlineValue {
		parsedVal, err := parsePrintValueContent(node, capabilities && psf2)
		if err != nil {
			return value, err
		}
		values++
		value.Children = append(value.Children, PrintSetting{Kind: PrintSettingValue, Value: parsedVal})
	}
	for _, child := range node.Children {
		childKind, _, err := printSettingKindForVersion(child, version)
		if err != nil {
			return value, err
		}
		allowed := false
		switch value.Kind {
		case PrintSettingFeature:
			allowed = childKind == PrintSettingProperty || childKind == PrintSettingFeature || childKind == PrintSettingOption
		case PrintSettingOption:
			allowed = childKind == PrintSettingProperty || childKind == PrintSettingScoredProperty
		case PrintSettingProperty:
			allowed = childKind == PrintSettingValue || childKind == PrintSettingProperty
		case PrintSettingScoredProperty:
			allowed = childKind == PrintSettingValue || childKind == PrintSettingParameterRef || childKind == PrintSettingProperty || childKind == PrintSettingScoredProperty
		case PrintSettingParameterInit:
			allowed = childKind == PrintSettingValue
		case PrintSettingParameterDef:
			allowed = capabilities && childKind == PrintSettingProperty
		}
		if !allowed {
			return value, fmt.Errorf("%w: %s child in print settings %s", ErrInvalid, child.Name.Local, node.Name.Local)
		}
		parsed, err := parsePrintSetting(child, version, nesting, ctx, capabilities)
		if err != nil {
			return value, err
		}
		if childKind != PrintSettingOption && parsed.Name != (xml.Name{}) {
			key := printCanonicalKey(parsed.Name)
			if seen[key] {
				return value, fmt.Errorf("%w: duplicate print setting child {%s}%s", ErrInvalid, parsed.Name.Space, parsed.Name.Local)
			}
			seen[key] = true
		}
		if childKind == PrintSettingValue || childKind == PrintSettingParameterRef {
			values++
		}
		if childKind == PrintSettingFeature || childKind == PrintSettingOption {
			choices++
		}
		value.Children = append(value.Children, parsed)
	}
	valid := true
	switch value.Kind {
	case PrintSettingFeature:
		valid = choices > 0
	case PrintSettingProperty:
		valid = len(value.Children) > 0 && values <= 1
	case PrintSettingScoredProperty, PrintSettingParameterInit:
		valid = values == 1
	case PrintSettingParameterRef:
		valid = len(value.Children) == 0
	case PrintSettingParameterDef:
		valid = capabilities
	}
	if !valid {
		return value, fmt.Errorf("%w: print settings %s child count", ErrInvalid, node.Name.Local)
	}
	if value.Kind == PrintSettingParameterDef {
		if err := printParameterDefaultQName(node, &value, psf2); err != nil {
			return value, err
		}
	}
	return value, nil
}

// printSettingKind 根据展开名称识别允许的Framework v1显式元素
// 入参: name 元素展开名称
// 返回: PrintSettingKind 元素类型，非Framework v1或未知元素返回Unknown
func printSettingKind(name xml.Name) PrintSettingKind {
	if name.Space == printFrameworkNS {
		for kind, local := range printSettingNames {
			if kind != 0 && name.Local == local {
				return PrintSettingKind(kind)
			}
		}
	}
	return PrintSettingUnknown
}

// printSettingKindForVersion 按框架版本严格识别v1显式包装元素或v2携带psf2:psftype属性的直接关键字元素
// 入参: node XML元素, version 框架版本号
// 返回: PrintSettingKind 元素类型, bool 是否为psf2:psftype直接元素, error 非法psftype或伪造包装元素错误
func printSettingKindForVersion(node *xmlElement, version uint32) (PrintSettingKind, bool, error) {
	if version != 2 {
		if kind := printSettingKind(node.Name); kind != PrintSettingUnknown {
			return kind, false, nil
		}
		return PrintSettingUnknown, false, nil
	}
	text, present := node.attributeNS(printFramework2NS, "psftype")
	if !present {
		return PrintSettingUnknown, false, nil
	}
	if node.Name.Space == "" {
		return PrintSettingUnknown, false, fmt.Errorf("%w: print settings v2 element without namespace", ErrInvalid)
	}
	if printFrameworkSpace(node.Name.Space) && (printSettingKind(xml.Name{Space: printFrameworkNS, Local: node.Name.Local}) != PrintSettingUnknown || node.Name.Local == "PrintTicket" || node.Name.Local == "PrintCapabilities" || node.Name.Local == "PrintDeviceCapabilities") {
		return PrintSettingUnknown, false, fmt.Errorf("%w: print settings v2 wrapper element {%s}%s", ErrInvalid, node.Name.Space, node.Name.Local)
	}
	text = strings.Trim(text, " \t\r\n")
	for kind, local := range printSettingNames {
		if kind != 0 && PrintSettingKind(kind) != PrintSettingValue && text == local {
			return PrintSettingKind(kind), true, nil
		}
	}
	return PrintSettingUnknown, false, fmt.Errorf("%w: print settings psf2:psftype %q", ErrInvalid, text)
}

// printSettingsXMLAttribute 校验标准XML 1.0及根元素XSD全局属性
// 入参: attribute XML属性, isRoot 是否位于文档根元素
// 返回: bool 是否已由标准全局属性规则处理, error 属性取值错误
func printSettingsXMLAttribute(attribute xml.Attr, isRoot bool) (bool, error) {
	if attribute.Name.Space == xmlNamespace {
		switch attribute.Name.Local {
		case "lang":
			return true, nil
		case "space":
			if attribute.Value != "default" && attribute.Value != "preserve" {
				return true, fmt.Errorf("%w: print settings xml:space value", ErrInvalid)
			}
			return true, nil
		}
	}
	if isRoot && attribute.Name.Space == xsiNamespace && (attribute.Name.Local == "schemaLocation" || attribute.Name.Local == "noNamespaceSchemaLocation") {
		return true, nil
	}
	return false, nil
}

// printSettingsPSF2Attributes 校验Print Schema v2直接元素的框架属性并提取约束、默认标记与选择类型
// 入参: node XML元素, kind 已识别元素类型, capabilities 是否为能力文档, allowType 是否允许xsi:type, constraint 约束输出, hasDefault 默认声明标志输出, isDefault 默认选项值输出, selection 选择属性输出
// 返回: error 属性或取值错误
func printSettingsPSF2Attributes(node *xmlElement, kind PrintSettingKind, capabilities, allowType bool, constraint *PrintConstraint, hasDefault, isDefault *bool, selection **PrintSetting) error {
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if handled, err := printSettingsXMLAttribute(attribute, false); handled {
			if err != nil {
				return err
			}
			continue
		}
		if attribute.Name == (xml.Name{Space: printFramework2NS, Local: "psftype"}) {
			continue
		}
		if allowType && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			continue
		}
		if capabilities && kind == PrintSettingOption && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "default"}) {
			value := strings.Trim(attribute.Value, " \t\r\n")
			if value != "true" && value != "false" {
				return fmt.Errorf("%w: print settings psf2:default value", ErrInvalid)
			}
			*hasDefault = true
			*isDefault = value == "true"
			continue
		}
		if capabilities && kind == PrintSettingOption && (attribute.Name == (xml.Name{Local: "constrained"}) || attribute.Name == (xml.Name{Space: printFramework2NS, Local: "constrained"})) {
			parsed, err := printConstraint(node, attribute.Value)
			if err != nil {
				return err
			}
			*constraint = parsed
			continue
		}
		if capabilities && kind == PrintSettingFeature && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "selectiontype"}) {
			qname, err := printSettingsQName(node, attribute.Value)
			if err != nil || !printPublicKeywordSpace(qname.Space) || (qname.Local != "PickOne" && qname.Local != "PickMany") {
				return fmt.Errorf("%w: print settings psf2:selectiontype value", ErrInvalid)
			}
			prop := PrintSetting{
				Kind: PrintSettingProperty,
				Name: xml.Name{Space: printFrameworkNS, Local: "SelectionType"},
				Children: []PrintSetting{{
					Kind:  PrintSettingValue,
					Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: strings.Trim(attribute.Value, " \t\r\n"), QName: qname},
				}},
			}
			*selection = &prop
			continue
		}
		return fmt.Errorf("%w: print settings attribute {%s}%s", ErrInvalid, attribute.Name.Space, attribute.Name.Local)
	}
	return nil
}

// printSettingsAttributes 检查允许的无命名空间属性、标准XML属性及Value的xsi:type，不接受私有XML属性
// 入参: node 元素, allowed 允许的无命名空间属性
// 返回: error 非法属性错误
func printSettingsAttributes(node *xmlElement, allowed ...string) error {
	return printSettingsElementAttributes(node, false, allowed...)
}

// printSettingsElementAttributes 校验元素属性，允许标准XML 1.0全局属性及根元素XSD架构位置属性
// 入参: node 元素, isRoot 是否为文档根元素, allowed 允许的无命名空间属性
// 返回: error 非法属性错误
func printSettingsElementAttributes(node *xmlElement, isRoot bool, allowed ...string) error {
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if handled, err := printSettingsXMLAttribute(attribute, isRoot); handled {
			if err != nil {
				return err
			}
			continue
		}
		valid := false
		for _, name := range allowed {
			valid = valid || name != "" && attribute.Name == (xml.Name{Local: name})
		}
		if valid {
			continue
		}
		if !isRoot && node.Name.Local == "Value" && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			continue
		}
		return fmt.Errorf("%w: print settings attribute {%s}%s", ErrInvalid, attribute.Name.Space, attribute.Name.Local)
	}
	return nil
}

// printSettingsName 读取关键字QName，Option允许完全省略名称但不允许显式空名称
// 入参: node 元素, required 是否要求名称
// 返回: xml.Name 展开关键字, error 缺失、空名称或QName错误
func printSettingsName(node *xmlElement, required bool) (xml.Name, error) {
	text, exists := node.attribute("name")
	if !exists && !required {
		return xml.Name{}, nil
	}
	if !exists {
		return xml.Name{}, fmt.Errorf("%w: missing print settings name", ErrInvalid)
	}
	name, err := printSettingsQName(node, text)
	if err != nil {
		return name, err
	}
	if name.Space == "" {
		return name, fmt.Errorf("%w: print settings keyword without namespace", ErrInvalid)
	}
	return name, nil
}

// printSettingsQName 按XML Schema空白规则解析QName，不接受通配符或未声明前缀
// 入参: node 命名空间作用域, text QName文本
// 返回: xml.Name 展开名称, error QName错误
func printSettingsQName(node *xmlElement, text string) (xml.Name, error) {
	text = strings.Trim(text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified {
		if !xmlNCName(text) {
			return xml.Name{}, fmt.Errorf("%w: print settings QName %q", ErrInvalid, text)
		}
		return xml.Name{Space: node.Namespaces[""], Local: text}, nil
	}
	if !xmlNCName(prefix) || !xmlNCName(local) || prefix == "xmlns" || node.Namespaces[prefix] == "" {
		return xml.Name{}, fmt.Errorf("%w: print settings QName %q", ErrInvalid, text)
	}
	return xml.Name{Space: node.Namespaces[prefix], Local: local}, nil
}

// printKeywordScope 读取关键字的作用域前缀，不按命名空间或厂商名称猜测设备语义
// 入参: name 展开关键字
// 返回: PrintScope 作用域，没有约定前缀时返回Unknown
func printKeywordScope(name xml.Name) PrintScope {
	switch {
	case strings.HasPrefix(name.Local, "Job"):
		return PrintScopeJob
	case strings.HasPrefix(name.Local, "Document"):
		return PrintScopeDocument
	case strings.HasPrefix(name.Local, "Page"):
		return PrintScopePage
	default:
		return PrintScopeUnknown
	}
}

// parsePrintValue 解析四种Framework基本值类型，省略xsi:type时采用string，空值保持未赋值
// 入参: node Value元素
// 返回: *PrintValue 独立值, error 结构、类型或字符数据错误
func parsePrintValue(node *xmlElement) (*PrintValue, error) {
	if len(node.Children) != 0 {
		return nil, fmt.Errorf("%w: print settings Value children", ErrInvalid)
	}
	if err := printSettingsAttributes(node, ""); err != nil {
		return nil, err
	}
	return parsePrintValueContent(node, false)
}

// parsePrintValueContent 解析元素文本与xsi:type为标准Framework标量值，PSF2内联值额外支持psf2:ImageableAreaType
// 入参: node 携带值文本与命名空间作用域的元素, allowPSF2 是否允许PSF2专属数据类型
// 返回: *PrintValue 独立值, error 类型或字符数据错误
func parsePrintValueContent(node *xmlElement, allowPSF2 bool) (*PrintValue, error) {
	value := &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: node.Text}
	if text, exists := node.attributeNS(xsiNamespace, "type"); exists {
		var err error
		value.Type, err = printSettingsQName(node, text)
		if err != nil {
			return nil, err
		}
	}
	if allowPSF2 && value.Type == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
		if !printImageableAreaValid(value.Text) {
			return nil, fmt.Errorf("%w: print settings ImageableAreaType value", ErrInvalid)
		}
		return value, nil
	}
	if value.Type.Space != printValueNS {
		return nil, fmt.Errorf("%w: print settings Value type", ErrInvalid)
	}
	text := strings.Trim(value.Text, " \t\r\n")
	valid := true
	switch value.Type.Local {
	case "string":
	case "integer":
		valid = text == "" || printInteger(text)
	case "decimal":
		valid = text == "" || printDecimal(text)
	case "QName":
		if text != "" {
			var err error
			value.QName, err = printSettingsQName(node, text)
			if err != nil {
				return nil, err
			}
		}
	default:
		valid = false
	}
	if !valid {
		return nil, fmt.Errorf("%w: print settings %s value", ErrInvalid, value.Type.Local)
	}
	return value, nil
}

// printImageableAreaValid 校验psf2:ImageableAreaType的四个逗号分隔非负int64微米整数词法与边界
// 入参: text 原始区域文本
// 返回: bool 是否为合法四元非负微米整数列表
func printImageableAreaValid(text string) bool {
	_, ok := printParseImageableArea(text)
	return ok
}

// printParseImageableArea 解析psf2:ImageableAreaType的四个非负微米整数值
// 入参: text 原始区域文本
// 返回: [4]int64 依次为原点X、原点Y、宽度与高度微米值, bool 是否解析成功
func printParseImageableArea(text string) ([4]int64, bool) {
	var result [4]int64
	parts := strings.Split(text, ",")
	if len(parts) != 4 {
		return result, false
	}
	for index, part := range parts {
		trimmed := strings.Trim(part, " \t\r\n")
		if trimmed == "" || strings.HasPrefix(trimmed, "-") || !printInteger(trimmed) {
			return [4]int64{}, false
		}
		parsed, err := strconv.ParseInt(trimmed, 10, 64)
		if err != nil || parsed < 0 {
			return [4]int64{}, false
		}
		result[index] = parsed
	}
	return result, true
}

// printInteger 校验任意精度XML Schema整数的词法形式，不转为有限位数整数
// 入参: text 已去除首尾XML空白的文本
// 返回: bool 是否为合法整数
func printInteger(text string) bool {
	if text != "" && (text[0] == '+' || text[0] == '-') {
		text = text[1:]
	}
	if text == "" {
		return false
	}
	for i := range len(text) {
		if text[i] < '0' || text[i] > '9' {
			return false
		}
	}
	return true
}

// printDecimal 校验任意精度XML Schema十进制数，不接受指数、NaN或无穷大
// 入参: text 已去除首尾XML空白的文本
// 返回: bool 是否为合法十进制数
func printDecimal(text string) bool {
	if text != "" && (text[0] == '+' || text[0] == '-') {
		text = text[1:]
	}
	digits, points := 0, 0
	for i := range len(text) {
		if text[i] >= '0' && text[i] <= '9' {
			digits++
		} else if text[i] == '.' {
			points++
		} else {
			return false
		}
	}
	return digits > 0 && points <= 1
}

// Settings 解析Print Schema1.1及2.0票据，默认采用票据关联层级过滤根设置
// 能力文档及自定义票据格式返回ErrUnsupported，不把未知格式误判为损坏XML
// 入参: ctx 取消Context，nil采用Background, options 解析参数，非Unknown的Scope覆盖票据层级，nil采用默认值
// 返回: *PrintSettings 独立设置结构, error 内容类型、XML、Framework或资源错误
func (t *PrintTicket) Settings(ctx context.Context, options *PrintSettingsOptions) (*PrintSettings, error) {
	ctx = normalizeContext(ctx)
	if t == nil {
		return nil, fmt.Errorf("%w: nil print ticket", ErrInvalid)
	}
	if known, capabilities := printResourceMedia(t.ContentType); !known || capabilities {
		return nil, fmt.Errorf("%w: print ticket format %s", ErrUnsupported, t.ContentType)
	}
	configuration := PrintSettingsOptions{}
	if options != nil {
		configuration = *options
	}
	if configuration.Scope == PrintScopeUnknown {
		configuration.Scope = t.Scope
	}
	return ParsePrintSettings(ctx, t.Data, &configuration)
}

// MergePrintSettings 合并根设置，同名Feature递归合并子Feature、Option与Property，其他同名项由delta覆盖
// 同族不同作用域前缀按高优先级作用域覆盖低层级项，作用域过滤分别应用于两个输入，不执行设备默认值或约束求解
// 入参: ctx 取消Context，nil采用Background, baseline 基础设置, delta 优先设置, options 合并结果的关联层级及资源参数
// 返回: *PrintSettings 独立合并结构, error 结构、资源或取消错误
func MergePrintSettings(ctx context.Context, baseline, delta *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	base, err := validatePrintSettingsModel(baseline, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	change, err := validatePrintSettingsModel(delta, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	merged, err := mergePrintSettingsValidated(base, change, configuration)
	if err != nil {
		return nil, err
	}
	result, err := validatePrintSettingsModel(merged, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsOutputBudget(result, configuration, printDocumentTicket); err != nil {
		return nil, err
	}
	return result, nil
}

// mergePrintSettingsValidated 在纯内存中合并两份已校验且已按作用域过滤的打印票据模型
// 入参: base 已校验基础票据副本, change 已校验增量票据副本, configuration 已校验配置
// 返回: *PrintSettings 合并后的打印设置模型, error 取消错误
func mergePrintSettingsValidated(base, change *PrintSettings, configuration printSettingsConfig) (*PrintSettings, error) {
	elements := make([]PrintSetting, len(base.Elements))
	copy(elements, base.Elements)
	removed := make([]bool, len(elements))
	indices := make(map[xml.Name]int, len(elements))
	families := make(map[printPrefixKey]int, len(elements))
	for index, value := range elements {
		indices[printCanonicalKey(value.Name)] = index
		if key, _, ok := printPrefixFamily(value); ok {
			families[key] = index
		}
	}
	for _, value := range change.Elements {
		if err := checkContext(configuration.context); err != nil {
			return nil, err
		}
		valueKey := printCanonicalKey(value.Name)
		familyKey, scope, hasFamily := printPrefixFamily(value)
		replacedIndex := -1
		if hasFamily {
			if existing, exists := families[familyKey]; exists && printCanonicalKey(elements[existing].Name) != valueKey {
				if scope < printKeywordScope(elements[existing].Name) {
					continue
				}
				delete(indices, printCanonicalKey(elements[existing].Name))
				delete(families, familyKey)
				removed[existing] = true
				replacedIndex = existing
			}
		}
		if index, exists := indices[valueKey]; exists {
			if elements[index].Kind == PrintSettingFeature && value.Kind == PrintSettingFeature {
				mergedFeature, err := mergePrintFeature(elements[index], value, configuration.context)
				if err != nil {
					return nil, err
				}
				elements[index] = mergedFeature
			} else {
				if oldKey, _, ok := printPrefixFamily(elements[index]); ok && families[oldKey] == index {
					delete(families, oldKey)
				}
				elements[index] = value
				if hasFamily {
					families[familyKey] = index
				}
			}
		} else if replacedIndex >= 0 {
			removed[replacedIndex] = false
			elements[replacedIndex] = value
			indices[valueKey] = replacedIndex
			families[familyKey] = replacedIndex
		} else {
			index := len(elements)
			elements = append(elements, value)
			removed = append(removed, false)
			indices[valueKey] = index
			if hasFamily {
				families[familyKey] = index
			}
		}
	}
	merged := make([]PrintSetting, 0, len(elements))
	for index, value := range elements {
		if !removed[index] {
			merged = append(merged, value)
		}
	}
	base.Elements = merged
	if change.Version > base.Version {
		base.Version = change.Version
	}
	if base.Version > 1 && printSettingsHasAnonymousOption(base.Elements) {
		base.Version = 1
		printStripOptionDefaults(base.Elements)
	}
	return base, nil
}

// mergePrintFeature 递归合并同名Feature的直接子Feature、Option与Property，delta未提供直接Option时保留baseline的Option
// 入参: baseline 基础Feature, delta 优先Feature, ctx 取消Context
// 返回: PrintSetting 合并后的Feature, error 取消错误
func mergePrintFeature(baseline, delta PrintSetting, ctx context.Context) (PrintSetting, error) {
	if err := checkContext(ctx); err != nil {
		return PrintSetting{}, err
	}
	var baselineOption, deltaOption xml.Name
	baselineHasOption, deltaHasOption := false, false
	for _, child := range baseline.Children {
		if child.Kind == PrintSettingOption {
			baselineOption, baselineHasOption = child.Name, true
			break
		}
	}
	for _, child := range delta.Children {
		if child.Kind == PrintSettingOption {
			deltaOption, deltaHasOption = child.Name, true
			break
		}
	}
	watermark := printPublicKeywordSpace(baseline.Name.Space) && baseline.Name.Local == "PageWatermark"
	dropBaseSubfeatures := watermark && deltaHasOption && (!baselineHasOption || printCanonicalKey(deltaOption) != printCanonicalKey(baselineOption))
	dropDeltaLayering := watermark && !deltaHasOption && baselineHasOption && printPublicKeywordSpace(baselineOption.Space) && baselineOption.Local == "None"
	elements := make([]PrintSetting, 0, len(baseline.Children)+len(delta.Children))
	removed := make([]bool, 0, len(baseline.Children)+len(delta.Children))
	indices := make(map[xml.Name]int, len(baseline.Children))
	families := make(map[printPrefixKey]int, len(baseline.Children))
	for _, child := range baseline.Children {
		if child.Kind == PrintSettingOption && deltaHasOption {
			continue
		}
		if child.Kind == PrintSettingFeature && dropBaseSubfeatures {
			continue
		}
		index := len(elements)
		elements = append(elements, child)
		removed = append(removed, false)
		if child.Kind != PrintSettingOption && child.Name != (xml.Name{}) {
			indices[printCanonicalKey(child.Name)] = index
			if key, _, ok := printPrefixFamily(child); ok {
				families[key] = index
			}
		}
	}
	for _, child := range delta.Children {
		if err := checkContext(ctx); err != nil {
			return PrintSetting{}, err
		}
		if child.Kind == PrintSettingFeature && dropDeltaLayering && printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "Layering" {
			continue
		}
		if child.Kind == PrintSettingOption {
			elements = append(elements, child)
			removed = append(removed, false)
			continue
		}
		childKey := printCanonicalKey(child.Name)
		familyKey, scope, hasFamily := printPrefixFamily(child)
		replacedIndex := -1
		if hasFamily {
			if existing, exists := families[familyKey]; exists && printCanonicalKey(elements[existing].Name) != childKey {
				if scope < printKeywordScope(elements[existing].Name) {
					continue
				}
				delete(indices, printCanonicalKey(elements[existing].Name))
				delete(families, familyKey)
				removed[existing] = true
				replacedIndex = existing
			}
		}
		if index, exists := indices[childKey]; exists {
			if elements[index].Kind == PrintSettingFeature && child.Kind == PrintSettingFeature {
				mergedChild, err := mergePrintFeature(elements[index], child, ctx)
				if err != nil {
					return PrintSetting{}, err
				}
				elements[index] = mergedChild
			} else {
				if oldKey, _, ok := printPrefixFamily(elements[index]); ok && families[oldKey] == index {
					delete(families, oldKey)
				}
				elements[index] = child
				if hasFamily {
					families[familyKey] = index
				}
			}
		} else if replacedIndex >= 0 {
			removed[replacedIndex] = false
			elements[replacedIndex] = child
			indices[childKey] = replacedIndex
			families[familyKey] = replacedIndex
		} else {
			index := len(elements)
			elements = append(elements, child)
			removed = append(removed, false)
			indices[childKey] = index
			if hasFamily {
				families[familyKey] = index
			}
		}
	}
	merged := make([]PrintSetting, 0, len(elements))
	for index, value := range elements {
		if !removed[index] {
			merged = append(merged, value)
		}
	}
	result := baseline
	if deltaHasOption {
		result.Name = delta.Name
	}
	result.Children = merged
	return result, nil
}

// EncodePrintSettings 校验并编码Framework票据，省略的版本采用1，Value始终写出明确类型
// 结构、预算或取消错误发生在写入调用方流之前，不接管输出流生命周期
// 入参: ctx 取消Context，nil采用Background, output 输出流, settings 设置结构, options 编码参数，nil采用默认值
// 返回: int64 实际写入字节数, error 结构、预算、取消或输出错误
func EncodePrintSettings(ctx context.Context, output io.Writer, settings *PrintSettings, options *PrintSettingsOptions) (int64, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return 0, err
	}
	if output == nil {
		return 0, fmt.Errorf("%w: nil print settings output", ErrInvalid)
	}
	validated, err := validatePrintSettingsModel(settings, configuration, printDocumentTicket)
	if err != nil {
		return 0, err
	}
	root, err := printSettingsRoot(validated, configuration)
	if err != nil {
		return 0, err
	}
	limit := min(configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPartBytes, configuration.Limits.MaxPackageBytes)
	var buffer bytes.Buffer
	if _, err := writePrintSettingsMarkup(&buffer, root, configuration); err != nil {
		return 0, err
	}
	result := packageOutput{writer: output, context: configuration.context, limit: limit}
	_, err = result.Write(buffer.Bytes())
	return result.count, err
}

// printSettingsRoot 生成独立XML结构，过滤作用域后处理子内容，不复制调用方的可变值指针
// 入参: settings 设置结构, options 已校验参数
// 返回: *xmlElement 独立根节点, error 结构、预算或取消错误
func printSettingsRoot(settings *PrintSettings, options printSettingsConfig) (*xmlElement, error) {
	if settings == nil {
		return nil, fmt.Errorf("%w: nil print settings", ErrInvalid)
	}
	return printDocumentRoot(settings.Version, settings.Elements, options, false)
}

// printDocumentRoot 生成票据或能力文档的独立XML结构，共用名称绑定及资源预算，按版本输出标准PSF1或PSF2结构
// 入参: version Framework版本, elements 根内容, options 已校验参数, capabilities 是否为设备能力文档
// 返回: *xmlElement 独立根节点, error 结构、预算或取消错误
func printDocumentRoot(version uint32, elements []PrintSetting, options printSettingsConfig, capabilities bool) (*xmlElement, error) {
	mode := printDocumentTicket
	if capabilities {
		mode = printDocumentCapabilities
	}
	return printDocumentRootWithChangeID(version, "", elements, options, mode)
}

// printDocumentRootWithChangeID 按指定文档模式及可选PDC变更标识生成Framework根节点
// 入参: version Framework版本, changeID 可选PDC变更标识, elements 根内容, options 已校验参数, mode 文档类别模式
// 返回: *xmlElement 独立根节点, error 结构、预算或取消错误
func printDocumentRootWithChangeID(version uint32, changeID string, elements []PrintSetting, options printSettingsConfig, mode printDocumentMode) (*xmlElement, error) {
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	capabilities := mode != printDocumentTicket
	if mode == printDocumentDeviceCapabilities {
		if version == 0 {
			version = 2
		}
		if version != 2 {
			return nil, fmt.Errorf("%w: print device capabilities requires framework version 2", ErrUnsupported)
		}
	} else {
		if version == 0 {
			version = 1
		}
		if version != 1 && version != 2 {
			return nil, fmt.Errorf("%w: print settings framework version", ErrUnsupported)
		}
	}
	framework, prefix := printFrameworkNS, "psf"
	if version == 2 {
		framework, prefix = printFramework2NS, "psf2"
	}
	builder := printSettingsBuilder{options: options, framework: framework, prefixes: map[string]string{framework: prefix}, scope: map[string]string{prefix: framework}, nodes: 1, capabilities: capabilities}
	limit := min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)
	rootName, parameterKind := "PrintTicket", PrintSettingParameterInit
	if mode == printDocumentCapabilities {
		rootName, parameterKind = "PrintCapabilities", PrintSettingParameterDef
	} else if mode == printDocumentDeviceCapabilities {
		rootName, parameterKind = "PrintDeviceCapabilities", PrintSettingParameterDef
	}
	root := &xmlElement{Name: xml.Name{Space: framework, Local: rootName}, Attr: []xml.Attr{{Name: xml.Name{Local: "version"}, Value: strconv.FormatUint(uint64(version), 10)}}, Namespaces: builder.scope}
	if mode == printDocumentDeviceCapabilities && changeID != "" {
		if strings.TrimSpace(changeID) == "" || !xmlTextValid(changeID) {
			return nil, fmt.Errorf("%w: print device capabilities CapabilitiesChangeID", ErrInvalid)
		}
		if int64(len(changeID)) > limit {
			return nil, fmt.Errorf("%w: print settings byte budget", ErrLimit)
		}
		typeText, err := builder.qname(xml.Name{Space: printValueNS, Local: "string"})
		if err != nil {
			return nil, err
		}
		if _, err := builder.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return nil, err
		}
		builder.nodes++
		if builder.nodes > builder.options.Limits.MaxXMLNodes {
			return nil, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
		}
		if err := builder.reserve(int64(len(changeID)) + int64(len(typeText)) + 66); err != nil {
			return nil, err
		}
		root.Children = append(root.Children, &xmlElement{
			Name:       xml.Name{Space: printFramework2NS, Local: "CapabilitiesChangeID"},
			Attr:       []xml.Attr{{Name: xml.Name{Space: xsiNamespace, Local: "type"}, Value: typeText}},
			Text:       changeID,
			Namespaces: builder.scope,
		})
	}
	for _, setting := range elements {
		if setting.Kind != PrintSettingFeature && setting.Kind != parameterKind && setting.Kind != PrintSettingProperty {
			return nil, fmt.Errorf("%w: print settings root child", ErrInvalid)
		}
		if int64(len(setting.Name.Space)) > limit-int64(len(setting.Name.Local)) {
			return nil, fmt.Errorf("%w: print settings name byte budget", ErrLimit)
		}
		if setting.Name.Space == "" || !xmlNCName(setting.Name.Local) || !xmlTextValid(setting.Name.Space) {
			return nil, fmt.Errorf("%w: print settings name", ErrInvalid)
		}
		scope := printKeywordScope(setting.Name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		var node *xmlElement
		var err error
		if mode == printDocumentDeviceCapabilities && setting.Kind == PrintSettingParameterDef {
			node, err = builder.elementV1(setting, 2)
		} else {
			node, err = builder.element(setting, 2)
		}
		if err != nil {
			return nil, err
		}
		root.Children = append(root.Children, node)
	}
	return root, nil
}

// element 将一个设置转换为XML节点，按框架版本分派标准PSF1或原生PSF2编码并在递归前检查资源限制
// 入参: value 设置元素, depth XML层级
// 返回: *xmlElement 独立节点, error 结构、预算或取消错误
func (b *printSettingsBuilder) element(value PrintSetting, depth int) (*xmlElement, error) {
	if b.framework == printFramework2NS {
		return b.elementV2(value, depth)
	}
	return b.elementV1(value, depth)
}

// elementV1 将设置按Print Schema v1显式包装元素语法转换为XML节点，供PSF1文档与PDC根级ParameterDef共用
// 入参: value 设置元素, depth XML层级
// 返回: *xmlElement 独立PSF1节点, error 结构、预算或取消错误
func (b *printSettingsBuilder) elementV1(value PrintSetting, depth int) (*xmlElement, error) {
	if err := checkContext(b.options.context); err != nil {
		return nil, err
	}
	b.nodes++
	if b.nodes > b.options.Limits.MaxXMLNodes || depth > b.options.Limits.MaxXMLDepth {
		return nil, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
	}
	if value.Kind == PrintSettingUnknown || int(value.Kind) >= len(printSettingNames) {
		return nil, fmt.Errorf("%w: print settings element kind", ErrInvalid)
	}
	if value.HasDefault || value.Default {
		return nil, fmt.Errorf("%w: print settings Option default requires version 2", ErrInvalid)
	}
	local := printSettingNames[value.Kind]
	if _, err := b.qname(xml.Name{Space: printFrameworkNS, Local: local}); err != nil {
		return nil, err
	}
	node := &xmlElement{Name: xml.Name{Space: printFrameworkNS, Local: local}, Namespaces: b.scope}
	cost := int64(2*len(local) + 13)
	if value.Constraint != PrintConstraintUnknown {
		if !b.capabilities || value.Kind != PrintSettingOption || int(value.Constraint) >= len(printConstraintNames) {
			return nil, fmt.Errorf("%w: print settings Option constraint", ErrInvalid)
		}
		text, err := b.qname(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
		if err != nil {
			return nil, err
		}
		node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Local: "constrained"}, Value: text})
		cost += int64(len(text)) + 15
	}
	if value.Kind == PrintSettingValue {
		if value.Value == nil || value.Name != (xml.Name{}) || len(value.Children) != 0 {
			return nil, fmt.Errorf("%w: print settings Value structure", ErrInvalid)
		}
		if int64(len(value.Value.Text)) > min(b.options.Limits.MaxMetadataBytes, b.options.Limits.MaxPartBytes, b.options.Limits.MaxPackageBytes) {
			return nil, fmt.Errorf("%w: print settings value byte budget", ErrLimit)
		}
		kind := value.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		text, err := b.qname(kind)
		if err != nil {
			return nil, err
		}
		b.prefixes[xsiNamespace] = "xsi"
		b.scope["xsi"] = xsiNamespace
		node.Attr = []xml.Attr{{Name: xml.Name{Space: xsiNamespace, Local: "type"}, Value: text}}
		node.Text = value.Value.Text
		if kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"}) && value.Value.QName != (xml.Name{}) {
			if value.Value.QName != (xml.Name{}) {
				normalized := *value.Value
				normalized.Type = kind
				node.Text, err = b.valueQName(normalized, node)
				if err != nil {
					return nil, err
				}
			} else if !xmlWhitespace(node.Text) {
				return nil, fmt.Errorf("%w: unresolved print settings QName value", ErrInvalid)
			}
		} else if value.Value.QName != (xml.Name{}) {
			return nil, fmt.Errorf("%w: QName on non-QName print settings value", ErrInvalid)
		}
		if !xmlTextValid(node.Text) {
			return nil, fmt.Errorf("%w: print settings value XML text", ErrInvalid)
		}
		cost += int64(len(node.Text)) + int64(len(text)) + 12
	} else {
		if value.Value != nil {
			return nil, fmt.Errorf("%w: value on print settings container", ErrInvalid)
		}
		if value.Name == (xml.Name{}) {
			if value.Kind != PrintSettingOption {
				return nil, fmt.Errorf("%w: missing print settings name", ErrInvalid)
			}
		} else {
			if value.Name.Space == "" {
				return nil, fmt.Errorf("%w: print settings keyword without namespace", ErrInvalid)
			}
			text, err := b.qname(value.Name)
			if err != nil {
				return nil, err
			}
			node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Local: "name"}, Value: text})
			cost += int64(len(text)) + 8
		}
	}
	if err := b.reserve(cost); err != nil {
		return nil, err
	}
	for _, child := range value.Children {
		parsed, err := b.elementV1(child, depth+1)
		if err != nil {
			return nil, err
		}
		node.Children = append(node.Children, parsed)
	}
	return node, nil
}

// elementV2 将设置按Microsoft Print Schema v2规范转换为直接关键字XML节点，支持内联值、内联ParameterRef、默认标记、约束与选择类型属性
// 入参: value 设置元素, depth XML层级
// 返回: *xmlElement 独立PSF2节点, error 结构、预算或取消错误
func (b *printSettingsBuilder) elementV2(value PrintSetting, depth int) (*xmlElement, error) {
	if err := checkContext(b.options.context); err != nil {
		return nil, err
	}
	b.nodes++
	if b.nodes > b.options.Limits.MaxXMLNodes || depth > b.options.Limits.MaxXMLDepth {
		return nil, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
	}
	if value.Kind == PrintSettingUnknown || int(value.Kind) >= len(printSettingNames) || value.Kind == PrintSettingValue {
		return nil, fmt.Errorf("%w: print settings v2 element kind", ErrInvalid)
	}
	if value.Value != nil {
		return nil, fmt.Errorf("%w: value on print settings container", ErrInvalid)
	}
	if (value.HasDefault || value.Default) && (!b.capabilities || value.Kind != PrintSettingOption) {
		return nil, fmt.Errorf("%w: print settings default requires capability Option", ErrInvalid)
	}
	if value.Constraint != PrintConstraintUnknown && (!b.capabilities || value.Kind != PrintSettingOption || int(value.Constraint) >= len(printConstraintNames)) {
		return nil, fmt.Errorf("%w: print settings Option constraint", ErrInvalid)
	}
	if value.Name.Space == "" {
		return nil, fmt.Errorf("%w: missing print settings v2 keyword name", ErrInvalid)
	}
	if printFrameworkSpace(value.Name.Space) && (printSettingKind(xml.Name{Space: printFrameworkNS, Local: value.Name.Local}) != PrintSettingUnknown || value.Name.Local == "PrintTicket" || value.Name.Local == "PrintCapabilities" || value.Name.Local == "PrintDeviceCapabilities") {
		return nil, fmt.Errorf("%w: print settings v2 framework wrapper element", ErrInvalid)
	}
	nameText, err := b.qname(value.Name)
	if err != nil {
		return nil, err
	}
	local := printSettingNames[value.Kind]
	node := &xmlElement{
		Name:       value.Name,
		Attr:       []xml.Attr{{Name: xml.Name{Space: printFramework2NS, Local: "psftype"}, Value: local}},
		Namespaces: b.scope,
	}
	cost := int64(2*len(nameText) + len(local) + 22)
	if value.Kind == PrintSettingOption {
		if value.HasDefault || value.Default {
			flag := strconv.FormatBool(value.Default)
			node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Space: printFramework2NS, Local: "default"}, Value: flag})
			cost += int64(len(flag)) + 16
		}
		if value.Constraint != PrintConstraintUnknown {
			text, err := b.qname(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
			if err != nil {
				return nil, err
			}
			node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Space: printFramework2NS, Local: "constrained"}, Value: text})
			cost += int64(len(text)) + 20
		}
	}
	selectionIndex, valueIndex, refIndex := -1, -1, -1
	for index, child := range value.Children {
		if b.capabilities && value.Kind == PrintSettingFeature && child.Kind == PrintSettingProperty && printFrameworkSpace(child.Name.Space) && child.Name.Local == "SelectionType" {
			if selectionIndex >= 0 {
				return nil, fmt.Errorf("%w: duplicate print settings SelectionType", ErrInvalid)
			}
			selVal, err := printCommonValue(child)
			if err != nil || selVal.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || !printPublicKeywordSpace(selVal.QName.Space) || (selVal.QName.Local != "PickOne" && selVal.QName.Local != "PickMany") {
				return nil, fmt.Errorf("%w: print settings SelectionType value", ErrInvalid)
			}
			selText, err := b.qname(selVal.QName)
			if err != nil {
				return nil, err
			}
			node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Space: printFramework2NS, Local: "selectiontype"}, Value: selText})
			cost += int64(len(selText)) + 22
			selectionIndex = index
			continue
		}
		if child.Kind == PrintSettingValue {
			if value.Kind != PrintSettingProperty && value.Kind != PrintSettingScoredProperty && value.Kind != PrintSettingParameterInit {
				return nil, fmt.Errorf("%w: print settings v2 Value child", ErrInvalid)
			}
			if valueIndex >= 0 || refIndex >= 0 {
				return nil, fmt.Errorf("%w: multiple print settings values", ErrInvalid)
			}
			valueIndex = index
		}
		if child.Kind == PrintSettingParameterRef {
			if value.Kind != PrintSettingScoredProperty {
				return nil, fmt.Errorf("%w: print settings v2 ParameterRef child", ErrInvalid)
			}
			if valueIndex >= 0 || refIndex >= 0 {
				return nil, fmt.Errorf("%w: multiple print settings values", ErrInvalid)
			}
			refIndex = index
		}
	}
	if err := b.reserve(cost); err != nil {
		return nil, err
	}
	for index, child := range value.Children {
		if index == selectionIndex || index == valueIndex || index == refIndex {
			continue
		}
		parsed, err := b.elementV2(child, depth+1)
		if err != nil {
			return nil, err
		}
		node.Children = append(node.Children, parsed)
	}
	if refIndex >= 0 {
		refChild := value.Children[refIndex]
		if refChild.Name.Space == "" || len(refChild.Children) != 0 || refChild.Value != nil || refChild.Constraint != PrintConstraintUnknown || refChild.HasDefault || refChild.Default {
			return nil, fmt.Errorf("%w: print settings ParameterRef structure", ErrInvalid)
		}
		typeText, err := b.qname(xml.Name{Space: printFrameworkNS, Local: "ParameterRef"})
		if err != nil {
			return nil, err
		}
		if _, err := b.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return nil, err
		}
		refText, err := b.qname(refChild.Name)
		if err != nil {
			return nil, err
		}
		node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Space: xsiNamespace, Local: "type"}, Value: typeText})
		node.Text = refText
		if err := b.reserve(int64(len(refText)) + int64(len(typeText)) + 12); err != nil {
			return nil, err
		}
	}
	if valueIndex >= 0 {
		valChild := value.Children[valueIndex]
		if valChild.Value == nil || valChild.Name != (xml.Name{}) || len(valChild.Children) != 0 || valChild.Constraint != PrintConstraintUnknown || valChild.HasDefault || valChild.Default {
			return nil, fmt.Errorf("%w: print settings Value structure", ErrInvalid)
		}
		if int64(len(valChild.Value.Text)) > min(b.options.Limits.MaxMetadataBytes, b.options.Limits.MaxPartBytes, b.options.Limits.MaxPackageBytes) {
			return nil, fmt.Errorf("%w: print settings value byte budget", ErrLimit)
		}
		kind := valChild.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		if kind == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) && !b.capabilities {
			return nil, fmt.Errorf("%w: print settings ImageableAreaType requires capabilities", ErrInvalid)
		}
		typeText, err := b.qname(kind)
		if err != nil {
			return nil, err
		}
		if _, err := b.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return nil, err
		}
		node.Attr = append(node.Attr, xml.Attr{Name: xml.Name{Space: xsiNamespace, Local: "type"}, Value: typeText})
		node.Text = valChild.Value.Text
		if kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"}) && valChild.Value.QName != (xml.Name{}) {
			if valChild.Value.QName != (xml.Name{}) {
				normalized := *valChild.Value
				normalized.Type = kind
				node.Text, err = b.valueQName(normalized, node)
				if err != nil {
					return nil, err
				}
			} else if !xmlWhitespace(node.Text) {
				return nil, fmt.Errorf("%w: unresolved print settings QName value", ErrInvalid)
			}
		} else if valChild.Value.QName != (xml.Name{}) {
			return nil, fmt.Errorf("%w: QName on non-QName print settings value", ErrInvalid)
		}
		if !xmlTextValid(node.Text) {
			return nil, fmt.Errorf("%w: print settings value XML text", ErrInvalid)
		}
		if err := b.reserve(int64(len(node.Text)) + int64(len(typeText)) + 12); err != nil {
			return nil, err
		}
	}
	return node, nil
}

// qname 将展开名称绑定到根命名空间声明，不复用输入的任意前缀
// 入参: name 展开名称
// 返回: string 有效QName词法形式, error 名称、命名空间或预算错误
func (b *printSettingsBuilder) qname(name xml.Name) (string, error) {
	limit := min(b.options.Limits.MaxMetadataBytes, b.options.Limits.MaxPartBytes, b.options.Limits.MaxPackageBytes)
	if int64(len(name.Space)) > limit-int64(len(name.Local)) {
		return "", fmt.Errorf("%w: print settings expanded name byte budget", ErrLimit)
	}
	if !xmlNCName(name.Local) || !xmlTextValid(name.Space) {
		return "", fmt.Errorf("%w: print settings expanded name", ErrInvalid)
	}
	if name.Space == "" {
		return name.Local, nil
	}
	prefix, exists := b.prefixes[name.Space]
	if !exists {
		if name.Space == xmlnsNamespace {
			return "", fmt.Errorf("%w: reserved print settings namespace", ErrInvalid)
		}
		prefix = printKnownNamespacePrefix(name.Space)
		if prefix == "" || b.scope[prefix] != "" && b.scope[prefix] != name.Space {
			for {
				b.nextPrefix++
				prefix = "n" + strconv.Itoa(b.nextPrefix)
				if b.scope[prefix] == "" || b.scope[prefix] == name.Space {
					break
				}
			}
		}
		if err := b.reserve(int64(len(name.Space)) + int64(len(prefix)) + 9); err != nil {
			return "", err
		}
		b.prefixes[name.Space] = prefix
		b.scope[prefix] = name.Space
	}
	return prefix + ":" + name.Local, nil
}

// valueQName 保留可安全绑定的值前缀，避免改变QName参数字符串默认值的词法长度
// 入参: value 含展开QName的值, node 值节点及其名称作用域
// 返回: string 有效QName文本, error 预算、名称或命名空间绑定错误
func (b *printSettingsBuilder) valueQName(value PrintValue, node *xmlElement) (string, error) {
	text := strings.Trim(value.Text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified && text == value.QName.Local && xmlNCName(text) {
		if value.QName.Space != "" {
			if len(node.Children) > 0 {
				return b.qname(value.QName)
			}
			if err := b.localNamespace(node, "", value.QName.Space, value.Type); err != nil {
				return "", err
			}
		}
		return text, nil
	}
	if qualified && xmlNCName(prefix) && xmlNCName(local) && prefix != "xmlns" && local == value.QName.Local && value.QName.Space != "" && (prefix != "xml" || value.QName.Space == xmlNamespace) {
		if bound := b.scope[prefix]; bound == "" || bound == value.QName.Space {
			if !xmlTextValid(value.QName.Space) || value.QName.Space == xmlnsNamespace || (prefix == "xml") != (value.QName.Space == xmlNamespace) {
				return "", fmt.Errorf("%w: print value namespace", ErrInvalid)
			}
			if bound == "" {
				if err := b.reserve(int64(len(value.QName.Space)) + int64(len(prefix)) + 10); err != nil {
					return "", err
				}
				b.scope[prefix] = value.QName.Space
			}
			return text, nil
		}
		if len(node.Children) > 0 {
			return b.qname(value.QName)
		}
		if err := b.localNamespace(node, prefix, value.QName.Space, value.Type); err != nil {
			return "", err
		}
		return text, nil
	}
	return b.qname(value.QName)
}

// localNamespace 在值节点局部绑定名称，必要时为Framework元素、当前节点元素、类型属性及值类型分配无冲突前缀
// 入参: node 值节点, prefix 需绑定前缀或空默认前缀, uri 命名空间, kind 值类型
// 返回: error 命名空间或资源错误
func (b *printSettingsBuilder) localNamespace(node *xmlElement, prefix, uri string, kind xml.Name) error {
	if !xmlTextValid(uri) || uri == xmlnsNamespace || (prefix == "xml") != (uri == xmlNamespace) {
		return fmt.Errorf("%w: print value namespace", ErrInvalid)
	}
	scope := make(map[string]string, len(node.Namespaces)+5)
	for name, value := range node.Namespaces {
		scope[name] = value
	}
	node.Namespaces = scope
	add := func(name, namespace string) error {
		if err := b.reserve(int64(len(name)) + int64(len(namespace)) + 10); err != nil {
			return err
		}
		scope[name] = namespace
		attribute := xml.Name{Space: xmlnsNamespace, Local: name}
		if name == "" {
			attribute = xml.Name{Local: "xmlns"}
		}
		node.Attr = append(node.Attr, xml.Attr{Name: attribute, Value: namespace})
		return nil
	}
	if err := add(prefix, uri); err != nil {
		return err
	}
	required := []string{b.framework, xsiNamespace, printValueNS}
	if node.Name.Space != "" && node.Name.Space != b.framework && node.Name.Space != xsiNamespace && node.Name.Space != printValueNS {
		required = append(required, node.Name.Space)
	}
	for _, namespace := range required {
		if printSettingsPrefix(scope, namespace) != "" {
			continue
		}
		index := 1
		name := "p1"
		for scope[name] != "" {
			index++
			name = "p" + strconv.Itoa(index)
		}
		if err := add(name, namespace); err != nil {
			return err
		}
	}
	for index := range node.Attr {
		if node.Attr[index].Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			node.Attr[index].Value = printSettingsPrefix(scope, kind.Space) + ":" + kind.Local
		}
	}
	return nil
}

// printSettingsPrefix 从当前作用域选取实际绑定的非默认前缀，不依赖固定拼写
// 入参: scope 命名空间作用域, uri 命名空间
// 返回: string 确定性前缀，没有绑定时为空
func printSettingsPrefix(scope map[string]string, uri string) string {
	preferred := ""
	switch uri {
	case printFrameworkNS:
		preferred = "psf"
	case printFramework2NS:
		preferred = "psf2"
	case printKeywordsNS:
		preferred = "psk"
	case printKeywordsV11NS:
		preferred = "psk11"
	case printKeywordsV12NS:
		preferred = "psk12"
	case printKeywords2NS:
		preferred = "psk2"
	case printValueNS:
		preferred = "xs"
	case xsiNamespace:
		preferred = "xsi"
	}
	if preferred != "" && scope[preferred] == uri {
		return preferred
	}
	result := ""
	for prefix, namespace := range scope {
		if prefix != "" && namespace == uri && (result == "" || prefix < result) {
			result = prefix
		}
	}
	return result
}

// reserve 按生成XML的最小长度预检预算，完整转义后的长度仍由输出计数器校验
// 入参: size 本次最小增量
// 返回: error 字节预算错误
func (b *printSettingsBuilder) reserve(size int64) error {
	limit := min(b.options.Limits.MaxMetadataBytes, b.options.Limits.MaxPartBytes, b.options.Limits.MaxPackageBytes)
	if size > limit-b.bytes {
		return fmt.Errorf("%w: print settings byte budget", ErrLimit)
	}
	b.bytes += size
	return nil
}

// writePrintSettingsMarkup 编码已校验结构，按完整XML转义后的长度检查输出预算
// 入参: output 输出流, root 已校验根, options 已校验参数
// 返回: int64 实际写入字节数, error 取消、预算或输出错误
func writePrintSettingsMarkup(output io.Writer, root *xmlElement, options printSettingsConfig) (int64, error) {
	counted := packageOutput{writer: output, context: options.context, limit: min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)}
	encoder := xml.NewEncoder(&counted)
	if err := encodePrintSettingsNode(encoder, root, options, true); err != nil {
		return counted.count, err
	}
	if err := encoder.Flush(); err != nil {
		return counted.count, err
	}
	return counted.count, nil
}

// encodePrintSettingsNode 编码已校验的Framework结构，根声明绑定共享前缀，冲突值前缀保留节点局部声明
// 入参: encoder XML编码器, node 已校验节点, options 已校验参数, isRoot 是否为文档根节点
// 返回: error 取消或编码错误
func encodePrintSettingsNode(encoder *xml.Encoder, node *xmlElement, options printSettingsConfig, isRoot bool) error {
	if err := checkContext(options.context); err != nil {
		return err
	}
	nodeName := node.Name.Local
	if node.Name.Space != "" {
		nodeName = printSettingsPrefix(node.Namespaces, node.Name.Space) + ":" + node.Name.Local
	}
	start := xml.StartElement{Name: xml.Name{Local: nodeName}}
	if isRoot {
		prefixes := make([]string, 0, len(node.Namespaces))
		for prefix := range node.Namespaces {
			prefixes = append(prefixes, prefix)
		}
		slices.Sort(prefixes)
		for _, prefix := range prefixes {
			if err := xmlNamespaceOutput(prefix, node.Namespaces[prefix]); err != nil {
				return err
			}
			name := "xmlns"
			if prefix != "" {
				name += ":" + prefix
			}
			start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: name}, Value: node.Namespaces[prefix]})
		}
	}
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace {
			if err := xmlNamespaceOutput(attr.Name.Local, attr.Value); err != nil {
				return err
			}
			attr.Name = xml.Name{Local: "xmlns:" + attr.Name.Local}
		} else if attr.Name == (xml.Name{Local: "xmlns"}) {
			if err := xmlNamespaceOutput("", attr.Value); err != nil {
				return err
			}
		} else if attr.Name.Space != "" {
			attr.Name = xml.Name{Local: printSettingsPrefix(node.Namespaces, attr.Name.Space) + ":" + attr.Name.Local}
		}
		start.Attr = append(start.Attr, attr)
	}
	if err := encoder.EncodeToken(start); err != nil {
		return err
	}
	if node.Text != "" {
		if err := encoder.EncodeToken(xml.CharData(node.Text)); err != nil {
			return err
		}
	}
	for _, child := range node.Children {
		if err := encodePrintSettingsNode(encoder, child, options, false); err != nil {
			return err
		}
	}
	return encoder.EncodeToken(start.End())
}
