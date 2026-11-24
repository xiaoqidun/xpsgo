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
	"errors"
	"fmt"
	"io"
	"maps"
	"math/big"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
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
	printFrameworkNS = "http://schemas.microsoft.com/windows/2003/08/printing/printschemaframework"
	printKeywordsNS  = "http://schemas.microsoft.com/windows/2003/08/printing/printschemakeywords"
	printValueNS     = "http://www.w3.org/2001/XMLSchema"
	printTicketType  = "application/vnd.ms-printing.printticket+xml"
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

// PrintSettings 保存Framework版本及打印票据根元素列表
type PrintSettings struct {
	Version  uint32
	Elements []PrintSetting
}

// PrintSetting 保存展开后的关键字名称、子元素或值，不依赖输入XML的前缀拼写
// Option允许省略Name，只有Value元素使用Value，Constraint仅适用于能力文档的Option
type PrintSetting struct {
	Kind       PrintSettingKind
	Name       xml.Name
	Children   []PrintSetting
	Value      *PrintValue
	Constraint PrintConstraint
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

// printSettingsConfig 保存已校验的打印设置预算、关联层级与取消Context
type printSettingsConfig struct {
	PrintSettingsOptions
	context context.Context
}

// printSettingsBuilder 将展开名称绑定到确定性前缀，并约束生成结构的规模
type printSettingsBuilder struct {
	options      printSettingsConfig
	prefixes     map[string]string
	scope        map[string]string
	nodes        int
	bytes        int64
	nextPrefix   int
	capabilities bool
}

// PrintCapabilities 保存当前设备配置的Framework能力描述
type PrintCapabilities struct {
	Version  uint32
	Elements []PrintSetting
}

// printParameterDomain 保存一个参数的基础域及默认值，不解释私有单位或设备间约束
type printParameterDomain struct {
	kind         xml.Name
	defaultValue PrintValue
	mandatory    string
	unit         string
	minimum      *big.Rat
	maximum      *big.Rat
}

// printSelectionChecker 校验能力快照中的选择声明并约束Option及标量比较工作量
type printSelectionChecker struct {
	options     printSettingsConfig
	domains     map[xml.Name]*printParameterDomain
	namespaces  map[string]bool
	diagnostics []Diagnostic
	remaining   int
}

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

// Selection 返回Feature的选择方式，能力文档省略声明时默认为PickOne
// 返回: PrintSelection 选择方式, error 元素或属性错误
func (p PrintSetting) Selection() (PrintSelection, error) {
	if p.Kind != PrintSettingFeature {
		return PrintSelectionUnknown, fmt.Errorf("%w: selection on non-Feature", ErrInvalid)
	}
	for _, property := range p.Children {
		if property.Kind != PrintSettingProperty || property.Name != (xml.Name{Space: printFrameworkNS, Local: "SelectionType"}) {
			continue
		}
		value, err := printCommonValue(property)
		if err != nil || value.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || value.QName.Space != printKeywordsNS {
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
		if property.Kind != PrintSettingProperty || property.Name != (xml.Name{Space: printFrameworkNS, Local: "IdentityOption"}) {
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
			selection := setting.Name == (xml.Name{Space: printFrameworkNS, Local: "SelectionType"})
			identity := setting.Name == (xml.Name{Space: printFrameworkNS, Local: "IdentityOption"})
			displayUI := setting.Name == (xml.Name{Space: printKeywordsNS, Local: "DisplayUI"})
			displayName := setting.Name == (xml.Name{Space: printKeywordsNS, Local: "DisplayName"})
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
		if r.format == FormatXPS && !strings.EqualFold(typeName, printTicketType) {
			return &PartError{Part: part, Err: fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)}
		}
		known, capabilities := printResourceMedia(typeName)
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

// parsePrintDocument 按票据或能力文档规则校验根结构，只有票据执行关联层级过滤
// 入参: root 已解析XML根, options 已校验参数, capabilities 是否为设备能力文档
// 返回: *PrintSettings 独立Framework结构, error 结构、资源或取消错误
func parsePrintDocument(root *xmlElement, options printSettingsConfig, capabilities bool) (*PrintSettings, error) {
	rootName := "PrintTicket"
	if capabilities {
		rootName = "PrintCapabilities"
	}
	if root.Name != (xml.Name{Space: printFrameworkNS, Local: rootName}) || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: print settings root", ErrInvalid)
	}
	if err := printSettingsAttributes(root, "version"); err != nil {
		return nil, err
	}
	version, exists := root.attribute("version")
	version = strings.Trim(version, " \t\r\n")
	if !exists || !printInteger(version) || strings.HasPrefix(version, "-") {
		return nil, fmt.Errorf("%w: print settings version", ErrInvalid)
	}
	version = strings.TrimLeft(strings.TrimPrefix(version, "+"), "0")
	if version == "" {
		return nil, fmt.Errorf("%w: print settings version", ErrInvalid)
	}
	if version != "1" {
		return nil, fmt.Errorf("%w: print settings framework version", ErrUnsupported)
	}
	value := &PrintSettings{Version: 1}
	seen := make(map[xml.Name]bool)
	for _, child := range root.Children {
		if err := checkContext(options.context); err != nil {
			return nil, err
		}
		kind := printSettingKind(child.Name)
		parameterKind := PrintSettingParameterInit
		if capabilities {
			parameterKind = PrintSettingParameterDef
		}
		if kind != PrintSettingFeature && kind != parameterKind && kind != PrintSettingProperty {
			return nil, fmt.Errorf("%w: print settings root child %s", ErrInvalid, child.Name.Local)
		}
		name, err := printSettingsName(child, true)
		if err != nil {
			return nil, err
		}
		scope := printKeywordScope(name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		if seen[name] {
			return nil, fmt.Errorf("%w: duplicate print setting {%s}%s", ErrInvalid, name.Space, name.Local)
		}
		seen[name] = true
		setting, err := parsePrintSetting(child, [len(printSettingNames)]uint8{}, options.context, capabilities)
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
	return printPrefixKey{kind: value.Kind, space: value.Name.Space, local: suffix}, scope, true
}

// printSettingsPrefixConflicts 检查同一父级作用域内同类元素中仅作用域前缀不同的关键字冲突
// 入参: settings 当前父级作用域下的直接子元素列表
// 返回: error 作用域前缀冲突错误
func printSettingsPrefixConflicts(settings []PrintSetting) error {
	seen := make(map[printPrefixKey]xml.Name)
	for _, value := range settings {
		if key, _, ok := printPrefixFamily(value); ok {
			if previous, exists := seen[key]; exists && previous != value.Name {
				return fmt.Errorf("%w: print settings scope prefix conflict {%s}%s and %s", ErrInvalid, value.Name.Space, previous.Local, value.Name.Local)
			}
			seen[key] = value.Name
		}
		if err := printSettingsPrefixConflicts(value.Children); err != nil {
			return err
		}
	}
	return nil
}

// parsePrintSetting 校验单个Framework元素及其子结构，能力文档同类型元素及票据Feature不得嵌套超过十层
// 入参: node XML元素, nesting 各类型已包含的层数, ctx 取消Context, capabilities 是否为设备能力文档
// 返回: PrintSetting 独立设置元素, error 结构、值或取消错误
func parsePrintSetting(node *xmlElement, nesting [len(printSettingNames)]uint8, ctx context.Context, capabilities bool) (PrintSetting, error) {
	value := PrintSetting{Kind: printSettingKind(node.Name)}
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
		var err error
		value.Value, err = parsePrintValue(node)
		return value, err
	}
	if !xmlWhitespace(node.Text) {
		return value, fmt.Errorf("%w: text in print settings %s", ErrInvalid, node.Name.Local)
	}
	allowedAttributes := []string{"name"}
	if capabilities && value.Kind == PrintSettingOption {
		allowedAttributes = append(allowedAttributes, "constrained")
		if text, present := node.attribute("constrained"); present {
			var err error
			value.Constraint, err = printConstraint(node, text)
			if err != nil {
				return value, err
			}
		}
	}
	if err := printSettingsAttributes(node, allowedAttributes...); err != nil {
		return value, err
	}
	var err error
	value.Name, err = printSettingsName(node, value.Kind != PrintSettingOption)
	if err != nil {
		return value, err
	}
	seen := make(map[xml.Name]bool)
	values, choices := 0, 0
	for _, child := range node.Children {
		kind := printSettingKind(child.Name)
		allowed := false
		switch value.Kind {
		case PrintSettingFeature:
			allowed = kind == PrintSettingProperty || kind == PrintSettingFeature || kind == PrintSettingOption
		case PrintSettingOption:
			allowed = kind == PrintSettingProperty || kind == PrintSettingScoredProperty
		case PrintSettingProperty:
			allowed = kind == PrintSettingValue || kind == PrintSettingProperty
		case PrintSettingScoredProperty:
			allowed = kind == PrintSettingValue || kind == PrintSettingParameterRef || kind == PrintSettingProperty || kind == PrintSettingScoredProperty
		case PrintSettingParameterInit:
			allowed = kind == PrintSettingValue
		case PrintSettingParameterDef:
			allowed = capabilities && kind == PrintSettingProperty
		}
		if !allowed {
			return value, fmt.Errorf("%w: %s child in print settings %s", ErrInvalid, child.Name.Local, node.Name.Local)
		}
		parsed, err := parsePrintSetting(child, nesting, ctx, capabilities)
		if err != nil {
			return value, err
		}
		if kind != PrintSettingOption && parsed.Name != (xml.Name{}) {
			if seen[parsed.Name] {
				return value, fmt.Errorf("%w: duplicate print setting child {%s}%s", ErrInvalid, parsed.Name.Space, parsed.Name.Local)
			}
			seen[parsed.Name] = true
		}
		if kind == PrintSettingValue || kind == PrintSettingParameterRef {
			values++
		}
		if kind == PrintSettingFeature || kind == PrintSettingOption {
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
		if err := printParameterDefaultQName(node, &value); err != nil {
			return value, err
		}
	}
	return value, nil
}

// printSettingKind 根据展开名称识别允许的Framework元素
// 入参: name 元素展开名称
// 返回: PrintSettingKind 元素类型，非Framework或未知元素返回Unknown
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

// printSettingsAttributes 检查允许的无命名空间属性及Value的xsi:type，不接受私有XML属性
// 入参: node 元素, allowed 允许的无命名空间属性
// 返回: error 非法属性错误
func printSettingsAttributes(node *xmlElement, allowed ...string) error {
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		valid := false
		for _, name := range allowed {
			valid = valid || name != "" && attribute.Name == (xml.Name{Local: name})
		}
		if valid {
			continue
		}
		if node.Name.Local == "Value" && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
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
	value := &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: node.Text}
	if text, exists := node.attributeNS(xsiNamespace, "type"); exists {
		var err error
		value.Type, err = printSettingsQName(node, text)
		if err != nil {
			return nil, err
		}
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
	baseRoot, err := printSettingsRoot(baseline, configuration)
	if err != nil {
		return nil, err
	}
	base, err := parsePrintSettings(baseRoot, configuration)
	if err != nil {
		return nil, err
	}
	deltaRoot, err := printSettingsRoot(delta, configuration)
	if err != nil {
		return nil, err
	}
	change, err := parsePrintSettings(deltaRoot, configuration)
	if err != nil {
		return nil, err
	}
	elements := make([]PrintSetting, len(base.Elements))
	copy(elements, base.Elements)
	removed := make([]bool, len(elements))
	indices := make(map[xml.Name]int, len(elements))
	families := make(map[printPrefixKey]int, len(elements))
	for index, value := range elements {
		indices[value.Name] = index
		if key, _, ok := printPrefixFamily(value); ok {
			families[key] = index
		}
	}
	for _, value := range change.Elements {
		if err := checkContext(configuration.context); err != nil {
			return nil, err
		}
		familyKey, scope, hasFamily := printPrefixFamily(value)
		replacedIndex := -1
		if hasFamily {
			if existing, exists := families[familyKey]; exists && elements[existing].Name != value.Name {
				if scope < printKeywordScope(elements[existing].Name) {
					continue
				}
				delete(indices, elements[existing].Name)
				delete(families, familyKey)
				removed[existing] = true
				replacedIndex = existing
			}
		}
		if index, exists := indices[value.Name]; exists {
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
			indices[value.Name] = replacedIndex
			families[familyKey] = replacedIndex
		} else {
			index := len(elements)
			elements = append(elements, value)
			removed = append(removed, false)
			indices[value.Name] = index
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
	root, err := printSettingsRoot(base, configuration)
	if err != nil {
		return nil, err
	}
	result, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, err
	}
	if _, err := writePrintSettingsMarkup(io.Discard, root, configuration); err != nil {
		return nil, err
	}
	return result, nil
}

// mergePrintFeature 递归合并同名Feature的直接子Feature、Option与Property，delta未提供直接Option时保留baseline的Option
// 入参: baseline 基础Feature, delta 优先Feature, ctx 取消Context
// 返回: PrintSetting 合并后的Feature, error 取消错误
func mergePrintFeature(baseline, delta PrintSetting, ctx context.Context) (PrintSetting, error) {
	if err := checkContext(ctx); err != nil {
		return PrintSetting{}, err
	}
	deltaHasOption := false
	for _, child := range delta.Children {
		if child.Kind == PrintSettingOption {
			deltaHasOption = true
			break
		}
	}
	elements := make([]PrintSetting, 0, len(baseline.Children)+len(delta.Children))
	removed := make([]bool, 0, len(baseline.Children)+len(delta.Children))
	indices := make(map[xml.Name]int, len(baseline.Children))
	families := make(map[printPrefixKey]int, len(baseline.Children))
	for _, child := range baseline.Children {
		if child.Kind == PrintSettingOption && deltaHasOption {
			continue
		}
		index := len(elements)
		elements = append(elements, child)
		removed = append(removed, false)
		if child.Kind != PrintSettingOption && child.Name != (xml.Name{}) {
			indices[child.Name] = index
			if key, _, ok := printPrefixFamily(child); ok {
				families[key] = index
			}
		}
	}
	for _, child := range delta.Children {
		if err := checkContext(ctx); err != nil {
			return PrintSetting{}, err
		}
		if child.Kind == PrintSettingOption {
			elements = append(elements, child)
			removed = append(removed, false)
			continue
		}
		familyKey, scope, hasFamily := printPrefixFamily(child)
		replacedIndex := -1
		if hasFamily {
			if existing, exists := families[familyKey]; exists && elements[existing].Name != child.Name {
				if scope < printKeywordScope(elements[existing].Name) {
					continue
				}
				delete(indices, elements[existing].Name)
				delete(families, familyKey)
				removed[existing] = true
				replacedIndex = existing
			}
		}
		if index, exists := indices[child.Name]; exists {
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
			indices[child.Name] = replacedIndex
			families[familyKey] = replacedIndex
		} else {
			index := len(elements)
			elements = append(elements, child)
			removed = append(removed, false)
			indices[child.Name] = index
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
	root, err := printSettingsRoot(settings, configuration)
	if err != nil {
		return 0, err
	}
	if _, err := parsePrintSettings(root, configuration); err != nil {
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

// printDocumentRoot 生成票据或能力文档的独立XML结构，共用名称绑定及资源预算
// 入参: version Framework版本, elements 根内容, options 已校验参数, capabilities 是否为设备能力文档
// 返回: *xmlElement 独立根节点, error 结构、预算或取消错误
func printDocumentRoot(version uint32, elements []PrintSetting, options printSettingsConfig, capabilities bool) (*xmlElement, error) {
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	if version == 0 {
		version = 1
	}
	builder := printSettingsBuilder{options: options, prefixes: map[string]string{printFrameworkNS: "psf"}, scope: map[string]string{"psf": printFrameworkNS}, nodes: 1, capabilities: capabilities}
	limit := min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)
	rootName, parameterKind := "PrintTicket", PrintSettingParameterInit
	if capabilities {
		rootName, parameterKind = "PrintCapabilities", PrintSettingParameterDef
	}
	root := &xmlElement{Name: xml.Name{Space: printFrameworkNS, Local: rootName}, Attr: []xml.Attr{{Name: xml.Name{Local: "version"}, Value: strconv.FormatUint(uint64(version), 10)}}, Namespaces: builder.scope}
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
		node, err := builder.element(setting, 2)
		if err != nil {
			return nil, err
		}
		root.Children = append(root.Children, node)
	}
	return root, nil
}

// element 将一个设置转换为XML节点，在递归或分配子结构前检查资源限制
// 入参: value 设置元素, depth XML层级
// 返回: *xmlElement 独立节点, error 结构、预算或取消错误
func (b *printSettingsBuilder) element(value PrintSetting, depth int) (*xmlElement, error) {
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
	local := printSettingNames[value.Kind]
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
		parsed, err := b.element(child, depth+1)
		if err != nil {
			return nil, err
		}
		node.Children = append(node.Children, parsed)
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
		switch name.Space {
		case printKeywordsNS:
			prefix = "psk"
		case printValueNS:
			prefix = "xs"
		case xsiNamespace:
			prefix = "xsi"
		case xmlNamespace:
			prefix = "xml"
		case xmlnsNamespace:
			return "", fmt.Errorf("%w: reserved print settings namespace", ErrInvalid)
		default:
			prefix = ""
		}
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
		if err := b.localNamespace(node, prefix, value.QName.Space, value.Type); err != nil {
			return "", err
		}
		return text, nil
	}
	return b.qname(value.QName)
}

// localNamespace 在值节点局部绑定名称，必要时为Framework元素、类型属性及值类型分配无冲突前缀
// 入参: node 值节点, prefix 需绑定前缀或空默认前缀, uri 命名空间, kind 值类型
// 返回: error 命名空间或资源错误
func (b *printSettingsBuilder) localNamespace(node *xmlElement, prefix, uri string, kind xml.Name) error {
	if !xmlTextValid(uri) || uri == xmlnsNamespace || (prefix == "xml") != (uri == xmlNamespace) {
		return fmt.Errorf("%w: print value namespace", ErrInvalid)
	}
	scope := make(map[string]string, len(node.Namespaces)+4)
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
	for _, namespace := range []string{printFrameworkNS, xsiNamespace, printValueNS} {
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
	if err := encodePrintSettingsNode(encoder, root, options); err != nil {
		return counted.count, err
	}
	if err := encoder.Flush(); err != nil {
		return counted.count, err
	}
	return counted.count, nil
}

// encodePrintSettingsNode 编码已校验的Framework结构，根声明绑定共享前缀，冲突值前缀保留节点局部声明
// 入参: encoder XML编码器, node 已校验节点, options 已校验参数
// 返回: error 取消或编码错误
func encodePrintSettingsNode(encoder *xml.Encoder, node *xmlElement, options printSettingsConfig) error {
	if err := checkContext(options.context); err != nil {
		return err
	}
	start := xml.StartElement{Name: xml.Name{Local: printSettingsPrefix(node.Namespaces, node.Name.Space) + ":" + node.Name.Local}}
	if node.Name.Local == "PrintTicket" || node.Name.Local == "PrintCapabilities" {
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
		if err := encodePrintSettingsNode(encoder, child, options); err != nil {
			return err
		}
	}
	return encoder.EncodeToken(start.End())
}

// ParsePrintCapabilities 校验能力文档的Framework结构、参数域、默认值及选择约束声明
// 不推断私有关键字语义，不访问打印机或外部资源
// 入参: ctx 取消Context，nil采用Background, data UTF-8或UTF-16能力XML, options 资源参数，Scope须为Unknown
// 返回: *PrintCapabilities 独立能力结构, error XML、Framework、资源或取消错误
func ParsePrintCapabilities(ctx context.Context, data []byte, options *PrintSettingsOptions) (*PrintCapabilities, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if configuration.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print capabilities", ErrInvalid)
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	if int64(len(data)) > min(configuration.Limits.MaxPartBytes, configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: print capabilities byte budget", ErrLimit)
	}
	root, err := decodeXML(data, configuration.Limits)
	if err != nil {
		return nil, err
	}
	value, err := parsePrintDocument(root, configuration, true)
	if err != nil {
		return nil, err
	}
	return &PrintCapabilities{Version: value.Version, Elements: value.Elements}, nil
}

// EncodePrintCapabilities 校验并编码能力文档，省略的版本采用1，不修改调用方模型
// Framework、预算或取消错误不会提前写入输出流
// 入参: ctx 取消Context，nil采用Background, output 输出流, capabilities 能力结构, options 资源参数，Scope须为Unknown
// 返回: int64 实际写入字节数, error 结构、预算、取消或输出错误
func EncodePrintCapabilities(ctx context.Context, output io.Writer, capabilities *PrintCapabilities, options *PrintSettingsOptions) (int64, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return 0, err
	}
	if output == nil || capabilities == nil || configuration.Scope != PrintScopeUnknown {
		return 0, fmt.Errorf("%w: print capabilities encode parameters", ErrInvalid)
	}
	root, err := printDocumentRoot(capabilities.Version, capabilities.Elements, configuration, true)
	if err != nil {
		return 0, err
	}
	if _, err := parsePrintDocument(root, configuration, true); err != nil {
		return 0, err
	}
	var buffer bytes.Buffer
	if _, err := writePrintSettingsMarkup(&buffer, root, configuration); err != nil {
		return 0, err
	}
	counted := packageOutput{writer: output, context: configuration.context, limit: min(configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPartBytes, configuration.Limits.MaxPackageBytes)}
	_, err = counted.Write(buffer.Bytes())
	return counted.count, err
}

// printConstraint 解析约束枚举属性及其关键字QName并要求属于Print Schema公共关键字命名空间
// 入参: node Option命名空间作用域, text 约束属性文本
// 返回: PrintConstraint 约束类别, error 非法值错误
func printConstraint(node *xmlElement, text string) (PrintConstraint, error) {
	name, err := printSettingsQName(node, text)
	if err != nil || name.Space != printKeywordsNS {
		return PrintConstraintUnknown, fmt.Errorf("%w: print Option constraint QName", ErrInvalid)
	}
	for value, local := range printConstraintNames {
		if value != 0 && local == name.Local {
			return PrintConstraint(value), nil
		}
	}
	return PrintConstraintUnknown, fmt.Errorf("%w: print Option constraint", ErrInvalid)
}

// printParameterDefaultQName 解析QName参数的字符串默认值，保留其声明位置的名称绑定
// 入参: node ParameterDef原节点, value 已解析参数定义
// 返回: error 默认值QName错误
func printParameterDefaultQName(node *xmlElement, value *PrintSetting) error {
	kind := xml.Name{}
	defaultIndex := -1
	for index, child := range value.Children {
		if child.Name.Space != printFrameworkNS || len(child.Children) != 1 || child.Children[0].Value == nil {
			continue
		}
		if child.Name.Local == "DataType" {
			kind = child.Children[0].Value.QName
		} else if child.Name.Local == "DefaultValue" {
			defaultIndex = index
		}
	}
	if kind != (xml.Name{Space: printValueNS, Local: "QName"}) || defaultIndex < 0 {
		return nil
	}
	item := value.Children[defaultIndex].Children[0].Value
	if item.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
		return fmt.Errorf("%w: QName parameter default value type", ErrInvalid)
	}
	name, err := printSettingsQName(node.Children[defaultIndex].Children[0], item.Text)
	if err != nil {
		return err
	}
	item.QName = name
	return nil
}

// ParameterValue 校验被引用参数的显式值，仅Optional参数允许省略初始值并采用设备默认值
// 不按Multiple量化，不推断私有单位或进行设备配置调整
// 入参: ctx 取消Context，nil采用Background, name 参数展开名称, initializer 显式初始值或nil, options 资源及参数算术预算，Scope须为Unknown
// 返回: *PrintValue 独立参数值, error 未支持参数、定义、类型、范围、资源或取消错误
func (p *PrintCapabilities) ParameterValue(ctx context.Context, name xml.Name, initializer *PrintValue, options *PrintSettingsOptions) (*PrintValue, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if p == nil {
		return nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	if configuration.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print capabilities", ErrInvalid)
	}
	root, err := printDocumentRoot(p.Version, p.Elements, configuration, true)
	if err != nil {
		return nil, err
	}
	model, err := parsePrintDocument(root, configuration, true)
	if err != nil {
		return nil, err
	}
	for _, parameter := range model.Elements {
		if parameter.Kind != PrintSettingParameterDef || parameter.Name != name {
			continue
		}
		domain, err := printParameterDefinition(parameter, configuration)
		if err != nil {
			return nil, err
		}
		value := initializer
		if value == nil {
			if domain.mandatory != "Optional" {
				return nil, fmt.Errorf("%w: print parameter requires explicit initialization", ErrInvalid)
			}
			value = &domain.defaultValue
		}
		return domain.value(value, configuration)
	}
	return nil, fmt.Errorf("%w: print parameter definition not available", ErrUnsupported)
}

// printParameterDefinition 读取四种参数域所必需的Framework属性并校验范围及默认值
// 入参: parameter 参数定义, options 已校验参数
// 返回: *printParameterDomain 基础参数域, error 定义、资源或取消错误
func printParameterDefinition(parameter PrintSetting, options printSettingsConfig) (*printParameterDomain, error) {
	properties := make(map[string]*PrintValue)
	for _, property := range parameter.Children {
		if property.Name.Space != printFrameworkNS {
			continue
		}
		if len(property.Children) != 1 || property.Children[0].Kind != PrintSettingValue || property.Children[0].Value == nil {
			return nil, fmt.Errorf("%w: print parameter property structure", ErrInvalid)
		}
		properties[property.Name.Local] = property.Children[0].Value
	}
	for _, name := range []string{"DataType", "Mandatory", "UnitType", "DefaultValue"} {
		if properties[name] == nil {
			return nil, fmt.Errorf("%w: missing print parameter property %s", ErrInvalid, name)
		}
	}
	dataType, mandatory, unit, defaultValue := properties["DataType"], properties["Mandatory"], properties["UnitType"], properties["DefaultValue"]
	if dataType.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || dataType.QName.Space != printValueNS || mandatory.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || mandatory.QName.Space != printKeywordsNS || unit.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
		return nil, fmt.Errorf("%w: print parameter required property", ErrInvalid)
	}
	domain := &printParameterDomain{kind: dataType.QName, mandatory: mandatory.QName.Local, unit: unit.Text, defaultValue: *defaultValue}
	if domain.mandatory != "Optional" && domain.mandatory != "Conditional" && domain.mandatory != "Unconditional" {
		return nil, fmt.Errorf("%w: print parameter Mandatory", ErrInvalid)
	}
	if parameter.Name.Space == printKeywordsNS {
		units := []string{"characters", "numeric", "sRGB", "base64"}
		switch domain.kind.Local {
		case "QName":
			units = []string{"characters"}
		case "integer":
			units = []string{"copies", "microns", "percent", "points", "degrees", "dpi", "pixels", "sheets"}
		case "decimal":
			units = []string{"microns", "percent", "points", "degrees"}
		}
		if !slices.Contains(units, domain.unit) {
			return nil, fmt.Errorf("%w: public print parameter unit", ErrInvalid)
		}
	}
	var minimum, maximum *PrintValue
	switch domain.kind.Local {
	case "string", "QName":
		minimum, maximum = properties["MinLength"], properties["MaxLength"]
		if minimum == nil || maximum == nil || minimum.Type != (xml.Name{Space: printValueNS, Local: "integer"}) || maximum.Type != minimum.Type {
			return nil, fmt.Errorf("%w: print parameter length type", ErrInvalid)
		}
		if domain.kind.Local == "QName" {
			if defaultValue.Type != (xml.Name{Space: printValueNS, Local: "string"}) || defaultValue.QName.Local == "" {
				return nil, fmt.Errorf("%w: print QName parameter default", ErrInvalid)
			}
			domain.defaultValue.Type = domain.kind
		} else if defaultValue.Type != domain.kind {
			return nil, fmt.Errorf("%w: print string parameter default type", ErrInvalid)
		}
	case "integer", "decimal":
		minimum, maximum = properties["MinValue"], properties["MaxValue"]
		multiple := properties["Multiple"]
		if minimum == nil || maximum == nil || multiple == nil || minimum.Type != domain.kind || maximum.Type != domain.kind || multiple.Type != domain.kind || defaultValue.Type != domain.kind {
			return nil, fmt.Errorf("%w: print numeric parameter property type", ErrInvalid)
		}
		step, err := printParameterNumber(multiple.Text, options)
		if err != nil {
			return nil, err
		}
		if step.Sign() <= 0 {
			return nil, fmt.Errorf("%w: print parameter multiple must be positive", ErrInvalid)
		}
	default:
		return nil, fmt.Errorf("%w: print parameter data type", ErrInvalid)
	}
	var err error
	domain.minimum, err = printParameterNumber(minimum.Text, options)
	if err != nil {
		return nil, err
	}
	domain.maximum, err = printParameterNumber(maximum.Text, options)
	if err != nil {
		return nil, err
	}
	if domain.minimum.Cmp(domain.maximum) > 0 || (domain.kind.Local == "string" && domain.minimum.Sign() < 0) || (domain.kind.Local == "QName" && domain.minimum.Sign() <= 0) {
		return nil, fmt.Errorf("%w: print parameter range", ErrInvalid)
	}
	if parameter.Name.Space == printKeywordsNS && (domain.kind.Local == "string" && domain.unit != "base64" || domain.kind.Local == "QName") && domain.maximum.Cmp(big.NewRat(65535, 1)) > 0 {
		return nil, fmt.Errorf("%w: public print parameter string length", ErrInvalid)
	}
	if domain.kind.Local == "string" && domain.defaultValue.Text == "" {
		return domain, nil
	}
	if _, err := domain.value(&domain.defaultValue, options); err != nil {
		return nil, err
	}
	return domain, nil
}

// value 校验已经声明类型的参数值，返回独立副本，不舍入、截断或补造数值
// 入参: value 待校验值, options 已校验参数
// 返回: *PrintValue 独立副本, error 类型、基础域、资源或取消错误
func (p *printParameterDomain) value(value *PrintValue, options printSettingsConfig) (*PrintValue, error) {
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	if value == nil {
		return nil, fmt.Errorf("%w: nil print parameter value", ErrInvalid)
	}
	kind := value.Type
	if kind == (xml.Name{}) {
		kind = xml.Name{Space: printValueNS, Local: "string"}
	}
	if kind != p.kind {
		return nil, fmt.Errorf("%w: print parameter value type", ErrInvalid)
	}
	if int64(len(value.Text)) > min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: print parameter value byte budget", ErrLimit)
	}
	builder := printSettingsBuilder{options: options, prefixes: map[string]string{printFrameworkNS: "psf"}, scope: map[string]string{"psf": printFrameworkNS}}
	node, err := builder.element(PrintSetting{Kind: PrintSettingValue, Value: value}, 1)
	if err != nil {
		return nil, err
	}
	parsed, err := parsePrintValue(node)
	if err != nil {
		return nil, err
	}
	normalized := *value
	normalized.Type, normalized.Text = parsed.Type, parsed.Text
	if kind.Local == "QName" {
		normalized.QName = parsed.QName
	}
	value = &normalized
	var measure *big.Rat
	if kind.Local == "integer" || kind.Local == "decimal" {
		text := strings.Trim(value.Text, " \t\r\n")
		if kind.Local == "integer" && !printInteger(text) || kind.Local == "decimal" && !printDecimal(text) {
			return nil, fmt.Errorf("%w: print parameter numeric value", ErrInvalid)
		}
		var err error
		measure, err = printParameterNumber(text, options)
		if err != nil {
			return nil, err
		}
	} else if kind.Local == "string" {
		if p.unit == "numeric" {
			for _, character := range value.Text {
				if character < '0' || character > '9' {
					return nil, fmt.Errorf("%w: numeric print parameter string", ErrInvalid)
				}
			}
		} else if p.unit == "sRGB" {
			if len(value.Text) != 9 || value.Text[0] != '#' {
				return nil, fmt.Errorf("%w: sRGB print parameter string", ErrInvalid)
			}
			for _, character := range value.Text[1:] {
				if !((character >= '0' && character <= '9') || (character >= 'a' && character <= 'f') || (character >= 'A' && character <= 'F')) {
					return nil, fmt.Errorf("%w: sRGB print parameter string", ErrInvalid)
				}
			}
		}
		measure = big.NewRat(int64(utf8.RuneCountInString(value.Text)), 1)
	} else {
		if !xmlNCName(value.QName.Local) || !xmlTextValid(value.QName.Space) {
			return nil, fmt.Errorf("%w: unresolved print parameter QName", ErrInvalid)
		}
		measure = big.NewRat(int64(utf8.RuneCountInString(strings.Trim(value.Text, " \t\r\n"))), 1)
	}
	if measure.Cmp(p.minimum) < 0 || measure.Cmp(p.maximum) > 0 {
		return nil, fmt.Errorf("%w: print parameter value outside range", ErrInvalid)
	}
	return value, nil
}

// printParameterNumber 在算术精度预算内解析有限十进制数，不使用浮点近似
// 入参: text 数字文本, options 已校验参数
// 返回: *big.Rat 精确数值, error 词法、资源或取消错误
func printParameterNumber(text string, options printSettingsConfig) (*big.Rat, error) {
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	text = strings.Trim(text, " \t\r\n")
	remaining := options.MaxNumericDigits
	for _, character := range text {
		if character >= '0' && character <= '9' {
			remaining--
			if remaining < 0 {
				return nil, fmt.Errorf("%w: print parameter numeric precision", ErrLimit)
			}
		}
	}
	if !printDecimal(text) {
		return nil, fmt.Errorf("%w: print parameter number", ErrInvalid)
	}
	value, valid := new(big.Rat).SetString(text)
	if !valid {
		return nil, fmt.Errorf("%w: print parameter number", ErrInvalid)
	}
	return value, checkContext(options.context)
}

// ResolvePrintParameters 按能力文档校验票据的已知参数初始值，并将ParameterRef替换为独立值
// 检查Unconditional和被引用的Conditional参数，不按Multiple舍入，不进行Feature选择或设备约束求解
// 入参: ctx 取消Context，nil采用Background, settings 候选票据, capabilities 当前能力描述, options 资源、关联层级及算术预算
// 返回: *PrintSettings 独立解析结构, error 参数缺失、定义、基础域、资源或取消错误
func ResolvePrintParameters(ctx context.Context, settings *PrintSettings, capabilities *PrintCapabilities, options *PrintSettingsOptions) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if capabilities == nil {
		return nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	root, err := printSettingsRoot(settings, configuration)
	if err != nil {
		return nil, err
	}
	model, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, err
	}
	capRoot, err := printDocumentRoot(capabilities.Version, capabilities.Elements, configuration, true)
	if err != nil {
		return nil, err
	}
	capModel, err := parsePrintDocument(capRoot, configuration, true)
	if err != nil {
		return nil, err
	}
	domains := make(map[xml.Name]*printParameterDomain)
	for _, parameter := range capModel.Elements {
		if parameter.Kind != PrintSettingParameterDef {
			continue
		}
		if err := checkContext(configuration.context); err != nil {
			return nil, err
		}
		domain, err := printParameterDefinition(parameter, configuration)
		if err != nil {
			return nil, err
		}
		domains[parameter.Name] = domain
	}
	if err := resolvePrintParameterModel(model, domains, configuration); err != nil {
		return nil, err
	}
	resultRoot, err := printSettingsRoot(model, configuration)
	if err != nil {
		return nil, err
	}
	result, err := parsePrintSettings(resultRoot, configuration)
	if err != nil {
		return nil, err
	}
	if _, err := writePrintSettingsMarkup(io.Discard, resultRoot, configuration); err != nil {
		return nil, err
	}
	return result, nil
}

// resolvePrintParameterModel 在已复制并校验的模型中解析参数，允许选择校验复用已有定义索引
// 入参: model 独立票据模型, domains 已校验参数域, configuration 已校验参数
// 返回: error 初始化、基础域、资源或取消错误
func resolvePrintParameterModel(model *PrintSettings, domains map[xml.Name]*printParameterDomain, configuration printSettingsConfig) error {
	values := make(map[xml.Name]*PrintValue)
	for index := range model.Elements {
		parameter := &model.Elements[index]
		if parameter.Kind != PrintSettingParameterInit {
			continue
		}
		if domain := domains[parameter.Name]; domain != nil {
			value, err := domain.value(parameter.Children[0].Value, configuration)
			if err != nil {
				return err
			}
			parameter.Children[0].Value = value
			values[parameter.Name] = value
		}
	}
	for name, domain := range domains {
		scope := printKeywordScope(name)
		if configuration.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < configuration.Scope {
			continue
		}
		if domain.mandatory == "Unconditional" && values[name] == nil {
			return fmt.Errorf("%w: unconditional print parameter not initialized", ErrInvalid)
		}
	}
	return resolvePrintParameterRefs(model.Elements, domains, values, configuration)
}

// resolvePrintParameterRefs 在已复制结构中解析参数参照，每次使用的值拥有独立指针
// 入参: settings 当前内容, domains 参数定义索引, values 显式初始值索引, options 已校验参数
// 返回: error 缺失参数、必须显式初始化、基础域或取消错误
func resolvePrintParameterRefs(settings []PrintSetting, domains map[xml.Name]*printParameterDomain, values map[xml.Name]*PrintValue, options printSettingsConfig) error {
	for index := range settings {
		if err := checkContext(options.context); err != nil {
			return err
		}
		setting := &settings[index]
		if setting.Kind != PrintSettingParameterRef {
			if err := resolvePrintParameterRefs(setting.Children, domains, values, options); err != nil {
				return err
			}
			continue
		}
		domain := domains[setting.Name]
		if domain == nil {
			return fmt.Errorf("%w: referenced print parameter definition not available", ErrUnsupported)
		}
		value := values[setting.Name]
		if value == nil {
			if domain.mandatory != "Optional" {
				return fmt.Errorf("%w: referenced print parameter requires initialization", ErrInvalid)
			}
			var err error
			value, err = domain.value(&domain.defaultValue, options)
			if err != nil {
				return err
			}
			values[setting.Name] = value
		}
		copy := *value
		*setting = PrintSetting{Kind: PrintSettingValue, Value: &copy}
	}
	return nil
}

// ValidatePrintSelection 校验已知Feature的Option数量、声明值及当前快照约束，报告被忽略的未知命名空间
// 不修改输入，不补充缺少设置，不执行近似评分、动态设备约束或默认配置调整
// 入参: ctx 取消Context，nil采用Background, settings 候选票据, capabilities 当前能力快照, options 资源、作用域及比较预算
// 返回: []Diagnostic 非致命诊断, error 选择、参数、未支持能力、资源或取消错误
func ValidatePrintSelection(ctx context.Context, settings *PrintSettings, capabilities *PrintCapabilities, options *PrintSettingsOptions) ([]Diagnostic, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if capabilities == nil {
		return nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	root, err := printSettingsRoot(settings, configuration)
	if err != nil {
		return nil, err
	}
	model, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, err
	}
	capRoot, err := printDocumentRoot(capabilities.Version, capabilities.Elements, configuration, true)
	if err != nil {
		return nil, err
	}
	capModel, err := parsePrintDocument(capRoot, configuration, true)
	if err != nil {
		return nil, err
	}
	checker := printSelectionChecker{options: configuration, domains: make(map[xml.Name]*printParameterDomain), namespaces: make(map[string]bool), remaining: configuration.MaxOptionComparisons}
	checker.collectNamespaces(capModel.Elements)
	for _, setting := range capModel.Elements {
		if setting.Kind == PrintSettingParameterDef {
			domain, err := printParameterDefinition(setting, configuration)
			if err != nil {
				return nil, err
			}
			checker.domains[setting.Name] = domain
		}
	}
	model.Elements = checker.filter(model.Elements)
	if err := resolvePrintParameterModel(model, checker.domains, configuration); err != nil {
		return checker.diagnostics, err
	}
	err = checker.features(model.Elements, capModel.Elements)
	return checker.diagnostics, err
}

// collectNamespaces 递归收集能力文档声明的全部关键字命名空间
// 入参: settings 能力内容
func (c *printSelectionChecker) collectNamespaces(settings []PrintSetting) {
	for _, setting := range settings {
		if setting.Name.Space != "" {
			c.namespaces[setting.Name.Space] = true
		}
		c.collectNamespaces(setting.Children)
	}
}

// filter 在参数解析前忽略未声明命名空间的设置，保留可能通过描述值匹配的Option名称
// 入参: settings 已复制的候选内容
// 返回: []PrintSetting 保留内容
func (c *printSelectionChecker) filter(settings []PrintSetting) []PrintSetting {
	result := settings[:0]
	for _, setting := range settings {
		if setting.Kind != PrintSettingOption && setting.Kind != PrintSettingParameterRef && setting.Name.Space != "" && !c.namespaces[setting.Name.Space] {
			c.ignored(setting)
			continue
		}
		setting.Children = c.filter(setting.Children)
		result = append(result, setting)
	}
	return result
}

// ignored 为未声明命名空间的设置记录非致命忽略诊断
// 入参: setting 被忽略的设置
func (c *printSelectionChecker) ignored(setting PrintSetting) {
	c.diagnostics = append(c.diagnostics, Diagnostic{Element: printSettingNames[setting.Kind], Attribute: "name", Message: "unknown print setting namespace ignored"})
}

// step 在比较前检查取消及总工作量上限
// 返回: error 资源或取消错误
func (c *printSelectionChecker) step() error {
	if err := checkContext(c.options.context); err != nil {
		return err
	}
	if c.remaining == 0 {
		return fmt.Errorf("%w: print Option comparison budget", ErrLimit)
	}
	c.remaining--
	return nil
}

// features 在同一层级按展开名称匹配Feature，未知命名空间不影响已知设置的校验
// 入参: requested 候选内容, supported 能力内容
// 返回: error 已知Feature未支持、选择或资源错误
func (c *printSelectionChecker) features(requested, supported []PrintSetting) error {
	index := make(map[xml.Name]PrintSetting)
	for _, setting := range supported {
		if setting.Kind == PrintSettingFeature {
			index[setting.Name] = setting
		}
	}
	for _, setting := range requested {
		if setting.Kind != PrintSettingFeature {
			continue
		}
		if err := c.step(); err != nil {
			return err
		}
		capability, exists := index[setting.Name]
		if !exists {
			return fmt.Errorf("%w: print Feature not declared by capabilities", ErrUnsupported)
		}
		if err := c.feature(setting, capability); err != nil {
			return err
		}
	}
	return nil
}

// feature 校验直接Option的选择数量及声明，递归处理同组子Feature
// 入参: requested 候选Feature, supported 能力Feature
// 返回: error 选择、约束或资源错误
func (c *printSelectionChecker) feature(requested, supported PrintSetting) error {
	selection, err := supported.Selection()
	if err != nil {
		return err
	}
	var options []PrintSetting
	byName := make(map[xml.Name][]PrintSetting)
	for _, setting := range supported.Children {
		if setting.Kind == PrintSettingOption {
			options = append(options, setting)
			byName[setting.Name] = append(byName[setting.Name], setting)
		}
	}
	count, identities := 0, 0
	for _, requestedOption := range requested.Children {
		if requestedOption.Kind != PrintSettingOption {
			continue
		}
		count++
		candidates := options
		named := false
		if requestedOption.Name != (xml.Name{}) && len(byName[requestedOption.Name]) > 0 {
			candidates, named = byName[requestedOption.Name], true
		}
		matched := false
		for _, candidate := range candidates {
			if err := c.step(); err != nil {
				return err
			}
			if candidate.Constraint != PrintConstraintUnknown && candidate.Constraint != PrintConstraintNone {
				continue
			}
			if !named && requestedOption.Name != candidate.Name && printScoredCount(requestedOption.Children) == 0 {
				continue
			}
			same, err := c.scored(requestedOption.Children, candidate.Children, named)
			if err != nil {
				return err
			}
			if !same {
				continue
			}
			identity, err := candidate.Identity()
			if err != nil {
				return err
			}
			if identity {
				identities++
			}
			matched = true
			break
		}
		if !matched {
			return fmt.Errorf("%w: print Option not supported by current capabilities", ErrUnsupported)
		}
	}
	if len(options) != 0 && (count == 0 || selection == PrintSelectionOne && count != 1) {
		return fmt.Errorf("%w: print Feature selection count", ErrInvalid)
	}
	if identities > 0 && count > 1 {
		c.diagnostics = append(c.diagnostics, Diagnostic{Element: "Feature", Message: "identity print Option selected with other Options"})
	}
	return c.features(requested.Children, supported.Children)
}

// printScoredCount 统计当前层级的ScoredProperty，不让说明性Property影响匹配
// 入参: settings 当前内容
// 返回: int 声明数量
func printScoredCount(settings []PrintSetting) int {
	count := 0
	for _, setting := range settings {
		if setting.Kind == PrintSettingScoredProperty {
			count++
		}
	}
	return count
}

// scored 匹配声明值及嵌套ScoredProperty，命名选项允许省略设备已知的描述值
// 入参: requested 请求内容, supported 能力内容, subset 是否允许请求省略描述
// 返回: bool 是否匹配, error 资源、参数定义或取消错误
func (c *printSelectionChecker) scored(requested, supported []PrintSetting, subset bool) (bool, error) {
	if !subset && printScoredCount(requested) != printScoredCount(supported) {
		return false, nil
	}
	index := make(map[xml.Name]PrintSetting)
	for _, setting := range supported {
		if setting.Kind == PrintSettingScoredProperty {
			index[setting.Name] = setting
		}
	}
	for _, setting := range requested {
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := c.step(); err != nil {
			return false, err
		}
		capability, exists := index[setting.Name]
		if !exists {
			return false, nil
		}
		requestValue, _ := printScoredValue(setting.Children)
		capValue, reference := printScoredValue(capability.Children)
		if reference != (xml.Name{}) {
			domain := c.domains[reference]
			if domain == nil {
				return false, fmt.Errorf("%w: print Option parameter definition not available", ErrUnsupported)
			}
			if _, err := domain.value(requestValue, c.options); err != nil {
				if errors.Is(err, ErrInvalid) {
					return false, nil
				}
				return false, err
			}
		} else {
			same, err := c.value(requestValue, capValue)
			if err != nil || !same {
				return same, err
			}
		}
		if same, err := c.scored(setting.Children, capability.Children, subset); err != nil || !same {
			return same, err
		}
	}
	return true, nil
}

// printScoredValue 获取ScoredProperty的唯一值或参数参照
// 入参: settings 已校验子内容
// 返回: *PrintValue 直接值或nil, xml.Name 参数参照或空名称
func printScoredValue(settings []PrintSetting) (*PrintValue, xml.Name) {
	for _, setting := range settings {
		if setting.Kind == PrintSettingValue {
			return setting.Value, xml.Name{}
		}
		if setting.Kind == PrintSettingParameterRef {
			return nil, setting.Name
		}
	}
	return nil, xml.Name{}
}

// value 按基本类型比较值，数值采用精确比较，QName按展开名称比较
// 入参: requested 请求值, supported 能力值
// 返回: bool 是否等值, error 资源或取消错误
func (c *printSelectionChecker) value(requested, supported *PrintValue) (bool, error) {
	if err := c.step(); err != nil {
		return false, err
	}
	if requested == nil || supported == nil || requested.Type != supported.Type {
		return false, nil
	}
	switch requested.Type.Local {
	case "QName":
		return requested.QName == supported.QName, nil
	case "integer", "decimal":
		left, right := strings.Trim(requested.Text, " \t\r\n"), strings.Trim(supported.Text, " \t\r\n")
		if left == "" || right == "" {
			return left == right, nil
		}
		a, err := printParameterNumber(left, c.options)
		if err != nil {
			return false, err
		}
		b, err := printParameterNumber(right, c.options)
		if err != nil {
			return false, err
		}
		return a.Cmp(b) == 0, nil
	default:
		return requested.Text == supported.Text, nil
	}
}
