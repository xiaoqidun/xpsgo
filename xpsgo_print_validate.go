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
	"math/big"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

// PrintCapabilities 保存当前设备配置的Framework能力描述
type PrintCapabilities struct {
	Version  uint32
	Elements []PrintSetting
}

// PrintImageableAreaSummary 保存能力文档声明的可打印介质尺寸与可打印区域（微米）
type PrintImageableAreaSummary struct {
	WidthMicrons        int64
	HeightMicrons       int64
	OriginWidthMicrons  int64
	OriginHeightMicrons int64
	ExtentWidthMicrons  int64
	ExtentHeightMicrons int64
}

// PrintMediaSummary 保存能力文档支持的单个纸型选项只读摘要
type PrintMediaSummary struct {
	Name          xml.Name
	StandardName  string
	WidthMicrons  int64
	HeightMicrons int64
	ImageableArea *PrintImageableAreaSummary
	Default       bool
	Constrained   PrintConstraint
}

// PrintResolutionSummary 保存能力文档支持的单个输出分辨率选项只读摘要
type PrintResolutionSummary struct {
	Name        xml.Name
	X           int
	Y           int
	Default     bool
	Constrained PrintConstraint
}

// PrintParameterSummary 保存能力文档声明的单个参数域只读摘要
type PrintParameterSummary struct {
	Name         xml.Name
	DataType     string
	UnitType     string
	Mandatory    string
	MinValue     string
	MaxValue     string
	Multiple     string
	DefaultValue string
}

// PrintFeatureSummary 保存能力文档中标准或自定义Feature的选择方式与选项只读摘要
type PrintFeatureSummary struct {
	Name           xml.Name
	Selection      PrintSelection
	Options        []xml.Name
	DefaultOptions []xml.Name
}

// PrintCapabilitiesSummary 保存PrintCapabilities的通用只读能力摘要视图
type PrintCapabilitiesSummary struct {
	Version          uint32
	ImageableArea    *PrintImageableAreaSummary
	MediaSizes       []PrintMediaSummary
	Resolutions      []PrintResolutionSummary
	Orientations     []string
	DuplexModes      []PrintDuplex
	NUpCounts        []int
	ColorModes       []PrintColorMode
	ColorManagements []string
	RenderingIntents []string
	OutputQualities  []string
	Bindings         []PrintBinding
	Staples          []string
	HolePunches      []string
	Folds            []string
	Borderless       bool
	Watermark        bool
	Parameters       []PrintParameterSummary
	Features         []PrintFeatureSummary
}

// printParameterDomain 保存一个参数的基础域、步进及默认值，不解释私有单位或设备间约束
type printParameterDomain struct {
	kind         xml.Name
	defaultValue PrintValue
	mandatory    string
	unit         string
	minimum      *big.Rat
	maximum      *big.Rat
	multiple     *big.Rat
}

// printSelectionChecker 校验能力快照中的选择声明并约束Option及标量比较工作量
type printSelectionChecker struct {
	options     printSettingsConfig
	domains     map[xml.Name]*printParameterDomain
	namespaces  map[string]bool
	diagnostics []Diagnostic
	remaining   int
}

// printModelValidator 在纯内存中校验PrintSettings结构、作用域、嵌套、节点与字节预算
type printModelValidator struct {
	options      printSettingsConfig
	capabilities bool
	limit        int64
	nodes        int
	bytes        int64
}

// printBudgetEstimator 在纯内存中按XML序列化与转义规则精确核算输出字节预算与命名空间URI
type printBudgetEstimator struct {
	options      printSettingsConfig
	capabilities bool
	framework    string
	limit        int64
	prefixes     map[string]string
	scope        map[string]string
	nextPrefix   int
	bytes        int64
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

// Settings 返回当前PrintCapabilities的独立PrintSettings能力树副本，可直接用于规范化与合并
// 返回: *PrintSettings 独立能力树副本，接收者为nil时返回nil
func (p *PrintCapabilities) Settings() *PrintSettings {
	if p == nil {
		return nil
	}
	elements := make([]PrintSetting, len(p.Elements))
	for index, element := range p.Elements {
		elements[index] = printCloneSetting(element)
	}
	return &PrintSettings{Version: p.Version, Elements: elements}
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
	validated, err := validatePrintSettingsModel(&PrintSettings{Version: capabilities.Version, Elements: capabilities.Elements}, configuration, printDocumentCapabilities)
	if err != nil {
		return 0, err
	}
	root, err := printDocumentRoot(validated.Version, validated.Elements, configuration, true)
	if err != nil {
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
	if err != nil || !printPublicKeywordSpace(name.Space) {
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
// 入参: node ParameterDef原节点, value 已解析参数定义, psf2 是否为Print Schema v2直接元素
// 返回: error 默认值QName错误
func printParameterDefaultQName(node *xmlElement, value *PrintSetting, psf2 bool) error {
	kind := xml.Name{}
	defaultIndex := -1
	for index, child := range value.Children {
		if !printFrameworkSpace(child.Name.Space) || len(child.Children) != 1 || child.Children[0].Value == nil {
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
	scopeNode := node.Children[defaultIndex]
	if !psf2 && len(scopeNode.Children) > 0 {
		scopeNode = scopeNode.Children[0]
	}
	name, err := printSettingsQName(scopeNode, item.Text)
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
	model, err := validatePrintSettingsModel(&PrintSettings{Version: p.Version, Elements: p.Elements}, configuration, printDocumentCapabilities)
	if err != nil {
		return nil, err
	}
	target := printCanonicalKey(name)
	for _, parameter := range model.Elements {
		if parameter.Kind != PrintSettingParameterDef || printCanonicalKey(parameter.Name) != target {
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
		if !printFrameworkSpace(property.Name.Space) {
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
	if dataType.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || dataType.QName.Space != printValueNS || mandatory.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || !printPublicKeywordSpace(mandatory.QName.Space) || unit.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
		return nil, fmt.Errorf("%w: print parameter required property", ErrInvalid)
	}
	domain := &printParameterDomain{kind: dataType.QName, mandatory: mandatory.QName.Local, unit: unit.Text, defaultValue: *defaultValue}
	if domain.mandatory != "Optional" && domain.mandatory != "Conditional" && domain.mandatory != "Unconditional" {
		return nil, fmt.Errorf("%w: print parameter Mandatory", ErrInvalid)
	}
	if strings.TrimSpace(domain.unit) == "" {
		return nil, fmt.Errorf("%w: empty print parameter unit", ErrInvalid)
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
		domain.multiple = step
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
	if printPublicKeywordSpace(parameter.Name.Space) && (domain.kind.Local == "string" && domain.unit != "base64" || domain.kind.Local == "QName") && domain.maximum.Cmp(big.NewRat(65535, 1)) > 0 {
		return nil, fmt.Errorf("%w: public print parameter string length", ErrInvalid)
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
	parsed, err := validatePrintValueModel(value, false, options)
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
	if p.multiple != nil {
		diff := new(big.Rat).Sub(measure, p.minimum)
		if !new(big.Rat).Quo(diff, p.multiple).IsInt() {
			return nil, fmt.Errorf("%w: print parameter value multiple step", ErrInvalid)
		}
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
	model, err := validatePrintSettingsModel(settings, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	capModel, err := validatePrintSettingsModel(&PrintSettings{Version: capabilities.Version, Elements: capabilities.Elements}, configuration, printDocumentCapabilities)
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
		domains[printCanonicalKey(parameter.Name)] = domain
	}
	if err := resolvePrintParameterModel(model, domains, configuration); err != nil {
		return nil, err
	}
	result, err := validatePrintSettingsModel(model, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsOutputBudget(result, configuration, printDocumentTicket); err != nil {
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
		key := printCanonicalKey(parameter.Name)
		if domain := domains[key]; domain != nil {
			value, err := domain.value(parameter.Children[0].Value, configuration)
			if err != nil {
				return err
			}
			parameter.Children[0].Value = value
			values[key] = value
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
		key := printCanonicalKey(setting.Name)
		domain := domains[key]
		if domain == nil {
			return fmt.Errorf("%w: referenced print parameter definition not available", ErrUnsupported)
		}
		value := values[key]
		if value == nil {
			if domain.mandatory != "Optional" {
				return fmt.Errorf("%w: referenced print parameter requires initialization", ErrInvalid)
			}
			var err error
			value, err = domain.value(&domain.defaultValue, options)
			if err != nil {
				return err
			}
			values[key] = value
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
	model, err := validatePrintSettingsModel(settings, configuration, printDocumentTicket)
	if err != nil {
		return nil, err
	}
	capModel, err := validatePrintSettingsModel(&PrintSettings{Version: capabilities.Version, Elements: capabilities.Elements}, configuration, printDocumentCapabilities)
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
			checker.domains[printCanonicalKey(setting.Name)] = domain
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
			c.namespaces[printCanonicalKey(setting.Name).Space] = true
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
		if setting.Kind != PrintSettingOption && setting.Kind != PrintSettingParameterRef && setting.Name.Space != "" && !c.namespaces[printCanonicalKey(setting.Name).Space] {
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
			index[printCanonicalKey(setting.Name)] = setting
		}
	}
	for _, setting := range requested {
		if setting.Kind != PrintSettingFeature {
			continue
		}
		if err := c.step(); err != nil {
			return err
		}
		capability, exists := index[printCanonicalKey(setting.Name)]
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
			key := printCanonicalKey(setting.Name)
			byName[key] = append(byName[key], setting)
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
		reqKey := printCanonicalKey(requestedOption.Name)
		if requestedOption.Name != (xml.Name{}) && len(byName[reqKey]) > 0 {
			candidates, named = byName[reqKey], true
		}
		matched := false
		for _, candidate := range candidates {
			if err := c.step(); err != nil {
				return err
			}
			if candidate.Constraint != PrintConstraintUnknown && candidate.Constraint != PrintConstraintNone {
				continue
			}
			if !named && reqKey != printCanonicalKey(candidate.Name) && printScoredCount(requestedOption.Children) == 0 {
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
			index[printCanonicalKey(setting.Name)] = setting
		}
	}
	for _, setting := range requested {
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := c.step(); err != nil {
			return false, err
		}
		capability, exists := index[printCanonicalKey(setting.Name)]
		if !exists {
			return false, nil
		}
		requestValue, _ := printScoredValue(setting.Children)
		capValue, reference := printScoredValue(capability.Children)
		if reference != (xml.Name{}) {
			domain := c.domains[printCanonicalKey(reference)]
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

// printValuesEqual 按基本类型精确比较两个PrintValue是否等价，数值使用精确有理数比较
// 入参: requested 请求值, supported 能力值, options 解析与数值预算选项, canonicalQName 是否按规范命名空间键比较QName
// 返回: bool 是否等值, error 预算或取消错误
func printValuesEqual(requested, supported *PrintValue, options printSettingsConfig, canonicalQName bool) (bool, error) {
	if requested == nil || supported == nil || requested.Type != supported.Type {
		return false, nil
	}
	switch requested.Type.Local {
	case "QName":
		if canonicalQName {
			return printCanonicalKey(requested.QName) == printCanonicalKey(supported.QName), nil
		}
		return requested.QName == supported.QName, nil
	case "integer", "decimal":
		left, right := strings.Trim(requested.Text, " \t\r\n"), strings.Trim(supported.Text, " \t\r\n")
		if left == "" || right == "" {
			return left == right, nil
		}
		a, err := printParameterNumber(left, options)
		if err != nil {
			return false, err
		}
		b, err := printParameterNumber(right, options)
		if err != nil {
			return false, err
		}
		return a.Cmp(b) == 0, nil
	default:
		return requested.Text == supported.Text, nil
	}
}

// value 按基本类型比较值，数值采用精确比较，QName按展开名称比较
// 入参: requested 请求值, supported 能力值
// 返回: bool 是否等值, error 资源或取消错误
func (c *printSelectionChecker) value(requested, supported *PrintValue) (bool, error) {
	if err := c.step(); err != nil {
		return false, err
	}
	return printValuesEqual(requested, supported, c.options, false)
}

// printSettingsHasAnonymousOption 递归检查设置树中是否存在无名称的Option节点
// 入参: elements 待检查设置元素切片
// 返回: bool 是否存在匿名Option
func printSettingsHasAnonymousOption(elements []PrintSetting) bool {
	for _, element := range elements {
		if element.Kind == PrintSettingOption && element.Name == (xml.Name{}) {
			return true
		}
		if printSettingsHasAnonymousOption(element.Children) {
			return true
		}
	}
	return false
}

// printStripOptionDefaults 递归清除所有设置节点的Print Schema v2默认选项标记，供降级至v1序列化使用
// 入参: elements 待清理设置元素切片
func printStripOptionDefaults(elements []PrintSetting) {
	for index := range elements {
		elements[index].HasDefault = false
		elements[index].Default = false
		printStripOptionDefaults(elements[index].Children)
	}
}

// ParsePrintDeviceCapabilities 解析Windows V4驱动PrintDeviceCapabilities文档并校验PSF2结构与参数域
// 支持标准psf2:PrintDeviceCapabilities根元素并允许省略或显式声明version="2"，Scope须为Unknown
// 入参: ctx 取消Context，nil采用Background, data UTF-8或UTF-16设备能力XML, options 解析参数，nil采用默认值
// 返回: *PrintSettings 独立设备能力结构, error XML、Framework、资源或取消错误
func ParsePrintDeviceCapabilities(ctx context.Context, data []byte, options *PrintSettingsOptions) (*PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if configuration.Scope != PrintScopeUnknown {
		return nil, fmt.Errorf("%w: scope on print device capabilities", ErrInvalid)
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	if int64(len(data)) > min(configuration.Limits.MaxPartBytes, configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: print device capabilities byte budget", ErrLimit)
	}
	root, err := decodeXML(data, configuration.Limits)
	if err != nil {
		return nil, err
	}
	return parsePrintDocumentMode(root, configuration, printDocumentDeviceCapabilities)
}

// EncodePrintDeviceCapabilities 校验并按原生PSF2语法编码Windows V4驱动PrintDeviceCapabilities文档
// 省略的版本采用2，不修改调用方模型，结构、预算或取消错误不会提前写入输出流
// 入参: ctx 取消Context，nil采用Background, output 输出流, settings 设备能力结构, options 编码参数，Scope须为Unknown
// 返回: int64 实际写入字节数, error 结构、预算、取消或输出错误
func EncodePrintDeviceCapabilities(ctx context.Context, output io.Writer, settings *PrintSettings, options *PrintSettingsOptions) (int64, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return 0, err
	}
	if output == nil || settings == nil || configuration.Scope != PrintScopeUnknown {
		return 0, fmt.Errorf("%w: print device capabilities encode parameters", ErrInvalid)
	}
	validated, err := validatePrintSettingsModel(settings, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return 0, err
	}
	root, err := printDocumentRootWithChangeID(validated.Version, validated.CapabilitiesChangeID, validated.Elements, configuration, printDocumentDeviceCapabilities)
	if err != nil {
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

// validatePrintSettingsModel 在纯内存中校验PrintSettings结构、版本、作用域过滤、嵌套层数、重复冲突与参数定义并返回独立副本
// 入参: settings 待校验设置模型, options 已校验预算与作用域配置, mode 文档类别模式
// 返回: *PrintSettings 校验通过后的独立规范副本, error 结构、版本、预算或取消错误
func validatePrintSettingsModel(settings *PrintSettings, options printSettingsConfig, mode printDocumentMode) (*PrintSettings, error) {
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	if settings == nil {
		return nil, fmt.Errorf("%w: nil print settings", ErrInvalid)
	}
	capabilities := mode != printDocumentTicket
	version := settings.Version
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
	limit := min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)
	validator := printModelValidator{
		options:      options,
		capabilities: capabilities,
		limit:        limit,
		nodes:        1,
	}
	result := &PrintSettings{Version: version}
	if mode == printDocumentDeviceCapabilities && settings.CapabilitiesChangeID != "" {
		changeID := settings.CapabilitiesChangeID
		if strings.TrimSpace(changeID) == "" || !xmlTextValid(changeID) {
			return nil, fmt.Errorf("%w: print device capabilities CapabilitiesChangeID", ErrInvalid)
		}
		if int64(len(changeID)) > limit {
			return nil, fmt.Errorf("%w: print settings byte budget", ErrLimit)
		}
		validator.nodes++
		if validator.nodes > options.Limits.MaxXMLNodes {
			return nil, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
		}
		if err := validator.reserve(int64(len(changeID)) + 75); err != nil {
			return nil, err
		}
		result.CapabilitiesChangeID = changeID
	}
	parameterKind := PrintSettingParameterInit
	if capabilities {
		parameterKind = PrintSettingParameterDef
	}
	seen := make(map[xml.Name]bool, len(settings.Elements))
	for _, element := range settings.Elements {
		if err := checkContext(options.context); err != nil {
			return nil, err
		}
		if element.Kind != PrintSettingFeature && element.Kind != parameterKind && element.Kind != PrintSettingProperty {
			return nil, fmt.Errorf("%w: print settings root child", ErrInvalid)
		}
		if int64(len(element.Name.Space)) > limit-int64(len(element.Name.Local)) {
			return nil, fmt.Errorf("%w: print settings name byte budget", ErrLimit)
		}
		if element.Name.Space == "" || !xmlNCName(element.Name.Local) || !xmlTextValid(element.Name.Space) || element.Name.Space == xmlnsNamespace {
			return nil, fmt.Errorf("%w: print settings name", ErrInvalid)
		}
		scope := printKeywordScope(element.Name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		key := printCanonicalKey(element.Name)
		if seen[key] {
			return nil, fmt.Errorf("%w: duplicate print setting {%s}%s", ErrInvalid, element.Name.Space, element.Name.Local)
		}
		seen[key] = true
		elemVersion := version
		if mode == printDocumentDeviceCapabilities && element.Kind == PrintSettingParameterDef {
			elemVersion = 1
		}
		validated, err := validator.setting(element, elemVersion, 2, [len(printSettingNames)]uint8{})
		if err != nil {
			return nil, err
		}
		if validated.Kind == PrintSettingParameterDef {
			if _, err := printParameterDefinition(validated, options); err != nil {
				return nil, fmt.Errorf("print parameter {%s}%s: %w", validated.Name.Space, validated.Name.Local, err)
			}
		}
		result.Elements = append(result.Elements, validated)
	}
	if err := printSettingsPrefixConflicts(result.Elements); err != nil {
		return nil, err
	}
	if err := validatePrintCommon(result.Elements, PrintSettingUnknown, capabilities); err != nil {
		return nil, err
	}
	return result, nil
}

// reserve 在纯内存校验阶段累计最小序列化字节下界并检查是否超出预算
// 入参: size 本次新增最小字节数
// 返回: error 字节预算超限错误
func (v *printModelValidator) reserve(size int64) error {
	if size > v.limit-v.bytes {
		return fmt.Errorf("%w: print settings byte budget", ErrLimit)
	}
	v.bytes += size
	return nil
}

// validateName 校验展开名称的本地名、命名空间合法性及字节预算
// 入参: name 待校验展开名称
// 返回: error 名称非法或预算超限错误
func (v *printModelValidator) validateName(name xml.Name) error {
	if int64(len(name.Space)) > v.limit-int64(len(name.Local)) {
		return fmt.Errorf("%w: print settings expanded name byte budget", ErrLimit)
	}
	if !xmlNCName(name.Local) || !xmlTextValid(name.Space) || name.Space == xmlnsNamespace {
		return fmt.Errorf("%w: print settings expanded name", ErrInvalid)
	}
	return nil
}

// setting 按节点所属框架版本分派纯内存结构校验
// 入参: value 待校验设置元素, version 节点适用框架版本, depth 当前XML深度, nesting 各类型祖先嵌套层数
// 返回: PrintSetting 校验并深拷贝后的元素, error 结构、预算或取消错误
func (v *printModelValidator) setting(value PrintSetting, version uint32, depth int, nesting [len(printSettingNames)]uint8) (PrintSetting, error) {
	if version == 2 {
		return v.settingV2(value, depth, nesting)
	}
	return v.settingV1(value, depth, nesting)
}

// settingV1 按Print Schema v1语法规则纯内存校验设置节点及其子树
// 入参: value 待校验设置元素, depth 当前XML深度, nesting 各类型祖先嵌套层数
// 返回: PrintSetting 校验并深拷贝后的元素, error 结构、预算或取消错误
func (v *printModelValidator) settingV1(value PrintSetting, depth int, nesting [len(printSettingNames)]uint8) (PrintSetting, error) {
	if err := checkContext(v.options.context); err != nil {
		return PrintSetting{}, err
	}
	v.nodes++
	if v.nodes > v.options.Limits.MaxXMLNodes || depth > v.options.Limits.MaxXMLDepth {
		return PrintSetting{}, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
	}
	if value.Kind == PrintSettingUnknown || int(value.Kind) >= len(printSettingNames) {
		return PrintSetting{}, fmt.Errorf("%w: print settings element kind", ErrInvalid)
	}
	if value.HasDefault || value.Default {
		return PrintSetting{}, fmt.Errorf("%w: print settings Option default requires version 2", ErrInvalid)
	}
	nesting[value.Kind]++
	if (v.capabilities || value.Kind == PrintSettingFeature) && nesting[value.Kind] > 10 {
		return PrintSetting{}, fmt.Errorf("%w: print settings element nesting", ErrInvalid)
	}
	local := printSettingNames[value.Kind]
	cost := int64(2*len(local) + 13)
	if value.Constraint != PrintConstraintUnknown {
		if !v.capabilities || value.Kind != PrintSettingOption || int(value.Constraint) >= len(printConstraintNames) {
			return PrintSetting{}, fmt.Errorf("%w: print settings Option constraint", ErrInvalid)
		}
		cost += int64(len(printConstraintNames[value.Constraint])) + 19
	}
	if value.Kind == PrintSettingValue {
		if value.Value == nil || value.Name != (xml.Name{}) || len(value.Children) != 0 {
			return PrintSetting{}, fmt.Errorf("%w: print settings Value structure", ErrInvalid)
		}
		validatedVal, err := validatePrintValueModel(value.Value, false, v.options)
		if err != nil {
			return PrintSetting{}, err
		}
		cost += int64(len(validatedVal.Text)) + int64(len(validatedVal.Type.Local)) + 12
		if err := v.reserve(cost); err != nil {
			return PrintSetting{}, err
		}
		return PrintSetting{Kind: PrintSettingValue, Value: validatedVal}, nil
	}
	if value.Value != nil {
		return PrintSetting{}, fmt.Errorf("%w: value on print settings container", ErrInvalid)
	}
	if value.Name == (xml.Name{}) {
		if value.Kind != PrintSettingOption {
			return PrintSetting{}, fmt.Errorf("%w: missing print settings name", ErrInvalid)
		}
	} else {
		if value.Name.Space == "" {
			return PrintSetting{}, fmt.Errorf("%w: print settings keyword without namespace", ErrInvalid)
		}
		if err := v.validateName(value.Name); err != nil {
			return PrintSetting{}, err
		}
		cost += int64(len(value.Name.Local)) + 10
	}
	if err := v.reserve(cost); err != nil {
		return PrintSetting{}, err
	}
	out := PrintSetting{Kind: value.Kind, Name: value.Name, Constraint: value.Constraint}
	seen := make(map[xml.Name]bool, len(value.Children))
	values, choices := 0, 0
	for _, child := range value.Children {
		allowed := false
		switch value.Kind {
		case PrintSettingFeature:
			allowed = child.Kind == PrintSettingProperty || child.Kind == PrintSettingFeature || child.Kind == PrintSettingOption
		case PrintSettingOption:
			allowed = child.Kind == PrintSettingProperty || child.Kind == PrintSettingScoredProperty
		case PrintSettingProperty:
			allowed = child.Kind == PrintSettingValue || child.Kind == PrintSettingProperty
		case PrintSettingScoredProperty:
			allowed = child.Kind == PrintSettingValue || child.Kind == PrintSettingParameterRef || child.Kind == PrintSettingProperty || child.Kind == PrintSettingScoredProperty
		case PrintSettingParameterInit:
			allowed = child.Kind == PrintSettingValue
		case PrintSettingParameterDef:
			allowed = v.capabilities && child.Kind == PrintSettingProperty
		}
		if !allowed {
			return PrintSetting{}, fmt.Errorf("%w: %s child in print settings %s", ErrInvalid, child.Kind.String(), value.Kind.String())
		}
		parsed, err := v.settingV1(child, depth+1, nesting)
		if err != nil {
			return PrintSetting{}, err
		}
		if parsed.Kind != PrintSettingOption && parsed.Name != (xml.Name{}) {
			key := printCanonicalKey(parsed.Name)
			if seen[key] {
				return PrintSetting{}, fmt.Errorf("%w: duplicate print setting child {%s}%s", ErrInvalid, parsed.Name.Space, parsed.Name.Local)
			}
			seen[key] = true
		}
		if parsed.Kind == PrintSettingValue || parsed.Kind == PrintSettingParameterRef {
			values++
		}
		if parsed.Kind == PrintSettingFeature || parsed.Kind == PrintSettingOption {
			choices++
		}
		out.Children = append(out.Children, parsed)
	}
	valid := true
	switch out.Kind {
	case PrintSettingFeature:
		valid = choices > 0
	case PrintSettingProperty:
		valid = len(out.Children) > 0 && values <= 1
	case PrintSettingScoredProperty, PrintSettingParameterInit:
		valid = values == 1
	case PrintSettingParameterRef:
		valid = len(out.Children) == 0
	case PrintSettingParameterDef:
		valid = v.capabilities
	}
	if !valid {
		return PrintSetting{}, fmt.Errorf("%w: print settings %s child count", ErrInvalid, out.Kind.String())
	}
	if out.Kind == PrintSettingParameterDef {
		if err := validatePrintParameterDefaultQName(&out); err != nil {
			return PrintSetting{}, err
		}
	}
	return out, nil
}

// settingV2 按Print Schema v2语法规则纯内存校验直接关键字节点、内联值、内联ParameterRef与属性约束
// 入参: value 待校验设置元素, depth 当前XML深度, nesting 各类型祖先嵌套层数
// 返回: PrintSetting 校验并深拷贝后的元素, error 结构、预算或取消错误
func (v *printModelValidator) settingV2(value PrintSetting, depth int, nesting [len(printSettingNames)]uint8) (PrintSetting, error) {
	if err := checkContext(v.options.context); err != nil {
		return PrintSetting{}, err
	}
	v.nodes++
	if v.nodes > v.options.Limits.MaxXMLNodes || depth > v.options.Limits.MaxXMLDepth {
		return PrintSetting{}, fmt.Errorf("%w: print settings XML complexity", ErrLimit)
	}
	if value.Kind == PrintSettingUnknown || int(value.Kind) >= len(printSettingNames) || value.Kind == PrintSettingValue {
		return PrintSetting{}, fmt.Errorf("%w: print settings v2 element kind", ErrInvalid)
	}
	if value.Value != nil {
		return PrintSetting{}, fmt.Errorf("%w: value on print settings container", ErrInvalid)
	}
	if (value.HasDefault || value.Default) && (!v.capabilities || value.Kind != PrintSettingOption) {
		return PrintSetting{}, fmt.Errorf("%w: print settings default requires capability Option", ErrInvalid)
	}
	if value.Constraint != PrintConstraintUnknown && (!v.capabilities || value.Kind != PrintSettingOption || int(value.Constraint) >= len(printConstraintNames)) {
		return PrintSetting{}, fmt.Errorf("%w: print settings Option constraint", ErrInvalid)
	}
	if value.Name.Space == "" {
		return PrintSetting{}, fmt.Errorf("%w: missing print settings v2 keyword name", ErrInvalid)
	}
	if printFrameworkSpace(value.Name.Space) && (printSettingKind(xml.Name{Space: printFrameworkNS, Local: value.Name.Local}) != PrintSettingUnknown || value.Name.Local == "PrintTicket" || value.Name.Local == "PrintCapabilities" || value.Name.Local == "PrintDeviceCapabilities") {
		return PrintSetting{}, fmt.Errorf("%w: print settings v2 framework wrapper element", ErrInvalid)
	}
	if err := v.validateName(value.Name); err != nil {
		return PrintSetting{}, err
	}
	nesting[value.Kind]++
	if (v.capabilities || value.Kind == PrintSettingFeature) && nesting[value.Kind] > 10 {
		return PrintSetting{}, fmt.Errorf("%w: print settings element nesting", ErrInvalid)
	}
	local := printSettingNames[value.Kind]
	cost := int64(2*len(value.Name.Local) + len(local) + 22)
	out := PrintSetting{Kind: value.Kind, Name: value.Name, Constraint: value.Constraint}
	if value.Kind == PrintSettingOption {
		if value.HasDefault || value.Default {
			out.HasDefault = true
			out.Default = value.Default
			cost += 20
		}
		if value.Constraint != PrintConstraintUnknown {
			cost += int64(len(printConstraintNames[value.Constraint])) + 24
		}
	}
	selectionIndex, valueIndex, refIndex := -1, -1, -1
	var selectionProp *PrintSetting
	for index, child := range value.Children {
		if v.capabilities && value.Kind == PrintSettingFeature && child.Kind == PrintSettingProperty && printFrameworkSpace(child.Name.Space) && child.Name.Local == "SelectionType" {
			if selectionIndex >= 0 {
				return PrintSetting{}, fmt.Errorf("%w: duplicate print settings SelectionType", ErrInvalid)
			}
			selVal, err := printCommonValue(child)
			if err != nil || selVal.Type != (xml.Name{Space: printValueNS, Local: "QName"}) || !printPublicKeywordSpace(selVal.QName.Space) || (selVal.QName.Local != "PickOne" && selVal.QName.Local != "PickMany") {
				return PrintSetting{}, fmt.Errorf("%w: print settings SelectionType value", ErrInvalid)
			}
			selText, err := printCanonicalValueQName(*selVal)
			if err != nil {
				return PrintSetting{}, err
			}
			prop := PrintSetting{
				Kind: PrintSettingProperty,
				Name: xml.Name{Space: printFrameworkNS, Local: "SelectionType"},
				Children: []PrintSetting{{
					Kind:  PrintSettingValue,
					Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: selText, QName: selVal.QName},
				}},
			}
			selectionProp = &prop
			cost += int64(len(selText)) + 22
			selectionIndex = index
			continue
		}
		if child.Kind == PrintSettingValue {
			if value.Kind != PrintSettingProperty && value.Kind != PrintSettingScoredProperty && value.Kind != PrintSettingParameterInit {
				return PrintSetting{}, fmt.Errorf("%w: print settings v2 Value child", ErrInvalid)
			}
			if valueIndex >= 0 || refIndex >= 0 {
				return PrintSetting{}, fmt.Errorf("%w: multiple print settings values", ErrInvalid)
			}
			valueIndex = index
		}
		if child.Kind == PrintSettingParameterRef {
			if value.Kind != PrintSettingScoredProperty {
				return PrintSetting{}, fmt.Errorf("%w: print settings v2 ParameterRef child", ErrInvalid)
			}
			if valueIndex >= 0 || refIndex >= 0 {
				return PrintSetting{}, fmt.Errorf("%w: multiple print settings values", ErrInvalid)
			}
			refIndex = index
		}
	}
	if err := v.reserve(cost); err != nil {
		return PrintSetting{}, err
	}
	seen := make(map[xml.Name]bool, len(value.Children))
	values, choices := 0, 0
	if selectionProp != nil {
		seen[printCanonicalKey(selectionProp.Name)] = true
		out.Children = append(out.Children, *selectionProp)
	}
	if refIndex >= 0 {
		refChild := value.Children[refIndex]
		if refChild.Name.Space == "" || len(refChild.Children) != 0 || refChild.Value != nil || refChild.Constraint != PrintConstraintUnknown || refChild.HasDefault || refChild.Default {
			return PrintSetting{}, fmt.Errorf("%w: print settings ParameterRef structure", ErrInvalid)
		}
		if err := v.validateName(refChild.Name); err != nil {
			return PrintSetting{}, err
		}
		if err := v.reserve(int64(len(refChild.Name.Local)) + 26); err != nil {
			return PrintSetting{}, err
		}
		values++
		out.Children = append(out.Children, PrintSetting{Kind: PrintSettingParameterRef, Name: refChild.Name})
	}
	if valueIndex >= 0 {
		valChild := value.Children[valueIndex]
		if valChild.Value == nil || valChild.Name != (xml.Name{}) || len(valChild.Children) != 0 || valChild.Constraint != PrintConstraintUnknown || valChild.HasDefault || valChild.Default {
			return PrintSetting{}, fmt.Errorf("%w: print settings Value structure", ErrInvalid)
		}
		validatedVal, err := validatePrintValueModel(valChild.Value, v.capabilities, v.options)
		if err != nil {
			return PrintSetting{}, err
		}
		if err := v.reserve(int64(len(validatedVal.Text)) + int64(len(validatedVal.Type.Local)) + 12); err != nil {
			return PrintSetting{}, err
		}
		values++
		out.Children = append(out.Children, PrintSetting{Kind: PrintSettingValue, Value: validatedVal})
	}
	for index, child := range value.Children {
		if index == selectionIndex || index == valueIndex || index == refIndex {
			continue
		}
		allowed := false
		switch value.Kind {
		case PrintSettingFeature:
			allowed = child.Kind == PrintSettingProperty || child.Kind == PrintSettingFeature || child.Kind == PrintSettingOption
		case PrintSettingOption:
			allowed = child.Kind == PrintSettingProperty || child.Kind == PrintSettingScoredProperty
		case PrintSettingProperty:
			allowed = child.Kind == PrintSettingProperty
		case PrintSettingScoredProperty:
			allowed = child.Kind == PrintSettingProperty || child.Kind == PrintSettingScoredProperty
		case PrintSettingParameterDef:
			allowed = v.capabilities && child.Kind == PrintSettingProperty
		}
		if !allowed {
			return PrintSetting{}, fmt.Errorf("%w: %s child in print settings %s", ErrInvalid, child.Kind.String(), value.Kind.String())
		}
		parsed, err := v.settingV2(child, depth+1, nesting)
		if err != nil {
			return PrintSetting{}, err
		}
		if parsed.Kind != PrintSettingOption && parsed.Name != (xml.Name{}) {
			key := printCanonicalKey(parsed.Name)
			if seen[key] {
				return PrintSetting{}, fmt.Errorf("%w: duplicate print setting child {%s}%s", ErrInvalid, parsed.Name.Space, parsed.Name.Local)
			}
			seen[key] = true
		}
		if parsed.Kind == PrintSettingFeature || parsed.Kind == PrintSettingOption {
			choices++
		}
		out.Children = append(out.Children, parsed)
	}
	valid := true
	switch out.Kind {
	case PrintSettingFeature:
		valid = choices > 0
	case PrintSettingProperty:
		valid = len(out.Children) > 0 && values <= 1
	case PrintSettingScoredProperty, PrintSettingParameterInit:
		valid = values == 1
	case PrintSettingParameterRef:
		valid = len(out.Children) == 0
	case PrintSettingParameterDef:
		valid = v.capabilities
	}
	if !valid {
		return PrintSetting{}, fmt.Errorf("%w: print settings %s child count", ErrInvalid, out.Kind.String())
	}
	if out.Kind == PrintSettingParameterDef {
		if err := validatePrintParameterDefaultQName(&out); err != nil {
			return PrintSetting{}, err
		}
	}
	return out, nil
}

// validatePrintValueModel 在纯内存中校验单个PrintValue的类型、词法、QName与字节预算，不构造临时XML节点
// 入参: value 待校验标量值, allowPSF2 是否允许PSF2能力专属ImageableAreaType, options 已校验资源预算参数
// 返回: *PrintValue 校验并规范化后的独立值副本, error 类型、词法、命名空间或预算错误
func validatePrintValueModel(value *PrintValue, allowPSF2 bool, options printSettingsConfig) (*PrintValue, error) {
	if value == nil {
		return nil, fmt.Errorf("%w: nil print settings value", ErrInvalid)
	}
	limit := min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)
	if int64(len(value.Text)) > limit {
		return nil, fmt.Errorf("%w: print settings value byte budget", ErrLimit)
	}
	kind := value.Type
	if kind == (xml.Name{}) {
		kind = xml.Name{Space: printValueNS, Local: "string"}
	}
	if int64(len(kind.Space)) > limit-int64(len(kind.Local)) {
		return nil, fmt.Errorf("%w: print settings expanded name byte budget", ErrLimit)
	}
	if !xmlNCName(kind.Local) || !xmlTextValid(kind.Space) || kind.Space == xmlnsNamespace {
		return nil, fmt.Errorf("%w: print settings Value type", ErrInvalid)
	}
	if allowPSF2 && kind == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
		if value.QName != (xml.Name{}) {
			return nil, fmt.Errorf("%w: QName on non-QName print settings value", ErrInvalid)
		}
		if !xmlTextValid(value.Text) || !printImageableAreaValid(value.Text) {
			return nil, fmt.Errorf("%w: print settings ImageableAreaType value", ErrInvalid)
		}
		return &PrintValue{Type: kind, Text: value.Text}, nil
	}
	if kind.Space != printValueNS {
		return nil, fmt.Errorf("%w: print settings Value type", ErrInvalid)
	}
	out := &PrintValue{Type: kind, Text: value.Text, QName: value.QName}
	if kind.Local == "QName" || kind.Local == "string" && value.QName != (xml.Name{}) {
		if value.QName != (xml.Name{}) {
			if int64(len(value.QName.Space)) > limit-int64(len(value.QName.Local)) {
				return nil, fmt.Errorf("%w: print settings expanded name byte budget", ErrLimit)
			}
			text, err := printCanonicalValueQName(*out)
			if err != nil {
				return nil, err
			}
			out.Text = text
		} else if !xmlWhitespace(out.Text) {
			return nil, fmt.Errorf("%w: unresolved print settings QName value", ErrInvalid)
		}
	} else if value.QName != (xml.Name{}) {
		return nil, fmt.Errorf("%w: QName on non-QName print settings value", ErrInvalid)
	}
	if !xmlTextValid(out.Text) {
		return nil, fmt.Errorf("%w: print settings value XML text", ErrInvalid)
	}
	trimmed := strings.Trim(out.Text, " \t\r\n")
	switch kind.Local {
	case "string", "QName":
	case "integer":
		if trimmed != "" && !printInteger(trimmed) {
			return nil, fmt.Errorf("%w: print settings integer value", ErrInvalid)
		}
	case "decimal":
		if trimmed != "" && !printDecimal(trimmed) {
			return nil, fmt.Errorf("%w: print settings decimal value", ErrInvalid)
		}
	default:
		return nil, fmt.Errorf("%w: print settings %s value", ErrInvalid, kind.Local)
	}
	return out, nil
}

// printCanonicalValueQName 在纯内存中校验含QName的值并返回可安全保留或规范化的词法QName文本
// 入参: value 含非空QName的值
// 返回: string 词法QName文本, error 名称或命名空间错误
func printCanonicalValueQName(value PrintValue) (string, error) {
	if !xmlNCName(value.QName.Local) || !xmlTextValid(value.QName.Space) || value.QName.Space == xmlnsNamespace {
		return "", fmt.Errorf("%w: print settings QName value", ErrInvalid)
	}
	text := strings.Trim(value.Text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified && text == value.QName.Local && xmlNCName(text) {
		if value.QName.Space == xmlNamespace {
			return "", fmt.Errorf("%w: print value namespace", ErrInvalid)
		}
		return text, nil
	}
	if qualified && xmlNCName(prefix) && xmlNCName(local) && prefix != "xmlns" && local == value.QName.Local && value.QName.Space != "" && (prefix != "xml" || value.QName.Space == xmlNamespace) {
		if (prefix == "xml") != (value.QName.Space == xmlNamespace) {
			return "", fmt.Errorf("%w: print value namespace", ErrInvalid)
		}
		return text, nil
	}
	if value.QName.Space == "" {
		return value.QName.Local, nil
	}
	known := printKnownNamespacePrefix(value.QName.Space)
	if known == "" {
		known = "n1"
	}
	return known + ":" + value.QName.Local, nil
}

// printKnownNamespacePrefix 返回标准Print Schema及XML已知命名空间的默认推荐前缀
// 入参: uri 命名空间URI
// 返回: string 标准推荐前缀，非标准命名空间返回空字符串
func printKnownNamespacePrefix(uri string) string {
	switch uri {
	case printFrameworkNS:
		return "psf"
	case printFramework2NS:
		return "psf2"
	case printKeywordsNS:
		return "psk"
	case printKeywordsV11NS:
		return "psk11"
	case printKeywordsV12NS:
		return "psk12"
	case printKeywords2NS:
		return "psk2"
	case printValueNS:
		return "xs"
	case xsiNamespace:
		return "xsi"
	case xmlNamespace:
		return "xml"
	default:
		return ""
	}
}

// validatePrintParameterDefaultQName 校验QName类型ParameterDef的字符串默认值并补全无前缀展开名
// 入参: value 已完成基础结构校验的ParameterDef节点指针
// 返回: error 默认值类型或QName错误
func validatePrintParameterDefaultQName(value *PrintSetting) error {
	kind := xml.Name{}
	defaultIndex := -1
	for index, child := range value.Children {
		if !printFrameworkSpace(child.Name.Space) || len(child.Children) != 1 || child.Children[0].Value == nil {
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
	if item.QName != (xml.Name{}) {
		if !xmlNCName(item.QName.Local) || !xmlTextValid(item.QName.Space) || item.QName.Space == xmlnsNamespace {
			return fmt.Errorf("%w: print settings QName value", ErrInvalid)
		}
		return nil
	}
	trimmed := strings.Trim(item.Text, " \t\r\n")
	if !strings.Contains(trimmed, ":") && xmlNCName(trimmed) {
		item.QName = xml.Name{Local: trimmed}
		return nil
	}
	return fmt.Errorf("%w: print settings QName %q", ErrInvalid, item.Text)
}

// validatePrintSettingsOutputBudget 在纯内存中按XML序列化与转义规则精确核算输出字节数与命名空间URI合法性，不构造DOM树
// 入参: settings 已校验打印设置模型, options 已校验资源预算配置, mode 文档类别模式
// 返回: error 命名空间URI非法、字节预算超限或取消错误
func validatePrintSettingsOutputBudget(settings *PrintSettings, options printSettingsConfig, mode printDocumentMode) error {
	if err := checkContext(options.context); err != nil {
		return err
	}
	capabilities := mode != printDocumentTicket
	version := settings.Version
	if version == 0 {
		if mode == printDocumentDeviceCapabilities {
			version = 2
		} else {
			version = 1
		}
	}
	framework, prefix := printFrameworkNS, "psf"
	if version == 2 {
		framework, prefix = printFramework2NS, "psf2"
	}
	rootName := "PrintTicket"
	if mode == printDocumentCapabilities {
		rootName = "PrintCapabilities"
	} else if mode == printDocumentDeviceCapabilities {
		rootName = "PrintDeviceCapabilities"
	}
	estimator := printBudgetEstimator{
		options:      options,
		capabilities: capabilities,
		framework:    framework,
		limit:        min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes),
		prefixes:     map[string]string{framework: prefix},
		scope:        map[string]string{prefix: framework},
	}
	rootTagLen := int64(len(prefix) + 1 + len(rootName))
	versionText := strconv.FormatUint(uint64(version), 10)
	if err := estimator.add(2*rootTagLen + 5 + int64(len(` version="`)+len(versionText)+1)); err != nil {
		return err
	}
	if mode == printDocumentDeviceCapabilities && settings.CapabilitiesChangeID != "" {
		typeText, err := estimator.qname(xml.Name{Space: printValueNS, Local: "string"})
		if err != nil {
			return err
		}
		if _, err := estimator.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		tagLen := int64(len(prefix) + 1 + len("CapabilitiesChangeID"))
		attrLen := int64(len(" xsi:type=\"")) + printXMLEscapedLen(typeText, true) + 1
		if err := estimator.add(2*tagLen + 5 + attrLen + printXMLEscapedLen(settings.CapabilitiesChangeID, false)); err != nil {
			return err
		}
	}
	for _, setting := range settings.Elements {
		if err := checkContext(options.context); err != nil {
			return err
		}
		scope := printKeywordScope(setting.Name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		var err error
		if version == 2 && !(mode == printDocumentDeviceCapabilities && setting.Kind == PrintSettingParameterDef) {
			err = estimator.elementV2(setting)
		} else {
			err = estimator.elementV1(setting)
		}
		if err != nil {
			return err
		}
	}
	prefixes := make([]string, 0, len(estimator.scope))
	for p := range estimator.scope {
		prefixes = append(prefixes, p)
	}
	slices.Sort(prefixes)
	for _, p := range prefixes {
		uri := estimator.scope[p]
		if err := xmlNamespaceOutput(p, uri); err != nil {
			return err
		}
		nameLen := int64(len("xmlns"))
		if p != "" {
			nameLen += 1 + int64(len(p))
		}
		if err := estimator.add(1 + nameLen + 2 + printXMLEscapedLen(uri, true) + 1); err != nil {
			return err
		}
	}
	return nil
}

// add 向精确字节估算器累加字节数并校验预算上限
// 入参: size 新增字节数
// 返回: error 字节预算超限错误
func (e *printBudgetEstimator) add(size int64) error {
	if size > e.limit-e.bytes {
		return fmt.Errorf("%w: print settings byte budget", ErrLimit)
	}
	e.bytes += size
	return nil
}

// qname 复刻printSettingsBuilder的前缀分配规则并返回确定性QName文本
// 入参: name 展开名称
// 返回: string 词法QName, error 名称或命名空间错误
func (e *printBudgetEstimator) qname(name xml.Name) (string, error) {
	if name.Space == "" {
		return name.Local, nil
	}
	prefix, exists := e.prefixes[name.Space]
	if !exists {
		if name.Space == xmlnsNamespace {
			return "", fmt.Errorf("%w: reserved print settings namespace", ErrInvalid)
		}
		prefix = printKnownNamespacePrefix(name.Space)
		if prefix == "" || e.scope[prefix] != "" && e.scope[prefix] != name.Space {
			for {
				e.nextPrefix++
				prefix = "n" + strconv.Itoa(e.nextPrefix)
				if e.scope[prefix] == "" || e.scope[prefix] == name.Space {
					break
				}
			}
		}
		e.prefixes[name.Space] = prefix
		e.scope[prefix] = name.Space
	}
	return prefix + ":" + name.Local, nil
}

// valueQNameCost 计算含QName标量值的文本、局部命名空间附加属性字节数及局部命名空间作用域映射
// 入参: value 含QName的标量值, nodeSpace 所在元素命名空间, hasChildren 所在元素是否含XML子节点
// 返回: string 最终文本, int64 局部命名空间额外字节, map[string]string 若局部重绑定则返回局部命名空间作用域映射, error 命名空间或预算错误
func (e *printBudgetEstimator) valueQNameCost(value PrintValue, nodeSpace string, hasChildren bool) (string, int64, map[string]string, error) {
	text := strings.Trim(value.Text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified && text == value.QName.Local && xmlNCName(text) {
		if value.QName.Space != "" {
			if hasChildren {
				qn, err := e.qname(value.QName)
				return qn, 0, nil, err
			}
			extra, localScope, err := e.localNamespaceCost(nodeSpace, "", value.QName.Space)
			return text, extra, localScope, err
		}
		return text, 0, nil, nil
	}
	if qualified && xmlNCName(prefix) && xmlNCName(local) && prefix != "xmlns" && local == value.QName.Local && value.QName.Space != "" && (prefix != "xml" || value.QName.Space == xmlNamespace) {
		if bound := e.scope[prefix]; bound == "" || bound == value.QName.Space {
			if !xmlTextValid(value.QName.Space) || value.QName.Space == xmlnsNamespace || (prefix == "xml") != (value.QName.Space == xmlNamespace) {
				return "", 0, nil, fmt.Errorf("%w: print value namespace", ErrInvalid)
			}
			if bound == "" {
				e.scope[prefix] = value.QName.Space
			}
			return text, 0, nil, nil
		}
		if hasChildren {
			qn, err := e.qname(value.QName)
			return qn, 0, nil, err
		}
		extra, localScope, err := e.localNamespaceCost(nodeSpace, prefix, value.QName.Space)
		return text, extra, localScope, err
	}
	qn, err := e.qname(value.QName)
	return qn, 0, nil, err
}

// localNamespaceCost 复刻printSettingsBuilder.localNamespace逻辑并核算局部xmlns属性字节与输出URI校验
// 入参: nodeSpace 元素命名空间, prefix 局部前缀或空默认前缀, uri 局部命名空间URI
// 返回: int64 局部xmlns属性总字节数, map[string]string 局部作用域映射, error URI非法错误
func (e *printBudgetEstimator) localNamespaceCost(nodeSpace, prefix, uri string) (int64, map[string]string, error) {
	if err := xmlNamespaceOutput(prefix, uri); err != nil {
		return 0, nil, err
	}
	scope := make(map[string]string, len(e.scope)+5)
	for k, v := range e.scope {
		scope[k] = v
	}
	var extra int64
	addLocal := func(name, namespace string) error {
		if err := xmlNamespaceOutput(name, namespace); err != nil {
			return err
		}
		scope[name] = namespace
		attrNameLen := int64(len("xmlns"))
		if name != "" {
			attrNameLen += 1 + int64(len(name))
		}
		extra += 1 + attrNameLen + 2 + printXMLEscapedLen(namespace, true) + 1
		return nil
	}
	if err := addLocal(prefix, uri); err != nil {
		return 0, nil, err
	}
	required := []string{e.framework, xsiNamespace, printValueNS}
	if nodeSpace != "" && nodeSpace != e.framework && nodeSpace != xsiNamespace && nodeSpace != printValueNS {
		required = append(required, nodeSpace)
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
		if err := addLocal(name, namespace); err != nil {
			return 0, nil, err
		}
	}
	return extra, scope, nil
}

// elementV1 按PSF1编码格式精确核算单个节点及其子树的序列化字节数
// 入参: value 已校验设置元素
// 返回: error 命名空间、预算或取消错误
func (e *printBudgetEstimator) elementV1(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	local := printSettingNames[value.Kind]
	tag, err := e.qname(xml.Name{Space: printFrameworkNS, Local: local})
	if err != nil {
		return err
	}
	var attrsLen int64
	if value.Constraint != PrintConstraintUnknown {
		cText, err := e.qname(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
		if err != nil {
			return err
		}
		attrsLen += int64(len(` constrained="`)) + printXMLEscapedLen(cText, true) + 1
	}
	if value.Kind == PrintSettingValue {
		kind := value.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		typeText, err := e.qname(kind)
		if err != nil {
			return err
		}
		e.prefixes[xsiNamespace] = "xsi"
		e.scope["xsi"] = xsiNamespace
		text := value.Value.Text
		var localScope map[string]string
		if kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"}) && value.Value.QName != (xml.Name{}) {
			if value.Value.QName != (xml.Name{}) {
				normalized := *value.Value
				normalized.Type = kind
				var extra int64
				text, extra, localScope, err = e.valueQNameCost(normalized, printFrameworkNS, false)
				if err != nil {
					return err
				}
				attrsLen += extra
			}
		}
		xsiPrefix := "xsi"
		nodeTag := tag
		if localScope != nil {
			xsiPrefix = printSettingsPrefix(localScope, xsiNamespace)
			typeText = printSettingsPrefix(localScope, kind.Space) + ":" + kind.Local
			nodeTag = printSettingsPrefix(localScope, printFrameworkNS) + ":" + local
		}
		attrsLen += 1 + int64(len(xsiPrefix)+len(":type")) + 2 + printXMLEscapedLen(typeText, true) + 1
		return e.add(2*int64(len(nodeTag)) + 5 + attrsLen + printXMLEscapedLen(text, false))
	}
	if value.Name != (xml.Name{}) {
		nameText, err := e.qname(value.Name)
		if err != nil {
			return err
		}
		attrsLen += int64(len(` name="`)) + printXMLEscapedLen(nameText, true) + 1
	}
	if err := e.add(2*int64(len(tag)) + 5 + attrsLen); err != nil {
		return err
	}
	for _, child := range value.Children {
		if err := e.elementV1(child); err != nil {
			return err
		}
	}
	return nil
}

// elementV2 按PSF2编码格式精确核算单个直接关键字节点及其子树的序列化字节数
// 入参: value 已校验设置元素
// 返回: error 命名空间、预算或取消错误
func (e *printBudgetEstimator) elementV2(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	tag, err := e.qname(value.Name)
	if err != nil {
		return err
	}
	local := printSettingNames[value.Kind]
	psf2Prefix := e.prefixes[printFramework2NS]
	attrsLen := 1 + int64(len(psf2Prefix)+len(":psftype")) + 2 + printXMLEscapedLen(local, true) + 1
	if value.Kind == PrintSettingOption {
		if value.HasDefault || value.Default {
			flag := strconv.FormatBool(value.Default)
			attrsLen += 1 + int64(len(psf2Prefix)+len(":default")) + 2 + int64(len(flag)) + 1
		}
		if value.Constraint != PrintConstraintUnknown {
			cText, err := e.qname(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
			if err != nil {
				return err
			}
			attrsLen += 1 + int64(len(psf2Prefix)+len(":constrained")) + 2 + printXMLEscapedLen(cText, true) + 1
		}
	}
	selectionIndex, valueIndex, refIndex := -1, -1, -1
	xmlChildCount := 0
	for index, child := range value.Children {
		if e.capabilities && value.Kind == PrintSettingFeature && child.Kind == PrintSettingProperty && printFrameworkSpace(child.Name.Space) && child.Name.Local == "SelectionType" {
			selVal, err := printCommonValue(child)
			if err != nil {
				return err
			}
			selText, err := e.qname(selVal.QName)
			if err != nil {
				return err
			}
			attrsLen += 1 + int64(len(psf2Prefix)+len(":selectiontype")) + 2 + printXMLEscapedLen(selText, true) + 1
			selectionIndex = index
			continue
		}
		if child.Kind == PrintSettingValue {
			valueIndex = index
			continue
		}
		if child.Kind == PrintSettingParameterRef {
			refIndex = index
			continue
		}
		xmlChildCount++
	}
	for index, child := range value.Children {
		if index == selectionIndex || index == valueIndex || index == refIndex {
			continue
		}
		if err := e.elementV2(child); err != nil {
			return err
		}
	}
	var textLen int64
	var localScope map[string]string
	if refIndex >= 0 {
		refChild := value.Children[refIndex]
		typeText, err := e.qname(xml.Name{Space: printFrameworkNS, Local: "ParameterRef"})
		if err != nil {
			return err
		}
		if _, err := e.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		refText, err := e.qname(refChild.Name)
		if err != nil {
			return err
		}
		xsiPrefix := e.prefixes[xsiNamespace]
		attrsLen += 1 + int64(len(xsiPrefix)+len(":type")) + 2 + printXMLEscapedLen(typeText, true) + 1
		textLen = printXMLEscapedLen(refText, false)
	}
	if valueIndex >= 0 {
		valChild := value.Children[valueIndex]
		kind := valChild.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		typeText, err := e.qname(kind)
		if err != nil {
			return err
		}
		if _, err := e.qname(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		text := valChild.Value.Text
		if kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"}) && valChild.Value.QName != (xml.Name{}) {
			if valChild.Value.QName != (xml.Name{}) {
				normalized := *valChild.Value
				normalized.Type = kind
				var extra int64
				text, extra, localScope, err = e.valueQNameCost(normalized, value.Name.Space, xmlChildCount > 0)
				if err != nil {
					return err
				}
				attrsLen += extra
			}
		}
		xsiPrefix := e.prefixes[xsiNamespace]
		if localScope != nil {
			xsiPrefix = printSettingsPrefix(localScope, xsiNamespace)
			typeText = printSettingsPrefix(localScope, kind.Space) + ":" + kind.Local
		}
		attrsLen += 1 + int64(len(xsiPrefix)+len(":type")) + 2 + printXMLEscapedLen(typeText, true) + 1
		textLen = printXMLEscapedLen(text, false)
	}
	nodeTag := tag
	if localScope != nil {
		nodeTag = printSettingsPrefix(localScope, value.Name.Space) + ":" + value.Name.Local
		newPSF2 := printSettingsPrefix(localScope, printFramework2NS)
		if newPSF2 != psf2Prefix {
			diff := int64(len(newPSF2) - len(psf2Prefix))
			attrsLen += diff
			if value.Kind == PrintSettingOption {
				if value.HasDefault || value.Default {
					attrsLen += diff
				}
				if value.Constraint != PrintConstraintUnknown {
					attrsLen += diff
				}
			}
			if selectionIndex >= 0 {
				attrsLen += diff
			}
		}
	}
	return e.add(2*int64(len(nodeTag)) + 5 + attrsLen + textLen)
}

// printXMLEscapedLen 按Go标准encoding/xml转义规则计算字符串序列化后的精确字节数
// 入参: text 待转义字符串, attr 是否作为XML属性值转义
// 返回: int64 转义后的精确字节长度
func printXMLEscapedLen(text string, attr bool) int64 {
	total := int64(len(text))
	for i := range len(text) {
		switch text[i] {
		case '"', '\'', '&', '\t', '\r':
			total += 4
		case '<', '>':
			total += 3
		case '\n':
			if attr {
				total += 4
			}
		}
	}
	return total
}

// Summary 提取PrintCapabilities的通用只读能力摘要视图，涵盖可打印区、支持纸型微米表、DPI列表、参数域与标准/自定义Feature
// 返回: PrintCapabilitiesSummary 只读能力摘要视图, error 接收者为空或能力模型非法错误
func (p *PrintCapabilities) Summary() (PrintCapabilitiesSummary, error) {
	if p == nil {
		return PrintCapabilitiesSummary{}, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	configuration, err := printSettingsOptions(context.Background(), nil)
	if err != nil {
		return PrintCapabilitiesSummary{}, err
	}
	model, err := validatePrintSettingsModel(&PrintSettings{Version: p.Version, Elements: p.Elements}, configuration, printDocumentCapabilities)
	if err != nil {
		return PrintCapabilitiesSummary{}, err
	}
	summary := PrintCapabilitiesSummary{Version: model.Version}
	paramDefaults := make(map[xml.Name]int64)
	for _, el := range model.Elements {
		if el.Kind != PrintSettingParameterDef {
			continue
		}
		param := printExtractParameterSummary(el)
		summary.Parameters = append(summary.Parameters, param)
		if param.DataType == "integer" {
			if n, err := strconv.ParseInt(strings.TrimSpace(param.DefaultValue), 10, 64); err == nil {
				paramDefaults[printCanonicalKey(el.Name)] = n
			}
		}
	}
	for _, el := range model.Elements {
		if el.Kind == PrintSettingProperty && printPublicKeywordSpace(el.Name.Space) && el.Name.Local == "PageImageableSize" {
			if area, ok := printExtractPageImageableSummary(el); ok {
				summary.ImageableArea = &area
			}
			continue
		}
		if el.Kind != PrintSettingFeature {
			continue
		}
		featSummary, err := printExtractFeatureSummary(el, model.Version)
		if err != nil {
			return PrintCapabilitiesSummary{}, err
		}
		summary.Features = append(summary.Features, featSummary)
		if !printPublicKeywordSpace(el.Name.Space) {
			continue
		}
		defaultIdx := printCapabilityDefaultOptionIndex(el, model.Version)
		switch el.Name.Local {
		case "PageMediaSize":
			optIdx := 0
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption {
					continue
				}
				media := PrintMediaSummary{
					Name:        child.Name,
					Default:     optIdx == defaultIdx,
					Constrained: child.Constraint,
				}
				if printPublicKeywordSpace(child.Name.Space) {
					media.StandardName = child.Name.Local
				}
				media.WidthMicrons = printOptionInt64ScoredOrDefault(child, "MediaSizeWidth", paramDefaults)
				media.HeightMicrons = printOptionInt64ScoredOrDefault(child, "MediaSizeHeight", paramDefaults)
				if (media.WidthMicrons == 0 || media.HeightMicrons == 0) && media.StandardName != "" {
					if dims, ok := printMediaSizes[media.StandardName]; ok {
						if media.WidthMicrons == 0 {
							media.WidthMicrons = int64(dims[0])
						}
						if media.HeightMicrons == 0 {
							media.HeightMicrons = int64(dims[1])
						}
					}
				}
				for _, prop := range child.Children {
					if prop.Kind == PrintSettingProperty && len(prop.Children) == 1 && prop.Children[0].Value != nil && prop.Children[0].Value.Type == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
						if area, ok := printParseImageableArea(prop.Children[0].Value.Text); ok {
							media.ImageableArea = &PrintImageableAreaSummary{
								WidthMicrons:        media.WidthMicrons,
								HeightMicrons:       media.HeightMicrons,
								OriginWidthMicrons:  area[0],
								OriginHeightMicrons: area[1],
								ExtentWidthMicrons:  area[2],
								ExtentHeightMicrons: area[3],
							}
						}
					}
				}
				summary.MediaSizes = append(summary.MediaSizes, media)
				optIdx++
			}
		case "PageResolution":
			optIdx := 0
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption {
					continue
				}
				summary.Resolutions = append(summary.Resolutions, PrintResolutionSummary{
					Name:        child.Name,
					X:           printOptionIntScored(child, "ResolutionX"),
					Y:           printOptionIntScored(child, "ResolutionY"),
					Default:     optIdx == defaultIdx,
					Constrained: child.Constraint,
				})
				optIdx++
			}
		case "PageOrientation":
			summary.Orientations = printCollectPublicOptionKeywords(el, summary.Orientations)
		case "DocumentDuplex", "JobDuplexAllDocumentsContiguously":
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption || !printOptionUnconstrained(child) || !printPublicKeywordSpace(child.Name.Space) {
					continue
				}
				var mode PrintDuplex
				switch child.Name.Local {
				case "OneSided":
					mode = PrintSimplex
				case "TwoSidedLongEdge":
					mode = PrintDuplexLongEdge
				case "TwoSidedShortEdge":
					mode = PrintDuplexShortEdge
				default:
					continue
				}
				if !slices.Contains(summary.DuplexModes, mode) {
					summary.DuplexModes = append(summary.DuplexModes, mode)
				}
			}
		case "DocumentNUp", "JobNUpAllDocumentsContiguously":
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption || !printOptionUnconstrained(child) {
					continue
				}
				if count := printOptionIntScored(child, "PagesPerSheet"); count > 0 && !slices.Contains(summary.NUpCounts, count) {
					summary.NUpCounts = append(summary.NUpCounts, count)
				}
			}
		case "PageOutputColor":
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption || !printOptionUnconstrained(child) || !printPublicKeywordSpace(child.Name.Space) {
					continue
				}
				var mode PrintColorMode
				switch child.Name.Local {
				case "Color":
					mode = PrintColorPreserve
				case "Grayscale":
					mode = PrintColorGrayscale
				case "Monochrome":
					mode = PrintColorMonochrome
				default:
					continue
				}
				if !slices.Contains(summary.ColorModes, mode) {
					summary.ColorModes = append(summary.ColorModes, mode)
				}
			}
		case "PageColorManagement":
			summary.ColorManagements = printCollectPublicOptionKeywords(el, summary.ColorManagements)
		case "PageICMRenderingIntent":
			summary.RenderingIntents = printCollectPublicOptionKeywords(el, summary.RenderingIntents)
		case "PageOutputQuality":
			summary.OutputQualities = printCollectPublicOptionKeywords(el, summary.OutputQualities)
		case "DocumentBinding", "JobBindAllDocuments":
			for _, child := range el.Children {
				if child.Kind != PrintSettingOption || !printOptionUnconstrained(child) || !printPublicKeywordSpace(child.Name.Space) {
					continue
				}
				if binding, ok := printBindingNames[child.Name.Local]; ok && !slices.Contains(summary.Bindings, binding) {
					summary.Bindings = append(summary.Bindings, binding)
				}
			}
		case "DocumentStaple", "JobStapleAllDocuments":
			summary.Staples = printCollectPublicOptionKeywords(el, summary.Staples)
		case "DocumentHolePunch", "JobHolePunch":
			summary.HolePunches = printCollectPublicOptionKeywords(el, summary.HolePunches)
		case "DocumentFold", "JobFoldAllDocuments":
			summary.Folds = printCollectPublicOptionKeywords(el, summary.Folds)
		case "PageBorderless":
			for _, child := range el.Children {
				if child.Kind == PrintSettingOption && printOptionUnconstrained(child) && printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "Borderless" {
					summary.Borderless = true
				}
			}
		case "PageWatermark":
			for _, child := range el.Children {
				if child.Kind == PrintSettingOption && printOptionUnconstrained(child) && (!printPublicKeywordSpace(child.Name.Space) || child.Name.Local != "None") {
					summary.Watermark = true
				}
			}
		}
	}
	return summary, nil
}

// printOptionUnconstrained 判断能力Option是否未受约束
// 入参: option 能力Option节点
// 返回: bool 是否未受约束
func printOptionUnconstrained(option PrintSetting) bool {
	return option.Constraint == PrintConstraintUnknown || option.Constraint == PrintConstraintNone
}

// printCapabilityDefaultOptionIndex 计算能力Feature中默认Option的下标，v2优先psf2:default，v1取首个未受约束项
// 入参: feature 能力Feature节点, version 文档框架版本号
// 返回: int 默认Option在全部Option中的序号，无可用项为负一
func printCapabilityDefaultOptionIndex(feature PrintSetting, version uint32) int {
	firstUnconstrained := -1
	optIdx := 0
	for _, child := range feature.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		if printOptionUnconstrained(child) {
			if version == 2 && child.Default {
				return optIdx
			}
			if firstUnconstrained < 0 {
				firstUnconstrained = optIdx
			}
		}
		optIdx++
	}
	return firstUnconstrained
}

// printCollectPublicOptionKeywords 收集Feature下所有未受约束的公共关键字Option本地名称并去重追加
// 入参: feature 能力Feature节点, dst 目标切片
// 返回: []string 追加去重后的关键字列表
func printCollectPublicOptionKeywords(feature PrintSetting, dst []string) []string {
	for _, child := range feature.Children {
		if child.Kind != PrintSettingOption || !printOptionUnconstrained(child) || !printPublicKeywordSpace(child.Name.Space) {
			continue
		}
		if !slices.Contains(dst, child.Name.Local) {
			dst = append(dst, child.Name.Local)
		}
	}
	return dst
}

// printExtractParameterSummary 从已校验ParameterDef提取只读参数域摘要
// 入参: param 参数定义节点
// 返回: PrintParameterSummary 参数域摘要
func printExtractParameterSummary(param PrintSetting) PrintParameterSummary {
	out := PrintParameterSummary{Name: param.Name}
	for _, prop := range param.Children {
		if prop.Kind != PrintSettingProperty || !printFrameworkSpace(prop.Name.Space) || len(prop.Children) != 1 || prop.Children[0].Value == nil {
			continue
		}
		val := prop.Children[0].Value
		switch prop.Name.Local {
		case "DataType":
			out.DataType = val.QName.Local
		case "UnitType":
			out.UnitType = val.Text
		case "Mandatory":
			out.Mandatory = val.QName.Local
		case "MinValue", "MinLength":
			out.MinValue = strings.TrimSpace(val.Text)
		case "MaxValue", "MaxLength":
			out.MaxValue = strings.TrimSpace(val.Text)
		case "Multiple":
			out.Multiple = strings.TrimSpace(val.Text)
		case "DefaultValue":
			out.DefaultValue = val.Text
		}
	}
	return out
}

// printExtractPageImageableSummary 从根级PageImageableSize属性树提取完整微米可打印区域摘要
// 入参: prop PageImageableSize属性节点
// 返回: PrintImageableAreaSummary 微米区域摘要, bool 是否提取成功
func printExtractPageImageableSummary(prop PrintSetting) (PrintImageableAreaSummary, bool) {
	var out PrintImageableAreaSummary
	got := 0
	parsePropInt := func(node PrintSetting) (int64, bool) {
		if len(node.Children) != 1 || node.Children[0].Value == nil {
			return 0, false
		}
		n, err := strconv.ParseInt(strings.TrimSpace(node.Children[0].Value.Text), 10, 64)
		return n, err == nil
	}
	for _, child := range prop.Children {
		if child.Kind != PrintSettingProperty || !printPublicKeywordSpace(child.Name.Space) {
			continue
		}
		switch child.Name.Local {
		case "ImageableSizeWidth":
			if v, ok := parsePropInt(child); ok {
				out.WidthMicrons = v
				got |= 1
			}
		case "ImageableSizeHeight":
			if v, ok := parsePropInt(child); ok {
				out.HeightMicrons = v
				got |= 2
			}
		case "ImageableArea":
			for _, sub := range child.Children {
				if sub.Kind != PrintSettingProperty || !printPublicKeywordSpace(sub.Name.Space) {
					continue
				}
				switch sub.Name.Local {
				case "OriginWidth":
					if v, ok := parsePropInt(sub); ok {
						out.OriginWidthMicrons = v
						got |= 4
					}
				case "OriginHeight":
					if v, ok := parsePropInt(sub); ok {
						out.OriginHeightMicrons = v
						got |= 8
					}
				case "ExtentWidth":
					if v, ok := parsePropInt(sub); ok {
						out.ExtentWidthMicrons = v
						got |= 16
					}
				case "ExtentHeight":
					if v, ok := parsePropInt(sub); ok {
						out.ExtentHeightMicrons = v
						got |= 32
					}
				}
			}
		}
	}
	return out, got == 63
}

// printExtractFeatureSummary 从单个能力Feature节点提取选择方式、可用选项与默认选项摘要
// 入参: feature 能力Feature节点, version 文档框架版本号
// 返回: PrintFeatureSummary Feature摘要, error 选择属性非法错误
func printExtractFeatureSummary(feature PrintSetting, version uint32) (PrintFeatureSummary, error) {
	selection, err := feature.Selection()
	if err != nil {
		return PrintFeatureSummary{}, err
	}
	out := PrintFeatureSummary{Name: feature.Name, Selection: selection}
	defaultIdx := printCapabilityDefaultOptionIndex(feature, version)
	optIdx := 0
	for _, child := range feature.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		if printOptionUnconstrained(child) {
			out.Options = append(out.Options, child.Name)
			if version == 2 && selection == PrintSelectionMany && child.Default {
				out.DefaultOptions = append(out.DefaultOptions, child.Name)
			} else if optIdx == defaultIdx {
				out.DefaultOptions = append(out.DefaultOptions, child.Name)
			}
		}
		optIdx++
	}
	return out, nil
}

// printOptionInt64ScoredOrDefault 读取Option指定公共ScoredProperty的64位整数值，遇ParameterRef时回退参数默认值
// 入参: option 能力Option节点, local 公共关键字本地名称, paramDefaults 整数参数默认值映射
// 返回: int64 整数值，不可得时为0
func printOptionInt64ScoredOrDefault(option PrintSetting, local string, paramDefaults map[xml.Name]int64) int64 {
	for _, child := range option.Children {
		if child.Kind != PrintSettingScoredProperty || !printPublicKeywordSpace(child.Name.Space) || child.Name.Local != local {
			continue
		}
		val, ref := printScoredValue(child.Children)
		if ref != (xml.Name{}) {
			return paramDefaults[printCanonicalKey(ref)]
		}
		if val == nil {
			return 0
		}
		parsed, err := strconv.ParseInt(strings.Trim(val.Text, " \t\r\n"), 10, 64)
		if err != nil {
			return 0
		}
		return parsed
	}
	return 0
}
