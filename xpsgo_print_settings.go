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

// printAllowedOrientations 等切片与映射集中声明Print Schema公共关键字权威白名单与多作用域互斥表
var (
	printAllowedOrientations           = []string{"Portrait", "Landscape", "ReversePortrait", "ReverseLandscape"}
	printAllowedScalings               = []string{"None", "Custom", "CustomSquare", "FitApplicationMediaSizeToPageImageableSize", "FitApplicationContentSizeToPageImageableSize", "FitApplicationBleedSizeToPageImageableSize", "FitApplicationMediaSizeToPageMediaSize"}
	printAllowedScaleOffsetAlignments  = []string{"Center", "TopLeft", "TopCenter", "TopRight", "LeftCenter", "RightCenter", "BottomLeft", "BottomCenter", "BottomRight"}
	printAllowedMirrorImages           = []string{"None", "MirrorImageWidth", "MirrorImageHeight"}
	printAllowedPageOrders             = []string{"Standard", "Reverse"}
	printAllowedCollateModes           = []string{"Collated", "Uncollated"}
	printAllowedPresentationDirections = []string{"RightBottom", "BottomRight", "LeftBottom", "BottomLeft", "RightTop", "TopRight", "LeftTop", "TopLeft"}
	printAllowedDuplexOptions          = []string{"OneSided", "TwoSidedLongEdge", "TwoSidedShortEdge"}
	printAllowedBorderlessOptions      = []string{"None", "Borderless"}
	printAllowedOutputColors           = []string{"Color", "Grayscale", "Monochrome"}
	printAllowedColorManagements       = []string{"None", "Device", "Driver", "System"}
	printAllowedRenderingIntents       = []string{"AbsoluteColorimetric", "BusinessGraphics", "Photographs", "RelativeColorimetric"}
	printAllowedOutputQualities        = []string{"Automatic", "Draft", "Fax", "High", "Normal", "Photographic", "Text"}
	printAllowedPhotoPrintingIntents   = []string{"None", "PhotoBest", "PhotoDraft", "PhotoStandard"}
	printAllowedBindingOptions         = []string{"None", "Bale", "BindBottom", "BindLeft", "BindRight", "BindTop", "Booklet", "EdgeStitchBottom", "EdgeStitchLeft", "EdgeStitchRight", "EdgeStitchTop", "Fold", "JogOffset", "Trim"}
	printAllowedStapleOptions          = []string{"None", "SaddleStitch", "StapleBottomLeft", "StapleBottomRight", "StapleDualBottom", "StapleDualLeft", "StapleDualRight", "StapleDualTop", "StapleTopLeft", "StapleTopRight"}
	printAllowedHolePunchOptions       = []string{"None", "BottomEdge", "LeftEdge", "RightEdge", "TopEdge"}
	printAllowedWatermarkLayers        = []string{"Overlay", "Underlay"}
	printMutexFeatureGroups            = [][]string{
		{"JobBindAllDocuments", "DocumentBinding"},
		{"JobDuplexAllDocumentsContiguously", "DocumentDuplex"},
		{"JobNUpAllDocumentsContiguously", "DocumentNUp"},
		{"JobCollateAllDocuments", "DocumentCollate"},
		{"JobStapleAllDocuments", "DocumentStaple"},
		{"JobHolePunch", "DocumentHolePunch"},
		{"JobInputBin", "DocumentInputBin", "PageInputBin"},
		{"JobOutputBin", "DocumentOutputBin", "PageOutputBin"},
	}
	printMutexParameterGroups = [][]string{
		{"JobCopiesAllDocuments", "DocumentCopiesAllPages", "PageCopies"},
	}
	printDeviceControlFeatures = map[string]bool{
		"PageMediaType":              true,
		"PageOutputQuality":          true,
		"PagePhotoPrintingIntent":    true,
		"PageResolution":             true,
		"JobInputBin":                true,
		"DocumentInputBin":           true,
		"PageInputBin":               true,
		"JobOutputBin":               true,
		"DocumentOutputBin":          true,
		"PageOutputBin":              true,
		"JobStapleAllDocuments":      true,
		"DocumentStaple":             true,
		"JobHolePunch":               true,
		"DocumentHolePunch":          true,
		"PageTrueTypeFontMode":       true,
		"PageDeviceFontSubstitution": true,
	}
)

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

// PrintSettingsOptions 设置资源预算、票据关联层级与向前兼容校验选项，参数算术默认最多处理4096位数字
// Option匹配默认最多执行100000次比较，预算不足返回ErrLimit，不改为近似匹配
// 非Unknown层级会在Framework校验前移除更宽作用域的根设置，不推断私有设备约束
// IgnoreUndeclaredFeatures开启时，ValidatePrintSelection对已知命名空间中能力文档未声明的扩展Feature记录非致命诊断并忽略，仍严格拦截不支持的Option值
type PrintSettingsOptions struct {
	Limits                   Limits
	Scope                    PrintScope
	MaxNumericDigits         int
	MaxOptionComparisons     int
	IgnoreUndeclaredFeatures bool
}

// printSettingsConfig 保存已校验的打印设置预算、关联层级、忽略策略与取消Context
type printSettingsConfig struct {
	PrintSettingsOptions
	context           context.Context
	ignoreUnsupported bool
}

// printSettingsEncoder 在纯内存中执行两遍命名空间收集与流式XML编码或精确字节计费
type printSettingsEncoder struct {
	options      printSettingsConfig
	framework    string
	limit        int64
	prefixes     map[string]string
	scope        map[string]string
	out          io.Writer
	strOut       io.StringWriter
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

// printCanonicalKey 将v1与v2框架命名空间归并到规范框架命名空间用于合并与查重，公共关键字各版本及私有命名空间均保留真实命名空间
// 入参: name 展开关键字名称
// 返回: xml.Name 规范化后的展开名称
func printCanonicalKey(name xml.Name) xml.Name {
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

// Feature 按完整xml.Name只读检索根级Feature并返回独立深拷贝
// 入参: name 目标Feature的展开名称
// 返回: PrintSetting 独立Feature副本, bool 是否找到
func (p *PrintSettings) Feature(name xml.Name) (PrintSetting, bool) {
	if p == nil {
		return PrintSetting{}, false
	}
	return printFindChildSetting(p.Elements, PrintSettingFeature, name)
}

// Option 按Feature的完整xml.Name只读检索其首个直接Option并返回独立深拷贝
// 入参: feature 目标Feature的展开名称
// 返回: PrintSetting 独立Option副本, bool 是否找到
func (p *PrintSettings) Option(feature xml.Name) (PrintSetting, bool) {
	found, ok := p.Feature(feature)
	if !ok {
		return PrintSetting{}, false
	}
	return found.Option()
}

// Options 按Feature的完整xml.Name只读检索其全部直接Option并返回独立深拷贝切片
// 入参: feature 目标Feature的展开名称
// 返回: []PrintSetting 独立Option列表，未找到时为nil
func (p *PrintSettings) Options(feature xml.Name) []PrintSetting {
	found, ok := p.Feature(feature)
	if !ok {
		return nil
	}
	return found.Options()
}

// ScoredProperty 按Feature与ScoredProperty的完整xml.Name只读检索首个Option下的ScoredProperty并返回独立深拷贝
// 入参: feature 目标Feature的展开名称, property 目标ScoredProperty的展开名称
// 返回: PrintSetting 独立ScoredProperty副本, bool 是否找到
func (p *PrintSettings) ScoredProperty(feature, property xml.Name) (PrintSetting, bool) {
	option, ok := p.Option(feature)
	if !ok {
		return PrintSetting{}, false
	}
	return option.ScoredProperty(property)
}

// Property 按完整xml.Name只读检索根级Property并返回独立深拷贝
// 入参: name 目标Property的展开名称
// 返回: PrintSetting 独立Property副本, bool 是否找到
func (p *PrintSettings) Property(name xml.Name) (PrintSetting, bool) {
	if p == nil {
		return PrintSetting{}, false
	}
	return printFindChildSetting(p.Elements, PrintSettingProperty, name)
}

// ParameterInit 按完整xml.Name只读检索根级ParameterInit并返回独立深拷贝
// 入参: name 目标ParameterInit的展开名称
// 返回: PrintSetting 独立ParameterInit副本, bool 是否找到
func (p *PrintSettings) ParameterInit(name xml.Name) (PrintSetting, bool) {
	if p == nil {
		return PrintSetting{}, false
	}
	return printFindChildSetting(p.Elements, PrintSettingParameterInit, name)
}

// ParameterDef 按完整xml.Name只读检索根级ParameterDef并返回独立深拷贝
// 入参: name 目标ParameterDef的展开名称
// 返回: PrintSetting 独立ParameterDef副本, bool 是否找到
func (p *PrintSettings) ParameterDef(name xml.Name) (PrintSetting, bool) {
	if p == nil {
		return PrintSetting{}, false
	}
	return printFindChildSetting(p.Elements, PrintSettingParameterDef, name)
}

// Feature 按完整xml.Name只读检索当前节点的直接子Feature并返回独立深拷贝
// 入参: name 目标子Feature的展开名称
// 返回: PrintSetting 独立子Feature副本, bool 是否找到
func (p PrintSetting) Feature(name xml.Name) (PrintSetting, bool) {
	return printFindChildSetting(p.Children, PrintSettingFeature, name)
}

// Option 只读检索当前节点的首个直接子Option并返回独立深拷贝
// 返回: PrintSetting 独立Option副本, bool 是否找到
func (p PrintSetting) Option() (PrintSetting, bool) {
	for _, child := range p.Children {
		if child.Kind == PrintSettingOption {
			return printCloneSetting(child), true
		}
	}
	return PrintSetting{}, false
}

// Options 只读检索当前节点的全部直接子Option并返回独立深拷贝切片
// 返回: []PrintSetting 独立Option列表，无直接Option时为nil
func (p PrintSetting) Options() []PrintSetting {
	var result []PrintSetting
	for _, child := range p.Children {
		if child.Kind == PrintSettingOption {
			result = append(result, printCloneSetting(child))
		}
	}
	return result
}

// ScoredProperty 按完整xml.Name只读检索当前节点的直接子ScoredProperty并返回独立深拷贝
// 入参: name 目标ScoredProperty的展开名称
// 返回: PrintSetting 独立ScoredProperty副本, bool 是否找到
func (p PrintSetting) ScoredProperty(name xml.Name) (PrintSetting, bool) {
	return printFindChildSetting(p.Children, PrintSettingScoredProperty, name)
}

// Property 按完整xml.Name只读检索当前节点的直接子Property并返回独立深拷贝
// 入参: name 目标Property的展开名称
// 返回: PrintSetting 独立Property副本, bool 是否找到
func (p PrintSetting) Property(name xml.Name) (PrintSetting, bool) {
	return printFindChildSetting(p.Children, PrintSettingProperty, name)
}

// ScalarValue 只读提取当前节点的直接标量Value并返回独立深拷贝
// 返回: *PrintValue 独立值副本, bool 是否存在标量值
func (p PrintSetting) ScalarValue() (*PrintValue, bool) {
	if p.Kind == PrintSettingValue && p.Value != nil {
		val := *p.Value
		return &val, true
	}
	for _, child := range p.Children {
		if child.Kind == PrintSettingValue && child.Value != nil {
			val := *child.Value
			return &val, true
		}
	}
	return nil, false
}

// printFindChildSetting 在同级元素列表中按类型与规范化xml.Name查找首个匹配节点并返回独立深拷贝
// 入参: elements 同级元素列表, kind 目标元素类型, name 目标展开名称
// 返回: PrintSetting 独立深拷贝节点, bool 是否找到
func printFindChildSetting(elements []PrintSetting, kind PrintSettingKind, name xml.Name) (PrintSetting, bool) {
	target := printCanonicalKey(name)
	for _, element := range elements {
		if element.Kind == kind && printCanonicalKey(element.Name) == target {
			return printCloneSetting(element), true
		}
	}
	return PrintSetting{}, false
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
	if !capabilities {
		if err := printSettingsPrefixConflicts(value.Elements); err != nil {
			return nil, err
		}
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
	err := printSettingsWalkAttributes(node, false, func(attribute xml.Attr) (bool, error) {
		if attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			typeName, err := printSettingsQName(node, attribute.Value)
			if err != nil || typeName != (xml.Name{Space: printValueNS, Local: "string"}) {
				return true, fmt.Errorf("%w: print device capabilities CapabilitiesChangeID type", ErrInvalid)
			}
			return true, nil
		}
		return false, nil
	})
	if err != nil {
		return "", err
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

// printSettingsWalkAttributes 统一遍历元素属性，跳过命名空间声明并校验XML全局属性，将剩余属性交给专用回调处理
// 入参: node XML元素, isRoot 是否位于文档根元素, handle 专用属性处理回调
// 返回: error 非法属性或取值错误
func printSettingsWalkAttributes(node *xmlElement, isRoot bool, handle func(xml.Attr) (bool, error)) error {
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
		handled, err := handle(attribute)
		if err != nil {
			return err
		}
		if !handled {
			return fmt.Errorf("%w: print settings attribute {%s}%s", ErrInvalid, attribute.Name.Space, attribute.Name.Local)
		}
	}
	return nil
}

// printSettingsPSF2Attributes 校验Print Schema v2直接元素的框架属性并提取约束、默认标记与选择类型
// 入参: node XML元素, kind 已识别元素类型, capabilities 是否为能力文档, allowType 是否允许xsi:type, constraint 约束输出, hasDefault 默认声明标志输出, isDefault 默认选项值输出, selection 选择属性输出
// 返回: error 属性或取值错误
func printSettingsPSF2Attributes(node *xmlElement, kind PrintSettingKind, capabilities, allowType bool, constraint *PrintConstraint, hasDefault, isDefault *bool, selection **PrintSetting) error {
	return printSettingsWalkAttributes(node, false, func(attribute xml.Attr) (bool, error) {
		if attribute.Name == (xml.Name{Space: printFramework2NS, Local: "psftype"}) {
			return true, nil
		}
		if allowType && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			return true, nil
		}
		if capabilities && kind == PrintSettingOption && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "default"}) {
			value := strings.Trim(attribute.Value, " \t\r\n")
			if value != "true" && value != "false" {
				return true, fmt.Errorf("%w: print settings psf2:default value", ErrInvalid)
			}
			*hasDefault = true
			*isDefault = value == "true"
			return true, nil
		}
		if capabilities && kind == PrintSettingOption && (attribute.Name == (xml.Name{Local: "constrained"}) || attribute.Name == (xml.Name{Space: printFramework2NS, Local: "constrained"})) {
			parsed, err := printConstraint(node, attribute.Value)
			if err != nil {
				return true, err
			}
			*constraint = parsed
			return true, nil
		}
		if capabilities && kind == PrintSettingFeature && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "selectiontype"}) {
			qname, err := printSettingsQName(node, attribute.Value)
			if err != nil || !printPublicKeywordSpace(qname.Space) || (qname.Local != "PickOne" && qname.Local != "PickMany") {
				return true, fmt.Errorf("%w: print settings psf2:selectiontype value", ErrInvalid)
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
			return true, nil
		}
		return false, nil
	})
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
	return printSettingsWalkAttributes(node, isRoot, func(attribute xml.Attr) (bool, error) {
		for _, name := range allowed {
			if name != "" && attribute.Name == (xml.Name{Local: name}) {
				return true, nil
			}
		}
		if !isRoot && node.Name.Local == "Value" && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}) {
			return true, nil
		}
		return false, nil
	})
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
	result, err := mergePrintSettingsInternal(base, change, configuration)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsOutputBudget(result, configuration, printDocumentTicket); err != nil {
		return nil, err
	}
	return result, nil
}

// mergePrintSettingsInternal 在纯内存中合并两份已校验打印票据模型并执行轻量复杂度与冲突校验，不修改入参亦不触发整树重校验或模拟编码
// 入参: base 已校验基础票据，nil视为版本1空票据, change 已校验增量票据，nil直接返回base, configuration 已校验配置
// 返回: *PrintSettings 合并后的打印设置模型, error 嵌套、预算、前缀冲突或取消错误
func mergePrintSettingsInternal(base, change *PrintSettings, configuration printSettingsConfig) (*PrintSettings, error) {
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	if base == nil {
		base = &PrintSettings{Version: 1}
	}
	if change == nil || len(change.Elements) == 0 && change.Version <= base.Version {
		return base, nil
	}
	merged, err := mergePrintSettingsValidated(base, change, configuration)
	if err != nil {
		return nil, err
	}
	if err := validatePrintSettingsMergedFast(merged, configuration); err != nil {
		return nil, err
	}
	return merged, nil
}

// validatePrintSettingsMergedFast 对由已校验票据合并生成的模型执行零拷贝节点数、深度、Feature嵌套、下界字节与作用域前缀冲突复验
// 入参: settings 合并后的票据模型, configuration 已校验配置
// 返回: error 结构深度、冲突、预算或取消错误
func validatePrintSettingsMergedFast(settings *PrintSettings, configuration printSettingsConfig) error {
	limit := min(configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPartBytes, configuration.Limits.MaxPackageBytes)
	nodes := 1
	bytesCount := int64(32)
	if bytesCount > limit || nodes > configuration.Limits.MaxXMLNodes || configuration.Limits.MaxXMLDepth < 1 {
		return fmt.Errorf("%w: print settings budget", ErrLimit)
	}
	var walk func(items []PrintSetting, depth int, featureDepth int) error
	walk = func(items []PrintSetting, depth int, featureDepth int) error {
		if depth > configuration.Limits.MaxXMLDepth {
			return fmt.Errorf("%w: print settings depth", ErrLimit)
		}
		for _, item := range items {
			if err := checkContext(configuration.context); err != nil {
				return err
			}
			nodes++
			if nodes > configuration.Limits.MaxXMLNodes {
				return fmt.Errorf("%w: print settings nodes", ErrLimit)
			}
			bytesCount += int64(len(item.Name.Local)) + 16
			if item.Value != nil {
				bytesCount += int64(len(item.Value.Text)) + int64(len(item.Value.QName.Local)) + 8
			}
			if bytesCount > limit {
				return fmt.Errorf("%w: print settings byte budget", ErrLimit)
			}
			nextFeat := featureDepth
			if item.Kind == PrintSettingFeature {
				nextFeat++
				if nextFeat > 10 {
					return fmt.Errorf("%w: print settings element nesting", ErrInvalid)
				}
			}
			if len(item.Children) > 0 {
				if err := walk(item.Children, depth+1, nextFeat); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if err := walk(settings.Elements, 2, 0); err != nil {
		return err
	}
	return printSettingsPrefixConflicts(settings.Elements)
}

// mergePrintSettingsValidated 在纯内存中无副作用合并两份已校验且已按作用域过滤的打印票据模型
// 入参: base 已校验基础票据, change 已校验增量票据, configuration 已校验配置
// 返回: *PrintSettings 新建的合并打印设置模型, error 取消错误
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
	version := base.Version
	if version == 0 {
		version = 1
	}
	if change.Version > version {
		version = change.Version
	}
	result := &PrintSettings{Version: version, Elements: merged}
	if result.Version > 1 && printSettingsHasAnonymousOption(result.Elements) {
		result.Version = 1
		cloned := make([]PrintSetting, len(result.Elements))
		for index, element := range result.Elements {
			cloned[index] = printCloneSetting(element)
		}
		printStripOptionDefaults(cloned)
		result.Elements = cloned
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
	return writeEncodedPrintSettings(output, validated, configuration, printDocumentTicket)
}

// writeEncodedPrintSettings 先在内存缓冲完成完整编码与预算检查，再原子写入调用方输出流
// 入参: output 调用方输出流, validated 已校验设置模型, options 已校验预算参数, mode 文档类别模式
// 返回: int64 实际写入字节数, error 预算、命名空间、取消或输出错误
func writeEncodedPrintSettings(output io.Writer, validated *PrintSettings, options printSettingsConfig, mode printDocumentMode) (int64, error) {
	var buffer bytes.Buffer
	if _, err := encodePrintSettingsDocument(&buffer, validated, options, mode); err != nil {
		return 0, err
	}
	counted := packageOutput{writer: output, context: options.context, limit: min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes)}
	_, err := counted.Write(buffer.Bytes())
	return counted.count, err
}

// encodePrintSettingsDocument 按两遍纯内存流式策略收集冻结根前缀表并直接写出或精确计费XML
// 入参: output 目标输出流，nil表示仅纯内存精确计费并校验输出预算与命名空间, settings 已校验打印设置模型, options 已校验预算参数, mode 文档类别模式
// 返回: int64 精确写出或计费字节数, error 版本、命名空间、预算、取消或写入错误
func encodePrintSettingsDocument(output io.Writer, settings *PrintSettings, options printSettingsConfig, mode printDocumentMode) (int64, error) {
	if err := checkContext(options.context); err != nil {
		return 0, err
	}
	if settings == nil {
		return 0, fmt.Errorf("%w: nil print settings", ErrInvalid)
	}
	capabilities := mode != printDocumentTicket
	version := settings.Version
	if mode == printDocumentDeviceCapabilities {
		if version == 0 {
			version = 2
		}
		if version != 2 {
			return 0, fmt.Errorf("%w: print device capabilities requires framework version 2", ErrUnsupported)
		}
	} else {
		if version == 0 {
			version = 1
		}
		if version != 1 && version != 2 {
			return 0, fmt.Errorf("%w: print settings framework version", ErrUnsupported)
		}
	}
	framework, rootPrefix := printFrameworkNS, "psf"
	if version == 2 {
		framework, rootPrefix = printFramework2NS, "psf2"
	}
	rootName := "PrintTicket"
	if mode == printDocumentCapabilities {
		rootName = "PrintCapabilities"
	} else if mode == printDocumentDeviceCapabilities {
		rootName = "PrintDeviceCapabilities"
	}
	enc := printSettingsEncoder{
		options:      options,
		framework:    framework,
		limit:        min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes),
		prefixes:     map[string]string{framework: rootPrefix},
		scope:        map[string]string{rootPrefix: framework},
		out:          output,
		capabilities: capabilities,
	}
	if sw, ok := output.(io.StringWriter); ok {
		enc.strOut = sw
	}
	if mode == printDocumentDeviceCapabilities && settings.CapabilitiesChangeID != "" {
		if err := enc.bindRoot(xml.Name{Space: printValueNS, Local: "string"}); err != nil {
			return 0, err
		}
		if err := enc.bindRoot(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return 0, err
		}
	}
	for _, setting := range settings.Elements {
		if err := checkContext(options.context); err != nil {
			return 0, err
		}
		scope := printKeywordScope(setting.Name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		var err error
		if version == 2 && !(mode == printDocumentDeviceCapabilities && setting.Kind == PrintSettingParameterDef) {
			err = enc.collectV2(setting)
		} else {
			err = enc.collectV1(setting)
		}
		if err != nil {
			return 0, err
		}
	}
	sortedPrefixes := make([]string, 0, len(enc.scope))
	for prefix := range enc.scope {
		sortedPrefixes = append(sortedPrefixes, prefix)
	}
	slices.Sort(sortedPrefixes)
	for _, prefix := range sortedPrefixes {
		if err := xmlNamespaceOutput(prefix, enc.scope[prefix]); err != nil {
			return 0, err
		}
	}
	rootTag := enc.resolveQName(enc.scope, xml.Name{Space: framework, Local: rootName})
	if err := enc.writeRaw("<" + rootTag); err != nil {
		return enc.bytes, err
	}
	for _, prefix := range sortedPrefixes {
		attrName := "xmlns"
		if prefix != "" {
			attrName += ":" + prefix
		}
		if err := enc.writeAttr(attrName, enc.scope[prefix]); err != nil {
			return enc.bytes, err
		}
	}
	if err := enc.writeAttr("version", strconv.FormatUint(uint64(version), 10)); err != nil {
		return enc.bytes, err
	}
	if err := enc.writeRaw(">"); err != nil {
		return enc.bytes, err
	}
	if mode == printDocumentDeviceCapabilities && settings.CapabilitiesChangeID != "" {
		tag := enc.resolveQName(enc.scope, xml.Name{Space: printFramework2NS, Local: "CapabilitiesChangeID"})
		typeAttr := enc.resolveQName(enc.scope, xml.Name{Space: xsiNamespace, Local: "type"})
		typeVal := enc.resolveQName(enc.scope, xml.Name{Space: printValueNS, Local: "string"})
		if err := enc.writeRaw("<" + tag); err != nil {
			return enc.bytes, err
		}
		if err := enc.writeAttr(typeAttr, typeVal); err != nil {
			return enc.bytes, err
		}
		if err := enc.writeRaw(">"); err != nil {
			return enc.bytes, err
		}
		if err := enc.writeEscaped(settings.CapabilitiesChangeID, false); err != nil {
			return enc.bytes, err
		}
		if err := enc.writeRaw("</" + tag + ">"); err != nil {
			return enc.bytes, err
		}
	}
	for _, setting := range settings.Elements {
		if err := checkContext(options.context); err != nil {
			return enc.bytes, err
		}
		scope := printKeywordScope(setting.Name)
		if !capabilities && options.Scope != PrintScopeUnknown && scope != PrintScopeUnknown && scope < options.Scope {
			continue
		}
		var err error
		if version == 2 && !(mode == printDocumentDeviceCapabilities && setting.Kind == PrintSettingParameterDef) {
			err = enc.writeV2(setting)
		} else {
			err = enc.writeV1(setting)
		}
		if err != nil {
			return enc.bytes, err
		}
	}
	if err := enc.writeRaw("</" + rootTag + ">"); err != nil {
		return enc.bytes, err
	}
	return enc.bytes, nil
}

// writeRaw 累计字节并按需向输出流写入未转义原始片段
// 入参: text 待写入原始字符串
// 返回: error 字节预算超限或输出错误
func (e *printSettingsEncoder) writeRaw(text string) error {
	size := int64(len(text))
	if size > e.limit-e.bytes {
		return fmt.Errorf("%w: print settings byte budget", ErrLimit)
	}
	e.bytes += size
	if e.out == nil {
		return nil
	}
	if e.strOut != nil {
		_, err := e.strOut.WriteString(text)
		return err
	}
	_, err := io.WriteString(e.out, text)
	return err
}

// writeEscaped 按XML属性或字符数据规则转义并写出字符串，文本模式保持制表符与换行符单字节不膨胀
// 入参: text 待转义文本, attr 是否作为XML属性值转义
// 返回: error 字节预算超限或输出错误
func (e *printSettingsEncoder) writeEscaped(text string, attr bool) error {
	start := 0
	for i := range len(text) {
		var esc string
		switch text[i] {
		case '"':
			esc = "&#34;"
		case '\'':
			esc = "&#39;"
		case '&':
			esc = "&amp;"
		case '<':
			esc = "&lt;"
		case '>':
			esc = "&gt;"
		case '\t':
			if attr {
				esc = "&#x9;"
			}
		case '\n':
			if attr {
				esc = "&#xA;"
			}
		case '\r':
			esc = "&#xD;"
		}
		if esc == "" {
			continue
		}
		if i > start {
			if err := e.writeRaw(text[start:i]); err != nil {
				return err
			}
		}
		if err := e.writeRaw(esc); err != nil {
			return err
		}
		start = i + 1
	}
	if start < len(text) {
		return e.writeRaw(text[start:])
	}
	return nil
}

// writeAttr 写出单个带前导空格与双引号转义值的XML属性
// 入参: name 属性词法名称, value 属性值文本
// 返回: error 字节预算超限或输出错误
func (e *printSettingsEncoder) writeAttr(name, value string) error {
	if err := e.writeRaw(" " + name + `="`); err != nil {
		return err
	}
	if err := e.writeEscaped(value, true); err != nil {
		return err
	}
	return e.writeRaw(`"`)
}

// bindRoot 为展开名称分配确定性根命名空间前缀并写入根作用域映射
// 入参: name 展开名称
// 返回: error 名称或命名空间错误
func (e *printSettingsEncoder) bindRoot(name xml.Name) error {
	if name.Space == "" {
		return nil
	}
	if _, exists := e.prefixes[name.Space]; exists {
		return nil
	}
	if name.Space == xmlnsNamespace {
		return fmt.Errorf("%w: reserved print settings namespace", ErrInvalid)
	}
	prefix := printKnownNamespacePrefix(name.Space)
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
	return nil
}

// resolveQName 在给定冻结作用域中将展开名称解析为确定性词法QName
// 入参: scope 生效命名空间作用域, name 展开名称
// 返回: string 词法QName字符串
func (e *printSettingsEncoder) resolveQName(scope map[string]string, name xml.Name) string {
	if name.Space == "" {
		return name.Local
	}
	return printSettingsPrefix(scope, name.Space) + ":" + name.Local
}

// collectValueQName 在Pass1收集含QName标量值所需的前缀，保留无冲突词法前缀以便保持值长度不变
// 入参: value 含非空QName的标量值, hasChildren 所在元素是否含XML子节点
// 返回: error 命名空间错误
func (e *printSettingsEncoder) collectValueQName(value PrintValue, hasChildren bool) error {
	text := strings.Trim(value.Text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified && text == value.QName.Local && xmlNCName(text) {
		if value.QName.Space != "" && hasChildren {
			return e.bindRoot(value.QName)
		}
		return nil
	}
	if qualified && xmlNCName(prefix) && xmlNCName(local) && prefix != "xmlns" && local == value.QName.Local && value.QName.Space != "" && (prefix != "xml" || value.QName.Space == xmlNamespace) {
		if bound := e.scope[prefix]; bound == "" || bound == value.QName.Space {
			if !xmlTextValid(value.QName.Space) || value.QName.Space == xmlnsNamespace || (prefix == "xml") != (value.QName.Space == xmlNamespace) {
				return fmt.Errorf("%w: print value namespace", ErrInvalid)
			}
			if bound == "" {
				e.scope[prefix] = value.QName.Space
			}
			return nil
		}
		if hasChildren {
			return e.bindRoot(value.QName)
		}
		return nil
	}
	return e.bindRoot(value.QName)
}

// resolveValueQName 在Pass2决定含QName标量值的最终词法文本及必要时的局部命名空间重绑定作用域
// 入参: value 含非空QName的标量值, nodeSpace 所在元素命名空间, hasChildren 所在元素是否含XML子节点
// 返回: string 最终词法文本, map[string]string 局部作用域映射, [][2]string 局部xmlns声明列表, error 命名空间错误
func (e *printSettingsEncoder) resolveValueQName(value PrintValue, nodeSpace string, hasChildren bool) (string, map[string]string, [][2]string, error) {
	text := strings.Trim(value.Text, " \t\r\n")
	prefix, local, qualified := strings.Cut(text, ":")
	if !qualified && text == value.QName.Local && xmlNCName(text) {
		if value.QName.Space != "" {
			if hasChildren {
				return e.resolveQName(e.scope, value.QName), nil, nil, nil
			}
			localScope, localAttrs, err := e.buildLocalScope(nodeSpace, "", value.QName.Space)
			return text, localScope, localAttrs, err
		}
		return text, nil, nil, nil
	}
	if qualified && xmlNCName(prefix) && xmlNCName(local) && prefix != "xmlns" && local == value.QName.Local && value.QName.Space != "" && (prefix != "xml" || value.QName.Space == xmlNamespace) {
		if e.scope[prefix] == value.QName.Space {
			return text, nil, nil, nil
		}
		if hasChildren {
			return e.resolveQName(e.scope, value.QName), nil, nil, nil
		}
		localScope, localAttrs, err := e.buildLocalScope(nodeSpace, prefix, value.QName.Space)
		return text, localScope, localAttrs, err
	}
	return e.resolveQName(e.scope, value.QName), nil, nil, nil
}

// buildLocalScope 为存在前缀冲突的值节点构造局部命名空间作用域，并确保Framework、当前元素、xsi与xs均具无冲突前缀
// 入参: nodeSpace 元素命名空间, prefix 需局部绑定的前缀或空默认前缀, uri 局部绑定命名空间URI
// 返回: map[string]string 局部命名空间作用域, [][2]string 待写出的局部xmlns声明对, error 输出命名空间非法错误
func (e *printSettingsEncoder) buildLocalScope(nodeSpace, prefix, uri string) (map[string]string, [][2]string, error) {
	scope := make(map[string]string, len(e.scope)+5)
	maps.Copy(scope, e.scope)
	attrs := make([][2]string, 0, 5)
	addLocal := func(name, namespace string) error {
		if err := xmlNamespaceOutput(name, namespace); err != nil {
			return err
		}
		scope[name] = namespace
		attrs = append(attrs, [2]string{name, namespace})
		return nil
	}
	if err := addLocal(prefix, uri); err != nil {
		return nil, nil, err
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
			return nil, nil, err
		}
	}
	return scope, attrs, nil
}

// collectV1 在Pass1遍历PSF1设置子树收集根命名空间前缀
// 入参: value 已校验设置节点
// 返回: error 命名空间或取消错误
func (e *printSettingsEncoder) collectV1(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	if err := e.bindRoot(xml.Name{Space: printFrameworkNS, Local: printSettingNames[value.Kind]}); err != nil {
		return err
	}
	if value.Constraint != PrintConstraintUnknown {
		if err := e.bindRoot(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]}); err != nil {
			return err
		}
	}
	if value.Kind == PrintSettingValue {
		kind := value.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		if err := e.bindRoot(kind); err != nil {
			return err
		}
		if err := e.bindRoot(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		if (kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"})) && value.Value.QName != (xml.Name{}) {
			normalized := *value.Value
			normalized.Type = kind
			return e.collectValueQName(normalized, false)
		}
		return nil
	}
	if value.Name != (xml.Name{}) {
		if err := e.bindRoot(value.Name); err != nil {
			return err
		}
	}
	for _, child := range value.Children {
		if err := e.collectV1(child); err != nil {
			return err
		}
	}
	return nil
}

// collectV2 在Pass1遍历PSF2直接关键字子树收集根命名空间前缀
// 入参: value 已校验设置节点
// 返回: error 命名空间或取消错误
func (e *printSettingsEncoder) collectV2(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	if err := e.bindRoot(value.Name); err != nil {
		return err
	}
	if value.Kind == PrintSettingOption && value.Constraint != PrintConstraintUnknown {
		if err := e.bindRoot(xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]}); err != nil {
			return err
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
			if err := e.bindRoot(selVal.QName); err != nil {
				return err
			}
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
		if err := e.collectV2(child); err != nil {
			return err
		}
	}
	if refIndex >= 0 {
		if err := e.bindRoot(xml.Name{Space: printFrameworkNS, Local: "ParameterRef"}); err != nil {
			return err
		}
		if err := e.bindRoot(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		if err := e.bindRoot(value.Children[refIndex].Name); err != nil {
			return err
		}
	}
	if valueIndex >= 0 {
		valChild := value.Children[valueIndex]
		kind := valChild.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		if err := e.bindRoot(kind); err != nil {
			return err
		}
		if err := e.bindRoot(xml.Name{Space: xsiNamespace, Local: "type"}); err != nil {
			return err
		}
		if (kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"})) && valChild.Value.QName != (xml.Name{}) {
			normalized := *valChild.Value
			normalized.Type = kind
			if err := e.collectValueQName(normalized, xmlChildCount > 0); err != nil {
				return err
			}
		}
	}
	return nil
}

// writeV1 在Pass2按PSF1包装元素语法流式写出或精确计费节点子树
// 入参: value 已校验设置节点
// 返回: error 命名空间、预算、取消或输出错误
func (e *printSettingsEncoder) writeV1(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	local := printSettingNames[value.Kind]
	if value.Kind == PrintSettingValue {
		kind := value.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		text := value.Value.Text
		activeScope := e.scope
		var localAttrs [][2]string
		if (kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"})) && value.Value.QName != (xml.Name{}) {
			normalized := *value.Value
			normalized.Type = kind
			var localScope map[string]string
			var err error
			text, localScope, localAttrs, err = e.resolveValueQName(normalized, printFrameworkNS, false)
			if err != nil {
				return err
			}
			if localScope != nil {
				activeScope = localScope
			}
		}
		tag := e.resolveQName(activeScope, xml.Name{Space: printFrameworkNS, Local: local})
		typeAttr := e.resolveQName(activeScope, xml.Name{Space: xsiNamespace, Local: "type"})
		typeVal := e.resolveQName(activeScope, kind)
		if err := e.writeRaw("<" + tag); err != nil {
			return err
		}
		if err := e.writeAttr(typeAttr, typeVal); err != nil {
			return err
		}
		for _, pair := range localAttrs {
			attrName := "xmlns"
			if pair[0] != "" {
				attrName += ":" + pair[0]
			}
			if err := e.writeAttr(attrName, pair[1]); err != nil {
				return err
			}
		}
		if err := e.writeRaw(">"); err != nil {
			return err
		}
		if err := e.writeEscaped(text, false); err != nil {
			return err
		}
		return e.writeRaw("</" + tag + ">")
	}
	tag := e.resolveQName(e.scope, xml.Name{Space: printFrameworkNS, Local: local})
	if err := e.writeRaw("<" + tag); err != nil {
		return err
	}
	if value.Constraint != PrintConstraintUnknown {
		cVal := e.resolveQName(e.scope, xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
		if err := e.writeAttr("constrained", cVal); err != nil {
			return err
		}
	}
	if value.Name != (xml.Name{}) {
		if err := e.writeAttr("name", e.resolveQName(e.scope, value.Name)); err != nil {
			return err
		}
	}
	if err := e.writeRaw(">"); err != nil {
		return err
	}
	for _, child := range value.Children {
		if err := e.writeV1(child); err != nil {
			return err
		}
	}
	return e.writeRaw("</" + tag + ">")
}

// writeV2 在Pass2按PSF2直接关键字语法流式写出或精确计费节点子树
// 入参: value 已校验设置节点
// 返回: error 命名空间、预算、取消或输出错误
func (e *printSettingsEncoder) writeV2(value PrintSetting) error {
	if err := checkContext(e.options.context); err != nil {
		return err
	}
	selectionIndex, valueIndex, refIndex := -1, -1, -1
	xmlChildCount := 0
	var selQName xml.Name
	for index, child := range value.Children {
		if e.capabilities && value.Kind == PrintSettingFeature && child.Kind == PrintSettingProperty && printFrameworkSpace(child.Name.Space) && child.Name.Local == "SelectionType" {
			selVal, err := printCommonValue(child)
			if err != nil {
				return err
			}
			selQName = selVal.QName
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
	activeScope := e.scope
	var localAttrs [][2]string
	var xsiTypeVal, text string
	hasXsiType := false
	if refIndex >= 0 {
		hasXsiType = true
		xsiTypeVal = e.resolveQName(activeScope, xml.Name{Space: printFrameworkNS, Local: "ParameterRef"})
		text = e.resolveQName(activeScope, value.Children[refIndex].Name)
	} else if valueIndex >= 0 {
		valChild := value.Children[valueIndex]
		kind := valChild.Value.Type
		if kind == (xml.Name{}) {
			kind = xml.Name{Space: printValueNS, Local: "string"}
		}
		text = valChild.Value.Text
		if (kind == (xml.Name{Space: printValueNS, Local: "QName"}) || kind == (xml.Name{Space: printValueNS, Local: "string"})) && valChild.Value.QName != (xml.Name{}) {
			normalized := *valChild.Value
			normalized.Type = kind
			var localScope map[string]string
			var err error
			text, localScope, localAttrs, err = e.resolveValueQName(normalized, value.Name.Space, xmlChildCount > 0)
			if err != nil {
				return err
			}
			if localScope != nil {
				activeScope = localScope
			}
		}
		hasXsiType = true
		xsiTypeVal = e.resolveQName(activeScope, kind)
	}
	tag := e.resolveQName(activeScope, value.Name)
	psf2Prefix := printSettingsPrefix(activeScope, printFramework2NS)
	if err := e.writeRaw("<" + tag); err != nil {
		return err
	}
	if err := e.writeAttr(psf2Prefix+":psftype", printSettingNames[value.Kind]); err != nil {
		return err
	}
	if value.Kind == PrintSettingOption {
		if value.HasDefault || value.Default {
			if err := e.writeAttr(psf2Prefix+":default", strconv.FormatBool(value.Default)); err != nil {
				return err
			}
		}
		if value.Constraint != PrintConstraintUnknown {
			cVal := e.resolveQName(activeScope, xml.Name{Space: printKeywordsNS, Local: printConstraintNames[value.Constraint]})
			if err := e.writeAttr(psf2Prefix+":constrained", cVal); err != nil {
				return err
			}
		}
	}
	if selectionIndex >= 0 {
		if err := e.writeAttr(psf2Prefix+":selectiontype", e.resolveQName(activeScope, selQName)); err != nil {
			return err
		}
	}
	if hasXsiType {
		if err := e.writeAttr(e.resolveQName(activeScope, xml.Name{Space: xsiNamespace, Local: "type"}), xsiTypeVal); err != nil {
			return err
		}
	}
	for _, pair := range localAttrs {
		attrName := "xmlns"
		if pair[0] != "" {
			attrName += ":" + pair[0]
		}
		if err := e.writeAttr(attrName, pair[1]); err != nil {
			return err
		}
	}
	if err := e.writeRaw(">"); err != nil {
		return err
	}
	if text != "" {
		if err := e.writeEscaped(text, false); err != nil {
			return err
		}
	}
	for index, child := range value.Children {
		if index == selectionIndex || index == valueIndex || index == refIndex {
			continue
		}
		if err := e.writeV2(child); err != nil {
			return err
		}
	}
	return e.writeRaw("</" + tag + ">")
}

// printSettingsPrefix 从当前作用域选取实际绑定的非默认前缀，不依赖固定拼写
// 入参: scope 命名空间作用域, uri 命名空间
// 返回: string 确定性前缀，没有绑定时为空
func printSettingsPrefix(scope map[string]string, uri string) string {
	preferred := printKnownNamespacePrefix(uri)
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
