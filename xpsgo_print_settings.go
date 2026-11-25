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
	"io"
	"maps"
	"math"
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

// PrintCapabilities 保存当前设备配置的Framework能力描述
type PrintCapabilities struct {
	Version  uint32
	Elements []PrintSetting
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

// printDocumentMode 表示内部校验与编码的Print Schema文档类别
type printDocumentMode uint8

// PrintNormalizeOptions 设置PrintTicket规范化合并与设备能力补全的作用域及资源预算
type PrintNormalizeOptions struct {
	Settings PrintSettingsOptions
}

// printNormalizer 在单次规范化调用中保存能力索引、参数域、请求来源、比较预算及诊断列表
type printNormalizer struct {
	options     printSettingsConfig
	domains     map[xml.Name]*printParameterDomain
	deltaFeats  map[xml.Name]bool
	diagnostics []Diagnostic
	remaining   int
}

// PrintMediaSpec 描述能力文档支持的标准或自定义纸型规格，宽高与四周边距单位均为微米
// StandardName为Print Schema公开纸型名称（如ISOA4、NorthAmericaLetter），省略宽高时自动查表填充
// Margins依次表示左、上、右、下不可打印边距（微米），全零表示整张介质可打印
type PrintMediaSpec struct {
	StandardName  string
	Name          xml.Name
	WidthMicrons  int64
	HeightMicrons int64
	Margins       [4]int64
	Default       bool
	Constrained   PrintConstraint
}

// PrintCustomMediaSpec 描述能力文档的自定义纸型微米参数范围、步进与默认不可打印边距
type PrintCustomMediaSpec struct {
	MinWidthMicrons      int64
	MaxWidthMicrons      int64
	DefaultWidthMicrons  int64
	MinHeightMicrons     int64
	MaxHeightMicrons     int64
	DefaultHeightMicrons int64
	StepMicrons          int64
	Margins              [4]int64
}

// PrintResolutionSpec 描述能力文档支持的输出分辨率选项，单位为每英寸点数
type PrintResolutionSpec struct {
	Name        xml.Name
	X           int
	Y           int
	Default     bool
	Constrained PrintConstraint
}

// PrintCapabilitiesSpec 描述声明式构建PrintDeviceCapabilities与PrintCapabilities的设备能力规格
// 支持标准与自定义纸型、分辨率、方向、缩放、多合一、双面、无边距、色彩、质量、水印及副本参数配置
type PrintCapabilitiesSpec struct {
	CapabilitiesChangeID string
	MediaSizes           []PrintMediaSpec
	CustomMedia          *PrintCustomMediaSpec
	Resolutions          []PrintResolutionSpec
	Orientations         []string
	DefaultOrientation   string
	Scalings             []string
	DefaultScaling       string
	NUpCounts            []int
	DefaultNUp           int
	DuplexModes          []PrintDuplex
	DefaultDuplex        PrintDuplex
	Borderless           bool
	DefaultBorderless    bool
	ColorModes           []PrintColorMode
	DefaultColorMode     PrintColorMode
	OutputQualities      []string
	DefaultOutputQuality string
	Watermark            bool
	MaxCopies            int
	DefaultCopies        int
}

// PrintTicketSpec 描述声明式构建标准PrintTicket的高层打印参数规格
// 零值字段表示省略对应设置，CustomWidthMicrons与CustomHeightMicrons均大于零时启用CustomMediaSize
type PrintTicketSpec struct {
	Version               uint32
	MediaStandardName     string
	CustomWidthMicrons    int64
	CustomHeightMicrons   int64
	Resolution            *PrintResolution
	Orientation           string
	Borderless            *bool
	MirrorImage           string
	Scaling               string
	ScaleWidth            int
	ScaleHeight           int
	Scale                 int
	OffsetWidthMicrons    int64
	OffsetHeightMicrons   int64
	ScaleOffsetAlignment  string
	OutputColor           *PrintColor
	NegativeImage         *bool
	OutputQuality         string
	PhotoPrintingIntent   string
	Watermark             *PrintWatermark
	Copies                int
	DocumentCopies        int
	PageCopies            int
	Collate               string
	Duplex                *PrintDuplex
	ManualDuplex          bool
	NUp                   int
	PresentationDirection string
	PageOrder             string
	PageRanges            string
	PosterSheets          int
	Finishing             *PrintFinishing
	JobLevelFinishing     bool
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

// printDeriveState 保存V4 PDC派生阶段从有效票据提取的纸型、方向、无边距及冲突状态
type printDeriveState struct {
	hasMedia        bool
	imageableWidth  int64
	imageableHeight int64
	originX         int64
	originY         int64
	extentW         int64
	extentH         int64
	activeNUp       int
	activePoster    int
	activeBooklet   bool
	hasJobBind      bool
	hasDocBind      bool
	hasJobDuplex    bool
	hasDocDuplex    bool
	hasJobNUp       bool
	hasDocNUp       bool
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
		baseType := opcMediaTypeBase(typeName)
		if r.format == FormatXPS && !strings.EqualFold(baseType, printTicketType) {
			return &PartError{Part: part, Err: fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)}
		}
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
		parsedVal, err := parsePrintValueContent(node, true)
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
		if err := builder.reserve(int64(len(changeID)) + int64(len(typeText)) + 56); err != nil {
			return nil, err
		}
		root.Children = append(root.Children, &xmlElement{
			Name:       xml.Name{Local: "CapabilitiesChangeID"},
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
		switch name.Space {
		case printFrameworkNS:
			prefix = "psf"
		case printFramework2NS:
			prefix = "psf2"
		case printKeywordsNS:
			prefix = "psk"
		case printKeywordsV11NS:
			prefix = "psk11"
		case printKeywordsV12NS:
			prefix = "psk12"
		case printKeywords2NS:
			prefix = "psk2"
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
	root, err := printDocumentRoot(p.Version, p.Elements, configuration, true)
	if err != nil {
		return nil, err
	}
	model, err := parsePrintDocument(root, configuration, true)
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
	if int64(len(value.Text)) > min(options.Limits.MaxMetadataBytes, options.Limits.MaxPartBytes, options.Limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: print parameter value byte budget", ErrLimit)
	}
	builder := printSettingsBuilder{options: options, framework: printFrameworkNS, prefixes: map[string]string{printFrameworkNS: "psf"}, scope: map[string]string{"psf": printFrameworkNS}}
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
		domains[printCanonicalKey(parameter.Name)] = domain
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
	root, err := printDocumentRootWithChangeID(settings.Version, settings.CapabilitiesChangeID, settings.Elements, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return 0, err
	}
	if _, err := parsePrintDocumentMode(root, configuration, printDocumentDeviceCapabilities); err != nil {
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

// NormalizePrintTicket 直接基于PrintCapabilities对基础票据与增量票据执行合并、约束消解、默认补全与参数量化
// 入参: ctx 取消Context，nil采用Background, capabilities 设备PrintCapabilities能力文档, base 基础票据，允许为nil, delta 优先增量票据，允许为nil, options 作用域及资源预算，nil采用默认值
// 返回: *PrintSettings 规范化后的独立打印设置, []Diagnostic 规范化过程产生的诊断记录, error 结构、能力、预算或取消错误
func NormalizePrintTicket(ctx context.Context, capabilities *PrintCapabilities, base, delta *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, []Diagnostic, error) {
	if capabilities == nil {
		return nil, nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	var normOpts *PrintNormalizeOptions
	if options != nil {
		normOpts = &PrintNormalizeOptions{Settings: *options}
	}
	return NormalizePrintSettings(ctx, base, delta, capabilities.Settings(), normOpts)
}

// NormalizePrintSettings 按Microsoft Print Schema规范对基础票据与增量票据执行合并、设备能力校验、约束消解、默认补全与参数量化
// capabilities支持PrintCapabilities或PrintDeviceCapabilities模型，输出完全合法且独立的PrintSettings
// 入参: ctx 取消Context，nil采用Background, base 基础票据，允许为nil, delta 优先增量票据，允许为nil, capabilities 设备能力文档, options 规范化参数，nil采用默认值
// 返回: *PrintSettings 规范化后的独立打印设置, []Diagnostic 规范化过程产生的诊断记录, error 结构、能力、预算或取消错误
func NormalizePrintSettings(ctx context.Context, base, delta, capabilities *PrintSettings, options *PrintNormalizeOptions) (*PrintSettings, []Diagnostic, error) {
	var settingsOpts *PrintSettingsOptions
	if options != nil {
		optsCopy := options.Settings
		settingsOpts = &optsCopy
	}
	configuration, err := printSettingsOptions(ctx, settingsOpts)
	if err != nil {
		return nil, nil, err
	}
	if capabilities == nil {
		return nil, nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	capConfig := configuration
	capConfig.Scope = PrintScopeUnknown
	capMode := printDocumentCapabilities
	if capabilities.Version == 2 {
		capMode = printDocumentDeviceCapabilities
	}
	capRoot, err := printDocumentRootWithChangeID(capabilities.Version, capabilities.CapabilitiesChangeID, capabilities.Elements, capConfig, capMode)
	if err != nil {
		return nil, nil, err
	}
	capModel, err := parsePrintDocumentMode(capRoot, capConfig, capMode)
	if err != nil {
		return nil, nil, err
	}
	deltaFeats := make(map[xml.Name]bool)
	if delta != nil {
		deltaRoot, err := printSettingsRoot(delta, configuration)
		if err != nil {
			return nil, nil, err
		}
		parsedDelta, err := parsePrintSettings(deltaRoot, configuration)
		if err != nil {
			return nil, nil, err
		}
		for _, element := range parsedDelta.Elements {
			if element.Kind == PrintSettingFeature {
				deltaFeats[printCanonicalKey(element.Name)] = true
			}
		}
	}
	var ticket *PrintSettings
	if base != nil && delta != nil {
		ticket, err = MergePrintSettings(ctx, base, delta, &configuration.PrintSettingsOptions)
	} else if base != nil {
		ticket, err = MergePrintSettings(ctx, base, &PrintSettings{Version: base.Version}, &configuration.PrintSettingsOptions)
	} else if delta != nil {
		ticket, err = MergePrintSettings(ctx, &PrintSettings{Version: delta.Version}, delta, &configuration.PrintSettingsOptions)
	} else {
		ticket = &PrintSettings{Version: capModel.Version}
	}
	if err != nil {
		return nil, nil, err
	}
	normalizer := printNormalizer{
		options:    configuration,
		domains:    make(map[xml.Name]*printParameterDomain),
		deltaFeats: deltaFeats,
		remaining:  configuration.MaxOptionComparisons,
	}
	for _, element := range capModel.Elements {
		if element.Kind != PrintSettingParameterDef {
			continue
		}
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		domain, err := printParameterDefinition(element, capConfig)
		if err != nil {
			return nil, nil, err
		}
		key := printCanonicalKey(element.Name)
		normalizer.domains[key] = domain
	}
	paramInits := make(map[xml.Name]PrintSetting)
	paramValues := make(map[xml.Name]*PrintValue)
	var rootProperties []PrintSetting
	for _, element := range ticket.Elements {
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		switch element.Kind {
		case PrintSettingParameterInit:
			key := printCanonicalKey(element.Name)
			if normalizer.domains[key] == nil {
				normalizer.addDiagnostic("ParameterInit", "name", fmt.Sprintf("unsupported print ParameterInit %s removed", element.Name.Local))
				continue
			}
			paramInits[key] = element
			if len(element.Children) == 1 && element.Children[0].Value != nil {
				paramValues[key] = element.Children[0].Value
			}
		case PrintSettingProperty:
			rootProperties = append(rootProperties, element)
		}
	}
	skipCaps := normalizer.resolveRootMutexGroups(ticket.Elements, capModel.Elements, paramValues)
	normalizedFeatures, err := normalizer.normalizeFeatureList(ticket.Elements, capModel.Elements, paramValues, true, skipCaps)
	if err != nil {
		return nil, nil, err
	}
	referenced := make(map[xml.Name]bool)
	printCollectParameterRefs(normalizedFeatures, referenced)
	normalizedParams, err := normalizer.normalizeParameters(capModel.Elements, paramInits, referenced)
	if err != nil {
		return nil, nil, err
	}
	resultElements := make([]PrintSetting, 0, len(normalizedFeatures)+len(rootProperties)+len(normalizedParams))
	usedKeys := make(map[xml.Name]bool, len(normalizedFeatures)+len(normalizedParams))
	for _, feature := range normalizedFeatures {
		resultElements = append(resultElements, feature)
		usedKeys[printCanonicalKey(feature.Name)] = true
	}
	for _, param := range normalizedParams {
		usedKeys[printCanonicalKey(param.Name)] = true
	}
	for _, prop := range rootProperties {
		if !usedKeys[printCanonicalKey(prop.Name)] {
			resultElements = append(resultElements, prop)
			usedKeys[printCanonicalKey(prop.Name)] = true
		}
	}
	resultElements = append(resultElements, normalizedParams...)
	version := ticket.Version
	if version == 0 {
		version = 1
	}
	if version > 1 && printSettingsHasAnonymousOption(resultElements) {
		version = 1
	}
	printStripOptionDefaults(resultElements)
	candidate := &PrintSettings{Version: version, Elements: resultElements}
	root, err := printSettingsRoot(candidate, configuration)
	if err != nil {
		return nil, nil, err
	}
	result, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, nil, err
	}
	if _, err := writePrintSettingsMarkup(io.Discard, root, configuration); err != nil {
		return nil, nil, err
	}
	return result, normalizer.diagnostics, nil
}

// resolveRootMutexGroups 在根级规范化前消解作业级与文档级互斥Feature对，避免同时产出冲突设置
// 入参: requestedElements 票据根元素, capElements 能力根元素, paramValues 票据参数初值映射
// 返回: map[xml.Name]bool 需跳过规范化与默认补全的能力Feature规范键集合
func (n *printNormalizer) resolveRootMutexGroups(requestedElements, capElements []PrintSetting, paramValues map[xml.Name]*PrintValue) map[xml.Name]bool {
	skip := make(map[xml.Name]bool)
	capOrder := make(map[xml.Name]int)
	capFeats := make(map[xml.Name]PrintSetting)
	for index, element := range capElements {
		if element.Kind != PrintSettingFeature {
			continue
		}
		if n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(element.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(element.Name)
		capOrder[key] = index
		capFeats[key] = element
	}
	reqFeats := make(map[xml.Name]PrintSetting)
	for _, element := range requestedElements {
		if element.Kind == PrintSettingFeature {
			reqFeats[printCanonicalKey(element.Name)] = element
		}
	}
	pairs := [][2]string{
		{"JobBindAllDocuments", "DocumentBinding"},
		{"JobDuplexAllDocumentsContiguously", "DocumentDuplex"},
		{"JobNUpAllDocumentsContiguously", "DocumentNUp"},
	}
	for _, pair := range pairs {
		jobKey := xml.Name{Space: printKeywordsNS, Local: pair[0]}
		docKey := xml.Name{Space: printKeywordsNS, Local: pair[1]}
		_, hasCapJob := capFeats[jobKey]
		_, hasCapDoc := capFeats[docKey]
		if !hasCapJob || !hasCapDoc {
			continue
		}
		reqJob, hasReqJob := reqFeats[jobKey]
		reqDoc, hasReqDoc := reqFeats[docKey]
		if hasReqJob && !hasReqDoc {
			skip[docKey] = true
			continue
		}
		if !hasReqJob && hasReqDoc {
			skip[jobKey] = true
			continue
		}
		if hasReqJob && hasReqDoc {
			dropJob := true
			if n.deltaFeats[jobKey] && !n.deltaFeats[docKey] {
				dropJob = false
			} else if n.deltaFeats[docKey] && !n.deltaFeats[jobKey] {
				dropJob = true
			} else {
				jobNoOp := printMutexFeatureNoOp(reqJob, paramValues)
				docNoOp := printMutexFeatureNoOp(reqDoc, paramValues)
				if !jobNoOp && docNoOp {
					dropJob = false
				}
			}
			if dropJob {
				skip[jobKey] = true
				n.addDiagnostic("Feature", "name", fmt.Sprintf("conflicting print Feature %s removed in favor of %s", pair[0], pair[1]))
			} else {
				skip[docKey] = true
				n.addDiagnostic("Feature", "name", fmt.Sprintf("conflicting print Feature %s removed in favor of %s", pair[1], pair[0]))
			}
			continue
		}
		if capOrder[jobKey] < capOrder[docKey] {
			skip[docKey] = true
		} else {
			skip[jobKey] = true
		}
	}
	return skip
}

// printMutexFeatureNoOp 判断互斥装订、双面或拼版Feature在请求中是否为无效果恒等项
// 入参: feature 请求的Feature节点, paramValues 票据参数初值映射
// 返回: bool 是否为无效果恒等项
func printMutexFeatureNoOp(feature PrintSetting, paramValues map[xml.Name]*PrintValue) bool {
	for _, child := range feature.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		switch feature.Name.Local {
		case "JobBindAllDocuments", "DocumentBinding":
			return printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "None"
		case "JobDuplexAllDocumentsContiguously", "DocumentDuplex":
			return printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "OneSided"
		case "JobNUpAllDocumentsContiguously", "DocumentNUp":
			for _, prop := range child.Children {
				if prop.Kind == PrintSettingScoredProperty && printPublicKeywordSpace(prop.Name.Space) && prop.Name.Local == "PagesPerSheet" {
					val, ref := printScoredValue(prop.Children)
					if ref != (xml.Name{}) {
						val = paramValues[printCanonicalKey(ref)]
					}
					return val != nil && strings.Trim(val.Text, " \t\r\n") == "1"
				}
			}
			return false
		}
	}
	return true
}

// addDiagnostic 记录一条规范化过程中的非致命修正诊断
// 入参: element 元素名称, attribute 属性名称, message 诊断消息
func (n *printNormalizer) addDiagnostic(element, attribute, message string) {
	n.diagnostics = append(n.diagnostics, Diagnostic{Element: element, Attribute: attribute, Message: message})
}

// step 在选项比较前检查取消状态与比较预算
// 返回: error 取消或预算超限错误
func (n *printNormalizer) step() error {
	if err := checkContext(n.options.context); err != nil {
		return err
	}
	if n.remaining == 0 {
		return fmt.Errorf("%w: print Option comparison budget", ErrLimit)
	}
	n.remaining--
	return nil
}

// normalizeFeatureList 在同一父级层级规范化Feature集合，移除未声明项、执行互斥跳过并对缺失项执行Defaulting
// 入参: requestedElements 票据当前层级元素, capElements 能力当前层级元素, paramValues 票据参数初值映射, isRoot 是否位于文档根层级, skipCaps 需跳过的能力Feature规范键集合
// 返回: []PrintSetting 规范化后的Feature列表, error 预算或取消错误
func (n *printNormalizer) normalizeFeatureList(requestedElements, capElements []PrintSetting, paramValues map[xml.Name]*PrintValue, isRoot bool, skipCaps map[xml.Name]bool) ([]PrintSetting, error) {
	capByKey := make(map[xml.Name]PrintSetting)
	for _, element := range capElements {
		if element.Kind == PrintSettingFeature {
			capByKey[printCanonicalKey(element.Name)] = element
		}
	}
	reqByKey := make(map[xml.Name]PrintSetting)
	for _, element := range requestedElements {
		if element.Kind != PrintSettingFeature {
			continue
		}
		key := printCanonicalKey(element.Name)
		if _, exists := capByKey[key]; !exists {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("unsupported print Feature %s removed", element.Name.Local))
			continue
		}
		reqByKey[key] = element
	}
	var result []PrintSetting
	for _, capFeat := range capElements {
		if capFeat.Kind != PrintSettingFeature {
			continue
		}
		if err := checkContext(n.options.context); err != nil {
			return nil, err
		}
		if isRoot && n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(capFeat.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(capFeat.Name)
		if skipCaps[key] {
			continue
		}
		reqFeat, present := reqByKey[key]
		var reqPtr *PrintSetting
		if present {
			reqPtr = &reqFeat
		}
		normalized, ok, err := n.normalizeFeature(reqPtr, capFeat, paramValues)
		if err != nil {
			return nil, err
		}
		if ok {
			result = append(result, normalized)
		}
	}
	return result, nil
}

// printFeatureSuppressesSubFeatures 判断指定Feature在当前选中项下是否应跳过子Feature默认补全及丢弃冲突子Feature
// 入参: featureName Feature名称, selectedOptions 最终选中的Option切片, hasRequestedSub 请求中是否显式声明了子Feature
// 返回: bool 是否跳过子Feature补全, bool 是否必须移除请求中携带的子Feature
func printFeatureSuppressesSubFeatures(featureName xml.Name, selectedOptions []PrintSetting, hasRequestedSub bool) (bool, bool) {
	if !printPublicKeywordSpace(featureName.Space) || len(selectedOptions) == 0 {
		return false, false
	}
	onlyNone := true
	for _, opt := range selectedOptions {
		if !printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None" {
			onlyNone = false
			break
		}
	}
	if !onlyNone {
		return false, false
	}
	if featureName.Local == "PageWatermark" {
		return true, true
	}
	if featureName.Local == "PageScaling" && !hasRequestedSub {
		return true, false
	}
	return false, false
}

// normalizeFeature 规范化单个Feature及其直接Option和子Feature，支持参数化补全、内联参数裁剪、约束就近评分与PickMany恒等消解
// 入参: requested 票据中的Feature指针，缺失时为nil, capability 设备能力中的Feature, paramValues 票据参数初值映射
// 返回: PrintSetting 规范化Feature, bool 是否生成有效Feature, error 预算或取消错误
func (n *printNormalizer) normalizeFeature(requested *PrintSetting, capability PrintSetting, paramValues map[xml.Name]*PrintValue) (PrintSetting, bool, error) {
	selection, err := capability.Selection()
	if err != nil {
		return PrintSetting{}, false, err
	}
	var allOptions []PrintSetting
	var unconstrained []PrintSetting
	for _, child := range capability.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		allOptions = append(allOptions, child)
		if child.Constraint == PrintConstraintUnknown || child.Constraint == PrintConstraintNone {
			unconstrained = append(unconstrained, child)
		}
	}
	defaultIndex := -1
	for index := range unconstrained {
		if unconstrained[index].Default {
			defaultIndex = index
			break
		}
	}
	if defaultIndex < 0 && len(unconstrained) > 0 {
		defaultIndex = 0
	}
	var selectedOptions []PrintSetting
	var selectedCaps []PrintSetting
	if requested == nil {
		if len(allOptions) > 0 {
			if defaultIndex < 0 {
				return PrintSetting{}, false, nil
			}
			selectedOptions = append(selectedOptions, printTicketOptionFromCapability(unconstrained[defaultIndex]))
			selectedCaps = append(selectedCaps, unconstrained[defaultIndex])
		}
		var children []PrintSetting
		children = append(children, selectedOptions...)
		suppressSub, _ := printFeatureSuppressesSubFeatures(capability.Name, selectedOptions, false)
		if !suppressSub {
			subFeatures, err := n.normalizeFeatureList(nil, capability.Children, paramValues, false, nil)
			if err != nil {
				return PrintSetting{}, false, err
			}
			children = append(children, subFeatures...)
		}
		if len(children) == 0 {
			return PrintSetting{}, false, nil
		}
		return PrintSetting{Kind: PrintSettingFeature, Name: capability.Name, Children: children}, true, nil
	}
	var reqOptions []PrintSetting
	var reqProps []PrintSetting
	hasRequestedSub := false
	for _, child := range requested.Children {
		if child.Kind == PrintSettingOption {
			reqOptions = append(reqOptions, child)
		} else if child.Kind == PrintSettingProperty {
			reqProps = append(reqProps, child)
		} else if child.Kind == PrintSettingFeature {
			hasRequestedSub = true
		}
	}
	if len(allOptions) > 0 {
		if defaultIndex < 0 {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("all options for print Feature %s are constrained", capability.Name.Local))
			return PrintSetting{}, false, nil
		}
		if len(reqOptions) == 0 {
			selectedOptions = append(selectedOptions, printTicketOptionFromCapability(unconstrained[defaultIndex]))
			selectedCaps = append(selectedCaps, unconstrained[defaultIndex])
		} else {
			if selection == PrintSelectionOne && len(reqOptions) > 1 {
				n.addDiagnostic("Feature", "name", fmt.Sprintf("multiple options on PickOne print Feature %s resolved", capability.Name.Local))
				chosenReq := reqOptions[0]
				picked := false
				for _, candidateReq := range reqOptions {
					matchedIndex, err := n.matchExactOption(candidateReq, unconstrained, paramValues)
					if err != nil {
						return PrintSetting{}, false, err
					}
					if matchedIndex >= 0 {
						chosenReq, picked = candidateReq, true
						break
					}
				}
				if !picked {
					for _, candidateReq := range reqOptions {
						if _, matchedIndex, ok, err := n.normalizeParameterizedOption(candidateReq, unconstrained, paramValues, false); err != nil {
							return PrintSetting{}, false, err
						} else if ok && matchedIndex >= 0 {
							chosenReq = candidateReq
							break
						}
					}
				}
				reqOptions = []PrintSetting{chosenReq}
			}
			selectedIndices := make(map[int]bool)
			for _, reqOpt := range reqOptions {
				matchedIndex, err := n.matchExactOption(reqOpt, unconstrained, paramValues)
				if err != nil {
					return PrintSetting{}, false, err
				}
				if matchedIndex >= 0 {
					if selectedIndices[matchedIndex] {
						continue
					}
					selectedIndices[matchedIndex] = true
					kept := printCompleteOptionFromCapability(reqOpt, unconstrained[matchedIndex])
					selectedOptions = append(selectedOptions, kept)
					selectedCaps = append(selectedCaps, unconstrained[matchedIndex])
					continue
				}
				clampedOpt, clampedIndex, clampedOK, err := n.normalizeParameterizedOption(reqOpt, unconstrained, paramValues, true)
				if err != nil {
					return PrintSetting{}, false, err
				}
				if clampedOK && clampedIndex >= 0 {
					if selectedIndices[clampedIndex] {
						continue
					}
					selectedIndices[clampedIndex] = true
					selectedOptions = append(selectedOptions, clampedOpt)
					selectedCaps = append(selectedCaps, unconstrained[clampedIndex])
					continue
				}
				scoringOpt := reqOpt
				if reqOpt.Name != (xml.Name{}) {
					reqKey := printCanonicalKey(reqOpt.Name)
					for _, capOpt := range allOptions {
						if printCanonicalKey(capOpt.Name) == reqKey && printScoredCount(capOpt.Children) > 0 {
							scoringOpt = printCompleteOptionFromCapability(reqOpt, capOpt)
							break
						}
					}
				}
				bestIndex, err := n.bestOption(scoringOpt, unconstrained, paramValues)
				if err != nil {
					return PrintSetting{}, false, err
				}
				chosenIndex := defaultIndex
				if bestIndex >= 0 {
					chosenIndex = bestIndex
				}
				chosen := unconstrained[chosenIndex]
				n.addDiagnostic("Option", "name", fmt.Sprintf("print Option %s on Feature %s replaced by %s", reqOpt.Name.Local, capability.Name.Local, chosen.Name.Local))
				if selectedIndices[chosenIndex] {
					continue
				}
				selectedIndices[chosenIndex] = true
				selectedOptions = append(selectedOptions, printTicketOptionFromCapability(chosen))
				selectedCaps = append(selectedCaps, chosen)
			}
			if selection == PrintSelectionMany && len(selectedOptions) > 1 {
				hasIdentity, hasNonIdentity := false, false
				identities := make([]bool, len(selectedCaps))
				for index, capOpt := range selectedCaps {
					isID, err := capOpt.Identity()
					if err != nil {
						return PrintSetting{}, false, err
					}
					identities[index] = isID
					if isID {
						hasIdentity = true
					} else {
						hasNonIdentity = true
					}
				}
				if hasIdentity && hasNonIdentity {
					filtered := make([]PrintSetting, 0, len(selectedOptions))
					for index, opt := range selectedOptions {
						if identities[index] {
							n.addDiagnostic("Option", "name", fmt.Sprintf("identity print Option %s removed when combined with other Options on Feature %s", opt.Name.Local, capability.Name.Local))
							continue
						}
						filtered = append(filtered, opt)
					}
					selectedOptions = filtered
				}
			}
		}
	} else if len(reqOptions) > 0 {
		n.addDiagnostic("Option", "name", fmt.Sprintf("unsupported options on container print Feature %s removed", capability.Name.Local))
	}
	var children []PrintSetting
	children = append(children, selectedOptions...)
	suppressSub, dropReqSub := printFeatureSuppressesSubFeatures(capability.Name, selectedOptions, hasRequestedSub)
	var subFeatures []PrintSetting
	if suppressSub {
		if dropReqSub && hasRequestedSub {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("incompatible subfeatures removed for print Feature %s", capability.Name.Local))
		}
	} else {
		subFeatures, err = n.normalizeFeatureList(requested.Children, capability.Children, paramValues, false, nil)
		if err != nil {
			return PrintSetting{}, false, err
		}
		children = append(children, subFeatures...)
	}
	if len(children) == 0 {
		return PrintSetting{}, false, nil
	}
	usedPropKeys := make(map[xml.Name]bool, len(subFeatures))
	for _, sub := range subFeatures {
		usedPropKeys[printCanonicalKey(sub.Name)] = true
	}
	for _, prop := range reqProps {
		if !usedPropKeys[printCanonicalKey(prop.Name)] {
			children = append(children, printCloneSetting(prop))
		}
	}
	return PrintSetting{Kind: PrintSettingFeature, Name: requested.Name, Children: children}, true, nil
}

// printCompleteOptionFromCapability 将匹配能力的请求Option转为合法票据Option并从能力Option补齐缺失ScoredProperty与ParameterRef
// 入参: reqOpt 请求Option节点, capOpt 匹配的能力Option节点
// 返回: PrintSetting 补齐后的独立票据Option节点
func printCompleteOptionFromCapability(reqOpt, capOpt PrintSetting) PrintSetting {
	kept := printTicketOptionFromCapability(reqOpt)
	if kept.Name == (xml.Name{}) && capOpt.Name != (xml.Name{}) {
		kept.Name = capOpt.Name
	}
	kept.Children = printMergeMissingScored(kept.Children, capOpt.Children)
	return kept
}

// printMergeMissingScored 递归将能力节点中缺失的ScoredProperty补入目标节点子列表，保持请求既有值不变
// 入参: dstChildren 请求侧已拷贝子列表, capChildren 能力侧子列表
// 返回: []PrintSetting 补齐后的子列表
func printMergeMissingScored(dstChildren, capChildren []PrintSetting) []PrintSetting {
	existing := make(map[xml.Name]int)
	for index, child := range dstChildren {
		if child.Kind == PrintSettingScoredProperty {
			existing[printCanonicalKey(child.Name)] = index
		}
	}
	for _, capChild := range capChildren {
		if capChild.Kind != PrintSettingScoredProperty {
			continue
		}
		key := printCanonicalKey(capChild.Name)
		if idx, ok := existing[key]; ok {
			dstChildren[idx].Children = printMergeMissingScored(dstChildren[idx].Children, capChild.Children)
			continue
		}
		dstChildren = append(dstChildren, printTicketOptionFromCapability(capChild))
		existing[key] = len(dstChildren) - 1
	}
	return dstChildren
}

// normalizeParameterizedOption 尝试将请求Option内联超界或未对齐的参数化ScoredProperty按对应ParameterDef裁剪量化以匹配未受约束候选
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射, emitDiag 是否记录修正诊断
// 返回: PrintSetting 裁剪补全后的票据Option, int 匹配候选下标, bool 是否匹配成功, error 预算或取消错误
func (n *printNormalizer) normalizeParameterizedOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue, emitDiag bool) (PrintSetting, int, bool, error) {
	if printScoredCount(reqOpt.Children) == 0 {
		return PrintSetting{}, -1, false, nil
	}
	reqKey := printCanonicalKey(reqOpt.Name)
	hasNamed := false
	if reqOpt.Name != (xml.Name{}) {
		for _, cand := range candidates {
			if printCanonicalKey(cand.Name) == reqKey {
				hasNamed = true
				break
			}
		}
	}
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return PrintSetting{}, -1, false, err
		}
		sameName := reqOpt.Name != (xml.Name{}) && printCanonicalKey(cand.Name) == reqKey
		if hasNamed && !sameName {
			continue
		}
		cloned := printTicketOptionFromCapability(reqOpt)
		if cloned.Name == (xml.Name{}) && cand.Name != (xml.Name{}) {
			cloned.Name = cand.Name
		}
		clampedChildren, changed, ok, err := n.normalizeParameterizedScored(cloned.Children, cand.Children, sameName, paramValues, emitDiag)
		if err != nil {
			return PrintSetting{}, -1, false, err
		}
		if ok && changed {
			cloned.Children = printMergeMissingScored(clampedChildren, cand.Children)
			return cloned, index, true, nil
		}
	}
	return PrintSetting{}, -1, false, nil
}

// normalizeParameterizedScored 递归校验并对参数化ScoredProperty的内联超界数值执行ParameterDef域内裁剪量化
// 入参: reqChildren 请求子元素, capChildren 能力子元素, subset 是否允许省略描述, paramValues 票据参数初值映射, emitDiag 是否记录诊断
// 返回: []PrintSetting 规范化后的子元素, bool 是否执行过参数裁剪量化, bool 是否完整匹配候选结构, error 预算或取消错误
func (n *printNormalizer) normalizeParameterizedScored(reqChildren, capChildren []PrintSetting, subset bool, paramValues map[xml.Name]*PrintValue, emitDiag bool) ([]PrintSetting, bool, bool, error) {
	if !subset && printScoredCount(reqChildren) != printScoredCount(capChildren) {
		return nil, false, false, nil
	}
	capByKey := make(map[xml.Name]PrintSetting)
	for _, setting := range capChildren {
		if setting.Kind == PrintSettingScoredProperty {
			capByKey[printCanonicalKey(setting.Name)] = setting
		}
	}
	result := make([]PrintSetting, len(reqChildren))
	copy(result, reqChildren)
	anyChanged := false
	for index := range result {
		setting := &result[index]
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := n.step(); err != nil {
			return nil, false, false, err
		}
		cand, exists := capByKey[printCanonicalKey(setting.Name)]
		if !exists {
			return nil, false, false, nil
		}
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if capRef != (xml.Name{}) {
			if reqRef != (xml.Name{}) {
				if printCanonicalKey(reqRef) != printCanonicalKey(capRef) {
					return nil, false, false, nil
				}
			} else {
				domain := n.domains[printCanonicalKey(capRef)]
				if domain == nil || reqVal == nil {
					return nil, false, false, nil
				}
				if _, err := domain.value(reqVal, n.options); err != nil {
					if !errors.Is(err, ErrInvalid) {
						return nil, false, false, err
					}
					clamped, adjusted, ok, err := n.clampValueForDomain(*reqVal, domain)
					if err != nil {
						return nil, false, false, err
					}
					if !ok {
						return nil, false, false, nil
					}
					for childIdx := range setting.Children {
						if setting.Children[childIdx].Kind == PrintSettingValue {
							valCopy := clamped
							setting.Children[childIdx].Value = &valCopy
							break
						}
					}
					if adjusted {
						anyChanged = true
						if emitDiag {
							n.addDiagnostic("ScoredProperty", "name", fmt.Sprintf("inline print ScoredProperty %s clamped or quantized to %s", setting.Name.Local, clamped.Text))
						}
					}
				}
			}
		} else {
			if reqRef != (xml.Name{}) {
				reqVal = paramValues[printCanonicalKey(reqRef)]
				if reqVal == nil {
					if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
						reqVal = &domain.defaultValue
					}
				}
			}
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil || !same {
				return nil, false, false, err
			}
		}
		nestedChildren, nestedChanged, nestedOK, err := n.normalizeParameterizedScored(setting.Children, cand.Children, subset, paramValues, emitDiag)
		if err != nil || !nestedOK {
			return nil, false, false, err
		}
		setting.Children = nestedChildren
		anyChanged = anyChanged || nestedChanged
	}
	return result, anyChanged, true, nil
}

// normalizeValueForDomain 按ParameterDef域定义裁剪数值、按Multiple步进量化或截断超长字符串，无法合法修正时返回回退原因
// 入参: val 原始标量值, domain 参数域定义
// 返回: PrintValue 规范化后的值, bool 是否产生裁剪或截断, string 无法修正时的回退诊断原因，空表示合法, error 算术预算或取消错误
func (n *printNormalizer) normalizeValueForDomain(val PrintValue, domain *printParameterDomain) (PrintValue, bool, string, error) {
	if val.Type == (xml.Name{}) {
		val.Type = xml.Name{Space: printValueNS, Local: "string"}
	}
	if val.Type != domain.kind {
		return PrintValue{}, false, "type mismatch reset to default", nil
	}
	switch domain.kind.Local {
	case "integer", "decimal":
		text := strings.Trim(val.Text, " \t\r\n")
		if text == "" || domain.kind.Local == "integer" && !printInteger(text) || domain.kind.Local == "decimal" && !printDecimal(text) {
			return PrintValue{}, false, "invalid numeric value reset to default", nil
		}
		num, err := printParameterNumber(text, n.options)
		if err != nil {
			if errors.Is(err, ErrInvalid) {
				return PrintValue{}, false, "invalid numeric value reset to default", nil
			}
			return PrintValue{}, false, "", err
		}
		adjusted := false
		if num.Cmp(domain.minimum) < 0 {
			num = new(big.Rat).Set(domain.minimum)
			adjusted = true
		} else if num.Cmp(domain.maximum) > 0 {
			num = new(big.Rat).Set(domain.maximum)
			adjusted = true
		}
		if domain.multiple != nil {
			diff := new(big.Rat).Sub(num, domain.minimum)
			quot := new(big.Rat).Quo(diff, domain.multiple)
			if !quot.IsInt() {
				qInt := new(big.Int).Quo(quot.Num(), quot.Denom())
				rem := new(big.Int).Rem(quot.Num(), quot.Denom())
				twiceRem := new(big.Int).Lsh(rem, 1)
				chosen := new(big.Int).Set(qInt)
				if twiceRem.Cmp(quot.Denom()) >= 0 {
					ceilQ := new(big.Int).Add(qInt, big.NewInt(1))
					ceilVal := new(big.Rat).Add(domain.minimum, new(big.Rat).Mul(new(big.Rat).SetInt(ceilQ), domain.multiple))
					if ceilVal.Cmp(domain.maximum) <= 0 {
						chosen = ceilQ
					}
				}
				num = new(big.Rat).Add(domain.minimum, new(big.Rat).Mul(new(big.Rat).SetInt(chosen), domain.multiple))
				adjusted = true
			}
		}
		if adjusted {
			if domain.kind.Local == "integer" {
				val.Text = num.Num().String()
			} else {
				val.Text = printFormatDecimalRat(num, n.options.MaxNumericDigits)
			}
		}
		return val, adjusted, "", nil
	case "string":
		if _, err := domain.value(&val, n.options); err == nil {
			return val, false, "", nil
		} else if !errors.Is(err, ErrInvalid) {
			return PrintValue{}, false, "", err
		}
		if domain.unit == "sRGB" {
			return PrintValue{}, false, "invalid sRGB string reset to default", nil
		}
		if domain.unit == "numeric" {
			for _, character := range val.Text {
				if character < '0' || character > '9' {
					return PrintValue{}, false, "invalid numeric string reset to default", nil
				}
			}
		}
		count := big.NewRat(int64(utf8.RuneCountInString(val.Text)), 1)
		if count.Cmp(domain.maximum) > 0 {
			if !domain.maximum.IsInt() || !domain.maximum.Num().IsInt64() {
				return PrintValue{}, false, "string length exceeded reset to default", nil
			}
			val.Text = printTruncateRunes(val.Text, int(domain.maximum.Num().Int64()))
			if _, err := domain.value(&val, n.options); err != nil {
				if errors.Is(err, ErrInvalid) {
					return PrintValue{}, false, "truncated string invalid reset to default", nil
				}
				return PrintValue{}, false, "", err
			}
			return val, true, "", nil
		}
		return PrintValue{}, false, "string shorter than MinLength reset to default", nil
	default:
		validated, err := domain.value(&val, n.options)
		if err == nil {
			return *validated, false, "", nil
		}
		if errors.Is(err, ErrInvalid) {
			return PrintValue{}, false, "invalid QName value reset to default", nil
		}
		return PrintValue{}, false, "", err
	}
}

// clampValueForDomain 将类型匹配的数值或字符串值按ParameterDef的上下界与Multiple步进裁剪量化
// 入参: val 原始标量值, domain 参数域定义
// 返回: PrintValue 规范化后的值, bool 是否产生修正, bool 是否可按该域合法裁剪, error 算术预算或取消错误
func (n *printNormalizer) clampValueForDomain(val PrintValue, domain *printParameterDomain) (PrintValue, bool, bool, error) {
	normalized, adjusted, reason, err := n.normalizeValueForDomain(val, domain)
	if err != nil || reason != "" {
		return PrintValue{}, false, false, err
	}
	return normalized, adjusted, true, nil
}

// matchExactOption 在未受约束候选中查找与请求Option精确匹配的下标，未命中返回负一
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射
// 返回: int 命中候选下标，未命中为负一, error 预算或取消错误
func (n *printNormalizer) matchExactOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue) (int, error) {
	reqKey := printCanonicalKey(reqOpt.Name)
	hasNamedCandidate := false
	if reqOpt.Name != (xml.Name{}) {
		for _, cand := range candidates {
			if printCanonicalKey(cand.Name) == reqKey {
				hasNamedCandidate = true
				break
			}
		}
	}
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return -1, err
		}
		sameName := reqOpt.Name != (xml.Name{}) && printCanonicalKey(cand.Name) == reqKey
		if hasNamedCandidate && !sameName {
			continue
		}
		if !sameName && printScoredCount(reqOpt.Children) == 0 {
			continue
		}
		matched, err := n.matchScoredExact(reqOpt.Children, cand.Children, sameName, paramValues)
		if err != nil {
			return -1, err
		}
		if matched {
			return index, nil
		}
	}
	return -1, nil
}

// matchScoredExact 检查请求Option与候选Option的ScoredProperty是否精确匹配
// 入参: requested 请求子元素, supported 候选子元素, subset 是否允许省略候选已知描述, paramValues 票据参数初值映射
// 返回: bool 是否精确匹配, error 预算或取消错误
func (n *printNormalizer) matchScoredExact(requested, supported []PrintSetting, subset bool, paramValues map[xml.Name]*PrintValue) (bool, error) {
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
		if err := n.step(); err != nil {
			return false, err
		}
		cand, exists := index[printCanonicalKey(setting.Name)]
		if !exists {
			return false, nil
		}
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if capRef != (xml.Name{}) {
			if reqRef != (xml.Name{}) {
				if printCanonicalKey(reqRef) != printCanonicalKey(capRef) {
					return false, nil
				}
			} else {
				domain := n.domains[printCanonicalKey(capRef)]
				if domain == nil {
					return false, nil
				}
				if _, err := domain.value(reqVal, n.options); err != nil {
					if errors.Is(err, ErrInvalid) {
						return false, nil
					}
					return false, err
				}
			}
		} else {
			if reqRef != (xml.Name{}) {
				reqVal = paramValues[printCanonicalKey(reqRef)]
				if reqVal == nil {
					if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
						reqVal = &domain.defaultValue
					}
				}
			}
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil || !same {
				return same, err
			}
		}
		if same, err := n.matchScoredExact(setting.Children, cand.Children, subset, paramValues); err != nil || !same {
			return same, err
		}
	}
	return true, nil
}

// bestOption 按ScoredProperty匹配度评分查找最接近的未受约束候选下标，无匹配时返回负一
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射
// 返回: int 最佳候选下标，无匹配为负一, error 预算或取消错误
func (n *printNormalizer) bestOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue) (int, error) {
	if printScoredCount(reqOpt.Children) == 0 {
		return -1, nil
	}
	bestIndex := -1
	bestScore := 0.0
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return -1, err
		}
		score, err := n.scoreScored(reqOpt.Children, cand.Children, paramValues)
		if err != nil {
			return -1, err
		}
		if score > 0 && reqOpt.Name != (xml.Name{}) && printCanonicalKey(reqOpt.Name) == printCanonicalKey(cand.Name) {
			score += 0.5
		}
		if score > bestScore || score > 0 && score == bestScore && cand.Default && bestIndex >= 0 && !candidates[bestIndex].Default {
			bestScore = score
			bestIndex = index
		}
	}
	return bestIndex, nil
}

// scoreScored 递归计算两组ScoredProperty的相似度评分，精确值、数值接近度与参数域匹配分别计分
// 入参: requested 请求子元素, supported 候选子元素, paramValues 票据参数初值映射
// 返回: float64 相似度总分, error 预算或取消错误
func (n *printNormalizer) scoreScored(requested, supported []PrintSetting, paramValues map[xml.Name]*PrintValue) (float64, error) {
	index := make(map[xml.Name]PrintSetting)
	for _, setting := range supported {
		if setting.Kind == PrintSettingScoredProperty {
			index[printCanonicalKey(setting.Name)] = setting
		}
	}
	total := 0.0
	for _, setting := range requested {
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := n.step(); err != nil {
			return 0, err
		}
		cand, exists := index[printCanonicalKey(setting.Name)]
		if !exists {
			continue
		}
		total += 1.0
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if reqRef != (xml.Name{}) {
			if capRef != (xml.Name{}) && printCanonicalKey(reqRef) == printCanonicalKey(capRef) {
				total += 100.0
			} else if v := paramValues[printCanonicalKey(reqRef)]; v != nil {
				reqVal = v
			} else if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
				reqVal = &domain.defaultValue
			}
		}
		if capRef != (xml.Name{}) {
			if reqVal != nil {
				if domain := n.domains[printCanonicalKey(capRef)]; domain != nil {
					if _, err := domain.value(reqVal, n.options); err == nil {
						total += 100.0
					} else if !errors.Is(err, ErrInvalid) {
						return 0, err
					} else {
						capVal = &domain.defaultValue
					}
				}
			}
		}
		if reqVal != nil && capVal != nil {
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil {
				return 0, err
			}
			if same {
				total += 100.0
			} else if proximity, ok, err := n.numericProximity(reqVal, capVal); err != nil {
				return 0, err
			} else if ok {
				total += proximity
			}
		}
		nested, err := n.scoreScored(setting.Children, cand.Children, paramValues)
		if err != nil {
			return 0, err
		}
		total += nested
	}
	return total, nil
}

// valuesEqual 按基本类型精确比较两个PrintValue是否等价
// 入参: requested 请求值, supported 候选值
// 返回: bool 是否等值, error 预算或取消错误
func (n *printNormalizer) valuesEqual(requested, supported *PrintValue) (bool, error) {
	if err := n.step(); err != nil {
		return false, err
	}
	return printValuesEqual(requested, supported, n.options, true)
}

// numericProximity 计算两个数值PrintValue的接近度加分，越接近分值越高
// 入参: requested 请求值, supported 候选值
// 返回: float64 接近度分值, bool 是否为可比较数值, error 算术预算或取消错误
func (n *printNormalizer) numericProximity(requested, supported *PrintValue) (float64, bool, error) {
	if requested == nil || supported == nil {
		return 0, false, nil
	}
	if (requested.Type.Local != "integer" && requested.Type.Local != "decimal") || (supported.Type.Local != "integer" && supported.Type.Local != "decimal") {
		return 0, false, nil
	}
	left, right := strings.Trim(requested.Text, " \t\r\n"), strings.Trim(supported.Text, " \t\r\n")
	if left == "" || right == "" {
		return 0, false, nil
	}
	a, err := printParameterNumber(left, n.options)
	if err != nil {
		if errors.Is(err, ErrInvalid) {
			return 0, false, nil
		}
		return 0, false, err
	}
	b, err := printParameterNumber(right, n.options)
	if err != nil {
		if errors.Is(err, ErrInvalid) {
			return 0, false, nil
		}
		return 0, false, err
	}
	fa, _ := a.Float64()
	fb, _ := b.Float64()
	if math.IsNaN(fa) || math.IsInf(fa, 0) || math.IsNaN(fb) || math.IsInf(fb, 0) {
		return 0, false, nil
	}
	diff := math.Abs(fa - fb)
	scale := max(math.Abs(fa), math.Abs(fb), 1.0)
	return 50.0 / (1.0 + diff/scale), true, nil
}

// normalizeParameters 按设备ParameterDef校验、补全、裁剪与量化票据中的ParameterInit集合
// 入参: capElements 能力根元素列表, paramInits 票据已有ParameterInit索引, referenced 选定Option引用的参数集合
// 返回: []PrintSetting 规范化后的ParameterInit列表, error 预算或取消错误
func (n *printNormalizer) normalizeParameters(capElements []PrintSetting, paramInits map[xml.Name]PrintSetting, referenced map[xml.Name]bool) ([]PrintSetting, error) {
	var result []PrintSetting
	for _, element := range capElements {
		if element.Kind != PrintSettingParameterDef {
			continue
		}
		if err := checkContext(n.options.context); err != nil {
			return nil, err
		}
		if n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(element.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(element.Name)
		domain := n.domains[key]
		if domain == nil {
			continue
		}
		existing, present := paramInits[key]
		if !present {
			if domain.mandatory == "Unconditional" || referenced[key] {
				defaultCopy := domain.defaultValue
				result = append(result, PrintSetting{
					Kind:     PrintSettingParameterInit,
					Name:     element.Name,
					Children: []PrintSetting{{Kind: PrintSettingValue, Value: &defaultCopy}},
				})
				n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("missing print ParameterInit %s defaulted", element.Name.Local))
			}
			continue
		}
		normalized, err := n.normalizeParameterInit(existing, domain)
		if err != nil {
			return nil, err
		}
		result = append(result, normalized)
	}
	return result, nil
}

// normalizeParameterInit 校验单个ParameterInit，对越界数值裁剪量化、对越界字符串截断或回退默认值
// 入参: existing 票据已有ParameterInit, domain 对应参数域定义
// 返回: PrintSetting 规范化后的ParameterInit, error 算术预算或取消错误
func (n *printNormalizer) normalizeParameterInit(existing PrintSetting, domain *printParameterDomain) (PrintSetting, error) {
	fallback := func(reason string) PrintSetting {
		defaultCopy := domain.defaultValue
		n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s %s", existing.Name.Local, reason))
		return PrintSetting{
			Kind:     PrintSettingParameterInit,
			Name:     existing.Name,
			Children: []PrintSetting{{Kind: PrintSettingValue, Value: &defaultCopy}},
		}
	}
	if len(existing.Children) != 1 || existing.Children[0].Value == nil {
		return fallback("reset to default"), nil
	}
	normalized, adjusted, reason, err := n.normalizeValueForDomain(*existing.Children[0].Value, domain)
	if err != nil {
		return PrintSetting{}, err
	}
	if reason != "" {
		return fallback(reason), nil
	}
	if adjusted {
		if domain.kind.Local == "string" {
			n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s truncated to MaxLength", existing.Name.Local))
		} else {
			n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s clamped or quantized to %s", existing.Name.Local, normalized.Text))
		}
	}
	return PrintSetting{Kind: PrintSettingParameterInit, Name: existing.Name, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &normalized}}}, nil
}

// printFormatDecimalRat 将有限十进制有理数精确格式化为XML Schema十进制词法字符串
// 入参: value 精确有理数, maxDigits 最大允许小数位数上限
// 返回: string 无多余尾随零的十进制字符串
func printFormatDecimalRat(value *big.Rat, maxDigits int) string {
	if value.IsInt() {
		return value.Num().String()
	}
	denom := new(big.Int).Set(value.Denom())
	two, five, zero := big.NewInt(2), big.NewInt(5), big.NewInt(0)
	rem := new(big.Int)
	c2, c5 := 0, 0
	for {
		q, _ := new(big.Int).QuoRem(denom, two, rem)
		if rem.Cmp(zero) != 0 {
			break
		}
		denom = q
		c2++
	}
	for {
		q, _ := new(big.Int).QuoRem(denom, five, rem)
		if rem.Cmp(zero) != 0 {
			break
		}
		denom = q
		c5++
	}
	prec := max(c2, c5)
	if denom.Cmp(big.NewInt(1)) != 0 || prec > maxDigits {
		prec = min(maxDigits, 32)
	}
	text := value.FloatString(prec)
	if strings.Contains(text, ".") {
		text = strings.TrimRight(text, "0")
		text = strings.TrimRight(text, ".")
	}
	return text
}

// printTruncateRunes 按Unicode码点数量截断字符串至指定上限
// 入参: text 原字符串, limit 最大Unicode码点数
// 返回: string 截断后的字符串
func printTruncateRunes(text string, limit int) string {
	if limit <= 0 {
		return ""
	}
	count := 0
	for index := range text {
		if count == limit {
			return text[:index]
		}
		count++
	}
	return text
}

// printCollectParameterRefs 递归收集设置树中全部ParameterRef的规范化名称
// 入参: settings 设置树元素列表, target 输出引用集合
func printCollectParameterRefs(settings []PrintSetting, target map[xml.Name]bool) {
	for _, setting := range settings {
		if setting.Kind == PrintSettingParameterRef {
			target[printCanonicalKey(setting.Name)] = true
			continue
		}
		printCollectParameterRefs(setting.Children, target)
	}
}

// printTicketOptionFromCapability 将能力或候选Option深拷贝为不含能力专属元数据的票据Option
// 入参: option 源Option节点
// 返回: PrintSetting 独立票据Option节点
func printTicketOptionFromCapability(option PrintSetting) PrintSetting {
	result := PrintSetting{Kind: option.Kind, Name: option.Name}
	if option.Value != nil {
		val := *option.Value
		result.Value = &val
	}
	for _, child := range option.Children {
		if child.Kind == PrintSettingProperty && (printFrameworkSpace(child.Name.Space) && (child.Name.Local == "SelectionType" || child.Name.Local == "IdentityOption") || printPublicKeywordSpace(child.Name.Space) && (child.Name.Local == "DisplayName" || child.Name.Local == "DisplayUI") || printSettingHasImageableAreaType(child)) {
			continue
		}
		result.Children = append(result.Children, printTicketOptionFromCapability(child))
	}
	return result
}

// printSettingHasImageableAreaType 检查Property节点或其子节点是否包含psf2:ImageableAreaType值
// 入参: setting 待检查设置节点
// 返回: bool 是否含PSF2可打印区域类型值
func printSettingHasImageableAreaType(setting PrintSetting) bool {
	if setting.Kind == PrintSettingValue && setting.Value != nil && setting.Value.Type == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
		return true
	}
	for _, child := range setting.Children {
		if printSettingHasImageableAreaType(child) {
			return true
		}
	}
	return false
}

// printCloneSetting 深拷贝单个PrintSetting及其全部子元素和值指针
// 入参: setting 源设置节点
// 返回: PrintSetting 独立副本
func printCloneSetting(setting PrintSetting) PrintSetting {
	result := setting
	if setting.Value != nil {
		val := *setting.Value
		result.Value = &val
	}
	if len(setting.Children) > 0 {
		result.Children = make([]PrintSetting, len(setting.Children))
		for index, child := range setting.Children {
			result.Children[index] = printCloneSetting(child)
		}
	}
	return result
}

// printCloneSettings 深拷贝PrintSettings结构及其全部节点树与PDC变更标识
// 入参: src 源打印设置
// 返回: *PrintSettings 独立深拷贝，源为nil时返回nil
func printCloneSettings(src *PrintSettings) *PrintSettings {
	if src == nil {
		return nil
	}
	dst := &PrintSettings{Version: src.Version, CapabilitiesChangeID: src.CapabilitiesChangeID}
	if len(src.Elements) != 0 {
		dst.Elements = make([]PrintSetting, len(src.Elements))
		for index, element := range src.Elements {
			dst.Elements[index] = printCloneSetting(element)
		}
	}
	return dst
}

// BuildPrintDeviceCapabilities 按声明式能力规格构造合规的Windows V4 PSF2 PrintDeviceCapabilities文档
// 入参: spec 设备能力规格
// 返回: *PrintSettings 可直接通过EncodePrintDeviceCapabilities与ParsePrintDeviceCapabilities校验的PDC结构, error 规格非法错误
func BuildPrintDeviceCapabilities(spec PrintCapabilitiesSpec) (*PrintSettings, error) {
	elements, _, err := buildPrintCapabilitiesElements(spec, true)
	if err != nil {
		return nil, err
	}
	changeID := spec.CapabilitiesChangeID
	if changeID != "" && (strings.TrimSpace(changeID) == "" || !xmlTextValid(changeID)) {
		return nil, fmt.Errorf("%w: invalid CapabilitiesChangeID", ErrInvalid)
	}
	configuration, err := printSettingsOptions(context.Background(), nil)
	if err != nil {
		return nil, err
	}
	if changeID == "" {
		probeRoot, err := printDocumentRootWithChangeID(2, "", elements, configuration, printDocumentDeviceCapabilities)
		if err != nil {
			return nil, err
		}
		var buf bytes.Buffer
		if _, err := writePrintSettingsMarkup(&buf, probeRoot, configuration); err != nil {
			return nil, err
		}
		sum := sha256.Sum256(buf.Bytes())
		changeID = fmt.Sprintf("{%08X-%04X-%04X-%04X-%012X}", sum[0:4], sum[4:6], sum[6:8], sum[8:10], sum[10:16])
	}
	root, err := printDocumentRootWithChangeID(2, changeID, elements, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return nil, err
	}
	return parsePrintDocumentMode(root, configuration, printDocumentDeviceCapabilities)
}

// BuildPrintCapabilities 按声明式能力规格构造合规的PSF1 PrintCapabilities文档
// 入参: spec 设备能力规格
// 返回: *PrintCapabilities 可直接通过EncodePrintCapabilities与ParsePrintCapabilities校验的能力结构, error 规格非法错误
func BuildPrintCapabilities(spec PrintCapabilitiesSpec) (*PrintCapabilities, error) {
	elements, imageableProp, err := buildPrintCapabilitiesElements(spec, false)
	if err != nil {
		return nil, err
	}
	if imageableProp != nil {
		elements = append(elements, *imageableProp)
	}
	configuration, err := printSettingsOptions(context.Background(), nil)
	if err != nil {
		return nil, err
	}
	root, err := printDocumentRoot(1, elements, configuration, true)
	if err != nil {
		return nil, err
	}
	parsed, err := parsePrintDocument(root, configuration, true)
	if err != nil {
		return nil, err
	}
	return &PrintCapabilities{Version: parsed.Version, Elements: parsed.Elements}, nil
}

// buildPrintCapabilitiesElements 根据PrintCapabilitiesSpec构造PSF1或PSF2能力根元素与默认纸型可打印区属性
// 入参: spec 设备能力规格, isPDC 是否生成PSF2 PDC元素
// 返回: []PrintSetting 能力根元素列表, *PrintSetting 可选PSF1 PageImageableSize属性, error 规格校验错误
func buildPrintCapabilitiesElements(spec PrintCapabilitiesSpec, isPDC bool) ([]PrintSetting, *PrintSetting, error) {
	var elements []PrintSetting
	var params []PrintSetting
	paramSeen := make(map[xml.Name]bool)
	addParam := func(def PrintSetting) {
		key := printCanonicalKey(def.Name)
		if !paramSeen[key] {
			paramSeen[key] = true
			params = append(params, def)
		}
	}
	var defaultImageable *PrintSetting
	if len(spec.MediaSizes) > 0 || spec.CustomMedia != nil {
		mediaOptions := make([]PrintSetting, 0, len(spec.MediaSizes)+1)
		mediaSeen := make(map[xml.Name]bool)
		defaultIdx := -1
		var defaultW, defaultH int64
		var defaultMargins [4]int64
		for _, item := range spec.MediaSizes {
			optName := item.Name
			w, h := item.WidthMicrons, item.HeightMicrons
			if item.StandardName != "" {
				dims, ok := printMediaSizes[item.StandardName]
				if !ok {
					return nil, nil, fmt.Errorf("%w: unknown standard media %s", ErrInvalid, item.StandardName)
				}
				if optName == (xml.Name{}) {
					optName = xml.Name{Space: printKeywordsNS, Local: item.StandardName}
				}
				if w == 0 {
					w = int64(dims[0])
				}
				if h == 0 {
					h = int64(dims[1])
				}
			}
			if optName.Space == "" || !xmlNCName(optName.Local) || w <= 0 || h <= 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintMediaSpec", ErrInvalid)
			}
			if item.Margins[0] < 0 || item.Margins[1] < 0 || item.Margins[2] < 0 || item.Margins[3] < 0 || item.Margins[0] >= w || item.Margins[2] >= w-item.Margins[0] || item.Margins[1] >= h || item.Margins[3] >= h-item.Margins[1] {
				return nil, nil, fmt.Errorf("%w: invalid media margins for %s", ErrInvalid, optName.Local)
			}
			key := printCanonicalKey(optName)
			if mediaSeen[key] {
				return nil, nil, fmt.Errorf("%w: duplicate media option %s", ErrInvalid, optName.Local)
			}
			mediaSeen[key] = true
			optChildren := []PrintSetting{
				printBuildIntScored("MediaSizeWidth", w),
				printBuildIntScored("MediaSizeHeight", h),
			}
			extentW := w - item.Margins[0] - item.Margins[2]
			extentH := h - item.Margins[1] - item.Margins[3]
			if isPDC {
				optChildren = append(optChildren, printBuildPortraitImageableProperty(item.Margins[0], item.Margins[1], extentW, extentH))
			}
			opt := PrintSetting{Kind: PrintSettingOption, Name: optName, Children: optChildren, Constraint: item.Constrained}
			if item.Default {
				if defaultIdx >= 0 {
					return nil, nil, fmt.Errorf("%w: multiple default media options", ErrInvalid)
				}
				if item.Constrained != PrintConstraintUnknown && item.Constrained != PrintConstraintNone {
					return nil, nil, fmt.Errorf("%w: constrained media option cannot be default", ErrInvalid)
				}
				defaultIdx = len(mediaOptions)
				defaultW, defaultH, defaultMargins = w, h, item.Margins
			} else if defaultIdx < 0 && (item.Constrained == PrintConstraintUnknown || item.Constrained == PrintConstraintNone) && defaultW == 0 {
				defaultW, defaultH, defaultMargins = w, h, item.Margins
			}
			mediaOptions = append(mediaOptions, opt)
		}
		if spec.CustomMedia != nil {
			cm := spec.CustomMedia
			step := cm.StepMicrons
			if step == 0 {
				step = 1
			}
			defW, defH := cm.DefaultWidthMicrons, cm.DefaultHeightMicrons
			if defW == 0 {
				defW = cm.MinWidthMicrons
			}
			if defH == 0 {
				defH = cm.MinHeightMicrons
			}
			if cm.MinWidthMicrons <= 0 || cm.MinWidthMicrons > cm.MaxWidthMicrons || cm.MinHeightMicrons <= 0 || cm.MinHeightMicrons > cm.MaxHeightMicrons || step <= 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintCustomMediaSpec range", ErrInvalid)
			}
			if cm.Margins[0] < 0 || cm.Margins[1] < 0 || cm.Margins[2] < 0 || cm.Margins[3] < 0 || cm.Margins[0] >= defW || cm.Margins[2] >= defW-cm.Margins[0] || cm.Margins[1] >= defH || cm.Margins[3] >= defH-cm.Margins[1] {
				return nil, nil, fmt.Errorf("%w: invalid custom media margins", ErrInvalid)
			}
			customChildren := []PrintSetting{
				printBuildRefScored("MediaSizeWidth", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeWidth"}),
				printBuildRefScored("MediaSizeHeight", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}),
			}
			if isPDC {
				customChildren = append(customChildren, printBuildPortraitImageableProperty(cm.Margins[0], cm.Margins[1], defW-cm.Margins[0]-cm.Margins[2], defH-cm.Margins[1]-cm.Margins[3]))
			}
			mediaOptions = append(mediaOptions, PrintSetting{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printKeywordsNS, Local: "CustomMediaSize"},
				Children: customChildren,
			})
			if defaultW == 0 {
				defaultW, defaultH, defaultMargins = defW, defH, cm.Margins
			}
			addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeWidth"}, "microns", "Conditional", cm.MinWidthMicrons, cm.MaxWidthMicrons, step, defW))
			addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}, "microns", "Conditional", cm.MinHeightMicrons, cm.MaxHeightMicrons, step, defH))
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageMediaSize"}, mediaOptions, defaultIdx, isPDC, nil))
		if !isPDC && defaultW > 0 && defaultH > 0 {
			prop := printBuildPageImageableSizeProperty(defaultW, defaultH, defaultMargins[0], defaultMargins[1], defaultW-defaultMargins[0]-defaultMargins[2], defaultH-defaultMargins[1]-defaultMargins[3])
			defaultImageable = &prop
		}
	}
	if len(spec.Resolutions) > 0 {
		resOptions := make([]PrintSetting, 0, len(spec.Resolutions))
		resSeen := make(map[xml.Name]bool)
		defaultIdx := -1
		for _, item := range spec.Resolutions {
			if item.X <= 0 || item.Y <= 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintResolutionSpec", ErrInvalid)
			}
			optName := item.Name
			if optName == (xml.Name{}) {
				local := fmt.Sprintf("Res%dx%d", item.X, item.Y)
				if item.X == item.Y {
					local = fmt.Sprintf("Res%d", item.X)
				}
				optName = xml.Name{Space: printBuilderNS, Local: local}
			}
			if optName.Space == "" || !xmlNCName(optName.Local) {
				return nil, nil, fmt.Errorf("%w: invalid resolution option name", ErrInvalid)
			}
			key := printCanonicalKey(optName)
			if resSeen[key] {
				return nil, nil, fmt.Errorf("%w: duplicate resolution option %s", ErrInvalid, optName.Local)
			}
			resSeen[key] = true
			if item.Default {
				if defaultIdx >= 0 {
					return nil, nil, fmt.Errorf("%w: multiple default resolution options", ErrInvalid)
				}
				if item.Constrained != PrintConstraintUnknown && item.Constrained != PrintConstraintNone {
					return nil, nil, fmt.Errorf("%w: constrained resolution option cannot be default", ErrInvalid)
				}
				defaultIdx = len(resOptions)
			}
			resOptions = append(resOptions, PrintSetting{
				Kind:       PrintSettingOption,
				Name:       optName,
				Constraint: item.Constrained,
				Children: []PrintSetting{
					printBuildIntScored("ResolutionX", int64(item.X)),
					printBuildIntScored("ResolutionY", int64(item.Y)),
				},
			})
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageResolution"}, resOptions, defaultIdx, isPDC, nil))
	}
	if len(spec.Orientations) > 0 {
		orientOpts, defIdx, err := printBuildKeywordOptions(spec.Orientations, spec.DefaultOrientation, []string{"Portrait", "Landscape", "ReversePortrait", "ReverseLandscape"})
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOrientation"}, orientOpts, defIdx, isPDC, nil))
	}
	if len(spec.Scalings) > 0 {
		allowedScalings := []string{"None", "Custom", "CustomSquare", "FitApplicationMediaSizeToPageImageableSize", "FitApplicationContentSizeToPageImageableSize", "FitApplicationBleedSizeToPageImageableSize", "FitApplicationMediaSizeToPageMediaSize"}
		scaleOpts := make([]PrintSetting, 0, len(spec.Scalings))
		seen := make(map[string]bool)
		defIdx := -1
		needAlignment := false
		for _, name := range spec.Scalings {
			if !slices.Contains(allowedScalings, name) || seen[name] {
				return nil, nil, fmt.Errorf("%w: invalid or duplicate scaling option %s", ErrInvalid, name)
			}
			seen[name] = true
			if name != "None" {
				needAlignment = true
			}
			var children []PrintSetting
			switch name {
			case "Custom":
				children = []PrintSetting{
					printBuildRefScored("ScaleWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleWidth"}),
					printBuildRefScored("ScaleHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleHeight"}),
					printBuildRefScored("OffsetWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}),
					printBuildRefScored("OffsetHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}),
				}
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleWidth"}, "percent", "Conditional", 1, 1000, 1, 100))
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleHeight"}, "percent", "Conditional", 1, 1000, 1, 100))
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
			case "CustomSquare":
				children = []PrintSetting{
					printBuildRefScored("Scale", xml.Name{Space: printKeywordsNS, Local: "PageScalingScale"}),
					printBuildRefScored("OffsetWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}),
					printBuildRefScored("OffsetHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}),
				}
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingScale"}, "percent", "Conditional", 1, 1000, 1, 100))
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
				addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
			}
			if spec.DefaultScaling != "" && spec.DefaultScaling == name {
				defIdx = len(scaleOpts)
			}
			scaleOpts = append(scaleOpts, PrintSetting{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: name}, Children: children})
		}
		if spec.DefaultScaling != "" && defIdx < 0 {
			return nil, nil, fmt.Errorf("%w: default scaling %s not in Scalings", ErrInvalid, spec.DefaultScaling)
		}
		var subFeatures []PrintSetting
		if needAlignment {
			alignNames := []string{"Center", "TopLeft", "TopCenter", "TopRight", "CenterLeft", "CenterRight", "BottomLeft", "BottomCenter", "BottomRight"}
			alignOpts, alignDef, _ := printBuildKeywordOptions(alignNames, "Center", alignNames)
			subFeatures = append(subFeatures, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "ScaleOffsetAlignment"}, alignOpts, alignDef, isPDC, nil))
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageScaling"}, scaleOpts, defIdx, isPDC, subFeatures))
	}
	if len(spec.NUpCounts) > 0 {
		nupOpts := make([]PrintSetting, 0, len(spec.NUpCounts))
		seen := make(map[int]bool)
		defIdx := -1
		for _, count := range spec.NUpCounts {
			if count < 1 || seen[count] {
				return nil, nil, fmt.Errorf("%w: invalid or duplicate NUp count %d", ErrInvalid, count)
			}
			seen[count] = true
			if spec.DefaultNUp > 0 && spec.DefaultNUp == count {
				defIdx = len(nupOpts)
			}
			nupOpts = append(nupOpts, PrintSetting{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printBuilderNS, Local: fmt.Sprintf("PagesPerSheet%d", count)},
				Children: []PrintSetting{printBuildIntScored("PagesPerSheet", int64(count))},
			})
		}
		if spec.DefaultNUp > 0 && defIdx < 0 {
			return nil, nil, fmt.Errorf("%w: default NUp %d not in NUpCounts", ErrInvalid, spec.DefaultNUp)
		}
		dirNames := []string{"RightBottom", "BottomRight", "LeftBottom", "BottomLeft", "RightTop", "TopRight", "LeftTop", "TopLeft"}
		dirOpts, dirDef, _ := printBuildKeywordOptions(dirNames, "RightBottom", dirNames)
		sub := []PrintSetting{printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PresentationDirection"}, dirOpts, dirDef, isPDC, nil)}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "DocumentNUp"}, nupOpts, defIdx, isPDC, sub))
	}
	if len(spec.DuplexModes) > 0 {
		duplexNames := make([]string, 0, len(spec.DuplexModes))
		defaultDuplexName := ""
		for _, mode := range spec.DuplexModes {
			switch mode {
			case PrintSimplex, PrintDuplexLongEdge, PrintDuplexShortEdge:
				duplexNames = append(duplexNames, mode.String())
			default:
				return nil, nil, fmt.Errorf("%w: invalid duplex mode %v", ErrInvalid, mode)
			}
		}
		if spec.DefaultDuplex != PrintSimplex || slices.Contains(spec.DuplexModes, PrintSimplex) {
			if slices.Contains(spec.DuplexModes, spec.DefaultDuplex) {
				defaultDuplexName = spec.DefaultDuplex.String()
			} else if spec.DefaultDuplex != PrintSimplex {
				return nil, nil, fmt.Errorf("%w: default duplex not in DuplexModes", ErrInvalid)
			}
		}
		duplexOpts, defIdx, err := printBuildKeywordOptions(duplexNames, defaultDuplexName, []string{"OneSided", "TwoSidedLongEdge", "TwoSidedShortEdge"})
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "DocumentDuplex"}, duplexOpts, defIdx, isPDC, nil))
	}
	if spec.Borderless {
		defName := "None"
		if spec.DefaultBorderless {
			defName = "Borderless"
		}
		borderOpts, defIdx, _ := printBuildKeywordOptions([]string{"None", "Borderless"}, defName, []string{"None", "Borderless"})
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageBorderless"}, borderOpts, defIdx, isPDC, nil))
	}
	if len(spec.ColorModes) > 0 {
		colorNames := make([]string, 0, len(spec.ColorModes))
		modeToKeyword := func(mode PrintColorMode) (string, error) {
			switch mode {
			case PrintColorPreserve:
				return "Color", nil
			case PrintColorGrayscale:
				return "Grayscale", nil
			case PrintColorMonochrome:
				return "Monochrome", nil
			default:
				return "", fmt.Errorf("%w: unsupported color mode %v", ErrInvalid, mode)
			}
		}
		for _, mode := range spec.ColorModes {
			kw, err := modeToKeyword(mode)
			if err != nil {
				return nil, nil, err
			}
			colorNames = append(colorNames, kw)
		}
		defColor := ""
		if spec.DefaultColorMode != PrintColorOriginal {
			var err error
			defColor, err = modeToKeyword(spec.DefaultColorMode)
			if err != nil {
				return nil, nil, err
			}
		}
		colorOpts, defIdx, err := printBuildKeywordOptions(colorNames, defColor, []string{"Color", "Grayscale", "Monochrome"})
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOutputColor"}, colorOpts, defIdx, isPDC, nil))
	}
	if len(spec.OutputQualities) > 0 {
		qualOpts, defIdx, err := printBuildKeywordOptions(spec.OutputQualities, spec.DefaultOutputQuality, []string{"Automatic", "Draft", "Fax", "High", "Normal", "Photographic", "Text"})
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOutputQuality"}, qualOpts, defIdx, isPDC, nil))
	}
	if spec.Watermark {
		wmOpts := []PrintSetting{
			{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: "None"}},
			{
				Kind: PrintSettingOption,
				Name: xml.Name{Space: printKeywordsNS, Local: "Text"},
				Children: []PrintSetting{
					printBuildRefScored("OriginWidth", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginWidth"}),
					printBuildRefScored("OriginHeight", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginHeight"}),
					printBuildRefScored("Transparency", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTransparency"}),
					printBuildRefScored("Angle", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextAngle"}),
					printBuildRefScored("FontColor", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextColor"}),
					printBuildRefScored("FontSize", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextFontSize"}),
					printBuildRefScored("Text", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextText"}),
				},
			},
		}
		layerOpts, layerDef, _ := printBuildKeywordOptions([]string{"Overlay", "Underlay"}, "Overlay", []string{"Overlay", "Underlay"})
		sub := []PrintSetting{printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "Layering"}, layerOpts, layerDef, isPDC, nil)}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageWatermark"}, wmOpts, 0, isPDC, sub))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginWidth"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginHeight"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTransparency"}, "percent", "Conditional", 0, 100, 1, 50))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextAngle"}, "degrees", "Conditional", 0, 359, 1, 0))
		addParam(printBuildStringParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextColor"}, "sRGB", "Conditional", 9, 9, "#80808080"))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextFontSize"}, "points", "Conditional", 1, 1000, 1, 48))
		addParam(printBuildStringParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextText"}, "characters", "Conditional", 1, 256, "DRAFT"))
	}
	if spec.MaxCopies < 0 || spec.DefaultCopies < 0 {
		return nil, nil, fmt.Errorf("%w: negative copy limits", ErrInvalid)
	}
	if spec.MaxCopies > 0 {
		defCopies := spec.DefaultCopies
		if defCopies == 0 {
			defCopies = 1
		}
		if defCopies > spec.MaxCopies {
			return nil, nil, fmt.Errorf("%w: DefaultCopies exceeds MaxCopies", ErrInvalid)
		}
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "JobCopiesAllDocuments"}, "copies", "Unconditional", 1, int64(spec.MaxCopies), 1, int64(defCopies)))
	}
	elements = append(elements, params...)
	return elements, defaultImageable, nil
}

// printBuildKeywordOptions 校验并构造公共关键字Option列表及默认选项下标
// 入参: values 选项本地名列表, defaultValue 默认选项名，空表示首项, allowed 允许的关键字集合
// 返回: []PrintSetting Option列表, int 默认下标, error 非法或重复选项错误
func printBuildKeywordOptions(values []string, defaultValue string, allowed []string) ([]PrintSetting, int, error) {
	options := make([]PrintSetting, 0, len(values))
	seen := make(map[string]bool, len(values))
	defIdx := -1
	for _, name := range values {
		if !slices.Contains(allowed, name) || seen[name] {
			return nil, -1, fmt.Errorf("%w: invalid or duplicate option keyword %s", ErrInvalid, name)
		}
		seen[name] = true
		if defaultValue != "" && name == defaultValue {
			defIdx = len(options)
		}
		options = append(options, PrintSetting{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: name}})
	}
	if defaultValue != "" && defIdx < 0 {
		return nil, -1, fmt.Errorf("%w: default option %s not in list", ErrInvalid, defaultValue)
	}
	return options, defIdx, nil
}

// printBuildPickOneFeature 构造带SelectionType声明与默认项标记的PickOne能力Feature
// 入参: name Feature名称, options Option列表, defaultIdx 显式默认下标，负一采用首个未受约束项, isPDC 是否写出psf2:default, subFeatures 可选子Feature列表
// 返回: PrintSetting 构造完成的Feature节点
func printBuildPickOneFeature(name xml.Name, options []PrintSetting, defaultIdx int, isPDC bool, subFeatures []PrintSetting) PrintSetting {
	if defaultIdx < 0 {
		for index, opt := range options {
			if opt.Constraint == PrintConstraintUnknown || opt.Constraint == PrintConstraintNone {
				defaultIdx = index
				break
			}
		}
	}
	ordered := make([]PrintSetting, 0, len(options))
	if !isPDC && defaultIdx > 0 && defaultIdx < len(options) {
		ordered = append(ordered, options[defaultIdx])
		for index, opt := range options {
			if index != defaultIdx {
				ordered = append(ordered, opt)
			}
		}
	} else {
		ordered = append(ordered, options...)
	}
	for index := range ordered {
		if isPDC {
			if index == defaultIdx {
				ordered[index].HasDefault = true
				ordered[index].Default = true
			}
		} else {
			ordered[index].HasDefault = false
			ordered[index].Default = false
		}
	}
	children := make([]PrintSetting, 0, 1+len(ordered)+len(subFeatures))
	children = append(children, PrintSetting{
		Kind: PrintSettingProperty,
		Name: xml.Name{Space: printFrameworkNS, Local: "SelectionType"},
		Children: []PrintSetting{{
			Kind:  PrintSettingValue,
			Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "psk:PickOne", QName: xml.Name{Space: printKeywordsNS, Local: "PickOne"}},
		}},
	})
	children = append(children, ordered...)
	children = append(children, subFeatures...)
	return PrintSetting{Kind: PrintSettingFeature, Name: name, Children: children}
}

// printBuildIntScored 构造携带整数值的公共ScoredProperty节点
// 入参: local 公共关键字本地名称, value 整数值
// 返回: PrintSetting ScoredProperty节点
func printBuildIntScored(local string, value int64) PrintSetting {
	return PrintSetting{
		Kind: PrintSettingScoredProperty,
		Name: xml.Name{Space: printKeywordsNS, Local: local},
		Children: []PrintSetting{{
			Kind:  PrintSettingValue,
			Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(value, 10)},
		}},
	}
}

// printBuildStringScored 构造携带字符串值的公共ScoredProperty节点
// 入参: local 公共关键字本地名称, value 字符串值
// 返回: PrintSetting ScoredProperty节点
func printBuildStringScored(local, value string) PrintSetting {
	return PrintSetting{
		Kind: PrintSettingScoredProperty,
		Name: xml.Name{Space: printKeywordsNS, Local: local},
		Children: []PrintSetting{{
			Kind:  PrintSettingValue,
			Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: value},
		}},
	}
}

// printBuildRefScored 构造引用参数的公共ScoredProperty节点
// 入参: local 公共关键字本地名称, ref 参数展开名称
// 返回: PrintSetting ScoredProperty节点
func printBuildRefScored(local string, ref xml.Name) PrintSetting {
	return PrintSetting{
		Kind:     PrintSettingScoredProperty,
		Name:     xml.Name{Space: printKeywordsNS, Local: local},
		Children: []PrintSetting{{Kind: PrintSettingParameterRef, Name: ref}},
	}
}

// printBuildIntParameterDef 构造标准整数型ParameterDef节点
// 入参: name 参数展开名称, unit 单位名称, mandatory 初始化策略关键字, minVal 最小值, maxVal 最大值, step 步进, defVal 默认值
// 返回: PrintSetting ParameterDef节点
func printBuildIntParameterDef(name xml.Name, unit, mandatory string, minVal, maxVal, step, defVal int64) PrintSetting {
	prop := func(local string, val *PrintValue) PrintSetting {
		return PrintSetting{
			Kind:     PrintSettingProperty,
			Name:     xml.Name{Space: printFrameworkNS, Local: local},
			Children: []PrintSetting{{Kind: PrintSettingValue, Value: val}},
		}
	}
	return PrintSetting{
		Kind: PrintSettingParameterDef,
		Name: name,
		Children: []PrintSetting{
			prop("DataType", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "xs:integer", QName: xml.Name{Space: printValueNS, Local: "integer"}}),
			prop("UnitType", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: unit}),
			prop("Mandatory", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "psk:" + mandatory, QName: xml.Name{Space: printKeywordsNS, Local: mandatory}}),
			prop("MinValue", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(minVal, 10)}),
			prop("MaxValue", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(maxVal, 10)}),
			prop("Multiple", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(step, 10)}),
			prop("DefaultValue", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(defVal, 10)}),
		},
	}
}

// printBuildStringParameterDef 构造标准字符串型ParameterDef节点
// 入参: name 参数展开名称, unit 单位名称, mandatory 初始化策略关键字, minLen 最小长度, maxLen 最大长度, defVal 默认字符串
// 返回: PrintSetting ParameterDef节点
func printBuildStringParameterDef(name xml.Name, unit, mandatory string, minLen, maxLen int64, defVal string) PrintSetting {
	prop := func(local string, val *PrintValue) PrintSetting {
		return PrintSetting{
			Kind:     PrintSettingProperty,
			Name:     xml.Name{Space: printFrameworkNS, Local: local},
			Children: []PrintSetting{{Kind: PrintSettingValue, Value: val}},
		}
	}
	return PrintSetting{
		Kind: PrintSettingParameterDef,
		Name: name,
		Children: []PrintSetting{
			prop("DataType", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "xs:string", QName: xml.Name{Space: printValueNS, Local: "string"}}),
			prop("UnitType", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: unit}),
			prop("Mandatory", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "psk:" + mandatory, QName: xml.Name{Space: printKeywordsNS, Local: mandatory}}),
			prop("MinLength", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(minLen, 10)}),
			prop("MaxLength", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(maxLen, 10)}),
			prop("DefaultValue", &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: defVal}),
		},
	}
}

// printBuildPortraitImageableProperty 构造PSF2纸型选项下的psk12:PortraitImageableSize属性节点
// 入参: originX 可打印原点X微米, originY 可打印原点Y微米, extentW 可打印宽微米, extentH 可打印高微米
// 返回: PrintSetting PortraitImageableSize属性节点
func printBuildPortraitImageableProperty(originX, originY, extentW, extentH int64) PrintSetting {
	return PrintSetting{
		Kind: PrintSettingProperty,
		Name: xml.Name{Space: printKeywordsV12NS, Local: "PortraitImageableSize"},
		Children: []PrintSetting{{
			Kind: PrintSettingValue,
			Value: &PrintValue{
				Type: xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"},
				Text: fmt.Sprintf("%d,%d,%d,%d", originX, originY, extentW, extentH),
			},
		}},
	}
}

// printBuildPageImageableSizeProperty 构造标准PSF1根级psk:PageImageableSize属性树
// 入参: width 纸张宽微米, height 纸张高微米, originX 可打印原点X微米, originY 可打印原点Y微米, extentW 可打印宽微米, extentH 可打印高微米
// 返回: PrintSetting 完整PageImageableSize Property节点
func printBuildPageImageableSizeProperty(width, height, originX, originY, extentW, extentH int64) PrintSetting {
	intProp := func(local string, value int64) PrintSetting {
		return PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printKeywordsNS, Local: local},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(value, 10)},
			}},
		}
	}
	return PrintSetting{
		Kind: PrintSettingProperty,
		Name: xml.Name{Space: printKeywordsNS, Local: "PageImageableSize"},
		Children: []PrintSetting{
			intProp("ImageableSizeWidth", width),
			intProp("ImageableSizeHeight", height),
			{
				Kind: PrintSettingProperty,
				Name: xml.Name{Space: printKeywordsNS, Local: "ImageableArea"},
				Children: []PrintSetting{
					intProp("OriginWidth", originX),
					intProp("OriginHeight", originY),
					intProp("ExtentWidth", extentW),
					intProp("ExtentHeight", extentH),
				},
			},
		},
	}
}

// BuildPrintTicket 按声明式票据规格构造合规的标准PrintTicket模型
// 入参: spec 打印票据参数规格
// 返回: *PrintSettings 可直接用于编码、布局、计划与规范化的打印设置, error 规格非法或冲突错误
func BuildPrintTicket(spec PrintTicketSpec) (*PrintSettings, error) {
	version := spec.Version
	if version == 0 {
		version = 1
	}
	if version != 1 && version != 2 {
		return nil, fmt.Errorf("%w: unsupported print ticket version %d", ErrUnsupported, version)
	}
	var elements []PrintSetting
	var params []PrintSetting
	addIntParam := func(local string, value int64) {
		params = append(params, PrintSetting{
			Kind: PrintSettingParameterInit,
			Name: xml.Name{Space: printKeywordsNS, Local: local},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "integer"}, Text: strconv.FormatInt(value, 10)},
			}},
		})
	}
	addStringParam := func(local, value string) {
		params = append(params, PrintSetting{
			Kind: PrintSettingParameterInit,
			Name: xml.Name{Space: printKeywordsNS, Local: local},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: value},
			}},
		})
	}
	if spec.MediaStandardName != "" && (spec.CustomWidthMicrons != 0 || spec.CustomHeightMicrons != 0) {
		return nil, fmt.Errorf("%w: standard media and custom media are mutually exclusive", ErrInvalid)
	}
	if spec.MediaStandardName != "" {
		dims, ok := printMediaSizes[spec.MediaStandardName]
		if !ok || dims[1] == 0 {
			return nil, fmt.Errorf("%w: unsupported standard media %s", ErrInvalid, spec.MediaStandardName)
		}
		elements = append(elements, PrintSetting{
			Kind: PrintSettingFeature,
			Name: xml.Name{Space: printKeywordsNS, Local: "PageMediaSize"},
			Children: []PrintSetting{{
				Kind: PrintSettingOption,
				Name: xml.Name{Space: printKeywordsNS, Local: spec.MediaStandardName},
				Children: []PrintSetting{
					printBuildIntScored("MediaSizeWidth", int64(dims[0])),
					printBuildIntScored("MediaSizeHeight", int64(dims[1])),
				},
			}},
		})
	} else if spec.CustomWidthMicrons != 0 || spec.CustomHeightMicrons != 0 {
		if spec.CustomWidthMicrons <= 0 || spec.CustomHeightMicrons <= 0 {
			return nil, fmt.Errorf("%w: invalid custom media dimensions", ErrInvalid)
		}
		elements = append(elements, PrintSetting{
			Kind: PrintSettingFeature,
			Name: xml.Name{Space: printKeywordsNS, Local: "PageMediaSize"},
			Children: []PrintSetting{{
				Kind: PrintSettingOption,
				Name: xml.Name{Space: printKeywordsNS, Local: "CustomMediaSize"},
				Children: []PrintSetting{
					printBuildRefScored("MediaSizeWidth", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeWidth"}),
					printBuildRefScored("MediaSizeHeight", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}),
				},
			}},
		})
		addIntParam("PageMediaSizeMediaSizeWidth", spec.CustomWidthMicrons)
		addIntParam("PageMediaSizeMediaSizeHeight", spec.CustomHeightMicrons)
	}
	if spec.Resolution != nil {
		if !geometryFinite(spec.Resolution.X, spec.Resolution.Y) || spec.Resolution.X <= 0 || spec.Resolution.Y <= 0 {
			return nil, fmt.Errorf("%w: invalid ticket resolution", ErrInvalid)
		}
		rx, ry := int64(math.Round(spec.Resolution.X)), int64(math.Round(spec.Resolution.Y))
		local := fmt.Sprintf("Res%dx%d", rx, ry)
		if rx == ry {
			local = fmt.Sprintf("Res%d", rx)
		}
		elements = append(elements, PrintSetting{
			Kind: PrintSettingFeature,
			Name: xml.Name{Space: printKeywordsNS, Local: "PageResolution"},
			Children: []PrintSetting{{
				Kind: PrintSettingOption,
				Name: xml.Name{Space: printBuilderNS, Local: local},
				Children: []PrintSetting{
					printBuildIntScored("ResolutionX", rx),
					printBuildIntScored("ResolutionY", ry),
				},
			}},
		})
	}
	if spec.Orientation != "" {
		if !slices.Contains([]string{"Portrait", "Landscape", "ReversePortrait", "ReverseLandscape"}, spec.Orientation) {
			return nil, fmt.Errorf("%w: invalid ticket orientation %s", ErrInvalid, spec.Orientation)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageOrientation"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Orientation}}},
		})
	}
	if spec.Borderless != nil {
		opt := "None"
		if *spec.Borderless {
			opt = "Borderless"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageBorderless"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: opt}}},
		})
	}
	if spec.MirrorImage != "" {
		if !slices.Contains([]string{"None", "MirrorImageWidth", "MirrorImageHeight"}, spec.MirrorImage) {
			return nil, fmt.Errorf("%w: invalid ticket mirror image %s", ErrInvalid, spec.MirrorImage)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageMirrorImage"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.MirrorImage}}},
		})
	}
	if spec.Scaling != "" {
		allowedScalings := []string{"None", "Custom", "CustomSquare", "FitApplicationMediaSizeToPageImageableSize", "FitApplicationContentSizeToPageImageableSize", "FitApplicationBleedSizeToPageImageableSize", "FitApplicationMediaSizeToPageMediaSize"}
		if !slices.Contains(allowedScalings, spec.Scaling) {
			return nil, fmt.Errorf("%w: invalid ticket scaling %s", ErrInvalid, spec.Scaling)
		}
		var optChildren []PrintSetting
		switch spec.Scaling {
		case "Custom":
			sw, sh := spec.ScaleWidth, spec.ScaleHeight
			if sw == 0 {
				sw = 100
			}
			if sh == 0 {
				sh = 100
			}
			if sw < 0 || sh < 0 {
				return nil, fmt.Errorf("%w: negative ticket scaling", ErrInvalid)
			}
			optChildren = []PrintSetting{
				printBuildRefScored("ScaleWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleWidth"}),
				printBuildRefScored("ScaleHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingScaleHeight"}),
				printBuildRefScored("OffsetWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}),
				printBuildRefScored("OffsetHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}),
			}
			addIntParam("PageScalingScaleWidth", int64(sw))
			addIntParam("PageScalingScaleHeight", int64(sh))
			addIntParam("PageScalingOffsetWidth", spec.OffsetWidthMicrons)
			addIntParam("PageScalingOffsetHeight", spec.OffsetHeightMicrons)
		case "CustomSquare":
			sc := spec.Scale
			if sc == 0 {
				sc = 100
			}
			if sc < 0 {
				return nil, fmt.Errorf("%w: negative ticket square scaling", ErrInvalid)
			}
			optChildren = []PrintSetting{
				printBuildRefScored("Scale", xml.Name{Space: printKeywordsNS, Local: "PageScalingScale"}),
				printBuildRefScored("OffsetWidth", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetWidth"}),
				printBuildRefScored("OffsetHeight", xml.Name{Space: printKeywordsNS, Local: "PageScalingOffsetHeight"}),
			}
			addIntParam("PageScalingScale", int64(sc))
			addIntParam("PageScalingOffsetWidth", spec.OffsetWidthMicrons)
			addIntParam("PageScalingOffsetHeight", spec.OffsetHeightMicrons)
		}
		featChildren := []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Scaling}, Children: optChildren}}
		if spec.ScaleOffsetAlignment != "" {
			if !slices.Contains([]string{"TopLeft", "TopCenter", "TopRight", "CenterLeft", "Center", "CenterRight", "BottomLeft", "BottomCenter", "BottomRight"}, spec.ScaleOffsetAlignment) {
				return nil, fmt.Errorf("%w: invalid ticket ScaleOffsetAlignment %s", ErrInvalid, spec.ScaleOffsetAlignment)
			}
			featChildren = append(featChildren, PrintSetting{
				Kind:     PrintSettingFeature,
				Name:     xml.Name{Space: printKeywordsNS, Local: "ScaleOffsetAlignment"},
				Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.ScaleOffsetAlignment}}},
			})
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageScaling"},
			Children: featChildren,
		})
	}
	if spec.OutputColor != nil {
		if err := validatePrintColor(*spec.OutputColor); err != nil {
			return nil, err
		}
		var colorLocal string
		switch spec.OutputColor.Mode {
		case PrintColorPreserve:
			colorLocal = "Color"
		case PrintColorGrayscale:
			colorLocal = "Grayscale"
		case PrintColorMonochrome:
			colorLocal = "Monochrome"
		default:
			return nil, fmt.Errorf("%w: invalid ticket output color mode", ErrInvalid)
		}
		var optChildren []PrintSetting
		if spec.OutputColor.DeviceBitsPerPixel > 0 {
			optChildren = append(optChildren, printBuildIntScored("DeviceBitsPerPixel", int64(spec.OutputColor.DeviceBitsPerPixel)))
		}
		if spec.OutputColor.DriverBitsPerPixel > 0 {
			optChildren = append(optChildren, printBuildIntScored("DriverBitsPerPixel", int64(spec.OutputColor.DriverBitsPerPixel)))
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageOutputColor"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: colorLocal}, Children: optChildren}},
		})
	}
	if spec.NegativeImage != nil {
		opt := "None"
		if *spec.NegativeImage {
			opt = "Negative"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageNegativeImage"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: opt}}},
		})
	}
	if spec.OutputQuality != "" {
		if !slices.Contains([]string{"Automatic", "Draft", "Fax", "High", "Normal", "Photographic", "Text"}, spec.OutputQuality) {
			return nil, fmt.Errorf("%w: invalid ticket output quality %s", ErrInvalid, spec.OutputQuality)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageOutputQuality"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.OutputQuality}}},
		})
	}
	if spec.PhotoPrintingIntent != "" {
		if !slices.Contains([]string{"None", "PhotoBest", "PhotoDraft", "PhotoStandard"}, spec.PhotoPrintingIntent) {
			return nil, fmt.Errorf("%w: invalid ticket photo printing intent %s", ErrInvalid, spec.PhotoPrintingIntent)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PagePhotoPrintingIntent"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PhotoPrintingIntent}}},
		})
	}
	if spec.Watermark != nil {
		wm := spec.Watermark
		if wm.Text == "" || !geometryFinite(wm.Origin.X, wm.Origin.Y, wm.FontSize, wm.Angle, wm.Transparency) || wm.FontSize <= 0 || wm.Angle < 0 || wm.Angle > 359 || wm.Transparency < 0 || wm.Transparency > 100 {
			return nil, fmt.Errorf("%w: invalid ticket watermark", ErrInvalid)
		}
		fontSizePt := int64(math.Round(wm.FontSize * 72 / 96.0))
		if fontSizePt < 1 {
			fontSizePt = 1
		}
		optChildren := []PrintSetting{
			printBuildIntScored("OriginWidth", int64(math.Round(wm.Origin.X/printMicronUnit))),
			printBuildIntScored("OriginHeight", int64(math.Round(wm.Origin.Y/printMicronUnit))),
			printBuildIntScored("Angle", int64(math.Round(wm.Angle))),
			printBuildIntScored("FontSize", fontSizePt),
			printBuildStringScored("FontColor", fmt.Sprintf("#%02X%02X%02X%02X", wm.Color.A, wm.Color.R, wm.Color.G, wm.Color.B)),
			printBuildStringScored("Text", wm.Text),
		}
		if wm.HasTransparency || wm.Transparency > 0 {
			optChildren = append(optChildren, printBuildIntScored("Transparency", int64(math.Round(wm.Transparency))))
		}
		featChildren := []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: "Text"}, Children: optChildren}}
		if wm.Layer == PrintWatermarkOverlay || wm.Layer == PrintWatermarkUnderlay {
			featChildren = append(featChildren, PrintSetting{
				Kind:     PrintSettingFeature,
				Name:     xml.Name{Space: printKeywordsNS, Local: "Layering"},
				Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: wm.Layer.String()}}},
			})
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageWatermark"},
			Children: featChildren,
		})
	}
	if spec.Copies < 0 || spec.DocumentCopies < 0 || spec.PageCopies < 0 {
		return nil, fmt.Errorf("%w: negative ticket copies", ErrInvalid)
	}
	if spec.Copies > 0 {
		addIntParam("JobCopiesAllDocuments", int64(spec.Copies))
	}
	if spec.DocumentCopies > 0 {
		addIntParam("DocumentCopiesAllPages", int64(spec.DocumentCopies))
	}
	if spec.PageCopies > 0 {
		addIntParam("PageCopies", int64(spec.PageCopies))
	}
	if spec.Collate != "" {
		if spec.Collate != "Collated" && spec.Collate != "Uncollated" {
			return nil, fmt.Errorf("%w: invalid ticket collate %s", ErrInvalid, spec.Collate)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "JobCollateAllDocuments"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Collate}}},
		})
	}
	if spec.Duplex != nil {
		if *spec.Duplex > PrintDuplexShortEdge {
			return nil, fmt.Errorf("%w: invalid ticket duplex", ErrInvalid)
		}
		var optChildren []PrintSetting
		if *spec.Duplex != PrintSimplex && spec.ManualDuplex {
			optChildren = append(optChildren, printBuildStringScored("DuplexMode", "Manual"))
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "DocumentDuplex"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Duplex.String()}, Children: optChildren}},
		})
	}
	if spec.NUp < 0 {
		return nil, fmt.Errorf("%w: negative ticket NUp", ErrInvalid)
	}
	if spec.NUp > 0 {
		featChildren := []PrintSetting{{
			Kind:     PrintSettingOption,
			Name:     xml.Name{Space: printBuilderNS, Local: fmt.Sprintf("PagesPerSheet%d", spec.NUp)},
			Children: []PrintSetting{printBuildIntScored("PagesPerSheet", int64(spec.NUp))},
		}}
		if spec.PresentationDirection != "" {
			if !slices.Contains([]string{"RightBottom", "BottomRight", "LeftBottom", "BottomLeft", "RightTop", "TopRight", "LeftTop", "TopLeft"}, spec.PresentationDirection) {
				return nil, fmt.Errorf("%w: invalid ticket presentation direction %s", ErrInvalid, spec.PresentationDirection)
			}
			featChildren = append(featChildren, PrintSetting{
				Kind:     PrintSettingFeature,
				Name:     xml.Name{Space: printKeywordsNS, Local: "PresentationDirection"},
				Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PresentationDirection}}},
			})
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "DocumentNUp"},
			Children: featChildren,
		})
	}
	if spec.PageOrder != "" {
		if spec.PageOrder != "Standard" && spec.PageOrder != "Reverse" {
			return nil, fmt.Errorf("%w: invalid ticket page order %s", ErrInvalid, spec.PageOrder)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "JobPageOrder"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PageOrder}}},
		})
	}
	if spec.PageRanges != "" {
		addStringParam("DocumentPageRanges", spec.PageRanges)
	}
	if spec.PosterSheets < 0 {
		return nil, fmt.Errorf("%w: negative ticket poster sheets", ErrInvalid)
	}
	if spec.PosterSheets > 0 {
		elements = append(elements, PrintSetting{
			Kind: PrintSettingFeature,
			Name: xml.Name{Space: printKeywordsNS, Local: "PagePoster"},
			Children: []PrintSetting{{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printBuilderNS, Local: fmt.Sprintf("Poster%d", spec.PosterSheets)},
				Children: []PrintSetting{printBuildIntScored("SheetsPerPage", int64(spec.PosterSheets))},
			}},
		})
	}
	if spec.Finishing != nil {
		if spec.Finishing.Binding > PrintBindingTrim || !geometryFinite(spec.Finishing.Gutter) || spec.Finishing.Gutter < 0 {
			return nil, fmt.Errorf("%w: invalid ticket finishing", ErrInvalid)
		}
		featName := "DocumentBinding"
		if spec.JobLevelFinishing {
			featName = "JobBindAllDocuments"
		}
		var optChildren []PrintSetting
		if spec.Finishing.Binding != PrintBindingNone && spec.Finishing.Gutter > 0 {
			optChildren = append(optChildren, printBuildIntScored("BindingGutter", int64(math.Round(spec.Finishing.Gutter/printMicronUnit))))
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: featName},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Finishing.Binding.String()}, Children: optChildren}},
		})
	}
	elements = append(elements, params...)
	configuration, err := printSettingsOptions(context.Background(), nil)
	if err != nil {
		return nil, err
	}
	candidate := &PrintSettings{Version: version, Elements: elements}
	root, err := printSettingsRoot(candidate, configuration)
	if err != nil {
		return nil, err
	}
	return parsePrintSettings(root, configuration)
}

// DerivePrintCapabilities 执行Windows V4 PDC核心派生：将PSF2 PDC转换为PSF1 PrintCapabilities，结合基准票据计算动态PageImageableSize、标注约束并输出规范化默认PrintTicket
// 入参: ctx 取消Context，nil采用Background, pdc PSF2 PrintDeviceCapabilities结构, baseTicket 可选基准PrintTicket，nil按设备默认派生, opts 资源预算选项，Scope须为Unknown
// 返回: *PrintCapabilities 派生后的PSF1能力文档, *PrintSettings 规范化后的默认PSF1票据, error 结构、能力、预算或取消错误
func DerivePrintCapabilities(ctx context.Context, pdc *PrintSettings, baseTicket *PrintSettings, opts *PrintSettingsOptions) (*PrintCapabilities, *PrintSettings, error) {
	configuration, err := printSettingsOptions(ctx, opts)
	if err != nil {
		return nil, nil, err
	}
	if pdc == nil || configuration.Scope != PrintScopeUnknown {
		return nil, nil, fmt.Errorf("%w: print capabilities derive parameters", ErrInvalid)
	}
	pdcRoot, err := printDocumentRootWithChangeID(pdc.Version, pdc.CapabilitiesChangeID, pdc.Elements, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return nil, nil, err
	}
	pdcModel, err := parsePrintDocumentMode(pdcRoot, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return nil, nil, err
	}
	effectiveTicket, _, err := NormalizePrintSettings(ctx, baseTicket, nil, pdcModel, &PrintNormalizeOptions{Settings: configuration.PrintSettingsOptions})
	if err != nil {
		return nil, nil, err
	}
	effectiveTicket.Version = 1
	printStripOptionDefaults(effectiveTicket.Elements)
	ticketRoot, err := printSettingsRoot(effectiveTicket, configuration)
	if err != nil {
		return nil, nil, err
	}
	effectiveTicket, err = parsePrintSettings(ticketRoot, configuration)
	if err != nil {
		return nil, nil, err
	}
	state := printExtractDeriveState(effectiveTicket, pdcModel, configuration)
	capsElements := make([]PrintSetting, 0, len(pdcModel.Elements)+1)
	replacedImageable := false
	for _, element := range pdcModel.Elements {
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		if element.Kind == PrintSettingProperty && printPublicKeywordSpace(element.Name.Space) && element.Name.Local == "PageImageableSize" {
			if state.hasMedia {
				capsElements = append(capsElements, printBuildPageImageableSizeProperty(state.imageableWidth, state.imageableHeight, state.originX, state.originY, state.extentW, state.extentH))
				replacedImageable = true
				continue
			}
		}
		converted, keep := printConvertSettingToV1Cap(element)
		if !keep {
			continue
		}
		if converted.Kind == PrintSettingFeature {
			printApplyDeriveConstraints(&converted, state)
		}
		capsElements = append(capsElements, converted)
	}
	if state.hasMedia && !replacedImageable {
		capsElements = append(capsElements, printBuildPageImageableSizeProperty(state.imageableWidth, state.imageableHeight, state.originX, state.originY, state.extentW, state.extentH))
	}
	capRoot, err := printDocumentRoot(1, capsElements, configuration, true)
	if err != nil {
		return nil, nil, err
	}
	capModel, err := parsePrintDocument(capRoot, configuration, true)
	if err != nil {
		return nil, nil, err
	}
	return &PrintCapabilities{Version: capModel.Version, Elements: capModel.Elements}, effectiveTicket, nil
}

// printExtractDeriveState 从规范化基准票据与PDC提取动态PageImageableSize及约束判定状态
// 入参: ticket 有效基准票据, pdc 已校验PDC模型, options 已校验配置
// 返回: printDeriveState 派生上下文状态
func printExtractDeriveState(ticket, pdc *PrintSettings, options printSettingsConfig) printDeriveState {
	var state printDeriveState
	control := newPrintLayoutSettings(ticket, options)
	orientation := "Portrait"
	if opt, _, err := control.option(ticket.Elements, "PageOrientation"); err == nil && opt != nil && printPublicKeywordSpace(opt.Name.Space) {
		orientation = opt.Name.Local
	}
	borderless := false
	if opt, _, err := control.option(ticket.Elements, "PageBorderless"); err == nil && opt != nil && printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "Borderless" {
		borderless = true
	}
	if opt, _, err := control.option(ticket.Elements, "PageMediaSize"); err == nil && opt != nil {
		var mediaW, mediaH int64
		if _, w, ok, err := control.numberExact(opt, "MediaSizeWidth"); err == nil && ok && w > 0 {
			mediaW = w
		}
		if _, h, ok, err := control.numberExact(opt, "MediaSizeHeight"); err == nil && ok && h > 0 {
			mediaH = h
		}
		if (mediaW == 0 || mediaH == 0) && printPublicKeywordSpace(opt.Name.Space) {
			if dims, exists := printMediaSizes[opt.Name.Local]; exists && dims[1] > 0 {
				mediaW, mediaH = int64(dims[0]), int64(dims[1])
			}
		}
		if mediaW > 0 && mediaH > 0 {
			ox, oy, ew, eh := int64(0), int64(0), mediaW, mediaH
			if !borderless {
				if area, found := printFindPDCPortraitImageable(pdc, opt.Name); found {
					ox, oy, ew, eh = area[0], area[1], area[2], area[3]
					if ox > mediaW {
						ox = mediaW
					}
					if oy > mediaH {
						oy = mediaH
					}
					if ew > mediaW-ox {
						ew = mediaW - ox
					}
					if eh > mediaH-oy {
						eh = mediaH - oy
					}
				}
			}
			imgW, imgH := mediaW, mediaH
			switch orientation {
			case "ReversePortrait":
				ox, oy = mediaW-ox-ew, mediaH-oy-eh
			case "Landscape":
				imgW, imgH = mediaH, mediaW
				ox, oy, ew, eh = mediaH-oy-eh, ox, eh, ew
			case "ReverseLandscape":
				imgW, imgH = mediaH, mediaW
				ox, oy, ew, eh = oy, mediaW-ox-ew, eh, ew
			}
			state.hasMedia = true
			state.imageableWidth, state.imageableHeight = imgW, imgH
			state.originX, state.originY, state.extentW, state.extentH = ox, oy, ew, eh
		}
	}
	if nup, _, err := control.nup("JobNUpAllDocumentsContiguously", int(^uint(0)>>1)); err == nil && nup > 1 {
		state.activeNUp = nup
		state.hasJobNUp = true
	}
	if nup, _, err := control.nup("DocumentNUp", int(^uint(0)>>1)); err == nil && nup > 1 {
		state.activeNUp = max(state.activeNUp, nup)
		state.hasDocNUp = true
	}
	if poster, err := control.poster(int(^uint(0) >> 1)); err == nil && poster > 1 {
		state.activePoster = poster
	}
	if fin, declared, err := control.binding("JobBindAllDocuments"); err == nil && declared {
		state.hasJobBind = true
		if fin.Binding == PrintBindingBooklet {
			state.activeBooklet = true
		}
	}
	if fin, declared, err := control.binding("DocumentBinding"); err == nil && declared {
		state.hasDocBind = true
		if fin.Binding == PrintBindingBooklet {
			state.activeBooklet = true
		}
	}
	if dup, _, err := control.duplex("JobDuplexAllDocumentsContiguously"); err == nil && dup != PrintSimplex {
		state.hasJobDuplex = true
	}
	if dup, _, err := control.duplex("DocumentDuplex"); err == nil && dup != PrintSimplex {
		state.hasDocDuplex = true
	}
	return state
}

// printFindPDCPortraitImageable 在PDC的PageMediaSize特性中查找指定纸型声明的PortraitImageableSize四元微米区域
// 入参: pdc 已校验PDC模型, optionName 纸型Option展开名称
// 返回: [4]int64 原点X、原点Y、宽、高微米值, bool 是否找到合法声明
func printFindPDCPortraitImageable(pdc *PrintSettings, optionName xml.Name) ([4]int64, bool) {
	target := printCanonicalKey(optionName)
	for _, element := range pdc.Elements {
		if element.Kind != PrintSettingFeature || !printPublicKeywordSpace(element.Name.Space) || element.Name.Local != "PageMediaSize" {
			continue
		}
		for _, opt := range element.Children {
			if opt.Kind != PrintSettingOption || printCanonicalKey(opt.Name) != target {
				continue
			}
			for _, prop := range opt.Children {
				if prop.Kind != PrintSettingProperty || len(prop.Children) != 1 || prop.Children[0].Value == nil {
					continue
				}
				val := prop.Children[0].Value
				if val.Type == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
					return printParseImageableArea(val.Text)
				}
			}
		}
	}
	return [4]int64{}, false
}

// printConvertSettingToV1Cap 将PDC节点递归转换为兼容PSF1 PrintCapabilities的节点，清除PSF2默认属性与ImageableAreaType并将默认项置前
// 入参: setting PDC节点
// 返回: PrintSetting 转换后的PSF1能力节点, bool 是否保留该节点
func printConvertSettingToV1Cap(setting PrintSetting) (PrintSetting, bool) {
	if setting.Kind == PrintSettingProperty && printSettingHasImageableAreaType(setting) {
		return PrintSetting{}, false
	}
	result := PrintSetting{
		Kind:       setting.Kind,
		Name:       setting.Name,
		Constraint: setting.Constraint,
	}
	if setting.Value != nil {
		val := *setting.Value
		result.Value = &val
	}
	if result.Kind == PrintSettingProperty && result.Name.Space == printFramework2NS {
		result.Name.Space = printFrameworkNS
	}
	if result.Kind == PrintSettingOption && result.Constraint == PrintConstraintUnknown {
		result.Constraint = PrintConstraintNone
	}
	if result.Kind == PrintSettingFeature {
		var props, options, subFeats []PrintSetting
		defaultPos := -1
		for _, child := range setting.Children {
			converted, keep := printConvertSettingToV1Cap(child)
			if !keep {
				continue
			}
			switch child.Kind {
			case PrintSettingProperty:
				props = append(props, converted)
			case PrintSettingOption:
				if child.Default && defaultPos < 0 && (child.Constraint == PrintConstraintUnknown || child.Constraint == PrintConstraintNone) {
					defaultPos = len(options)
				}
				options = append(options, converted)
			case PrintSettingFeature:
				subFeats = append(subFeats, converted)
			}
		}
		if defaultPos > 0 {
			defOpt := options[defaultPos]
			reordered := make([]PrintSetting, 0, len(options))
			reordered = append(reordered, defOpt)
			for index, opt := range options {
				if index != defaultPos {
					reordered = append(reordered, opt)
				}
			}
			options = reordered
		}
		result.Children = append(result.Children, props...)
		result.Children = append(result.Children, options...)
		result.Children = append(result.Children, subFeats...)
		return result, true
	}
	for _, child := range setting.Children {
		converted, keep := printConvertSettingToV1Cap(child)
		if keep {
			result.Children = append(result.Children, converted)
		}
	}
	return result, true
}

// printApplyDeriveConstraints 按当前有效基准票据状态为PSF1能力Feature中的互斥选项动态标注PrintConstraintSettings
// 入参: feature 待标注的Feature指针, state 当前基准票据状态
func printApplyDeriveConstraints(feature *PrintSetting, state printDeriveState) {
	if !printPublicKeywordSpace(feature.Name.Space) {
		return
	}
	for index := range feature.Children {
		opt := &feature.Children[index]
		if opt.Kind != PrintSettingOption {
			continue
		}
		if opt.Constraint != PrintConstraintUnknown && opt.Constraint != PrintConstraintNone {
			continue
		}
		constrained := false
		switch feature.Name.Local {
		case "JobBindAllDocuments":
			if state.hasDocBind || (printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "Booklet" && (state.activeNUp > 1 || state.activePoster > 1)) {
				constrained = true
			}
		case "DocumentBinding":
			if state.hasJobBind || (printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "Booklet" && (state.activeNUp > 1 || state.activePoster > 1)) {
				constrained = true
			}
		case "JobNUpAllDocumentsContiguously":
			pages := printOptionIntScored(*opt, "PagesPerSheet")
			if state.hasDocNUp || (pages > 1 && (state.activeBooklet || state.activePoster > 1)) {
				constrained = true
			}
		case "DocumentNUp":
			pages := printOptionIntScored(*opt, "PagesPerSheet")
			if state.hasJobNUp || (pages > 1 && (state.activeBooklet || state.activePoster > 1)) {
				constrained = true
			}
		case "JobDuplexAllDocumentsContiguously":
			if state.hasDocDuplex || (state.activeBooklet && printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "OneSided") {
				constrained = true
			}
		case "DocumentDuplex":
			if state.hasJobDuplex || (state.activeBooklet && printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "OneSided") {
				constrained = true
			}
		case "PagePoster":
			sheets := printOptionIntScored(*opt, "SheetsPerPage")
			if sheets > 1 && (state.activeNUp > 1 || state.activeBooklet) {
				constrained = true
			}
		}
		if constrained {
			opt.Constraint = PrintConstraintSettings
		}
	}
}

// printOptionIntScored 读取Option直接子元素中指定公共整数ScoredProperty的数值，未找到或非整数返回零
// 入参: option Option节点, local 公共关键字本地名
// 返回: int 整数值，缺失或非整数为0
func printOptionIntScored(option PrintSetting, local string) int {
	for _, child := range option.Children {
		if child.Kind != PrintSettingScoredProperty || !printPublicKeywordSpace(child.Name.Space) || child.Name.Local != local {
			continue
		}
		val, ref := printScoredValue(child.Children)
		if ref != (xml.Name{}) || val == nil {
			return 0
		}
		parsed, err := strconv.Atoi(strings.Trim(val.Text, " \t\r\n"))
		if err != nil {
			return 0
		}
		return parsed
	}
	return 0
}
