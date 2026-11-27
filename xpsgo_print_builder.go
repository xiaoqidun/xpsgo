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
	"crypto/sha256"
	"encoding/xml"
	"fmt"
	"math"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

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

// PrintRollMediaSpec 描述能力文档支持的标准卷纸宽度与参数化长度微米范围及默认不可打印边距
// StandardName须为Print Schema公开卷纸名称（如Roll24Inch、Roll36Inch），宽度自动按标准卷纸查表填充
type PrintRollMediaSpec struct {
	StandardName         string
	MinHeightMicrons     int64
	MaxHeightMicrons     int64
	DefaultHeightMicrons int64
	StepMicrons          int64
	Margins              [4]int64
	Default              bool
	Constrained          PrintConstraint
}

// PrintResolutionSpec 描述能力文档支持的输出分辨率选项，单位为每英寸点数，Qualitative可选声明质量关键字
type PrintResolutionSpec struct {
	Name        xml.Name
	X           int
	Y           int
	Qualitative string
	Default     bool
	Constrained PrintConstraint
}

// PrintCustomOptionSpec 描述自定义私有命名空间Feature下的单个Option及其评分属性、参数引用、展示名与默认约束
type PrintCustomOptionSpec struct {
	Name         xml.Name
	ScoredValues map[xml.Name]PrintValue
	ScoredRefs   map[xml.Name]xml.Name
	DisplayName  string
	Identity     bool
	Default      bool
	Constrained  PrintConstraint
}

// PrintCustomFeatureSpec 描述自定义私有命名空间能力Feature及其选择方式、选项列表与嵌套子Feature
type PrintCustomFeatureSpec struct {
	Name        xml.Name
	Selection   PrintSelection
	DisplayName string
	Options     []PrintCustomOptionSpec
	SubFeatures []PrintCustomFeatureSpec
}

// PrintCustomSelectionSpec 描述打印票据中自定义私有命名空间Feature的选项选择与嵌套子Feature
type PrintCustomSelectionSpec struct {
	Feature     xml.Name
	Options     []PrintCustomOptionSpec
	SubFeatures []PrintCustomSelectionSpec
}

// PrintCustomParameterSpec 描述能力文档中自定义私有命名空间ParameterDef的数据类型、范围、步进与默认值
// DataType支持integer、decimal、string与QName，空字符串默认按string处理；Mandatory支持Conditional、Optional与Unconditional，空默认为Conditional
type PrintCustomParameterSpec struct {
	Name         xml.Name
	DataType     string
	UnitType     string
	Mandatory    string
	MinValue     string
	MaxValue     string
	Multiple     string
	DefaultValue string
	DefaultQName xml.Name
	DisplayName  string
}

// PrintCustomParameterInitSpec 描述打印票据中自定义私有命名空间ParameterInit的参数名称与初值
type PrintCustomParameterInitSpec struct {
	Name  xml.Name
	Value PrintValue
}

// PrintCustomPropertySpec 描述能力文档或打印票据根级自定义私有命名空间Property的名称、标量值及可选嵌套子Property
type PrintCustomPropertySpec struct {
	Name     xml.Name
	Value    *PrintValue
	Children []PrintCustomPropertySpec
}

// PrintDeriveOptions 配置Windows V4 PDC派生的资源预算与可选自定义动态约束回调
// CustomConstraints在标准派生约束标注与PageImageableSize重算完成后执行，可基于有效基准票据动态调整能力文档选项约束或根属性
type PrintDeriveOptions struct {
	Settings          PrintSettingsOptions
	CustomConstraints func(context.Context, *PrintSettings, *PrintCapabilities) error
}

// PrintCapabilitiesSpec 描述声明式构建PrintDeviceCapabilities与PrintCapabilities的设备能力规格
// 支持标准/自定义/卷纸纸型、分辨率、方向、缩放、镜像、页序、逐份、海报、多合一、双面、无边距、色彩管理与照片意图、进出纸盒、介质类型、装订/钉装/打孔、水印、副本及自定义私有Feature/ParameterDef/Property
type PrintCapabilitiesSpec struct {
	CapabilitiesChangeID       string
	MediaSizes                 []PrintMediaSpec
	RollMedia                  []PrintRollMediaSpec
	CustomMedia                *PrintCustomMediaSpec
	Resolutions                []PrintResolutionSpec
	Orientations               []string
	DefaultOrientation         string
	Scalings                   []string
	DefaultScaling             string
	MirrorImages               []string
	DefaultMirrorImage         string
	PageOrders                 []string
	DefaultPageOrder           string
	CollateModes               []string
	DefaultCollateMode         string
	DocumentCollateModes       []string
	DefaultDocumentCollateMode string
	NUpCounts                  []int
	DefaultNUp                 int
	JobLevelNUp                bool
	PosterCounts               []int
	DefaultPoster              int
	DuplexModes                []PrintDuplex
	DefaultDuplex              PrintDuplex
	JobLevelDuplex             bool
	Borderless                 bool
	DefaultBorderless          bool
	ColorModes                 []PrintColorMode
	DefaultColorMode           PrintColorMode
	ColorManagements           []string
	DefaultColorManagement     string
	RenderingIntents           []string
	DefaultRenderingIntent     string
	OutputQualities            []string
	DefaultOutputQuality       string
	PhotoPrintingIntents       []string
	DefaultPhotoPrintingIntent string
	JobInputBins               []string
	DefaultJobInputBin         string
	DocumentInputBins          []string
	DefaultDocumentInputBin    string
	PageInputBins              []string
	DefaultPageInputBin        string
	JobOutputBins              []string
	DefaultJobOutputBin        string
	DocumentOutputBins         []string
	DefaultDocumentOutputBin   string
	PageOutputBins             []string
	DefaultPageOutputBin       string
	MediaTypes                 []string
	DefaultMediaType           string
	Watermark                  bool
	MaxCopies                  int
	DefaultCopies              int
	JobLevelFinishing          bool
	Bindings                   []PrintBinding
	DefaultBinding             PrintBinding
	Staples                    []string
	DefaultStaple              string
	HolePunches                []string
	DefaultHolePunch           string
	CustomFeatures             []PrintCustomFeatureSpec
	CustomParameters           []PrintCustomParameterSpec
	CustomProperties           []PrintCustomPropertySpec
}

// PrintTicketSpec 描述声明式构建标准PrintTicket的高层打印参数规格
// 零值字段表示省略对应设置，CustomWidthMicrons与CustomHeightMicrons均大于零时启用CustomMediaSize，RollLengthMicrons大于零配合标准卷纸名启用卷纸长度
type PrintTicketSpec struct {
	Version               uint32
	MediaStandardName     string
	RollLengthMicrons     int64
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
	ColorManagement       string
	RenderingIntent       string
	NegativeImage         *bool
	OutputQuality         string
	PhotoPrintingIntent   string
	JobInputBin           string
	DocumentInputBin      string
	PageInputBin          string
	JobOutputBin          string
	DocumentOutputBin     string
	PageOutputBin         string
	MediaType             string
	Watermark             *PrintWatermark
	Copies                int
	DocumentCopies        int
	PageCopies            int
	Collate               string
	DocumentCollate       string
	Duplex                *PrintDuplex
	ManualDuplex          bool
	JobLevelDuplex        bool
	NUp                   int
	PresentationDirection string
	JobLevelNUp           bool
	PageOrder             string
	PageRanges            string
	PosterSheets          int
	Finishing             *PrintFinishing
	JobLevelFinishing     bool
	Staple                string
	HolePunch             string
	CustomFeatures        []PrintCustomSelectionSpec
	CustomParameters      []PrintCustomParameterInitSpec
	CustomProperties      []PrintCustomPropertySpec
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
	hasJobStaple    bool
	hasDocStaple    bool
	hasJobHolePunch bool
	hasDocHolePunch bool
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
	validated, err := validatePrintSettingsModel(&PrintSettings{Version: 2, CapabilitiesChangeID: changeID, Elements: elements}, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return nil, err
	}
	if changeID == "" {
		hasher := sha256.New()
		if _, err := encodePrintSettingsDocument(hasher, validated, configuration, printDocumentDeviceCapabilities); err != nil {
			return nil, err
		}
		sum := hasher.Sum(nil)
		validated.CapabilitiesChangeID = fmt.Sprintf("{%08X-%04X-%04X-%04X-%012X}", sum[0:4], sum[4:6], sum[6:8], sum[8:10], sum[10:16])
	}
	return validated, nil
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
	parsed, err := validatePrintSettingsModel(&PrintSettings{Version: 1, Elements: elements}, configuration, printDocumentCapabilities)
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
	if len(spec.MediaSizes) > 0 || len(spec.RollMedia) > 0 || spec.CustomMedia != nil {
		mediaOptions := make([]PrintSetting, 0, len(spec.MediaSizes)+len(spec.RollMedia)+1)
		mediaSeen := make(map[xml.Name]bool)
		stdSeen := make(map[string]bool)
		defaultIdx := -1
		var defaultW, defaultH int64
		var defaultMargins [4]int64
		hasHeightParam := false
		var heightMin, heightMax, heightStep, heightDef int64
		for _, item := range spec.MediaSizes {
			optName := item.Name
			w, h := item.WidthMicrons, item.HeightMicrons
			if item.StandardName != "" {
				if stdSeen[item.StandardName] {
					return nil, nil, fmt.Errorf("%w: duplicate standard media %s", ErrInvalid, item.StandardName)
				}
				stdSeen[item.StandardName] = true
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
		type printPendingRoll struct {
			name        xml.Name
			width       int64
			margins     [4]int64
			isDefault   bool
			constrained PrintConstraint
		}
		pendingRolls := make([]printPendingRoll, 0, len(spec.RollMedia))
		var minDynamicHeight int64
		for _, item := range spec.RollMedia {
			dims, ok := printMediaSizes[item.StandardName]
			if !ok || dims[1] != 0 {
				return nil, nil, fmt.Errorf("%w: invalid standard roll media %s", ErrInvalid, item.StandardName)
			}
			if stdSeen[item.StandardName] {
				return nil, nil, fmt.Errorf("%w: duplicate standard media %s", ErrInvalid, item.StandardName)
			}
			stdSeen[item.StandardName] = true
			optName := xml.Name{Space: printKeywordsNS, Local: item.StandardName}
			key := printCanonicalKey(optName)
			if mediaSeen[key] {
				return nil, nil, fmt.Errorf("%w: duplicate media option %s", ErrInvalid, optName.Local)
			}
			mediaSeen[key] = true
			w := int64(dims[0])
			step := item.StepMicrons
			if step == 0 {
				step = 1
			}
			defH := item.DefaultHeightMicrons
			if defH == 0 {
				defH = item.MinHeightMicrons
			}
			if item.MinHeightMicrons <= 0 || item.MinHeightMicrons > item.MaxHeightMicrons || step <= 0 || defH < item.MinHeightMicrons || defH > item.MaxHeightMicrons || (defH-item.MinHeightMicrons)%step != 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintRollMediaSpec height range for %s", ErrInvalid, item.StandardName)
			}
			if item.Margins[0] < 0 || item.Margins[1] < 0 || item.Margins[2] < 0 || item.Margins[3] < 0 || item.Margins[0] >= w || item.Margins[2] >= w-item.Margins[0] || item.Margins[1] >= item.MinHeightMicrons || item.Margins[3] >= item.MinHeightMicrons-item.Margins[1] {
				return nil, nil, fmt.Errorf("%w: invalid roll media margins for %s", ErrInvalid, item.StandardName)
			}
			if item.Default {
				if defaultIdx >= 0 {
					return nil, nil, fmt.Errorf("%w: multiple default media options", ErrInvalid)
				}
				if item.Constrained != PrintConstraintUnknown && item.Constrained != PrintConstraintNone {
					return nil, nil, fmt.Errorf("%w: constrained roll media option cannot be default", ErrInvalid)
				}
			}
			pendingRolls = append(pendingRolls, printPendingRoll{name: optName, width: w, margins: item.Margins, isDefault: item.Default, constrained: item.Constrained})
			if need := item.Margins[1] + item.Margins[3] + 1; need > minDynamicHeight {
				minDynamicHeight = need
			}
			if !hasHeightParam {
				hasHeightParam = true
				heightMin, heightMax, heightStep, heightDef = item.MinHeightMicrons, item.MaxHeightMicrons, step, defH
			} else {
				if item.MinHeightMicrons < heightMin {
					heightMin = item.MinHeightMicrons
				}
				if item.MaxHeightMicrons > heightMax {
					heightMax = item.MaxHeightMicrons
				}
				heightStep = 1
			}
		}
		var customName xml.Name
		var customDefW, customDefH, customStep int64
		if spec.CustomMedia != nil {
			customName = xml.Name{Space: printKeywordsNS, Local: "CustomMediaSize"}
			if mediaSeen[printCanonicalKey(customName)] {
				return nil, nil, fmt.Errorf("%w: duplicate media option CustomMediaSize", ErrInvalid)
			}
			mediaSeen[printCanonicalKey(customName)] = true
			cm := spec.CustomMedia
			customStep = cm.StepMicrons
			if customStep == 0 {
				customStep = 1
			}
			customDefW, customDefH = cm.DefaultWidthMicrons, cm.DefaultHeightMicrons
			if customDefW == 0 {
				customDefW = cm.MinWidthMicrons
			}
			if customDefH == 0 {
				customDefH = cm.MinHeightMicrons
			}
			if cm.MinWidthMicrons <= 0 || cm.MinWidthMicrons > cm.MaxWidthMicrons || cm.MinHeightMicrons <= 0 || cm.MinHeightMicrons > cm.MaxHeightMicrons || customStep <= 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintCustomMediaSpec range", ErrInvalid)
			}
			if customDefW < cm.MinWidthMicrons || customDefW > cm.MaxWidthMicrons || customDefH < cm.MinHeightMicrons || customDefH > cm.MaxHeightMicrons || (customDefW-cm.MinWidthMicrons)%customStep != 0 || (customDefH-cm.MinHeightMicrons)%customStep != 0 {
				return nil, nil, fmt.Errorf("%w: invalid PrintCustomMediaSpec default dimensions", ErrInvalid)
			}
			if cm.Margins[0] < 0 || cm.Margins[1] < 0 || cm.Margins[2] < 0 || cm.Margins[3] < 0 || cm.Margins[0] >= cm.MinWidthMicrons || cm.Margins[2] >= cm.MinWidthMicrons-cm.Margins[0] || cm.Margins[1] >= cm.MinHeightMicrons || cm.Margins[3] >= cm.MinHeightMicrons-cm.Margins[1] {
				return nil, nil, fmt.Errorf("%w: invalid custom media margins", ErrInvalid)
			}
			if need := cm.Margins[1] + cm.Margins[3] + 1; need > minDynamicHeight {
				minDynamicHeight = need
			}
			if !hasHeightParam {
				hasHeightParam = true
				heightMin, heightMax, heightStep, heightDef = cm.MinHeightMicrons, cm.MaxHeightMicrons, customStep, customDefH
			} else {
				if cm.MinHeightMicrons < heightMin {
					heightMin = cm.MinHeightMicrons
				}
				if cm.MaxHeightMicrons > heightMax {
					heightMax = cm.MaxHeightMicrons
				}
				heightStep = 1
			}
		}
		if hasHeightParam {
			if heightDef < minDynamicHeight {
				heightDef = minDynamicHeight
			}
			if heightDef > heightMax {
				return nil, nil, fmt.Errorf("%w: incompatible dynamic media height margins", ErrInvalid)
			}
			if heightStep > 1 {
				if rem := (heightDef - heightMin) % heightStep; rem != 0 {
					aligned := heightDef + (heightStep - rem)
					if aligned > heightMax {
						return nil, nil, fmt.Errorf("%w: incompatible dynamic media height step", ErrInvalid)
					}
					heightDef = aligned
				}
			}
		}
		for _, roll := range pendingRolls {
			rollChildren := []PrintSetting{
				printBuildIntScored("MediaSizeWidth", roll.width),
				printBuildRefScored("MediaSizeHeight", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}),
			}
			if isPDC {
				rollChildren = append(rollChildren, printBuildPortraitImageableProperty(roll.margins[0], roll.margins[1], roll.width-roll.margins[0]-roll.margins[2], heightDef-roll.margins[1]-roll.margins[3]))
			}
			opt := PrintSetting{Kind: PrintSettingOption, Name: roll.name, Children: rollChildren, Constraint: roll.constrained}
			if roll.isDefault {
				defaultIdx = len(mediaOptions)
				defaultW, defaultH, defaultMargins = roll.width, heightDef, roll.margins
			} else if defaultIdx < 0 && (roll.constrained == PrintConstraintUnknown || roll.constrained == PrintConstraintNone) && defaultW == 0 {
				defaultW, defaultH, defaultMargins = roll.width, heightDef, roll.margins
			}
			mediaOptions = append(mediaOptions, opt)
		}
		if spec.CustomMedia != nil {
			cm := spec.CustomMedia
			customChildren := []PrintSetting{
				printBuildRefScored("MediaSizeWidth", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeWidth"}),
				printBuildRefScored("MediaSizeHeight", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}),
			}
			if isPDC {
				customChildren = append(customChildren, printBuildPortraitImageableProperty(cm.Margins[0], cm.Margins[1], customDefW-cm.Margins[0]-cm.Margins[2], heightDef-cm.Margins[1]-cm.Margins[3]))
			}
			mediaOptions = append(mediaOptions, PrintSetting{
				Kind:     PrintSettingOption,
				Name:     customName,
				Children: customChildren,
			})
			if defaultW == 0 {
				defaultW, defaultH, defaultMargins = customDefW, heightDef, cm.Margins
			}
			addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeWidth"}, "microns", "Conditional", cm.MinWidthMicrons, cm.MaxWidthMicrons, customStep, customDefW))
		}
		if hasHeightParam {
			addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}, "microns", "Conditional", heightMin, heightMax, heightStep, heightDef))
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
			if item.Qualitative != "" && !xmlNCName(item.Qualitative) {
				return nil, nil, fmt.Errorf("%w: invalid resolution qualitative keyword %s", ErrInvalid, item.Qualitative)
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
			resChildren := []PrintSetting{
				printBuildIntScored("ResolutionX", int64(item.X)),
				printBuildIntScored("ResolutionY", int64(item.Y)),
			}
			if item.Qualitative != "" {
				resChildren = append(resChildren, printBuildQNameScored("QualitativeResolution", xml.Name{Space: printKeywordsNS, Local: item.Qualitative}))
			}
			resOptions = append(resOptions, PrintSetting{
				Kind:       PrintSettingOption,
				Name:       optName,
				Constraint: item.Constrained,
				Children:   resChildren,
			})
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageResolution"}, resOptions, defaultIdx, isPDC, nil))
	}
	if len(spec.Orientations) > 0 {
		orientOpts, defIdx, err := printBuildKeywordOptions(spec.Orientations, spec.DefaultOrientation, printAllowedOrientations)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOrientation"}, orientOpts, defIdx, isPDC, nil))
	}
	if len(spec.Scalings) > 0 {
		scaleOpts := make([]PrintSetting, 0, len(spec.Scalings))
		seen := make(map[string]bool)
		defIdx := -1
		needAlignment := false
		for _, name := range spec.Scalings {
			if !slices.Contains(printAllowedScalings, name) || seen[name] {
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
			alignOpts, alignDef, _ := printBuildKeywordOptions(printAllowedScaleOffsetAlignments, "Center", printAllowedScaleOffsetAlignments)
			subFeatures = append(subFeatures, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "ScaleOffsetAlignment"}, alignOpts, alignDef, isPDC, nil))
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageScaling"}, scaleOpts, defIdx, isPDC, subFeatures))
	}
	if len(spec.MirrorImages) > 0 {
		mirrorOpts, defIdx, err := printBuildKeywordOptions(spec.MirrorImages, spec.DefaultMirrorImage, printAllowedMirrorImages)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageMirrorImage"}, mirrorOpts, defIdx, isPDC, nil))
	}
	if len(spec.PageOrders) > 0 {
		orderOpts, defIdx, err := printBuildKeywordOptions(spec.PageOrders, spec.DefaultPageOrder, printAllowedPageOrders)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "JobPageOrder"}, orderOpts, defIdx, isPDC, nil))
	}
	if len(spec.CollateModes) > 0 {
		collateOpts, defIdx, err := printBuildKeywordOptions(spec.CollateModes, spec.DefaultCollateMode, printAllowedCollateModes)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "JobCollateAllDocuments"}, collateOpts, defIdx, isPDC, nil))
	}
	if len(spec.DocumentCollateModes) > 0 {
		docCollateOpts, defIdx, err := printBuildKeywordOptions(spec.DocumentCollateModes, spec.DefaultDocumentCollateMode, printAllowedCollateModes)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "DocumentCollate"}, docCollateOpts, defIdx, isPDC, nil))
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
		dirOpts, dirDef, _ := printBuildKeywordOptions(printAllowedPresentationDirections, "RightBottom", printAllowedPresentationDirections)
		sub := []PrintSetting{printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PresentationDirection"}, dirOpts, dirDef, isPDC, nil)}
		nupFeat := "DocumentNUp"
		if spec.JobLevelNUp {
			nupFeat = "JobNUpAllDocumentsContiguously"
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: nupFeat}, nupOpts, defIdx, isPDC, sub))
	}
	if len(spec.PosterCounts) > 0 {
		posterOpts := make([]PrintSetting, 0, len(spec.PosterCounts))
		seen := make(map[int]bool)
		defIdx := -1
		for _, count := range spec.PosterCounts {
			if count < 1 || seen[count] {
				return nil, nil, fmt.Errorf("%w: invalid or duplicate poster sheet count %d", ErrInvalid, count)
			}
			seen[count] = true
			if spec.DefaultPoster > 0 && spec.DefaultPoster == count {
				defIdx = len(posterOpts)
			}
			posterOpts = append(posterOpts, PrintSetting{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printBuilderNS, Local: fmt.Sprintf("Poster%d", count)},
				Children: []PrintSetting{printBuildIntScored("SheetsPerPage", int64(count))},
			})
		}
		if spec.DefaultPoster > 0 && defIdx < 0 {
			return nil, nil, fmt.Errorf("%w: default poster %d not in PosterCounts", ErrInvalid, spec.DefaultPoster)
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PagePoster"}, posterOpts, defIdx, isPDC, nil))
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
		duplexOpts, defIdx, err := printBuildKeywordOptions(duplexNames, defaultDuplexName, printAllowedDuplexOptions)
		if err != nil {
			return nil, nil, err
		}
		duplexFeat := "DocumentDuplex"
		if spec.JobLevelDuplex {
			duplexFeat = "JobDuplexAllDocumentsContiguously"
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: duplexFeat}, duplexOpts, defIdx, isPDC, nil))
	}
	if spec.Borderless {
		defName := "None"
		if spec.DefaultBorderless {
			defName = "Borderless"
		}
		borderOpts, defIdx, _ := printBuildKeywordOptions(printAllowedBorderlessOptions, defName, printAllowedBorderlessOptions)
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
		colorOpts, defIdx, err := printBuildKeywordOptions(colorNames, defColor, printAllowedOutputColors)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOutputColor"}, colorOpts, defIdx, isPDC, nil))
	}
	if len(spec.ColorManagements) > 0 {
		cmOpts, defIdx, err := printBuildKeywordOptions(spec.ColorManagements, spec.DefaultColorManagement, printAllowedColorManagements)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageColorManagement"}, cmOpts, defIdx, isPDC, nil))
	}
	if len(spec.RenderingIntents) > 0 {
		intentOpts, defIdx, err := printBuildKeywordOptions(spec.RenderingIntents, spec.DefaultRenderingIntent, printAllowedRenderingIntents)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageICMRenderingIntent"}, intentOpts, defIdx, isPDC, nil))
	}
	if len(spec.OutputQualities) > 0 {
		qualOpts, defIdx, err := printBuildKeywordOptions(spec.OutputQualities, spec.DefaultOutputQuality, printAllowedOutputQualities)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageOutputQuality"}, qualOpts, defIdx, isPDC, nil))
	}
	if len(spec.PhotoPrintingIntents) > 0 {
		photoOpts, defIdx, err := printBuildKeywordOptions(spec.PhotoPrintingIntents, spec.DefaultPhotoPrintingIntent, printAllowedPhotoPrintingIntents)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PagePhotoPrintingIntent"}, photoOpts, defIdx, isPDC, nil))
	}
	for _, group := range []struct {
		feature string
		values  []string
		def     string
	}{
		{"JobInputBin", spec.JobInputBins, spec.DefaultJobInputBin},
		{"DocumentInputBin", spec.DocumentInputBins, spec.DefaultDocumentInputBin},
		{"PageInputBin", spec.PageInputBins, spec.DefaultPageInputBin},
		{"JobOutputBin", spec.JobOutputBins, spec.DefaultJobOutputBin},
		{"DocumentOutputBin", spec.DocumentOutputBins, spec.DefaultDocumentOutputBin},
		{"PageOutputBin", spec.PageOutputBins, spec.DefaultPageOutputBin},
		{"PageMediaType", spec.MediaTypes, spec.DefaultMediaType},
	} {
		if len(group.values) == 0 {
			continue
		}
		opts, defIdx, err := printBuildKeywordOptions(group.values, group.def, nil)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: group.feature}, opts, defIdx, isPDC, nil))
	}
	if len(spec.Bindings) > 0 {
		bindingNames := make([]string, 0, len(spec.Bindings))
		for _, b := range spec.Bindings {
			if b > PrintBindingTrim {
				return nil, nil, fmt.Errorf("%w: invalid binding mode %v", ErrInvalid, b)
			}
			bindingNames = append(bindingNames, b.String())
		}
		defBindName := ""
		if spec.DefaultBinding != PrintBindingNone || slices.Contains(spec.Bindings, PrintBindingNone) {
			if slices.Contains(spec.Bindings, spec.DefaultBinding) {
				defBindName = spec.DefaultBinding.String()
			} else if spec.DefaultBinding != PrintBindingNone {
				return nil, nil, fmt.Errorf("%w: default binding not in Bindings", ErrInvalid)
			}
		}
		bindOpts, defIdx, err := printBuildKeywordOptions(bindingNames, defBindName, printAllowedBindingOptions)
		if err != nil {
			return nil, nil, err
		}
		bindFeat := "DocumentBinding"
		if spec.JobLevelFinishing {
			bindFeat = "JobBindAllDocuments"
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: bindFeat}, bindOpts, defIdx, isPDC, nil))
	}
	if len(spec.Staples) > 0 {
		stapleOpts, defIdx, err := printBuildKeywordOptions(spec.Staples, spec.DefaultStaple, printAllowedStapleOptions)
		if err != nil {
			return nil, nil, err
		}
		stapleFeat := "DocumentStaple"
		if spec.JobLevelFinishing {
			stapleFeat = "JobStapleAllDocuments"
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: stapleFeat}, stapleOpts, defIdx, isPDC, nil))
	}
	if len(spec.HolePunches) > 0 {
		punchOpts, defIdx, err := printBuildKeywordOptions(spec.HolePunches, spec.DefaultHolePunch, printAllowedHolePunchOptions)
		if err != nil {
			return nil, nil, err
		}
		punchFeat := "DocumentHolePunch"
		if spec.JobLevelFinishing {
			punchFeat = "JobHolePunch"
		}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: punchFeat}, punchOpts, defIdx, isPDC, nil))
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
		layerOpts, layerDef, _ := printBuildKeywordOptions(printAllowedWatermarkLayers, "Overlay", printAllowedWatermarkLayers)
		sub := []PrintSetting{printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "Layering"}, layerOpts, layerDef, isPDC, nil)}
		elements = append(elements, printBuildPickOneFeature(xml.Name{Space: printKeywordsNS, Local: "PageWatermark"}, wmOpts, 0, isPDC, sub))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginWidth"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginHeight"}, "microns", "Conditional", -1000000, 1000000, 1, 0))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTransparency"}, "percent", "Conditional", 0, 100, 1, 50))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextAngle"}, "degrees", "Conditional", 0, 359, 1, 0))
		addParam(printBuildStringParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextColor"}, "sRGB", "Conditional", 9, 9, "#80808080"))
		addParam(printBuildIntParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextFontSize"}, "points", "Conditional", 1, 1000, 1, 48))
		addParam(printBuildStringParameterDef(xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextText"}, "characters", "Conditional", 1, printWatermarkTextLimit, "DRAFT"))
	}
	for _, custom := range spec.CustomFeatures {
		feat, err := printBuildCustomCapabilityFeature(custom, isPDC)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, feat)
	}
	for _, propSpec := range spec.CustomProperties {
		prop, err := printBuildCustomProperty(propSpec)
		if err != nil {
			return nil, nil, err
		}
		elements = append(elements, prop)
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
	for _, paramSpec := range spec.CustomParameters {
		def, err := printBuildCustomParameterDef(paramSpec)
		if err != nil {
			return nil, nil, err
		}
		key := printCanonicalKey(def.Name)
		if paramSeen[key] {
			return nil, nil, fmt.Errorf("%w: duplicate custom ParameterDef %s", ErrInvalid, def.Name.Local)
		}
		addParam(def)
	}
	elements = append(elements, params...)
	return elements, defaultImageable, nil
}

// printBuildCustomCapabilityFeature 递归构造自定义私有命名空间能力Feature，支持PickOne与PickMany、展示名、恒等选项及ScoredProperty
// 入参: spec 自定义能力Feature规格, isPDC 是否生成PSF2 PDC节点
// 返回: PrintSetting 构造完成的Feature节点, error 规格非法错误
func printBuildCustomCapabilityFeature(spec PrintCustomFeatureSpec, isPDC bool) (PrintSetting, error) {
	if spec.Name.Space == "" || !xmlNCName(spec.Name.Local) || !xmlTextValid(spec.Name.Space) || spec.Name.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom feature name", ErrInvalid)
	}
	selection := spec.Selection
	if selection == PrintSelectionUnknown {
		selection = PrintSelectionOne
	}
	if selection != PrintSelectionOne && selection != PrintSelectionMany {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom feature selection %v", ErrInvalid, selection)
	}
	if len(spec.Options) == 0 && len(spec.SubFeatures) == 0 {
		return PrintSetting{}, fmt.Errorf("%w: empty custom feature %s", ErrInvalid, spec.Name.Local)
	}
	options := make([]PrintSetting, 0, len(spec.Options))
	optSeen := make(map[xml.Name]bool, len(spec.Options))
	defaultIdx := -1
	for _, optSpec := range spec.Options {
		opt, err := printBuildCustomOption(optSpec, true)
		if err != nil {
			return PrintSetting{}, err
		}
		key := printCanonicalKey(opt.Name)
		if optSeen[key] {
			return PrintSetting{}, fmt.Errorf("%w: duplicate custom option %s", ErrInvalid, opt.Name.Local)
		}
		optSeen[key] = true
		if optSpec.Default {
			if optSpec.Constrained != PrintConstraintUnknown && optSpec.Constrained != PrintConstraintNone {
				return PrintSetting{}, fmt.Errorf("%w: constrained custom option cannot be default", ErrInvalid)
			}
			if selection == PrintSelectionOne {
				if defaultIdx >= 0 {
					return PrintSetting{}, fmt.Errorf("%w: multiple default options on PickOne custom feature %s", ErrInvalid, spec.Name.Local)
				}
				defaultIdx = len(options)
			} else if isPDC {
				opt.HasDefault = true
				opt.Default = true
			}
		}
		options = append(options, opt)
	}
	subFeatures := make([]PrintSetting, 0, len(spec.SubFeatures))
	for _, subSpec := range spec.SubFeatures {
		sub, err := printBuildCustomCapabilityFeature(subSpec, isPDC)
		if err != nil {
			return PrintSetting{}, err
		}
		subFeatures = append(subFeatures, sub)
	}
	var feat PrintSetting
	if selection == PrintSelectionOne {
		feat = printBuildPickOneFeature(spec.Name, options, defaultIdx, isPDC, subFeatures)
	} else {
		children := make([]PrintSetting, 0, 1+len(options)+len(subFeatures))
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "SelectionType"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "psk:PickMany", QName: xml.Name{Space: printKeywordsNS, Local: "PickMany"}},
			}},
		})
		children = append(children, options...)
		children = append(children, subFeatures...)
		feat = PrintSetting{Kind: PrintSettingFeature, Name: spec.Name, Children: children}
	}
	if spec.DisplayName != "" {
		if !xmlTextValid(spec.DisplayName) {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom feature DisplayName", ErrInvalid)
		}
		feat.Children = append([]PrintSetting{{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printKeywordsNS, Local: "DisplayName"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: spec.DisplayName},
			}},
		}}, feat.Children...)
	}
	return feat, nil
}

// printBuildCustomOption 构造自定义Option节点并按确定性名称顺序生成ScoredProperty、ParameterRef与能力属性
// 入参: spec 自定义Option规格, capabilities 是否为能力文档模式
// 返回: PrintSetting Option节点, error 名称或评分属性非法错误
func printBuildCustomOption(spec PrintCustomOptionSpec, capabilities bool) (PrintSetting, error) {
	if spec.Name.Space == "" || !xmlNCName(spec.Name.Local) || !xmlTextValid(spec.Name.Space) || spec.Name.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom option name", ErrInvalid)
	}
	if !capabilities && (spec.Constrained != PrintConstraintUnknown || spec.Identity || spec.DisplayName != "" || spec.Default) {
		return PrintSetting{}, fmt.Errorf("%w: capability metadata not allowed on ticket custom option", ErrInvalid)
	}
	var children []PrintSetting
	if capabilities && spec.Identity {
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "IdentityOption"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: "True"},
			}},
		})
	}
	if capabilities && spec.DisplayName != "" {
		if !xmlTextValid(spec.DisplayName) {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom option DisplayName", ErrInvalid)
		}
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printKeywordsNS, Local: "DisplayName"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: spec.DisplayName},
			}},
		})
	}
	seenScored := make(map[xml.Name]bool, len(spec.ScoredValues)+len(spec.ScoredRefs))
	valKeys := make([]xml.Name, 0, len(spec.ScoredValues))
	for k := range spec.ScoredValues {
		valKeys = append(valKeys, k)
	}
	slices.SortFunc(valKeys, func(a, b xml.Name) int {
		if a.Space != b.Space {
			return strings.Compare(a.Space, b.Space)
		}
		return strings.Compare(a.Local, b.Local)
	})
	for _, k := range valKeys {
		if k.Space == "" || !xmlNCName(k.Local) || !xmlTextValid(k.Space) || k.Space == xmlnsNamespace {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom ScoredProperty name", ErrInvalid)
		}
		ck := printCanonicalKey(k)
		if seenScored[ck] {
			return PrintSetting{}, fmt.Errorf("%w: duplicate custom ScoredProperty %s", ErrInvalid, k.Local)
		}
		seenScored[ck] = true
		val := spec.ScoredValues[k]
		if val.Type == (xml.Name{}) {
			val.Type = xml.Name{Space: printValueNS, Local: "string"}
		}
		children = append(children, PrintSetting{
			Kind:     PrintSettingScoredProperty,
			Name:     k,
			Children: []PrintSetting{{Kind: PrintSettingValue, Value: &val}},
		})
	}
	refKeys := make([]xml.Name, 0, len(spec.ScoredRefs))
	for k := range spec.ScoredRefs {
		refKeys = append(refKeys, k)
	}
	slices.SortFunc(refKeys, func(a, b xml.Name) int {
		if a.Space != b.Space {
			return strings.Compare(a.Space, b.Space)
		}
		return strings.Compare(a.Local, b.Local)
	})
	for _, k := range refKeys {
		ref := spec.ScoredRefs[k]
		if k.Space == "" || !xmlNCName(k.Local) || !xmlTextValid(k.Space) || k.Space == xmlnsNamespace || ref.Space == "" || !xmlNCName(ref.Local) || !xmlTextValid(ref.Space) || ref.Space == xmlnsNamespace {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom ScoredProperty ParameterRef", ErrInvalid)
		}
		ck := printCanonicalKey(k)
		if seenScored[ck] {
			return PrintSetting{}, fmt.Errorf("%w: duplicate custom ScoredProperty %s", ErrInvalid, k.Local)
		}
		seenScored[ck] = true
		children = append(children, PrintSetting{
			Kind:     PrintSettingScoredProperty,
			Name:     k,
			Children: []PrintSetting{{Kind: PrintSettingParameterRef, Name: ref}},
		})
	}
	return PrintSetting{Kind: PrintSettingOption, Name: spec.Name, Children: children, Constraint: spec.Constrained}, nil
}

// printBuildCustomTicketFeature 递归构造打印票据中的自定义私有命名空间Feature选择节点
// 入参: spec 自定义票据Feature选择规格
// 返回: PrintSetting Feature节点, error 规格非法错误
func printBuildCustomTicketFeature(spec PrintCustomSelectionSpec) (PrintSetting, error) {
	if spec.Feature.Space == "" || !xmlNCName(spec.Feature.Local) || !xmlTextValid(spec.Feature.Space) || spec.Feature.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom ticket feature name", ErrInvalid)
	}
	if len(spec.Options) == 0 && len(spec.SubFeatures) == 0 {
		return PrintSetting{}, fmt.Errorf("%w: empty custom ticket feature %s", ErrInvalid, spec.Feature.Local)
	}
	children := make([]PrintSetting, 0, len(spec.Options)+len(spec.SubFeatures))
	for _, optSpec := range spec.Options {
		opt, err := printBuildCustomOption(optSpec, false)
		if err != nil {
			return PrintSetting{}, err
		}
		children = append(children, opt)
	}
	for _, subSpec := range spec.SubFeatures {
		sub, err := printBuildCustomTicketFeature(subSpec)
		if err != nil {
			return PrintSetting{}, err
		}
		children = append(children, sub)
	}
	return PrintSetting{Kind: PrintSettingFeature, Name: spec.Feature, Children: children}, nil
}

// printBuildCustomParameterDef 按自定义私有参数规格构造合规的ParameterDef节点，由调用方外层统一执行参数域校验
// 入参: spec 自定义参数域规格
// 返回: PrintSetting ParameterDef节点, error 名称、类型或必填约束非法错误
func printBuildCustomParameterDef(spec PrintCustomParameterSpec) (PrintSetting, error) {
	if spec.Name.Space == "" || !xmlNCName(spec.Name.Local) || !xmlTextValid(spec.Name.Space) || spec.Name.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterDef name", ErrInvalid)
	}
	dataType := spec.DataType
	if dataType == "" {
		dataType = "string"
	}
	if dataType != "integer" && dataType != "decimal" && dataType != "string" && dataType != "QName" {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterDef DataType %s", ErrInvalid, dataType)
	}
	mandatory := spec.Mandatory
	if mandatory == "" {
		mandatory = "Conditional"
	}
	if mandatory != "Conditional" && mandatory != "Optional" && mandatory != "Unconditional" {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterDef Mandatory %s", ErrInvalid, mandatory)
	}
	children := []PrintSetting{
		{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "DataType"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "xs:" + dataType, QName: xml.Name{Space: printValueNS, Local: dataType}},
			}},
		},
		{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "Mandatory"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: "psk:" + mandatory, QName: xml.Name{Space: printKeywordsNS, Local: mandatory}},
			}},
		},
	}
	if spec.UnitType != "" {
		if !xmlTextValid(spec.UnitType) {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterDef UnitType", ErrInvalid)
		}
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "UnitType"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: spec.UnitType},
			}},
		})
	}
	if spec.DisplayName != "" {
		if !xmlTextValid(spec.DisplayName) {
			return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterDef DisplayName", ErrInvalid)
		}
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printKeywordsNS, Local: "DisplayName"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: spec.DisplayName},
			}},
		})
	}
	switch dataType {
	case "integer", "decimal":
		if spec.MinValue == "" || spec.MaxValue == "" {
			return PrintSetting{}, fmt.Errorf("%w: custom numeric ParameterDef requires MinValue and MaxValue", ErrInvalid)
		}
		mult := spec.Multiple
		if mult == "" {
			mult = "1"
		}
		defVal := spec.DefaultValue
		if defVal == "" {
			defVal = spec.MinValue
		}
		valType := xml.Name{Space: printValueNS, Local: dataType}
		children = append(children,
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "MinValue"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: valType, Text: spec.MinValue}}}},
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "MaxValue"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: valType, Text: spec.MaxValue}}}},
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "Multiple"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: valType, Text: mult}}}},
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "DefaultValue"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: valType, Text: defVal}}}},
		)
	case "string":
		minLen := spec.MinValue
		if minLen == "" {
			minLen = "0"
		}
		if spec.MaxValue == "" {
			return PrintSetting{}, fmt.Errorf("%w: custom string ParameterDef requires MaxValue", ErrInvalid)
		}
		intType := xml.Name{Space: printValueNS, Local: "integer"}
		defVal := &PrintValue{Type: xml.Name{Space: printValueNS, Local: "string"}, Text: spec.DefaultValue, QName: spec.DefaultQName}
		children = append(children,
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "MinLength"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: intType, Text: minLen}}}},
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "MaxLength"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &PrintValue{Type: intType, Text: spec.MaxValue}}}},
			PrintSetting{Kind: PrintSettingProperty, Name: xml.Name{Space: printFrameworkNS, Local: "DefaultValue"}, Children: []PrintSetting{{Kind: PrintSettingValue, Value: defVal}}},
		)
	case "QName":
		if spec.DefaultQName.Space == "" || !xmlNCName(spec.DefaultQName.Local) || !xmlTextValid(spec.DefaultQName.Space) || spec.DefaultQName.Space == xmlnsNamespace {
			return PrintSetting{}, fmt.Errorf("%w: custom QName ParameterDef requires valid DefaultQName", ErrInvalid)
		}
		text := spec.DefaultValue
		if text == "" {
			text = spec.DefaultQName.Local
		}
		children = append(children, PrintSetting{
			Kind: PrintSettingProperty,
			Name: xml.Name{Space: printFrameworkNS, Local: "DefaultValue"},
			Children: []PrintSetting{{
				Kind:  PrintSettingValue,
				Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, Text: text, QName: spec.DefaultQName},
			}},
		})
	}
	return PrintSetting{Kind: PrintSettingParameterDef, Name: spec.Name, Children: children}, nil
}

// printBuildCustomParameterInit 按自定义私有参数初值规格构造ParameterInit节点
// 入参: spec 自定义参数初值规格
// 返回: PrintSetting ParameterInit节点, error 名称非法错误
func printBuildCustomParameterInit(spec PrintCustomParameterInitSpec) (PrintSetting, error) {
	if spec.Name.Space == "" || !xmlNCName(spec.Name.Local) || !xmlTextValid(spec.Name.Space) || spec.Name.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom ParameterInit name", ErrInvalid)
	}
	val := spec.Value
	if val.Type == (xml.Name{}) {
		val.Type = xml.Name{Space: printValueNS, Local: "string"}
	}
	return PrintSetting{
		Kind:     PrintSettingParameterInit,
		Name:     spec.Name,
		Children: []PrintSetting{{Kind: PrintSettingValue, Value: &val}},
	}, nil
}

// printBuildCustomProperty 递归构造自定义私有命名空间Property节点，支持标量值与嵌套子Property
// 入参: spec 自定义属性规格
// 返回: PrintSetting Property节点, error 名称、空体或重复子项错误
func printBuildCustomProperty(spec PrintCustomPropertySpec) (PrintSetting, error) {
	if spec.Name.Space == "" || !xmlNCName(spec.Name.Local) || !xmlTextValid(spec.Name.Space) || spec.Name.Space == xmlnsNamespace {
		return PrintSetting{}, fmt.Errorf("%w: invalid custom Property name", ErrInvalid)
	}
	if spec.Value == nil && len(spec.Children) == 0 {
		return PrintSetting{}, fmt.Errorf("%w: empty custom Property %s", ErrInvalid, spec.Name.Local)
	}
	children := make([]PrintSetting, 0, len(spec.Children)+1)
	if spec.Value != nil {
		val := *spec.Value
		if val.Type == (xml.Name{}) {
			val.Type = xml.Name{Space: printValueNS, Local: "string"}
		}
		children = append(children, PrintSetting{Kind: PrintSettingValue, Value: &val})
	}
	seen := make(map[xml.Name]bool, len(spec.Children))
	for _, childSpec := range spec.Children {
		child, err := printBuildCustomProperty(childSpec)
		if err != nil {
			return PrintSetting{}, err
		}
		key := printCanonicalKey(child.Name)
		if seen[key] {
			return PrintSetting{}, fmt.Errorf("%w: duplicate custom child Property %s", ErrInvalid, child.Name.Local)
		}
		seen[key] = true
		children = append(children, child)
	}
	return PrintSetting{Kind: PrintSettingProperty, Name: spec.Name, Children: children}, nil
}

// printBuildKeywordOptions 校验并构造公共关键字Option列表及默认选项下标，allowed为nil时校验合法NCName
// 入参: values 选项本地名列表, defaultValue 默认选项名，空表示首项, allowed 允许的关键字集合，nil表示接受任意合法NCName
// 返回: []PrintSetting Option列表, int 默认下标, error 非法或重复选项错误
func printBuildKeywordOptions(values []string, defaultValue string, allowed []string) ([]PrintSetting, int, error) {
	options := make([]PrintSetting, 0, len(values))
	seen := make(map[string]bool, len(values))
	defIdx := -1
	for _, name := range values {
		if seen[name] || (len(allowed) > 0 && !slices.Contains(allowed, name)) || (len(allowed) == 0 && !xmlNCName(name)) {
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

// printBuildQNameScored 构造携带QName值的公共ScoredProperty节点
// 入参: local 公共关键字本地名称, value 展开名称
// 返回: PrintSetting ScoredProperty节点
func printBuildQNameScored(local string, value xml.Name) PrintSetting {
	return PrintSetting{
		Kind: PrintSettingScoredProperty,
		Name: xml.Name{Space: printKeywordsNS, Local: local},
		Children: []PrintSetting{{
			Kind:  PrintSettingValue,
			Value: &PrintValue{Type: xml.Name{Space: printValueNS, Local: "QName"}, QName: value},
		}},
	}
}

// printUnitsToMicronsChecked 将九十六分之一英寸单位安全换算为64位微米整数，防非有限数或int64溢出
// 入参: units 九十六分之一英寸坐标或长度
// 返回: int64 精确微米整数, error 非有限或溢出错误
func printUnitsToMicronsChecked(units float64) (int64, error) {
	if !geometryFinite(units) {
		return 0, fmt.Errorf("%w: non-finite print micron value", ErrInvalid)
	}
	scaled := math.Round(units / printMicronUnit)
	if !geometryFinite(scaled) || scaled < float64(math.MinInt64) || scaled >= float64(math.MaxInt64) {
		return 0, fmt.Errorf("%w: print micron conversion overflows int64", ErrInvalid)
	}
	return int64(scaled), nil
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
	configuration, err := printSettingsOptions(context.Background(), nil)
	if err != nil {
		return nil, err
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
	if spec.RollLengthMicrons < 0 {
		return nil, fmt.Errorf("%w: negative roll media length", ErrInvalid)
	}
	if spec.MediaStandardName != "" {
		dims, ok := printMediaSizes[spec.MediaStandardName]
		if !ok {
			return nil, fmt.Errorf("%w: unsupported standard media %s", ErrInvalid, spec.MediaStandardName)
		}
		if dims[1] == 0 {
			if spec.RollLengthMicrons <= 0 {
				return nil, fmt.Errorf("%w: roll media %s requires positive RollLengthMicrons", ErrInvalid, spec.MediaStandardName)
			}
			elements = append(elements, PrintSetting{
				Kind: PrintSettingFeature,
				Name: xml.Name{Space: printKeywordsNS, Local: "PageMediaSize"},
				Children: []PrintSetting{{
					Kind: PrintSettingOption,
					Name: xml.Name{Space: printKeywordsNS, Local: spec.MediaStandardName},
					Children: []PrintSetting{
						printBuildIntScored("MediaSizeWidth", int64(dims[0])),
						printBuildRefScored("MediaSizeHeight", xml.Name{Space: printKeywordsNS, Local: "PageMediaSizeMediaSizeHeight"}),
					},
				}},
			})
			addIntParam("PageMediaSizeMediaSizeHeight", spec.RollLengthMicrons)
		} else {
			if spec.RollLengthMicrons != 0 {
				return nil, fmt.Errorf("%w: RollLengthMicrons only applies to roll media", ErrInvalid)
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
		}
	} else if spec.RollLengthMicrons != 0 {
		return nil, fmt.Errorf("%w: RollLengthMicrons requires a standard roll MediaStandardName", ErrInvalid)
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
		if !geometryFinite(spec.Resolution.X, spec.Resolution.Y) || spec.Resolution.X <= 0 || spec.Resolution.Y <= 0 || spec.Resolution.X > float64(math.MaxInt64/2) || spec.Resolution.Y > float64(math.MaxInt64/2) {
			return nil, fmt.Errorf("%w: invalid ticket resolution", ErrInvalid)
		}
		if spec.Resolution.Qualitative != "" && !xmlNCName(spec.Resolution.Qualitative) {
			return nil, fmt.Errorf("%w: invalid ticket resolution qualitative %s", ErrInvalid, spec.Resolution.Qualitative)
		}
		rx, ry := int64(math.Round(spec.Resolution.X)), int64(math.Round(spec.Resolution.Y))
		if rx <= 0 || ry <= 0 {
			return nil, fmt.Errorf("%w: invalid ticket resolution", ErrInvalid)
		}
		local := fmt.Sprintf("Res%dx%d", rx, ry)
		if rx == ry {
			local = fmt.Sprintf("Res%d", rx)
		}
		resChildren := []PrintSetting{
			printBuildIntScored("ResolutionX", rx),
			printBuildIntScored("ResolutionY", ry),
		}
		if spec.Resolution.Qualitative != "" {
			resChildren = append(resChildren, printBuildQNameScored("QualitativeResolution", xml.Name{Space: printKeywordsNS, Local: spec.Resolution.Qualitative}))
		}
		elements = append(elements, PrintSetting{
			Kind: PrintSettingFeature,
			Name: xml.Name{Space: printKeywordsNS, Local: "PageResolution"},
			Children: []PrintSetting{{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printBuilderNS, Local: local},
				Children: resChildren,
			}},
		})
	}
	if spec.Orientation != "" {
		if !slices.Contains(printAllowedOrientations, spec.Orientation) {
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
		if !slices.Contains(printAllowedMirrorImages, spec.MirrorImage) {
			return nil, fmt.Errorf("%w: invalid ticket mirror image %s", ErrInvalid, spec.MirrorImage)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageMirrorImage"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.MirrorImage}}},
		})
	}
	if spec.ScaleOffsetAlignment != "" {
		if !slices.Contains(printAllowedScaleOffsetAlignments, spec.ScaleOffsetAlignment) {
			return nil, fmt.Errorf("%w: invalid ticket ScaleOffsetAlignment %s", ErrInvalid, spec.ScaleOffsetAlignment)
		}
	}
	if spec.Scaling != "" || spec.ScaleOffsetAlignment != "" {
		var featChildren []PrintSetting
		if spec.Scaling != "" {
			if !slices.Contains(printAllowedScalings, spec.Scaling) {
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
			featChildren = append(featChildren, PrintSetting{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Scaling}, Children: optChildren})
		}
		if spec.ScaleOffsetAlignment != "" {
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
	if spec.ColorManagement != "" {
		if !slices.Contains(printAllowedColorManagements, spec.ColorManagement) {
			return nil, fmt.Errorf("%w: invalid ticket color management %s", ErrInvalid, spec.ColorManagement)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageColorManagement"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.ColorManagement}}},
		})
	}
	if spec.RenderingIntent != "" {
		if !slices.Contains(printAllowedRenderingIntents, spec.RenderingIntent) {
			return nil, fmt.Errorf("%w: invalid ticket rendering intent %s", ErrInvalid, spec.RenderingIntent)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageICMRenderingIntent"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.RenderingIntent}}},
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
		if !slices.Contains(printAllowedOutputQualities, spec.OutputQuality) {
			return nil, fmt.Errorf("%w: invalid ticket output quality %s", ErrInvalid, spec.OutputQuality)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PageOutputQuality"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.OutputQuality}}},
		})
	}
	if spec.PhotoPrintingIntent != "" {
		if !slices.Contains(printAllowedPhotoPrintingIntents, spec.PhotoPrintingIntent) {
			return nil, fmt.Errorf("%w: invalid ticket photo printing intent %s", ErrInvalid, spec.PhotoPrintingIntent)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "PagePhotoPrintingIntent"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PhotoPrintingIntent}}},
		})
	}
	for _, item := range []struct {
		feature string
		option  string
	}{
		{"JobInputBin", spec.JobInputBin},
		{"DocumentInputBin", spec.DocumentInputBin},
		{"PageInputBin", spec.PageInputBin},
		{"JobOutputBin", spec.JobOutputBin},
		{"DocumentOutputBin", spec.DocumentOutputBin},
		{"PageOutputBin", spec.PageOutputBin},
		{"PageMediaType", spec.MediaType},
	} {
		if item.option == "" {
			continue
		}
		if !xmlNCName(item.option) {
			return nil, fmt.Errorf("%w: invalid ticket %s option %s", ErrInvalid, item.feature, item.option)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: item.feature},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: item.option}}},
		})
	}
	if spec.Watermark != nil {
		wm := spec.Watermark
		if wm.Text == "" || utf8.RuneCountInString(wm.Text) > printWatermarkTextLimit || !geometryFinite(wm.Origin.X, wm.Origin.Y, wm.FontSize, wm.Angle, wm.Transparency) || wm.FontSize <= 0 || wm.Angle < 0 || wm.Angle > 359 || wm.Transparency < 0 || wm.Transparency > 100 {
			return nil, fmt.Errorf("%w: invalid ticket watermark", ErrInvalid)
		}
		scaledPt := math.Round(wm.FontSize * 72 / 96.0)
		if !geometryFinite(scaledPt) || scaledPt >= float64(math.MaxInt64) {
			return nil, fmt.Errorf("%w: invalid ticket watermark font size", ErrInvalid)
		}
		fontSizePt := int64(scaledPt)
		if fontSizePt < 1 {
			fontSizePt = 1
		}
		originX, err := printUnitsToMicronsChecked(wm.Origin.X)
		if err != nil {
			return nil, err
		}
		originY, err := printUnitsToMicronsChecked(wm.Origin.Y)
		if err != nil {
			return nil, err
		}
		optChildren := []PrintSetting{
			printBuildRefScored("OriginWidth", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginWidth"}),
			printBuildRefScored("OriginHeight", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkOriginHeight"}),
			printBuildRefScored("Angle", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextAngle"}),
			printBuildRefScored("FontSize", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextFontSize"}),
			printBuildRefScored("FontColor", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextColor"}),
			printBuildRefScored("Text", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTextText"}),
		}
		addIntParam("PageWatermarkOriginWidth", originX)
		addIntParam("PageWatermarkOriginHeight", originY)
		addIntParam("PageWatermarkTextAngle", int64(math.Round(wm.Angle)))
		addIntParam("PageWatermarkTextFontSize", fontSizePt)
		addStringParam("PageWatermarkTextColor", fmt.Sprintf("#%02X%02X%02X%02X", wm.Color.A, wm.Color.R, wm.Color.G, wm.Color.B))
		addStringParam("PageWatermarkTextText", wm.Text)
		if wm.HasTransparency || wm.Transparency > 0 {
			optChildren = append(optChildren, printBuildRefScored("Transparency", xml.Name{Space: printKeywordsNS, Local: "PageWatermarkTransparency"}))
			addIntParam("PageWatermarkTransparency", int64(math.Round(wm.Transparency)))
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
		if !slices.Contains(printAllowedCollateModes, spec.Collate) {
			return nil, fmt.Errorf("%w: invalid ticket collate %s", ErrInvalid, spec.Collate)
		}
		collateFeat := "JobCollateAllDocuments"
		if spec.DocumentCollate == "" && spec.DocumentCopies > 0 && spec.Copies == 0 {
			collateFeat = "DocumentCollate"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: collateFeat},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Collate}}},
		})
	}
	if spec.DocumentCollate != "" {
		if !slices.Contains(printAllowedCollateModes, spec.DocumentCollate) {
			return nil, fmt.Errorf("%w: invalid ticket document collate %s", ErrInvalid, spec.DocumentCollate)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "DocumentCollate"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.DocumentCollate}}},
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
		duplexFeat := "DocumentDuplex"
		if spec.JobLevelDuplex {
			duplexFeat = "JobDuplexAllDocumentsContiguously"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: duplexFeat},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Duplex.String()}, Children: optChildren}},
		})
	}
	if spec.NUp < 0 {
		return nil, fmt.Errorf("%w: negative ticket NUp", ErrInvalid)
	}
	if spec.PresentationDirection != "" {
		if !slices.Contains(printAllowedPresentationDirections, spec.PresentationDirection) {
			return nil, fmt.Errorf("%w: invalid ticket presentation direction %s", ErrInvalid, spec.PresentationDirection)
		}
	}
	if spec.NUp > 0 || spec.PresentationDirection != "" {
		var featChildren []PrintSetting
		if spec.NUp > 0 {
			featChildren = append(featChildren, PrintSetting{
				Kind:     PrintSettingOption,
				Name:     xml.Name{Space: printBuilderNS, Local: fmt.Sprintf("PagesPerSheet%d", spec.NUp)},
				Children: []PrintSetting{printBuildIntScored("PagesPerSheet", int64(spec.NUp))},
			})
		}
		if spec.PresentationDirection != "" {
			featChildren = append(featChildren, PrintSetting{
				Kind:     PrintSettingFeature,
				Name:     xml.Name{Space: printKeywordsNS, Local: "PresentationDirection"},
				Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PresentationDirection}}},
			})
		}
		nupFeat := "DocumentNUp"
		if spec.JobLevelNUp {
			nupFeat = "JobNUpAllDocumentsContiguously"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: nupFeat},
			Children: featChildren,
		})
	}
	if spec.PageOrder != "" {
		if !slices.Contains(printAllowedPageOrders, spec.PageOrder) {
			return nil, fmt.Errorf("%w: invalid ticket page order %s", ErrInvalid, spec.PageOrder)
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: "JobPageOrder"},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.PageOrder}}},
		})
	}
	if spec.PageRanges != "" {
		if utf8.RuneCountInString(spec.PageRanges) > printWatermarkTextLimit {
			return nil, fmt.Errorf("%w: ticket page ranges exceed limit", ErrInvalid)
		}
		if _, err := parsePrintPageRangeSpans(spec.PageRanges, configuration); err != nil {
			return nil, err
		}
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
			gutterMicrons, err := printUnitsToMicronsChecked(spec.Finishing.Gutter)
			if err != nil {
				return nil, err
			}
			optChildren = append(optChildren, printBuildIntScored("BindingGutter", gutterMicrons))
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: featName},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Finishing.Binding.String()}, Children: optChildren}},
		})
	}
	if spec.Staple != "" {
		if !slices.Contains(printAllowedStapleOptions, spec.Staple) {
			return nil, fmt.Errorf("%w: invalid ticket staple %s", ErrInvalid, spec.Staple)
		}
		featName := "DocumentStaple"
		if spec.JobLevelFinishing {
			featName = "JobStapleAllDocuments"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: featName},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.Staple}}},
		})
	}
	if spec.HolePunch != "" {
		if !slices.Contains(printAllowedHolePunchOptions, spec.HolePunch) {
			return nil, fmt.Errorf("%w: invalid ticket hole punch %s", ErrInvalid, spec.HolePunch)
		}
		featName := "DocumentHolePunch"
		if spec.JobLevelFinishing {
			featName = "JobHolePunch"
		}
		elements = append(elements, PrintSetting{
			Kind:     PrintSettingFeature,
			Name:     xml.Name{Space: printKeywordsNS, Local: featName},
			Children: []PrintSetting{{Kind: PrintSettingOption, Name: xml.Name{Space: printKeywordsNS, Local: spec.HolePunch}}},
		})
	}
	for _, custom := range spec.CustomFeatures {
		feat, err := printBuildCustomTicketFeature(custom)
		if err != nil {
			return nil, err
		}
		elements = append(elements, feat)
	}
	for _, propSpec := range spec.CustomProperties {
		prop, err := printBuildCustomProperty(propSpec)
		if err != nil {
			return nil, err
		}
		elements = append(elements, prop)
	}
	for _, paramSpec := range spec.CustomParameters {
		paramInit, err := printBuildCustomParameterInit(paramSpec)
		if err != nil {
			return nil, err
		}
		params = append(params, paramInit)
	}
	elements = append(elements, params...)
	return validatePrintSettingsModel(&PrintSettings{Version: version, Elements: elements}, configuration, printDocumentTicket)
}

// DerivePrintCapabilities 执行Windows V4 PDC核心派生：将PSF2 PDC转换为PSF1 PrintCapabilities，结合基准票据计算动态PageImageableSize、标注约束并输出规范化默认PrintTicket
// 入参: ctx 取消Context，nil采用Background, pdc PSF2 PrintDeviceCapabilities结构, baseTicket 可选基准PrintTicket，nil按设备默认派生, opts 资源预算选项，Scope须为Unknown
// 返回: *PrintCapabilities 派生后的PSF1能力文档, *PrintSettings 规范化后的默认PSF1票据, error 结构、能力、预算或取消错误
func DerivePrintCapabilities(ctx context.Context, pdc *PrintSettings, baseTicket *PrintSettings, opts *PrintSettingsOptions) (*PrintCapabilities, *PrintSettings, error) {
	var deriveOpts *PrintDeriveOptions
	if opts != nil {
		deriveOpts = &PrintDeriveOptions{Settings: *opts}
	}
	return DerivePrintCapabilitiesWithOptions(ctx, pdc, baseTicket, deriveOpts)
}

// DerivePrintCapabilitiesWithOptions 执行Windows V4 PDC核心派生并支持可选自定义动态约束回调，回调执行后会重新校验能力文档合法性
// 入参: ctx 取消Context，nil采用Background, pdc PSF2 PrintDeviceCapabilities结构, baseTicket 可选基准PrintTicket，nil按设备默认派生, opts 资源预算与自定义约束回调选项，nil采用默认值
// 返回: *PrintCapabilities 派生后的PSF1能力文档, *PrintSettings 规范化后的默认PSF1票据, error 结构、能力、回调、预算或取消错误
func DerivePrintCapabilitiesWithOptions(ctx context.Context, pdc *PrintSettings, baseTicket *PrintSettings, opts *PrintDeriveOptions) (*PrintCapabilities, *PrintSettings, error) {
	var settingsOpts *PrintSettingsOptions
	var customConstraints func(context.Context, *PrintSettings, *PrintCapabilities) error
	if opts != nil {
		copySettings := opts.Settings
		settingsOpts = &copySettings
		customConstraints = opts.CustomConstraints
	}
	configuration, err := printSettingsOptions(ctx, settingsOpts)
	if err != nil {
		return nil, nil, err
	}
	if pdc == nil || configuration.Scope != PrintScopeUnknown {
		return nil, nil, fmt.Errorf("%w: print capabilities derive parameters", ErrInvalid)
	}
	pdcModel, err := validatePrintSettingsModel(pdc, configuration, printDocumentDeviceCapabilities)
	if err != nil {
		return nil, nil, err
	}
	effectiveTicket, _, err := normalizePrintSettingsInternal(baseTicket, nil, pdcModel, printDocumentDeviceCapabilities, configuration, nil, true, false)
	if err != nil {
		return nil, nil, err
	}
	effectiveTicket.Version = 1
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
	capModel, err := validatePrintSettingsModel(&PrintSettings{Version: 1, Elements: capsElements}, configuration, printDocumentCapabilities)
	if err != nil {
		return nil, nil, err
	}
	derived := &PrintCapabilities{Version: capModel.Version, Elements: capModel.Elements}
	if customConstraints != nil {
		if err := customConstraints(configuration.context, printCloneSettings(effectiveTicket), derived); err != nil {
			return nil, nil, err
		}
		rechecked, err := validatePrintSettingsModel(&PrintSettings{Version: derived.Version, Elements: derived.Elements}, configuration, printDocumentCapabilities)
		if err != nil {
			return nil, nil, err
		}
		derived = &PrintCapabilities{Version: rechecked.Version, Elements: rechecked.Elements}
	}
	return derived, effectiveTicket, nil
}

// printExtractDeriveState 从规范化基准票据与PDC提取动态PageImageableSize（涵盖卷纸、自定义纸型与任意参数化介质）及约束判定状态
// 入参: ticket 有效基准票据, pdc 已校验PDC模型, options 已校验配置
// 返回: printDeriveState 派生状态
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
				if pdcOpt, area, found := printFindPDCMediaImageable(pdc, opt.Name); found {
					refW, refH := mediaW, mediaH
					dynamicDim := false
					okRef := true
					if wRef, hasWRef := printOptionScoredParamRef(pdcOpt, "MediaSizeWidth"); hasWRef {
						dynamicDim = true
						if defW, okW := printFindPDCParameterDefaultInt(pdc, wRef); okW && defW > 0 {
							refW = defW
						} else {
							okRef = false
						}
					}
					if hRef, hasHRef := printOptionScoredParamRef(pdcOpt, "MediaSizeHeight"); hasHRef {
						dynamicDim = true
						if defH, okH := printFindPDCParameterDefaultInt(pdc, hRef); okH && defH > 0 {
							refH = defH
						} else {
							okRef = false
						}
					}
					if dynamicDim && okRef && refW > 0 && refH > 0 && area[0] <= refW && area[1] <= refH && area[2] <= refW-area[0] && area[3] <= refH-area[1] {
						left, top := area[0], area[1]
						right, bottom := refW-area[0]-area[2], refH-area[1]-area[3]
						ox = min(left, mediaW)
						oy = min(top, mediaH)
						ew = max(int64(0), mediaW-ox-right)
						eh = max(int64(0), mediaH-oy-bottom)
					} else {
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
		if fin.Binding != PrintBindingNone {
			state.hasJobBind = true
		}
		if fin.Binding == PrintBindingBooklet {
			state.activeBooklet = true
		}
	}
	if fin, declared, err := control.binding("DocumentBinding"); err == nil && declared {
		if fin.Binding != PrintBindingNone {
			state.hasDocBind = true
		}
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
	if opt, _, err := control.option(ticket.Elements, "JobStapleAllDocuments"); err == nil && opt != nil && (!printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None") {
		state.hasJobStaple = true
	}
	if opt, _, err := control.option(ticket.Elements, "DocumentStaple"); err == nil && opt != nil && (!printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None") {
		state.hasDocStaple = true
	}
	if opt, _, err := control.option(ticket.Elements, "JobHolePunch"); err == nil && opt != nil && (!printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None") {
		state.hasJobHolePunch = true
	}
	if opt, _, err := control.option(ticket.Elements, "DocumentHolePunch"); err == nil && opt != nil && (!printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None") {
		state.hasDocHolePunch = true
	}
	return state
}

// printOptionScoredParamRef 查找Option中指定公共ScoredProperty的ParameterRef展开名称
// 入参: opt 介质Option节点, local 公共ScoredProperty本地名称
// 返回: xml.Name ParameterRef展开名称, bool 是否引用了参数
func printOptionScoredParamRef(opt PrintSetting, local string) (xml.Name, bool) {
	for _, child := range opt.Children {
		if child.Kind != PrintSettingScoredProperty || !printPublicKeywordSpace(child.Name.Space) || child.Name.Local != local {
			continue
		}
		_, ref := printScoredValue(child.Children)
		if ref != (xml.Name{}) {
			return ref, true
		}
	}
	return xml.Name{}, false
}

// printFindPDCParameterDefaultInt 在PDC根级ParameterDef中查找指定整数参数的DefaultValue
// 入参: pdc 已校验PDC模型, target 目标参数展开名称
// 返回: int64 参数默认值, bool 是否找到合法整数默认值
func printFindPDCParameterDefaultInt(pdc *PrintSettings, target xml.Name) (int64, bool) {
	key := printCanonicalKey(target)
	for _, element := range pdc.Elements {
		if element.Kind != PrintSettingParameterDef || printCanonicalKey(element.Name) != key {
			continue
		}
		for _, prop := range element.Children {
			if prop.Kind != PrintSettingProperty || !printFrameworkSpace(prop.Name.Space) || prop.Name.Local != "DefaultValue" || len(prop.Children) != 1 || prop.Children[0].Value == nil {
				continue
			}
			n, err := strconv.ParseInt(strings.Trim(prop.Children[0].Value.Text, " \t\r\n"), 10, 64)
			if err == nil {
				return n, true
			}
		}
	}
	return 0, false
}

// printFindPDCMediaImageable 在PDC的PageMediaSize特性中查找指定纸型Option及其声明的PortraitImageableSize四元微米区域
// 入参: pdc 已校验PDC模型, optionName 纸型Option展开名称
// 返回: PrintSetting 匹配的PDC纸型Option, [4]int64 原点X、原点Y、宽、高微米值, bool 是否找到合法声明
func printFindPDCMediaImageable(pdc *PrintSettings, optionName xml.Name) (PrintSetting, [4]int64, bool) {
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
					if area, ok := printParseImageableArea(val.Text); ok {
						return opt, area, true
					}
				}
			}
		}
	}
	return PrintSetting{}, [4]int64{}, false
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
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasDocBind && !isNone || printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "Booklet" && (state.activeNUp > 1 || state.activePoster > 1) {
				constrained = true
			}
		case "DocumentBinding":
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasJobBind && !isNone || printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "Booklet" && (state.activeNUp > 1 || state.activePoster > 1) {
				constrained = true
			}
		case "JobNUpAllDocumentsContiguously":
			pages := printOptionScoredInt(*opt, "PagesPerSheet", nil)
			if state.hasDocNUp || (pages > 1 && (state.activeBooklet || state.activePoster > 1)) {
				constrained = true
			}
		case "DocumentNUp":
			pages := printOptionScoredInt(*opt, "PagesPerSheet", nil)
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
		case "JobStapleAllDocuments":
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasDocStaple && !isNone {
				constrained = true
			}
		case "DocumentStaple":
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasJobStaple && !isNone {
				constrained = true
			}
		case "JobHolePunch":
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasDocHolePunch && !isNone {
				constrained = true
			}
		case "DocumentHolePunch":
			isNone := printPublicKeywordSpace(opt.Name.Space) && opt.Name.Local == "None"
			if state.hasJobHolePunch && !isNone {
				constrained = true
			}
		case "PagePoster":
			sheets := printOptionScoredInt(*opt, "SheetsPerPage", nil)
			if sheets > 1 && (state.activeNUp > 1 || state.activeBooklet) {
				constrained = true
			}
		}
		if constrained {
			opt.Constraint = PrintConstraintSettings
		}
	}
}
