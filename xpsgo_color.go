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
	"cmp"
	"context"
	"encoding/binary"
	"fmt"
	"image/color"
	"math"
	"net/url"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"
	"unicode/utf8"
)

const (
	// ColorUnknown 表示未知源色彩空间
	ColorUnknown ColorSpace = iota
	// ColorSRGB 表示sRGB源色彩空间
	ColorSRGB
	// ColorScRGB 表示scRGB扩展线性色彩空间
	ColorScRGB
	// ColorContext 表示带ICC配置文件引用的ContextColor色彩空间
	ColorContext
)

// renderSRGB 等常量表示合成工作色彩空间
const (
	renderSRGB renderColorSpace = iota
	renderScRGB
)

// iccCurveIdentity 等常量表示ICC一维传递曲线编码类别
const (
	iccCurveIdentity iccCurveKind = iota
	iccCurveGamma
	iccCurveSampled
	iccCurveParametric
)

// iccStageMatrix 等常量表示ICC多阶段色彩转换步骤类型
const (
	iccStageMatrix iccStageKind = iota
	iccStageCurves
	iccStageCLUT
	iccStageFloatMatrix
	iccStageSegmentedCurves
)

// iccMaxChannels 等常量限制ICC色彩通道、管线元素、命名色条目与色彩解析缓存上限
const (
	iccMaxChannels           = 15
	iccMaxElements           = 4096
	iccMaxNamedColors        = 1 << 20
	iccMinFloat32            = 1.1754943508222875e-38
	colorResolverMaxProfiles = 256
)

// cicpBT2100Red 等常量定义ITU-R BT.2100亮度权重与PQ、HLG传递特性常数
const (
	cicpBT2100Red   = 0.2627
	cicpBT2100Green = 0.6780
	cicpBT2100Blue  = 0.0593
	cicpPQC1        = 107.0 / 128
	cicpPQC2        = 2413.0 / 128
	cicpPQC3        = 2392.0 / 128
	cicpPQM1        = 1305.0 / 8192
	cicpPQM2        = 2523.0 / 32
	cicpHLGA        = 0.17883277
	cicpHLGB        = 1 - 4*cicpHLGA
	cicpHLGC        = 0.5599107295295620
)

// colorDecimalPattern 匹配十进制颜色分量词法
var colorDecimalPattern = regexp.MustCompile(`^-?(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)$`)

var (
	// cicpBradford 保存Bradford色度适应变换矩阵
	cicpBradford = [9]float64{0.8951, 0.2664, -0.1614, -0.7502, 1.7135, 0.0367, 0.0389, -0.0685, 1.0296}
	// cicpBradfordInverse 保存Bradford色度适应逆矩阵
	cicpBradfordInverse, _ = iccInverseMatrix(cicpBradford)
	// cicpBT2020ToSRGB 保存BT.2020线性RGB到D65线性sRGB的转换矩阵
	cicpBT2020ToSRGB, _, _, _ = cicpPrimariesMatrix(9)
	// cicpSRGBToBT2020 保存D65线性sRGB到BT.2020线性RGB的转换矩阵
	cicpSRGBToBT2020, _ = iccInverseMatrix(cicpBT2020ToSRGB)
	// cicpBT2446SDRRho 保存BT.2446方法A中100 cd/m²输出的ρ减一
	cicpBT2446SDRRho = 32 * math.Pow(100.0/10000, 1/2.4)
	// cicpBT2446SDRLog 保存SDR的ρ对数
	cicpBT2446SDRLog = math.Log1p(cicpBT2446SDRRho)
)

// imageCICPTransform 保存已校验的H.273 CICP信号范围、线性化及基色转换参数
type imageCICPTransform struct {
	linearMatrix [9]float64
	hlgLuma      [3]float64
	offset       float64
	scale        float64
	primaries    uint8
	transfer     uint8
	hdr          bool
	peakNits     float64
}

// imageGammaChromaTransform 保存已校验的PNG gAMA线性化幂次与cHRM到D65线性sRGB转换矩阵
type imageGammaChromaTransform struct {
	hasGamma     bool
	invGamma     float64
	hasMatrix    bool
	linearMatrix [9]float64
}

// ColorSpace 表示颜色的源色彩空间
type ColorSpace uint8

// Color 保存非预乘颜色、源分量、原始词法及尚未解析的ICC部件引用
type Color struct {
	Space      ColorSpace
	Alpha      float64
	Components []float64
	ProfileURI string
	Raw        string
}

// ColorResolveOptions 设置颜色解析的ICC渲染意图、打印输出色彩模式及反相开关
type ColorResolveOptions struct {
	Intent     RenderingIntent
	PrintColor PrintColorMode
	Negative   bool
}

// ResolvedSpotColor 保存ICC命名专色表（nmcl）中单个命中的专色名称、有效色调、连接空间坐标、满墨参考设备坐标及按色调缩放后的有效设备坐标
type ResolvedSpotColor struct {
	Name       string
	Tint       float64
	PCS        [3]float64
	FullDevice []float64
	Device     []float64
}

// ResolvedColor 保存颜色经ICC与打印色彩策略解析后的精确线性值、量化sRGB、源色彩空间、专色、有效设备分量及灰度结果
type ResolvedColor struct {
	Space            ColorSpace
	ColorSpace       string
	ProfilePart      string
	ProfileSpace     string
	SpotName         string
	SpotColors       []ResolvedSpotColor
	DeviceComponents []float64
	Components       []float64
	Alpha            float64
	SRGB             color.NRGBA
	SRGB16           color.NRGBA64
	Linear           [3]float64
	CMYK             [4]float64
	HasCMYK          bool
	Gray             float64
}

// colorResolverEntry 保存单个规范化ICC部件对应的已解析配置与四个标准渲染意图的变换缓存
type colorResolverEntry struct {
	profile    *iccProfile
	transforms [4]*iccTransform
}

// ColorResolver 提供并发安全且有界的ICC配置与变换缓存，用于高频复用ContextColor颜色解析
type ColorResolver struct {
	reader     *Reader
	view       *streamPageView
	mu         sync.RWMutex
	entries    map[string]*colorResolverEntry
	order      []string
	maxEntries int
}

// renderColorSpace 表示页面与图层的合成工作色彩空间
type renderColorSpace uint8

// renderColor 保存工作空间内的预乘颜色，scRGB允许扩展分量，透明黑为零值
type renderColor struct {
	r float64
	g float64
	b float64
	a float64
}

// iccNamedColor 保存命名色的名称、前后缀、连接空间坐标、相对色度XYZ及可选设备坐标
type iccNamedColor struct {
	name   string
	prefix string
	suffix string
	pcs    [3]float64
	xyz    [3]float64
	device []float64
}

// iccCurveKind 表示一维传递曲线的编码类型
type iccCurveKind uint8

// iccCurve 保存只读采样值或参数化曲线，不为大采样表重复分配浮点数组
type iccCurve struct {
	kind       iccCurveKind
	function   uint16
	parameters [7]float64
	values     []byte
	precision  int
}

// iccInverseCurve 保存已验证TRC的端点和分段值，避免逐像素重复计算准备阶段的幂函数
type iccInverseCurve struct {
	curve iccCurve
	first float64
	last  float64
	upper float64
}

// iccFloatCurveSegment 保存多阶段浮点曲线的单个公式段或采样段，采样字节共享只读配置存储
type iccFloatCurveSegment struct {
	sampled    bool
	function   uint16
	parameters [5]float64
	values     []byte
	startValue float64
}

// iccSegmentedCurve 保存按断点有序划分的浮点分段传递曲线
type iccSegmentedCurve struct {
	breakpoints []float64
	segments    []iccFloatCurveSegment
}

// iccStageKind 表示色彩转换中的矩阵、逐通道曲线或多维查找表
type iccStageKind uint8

// iccStage 保存一个转换阶段，查找表字节与原配置文件共享只读存储
type iccStage struct {
	kind        iccStageKind
	matrix      [12]float64
	floatMatrix []float64
	curves      []iccCurve
	segCurves   []iccSegmentedCurve
	grid        []int
	data        []byte
	precision   int
	inputs      int
	outputs     int
}

// iccPipeline 保存按处理顺序排列的转换阶段，整数管线采用归一化编码而浮点管线保留无裁剪数值
type iccPipeline struct {
	inputs         int
	outputs        int
	stages         []iccStage
	legacyLab      bool
	floating       bool
	inputPrecision int
}

// iccStageRange 记录处理元素范围，只有完全相同的曲线定义允许共享
type iccStageRange struct {
	offset uint64
	size   uint64
	curve  bool
}

// String 返回源色彩空间的文本表示
// 返回: string 色彩空间名称
func (s ColorSpace) String() string {
	switch s {
	case ColorUnknown:
		return "Unknown"
	case ColorSRGB:
		return "sRGB"
	case ColorScRGB:
		return "scRGB"
	case ColorContext:
		return "ContextColor"
	default:
		return fmt.Sprintf("ColorSpace(%d)", s)
	}
}

// ResolvePartURI 按源部件URI解析并规范化包内相对或绝对引用，拒绝外部URI、查询、片段及越界路径
// 入参: basePart 源部件的包根URI，包根使用/, relURI 相对或包根URI
// 返回: string 规范化包根URI, error 引用、编码或越界错误
func ResolvePartURI(basePart, relURI string) (string, error) {
	return resolvePart(basePart, relURI)
}

// NewColorResolver 创建绑定当前阅读器的并发安全有界ICC缓存颜色解析器
// 返回: *ColorResolver 可跨页高频复用的颜色解析器
func (r *Reader) NewColorResolver() *ColorResolver {
	return &ColorResolver{
		reader:     r,
		entries:    make(map[string]*colorResolverEntry),
		maxEntries: colorResolverMaxProfiles,
	}
}

// newStreamColorResolver 创建绑定流式视图生命周期守卫的并发安全有界ICC缓存颜色解析器
// 入参: view 临时流式视图状态，回调结束后将关闭
// 返回: *ColorResolver 受视图生命周期守卫保护的颜色解析器
func newStreamColorResolver(view *streamPageView) *ColorResolver {
	return &ColorResolver{
		view:       view,
		entries:    make(map[string]*colorResolverEntry),
		maxEntries: colorResolverMaxProfiles,
	}
}

// ResolveColor 经有界ICC缓存解析sRGB、scRGB或ContextColor，避免重复读取和构建同一配置文件变换
// 入参: ctx 取消Context，nil采用Background, basePart 源部件包根URI, value 待解析颜色, opts 色彩解析选项，nil采用默认值
// 返回: ResolvedColor 解析后的多空间颜色及专色元数据, error 状态、参数、部件、配置、转换、关闭或取消错误
func (c *ColorResolver) ResolveColor(ctx context.Context, basePart string, value Color, opts *ColorResolveOptions) (ResolvedColor, error) {
	if c == nil {
		return ResolvedColor{}, fmt.Errorf("%w: color resolver has no reader", ErrInvalid)
	}
	if c.view != nil {
		r, resolveCtx, cleanup, err := c.view.prepareCall(ctx)
		if err != nil {
			return ResolvedColor{}, err
		}
		defer cleanup()
		return r.resolveColorWithCache(resolveCtx, basePart, value, opts, c)
	}
	if c.reader == nil {
		return ResolvedColor{}, fmt.Errorf("%w: color resolver has no reader", ErrInvalid)
	}
	return c.reader.resolveColorWithCache(ctx, basePart, value, opts, c)
}

// lookup 在读锁下查询已缓存的ICC配置及对应意图变换
// 入参: key 规范化小写部件名, intent ICC意图编号（0至3）
// 返回: *iccProfile 缓存配置，未命中为nil, *iccTransform 缓存变换，未命中为nil
func (c *ColorResolver) lookup(key string, intent uint32) (*iccProfile, *iccTransform) {
	c.mu.RLock()
	entry := c.entries[key]
	if entry == nil {
		c.mu.RUnlock()
		return nil, nil
	}
	profile := entry.profile
	transform := entry.transforms[intent]
	c.mu.RUnlock()
	return profile, transform
}

// store 在写锁下写入已解析ICC配置与对应意图变换，超出条目上限时按先进先出淘汰最旧项
// 入参: key 规范化小写部件名, intent ICC意图编号（0至3）, profile 已解析配置, transform 已准备变换
func (c *ColorResolver) store(key string, intent uint32, profile *iccProfile, transform *iccTransform) {
	c.mu.Lock()
	defer c.mu.Unlock()
	entry := c.entries[key]
	if entry == nil {
		for len(c.entries) >= c.maxEntries && len(c.order) > 0 {
			oldest := c.order[0]
			copy(c.order, c.order[1:])
			c.order[len(c.order)-1] = ""
			c.order = c.order[:len(c.order)-1]
			delete(c.entries, oldest)
		}
		entry = &colorResolverEntry{profile: profile}
		c.entries[key] = entry
		c.order = append(c.order, key)
	}
	entry.transforms[intent] = transform
}

// ResolveColor 解析sRGB、scRGB及含ICC配置的ContextColor，支持按意图、负片及灰度黑白打印策略转换
// 源为四通道CMYK配置且未启用反相或灰度单色转换时在CMYK保留原始源分量并置HasCMYK为真
// 入参: ctx 取消Context，nil采用Background, basePart 源部件包根URI, value 待解析颜色, opts 色彩解析选项，nil采用默认值
// 返回: ResolvedColor 解析后的多空间颜色结果, error 状态、参数、部件、配置、转换或取消错误
func (r *Reader) ResolveColor(ctx context.Context, basePart string, value Color, opts *ColorResolveOptions) (ResolvedColor, error) {
	return r.resolveColorWithCache(ctx, basePart, value, opts, nil)
}

// finalizeResolvedColor 按打印色彩策略完成线性RGB后处理并填充解析颜色的线性、灰度及sRGB字段
// 入参: result 待填充解析颜色指针, linear 非预乘线性RGB分量, opts 色彩解析选项
// 返回: error 数值范围错误
func finalizeResolvedColor(result *ResolvedColor, linear [3]float64, opts ColorResolveOptions) error {
	outLinear, luminance, err := applyPrintLinearColor(linear, opts.Negative, opts.PrintColor)
	if err != nil {
		return err
	}
	srgb := [3]float64{
		renderLinearToSRGB(colorClamp(outLinear[0])),
		renderLinearToSRGB(colorClamp(outLinear[1])),
		renderLinearToSRGB(colorClamp(outLinear[2])),
	}
	result.Linear = outLinear
	result.Gray = renderLinearToSRGB(luminance)
	result.SRGB = color.NRGBA{
		R: colorQuantize8(srgb[0]),
		G: colorQuantize8(srgb[1]),
		B: colorQuantize8(srgb[2]),
		A: colorQuantize8(result.Alpha),
	}
	result.SRGB16 = color.NRGBA64{
		R: colorQuantize16(srgb[0]),
		G: colorQuantize16(srgb[1]),
		B: colorQuantize16(srgb[2]),
		A: colorQuantize16(result.Alpha),
	}
	return nil
}

// resolveLocalColor 在无需Reader及ICC配置文件的纯内存路径下解析sRGB与scRGB颜色
// 入参: value 待解析颜色, opts 色彩解析选项
// 返回: ResolvedColor 解析后的多空间颜色结果, error 参数、色彩空间、能力或数值范围错误
func resolveLocalColor(value Color, opts ColorResolveOptions) (ResolvedColor, error) {
	if !geometryFinite(value.Alpha) || value.Alpha < 0 || value.Alpha > 1 {
		return ResolvedColor{}, fmt.Errorf("%w: invalid color alpha", ErrInvalid)
	}
	for _, component := range value.Components {
		if !geometryFinite(component) {
			return ResolvedColor{}, fmt.Errorf("%w: non-finite color component", ErrInvalid)
		}
	}
	result := ResolvedColor{
		Space: value.Space,
		Alpha: value.Alpha,
	}
	var linear [3]float64
	switch value.Space {
	case ColorSRGB:
		if len(value.Components) != 3 {
			return ResolvedColor{}, fmt.Errorf("%w: sRGB color requires three components", ErrInvalid)
		}
		for i, component := range value.Components {
			if component < 0 || component > 1 {
				return ResolvedColor{}, fmt.Errorf("%w: sRGB component outside unit range", ErrInvalid)
			}
			linear[i] = renderSRGBToLinear(component)
		}
		result.ColorSpace = "sRGB"
	case ColorScRGB:
		if len(value.Components) != 3 {
			return ResolvedColor{}, fmt.Errorf("%w: scRGB color requires three components", ErrInvalid)
		}
		linear = [3]float64{value.Components[0], value.Components[1], value.Components[2]}
		result.ColorSpace = "scRGB"
	case ColorContext:
		return ResolvedColor{}, fmt.Errorf("%w: context color requires Reader or ColorResolver", ErrUnsupported)
	default:
		return ResolvedColor{}, fmt.Errorf("%w: unsupported color space", ErrInvalid)
	}
	if err := finalizeResolvedColor(&result, linear, opts); err != nil {
		return ResolvedColor{}, err
	}
	result.Components = slices.Clone(value.Components)
	return result, nil
}

// resolveColorWithCache 共用颜色解析管线，支持可选有界ICC缓存并填充专色与设备分量元数据
// 入参: ctx 取消Context，nil采用Background, basePart 源部件包根URI, value 待解析颜色, opts 色彩解析选项, cache 可选有界缓存
// 返回: ResolvedColor 解析后的多空间颜色结果, error 状态、参数、部件、配置、转换或取消错误
func (r *Reader) resolveColorWithCache(ctx context.Context, basePart string, value Color, opts *ColorResolveOptions, cache *ColorResolver) (ResolvedColor, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return ResolvedColor{}, err
	}
	if err := r.readLock(); err != nil {
		return ResolvedColor{}, err
	}
	defer r.mu.RUnlock()
	var cfg ColorResolveOptions
	if opts != nil {
		cfg = *opts
	}
	if cfg.Intent > IntentAbsoluteColorimetric || cfg.PrintColor > PrintColorMonochrome {
		return ResolvedColor{}, fmt.Errorf("%w: color resolve options", ErrInvalid)
	}
	if value.Space != ColorContext {
		return resolveLocalColor(value, cfg)
	}
	if !geometryFinite(value.Alpha) || value.Alpha < 0 || value.Alpha > 1 {
		return ResolvedColor{}, fmt.Errorf("%w: invalid color alpha", ErrInvalid)
	}
	for _, component := range value.Components {
		if !geometryFinite(component) {
			return ResolvedColor{}, fmt.Errorf("%w: non-finite color component", ErrInvalid)
		}
	}
	result := ResolvedColor{
		Space: value.Space,
		Alpha: value.Alpha,
	}
	sourceBase := basePart
	if sourceBase == "" && strings.HasPrefix(value.ProfileURI, "/") {
		sourceBase = "/"
	}
	part, err := resolvePart(sourceBase, value.ProfileURI)
	if err != nil {
		return ResolvedColor{}, err
	}
	iccIntent := uint32(1)
	if cfg.Intent != IntentDefault {
		iccIntent = uint32(cfg.Intent - 1)
	}
	key := strings.ToLower(part)
	var profile *iccProfile
	var transform *iccTransform
	if cache != nil {
		profile, transform = cache.lookup(key, iccIntent)
	}
	if profile == nil {
		media, err := r.pkg.contentType(part)
		if err != nil {
			return ResolvedColor{}, wrapPartError(part, "", err)
		}
		if !requiredResourceMedia(requiredProfile, media) {
			return ResolvedColor{}, wrapPartError(part, "", fmt.Errorf("%w: color profile content type %q", ErrInvalid, media))
		}
		data, err := r.pkg.readPartContext(ctx, part)
		if err != nil {
			return ResolvedColor{}, wrapPartError(part, "", err)
		}
		profile, err = parseICCProfile(data)
		if err != nil {
			return ResolvedColor{}, wrapPartError(part, "", err)
		}
	}
	if transform == nil {
		transform, err = prepareICCTransform(profile, iccIntent)
		if err != nil {
			return ResolvedColor{}, wrapPartError(part, "", err)
		}
		if cache != nil {
			cache.store(key, iccIntent, profile, transform)
		}
	}
	if len(value.Components) != transform.inputChannels() {
		return ResolvedColor{}, wrapPartError(part, "", fmt.Errorf("%w: context color channel count", ErrInvalid))
	}
	linear, err := transform.linearRGB(value.Components, false)
	if err != nil {
		return ResolvedColor{}, wrapPartError(part, "", err)
	}
	if err := finalizeResolvedColor(&result, linear, cfg); err != nil {
		return ResolvedColor{}, err
	}
	result.ProfilePart = part
	result.ProfileSpace = profile.space
	result.ColorSpace = strings.TrimSpace(profile.space)
	result.Components = slices.Clone(value.Components)
	postProcessed := cfg.Negative || cfg.PrintColor == PrintColorGrayscale || cfg.PrintColor == PrintColorMonochrome
	if profile.class == "nmcl" && len(transform.named) > 0 {
		if !postProcessed {
			result.SpotName, result.DeviceComponents, result.SpotColors = resolveICCNamedSpotMetadata(profile.space, transform.named, value.Components)
		}
	} else if !postProcessed {
		result.DeviceComponents = slices.Clone(value.Components)
	}
	if profile.space == "CMYK" && profile.class != "nmcl" && len(value.Components) == 4 && !postProcessed {
		result.CMYK = [4]float64{
			colorClamp(value.Components[0]),
			colorClamp(value.Components[1]),
			colorClamp(value.Components[2]),
			colorClamp(value.Components[3]),
		}
		result.HasCMYK = true
	}
	return result, nil
}

// resolveICCNamedSpotMetadata 根据命名色配置、源色彩空间与各色调分量提取完整专色名、当前色调有效设备坐标及结构化专色列表
// 加色空间（RGB/GRAY）按1-tint*(1-value)向纸白缩放，减色空间按value*tint缩放；全零tint时保留全部专色条目与对应有效设备坐标
// 入参: space 命名色配置色彩空间标识, named 命名色表条目, tints 各命名色色调分量
// 返回: string 命中的完整专色名, []float64 单专色当前色调有效设备坐标或nil, []ResolvedSpotColor 结构化专色列表
func resolveICCNamedSpotMetadata(space string, named []iccNamedColor, tints []float64) (string, []float64, []ResolvedSpotColor) {
	additive := space == "RGB " || space == "GRAY"
	makeSpot := func(entry iccNamedColor, tint float64) ResolvedSpotColor {
		var fullDev, effDev []float64
		if len(entry.device) > 0 {
			fullDev = slices.Clone(entry.device)
			effDev = make([]float64, len(entry.device))
			if additive {
				for i, value := range entry.device {
					effDev[i] = 1 - tint*(1-value)
				}
			} else if tint > 0 {
				for i, value := range entry.device {
					effDev[i] = value * tint
				}
			}
		}
		return ResolvedSpotColor{
			Name:       entry.prefix + entry.name + entry.suffix,
			Tint:       tint,
			PCS:        entry.pcs,
			FullDevice: fullDev,
			Device:     effDev,
		}
	}
	var spots []ResolvedSpotColor
	for i, entry := range named {
		if i < len(tints) {
			if tint := colorClamp(tints[i]); tint > 0 {
				spots = append(spots, makeSpot(entry, tint))
			}
		}
	}
	if len(spots) == 0 {
		spots = make([]ResolvedSpotColor, 0, len(named))
		for i, entry := range named {
			if i < len(tints) {
				spots = append(spots, makeSpot(entry, 0))
			}
		}
	}
	if len(spots) == 1 {
		return spots[0].Name, slices.Clone(spots[0].Device), spots
	}
	if len(spots) > 1 {
		names := make([]string, len(spots))
		for i, spot := range spots {
			names[i] = spot.Name
		}
		return strings.Join(names, ", "), nil, spots
	}
	return "", nil, nil
}

// applyPrintLinearColor 对非预乘线性RGB依次施加负片反相及灰度或黑白单色转换，并返回最终线性RGB与BT.709线性亮度
// 入参: linear 非预乘线性RGB分量, negative 是否启用负片反相, mode 打印输出色彩模式
// 返回: [3]float64 转换后的线性RGB分量, float64 归一化BT.709线性亮度, error 数值范围错误
func applyPrintLinearColor(linear [3]float64, negative bool, mode PrintColorMode) ([3]float64, float64, error) {
	if negative {
		for i := range 3 {
			linear[i] = renderSignedSRGBToLinear(1 - renderSignedLinearToSRGB(linear[i]))
		}
		if !geometryFinite(linear[0], linear[1], linear[2]) {
			return [3]float64{}, 0, fmt.Errorf("%w: negative color arithmetic", ErrLimit)
		}
	}
	luminance := colorClamp(0.2126*linear[0] + 0.7152*linear[1] + 0.0722*linear[2])
	if mode == PrintColorGrayscale || mode == PrintColorMonochrome {
		if mode == PrintColorMonochrome {
			if luminance >= 0.5 {
				luminance = 1
			} else {
				luminance = 0
			}
		}
		linear = [3]float64{luminance, luminance, luminance}
	}
	return linear, luminance, nil
}

// colorQuantize8 将归一化颜色或透明度分量四舍五入量化为八位无符号整数
// 入参: value 有限归一化分量
// 返回: uint8 八位量化结果
func colorQuantize8(value float64) uint8 {
	return uint8(math.Floor(colorClamp(value)*255 + 0.5))
}

// colorQuantize16 将归一化颜色或透明度分量四舍五入量化为十六位无符号整数
// 入参: value 有限归一化分量
// 返回: uint16 十六位量化结果
func colorQuantize16(value float64) uint16 {
	return uint16(math.Floor(colorClamp(value)*65535 + 0.5))
}

// ParseColor 解析sRGB、scRGB或ContextColor文本，不加载ICC配置文件或执行色彩转换
// sRGB、alpha及ContextColor分量裁剪到0至1，scRGB保留扩展分量，ContextColor允许1至8通道
// 入参: text 颜色属性文本
// 返回: Color 颜色数据, error 词法或引用错误
func ParseColor(text string) (Color, error) {
	s := strings.Trim(text, " \t\r\n")
	c := Color{Alpha: 1, Raw: text}
	switch {
	case strings.HasPrefix(s, "#"):
		if len(s) != 7 && len(s) != 9 {
			return Color{}, fmt.Errorf("%w: sRGB requires six or eight hexadecimal digits", ErrInvalid)
		}
		v, err := strconv.ParseUint(s[1:], 16, 32)
		if err != nil {
			return Color{}, fmt.Errorf("%w: invalid sRGB color %q", ErrInvalid, text)
		}
		c.Space = ColorSRGB
		c.Components = []float64{float64(v>>16&255) / 255, float64(v>>8&255) / 255, float64(v&255) / 255}
		if len(s) == 9 {
			c.Alpha = float64(v>>24) / 255
		}
	case strings.HasPrefix(s, "sc#"):
		v, err := colorComponents(s[3:], 3, 4)
		if err != nil {
			return Color{}, err
		}
		c.Space = ColorScRGB
		if len(v) == 4 {
			c.Alpha, v = colorClamp(v[0]), v[1:]
		}
		c.Components = v
	case strings.HasPrefix(s, "ContextColor"):
		const prefix = "ContextColor"
		if len(s) == len(prefix) || !xmlSpace(s[len(prefix)]) {
			return Color{}, fmt.Errorf("%w: missing ContextColor separator", ErrInvalid)
		}
		rest := strings.TrimLeft(s[len(prefix):], " \t\r\n")
		i := strings.IndexAny(rest, " \t\r\n")
		if i < 1 {
			return Color{}, fmt.Errorf("%w: missing ContextColor profile or components", ErrInvalid)
		}
		c.ProfileURI = rest[:i]
		if err := brushPartReference(c.ProfileURI); err != nil {
			return Color{}, fmt.Errorf("ContextColor profile: %w", err)
		}
		v, err := colorComponents(rest[i:], 2, 9)
		if err != nil {
			return Color{}, err
		}
		for i := range v {
			v[i] = colorClamp(v[i])
		}
		c.Space, c.Alpha, c.Components = ColorContext, v[0], v[1:]
	default:
		return Color{}, fmt.Errorf("%w: invalid color %q", ErrInvalid, text)
	}
	return c, nil
}

// colorComponents 解析受数量限制的十进制颜色分量，拒绝指数和前导加号
// 入参: text 逗号分隔文本, minimum 最少数量, maximum 最多数量
// 返回: []float64 有限分量, error 词法错误
func colorComponents(text string, minimum, maximum int) ([]float64, error) {
	count := strings.Count(text, ",") + 1
	if count < minimum || count > maximum {
		return nil, fmt.Errorf("%w: invalid color component count %d", ErrInvalid, count)
	}
	values := make([]float64, 0, count)
	for _, token := range strings.Split(text, ",") {
		token = strings.Trim(token, " \t\r\n")
		if !colorDecimalPattern.MatchString(token) {
			return nil, fmt.Errorf("%w: invalid color decimal %q", ErrInvalid, token)
		}
		value, err := strconv.ParseFloat(token, 64)
		if err != nil || !geometryFinite(value) {
			return nil, fmt.Errorf("%w: non-finite color component %q", ErrInvalid, token)
		}
		values = append(values, value)
	}
	return values, nil
}

// colorClamp 将透明度或ICC输入分量裁剪到单位区间
// 入参: value 有限分量
// 返回: float64 裁剪结果
func colorClamp(value float64) float64 {
	return min(1, max(0, value))
}

// parseBrushColor 按固定布局命名空间解析颜色并校验ContextColor通道数范围
// 入参: text 颜色文本, namespace XPS或OpenXPS命名空间
// 返回: Color 颜色数据, error 颜色或方言错误
func parseBrushColor(text, namespace string) (Color, error) {
	if namespace != xpsNamespace && namespace != openXPSNamespace {
		return Color{}, fmt.Errorf("%w: invalid color namespace", ErrInvalid)
	}
	c, err := ParseColor(text)
	if err != nil {
		return Color{}, err
	}
	if namespace == xpsNamespace && c.Space == ColorContext && len(c.Components) < 3 {
		return Color{}, fmt.Errorf("%w: XPS ContextColor requires three to eight channels", ErrInvalid)
	}
	return c, nil
}

// brushPartReference 校验包内部件引用的基本语法形式，保留相对路径与Unicode文本
// 入参: value 待检查引用
// 返回: error 非法引用错误
func brushPartReference(value string) error {
	if value == "" || !utf8.ValidString(value) || strings.ContainsAny(value, "\\?#<>\"{}|^`") || strings.HasPrefix(value, "//") {
		return fmt.Errorf("%w: invalid brush part reference %q", ErrInvalid, value)
	}
	for _, c := range value {
		if c < 0x20 || c == 0x7f || c == 0xfffe || c == 0xffff {
			return fmt.Errorf("%w: invalid character in brush part reference", ErrInvalid)
		}
	}
	u, err := url.Parse(value)
	if err != nil || u.Scheme != "" || u.Host != "" || u.Opaque != "" || u.User != nil {
		return fmt.Errorf("%w: brush reference must identify a package part", ErrInvalid)
	}
	if strings.HasSuffix(value, "/") || strings.HasSuffix(value, "/.") || strings.HasSuffix(value, "/..") || value == "." || value == ".." {
		return fmt.Errorf("%w: brush reference identifies a directory", ErrInvalid)
	}
	return nil
}

// renderColorFromColor 将非预乘源颜色转换至目标工作空间并预乘alpha，sRGB目标裁剪色域
// 入参: c 非预乘颜色, space 目标合成空间
// 返回: renderColor 预乘颜色, error 颜色结构或未支持的颜色转换错误
func renderColorFromColor(c Color, space renderColorSpace) (renderColor, error) {
	if space != renderSRGB && space != renderScRGB {
		return renderColor{}, fmt.Errorf("%w: compositor color space", ErrUnsupported)
	}
	if !geometryFinite(c.Alpha) {
		return renderColor{}, fmt.Errorf("%w: non-finite color alpha", ErrInvalid)
	}
	for _, value := range c.Components {
		if !geometryFinite(value) {
			return renderColor{}, fmt.Errorf("%w: non-finite color component", ErrInvalid)
		}
	}
	if c.Space == ColorContext {
		return renderColor{}, fmt.Errorf("%w: ICC color transform requires a color backend", ErrUnsupported)
	}
	if c.Space != ColorSRGB && c.Space != ColorScRGB || len(c.Components) != 3 {
		return renderColor{}, fmt.Errorf("%w: compositor requires an RGB source color", ErrInvalid)
	}
	channels := [3]float64{c.Components[0], c.Components[1], c.Components[2]}
	for i, value := range channels {
		if c.Space == ColorSRGB {
			if value < 0 || value > 1 {
				return renderColor{}, fmt.Errorf("%w: sRGB component outside unit range", ErrInvalid)
			}
			if space == renderScRGB {
				channels[i] = renderSRGBToLinear(value)
			}
		} else if space == renderSRGB {
			channels[i] = renderLinearToSRGB(colorClamp(value))
		}
	}
	alpha := colorClamp(c.Alpha)
	if alpha == 0 {
		return renderColor{}, nil
	}
	return renderColor{channels[0] * alpha, channels[1] * alpha, channels[2] * alpha, alpha}, nil
}

// renderSRGBToLinear 将归一化sRGB分量解码为线性光值
// 入参: value 单位区间内的有限sRGB分量
// 返回: float64 对应线性分量
func renderSRGBToLinear(value float64) float64 {
	if value <= 0.04045 {
		return value / 12.92
	}
	return math.Pow((value+0.055)/1.055, 2.4)
}

// renderSignedSRGBToLinear 将带符号扩展色域sRGB分量按对称IEC 61966-2-1曲线解码为线性光值
// 入参: value 有限sRGB分量，允许小于零或大于一
// 返回: float64 对应线性分量
func renderSignedSRGBToLinear(value float64) float64 {
	magnitude := math.Abs(value)
	if magnitude <= 0.04045 {
		return value / 12.92
	}
	return math.Copysign(math.Pow((magnitude+0.055)/1.055, 2.4), value)
}

// renderLinearToSRGB 将归一化线性分量编码为sRGB值，不变换alpha
// 入参: value 单位区间内的有限线性分量
// 返回: float64 对应sRGB分量
func renderLinearToSRGB(value float64) float64 {
	if value == 1 {
		return 1
	}
	if value <= 0.0031308 {
		return 12.92 * value
	}
	return 1.055*math.Pow(value, 1.0/2.4) - 0.055
}

// validate 检查工作颜色的有限性及透明色合同，不裁剪扩展RGB分量
// 返回: error 非法数值或未支持的零alpha发光分量错误
func (c renderColor) validate() error {
	if !geometryFinite(c.r, c.g, c.b, c.a) || c.a < 0 || c.a > 1 {
		return fmt.Errorf("%w: invalid compositor color", ErrInvalid)
	}
	if c.a == 0 && (c.r != 0 || c.g != 0 || c.b != 0) {
		return fmt.Errorf("%w: nonzero premultiplied color with zero alpha", ErrUnsupported)
	}
	return nil
}

// renderSourceOver 在同一工作空间执行预乘source-over合成，不在合成期间裁剪色域
// 入参: source 前景预乘颜色, destination 背景预乘颜色
// 返回: renderColor 合成结果, error 非法输入或浮点溢出错误
func renderSourceOver(source, destination renderColor) (renderColor, error) {
	if err := source.validate(); err != nil {
		return renderColor{}, err
	}
	if err := destination.validate(); err != nil {
		return renderColor{}, err
	}
	remaining := 1 - source.a
	result := renderColor{
		source.r + destination.r*remaining,
		source.g + destination.g*remaining,
		source.b + destination.b*remaining,
		source.a + destination.a*remaining,
	}
	if !geometryFinite(result.r, result.g, result.b, result.a) {
		return renderColor{}, fmt.Errorf("%w: compositor arithmetic overflow", ErrLimit)
	}
	return result, nil
}

// renderColorModulate 将不透明度与覆盖率施加于预乘RGB和alpha，下溢为零时安全归零
// 入参: c 预乘颜色, opacity 单位区间内的不透明度, coverage 单位区间内的覆盖率
// 返回: renderColor 调制结果, error 非法输入错误
func renderColorModulate(c renderColor, opacity, coverage float64) (renderColor, error) {
	if err := c.validate(); err != nil {
		return renderColor{}, err
	}
	if !geometryFinite(opacity, coverage) || opacity < 0 || opacity > 1 || coverage < 0 || coverage > 1 {
		return renderColor{}, fmt.Errorf("%w: opacity or coverage outside unit range", ErrInvalid)
	}
	factor := opacity * coverage
	if factor == 0 {
		return renderColor{}, nil
	}
	result := renderColor{c.r * factor, c.g * factor, c.b * factor, c.a * factor}
	if result.a == 0 {
		return renderColor{}, nil
	}
	return result, nil
}

// renderColorToNRGBA 将工作空间预乘颜色还原、裁剪并量化为8位非预乘sRGB像素
// 入参: c 指定工作空间中的预乘颜色, space 工作空间
// 返回: color.NRGBA 非预乘sRGB像素, error 非法输入或未支持的工作空间错误
func renderColorToNRGBA(c renderColor, space renderColorSpace) (color.NRGBA, error) {
	if space != renderSRGB && space != renderScRGB {
		return color.NRGBA{}, fmt.Errorf("%w: compositor output color space", ErrUnsupported)
	}
	if err := c.validate(); err != nil {
		return color.NRGBA{}, err
	}
	alpha := uint8(math.Floor(c.a*255 + 0.5))
	if alpha == 0 {
		return color.NRGBA{}, nil
	}
	channels := [3]float64{c.r, c.g, c.b}
	var pixels [3]uint8
	for i, value := range channels {
		if value <= 0 {
			value = 0
		} else if value >= c.a {
			value = 1
		} else {
			value /= c.a
		}
		if space == renderScRGB {
			value = renderLinearToSRGB(value)
		}
		pixels[i] = uint8(math.Floor(colorClamp(value)*255 + 0.5))
	}
	return color.NRGBA{R: pixels[0], G: pixels[1], B: pixels[2], A: alpha}, nil
}

// renderColorToNRGBAToneMapped 按ITU-R BT.2446方法A将线性scRGB预乘颜色色调映射并量化为8位非预乘sRGB像素
// 入参: c 线性scRGB预乘颜色, peakNits HDR标称峰值亮度（cd/m²）
// 返回: color.NRGBA 非预乘sRGB像素, error 非法输入错误
func renderColorToNRGBAToneMapped(c renderColor, peakNits float64) (color.NRGBA, error) {
	if err := c.validate(); err != nil {
		return color.NRGBA{}, err
	}
	alpha := uint8(math.Floor(c.a*255 + 0.5))
	if alpha == 0 {
		return color.NRGBA{}, nil
	}
	mapped := renderBT2446MethodA([3]float64{c.r / c.a, c.g / c.a, c.b / c.a}, peakNits)
	var pixels [3]uint8
	for i, value := range mapped {
		pixels[i] = uint8(math.Floor(colorClamp(renderLinearToSRGB(colorClamp(value)))*255 + 0.5))
	}
	return color.NRGBA{R: pixels[0], G: pixels[1], B: pixels[2], A: alpha}, nil
}

// parseICCNamedColor 读取namedColor2Type，区分设备坐标数与OpenXPS色调分量数
// 入参: profile 命名色配置文件
// 返回: []iccNamedColor 声明顺序的命名色, error 字段、编码或能力错误
func parseICCNamedColor(profile *iccProfile) ([]iccNamedColor, error) {
	if profile == nil || profile.pcs != "XYZ " && profile.pcs != "Lab " {
		return nil, fmt.Errorf("%w: ICC named connection space", ErrInvalid)
	}
	var colors []iccNamedColor
	err := walkICCNamedColor(profile, nil, true, iccMaxNamedColors, func(count int, prefix, suffix, name string, pcs [3]uint16, devBytes []byte) error {
		if colors == nil {
			colors = make([]iccNamedColor, 0, count)
		}
		var pcsCoord, xyz [3]float64
		if profile.pcs == "XYZ " {
			for axis := range 3 {
				xyz[axis] = float64(pcs[axis]) / 32768
			}
			pcsCoord = xyz
		} else if profile.version >= 0x04000000 {
			pcsCoord = [3]float64{float64(pcs[0]) * 100 / 65535, float64(pcs[1])*255/65535 - 128, float64(pcs[2])*255/65535 - 128}
			xyz = iccLabToXYZ(pcsCoord)
		} else {
			pcsCoord = [3]float64{min(100, float64(pcs[0])*100/65280), float64(pcs[1])/256 - 128, float64(pcs[2])/256 - 128}
			xyz = iccLabToXYZ(pcsCoord)
		}
		var dev []float64
		if len(devBytes) != 0 {
			device := len(devBytes) / 2
			dev = make([]float64, device)
			for axis := range device {
				dev[axis] = float64(binary.BigEndian.Uint16(devBytes[axis*2:])) / 65535
			}
		}
		colors = append(colors, iccNamedColor{name: name, prefix: prefix, suffix: suffix, pcs: pcsCoord, xyz: xyz, device: dev})
		return nil
	})
	if err != nil {
		return nil, err
	}
	return colors, nil
}

// iccNamedASCIIText 校验并提取零终止的7位ASCII命名色文本及NUL后全零填充，不解释名称为文件或资源引用
// 入参: data 固定长度原始字段
// 返回: string 去除终止符的ASCII文本, error 编码、终止或填充错误
func iccNamedASCIIText(data []byte) (string, error) {
	end := bytes.IndexByte(data, 0)
	if end < 0 {
		return "", fmt.Errorf("%w: ICC named ASCII termination", ErrInvalid)
	}
	for _, value := range data[:end] {
		if value > 127 {
			return "", fmt.Errorf("%w: ICC named ASCII encoding", ErrInvalid)
		}
	}
	for _, value := range data[end:] {
		if value != 0 {
			return "", fmt.Errorf("%w: ICC named ASCII padding", ErrInvalid)
		}
	}
	return string(data[:end]), nil
}

// inputChannels 取得转换所需分量数，命名色色调数量独立于可选设备坐标数量
// 返回: int 源分量数
func (t *iccTransform) inputChannels() int {
	if len(t.named) != 0 {
		return len(t.named)
	}
	return t.profile.channels
}

// namedXYZ 按相对白点的XYZ分量积混合命名色，单色按色调线性稀释
// 入参: input 各命名色的色调
// 返回: [3]float64 显示近似XYZ
func (t *iccTransform) namedXYZ(input []float64) [3]float64 {
	result := iccPCSWhite
	for i, color := range t.named {
		tint := colorClamp(input[i])
		for axis := range 3 {
			result[axis] *= 1 - tint + tint*color.xyz[axis]/iccPCSWhite[axis]
		}
	}
	return result
}

// parseICCCurve 解析curveType及五种parametricCurveType，返回未计末尾对齐的字节数
// 入参: data 曲线定义及可能的后续数据
// 返回: iccCurve 曲线, int 本曲线字节数, error 数据或资源错误
func parseICCCurve(data []byte) (iccCurve, int, error) {
	if len(data) < 12 || binary.BigEndian.Uint32(data[4:]) != 0 {
		return iccCurve{}, 0, fmt.Errorf("%w: ICC curve header", ErrInvalid)
	}
	switch string(data[:4]) {
	case "curv":
		count := uint64(binary.BigEndian.Uint32(data[8:]))
		if count > iccMaxCurveSamples {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC curve sample count", ErrLimit)
		}
		size := uint64(12) + 2*count
		if size > uint64(len(data)) {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC curve sample data", ErrInvalid)
		}
		curve := iccCurve{kind: iccCurveIdentity}
		if count == 1 {
			curve.kind = iccCurveGamma
			curve.parameters[0] = float64(binary.BigEndian.Uint16(data[12:])) / 256
		} else if count > 1 {
			curve.kind = iccCurveSampled
			curve.values = data[12:size]
			curve.precision = 2
		}
		return curve, int(size), nil
	case "para":
		function := binary.BigEndian.Uint16(data[8:])
		if function > 4 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve function", ErrUnsupported)
		}
		if binary.BigEndian.Uint16(data[10:]) != 0 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve reserved field", ErrInvalid)
		}
		count := [5]int{1, 3, 4, 5, 7}[function]
		size := 12 + 4*count
		if len(data) < size {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve parameters", ErrInvalid)
		}
		curve := iccCurve{kind: iccCurveParametric, function: function}
		for i := range count {
			curve.parameters[i] = iccFixed(data[12+i*4:])
		}
		if (function == 1 || function == 2) && curve.parameters[1] == 0 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve division", ErrInvalid)
		}
		return curve, size, nil
	default:
		return iccCurve{}, 0, fmt.Errorf("%w: ICC curve type %q", ErrUnsupported, string(data[:4]))
	}
}

// evaluate 按ICC单位定义域求值并裁剪输出，不将gamma误解释为其倒数
// 入参: value 有限输入分量
// 返回: float64 单位区间输出, error 非实数函数或输入错误
func (c iccCurve) evaluate(value float64) (float64, error) {
	if !geometryFinite(value) {
		return 0, fmt.Errorf("%w: ICC curve input", ErrInvalid)
	}
	value = colorClamp(value)
	var result float64
	switch c.kind {
	case iccCurveIdentity:
		return value, nil
	case iccCurveGamma:
		result = math.Pow(value, c.parameters[0])
	case iccCurveSampled:
		if c.precision != 1 && c.precision != 2 {
			return 0, fmt.Errorf("%w: ICC curve sample precision", ErrInvalid)
		}
		count := len(c.values) / c.precision
		if count < 2 {
			return 0, fmt.Errorf("%w: ICC sampled curve", ErrInvalid)
		}
		position := value * float64(count-1)
		index := min(int(position), count-2)
		fraction := position - float64(index)
		var a, b float64
		if c.precision == 1 {
			a, b = float64(c.values[index])/255, float64(c.values[index+1])/255
		} else {
			a, b = float64(binary.BigEndian.Uint16(c.values[2*index:]))/65535, float64(binary.BigEndian.Uint16(c.values[2*index+2:]))/65535
		}
		result = a*(1-fraction) + b*fraction
	case iccCurveParametric:
		p := c.parameters
		switch c.function {
		case 0:
			result = math.Pow(value, p[0])
		case 1, 2:
			if value >= -p[2]/p[1] {
				result = math.Pow(max(0, p[1]*value+p[2]), p[0])
			}
			if c.function == 2 {
				result += p[3]
			}
		case 3, 4:
			if value >= p[4] {
				result = math.Pow(p[1]*value+p[2], p[0])
				if c.function == 4 {
					result += p[5]
				}
			} else {
				result = p[3] * value
				if c.function == 4 {
					result += p[6]
				}
			}
		default:
			return 0, fmt.Errorf("%w: ICC curve function", ErrUnsupported)
		}
	default:
		return 0, fmt.Errorf("%w: ICC curve kind", ErrInvalid)
	}
	if math.IsNaN(result) {
		return 0, fmt.Errorf("%w: non-real ICC curve value", ErrInvalid)
	}
	return colorClamp(result), nil
}

// evaluateExtended 按ICC曲线公式在扩展范围无裁剪求值，采样曲线超出单位区间时沿端点斜率线性外推
// 入参: value 有限输入分量
// 返回: float64 无裁剪曲线输出, error 非实数函数或输入错误
func (c iccCurve) evaluateExtended(value float64) (float64, error) {
	if !geometryFinite(value) {
		return 0, fmt.Errorf("%w: ICC curve input", ErrInvalid)
	}
	var result float64
	switch c.kind {
	case iccCurveIdentity:
		return value, nil
	case iccCurveGamma:
		g := c.parameters[0]
		if g == 0 {
			return 1, nil
		}
		if g == 1 {
			return value, nil
		}
		result = math.Copysign(math.Pow(math.Abs(value), g), value)
	case iccCurveSampled:
		if value >= 0 && value <= 1 {
			return c.evaluate(value)
		}
		if c.precision != 1 && c.precision != 2 {
			return 0, fmt.Errorf("%w: ICC curve sample precision", ErrInvalid)
		}
		count := len(c.values) / c.precision
		if count < 2 {
			return 0, fmt.Errorf("%w: ICC sampled curve", ErrInvalid)
		}
		if value < 0 {
			y0, y1 := iccInverseCurveSample(c, 0), iccInverseCurveSample(c, 1)
			result = y0 + (y1-y0)*float64(count-1)*value
		} else {
			y0, y1 := iccInverseCurveSample(c, count-2), iccInverseCurveSample(c, count-1)
			result = y1 + (y1-y0)*float64(count-1)*(value-1)
		}
	case iccCurveParametric:
		p := c.parameters
		switch c.function {
		case 0:
			if p[0] == 0 {
				return 1, nil
			}
			if p[0] == 1 {
				return value, nil
			}
			result = math.Copysign(math.Pow(math.Abs(value), p[0]), value)
		case 1, 2:
			if value >= -p[2]/p[1] {
				base := p[1]*value + p[2]
				if p[0] == 0 {
					result = 1
				} else if base > 0 {
					result = math.Pow(base, p[0])
				}
			}
			if c.function == 2 {
				result += p[3]
			}
		case 3, 4:
			if value >= p[4] {
				base := p[1]*value + p[2]
				if p[0] == 0 {
					result = 1
				} else if base != 0 || p[0] < 0 {
					result = math.Pow(base, p[0])
				}
				if c.function == 4 {
					result += p[5]
				}
			} else {
				result = p[3] * value
				if c.function == 4 {
					result += p[6]
				}
			}
		default:
			return 0, fmt.Errorf("%w: ICC curve function", ErrUnsupported)
		}
	default:
		return 0, fmt.Errorf("%w: ICC curve kind", ErrInvalid)
	}
	if !geometryFinite(result) {
		return 0, fmt.Errorf("%w: non-real ICC curve value", ErrInvalid)
	}
	return result, nil
}

// prepareICCInverseCurve 验证TRC并缓存求逆所需的端点及幂分段边界
// 入参: curve 原始曲线, ctx 取消Context
// 返回: iccInverseCurve 可直接求逆的曲线, error 能力、数值或取消错误
func prepareICCInverseCurve(curve iccCurve, ctx context.Context) (iccInverseCurve, error) {
	if err := validateICCInverseCurve(curve, ctx); err != nil {
		return iccInverseCurve{}, err
	}
	first, _ := curve.evaluate(0)
	last, _ := curve.evaluate(1)
	result := iccInverseCurve{curve: curve, first: first, last: last}
	if curve.kind == iccCurveParametric && curve.function >= 3 && curve.parameters[4] > 0 && curve.parameters[4] < 1 {
		result.upper, _ = curve.evaluate(curve.parameters[4])
	}
	return result, nil
}

// validateICCInverseCurve 检查可逆TRC的单调性，平坦段允许采用最左侧广义逆
// 入参: c 已解析曲线, ctx 取消Context
// 返回: error 非单调、常量、数值或取消错误
func validateICCInverseCurve(c iccCurve, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	a, err := c.evaluate(0)
	if err != nil {
		return err
	}
	b, err := c.evaluate(1)
	if err != nil {
		return err
	}
	if a == b {
		return fmt.Errorf("%w: constant ICC target curve", ErrUnsupported)
	}
	points := []float64{0, 1}
	if c.kind == iccCurveSampled {
		count := len(c.values) / c.precision
		previous := a
		for i := 1; i < count; i++ {
			if i&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return err
				}
			}
			value := iccInverseCurveSample(c, i)
			if b > a && value < previous || b < a && value > previous {
				return fmt.Errorf("%w: nonmonotonic ICC target curve", ErrUnsupported)
			}
			previous = value
		}
	} else if c.kind == iccCurveParametric {
		p := c.parameters
		boundary := 0.0
		if c.function == 1 || c.function == 2 {
			boundary = -p[2] / p[1]
		} else if c.function >= 3 {
			boundary = p[4]
		}
		if boundary > 0 && boundary < 1 {
			points = append(points, math.Nextafter(boundary, 0), boundary, math.Nextafter(boundary, 1))
		}
		if c.function == 0 && p[0] <= 0 || c.function != 0 && (p[0] <= 0 || p[1] <= 0) || c.function >= 3 && p[3] < 0 {
			return fmt.Errorf("%w: ICC target parametric curve inverse", ErrUnsupported)
		}
		if c.function >= 3 && boundary < 1 && p[1]*max(0, boundary)+p[2] < 0 {
			return fmt.Errorf("%w: ICC target curve power domain", ErrUnsupported)
		}
	}
	slices.Sort(points)
	previous := a
	for _, point := range points {
		value, err := c.evaluate(point)
		if err != nil {
			return err
		}
		if b > a && value < previous || b < a && value > previous {
			return fmt.Errorf("%w: discontinuous ICC target curve inverse", ErrUnsupported)
		}
		previous = value
	}
	return checkContext(ctx)
}

// inverseICCCurve 求已验证TRC的最左侧广义逆，超出曲线值域时取最近端点
// 入参: prepared 已准备的单调曲线, value 有限目标值
// 返回: float64 单位区间设备分量
func inverseICCCurve(prepared iccInverseCurve, value float64) float64 {
	c := prepared.curve
	if c.kind == iccCurveIdentity {
		return colorClamp(value)
	}
	if c.kind == iccCurveGamma {
		return math.Pow(colorClamp(value), 1/c.parameters[0])
	}
	a, b := prepared.first, prepared.last
	increasing := b > a
	if increasing && value <= a || !increasing && value >= a {
		return 0
	}
	if increasing && value > b || !increasing && value < b {
		return 1
	}
	if c.kind == iccCurveSampled {
		count := len(c.values) / c.precision
		low, high := 0, count-1
		for low < high {
			mid := low + (high-low)/2
			v := iccInverseCurveSample(c, mid)
			if increasing && v < value || !increasing && v > value {
				low = mid + 1
			} else {
				high = mid
			}
		}
		if low == 0 {
			return 0
		}
		x0, x1 := float64(low-1)/float64(count-1), float64(low)/float64(count-1)
		y0, y1 := iccInverseCurveSample(c, low-1), iccInverseCurveSample(c, low)
		if y0 == y1 {
			return x0
		}
		return x0 + (x1-x0)*(value-y0)/(y1-y0)
	}
	p := c.parameters
	if c.function == 0 {
		return colorClamp(math.Pow(value, 1/p[0]))
	}
	offset, boundary := 0.0, -p[2]/p[1]
	if c.function == 2 {
		offset = p[3]
	}
	if c.function >= 3 {
		boundary = p[4]
		linearOffset := 0.0
		if c.function == 4 {
			offset, linearOffset = p[5], p[6]
		}
		if boundary > 0 {
			limit := min(1, boundary)
			if value <= colorClamp(p[3]*limit+linearOffset) && p[3] > 0 {
				return min(limit, colorClamp((value-linearOffset)/p[3]))
			}
			if boundary < 1 {
				if value <= prepared.upper {
					return boundary
				}
			}
		}
	}
	return colorClamp(max(boundary, (math.Pow(max(0, value-offset), 1/p[0])-p[2])/p[1]))
}

// iccInverseCurveSample 读取已验证采样表的节点值，不对整数索引重复执行曲线插值
// 入参: curve 有效采样曲线, index 有效节点索引
// 返回: float64 归一化节点值
func iccInverseCurveSample(curve iccCurve, index int) float64 {
	if curve.precision == 1 {
		return float64(curve.values[index]) / 255
	}
	return float64(binary.BigEndian.Uint16(curve.values[index*2:])) / 65535
}

// parseICCLUT 解析lut8Type和lut16Type，检查矩阵条件及全部表格范围后再建立视图
// 入参: data 标签字节, inputXYZ 输入是否为XYZ空间
// 返回: *iccPipeline 转换阶段, error 数据、能力或资源错误
func parseICCLUT(data []byte, inputXYZ bool) (*iccPipeline, error) {
	if len(data) < 48 || binary.BigEndian.Uint32(data[4:]) != 0 || data[11] != 0 {
		return nil, fmt.Errorf("%w: ICC LUT header", ErrInvalid)
	}
	precision, inputEntries, outputEntries, offset := 1, 256, 256, 48
	switch string(data[:4]) {
	case "mft1":
	case "mft2":
		if len(data) < 52 {
			return nil, fmt.Errorf("%w: ICC LUT16 header", ErrInvalid)
		}
		precision, offset = 2, 52
		inputEntries = int(binary.BigEndian.Uint16(data[48:]))
		outputEntries = int(binary.BigEndian.Uint16(data[50:]))
		if inputEntries < 2 || inputEntries > 4096 || outputEntries < 2 || outputEntries > 4096 {
			return nil, fmt.Errorf("%w: ICC LUT16 table count", ErrInvalid)
		}
	default:
		return nil, fmt.Errorf("%w: ICC LUT type %q", ErrUnsupported, string(data[:4]))
	}
	inputs, outputs, points := int(data[8]), int(data[9]), int(data[10])
	if inputs == 0 || outputs == 0 {
		return nil, fmt.Errorf("%w: ICC LUT channels", ErrInvalid)
	}
	if inputs > iccMaxChannels || outputs > iccMaxChannels {
		return nil, fmt.Errorf("%w: ICC LUT channel count", ErrUnsupported)
	}
	if points < 2 {
		return nil, fmt.Errorf("%w: ICC LUT grid", ErrInvalid)
	}
	matrix := iccStage{kind: iccStageMatrix}
	identity := true
	for i := range 9 {
		matrix.matrix[i] = iccFixed(data[12+4*i:])
		want := 0.0
		if i%4 == 0 {
			want = 1
		}
		identity = identity && matrix.matrix[i] == want
	}
	if !inputXYZ && !identity {
		return nil, fmt.Errorf("%w: ICC LUT matrix requires XYZ input", ErrInvalid)
	}
	if inputXYZ && inputs != 3 {
		return nil, fmt.Errorf("%w: ICC XYZ LUT input count", ErrInvalid)
	}
	cells := uint64(outputs)
	for range inputs {
		if cells > uint64(len(data))/uint64(points) {
			return nil, fmt.Errorf("%w: ICC LUT grid size", ErrInvalid)
		}
		cells *= uint64(points)
	}
	inputBytes := inputs * inputEntries * precision
	outputBytes := outputs * outputEntries * precision
	if cells > uint64(len(data))/uint64(precision) || uint64(offset+inputBytes+outputBytes)+cells*uint64(precision) > uint64(len(data)) {
		return nil, fmt.Errorf("%w: ICC LUT data size", ErrInvalid)
	}
	p := &iccPipeline{inputs: inputs, outputs: outputs, legacyLab: precision == 2, inputPrecision: precision}
	if inputXYZ && !identity {
		p.stages = append(p.stages, matrix)
	}
	input := iccStage{kind: iccStageCurves}
	for i := range inputs {
		first := offset + i*inputEntries*precision
		input.curves = append(input.curves, iccCurve{kind: iccCurveSampled, precision: precision, values: data[first : first+inputEntries*precision]})
	}
	p.stages = append(p.stages, input)
	offset += inputBytes
	clut := iccStage{kind: iccStageCLUT, precision: precision, outputs: outputs, data: data[offset : offset+int(cells)*precision]}
	for range inputs {
		clut.grid = append(clut.grid, points)
	}
	p.stages = append(p.stages, clut)
	offset += len(clut.data)
	output := iccStage{kind: iccStageCurves}
	for i := range outputs {
		first := offset + i*outputEntries*precision
		output.curves = append(output.curves, iccCurve{kind: iccCurveSampled, precision: precision, values: data[first : first+outputEntries*precision]})
	}
	p.stages = append(p.stages, output)
	return p, nil
}

// evaluate 执行有界转换，保留阶段之间的浮点精度且浮点管线不裁剪范围
// 入参: input 源分量
// 返回: [iccMaxChannels]float64 目标分量，数量由管线定义, error 输入或阶段错误
func (p *iccPipeline) evaluate(input []float64) ([iccMaxChannels]float64, error) {
	if p == nil || len(input) != p.inputs || p.inputs < 1 || p.inputs > iccMaxChannels || p.outputs < 1 || p.outputs > iccMaxChannels {
		return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC pipeline channels", ErrInvalid)
	}
	var values [iccMaxChannels]float64
	for i, value := range input {
		if !geometryFinite(value) {
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC pipeline input", ErrInvalid)
		}
		if p.floating {
			values[i] = value
		} else {
			values[i] = colorClamp(value)
		}
	}
	count := p.inputs
	for _, stage := range p.stages {
		switch stage.kind {
		case iccStageMatrix:
			if count != 3 {
				return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC matrix stage channels", ErrInvalid)
			}
			original := values
			for row := range 3 {
				m := stage.matrix[row*3:]
				v := m[0]*original[0] + m[1]*original[1] + m[2]*original[2] + stage.matrix[9+row]
				if !geometryFinite(v) {
					return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC matrix stage range", ErrLimit)
				}
				if p.floating {
					values[row] = v
				} else {
					values[row] = colorClamp(v)
				}
			}
		case iccStageFloatMatrix:
			if count != stage.inputs || stage.outputs < 1 || stage.outputs > iccMaxChannels || len(stage.floatMatrix) != stage.outputs*stage.inputs+stage.outputs {
				return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC float matrix stage channels", ErrInvalid)
			}
			var next [iccMaxChannels]float64
			offsetBase := stage.outputs * stage.inputs
			for row := range stage.outputs {
				sum := stage.floatMatrix[offsetBase+row]
				rowBase := row * stage.inputs
				for col := range stage.inputs {
					sum += stage.floatMatrix[rowBase+col] * values[col]
				}
				if !geometryFinite(sum) {
					return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC float matrix stage range", ErrLimit)
				}
				next[row] = sum
			}
			values = next
			count = stage.outputs
		case iccStageCurves:
			if len(stage.curves) != count {
				return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC curve stage channels", ErrInvalid)
			}
			for i, curve := range stage.curves {
				value, err := curve.evaluate(values[i])
				if err != nil {
					return [iccMaxChannels]float64{}, err
				}
				values[i] = value
			}
		case iccStageSegmentedCurves:
			if len(stage.segCurves) != count {
				return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC segmented curve stage channels", ErrInvalid)
			}
			for i, curve := range stage.segCurves {
				value, err := curve.evaluate(values[i])
				if err != nil {
					return [iccMaxChannels]float64{}, err
				}
				values[i] = value
			}
		case iccStageCLUT:
			var err error
			values, err = stage.lookup(values[:count])
			if err != nil {
				return [iccMaxChannels]float64{}, err
			}
			count = stage.outputs
		default:
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC stage kind", ErrInvalid)
		}
	}
	if count != p.outputs {
		return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC pipeline output channels", ErrInvalid)
	}
	return values, nil
}

// lookup 按首通道变化最慢的表布局执行多线性插值，支持八位、十六位及三十二位浮点查找表
// 入参: input 当前阶段分量
// 返回: [iccMaxChannels]float64 插值输出, error 布局或参数错误
func (s iccStage) lookup(input []float64) ([iccMaxChannels]float64, error) {
	n := len(s.grid)
	if n < 1 || n > iccMaxChannels || len(input) != n || s.outputs < 1 || s.outputs > iccMaxChannels || s.precision != 1 && s.precision != 2 && s.precision != 4 {
		return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC CLUT layout", ErrInvalid)
	}
	var activeFrac [iccMaxChannels]float64
	var activeStride [iccMaxChannels]int
	active, baseIndex, cells := 0, 0, s.outputs
	for i := n - 1; i >= 0; i-- {
		if s.grid[i] < 2 || cells > len(s.data)/s.precision/s.grid[i] {
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC CLUT data", ErrInvalid)
		}
		curStride := cells
		cells *= s.grid[i]
		if !geometryFinite(input[i]) {
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC CLUT input", ErrInvalid)
		}
		position := colorClamp(input[i]) * float64(s.grid[i]-1)
		low := min(int(position), s.grid[i]-2)
		frac := position - float64(low)
		if frac == 0 {
			baseIndex += low * curStride
		} else if frac == 1 {
			baseIndex += (low + 1) * curStride
		} else {
			baseIndex += low * curStride
			activeStride[active] = curStride
			activeFrac[active] = frac
			active++
		}
	}
	var out [iccMaxChannels]float64
	for corner := 0; corner < 1<<active; corner++ {
		index, weight := baseIndex, 1.0
		for i := range active {
			if corner>>i&1 != 0 {
				index += activeStride[i]
				weight *= activeFrac[i]
			} else {
				weight *= 1 - activeFrac[i]
			}
		}
		if weight == 0 {
			continue
		}
		for channel := range s.outputs {
			value := 0.0
			switch s.precision {
			case 1:
				value = float64(s.data[index+channel]) / 255
			case 2:
				value = float64(binary.BigEndian.Uint16(s.data[(index+channel)*2:])) / 65535
			case 4:
				value = float64(math.Float32frombits(binary.BigEndian.Uint32(s.data[(index+channel)*4:])))
				if !geometryFinite(value) {
					return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC CLUT float value", ErrInvalid)
				}
			}
			out[channel] += value * weight
		}
	}
	for channel := range s.outputs {
		if !geometryFinite(out[channel]) {
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC CLUT output range", ErrLimit)
		}
		if s.precision != 4 {
			out[channel] = colorClamp(out[channel])
		}
	}
	return out, nil
}

// parseICCMultiLUT 解析正向或反向多阶段查找表，检查允许的阶段组合和共享曲线
// 入参: data lutAtoBType或lutBtoAType标签
// 返回: *iccPipeline 转换管线, error 数据、能力或资源错误
func parseICCMultiLUT(data []byte) (*iccPipeline, error) {
	if len(data) < 32 || binary.BigEndian.Uint32(data[4:]) != 0 || binary.BigEndian.Uint16(data[10:]) != 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT header", ErrInvalid)
	}
	reverse := string(data[:4]) == "mBA "
	if !reverse && string(data[:4]) != "mAB " {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT type", ErrUnsupported)
	}
	inputs, outputs := int(data[8]), int(data[9])
	if inputs == 0 || outputs == 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT channels", ErrInvalid)
	}
	if inputs > iccMaxChannels || outputs > iccMaxChannels {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT channel count", ErrUnsupported)
	}
	var offsets [5]uint64
	for i := range offsets {
		offsets[i] = uint64(binary.BigEndian.Uint32(data[12+4*i:]))
		if offsets[i] != 0 && (offsets[i] < 32 || offsets[i]%4 != 0 || offsets[i] >= uint64(len(data))) {
			return nil, fmt.Errorf("%w: ICC multi-stage LUT offset", ErrInvalid)
		}
	}
	if offsets[0] == 0 || (offsets[1] == 0) != (offsets[2] == 0) || (offsets[3] == 0) != (offsets[4] == 0) || inputs != outputs && offsets[3] == 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT combination", ErrInvalid)
	}
	curveChannels := outputs
	lastChannels := inputs
	if reverse {
		curveChannels, lastChannels = inputs, outputs
	}
	if offsets[1] != 0 && curveChannels != 3 {
		return nil, fmt.Errorf("%w: ICC multi-stage matrix channels", ErrInvalid)
	}
	var stages [5]iccStage
	var ranges []iccStageRange
	for _, index := range []int{0, 2, 4} {
		if offsets[index] == 0 {
			continue
		}
		count := curveChannels
		if index == 4 {
			count = lastChannels
		}
		stage, spans, err := iccEmbeddedCurves(data, offsets[index], count)
		if err != nil {
			return nil, err
		}
		stages[index] = stage
		ranges = append(ranges, spans...)
	}
	if offsets[1] != 0 {
		at := offsets[1]
		if at+48 > uint64(len(data)) {
			return nil, fmt.Errorf("%w: ICC multi-stage matrix data", ErrInvalid)
		}
		stages[1].kind = iccStageMatrix
		for i := range 12 {
			stages[1].matrix[i] = iccFixed(data[at+uint64(i)*4:])
		}
		ranges = append(ranges, iccStageRange{offset: at, size: 48})
	}
	if offsets[3] != 0 {
		stage, size, err := iccEmbeddedCLUT(data[offsets[3]:], inputs, outputs)
		if err != nil {
			return nil, err
		}
		stages[3] = stage
		ranges = append(ranges, iccStageRange{offset: offsets[3], size: uint64(size)})
	}
	slices.SortFunc(ranges, func(a, b iccStageRange) int {
		if value := cmp.Compare(a.offset, b.offset); value != 0 {
			return value
		}
		return cmp.Compare(a.size, b.size)
	})
	for i := 1; i < len(ranges); i++ {
		a, b := ranges[i-1], ranges[i]
		if b.offset < a.offset+a.size && (!a.curve || !b.curve || a.offset != b.offset || a.size != b.size) {
			return nil, fmt.Errorf("%w: overlapping ICC processing elements", ErrInvalid)
		}
	}
	p := &iccPipeline{inputs: inputs, outputs: outputs}
	order := []int{4, 3, 2, 1, 0}
	if reverse {
		order = []int{0, 1, 2, 3, 4}
	}
	for _, index := range order {
		if offsets[index] != 0 {
			p.stages = append(p.stages, stages[index])
		}
	}
	return p, nil
}

// iccEmbeddedCurves 读取顺序排列的逐通道曲线，并保留各曲线独立范围以校验共享
// 入参: data 标签字节, offset 首条曲线偏移, count 通道数
// 返回: iccStage 曲线阶段, []iccStageRange 曲线范围, error 曲线或对齐错误
func iccEmbeddedCurves(data []byte, offset uint64, count int) (iccStage, []iccStageRange, error) {
	stage := iccStage{kind: iccStageCurves}
	var ranges []iccStageRange
	for index := range count {
		if offset >= uint64(len(data)) {
			return iccStage{}, nil, fmt.Errorf("%w: ICC embedded curve offset", ErrInvalid)
		}
		curve, size, err := parseICCCurve(data[offset:])
		if err != nil {
			return iccStage{}, nil, err
		}
		ranges = append(ranges, iccStageRange{offset, uint64(size), true})
		stage.curves = append(stage.curves, curve)
		end := offset + uint64(size)
		next := (end + 3) &^ uint64(3)
		if next > uint64(len(data)) {
			if index == count-1 && end == uint64(len(data)) {
				break
			}
			return iccStage{}, nil, fmt.Errorf("%w: ICC curve alignment", ErrInvalid)
		}
		for _, value := range data[end:next] {
			if value != 0 {
				return iccStage{}, nil, fmt.Errorf("%w: ICC curve padding", ErrInvalid)
			}
		}
		offset = next
	}
	return stage, ranges, nil
}

// iccEmbeddedCLUT 读取各轴独立网格的八位或十六位表，不为表格分配副本
// 入参: data CLUT定义及后续数据, inputs 输入通道数, outputs 输出通道数
// 返回: iccStage 查找表阶段, int 元素字节数, error 数据或资源错误
func iccEmbeddedCLUT(data []byte, inputs, outputs int) (iccStage, int, error) {
	if len(data) < 20 || inputs < 1 || inputs > iccMaxChannels || outputs < 1 || outputs > iccMaxChannels {
		return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT header", ErrInvalid)
	}
	precision := int(data[16])
	if precision != 1 && precision != 2 || data[17] != 0 || data[18] != 0 || data[19] != 0 {
		return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT precision", ErrInvalid)
	}
	for _, value := range data[inputs:16] {
		if value != 0 {
			return iccStage{}, 0, fmt.Errorf("%w: ICC unused CLUT grid", ErrInvalid)
		}
	}
	stage := iccStage{kind: iccStageCLUT, precision: precision, outputs: outputs}
	cells := uint64(outputs)
	for _, value := range data[:inputs] {
		if value < 2 {
			return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT grid", ErrInvalid)
		}
		if cells > uint64(len(data)-20)/uint64(precision)/uint64(value) {
			return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT size", ErrInvalid)
		}
		cells *= uint64(value)
		stage.grid = append(stage.grid, int(value))
	}
	size := 20 + int(cells)*precision
	stage.data = data[20:size]
	return stage, size, nil
}

// iccFloat32 解码大端IEEE 754单精度浮点数并校验有限性
// 入参: data 至少四字节切片
// 返回: float64 有限浮点值, error 非有限数值错误
func iccFloat32(data []byte) (float64, error) {
	value := float64(math.Float32frombits(binary.BigEndian.Uint32(data)))
	if !geometryFinite(value) {
		return 0, fmt.Errorf("%w: ICC non-finite float32", ErrInvalid)
	}
	return value, nil
}

// parseICCMultiProcess 解析ICC v4.3 multiProcessElementsType浮点管线，支持cvst、matf、clut、bACS与eACS
// 入参: data mpet标签完整字节
// 返回: *iccPipeline 无裁剪浮点转换管线, error 格式、能力或资源错误
func parseICCMultiProcess(data []byte) (*iccPipeline, error) {
	if len(data) < 16 || string(data[:4]) != "mpet" || binary.BigEndian.Uint32(data[4:]) != 0 {
		return nil, fmt.Errorf("%w: ICC multi-process header", ErrInvalid)
	}
	inputs, outputs := int(binary.BigEndian.Uint16(data[8:])), int(binary.BigEndian.Uint16(data[10:]))
	if inputs == 0 || outputs == 0 {
		return nil, fmt.Errorf("%w: ICC multi-process channels", ErrInvalid)
	}
	if inputs > iccMaxChannels || outputs > iccMaxChannels {
		return nil, fmt.Errorf("%w: ICC multi-process channel count", ErrUnsupported)
	}
	count := uint64(binary.BigEndian.Uint32(data[12:]))
	if count > iccMaxElements {
		return nil, fmt.Errorf("%w: ICC multi-process element count", ErrLimit)
	}
	first := uint64(16) + 8*count
	if first > uint64(len(data)) {
		return nil, fmt.Errorf("%w: ICC multi-process table", ErrInvalid)
	}
	if count == 0 {
		if inputs != outputs {
			return nil, fmt.Errorf("%w: ICC empty multi-process channels", ErrInvalid)
		}
		return &iccPipeline{inputs: inputs, outputs: outputs, floating: true}, nil
	}
	positions := make([]iccTag, int(count))
	ranges := make([]iccTag, int(count))
	for i := range count {
		entry := data[16+8*i : 24+8*i]
		pos := iccTag{offset: binary.BigEndian.Uint32(entry[:4]), size: binary.BigEndian.Uint32(entry[4:])}
		if uint64(pos.offset) < first || pos.offset%4 != 0 || pos.size < 12 || uint64(pos.offset)+uint64(pos.size) > uint64(len(data)) {
			return nil, fmt.Errorf("%w: ICC multi-process element range", ErrInvalid)
		}
		positions[i] = pos
		ranges[i] = pos
	}
	slices.SortFunc(ranges, func(a, b iccTag) int {
		if value := cmp.Compare(a.offset, b.offset); value != 0 {
			return value
		}
		return cmp.Compare(a.size, b.size)
	})
	for i := 1; i < len(ranges); i++ {
		a, b := ranges[i-1], ranges[i]
		if uint64(b.offset) < uint64(a.offset)+uint64(a.size) && a != b {
			return nil, fmt.Errorf("%w: overlapping ICC multi-process elements", ErrInvalid)
		}
	}
	p := &iccPipeline{inputs: inputs, outputs: outputs, floating: true}
	current := inputs
	for _, pos := range positions {
		elem := data[uint64(pos.offset) : uint64(pos.offset)+uint64(pos.size)]
		if binary.BigEndian.Uint32(elem[4:]) != 0 {
			return nil, fmt.Errorf("%w: ICC process element reserved field", ErrInvalid)
		}
		inCh, outCh := int(binary.BigEndian.Uint16(elem[8:])), int(binary.BigEndian.Uint16(elem[10:]))
		if inCh != current || outCh == 0 {
			return nil, fmt.Errorf("%w: ICC process element channels", ErrInvalid)
		}
		if inCh > iccMaxChannels || outCh > iccMaxChannels {
			return nil, fmt.Errorf("%w: ICC process element channel count", ErrUnsupported)
		}
		switch string(elem[:4]) {
		case "bACS", "eACS":
			if len(elem) != 16 || inCh != outCh {
				return nil, fmt.Errorf("%w: ICC ACS process element", ErrInvalid)
			}
		case "matf":
			total := uint64(outCh)*uint64(inCh) + uint64(outCh)
			if uint64(len(elem)) != 12+4*total {
				return nil, fmt.Errorf("%w: ICC matrix process element size", ErrInvalid)
			}
			matrix := make([]float64, int(total))
			for i := range matrix {
				v, err := iccFloat32(elem[12+4*i:])
				if err != nil {
					return nil, err
				}
				matrix[i] = v
			}
			p.stages = append(p.stages, iccStage{kind: iccStageFloatMatrix, floatMatrix: matrix, inputs: inCh, outputs: outCh})
		case "clut":
			if len(elem) < 28 {
				return nil, fmt.Errorf("%w: ICC float CLUT header", ErrInvalid)
			}
			for _, unused := range elem[12+inCh : 28] {
				if unused != 0 {
					return nil, fmt.Errorf("%w: ICC unused float CLUT grid", ErrInvalid)
				}
			}
			grid := make([]int, inCh)
			cells := uint64(outCh)
			avail := uint64(len(elem)-28) / 4
			for i := range inCh {
				g := int(elem[12+i])
				if g < 2 {
					return nil, fmt.Errorf("%w: ICC float CLUT grid", ErrInvalid)
				}
				if cells > avail/uint64(g) {
					return nil, fmt.Errorf("%w: ICC float CLUT size", ErrInvalid)
				}
				cells *= uint64(g)
				grid[i] = g
			}
			if uint64(len(elem)-28) != cells*4 {
				return nil, fmt.Errorf("%w: ICC float CLUT length", ErrInvalid)
			}
			for off := 28; off < len(elem); off += 4 {
				if binary.BigEndian.Uint32(elem[off:])&0x7f800000 == 0x7f800000 {
					return nil, fmt.Errorf("%w: ICC float CLUT non-finite entry", ErrInvalid)
				}
			}
			p.stages = append(p.stages, iccStage{kind: iccStageCLUT, precision: 4, grid: grid, inputs: inCh, outputs: outCh, data: elem[28:]})
		case "cvst":
			if inCh != outCh {
				return nil, fmt.Errorf("%w: ICC curve set channels", ErrInvalid)
			}
			curves, err := parseICCCurveSet(elem, inCh)
			if err != nil {
				return nil, err
			}
			p.stages = append(p.stages, iccStage{kind: iccStageSegmentedCurves, segCurves: curves, inputs: inCh, outputs: outCh})
		default:
			return nil, fmt.Errorf("%w: ICC process element type %q", ErrUnsupported, string(elem[:4]))
		}
		current = outCh
	}
	if current != outputs {
		return nil, fmt.Errorf("%w: ICC multi-process output channels", ErrInvalid)
	}
	return p, nil
}

// parseICCCurveSet 解析cvst曲线集内各通道的偏移表与分段曲线定义，支持共享曲线与非紧邻布局
// 入参: data cvst元素完整字节, channels 通道数
// 返回: []iccSegmentedCurve 逐通道分段曲线, error 格式、能力或资源错误
func parseICCCurveSet(data []byte, channels int) ([]iccSegmentedCurve, error) {
	first := uint64(12) + 8*uint64(channels)
	if first > uint64(len(data)) {
		return nil, fmt.Errorf("%w: ICC curve set table", ErrInvalid)
	}
	positions := make([]iccTag, channels)
	ranges := make([]iccTag, channels)
	for i := range channels {
		entry := data[12+8*i : 20+8*i]
		pos := iccTag{offset: binary.BigEndian.Uint32(entry[:4]), size: binary.BigEndian.Uint32(entry[4:])}
		if uint64(pos.offset) < first || pos.offset%4 != 0 || pos.size < 12 || uint64(pos.offset)+uint64(pos.size) > uint64(len(data)) {
			return nil, fmt.Errorf("%w: ICC curve set entry range", ErrInvalid)
		}
		positions[i] = pos
		ranges[i] = pos
	}
	slices.SortFunc(ranges, func(a, b iccTag) int {
		if value := cmp.Compare(a.offset, b.offset); value != 0 {
			return value
		}
		return cmp.Compare(a.size, b.size)
	})
	for i := 1; i < len(ranges); i++ {
		a, b := ranges[i-1], ranges[i]
		if uint64(b.offset) < uint64(a.offset)+uint64(a.size) && a != b {
			return nil, fmt.Errorf("%w: overlapping ICC curve set entries", ErrInvalid)
		}
	}
	curves := make([]iccSegmentedCurve, channels)
	for i, pos := range positions {
		curve, err := parseICCSegmentedCurve(data[uint64(pos.offset) : uint64(pos.offset)+uint64(pos.size)])
		if err != nil {
			return nil, err
		}
		curves[i] = curve
	}
	return curves, nil
}

// parseICCSegmentedCurve 解析单通道curf分段曲线及内部的parf公式段与samf采样段
// 入参: data curf曲线完整字节
// 返回: iccSegmentedCurve 断点与分段列表, error 格式、能力或资源错误
func parseICCSegmentedCurve(data []byte) (iccSegmentedCurve, error) {
	if len(data) < 12 || string(data[:4]) != "curf" || binary.BigEndian.Uint32(data[4:]) != 0 || binary.BigEndian.Uint16(data[10:]) != 0 {
		return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve header", ErrInvalid)
	}
	segCount := int(binary.BigEndian.Uint16(data[8:]))
	if segCount == 0 {
		return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve count", ErrInvalid)
	}
	if segCount > iccMaxElements {
		return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve count", ErrLimit)
	}
	offset := uint64(12) + 4*uint64(segCount-1)
	if offset > uint64(len(data)) {
		return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve breakpoints", ErrInvalid)
	}
	var breakpoints []float64
	if segCount > 1 {
		breakpoints = make([]float64, segCount-1)
		for i := range breakpoints {
			bp, err := iccFloat32(data[12+4*i:])
			if err != nil {
				return iccSegmentedCurve{}, err
			}
			if i > 0 && bp < breakpoints[i-1] {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve breakpoint order", ErrInvalid)
			}
			breakpoints[i] = bp
		}
	}
	segments := make([]iccFloatCurveSegment, segCount)
	for i := range segCount {
		if offset+12 > uint64(len(data)) || binary.BigEndian.Uint32(data[offset+4:]) != 0 {
			return iccSegmentedCurve{}, fmt.Errorf("%w: ICC curve segment header", ErrInvalid)
		}
		switch string(data[offset : offset+4]) {
		case "parf":
			fn := binary.BigEndian.Uint16(data[offset+8:])
			if binary.BigEndian.Uint16(data[offset+10:]) != 0 {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC formula curve reserved field", ErrInvalid)
			}
			paramCount := 0
			switch fn {
			case 0:
				paramCount = 4
			case 1, 2:
				paramCount = 5
			default:
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC formula curve function %d", ErrUnsupported, fn)
			}
			end := offset + 12 + 4*uint64(paramCount)
			if end > uint64(len(data)) {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC formula curve parameters", ErrInvalid)
			}
			seg := iccFloatCurveSegment{function: fn}
			for j := range paramCount {
				v, err := iccFloat32(data[offset+12+4*uint64(j):])
				if err != nil {
					return iccSegmentedCurve{}, err
				}
				seg.parameters[j] = v
			}
			segments[i] = seg
			offset = end
		case "samf":
			if i == 0 || i == segCount-1 {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC sampled curve segment requires finite bounds", ErrInvalid)
			}
			count := uint64(binary.BigEndian.Uint32(data[offset+8:]))
			if count == 0 {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC sampled curve segment count", ErrInvalid)
			}
			if count > iccMaxCurveSamples {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC sampled curve segment count", ErrLimit)
			}
			if count > (uint64(len(data))-offset-12)/4 {
				return iccSegmentedCurve{}, fmt.Errorf("%w: ICC sampled curve segment data", ErrInvalid)
			}
			end := offset + 12 + 4*count
			values := data[offset+12 : end]
			for pos := 0; pos < len(values); pos += 4 {
				if binary.BigEndian.Uint32(values[pos:])&0x7f800000 == 0x7f800000 {
					return iccSegmentedCurve{}, fmt.Errorf("%w: ICC sampled curve non-finite entry", ErrInvalid)
				}
			}
			prevLo, prevHi := 0.0, 0.0
			if i >= 2 {
				prevLo, prevHi = breakpoints[i-2], breakpoints[i-1]
			}
			startVal, err := segments[i-1].evaluateAt(breakpoints[i-1], prevLo, prevHi)
			if err != nil {
				return iccSegmentedCurve{}, err
			}
			segments[i] = iccFloatCurveSegment{sampled: true, values: values, startValue: startVal}
			offset = end
		default:
			return iccSegmentedCurve{}, fmt.Errorf("%w: ICC curve segment type %q", ErrUnsupported, string(data[offset:offset+4]))
		}
	}
	if offset != uint64(len(data)) {
		return iccSegmentedCurve{}, fmt.Errorf("%w: ICC segmented curve length", ErrInvalid)
	}
	return iccSegmentedCurve{breakpoints: breakpoints, segments: segments}, nil
}

// evaluate 按断点选择所属分段并无裁剪求值
// 入参: x 有限浮点输入
// 返回: float64 有限浮点输出, error 输入或求值错误
func (c iccSegmentedCurve) evaluate(x float64) (float64, error) {
	if !geometryFinite(x) || len(c.segments) == 0 {
		return 0, fmt.Errorf("%w: ICC segmented curve input", ErrInvalid)
	}
	idx := len(c.segments) - 1
	for i, bp := range c.breakpoints {
		if x <= bp {
			idx = i
			break
		}
	}
	lo, hi := 0.0, 0.0
	if idx > 0 && idx < len(c.segments)-1 {
		lo, hi = c.breakpoints[idx-1], c.breakpoints[idx]
	}
	return c.segments[idx].evaluateAt(x, lo, hi)
}

// evaluateAt 求单个公式段或采样段在指定坐标的值，采样段以左断点延续值作为起点线性插值
// 入参: x 输入值, lo 采样段左断点, hi 采样段右断点
// 返回: float64 有限输出值, error 非实数或溢出错误
func (s iccFloatCurveSegment) evaluateAt(x, lo, hi float64) (float64, error) {
	var result float64
	if s.sampled {
		count := len(s.values) / 4
		if count == 0 {
			return 0, fmt.Errorf("%w: ICC sampled curve segment", ErrInvalid)
		}
		if hi <= lo || x >= hi {
			result = float64(math.Float32frombits(binary.BigEndian.Uint32(s.values[(count-1)*4:])))
		} else if x <= lo {
			result = s.startValue
		} else {
			pos := (x - lo) / (hi - lo) * float64(count)
			idx := int(pos)
			if idx >= count {
				result = float64(math.Float32frombits(binary.BigEndian.Uint32(s.values[(count-1)*4:])))
			} else {
				frac := pos - float64(idx)
				y0 := s.startValue
				if idx > 0 {
					y0 = float64(math.Float32frombits(binary.BigEndian.Uint32(s.values[(idx-1)*4:])))
				}
				y1 := float64(math.Float32frombits(binary.BigEndian.Uint32(s.values[idx*4:])))
				result = y0*(1-frac) + y1*frac
			}
		}
	} else {
		p := s.parameters
		switch s.function {
		case 0:
			result = iccFloatClamp(iccFloatClamp(iccFloatPow(p[1]*x+p[2], p[0])) + p[3])
		case 1:
			arg := p[2]*iccFloatClamp(iccFloatPow(x, p[0])) + p[3]
			if !(arg > iccMinFloat32) {
				arg = iccMinFloat32
			} else if math.IsInf(arg, 1) {
				arg = math.MaxFloat32
			}
			result = iccFloatClamp(p[1]*math.Log10(arg) + p[4])
		case 2:
			exp := p[2]*x + p[3]
			var powered float64
			switch {
			case exp == 0:
				powered = 1
			case p[1] == 0:
				if exp < 0 {
					powered = math.MaxFloat32
				}
			case p[1] > 0:
				powered = math.Pow(p[1], exp)
			case math.Trunc(exp) == exp:
				powered = math.Pow(p[1], exp)
			}
			result = iccFloatClamp(p[0]*iccFloatClamp(powered) + p[4])
		default:
			return 0, fmt.Errorf("%w: ICC formula curve function", ErrUnsupported)
		}
	}
	if !geometryFinite(result) {
		return 0, fmt.Errorf("%w: non-finite ICC segmented curve value", ErrInvalid)
	}
	return result, nil
}

// iccFloatPow 计算ICC浮点公式曲线的带符号保护幂运算
// 入参: base 底数, exp 指数
// 返回: float64 幂运算结果
func iccFloatPow(base, exp float64) float64 {
	switch {
	case exp == 0:
		return 1
	case base == 0:
		if exp < 0 {
			return math.MaxFloat32
		}
		return 0
	case base > 0 || math.Trunc(exp) == exp:
		return math.Pow(base, exp)
	case exp > 0:
		return -math.Pow(-base, exp)
	default:
		return 0
	}
}

// iccFloatClamp 将浮点中间结果安全钳位到ICC单精度有限范围，消除NaN与无穷大
// 入参: value 待保护的浮点值
// 返回: float64 有限单精度范围内的数值
func iccFloatClamp(value float64) float64 {
	if math.IsNaN(value) {
		return 0
	}
	if value > math.MaxFloat32 {
		return math.MaxFloat32
	}
	if value < -math.MaxFloat32 {
		return -math.MaxFloat32
	}
	return value
}

// imageCICPUsable 判断图像声明的CICP四元组是否包含需解析的色彩标识，全未指定时返回false
// 入参: cicp 图像CICP四元组
// 返回: bool 是否应由CICP管线接管
func imageCICPUsable(cicp *imageCICP) bool {
	return cicp != nil && !(cicp.primaries == 2 && cicp.transfer == 2 && cicp.matrix == 0)
}

// prepareImageCICP 校验并构建非JXR图像的H.273 CICP线性转换器，输出相对100 cd/m²归一化的D65线性scRGB
// 入参: cicp 图像CICP四元组, channels 源颜色通道数, bits 每通道编码位深（8、16或0表示浮点）, hdrPeakNits 可选HDR峰值亮度
// 返回: *imageCICPTransform CICP转换器，未指定时为nil, error 不支持或非法的CICP参数错误
func prepareImageCICP(cicp *imageCICP, channels, bits int, hdrPeakNits float64) (*imageCICPTransform, error) {
	if !imageCICPUsable(cicp) {
		return nil, nil
	}
	if channels == 1 && cicp.primaries == 10 {
		return nil, fmt.Errorf("%w: CICP CIE XYZ primaries require three channels", ErrInvalid)
	}
	if cicp.matrix != 0 {
		return nil, fmt.Errorf("%w: unsupported CICP matrix %d for RGB/Gray image", ErrUnsupported, cicp.matrix)
	}
	transfer := cicp.transfer
	switch transfer {
	case 6, 14, 15:
		transfer = 1
	case 1, 4, 5, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18:
	default:
		return nil, fmt.Errorf("%w: unsupported CICP transfer %d", ErrUnsupported, cicp.transfer)
	}
	if cicp.primaries == 10 && transfer != 8 && transfer != 16 && transfer != 17 || transfer == 17 && cicp.primaries != 10 {
		return nil, fmt.Errorf("%w: unsupported CICP XYZ transfer combination", ErrUnsupported)
	}
	matrix, kr, kb, ok := cicpPrimariesMatrix(cicp.primaries)
	if !ok {
		return nil, fmt.Errorf("%w: unsupported CICP primaries %d", ErrUnsupported, cicp.primaries)
	}
	offset, scale := 0.0, 1.0
	if !cicp.fullRange {
		if bits >= 8 && bits <= 16 {
			maximum := math.Ldexp(1, bits) - 1
			step := math.Ldexp(1, bits-8)
			offset, scale = (16*step)/maximum, maximum/(219*step)
		} else {
			offset, scale = 16.0/256.0, 256.0/219.0
		}
	}
	hdr := transfer == 16 || transfer == 18
	peak := hdrPeakNits
	if hdr && peak <= 0 {
		if transfer == 16 {
			peak = 10000
		} else {
			peak = 1000
		}
	}
	var hlgLuma [3]float64
	if transfer == 18 {
		if cicp.primaries == 9 {
			hlgLuma = [3]float64{cicpBT2100Red, cicpBT2100Green, cicpBT2100Blue}
		} else {
			kg := 1 - kr - kb
			if kr < 0 || kg < 0 || kb < 0 {
				return nil, fmt.Errorf("%w: invalid CICP HLG primaries", ErrUnsupported)
			}
			hlgLuma = [3]float64{kr, kg, kb}
		}
	}
	return &imageCICPTransform{
		linearMatrix: matrix,
		hlgLuma:      hlgLuma,
		offset:       offset,
		scale:        scale,
		primaries:    cicp.primaries,
		transfer:     transfer,
		hdr:          hdr,
		peakNits:     peak,
	}, nil
}

// toLinearSRGB 将归一化源RGB或灰度像素按CICP转换为未裁剪的D65线性scRGB，HDR按100 cd/m²归一化
// 入参: r, g, b 源像素分量, gray 是否为单通道灰度源
// 返回: [3]float64 线性scRGB三通道
func (t *imageCICPTransform) toLinearSRGB(r, g, b float64, gray bool) [3]float64 {
	if gray {
		g, b = r, r
	}
	rgb := [3]float64{
		(r - t.offset) * t.scale,
		(g - t.offset) * t.scale,
		(b - t.offset) * t.scale,
	}
	if t.hdr {
		for i, v := range rgb {
			rgb[i] = cicpHDRInverseTransfer(v, t.transfer)
		}
		scale := 100.0
		if t.transfer == 18 {
			rgb = cicpHLGDisplayLight(rgb, t.hlgLuma, t.peakNits)
			scale = t.peakNits / 100.0
		}
		for i := range rgb {
			rgb[i] *= scale
		}
	} else {
		for i, v := range rgb {
			rgb[i] = cicpSDRInverseTransfer(v, t.transfer)
		}
	}
	if gray && !t.hdr && t.primaries != 10 {
		return [3]float64{rgb[0], rgb[0], rgb[0]}
	}
	return iccMatrixColor(t.linearMatrix, rgb)
}

// prepareImageGammaChroma 校验并构建PNG gAMA与cHRM线性转换器，灰度图像仅应用gAMA
// 入参: gc 图像伽马与色度坐标元数据, channels 源颜色通道数
// 返回: *imageGammaChromaTransform 转换器，无有效参数时返回nil
func prepareImageGammaChroma(gc *imageGammaChroma, channels int) *imageGammaChromaTransform {
	if gc == nil {
		return nil
	}
	hasGamma := gc.hasGamma && geometryFinite(gc.gamma) && gc.gamma > 0
	invGamma := 0.0
	if hasGamma {
		invGamma = 1 / gc.gamma
		if !geometryFinite(invGamma) {
			hasGamma = false
		}
	}
	hasMatrix := false
	var linearMatrix [9]float64
	if channels != 1 && gc.hasChrm &&
		geometryFinite(gc.whiteX, gc.whiteY, gc.redX, gc.redY, gc.greenX, gc.greenY, gc.blueX, gc.blueY) &&
		gc.whiteX > 0 && gc.whiteY > 0 && gc.whiteX+gc.whiteY < 1 &&
		gc.redX >= 0 && gc.redY > 0 && gc.redX+gc.redY <= 1 &&
		gc.greenX >= 0 && gc.greenY > 0 && gc.greenX+gc.greenY <= 1 &&
		gc.blueX >= 0 && gc.blueY > 0 && gc.blueX+gc.blueY <= 1 {
		matrix, kr, kb, ok := cicpChromaticityToSRGB(
			[3][2]float64{{gc.redX, gc.redY}, {gc.greenX, gc.greenY}, {gc.blueX, gc.blueY}},
			[2]float64{gc.whiteX, gc.whiteY},
		)
		if ok && kr > 0 && kb > 0 && 1-kr-kb > 0 {
			hasMatrix = true
			linearMatrix = matrix
		}
	}
	if !hasGamma && !hasMatrix {
		return nil
	}
	return &imageGammaChromaTransform{
		hasGamma:     hasGamma,
		invGamma:     invGamma,
		hasMatrix:    hasMatrix,
		linearMatrix: linearMatrix,
	}
}

// toLinearSRGB 将归一化PNG像素按gAMA与cHRM转换为D65线性scRGB，灰度图像仅执行伽马解码
// 入参: r, g, b 源像素分量, gray 是否为单通道灰度源
// 返回: [3]float64 D65线性scRGB三通道
func (t *imageGammaChromaTransform) toLinearSRGB(r, g, b float64, gray bool) [3]float64 {
	if gray {
		v := colorClamp(r)
		if t.hasGamma {
			v = math.Pow(v, t.invGamma)
		} else {
			v = renderSRGBToLinear(v)
		}
		return [3]float64{v, v, v}
	}
	rgb := [3]float64{colorClamp(r), colorClamp(g), colorClamp(b)}
	for i, v := range rgb {
		if t.hasGamma {
			rgb[i] = math.Pow(v, t.invGamma)
		} else {
			rgb[i] = renderSRGBToLinear(v)
		}
	}
	if !t.hasMatrix {
		return rgb
	}
	return iccMatrixColor(t.linearMatrix, rgb)
}

// cicpPrimariesMatrix 由ITU-T H.273基色代码计算源线性RGB到D65线性sRGB矩阵及红蓝亮度权重
// 入参: code H.273基色代码
// 返回: [9]float64 源线性RGB到线性sRGB矩阵, float64 红基色亮度权重, float64 蓝基色亮度权重, bool 是否受支持
func cicpPrimariesMatrix(code uint8) ([9]float64, float64, float64, bool) {
	const d65x, d65y = 0.3127, 0.3290
	wx, wy := d65x, d65y
	var xy [3][2]float64
	switch code {
	case 1:
		return [9]float64{1, 0, 0, 0, 1, 0, 0, 0, 1}, 87098.0 / 409605, 12673.0 / 175545, true
	case 4:
		xy, wx, wy = [3][2]float64{{0.67, 0.33}, {0.21, 0.71}, {0.14, 0.08}}, 0.310, 0.316
	case 5:
		xy = [3][2]float64{{0.64, 0.33}, {0.29, 0.60}, {0.15, 0.06}}
	case 6, 7:
		xy = [3][2]float64{{0.630, 0.340}, {0.310, 0.595}, {0.155, 0.070}}
	case 8:
		xy, wx, wy = [3][2]float64{{0.681, 0.319}, {0.243, 0.692}, {0.145, 0.049}}, 0.310, 0.316
	case 9:
		xy = [3][2]float64{{0.708, 0.292}, {0.170, 0.797}, {0.131, 0.046}}
	case 10:
		return iccXYZD65ToLinearRGB, 0, 0, true
	case 11, 12:
		xy = [3][2]float64{{0.680, 0.320}, {0.265, 0.690}, {0.150, 0.060}}
		if code == 11 {
			wx, wy = 0.314, 0.351
		}
	case 22:
		xy = [3][2]float64{{0.630, 0.340}, {0.295, 0.605}, {0.155, 0.077}}
	default:
		return [9]float64{}, 0, 0, false
	}
	return cicpChromaticityToSRGB(xy, [2]float64{wx, wy})
}

// cicpChromaticityToSRGB 根据源基色与源白点色度推导经Bradford适配至D65线性sRGB的三阶矩阵
// 入参: xy 红绿蓝基色色度坐标, whiteXY 源白点色度坐标
// 返回: [9]float64 行优先线性RGB到线性sRGB矩阵, float64 红基色亮度权重, float64 蓝基色亮度权重, bool 矩阵是否有效
func cicpChromaticityToSRGB(xy [3][2]float64, whiteXY [2]float64) ([9]float64, float64, float64, bool) {
	wx, wy := whiteXY[0], whiteXY[1]
	if wx <= 0 || wy <= 0 || wx+wy >= 1 {
		return [9]float64{}, 0, 0, false
	}
	white := [3]float64{wx / wy, 1, (1 - wx - wy) / wy}
	var primaries [9]float64
	for col, p := range xy {
		primaries[col] = p[0]
		primaries[3+col] = p[1]
		primaries[6+col] = 1 - p[0] - p[1]
	}
	invPrimaries, err := iccInverseMatrix(primaries)
	if err != nil {
		return [9]float64{}, 0, 0, false
	}
	scale := iccMatrixColor(invPrimaries, white)
	for row := range 3 {
		for col := range 3 {
			primaries[row*3+col] *= scale[col]
		}
	}
	d65 := [3]float64{0.3127 / 0.3290, 1, (1 - 0.3127 - 0.3290) / 0.3290}
	coneSrc, coneDst := iccMatrixColor(cicpBradford, white), iccMatrixColor(cicpBradford, d65)
	adapt := cicpBradford
	for row := range 3 {
		for col := range 3 {
			adapt[row*3+col] *= coneDst[row] / coneSrc[row]
		}
	}
	cat := cicpMulMatrix3(cicpBradfordInverse, adapt)
	xyzToSRGB := cicpMulMatrix3(iccXYZD65ToLinearRGB, cat)
	out := cicpMulMatrix3(xyzToSRGB, primaries)
	for _, v := range out {
		if !geometryFinite(v) {
			return [9]float64{}, 0, 0, false
		}
	}
	return out, primaries[3], primaries[5], true
}

// cicpMulMatrix3 计算两个行优先三阶矩阵的乘积
// 入参: a 左矩阵, b 右矩阵
// 返回: [9]float64 乘积矩阵
func cicpMulMatrix3(a, b [9]float64) [9]float64 {
	var out [9]float64
	for row := range 3 {
		for col := range 3 {
			for k := range 3 {
				out[row*3+col] += a[row*3+k] * b[k*3+col]
			}
		}
	}
	return out
}

// cicpSDRInverseTransfer 反解ITU-T H.273的SDR及线性传递特性
// 入参: value 非线性分量, transfer 规范化传递特性编号
// 返回: float64 线性光分量
func cicpSDRInverseTransfer(value float64, transfer uint8) float64 {
	switch transfer {
	case 4:
		return math.Pow(max(0, value), 2.2)
	case 5:
		return math.Pow(max(0, value), 2.8)
	case 8:
		return value
	case 9, 10:
		if value <= 0 {
			return 0
		}
		decades := 2.5
		if transfer == 9 {
			decades = 2
		}
		return math.Pow(10, decades*(value-1))
	case 17:
		return (52.37 / 48) * math.Pow(colorClamp(value), 2.6)
	}
	alpha, beta, slope, power := 1.099296826809442, 0.018053968510807, 4.5, 1/0.45
	switch transfer {
	case 7:
		alpha, beta, slope, power = 1.1115721959217313, 0.022821585529445028, 4, 1/0.45
	case 13:
		alpha, beta, slope, power = 1.055, 0.0031308, 12.92, 2.4
	}
	if transfer == 12 && value < -slope*beta/4 {
		return -math.Pow((alpha-1-4*value)/alpha, power) / 4
	}
	magnitude := value
	if transfer == 11 {
		magnitude = math.Abs(value)
	}
	if magnitude <= beta*slope {
		return value / slope
	}
	return math.Copysign(math.Pow((magnitude+alpha-1)/alpha, power), value)
}

// cicpHDRInverseTransfer 将PQ转换为相对10000 cd/m²的显示光或将HLG转换为场景光
// 入参: value 非线性HDR分量, transfer 16(PQ)或18(HLG)
// 返回: float64 线性光强度
func cicpHDRInverseTransfer(value float64, transfer uint8) float64 {
	value = colorClamp(value)
	if transfer == 16 {
		root := math.Pow(value, 1/cicpPQM2)
		return math.Pow(max(root-cicpPQC1, 0)/(cicpPQC2-cicpPQC3*root), 1/cicpPQM1)
	}
	if value <= 0.5 {
		return value * value / 3
	}
	return (math.Exp((value-cicpHLGC)/cicpHLGA) + cicpHLGB) / 12
}

// cicpHLGDisplayLight 按BT.2100-2参考峰值亮度及表5注5f系统伽马公式将HLG场景光转换为归一化显示光，防护极小峰值与极小亮度溢出
// 入参: rgb 线性场景RGB, weights 场景亮度权重, peakNits 参考显示峰值亮度
// 返回: [3]float64 相对peakNits归一化的显示光RGB
func cicpHLGDisplayLight(rgb, weights [3]float64, peakNits float64) [3]float64 {
	luma := weights[0]*rgb[0] + weights[1]*rgb[1] + weights[2]*rgb[2]
	if !(luma > 0) || !geometryFinite(luma) {
		return [3]float64{}
	}
	if !(peakNits > 0) || !geometryFinite(peakNits) {
		peakNits = 1000
	}
	gamma := 1.2
	if peakNits != 1000 {
		if peakNits >= 400 && peakNits <= 2000 {
			gamma = 1.2 + 0.42*math.Log10(peakNits/1000)
		} else {
			gamma = 1.2 * math.Pow(1.111, math.Log2(peakNits)-math.Log2(1000))
		}
	}
	gain := math.Pow(luma, gamma-1)
	lumaGamma := 0.0
	lumaLog := 0.0
	hasFallback := false
	for i := range rgb {
		if rgb[i] == 0 {
			continue
		}
		if geometryFinite(gain) {
			if value := rgb[i] * gain; geometryFinite(value) {
				rgb[i] = value
				continue
			}
		}
		if !hasFallback {
			lumaGamma, lumaLog, hasFallback = math.Pow(luma, gamma), math.Log(luma), true
		}
		if value := (rgb[i] / luma) * lumaGamma; geometryFinite(value) {
			rgb[i] = value
			continue
		}
		value := math.Copysign(math.Exp(math.Log(math.Abs(rgb[i]))+(gamma-1)*lumaLog), rgb[i])
		if !geometryFinite(value) {
			value = math.Copysign(math.MaxFloat64, rgb[i])
		}
		rgb[i] = value
	}
	return rgb
}

// renderBT2446MethodA 按ITU-R BT.2446方法A将相对100 cd/m²的线性scRGB映射至100 cd/m²线性sRGB，低于100 cd/m²恒等裁剪并在100至200 cd/m²按对数权重平滑过渡
// 入参: linearSRGB 相对100 cd/m²归一化的线性scRGB, peakNits HDR标称峰值亮度（cd/m²）
// 返回: [3]float64 映射后的100 cd/m²线性sRGB
func renderBT2446MethodA(linearSRGB [3]float64, peakNits float64) [3]float64 {
	if !(peakNits > 0) || !geometryFinite(peakNits) {
		return linearSRGB
	}
	var clamped [3]float64
	if peakNits < 200 {
		for i, v := range linearSRGB {
			if v > 1 {
				clamped[i] = 1
			} else if v > 0 {
				clamped[i] = v
			}
		}
		if peakNits <= 100 {
			return clamped
		}
	}
	bt2020 := iccMatrixColor(cicpSRGBToBT2020, linearSRGB)
	invPeak := 100.0 / peakNits
	var rgb [3]float64
	for i, v := range bt2020 {
		scaled := v * invPeak
		if !(scaled > 0) {
			rgb[i] = 0
		} else if scaled >= 1 {
			rgb[i] = 1
		} else {
			rgb[i] = math.Pow(scaled, 1/2.4)
		}
	}
	luma := cicpBT2100Red*rgb[0] + cicpBT2100Green*rgb[1] + cicpBT2100Blue*rgb[2]
	var mapped [3]float64
	if luma > 0 {
		hdrRho := 32 * math.Pow(peakNits/10000, 1/2.4)
		perceptual := math.Log1p(hdrRho*luma) / math.Log1p(hdrRho)
		var compressed float64
		switch {
		case perceptual <= 0.7399:
			compressed = 1.0770 * perceptual
		case perceptual < 0.9909:
			compressed = (-1.1510*perceptual+2.7811)*perceptual - 0.6302
		default:
			compressed = 0.5*perceptual + 0.5
		}
		sdr := math.Expm1(cicpBT2446SDRLog*compressed) / cicpBT2446SDRRho
		gain := sdr / (1.1 * luma)
		cb, cr := gain*(rgb[2]-luma)/1.8814, gain*(rgb[0]-luma)/1.4746
		yPrime := sdr - max(0.1*cr, 0)
		red := yPrime + 2*(1-cicpBT2100Red)*cr
		blue := yPrime + 2*(1-cicpBT2100Blue)*cb
		green := (yPrime - cicpBT2100Red*red - cicpBT2100Blue*blue) / cicpBT2100Green
		sdrBT2020 := [3]float64{
			math.Pow(max(0, red), 2.4),
			math.Pow(max(0, green), 2.4),
			math.Pow(max(0, blue), 2.4),
		}
		mapped = iccMatrixColor(cicpBT2020ToSRGB, sdrBT2020)
	}
	if peakNits < 200 {
		t := math.Log2(peakNits / 100)
		for i := range mapped {
			mapped[i] = clamped[i]*(1-t) + mapped[i]*t
		}
	}
	return mapped
}
