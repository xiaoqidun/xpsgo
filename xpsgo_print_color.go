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
	"encoding/base64"
	"encoding/xml"
	"errors"
	"fmt"
	"image"
	"image/color"
	"math"
	"strings"
	"sync"
	"sync/atomic"
)

const (
	// PrintColorOriginal 表示票据未指定目标纸面颜色模式
	PrintColorOriginal PrintColorMode = iota
	// PrintColorPreserve 表示保持彩色输出模式
	PrintColorPreserve
	// PrintColorGrayscale 表示转换为灰度输出模式
	PrintColorGrayscale
	// PrintColorMonochrome 表示转换为黑白单色输出模式
	PrintColorMonochrome
)

const (
	// PrintColorManagementNone 表示不启用额外色彩管理
	PrintColorManagementNone = "None"
	// PrintColorManagementDevice 表示由设备执行色彩管理
	PrintColorManagementDevice = "Device"
	// PrintColorManagementDriver 表示由驱动执行色彩管理
	PrintColorManagementDriver = "Driver"
	// PrintColorManagementSystem 表示由系统执行色彩管理
	PrintColorManagementSystem = "System"
	// PrintColorDeviceUsageMatchToDefault 表示匹配设备默认色彩空间
	PrintColorDeviceUsageMatchToDefault = "MatchToDefault"
	// PrintColorDeviceUsageOverrideDeviceDefault 表示覆盖设备默认色彩空间
	PrintColorDeviceUsageOverrideDeviceDefault = "OverrideDeviceDefault"
	// PrintColorSourceSpaceNone 表示未启用源色彩配置空间
	PrintColorSourceSpaceNone = "None"
	// PrintColorSourceSpaceRGB 表示源色彩配置空间为RGB
	PrintColorSourceSpaceRGB = "RGB"
	// PrintColorSourceSpaceCMYK 表示源色彩配置空间为CMYK
	PrintColorSourceSpaceCMYK = "CMYK"
	// PrintColorDestinationModeApplication 表示由应用程序提供目标色彩配置
	PrintColorDestinationModeApplication = "Application"
	// PrintColorDestinationModeDriverConfiguration 表示由驱动配置决定目标色彩配置
	PrintColorDestinationModeDriverConfiguration = "DriverConfiguration"
	// PrintColorBlendSpaceSRGB 表示混合色彩空间为sRGB
	PrintColorBlendSpaceSRGB = "sRGB"
	// PrintColorBlendSpaceScRGB 表示混合色彩空间为scRGB
	PrintColorBlendSpaceScRGB = "scRGB"
	// PrintColorBlendSpaceICCProfile 表示混合色彩空间由ICC配置指定
	PrintColorBlendSpaceICCProfile = "ICCProfile"
)

// printSurfacePoolMax 定义打印色彩渲染表面复用池的单缓冲区像素上限
const printSurfacePoolMax = 32 * 8 * 32 * 8

// printSurfacePool 复用打印设备原生颜色图块缓冲
var printSurfacePool sync.Pool

// renderPrintColorLinearTable 保存八位sRGB的线性解码值，初始化后只读，供目标页像素转换共享
var renderPrintColorLinearTable = newRenderPrintColorLinearTable()

// PrintColorMode 表示目标纸面的输出色彩，零值表示票据未声明，不改变输出
type PrintColorMode uint8

// PrintColor 保存目标纸面的输出色彩模式及设备、驱动色深意图
// DeviceBitsPerPixel与DriverBitsPerPixel为零表示未声明，均不得为负
type PrintColor struct {
	Mode               PrintColorMode
	DeviceBitsPerPixel int
	DriverBitsPerPixel int
}

// PrintColorProfile 保存票据中的包根ICC引用或独立嵌入数据，两者不同时使用
type PrintColorProfile struct {
	URI  string
	Data []byte
}

// PrintColorPlan 保存有效源页的颜色管理计划，空字符串与IntentDefault表示未声明，URI按包根解析
// Management取PrintColorManagement*常量，DeviceUsage取PrintColorDeviceUsage*常量，SourceSpace取PrintColorSourceSpace*常量
// DestinationMode取PrintColorDestinationMode*常量，BlendSpace取PrintColorBlendSpace*常量
type PrintColorPlan struct {
	Management      string
	DeviceUsage     string
	Intent          RenderingIntent
	Device          PrintColorProfile
	Source          PrintColorProfile
	SourceSpace     string
	Destination     PrintColorProfile
	DestinationMode string
	Blend           PrintColorProfile
	BlendSpace      string
}

// PrintColorOptions 提供设备默认ICC、原生设备ICC及颜色覆盖策略，调用期间不得修改其切片数据
// NativeProfiles仅在匹配Conditions与Colorants顺序时保留原生分量；Override允许显式目标或意图替代票据策略
// 透明混合直接在所选混合空间合成，混合策略差异或跨政策重叠在DeviceImage.Diagnostics中报告
type PrintColorOptions struct {
	Profile        []byte
	Conditions     string
	Colorants      []string
	NativeProfiles [][]byte
	Override       bool
}

// printSurfaceBuffer 保存可复用的八通道打印表面及其预留存活像素预算
type printSurfaceBuffer struct {
	pixels   []printNativeColor
	reserved int
}

// printWorkingSpace 保存本次绘制的颜色编码及已准备的双向连接，不跨调用共享
type printWorkingSpace struct {
	profile      *iccProfile
	forward      *iccTransform
	reverse      *iccTargetTransform
	space        ColorSpace
	channels     int
	intent       RenderingIntent
	outputIntent RenderingIntent
	renderer     *sceneRenderer
	hash         [32]byte
}

// printNativeColor 保存最多八个非预乘颜色分量，alpha与编码身份独立
type printNativeColor struct {
	value  [8]float64
	alpha  float64
	space  *printWorkingSpace
	blend  *printWorkingSpace
	intent RenderingIntent
}

// printNativeSample 在设备坐标中读取保持编码身份的颜色
type printNativeSample func(Point, Point) (printNativeColor, error)

// printColorRuntime 保存一个源页的颜色政策和本次共享资源缓存
type printColorRuntime struct {
	plan          *PrintColorPlan
	options       *PrintColorOptions
	colors        *sceneColorCache
	target        *deviceRenderState
	working       *printWorkingSpace
	device        *printWorkingSpace
	source        *iccProfile
	nativeProfile *iccProfile
	format        Format
	renderer      *sceneRenderer
	transforms    map[*iccProfile][4]*iccTransform
	nativeMatch   map[*iccProfile]bool
}

// String 返回打印输出色彩模式名称
// 返回: string 模式名称
func (m PrintColorMode) String() string {
	switch m {
	case PrintColorOriginal:
		return "Original"
	case PrintColorPreserve:
		return "Preserve"
	case PrintColorGrayscale:
		return "Grayscale"
	case PrintColorMonochrome:
		return "Monochrome"
	default:
		return fmt.Sprintf("PrintColorMode(%d)", m)
	}
}

// printColors 读取源页反色和目标页颜色设置，二者分别在源页合成和目标栅格输出阶段执行
// 返回: bool 是否反色, PrintColor 目标纸面设置, error 结构、类型、范围或能力错误
func (s *printLayoutSettings) printColors() (bool, PrintColor, error) {
	negative, err := s.choice("PageNegativeImage", "None", "None", "Negative")
	if err != nil {
		return false, PrintColor{}, err
	}
	option, feature, err := s.option(s.model.Elements, "PageOutputColor")
	if err != nil || option == nil {
		return negative == "Negative", PrintColor{}, err
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature {
			return false, PrintColor{}, fmt.Errorf("%w: print output color subfeature", ErrUnsupported)
		}
	}
	if err := printOptionProperties(option, "DeviceBitsPerPixel", "DriverBitsPerPixel"); err != nil {
		return false, PrintColor{}, err
	}
	result := PrintColor{}
	if option.Name.Space != printKeywordsNS {
		return false, result, fmt.Errorf("%w: private print output color", ErrUnsupported)
	}
	switch option.Name.Local {
	case "Color":
		result.Mode = PrintColorPreserve
	case "Grayscale":
		result.Mode = PrintColorGrayscale
	case "Monochrome":
		result.Mode = PrintColorMonochrome
	default:
		return false, result, fmt.Errorf("%w: print output color option %s", ErrUnsupported, option.Name.Local)
	}
	for _, field := range []struct {
		name  string
		value *int
	}{
		{"DeviceBitsPerPixel", &result.DeviceBitsPerPixel},
		{"DriverBitsPerPixel", &result.DriverBitsPerPixel},
	} {
		value, err := s.scored(option, field.name)
		if err != nil {
			return false, PrintColor{}, err
		}
		if value == nil {
			continue
		}
		*field.value, err = s.integer(value, field.name, int(^uint(0)>>1))
		if err != nil {
			return false, PrintColor{}, err
		}
	}
	if err := validatePrintColor(result); err != nil {
		return false, PrintColor{}, err
	}
	return negative == "Negative", result, checkContext(s.options.context)
}

// printColorSettings 解析并移除已由打印消费者执行的两种色彩Feature，保留其他设置供后续校验
// 入参: settings 有效票据, options 描述值及取消参数
// 返回: *PrintSettings 只读布局视图, bool 源页反色, PrintColor 目标颜色, error 设置或资源错误
func printColorSettings(settings *PrintSettings, options printSettingsConfig) (*PrintSettings, bool, PrintColor, error) {
	if settings == nil {
		return nil, false, PrintColor{}, fmt.Errorf("%w: nil print color settings", ErrInvalid)
	}
	present := false
	for _, setting := range settings.Elements {
		if setting.Kind == PrintSettingFeature && setting.Name.Space == printKeywordsNS && (setting.Name.Local == "PageOutputColor" || setting.Name.Local == "PageNegativeImage") {
			present = true
			break
		}
	}
	if !present {
		return settings, false, PrintColor{}, checkContext(options.context)
	}
	configuration, err := printSettingsOptions(options.context, &options.PrintSettingsOptions)
	if err != nil {
		return nil, false, PrintColor{}, err
	}
	negative, output, err := newPrintLayoutSettings(settings, configuration).printColors()
	if err != nil {
		return nil, false, PrintColor{}, err
	}
	result := &PrintSettings{Version: settings.Version}
	for _, setting := range settings.Elements {
		if setting.Kind != PrintSettingFeature || setting.Name != (xml.Name{Space: printKeywordsNS, Local: "PageOutputColor"}) && setting.Name != (xml.Name{Space: printKeywordsNS, Local: "PageNegativeImage"}) {
			result.Elements = append(result.Elements, setting)
		}
	}
	return result, negative, output, nil
}

// vector 保留原始矢量颜色的ICC身份及源页意图
// 入参: part 定义部件, value 原始颜色
// 返回: printNativeColor 页面颜色, error 引用或转换错误
func (c *printColorRuntime) vector(part string, value Color) (printNativeColor, error) {
	var components [8]float64
	if len(value.Components) > len(components) {
		return printNativeColor{}, fmt.Errorf("%w: print color channels", ErrInvalid)
	}
	copy(components[:], value.Components)
	var profile *iccProfile
	if value.Space == ColorContext {
		var err error
		profile, err = c.colors.profile(part, value.ProfileURI)
		if err != nil {
			return printNativeColor{}, err
		}
		channels := profile.channels
		if profile.class == "nmcl" {
			named, err := parseICCNamedColor(profile)
			if err != nil {
				return printNativeColor{}, err
			}
			channels = len(named)
		}
		if channels != len(value.Components) {
			return printNativeColor{}, fmt.Errorf("%w: print vector profile channels", ErrInvalid)
		}
	}
	return c.color(profile, components, value.Alpha, value.Space, false)
}

// previewSample 为既有视觉过滤器提供高精度RGB视图，不产生八位中间图像
// 入参: sample 原生分量采样器
// 返回: sceneSample 同位置的RGB采样器
func (c *printColorRuntime) previewSample(sample printNativeSample) sceneSample {
	return func(point, center Point) (renderColor, error) {
		value, err := sample(point, center)
		if err != nil {
			return renderColor{}, err
		}
		space := &printWorkingSpace{space: ColorScRGB, channels: 3}
		if c.renderer.options.space == renderSRGB {
			space.space = ColorSRGB
		}
		value, err = value.convert(space, c.renderer)
		if err != nil {
			return renderColor{}, err
		}
		return renderColor{r: value.value[0] * value.alpha, g: value.value[1] * value.alpha, b: value.value[2] * value.alpha, a: value.alpha}, nil
	}
}

// brush 为打印执行建立保持颜色编码的采样器，复用既有几何和图块映射
// 入参: brush 原始画刷, transform 使用位置变换, aliased 边缘模式, depth 当前深度
// 返回: printNativeSample 原生采样器, error 画刷、资源或预算错误
func (c *printColorRuntime) brush(brush *Brush, transform Matrix, aliased bool, depth int) (printNativeSample, error) {
	r := c.renderer
	if brush == nil || !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 {
		return nil, fmt.Errorf("%w: print brush opacity", ErrInvalid)
	}
	if err := r.charge(1 + uint64(len(brush.Stops))); err != nil {
		return nil, err
	}
	switch brush.Kind {
	case BrushSolidColor:
		value, err := c.vector(brush.Part, brush.Color)
		if err != nil {
			return nil, err
		}
		value.alpha *= brush.Opacity
		return func(Point, Point) (printNativeColor, error) { return value, nil }, nil
	case BrushLinearGradient, BrushRadialGradient:
		return c.gradient(brush, transform)
	case BrushImage:
		return c.image(brush, transform)
	case BrushVisual:
		r.nativeSample = nil
		_, err := r.visualBrush(brush, transform, aliased, depth)
		if err != nil {
			return nil, err
		}
		if r.nativeSample != nil {
			return r.nativeSample, nil
		}
		return func(Point, Point) (printNativeColor, error) { return printNativeColor{}, nil }, nil
	default:
		return nil, fmt.Errorf("%w: print brush kind", ErrUnsupported)
	}
}

// gradient 在已选工作空间逐通道插值，几何与停止点边界沿用共用渐变采样器
// 入参: brush 渐变画刷, transform 使用位置变换
// 返回: printNativeSample 高精度渐变, error 颜色、几何或预算错误
func (c *printColorRuntime) gradient(brush *Brush, transform Matrix) (printNativeSample, error) {
	working := c.working
	if c.format == FormatXPS {
		native, opaque, builtin := false, brush.Opacity == 1, false
		for _, stop := range brush.Stops {
			opaque = opaque && stop.Color.Alpha == 1
			builtin = builtin || stop.Color.Space == ColorSRGB || stop.Color.Space == ColorScRGB
			if stop.Color.Space == ColorContext {
				profile, err := c.colors.profile(brush.Part, stop.Color.ProfileURI)
				if err != nil {
					return nil, err
				}
				verified, err := c.native(profile)
				if err != nil {
					return nil, err
				}
				native = native || verified
			}
		}
		if native && opaque && builtin {
			return nil, fmt.Errorf("%w: opaque XPS native gradient with RGB stops requires an explicit M8.11/M8.25 execution policy", ErrUnsupported)
		}
		if native && opaque {
			working = c.device
			c.target.printDiagnostic("PageBlendColorSpace", "opaque XPS native gradient retains device encoding under M8.11")
		}
	}
	for _, stop := range brush.Stops {
		if stop.Color.Space == ColorSRGB || stop.Color.Space == ColorScRGB {
			space := ColorSRGB
			if brush.ColorInterpolationMode == ColorInterpolationScRGB {
				space = ColorScRGB
			}
			working = &printWorkingSpace{space: space, channels: 3, intent: c.destinationIntent(nil, false)}
			break
		}
	}
	stops := make([]printNativeColor, len(brush.Stops))
	for i, stop := range brush.Stops {
		value, err := c.vector(brush.Part, stop.Color)
		if err != nil {
			return nil, err
		}
		stops[i], err = value.convert(working, c.renderer)
		if err != nil {
			return nil, err
		}
	}
	count := (working.channels + 2) / 3
	var samplers [3]*gradientSampler
	for plane := range count {
		copyBrush := *brush
		copyBrush.ColorInterpolationMode = ColorInterpolationScRGB
		copyBrush.Stops = append([]GradientStop(nil), brush.Stops...)
		for i, stop := range stops {
			values := make([]float64, 3)
			for j := range 3 {
				if channel := plane*3 + j; channel < working.channels {
					values[j] = stop.value[channel]
				}
			}
			copyBrush.Stops[i].Color = Color{Space: ColorScRGB, Alpha: stop.alpha, Components: values}
		}
		var err error
		samplers[plane], err = newGradientSampler(&copyBrush, transform)
		if err != nil {
			return nil, err
		}
	}
	intent := printWorkingIntent(working)
	sourceIntent := c.destinationIntent(nil, false)
	mismatch := sourceIntent != IntentDefault && sourceIntent != intent
	var reported atomic.Bool
	return func(point, _ Point) (printNativeColor, error) {
		if mismatch && !reported.Load() && reported.CompareAndSwap(false, true) {
			c.renderer.options.device.printDiagnostic("PrintColor", "mixed colors use the blend group output intent; per-object destination recommendations apply only before blending")
		}
		value := printNativeColor{space: working, blend: c.working, intent: intent}
		for plane := range count {
			if err := c.renderer.charge(8); err != nil {
				return printNativeColor{}, err
			}
			color, err := samplers[plane].sample(point)
			if err != nil {
				return printNativeColor{}, err
			}
			value.alpha = color.Alpha
			for j := range 3 {
				if channel := plane*3 + j; channel < working.channels {
					value.value[channel] = color.Components[j]
				}
			}
		}
		return value, nil
	}, nil
}

// image 复用原生图像解码及重采样器，在取样前选择正确ICC而不先降为RGB图像
// 入参: brush 图像画刷, transform 使用位置变换
// 返回: printNativeSample 原生图像采样器, error 解码、配置或预算错误
func (c *printColorRuntime) image(brush *Brush, transform Matrix) (printNativeSample, error) {
	if c.renderer.options.image == nil {
		return nil, fmt.Errorf("%w: print image loader", ErrUnsupported)
	}
	source, err := c.renderer.options.image(brush)
	if err != nil {
		return nil, err
	}
	var profile *iccProfile
	profile = source.selectedProfile
	if source.transform != nil {
		profile = source.transform.profile
	}
	if profile == nil && c.source != nil && (c.plan.SourceSpace == PrintColorSourceSpaceRGB && !source.linear && imageColorChannels(source) == 3 || c.plan.SourceSpace == PrintColorSourceSpaceCMYK && imageColorChannels(source) == 4) {
		profile = c.source
		copySource := *source
		copySource.selectedProfile = profile
		source = &copySource
	}
	working := c.working
	native, err := c.native(profile)
	if err != nil {
		return nil, err
	}
	if profile != nil && !native {
		if _, err := c.sourceTransform(profile, true); err != nil {
			if c.format != FormatOpenXPS || !source.associatedProfile || len(source.profile) == 0 || !colorProfileUnusable(err) {
				return nil, err
			}
			part, resolveErr := resolvePart(brush.Part, brush.ImageSource)
			if resolveErr != nil {
				return nil, resolveErr
			}
			fallback, fallbackErr := c.colors.embeddedProfile(part, source.profile, source.profileCompressed)
			if fallbackErr != nil {
				return nil, fallbackErr
			}
			compatible, fallbackErr := imageICCCompatible(source, fallback)
			if fallbackErr != nil {
				return nil, fallbackErr
			}
			if !compatible {
				return nil, fmt.Errorf("%w: fallback print image profile channels", ErrInvalid)
			}
			view := *source
			view.selectedProfile, view.associatedProfile = fallback, false
			source, profile = &view, fallback
			native, fallbackErr = c.native(profile)
			if fallbackErr != nil {
				return nil, fallbackErr
			}
			if !native {
				if _, fallbackErr = c.sourceTransform(profile, true); fallbackErr != nil {
					return nil, fallbackErr
				}
			}
		}
	}
	if native {
		working = c.device
	}
	count := (working.channels + 2) / 3
	var samplers [3]*imageSampler
	for plane := range count {
		sampler, err := newImageSampler(brush, source, transform, renderScRGB)
		if err != nil {
			return nil, err
		}
		sampler.charge, sampler.reserve = c.renderer.charge, c.renderer.reservePixels
		sampler.convert = func(components [8]float64, alpha float64) (renderColor, error) {
			space := ColorSRGB
			if source.linear {
				space = ColorScRGB
			}
			value, err := c.color(profile, components, alpha, space, true)
			if err != nil {
				return renderColor{}, err
			}
			value, err = value.convert(working, c.renderer)
			if err != nil {
				return renderColor{}, err
			}
			packed := renderColor{a: alpha}
			var values [3]float64
			for j := range 3 {
				if channel := plane*3 + j; channel < working.channels {
					values[j] = value.value[channel] * alpha
				}
			}
			packed.r, packed.g, packed.b = values[0], values[1], values[2]
			return packed, nil
		}
		samplers[plane] = sampler
	}
	intent := c.destinationIntent(profile, true)
	return func(point, center Point) (printNativeColor, error) {
		value := printNativeColor{space: working, blend: c.working, intent: intent}
		for plane := range count {
			color, err := samplers[plane].sampleAt(point, center)
			if err != nil {
				return printNativeColor{}, err
			}
			value.alpha = color.a
			if color.a == 0 {
				continue
			}
			for j, component := range [3]float64{color.r, color.g, color.b} {
				if channel := plane*3 + j; channel < working.channels {
					value.value[channel] = component / color.a
				}
			}
		}
		return value, nil
	}, nil
}

// ColorPlan 从已合并打印设置中提取颜色管理计划，不执行设备默认选择或颜色转换
// 入参: ctx 取消Context，nil采用Background, options 票据解析预算，nil采用默认值
// 返回: *PrintColorPlan 独立颜色计划，未声明时为nil, error 结构、引用、预算或取消错误
func (s *PrintSettings) ColorPlan(ctx context.Context, options *PrintSettingsOptions) (*PrintColorPlan, error) {
	ctx = normalizeContext(ctx)
	if s == nil {
		configuration, err := printSettingsOptions(ctx, options)
		if err != nil {
			return nil, err
		}
		return nil, checkContext(configuration.context)
	}
	_, result, err := printColorPlanSettings(ctx, s, options)
	return result, err
}

// PrintColorPlan 解析指定源页的有效颜色票据，不执行设备默认选择或颜色转换
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页号, defaults 消费者基础设置, options 票据解析预算
// 返回: *PrintColorPlan 独立颜色计划，未声明时为nil, error 结构、引用、预算或取消错误
func (r *Reader) PrintColorPlan(ctx context.Context, pageIndex int, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintColorPlan, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	settings, err := r.readPrintSettings(ctx, pageIndex, defaults, options)
	if err != nil {
		return nil, err
	}
	_, result, err := printColorPlanSettings(ctx, settings, options)
	return result, err
}

// printColorPlanSettings 提取标准颜色语义，只有完整验证的设置才从内部执行视图移除
// 入参: ctx 取消Context, model 有效票据, options 资源参数
// 返回: *PrintSettings 剩余设置, *PrintColorPlan 独立颜色计划, error 格式或能力错误
func printColorPlanSettings(ctx context.Context, model *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, *PrintColorPlan, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, nil, err
	}
	root, err := printSettingsRoot(model, configuration)
	if err != nil {
		return nil, nil, err
	}
	validated, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, nil, err
	}
	s := newPrintLayoutSettings(validated, configuration)
	p := &PrintColorPlan{}
	features := []struct {
		name    string
		output  *string
		allowed []string
	}{
		{"PageColorManagement", &p.Management, []string{PrintColorManagementNone, PrintColorManagementDevice, PrintColorManagementDriver, PrintColorManagementSystem}},
		{"PageDeviceColorSpaceUsage", &p.DeviceUsage, []string{PrintColorDeviceUsageMatchToDefault, PrintColorDeviceUsageOverrideDeviceDefault}},
		{"PageBlendColorSpace", &p.BlendSpace, []string{PrintColorBlendSpaceSRGB, PrintColorBlendSpaceScRGB, PrintColorBlendSpaceICCProfile}},
		{"PageSourceColorProfile", &p.SourceSpace, []string{PrintColorSourceSpaceNone, PrintColorSourceSpaceRGB, PrintColorSourceSpaceCMYK}},
		{"PageDestinationColorProfile", &p.DestinationMode, []string{PrintColorDestinationModeApplication, PrintColorDestinationModeDriverConfiguration}},
	}
	for _, f := range features {
		option, err := s.leafOption(validated.Elements, f.name)
		if err != nil {
			return nil, nil, err
		}
		if option == nil {
			continue
		}
		if option.Name.Space != printKeywordsNS {
			return nil, nil, fmt.Errorf("%w: private print color option", ErrUnsupported)
		}
		found := false
		for _, name := range f.allowed {
			if option.Name.Local == name {
				found = true
			}
		}
		if !found {
			return nil, nil, fmt.Errorf("%w: print color option %s", ErrUnsupported, option.Name.Local)
		}
		*f.output = option.Name.Local
		var names []string
		switch f.name {
		case "PageBlendColorSpace":
			if p.BlendSpace == PrintColorBlendSpaceICCProfile {
				names = []string{"URI"}
			}
		case "PageSourceColorProfile":
			if p.SourceSpace != PrintColorSourceSpaceNone {
				names = []string{"SourceColorProfileURI", "SourceColorProfileEmbedded"}
			}
		case "PageDestinationColorProfile":
			if p.DestinationMode == PrintColorDestinationModeApplication {
				names = []string{"DestinationColorProfileURI", "DestinationColorProfileEmbedded"}
			}
		}
		if err := printOptionProperties(option, names...); err != nil {
			return nil, nil, err
		}
	}
	intent, err := s.leafOption(validated.Elements, "PageICMRenderingIntent")
	if err != nil {
		return nil, nil, err
	}
	if intent != nil {
		if err := printOptionProperties(intent); err != nil {
			return nil, nil, err
		}
		if intent.Name.Space != printKeywordsNS {
			return nil, nil, fmt.Errorf("%w: private print rendering intent", ErrUnsupported)
		}
		switch intent.Name.Local {
		case "Photographs":
			p.Intent = IntentPerceptual
		case "RelativeColorimetric":
			p.Intent = IntentRelativeColorimetric
		case "BusinessGraphics":
			p.Intent = IntentSaturation
		case "AbsoluteColorimetric":
			p.Intent = IntentAbsoluteColorimetric
		default:
			return nil, nil, fmt.Errorf("%w: print rendering intent", ErrUnsupported)
		}
	}
	remaining := min(configuration.Limits.MaxPartBytes, configuration.Limits.MaxMetadataBytes, configuration.Limits.MaxPackageBytes)
	if value := s.values[xml.Name{Space: printKeywordsNS, Local: "PageDeviceColorSpaceProfileURI"}]; value != nil {
		p.Device, err = printColorProfileValue(value, false, &remaining)
		if err != nil {
			return nil, nil, err
		}
	}
	for _, f := range []struct {
		feature, uri, embedded string
		output                 *PrintColorProfile
		selected               bool
	}{
		{"PageBlendColorSpace", "URI", "", &p.Blend, p.BlendSpace == PrintColorBlendSpaceICCProfile},
		{"PageSourceColorProfile", "SourceColorProfileURI", "SourceColorProfileEmbedded", &p.Source, p.SourceSpace == PrintColorSourceSpaceRGB || p.SourceSpace == PrintColorSourceSpaceCMYK},
		{"PageDestinationColorProfile", "DestinationColorProfileURI", "DestinationColorProfileEmbedded", &p.Destination, p.DestinationMode == PrintColorDestinationModeApplication},
	} {
		if !f.selected {
			continue
		}
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		option, _, e := s.option(validated.Elements, f.feature)
		if e != nil {
			return nil, nil, e
		}
		if option == nil {
			return nil, nil, fmt.Errorf("%w: missing print color option %s", ErrInvalid, f.feature)
		}
		uri, e := s.scored(option, f.uri)
		if e != nil {
			return nil, nil, e
		}
		var embedded *PrintValue
		if f.embedded != "" {
			embedded, e = s.scored(option, f.embedded)
			if e != nil {
				return nil, nil, e
			}
		}
		if uri == nil && embedded == nil {
			return nil, nil, fmt.Errorf("%w: missing print color profile", ErrUnsupported)
		}
		if uri != nil && embedded != nil {
			return nil, nil, fmt.Errorf("%w: ambiguous print color profile", ErrUnsupported)
		}
		if uri != nil {
			*f.output, err = printColorProfileValue(uri, false, &remaining)
		} else {
			*f.output, err = printColorProfileValue(embedded, true, &remaining)
		}
		if err != nil {
			return nil, nil, err
		}
	}
	result := &PrintSettings{Version: validated.Version}
	present := false
	for _, value := range validated.Elements {
		if printColorPlanName(value.Name) && (value.Kind == PrintSettingFeature || value.Kind == PrintSettingParameterInit) {
			parameter := strings.HasSuffix(value.Name.Local, "URI") || strings.HasSuffix(value.Name.Local, "Embedded")
			if parameter != (value.Kind == PrintSettingParameterInit) {
				return nil, nil, fmt.Errorf("%w: print color keyword kind", ErrInvalid)
			}
			if parameter && (len(value.Children) == 0 || value.Children[0].Value == nil || value.Children[0].Value.Type != (xml.Name{Space: printValueNS, Local: "string"})) {
				return nil, nil, fmt.Errorf("%w: print color parameter type", ErrInvalid)
			}
			present = true
			continue
		}
		result.Elements = append(result.Elements, value)
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, nil, err
	}
	if !present {
		return model, nil, nil
	}
	return result, p, nil
}

// printColorPlanName 识别本执行组解释的公共颜色Feature及标准参数名称
// 入参: name 展开关键字
// 返回: bool 是否属于本组
func printColorPlanName(name xml.Name) bool {
	if name.Space != printKeywordsNS {
		return false
	}
	switch name.Local {
	case "PageColorManagement", "PageDeviceColorSpaceUsage", "PageICMRenderingIntent", "PageBlendColorSpace", "PageSourceColorProfile", "PageDestinationColorProfile", "PageDeviceColorSpaceProfileURI", "PageBlendColorSpaceICCProfileURI", "PageSourceColorProfileURI", "PageSourceColorProfileEmbedded", "PageDestinationColorProfileURI", "PageDestinationColorProfileEmbedded":
		return true
	}
	return false
}

// printColorProfileValue 解析包根URI或有界base64，不访问外部资源
// 入参: value 字符串值, embedded 是否为嵌入数据, remaining 累计数据预算
// 返回: PrintColorProfile 独立描述, error 类型、URI、编码或预算错误
func printColorProfileValue(value *PrintValue, embedded bool, remaining *int64) (PrintColorProfile, error) {
	if value == nil || value.Type != (xml.Name{Space: printValueNS, Local: "string"}) {
		return PrintColorProfile{}, fmt.Errorf("%w: print color profile string", ErrInvalid)
	}
	if !embedded {
		uri, err := opcPartName(value.Text)
		if err != nil {
			return PrintColorProfile{}, err
		}
		return PrintColorProfile{URI: uri}, nil
	}
	if int64(len(value.Text)) > *remaining {
		return PrintColorProfile{}, fmt.Errorf("%w: embedded print profile input", ErrLimit)
	}
	text := strings.Map(func(r rune) rune {
		if r == ' ' || r == '\t' || r == '\r' || r == '\n' {
			return -1
		}
		return r
	}, value.Text)
	if len(text) == 0 || len(text)%4 != 0 {
		return PrintColorProfile{}, fmt.Errorf("%w: embedded print profile base64", ErrInvalid)
	}
	n := base64.StdEncoding.DecodedLen(len(text))
	if strings.HasSuffix(text, "==") {
		n -= 2
	} else if strings.HasSuffix(text, "=") {
		n--
	}
	if int64(n) > *remaining {
		return PrintColorProfile{}, fmt.Errorf("%w: embedded print profile bytes", ErrLimit)
	}
	data, err := base64.StdEncoding.Strict().DecodeString(text)
	if err != nil || len(data) == 0 {
		return PrintColorProfile{}, fmt.Errorf("%w: embedded print profile base64", ErrInvalid)
	}
	*remaining -= int64(len(data))
	return PrintColorProfile{Data: data}, nil
}

// clonePrintColorPlan 复制颜色描述及嵌入数据，避免副本间共享可变载荷
// 入参: source 原颜色计划
// 返回: *PrintColorPlan 独立副本，nil保持nil
func clonePrintColorPlan(source *PrintColorPlan) *PrintColorPlan {
	if source == nil {
		return nil
	}
	result := *source
	result.Device.Data = bytes.Clone(source.Device.Data)
	result.Source.Data = bytes.Clone(source.Source.Data)
	result.Destination.Data = bytes.Clone(source.Destination.Data)
	result.Blend.Data = bytes.Clone(source.Blend.Data)
	return &result
}

// printColorTargetEqual 比较两个源页颜色计划是否共享同一目标声明
// 入参: a, b 两个源页颜色计划
// 返回: bool 是否可共享同一目标声明
func printColorTargetEqual(a, b *PrintColorPlan) bool {
	if a == nil {
		a = &PrintColorPlan{}
	}
	if b == nil {
		b = &PrintColorPlan{}
	}
	overrideA, overrideB := a.DeviceUsage == PrintColorDeviceUsageOverrideDeviceDefault, b.DeviceUsage == PrintColorDeviceUsageOverrideDeviceDefault
	if a.DestinationMode != b.DestinationMode || overrideA != overrideB {
		return false
	}
	if !strings.EqualFold(a.Destination.URI, b.Destination.URI) || !bytes.Equal(a.Destination.Data, b.Destination.Data) {
		return false
	}
	if overrideA && (!strings.EqualFold(a.Device.URI, b.Device.URI) || !bytes.Equal(a.Device.Data, b.Device.Data)) {
		return false
	}
	return true
}

// printSideColorTargetEqual 检查已有纸面是否能接受相同目标声明的源页
// 入参: side 已有纸面, plan 新源页颜色计划
// 返回: bool 是否可以共面
func printSideColorTargetEqual(side PrintSide, plan *PrintColorPlan) bool {
	return len(side.Pages) == 0 || printColorTargetEqual(side.Pages[0].Color, plan)
}

// releasePrintSurfaceBuffer 将常规尺寸打印表面缓冲归还有界对象池并重置预留计数
// 入参: buf 不再使用的打印表面缓冲
func releasePrintSurfaceBuffer(buf *printSurfaceBuffer) {
	if buf == nil || buf.pixels == nil {
		return
	}
	if cap(buf.pixels) > 0 && cap(buf.pixels) <= printSurfacePoolMax {
		pooled := buf.pixels[:cap(buf.pixels)]
		clear(pooled)
		printSurfacePool.Put(&pooled)
	}
	buf.pixels = nil
	buf.reserved = 0
}

// renderPrintColorScene 在独立设备分量表面绘制，支持有界多核图块并行与工作缓冲复用
// 入参: elements 场景, transform 设备变换, bounds 输出范围
// 返回: *image.NRGBA 始终为nil, error 准备、绘制或设备编码错误
func (r *sceneRenderer) renderPrintColorScene(elements []Element, transform Matrix, bounds image.Rectangle) (*image.NRGBA, error) {
	if r.options.device == nil {
		return nil, fmt.Errorf("%w: print color device target", ErrUnsupported)
	}
	if r.options.printSide {
		intent := IntentRelativeColorimetric
		if r.options.printOptions != nil && r.options.printOptions.Override && r.options.device.explicitIntent != IntentDefault {
			intent = r.options.device.explicitIntent
		}
		r.printSideSpace = &printWorkingSpace{space: ColorSRGB, channels: 3, intent: intent}
	}
	r.printContext = make(map[*Canvas]*printColorRuntime)
	if err := r.preparePrintColorContext(elements); err != nil {
		return nil, err
	}
	nodes, err := r.prepare(elements, transform, false, 0)
	if err != nil {
		return nil, err
	}
	if err := r.options.device.allocate(bounds); err != nil {
		return nil, err
	}
	samples := r.options.samples
	var background printNativeColor
	if r.options.background.a != 0 {
		space := ColorScRGB
		if r.options.space == renderSRGB {
			space = ColorSRGB
		}
		background = printNativeColor{
			value: [8]float64{r.options.background.r / r.options.background.a, r.options.background.g / r.options.background.a, r.options.background.b / r.options.background.a},
			alpha: r.options.background.a,
			space: &printWorkingSpace{space: space, channels: 3},
		}
	}
	if bounds.Empty() {
		return nil, nil
	}
	cols := (bounds.Dx() + sceneTileSize - 1) / sceneTileSize
	rows := (bounds.Dy() + sceneTileSize - 1) / sceneTileSize
	tileCount := cols * rows
	tileW := min(sceneTileSize, bounds.Dx()) * samples
	tileH := min(sceneTileSize, bounds.Dy()) * samples
	first := image.Rect(bounds.Min.X*samples, bounds.Min.Y*samples, bounds.Min.X*samples+tileW, bounds.Min.Y*samples+tileH)
	workers := resolveXPSWorkers(r.options.workers, tileCount)
	if r.options.workers == 0 && (tileCount < 4 || bounds.Dx()*bounds.Dy() < 4096) {
		workers = 1
	}
	if workers > 1 {
		available := uint64(max(0, r.options.pixels-r.live))
		perWorker := uint64(tileW) * uint64(tileH) * 4 * uint64(1+sceneMaxIsolatedDepth(nodes))
		if r.hasFiltered {
			if available <= perWorker*2 {
				workers = 1
			} else {
				workers = budgetXPSWorkers(workers, available/2, perWorker)
			}
		} else {
			workers = budgetXPSWorkers(workers, available, perWorker)
		}
	}
	if workers <= 1 {
		storage, err := r.acquirePrintSurface(first)
		if err != nil {
			return nil, err
		}
		defer r.releasePrintSurface(storage)
		worker := acquireSceneWorker()
		defer releaseSceneWorker(worker)
		for y := bounds.Min.Y; y < bounds.Max.Y; y += sceneTileSize {
			for x := bounds.Min.X; x < bounds.Max.X; x += sceneTileSize {
				tileOut := image.Rect(x, y, min(x+sceneTileSize, bounds.Max.X), min(y+sceneTileSize, bounds.Max.Y))
				if err := r.printColorTile(nodes, storage, background, tileOut, worker); err != nil {
					return nil, err
				}
			}
		}
		return nil, nil
	}
	r.initPrintSync()
	surfaces := make([]*printSurfaceBuffer, workers)
	states := make([]*sceneWorkerState, workers)
	defer func() {
		for i := range workers {
			if states[i] != nil {
				releaseSceneWorker(states[i])
			}
			if surfaces[i] != nil {
				r.releasePrintSurface(surfaces[i])
			}
		}
	}()
	for i := range workers {
		surface, err := r.acquirePrintSurface(first)
		if err != nil {
			return nil, err
		}
		surfaces[i] = surface
		states[i] = acquireSceneWorker()
	}
	r.concurrent = true
	err = runXPSWorkerSlots(r.options.context, workers, tileCount, func(runCtx context.Context, slot, task int) error {
		if err := runCtx.Err(); err != nil {
			r.cancelled.Store(true)
			return err
		}
		tx := task % cols
		ty := task / cols
		x := bounds.Min.X + tx*sceneTileSize
		y := bounds.Min.Y + ty*sceneTileSize
		tileOut := image.Rect(x, y, min(x+sceneTileSize, bounds.Max.X), min(y+sceneTileSize, bounds.Max.Y))
		if err := r.printColorTile(nodes, surfaces[slot], background, tileOut, states[slot]); err != nil {
			r.cancelled.Store(true)
			return err
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	return nil, nil
}

// initPrintSync 在并发图块绘制前登记所有带ICC的工作空间并同步已就绪转换状态
func (r *sceneRenderer) initPrintSync() {
	r.printSpaceIndex = make(map[*printWorkingSpace]int, len(r.printContext)*2+1)
	register := func(space *printWorkingSpace) {
		if space == nil || space.profile == nil {
			return
		}
		if _, exists := r.printSpaceIndex[space]; exists {
			return
		}
		r.printSpaceIndex[space] = len(r.printSpaceIndex)
	}
	register(r.printSideSpace)
	for _, runtime := range r.printContext {
		if runtime == nil {
			continue
		}
		register(runtime.working)
		register(runtime.device)
	}
	r.printSpaceFlags = make([]atomic.Uint32, len(r.printSpaceIndex))
	for space, idx := range r.printSpaceIndex {
		var bits uint32
		if space.forward != nil {
			bits |= 1
		}
		if space.reverse != nil {
			bits |= 2
		}
		if bits != 0 {
			r.printSpaceFlags[idx].Store(bits)
		}
	}
	var targetBits uint32
	for i, target := range r.options.device.printTarget {
		if target != nil {
			targetBits |= 1 << uint(i)
		}
	}
	r.printTargetReady.Store(targetBits)
}

// printSpaceBit 查询工作空间指定方向的ICC转换是否已并发安全就绪
// 入参: space 待检工作空间, bit 方向标志位，1表示forward，2表示reverse
// 返回: bool 是否可无锁调用
func (r *sceneRenderer) printSpaceBit(space *printWorkingSpace, bit uint32) bool {
	if space == nil || space.profile == nil {
		return true
	}
	idx, ok := r.printSpaceIndex[space]
	return ok && r.printSpaceFlags[idx].Load()&bit != 0
}

// markPrintSpaceBit 发布工作空间已完成初始化的ICC转换方向标志
// 入参: space 已就绪工作空间, bit 方向标志位
func (r *sceneRenderer) markPrintSpaceBit(space *printWorkingSpace, bit uint32) {
	if space == nil || space.profile == nil {
		return
	}
	if idx, ok := r.printSpaceIndex[space]; ok {
		r.printSpaceFlags[idx].Or(bit)
	}
}

// printConvert 在多核阶段保护首次ICC工作空间懒初始化，就绪后无锁执行颜色空间转换
// 入参: value 源颜色, target 目标工作空间, locked 调用方是否已持有visualMu
// 返回: printNativeColor 转换后颜色, error 预算或变换错误
func (r *sceneRenderer) printConvert(value printNativeColor, target *printWorkingSpace, locked bool) (printNativeColor, error) {
	if value.space == target || value.alpha == 0 || value.space != nil && target != nil && value.space.profile != nil && target.profile != nil && value.space.hash == target.hash {
		value.space = target
		return value, nil
	}
	if !r.concurrent || locked {
		return value.convert(target, r)
	}
	if r.printSpaceBit(value.space, 1) && r.printSpaceBit(target, 2) {
		return value.convert(target, r)
	}
	r.visualMu.Lock()
	defer r.visualMu.Unlock()
	result, err := value.convert(target, r)
	if err == nil {
		if value.space != nil && value.space.forward != nil {
			r.markPrintSpaceBit(value.space, 1)
		}
		if target != nil && target.reverse != nil {
			r.markPrintSpaceBit(target, 2)
		}
	}
	return result, err
}

// printOver 在多核阶段保护首次ICC混合工作空间懒初始化，就绪后无锁执行source-over合成
// 入参: fg 前景颜色, bg 背景颜色, locked 调用方是否已持有visualMu
// 返回: printNativeColor 合成后颜色, error 预算或变换错误
func (r *sceneRenderer) printOver(fg, bg printNativeColor, locked bool) (printNativeColor, error) {
	if !r.concurrent || locked || fg.alpha == 0 || fg.alpha == 1 || bg.alpha == 0 {
		return fg.over(bg, r)
	}
	working := fg.blend
	if r.printSideSpace != nil && bg.blend != nil && working != nil && !printWorkingEquivalent(working, bg.blend) {
		working = r.printSideSpace
	}
	if r.printSpaceBit(fg.space, 1) && r.printSpaceBit(bg.space, 1) && r.printSpaceBit(working, 2) {
		return fg.over(bg, r)
	}
	r.visualMu.Lock()
	defer r.visualMu.Unlock()
	result, err := fg.over(bg, r)
	if err == nil {
		if fg.space != nil && fg.space.forward != nil {
			r.markPrintSpaceBit(fg.space, 1)
		}
		if bg.space != nil && bg.space.forward != nil {
			r.markPrintSpaceBit(bg.space, 1)
		}
		if working != nil && working.reverse != nil {
			r.markPrintSpaceBit(working, 2)
		}
	}
	return result, err
}

// printPixelSafe 在多核阶段保护首次目标意图ICC表懒初始化，就绪后无锁执行设备像素编码
// 入参: x, y 输出坐标, value 合成结果
// 返回: error 转换、预算或数值错误
func (r *sceneRenderer) printPixelSafe(x, y int, value printNativeColor) error {
	if !r.concurrent {
		return r.options.device.printPixel(x, y, value, r)
	}
	if value.alpha == 0 || value.space != nil && value.space.profile != nil && value.space.hash == r.options.device.printProfileHash {
		return r.options.device.printPixel(x, y, value, r)
	}
	intent := value.intent
	if intent == IntentDefault {
		intent = IntentRelativeColorimetric
	}
	bit := uint32(1) << (intent - 1)
	if r.printTargetReady.Load()&bit != 0 && r.printSpaceBit(value.space, 1) {
		return r.options.device.printPixel(x, y, value, r)
	}
	r.visualMu.Lock()
	defer r.visualMu.Unlock()
	err := r.options.device.printPixel(x, y, value, r)
	if err == nil {
		if r.options.device.printTarget[intent-1] != nil {
			r.printTargetReady.Or(bit)
		}
		if value.space != nil && value.space.forward != nil {
			r.markPrintSpaceBit(value.space, 1)
		}
	}
	return err
}

// printColorTile 绘制单个打印颜色图块并降采样编码写入设备输出缓冲
// 入参: nodes 已准备根节点, storage 复用打印表面, background 背景原生颜色, tileOut 输出像素范围, worker 工作Goroutine独占状态
// 返回: error 绘制、预算或编码错误
func (r *sceneRenderer) printColorTile(nodes []*sceneNode, storage *printSurfaceBuffer, background printNativeColor, tileOut image.Rectangle, worker *sceneWorkerState) error {
	samples := r.options.samples
	tile := image.Rect(tileOut.Min.X*samples, tileOut.Min.Y*samples, tileOut.Max.X*samples, tileOut.Max.Y*samples)
	pixels := storage.pixels[:tile.Dx()*tile.Dy()]
	if background.alpha != 0 {
		if err := r.charge(uint64(len(pixels))); err != nil {
			return err
		}
		for i := range pixels {
			pixels[i] = background
		}
	} else {
		clear(pixels)
	}
	for _, node := range nodes {
		if err := r.drawPrintColor(node, pixels, tile, 0, worker); err != nil {
			return err
		}
	}
	for py := tileOut.Min.Y; py < tileOut.Max.Y; py++ {
		for px := tileOut.Min.X; px < tileOut.Max.X; px++ {
			value, err := r.averagePrintColor(pixels, tile, px, py)
			if err != nil {
				return err
			}
			if r.options.outputColor == PrintColorGrayscale || r.options.outputColor == PrintColorMonochrome {
				value, err = r.printConvert(value, &printWorkingSpace{space: ColorScRGB, channels: 3}, false)
				if err != nil {
					return err
				}
				level := colorClamp(.2126*value.value[0] + .7152*value.value[1] + .0722*value.value[2])
				if r.options.outputColor == PrintColorMonochrome {
					if level >= .5 {
						level = 1
					} else {
						level = 0
					}
				}
				value.value = [8]float64{level, level, level}
			}
			if err := r.printPixelSafe(px, py, value); err != nil {
				return err
			}
		}
	}
	return nil
}

// preparePrintColorContext 在字体及图像载入前验证全部源页的设备目标和颜色资源
// 入参: elements 尚未准备的源场景
// 返回: error 票据、profile、预算或取消错误
func (r *sceneRenderer) preparePrintColorContext(elements []Element) error {
	for _, element := range elements {
		if err := r.charge(1); err != nil {
			return err
		}
		canvas, ok := element.(*Canvas)
		if !ok || canvas == nil {
			continue
		}
		if plan, present := r.options.printPlan[canvas]; present {
			value, err := newPrintColorRuntime(plan, r.options.printOptions, r.options.printProfiles, r)
			if err != nil {
				return err
			}
			r.printContext[canvas] = value
		}
		if err := r.preparePrintColorContext(canvas.Elements); err != nil {
			return err
		}
	}
	return nil
}

// reservePrintSurface 检查表面尺寸并预留存活像素预算与工作量
// 入参: bounds 表面像素范围
// 返回: int 像素数量, int 预留存活像素单位, error 容量或取消错误
func (r *sceneRenderer) reservePrintSurface(bounds image.Rectangle) (int, int, error) {
	count := uint64(bounds.Dx()) * uint64(bounds.Dy())
	if count > uint64(^uint(0)>>1)/128 {
		return 0, 0, fmt.Errorf("%w: print channel surface", ErrLimit)
	}
	reserved := int(count) * 4
	if err := r.reservePixels(reserved); err != nil {
		return 0, 0, fmt.Errorf("%w: print channel surface", ErrLimit)
	}
	if err := r.charge(count); err != nil {
		r.releaseLive(reserved)
		return 0, 0, err
	}
	return int(count), reserved, nil
}

// allocPrintSurfacePixels 优先从对象池取出并清零打印表面像素切片，超限时独立分配
// 入参: count 所需像素数
// 返回: []printNativeColor 已清零像素切片
func allocPrintSurfacePixels(count int) []printNativeColor {
	if count <= printSurfacePoolMax {
		if pooled, ok := printSurfacePool.Get().(*[]printNativeColor); ok && pooled != nil && cap(*pooled) >= count {
			pixels := (*pooled)[:count]
			clear(pixels)
			return pixels
		}
	}
	return make([]printNativeColor, count)
}

// acquirePrintSurface 按四个RGB等价单位预留存活预算并从对象池租用八通道打印表面
// 入参: bounds 表面范围
// 返回: *printSurfaceBuffer 可复用打印表面, error 容量或取消错误
func (r *sceneRenderer) acquirePrintSurface(bounds image.Rectangle) (*printSurfaceBuffer, error) {
	count, reserved, err := r.reservePrintSurface(bounds)
	if err != nil {
		return nil, err
	}
	return &printSurfaceBuffer{pixels: allocPrintSurfacePixels(count), reserved: reserved}, nil
}

// releasePrintSurface 归还打印表面缓冲并按原始预留容量精确释放存活像素预算
// 入参: buf 待释放的打印表面
func (r *sceneRenderer) releasePrintSurface(buf *printSurfaceBuffer) {
	if buf == nil {
		return
	}
	reserved := buf.reserved
	releasePrintSurfaceBuffer(buf)
	r.releaseLive(reserved)
}

// acquirePrintIsolatedSurface 按嵌套深度复用工作Goroutine的打印隔离表面并扣减存活像素预算
// 入参: bounds 子像素范围, depth 当前隔离深度, worker 工作Goroutine独占状态
// 返回: *printSurfaceBuffer 已清零的打印隔离表面, error 容量或取消错误
func (r *sceneRenderer) acquirePrintIsolatedSurface(bounds image.Rectangle, depth int, worker *sceneWorkerState) (*printSurfaceBuffer, error) {
	count, reserved, err := r.reservePrintSurface(bounds)
	if err != nil {
		return nil, err
	}
	for len(worker.printIsolated) <= depth {
		worker.printIsolated = append(worker.printIsolated, nil)
	}
	buf := worker.printIsolated[depth]
	if buf != nil && cap(buf.pixels) >= count {
		buf.pixels = buf.pixels[:count]
		buf.reserved = reserved
		clear(buf.pixels)
		return buf, nil
	}
	if buf != nil {
		releasePrintSurfaceBuffer(buf)
		worker.printIsolated[depth] = nil
	}
	buf = &printSurfaceBuffer{pixels: allocPrintSurfacePixels(count), reserved: reserved}
	worker.printIsolated[depth] = buf
	return buf, nil
}

// samplePrintPaint 使用保持原生编码的画刷，固有RGB位图字形走高精度连接
// 入参: node 所属节点, paint 画笔, point, center 采样坐标
// 返回: printNativeColor 颜色, error 采样或转换错误
func (r *sceneRenderer) samplePrintPaint(node *sceneNode, paint scenePaint, point, center Point) (printNativeColor, error) {
	if paint.native != nil {
		return paint.native(point, center)
	}
	value, err := paint.sample(point, center)
	if err != nil || value.a == 0 {
		return printNativeColor{}, err
	}
	if node.color == nil {
		return printNativeColor{}, fmt.Errorf("%w: missing page print color context", ErrInvalid)
	}
	space := ColorScRGB
	if r.options.space == renderSRGB {
		space = ColorSRGB
	}
	return node.color.color(nil, [8]float64{value.r / value.a, value.g / value.a, value.b / value.a}, value.a, space, false)
}

// drawPrintColorPaint 按相交覆盖掩码逐像素采样并合成单条打印画笔，并发遇非无锁画刷时以Defer保障互斥锁释放
// 入参: node 所属节点, paint 画笔, mask 覆盖掩码, surface 目标表面, bounds 目标表面子像素范围, subBounds 实际绘制子像素范围, scale 采样缩放系数
// 返回: error 采样、预算或合成错误
func (r *sceneRenderer) drawPrintColorPaint(node *sceneNode, paint scenePaint, mask *image.Alpha, surface []printNativeColor, bounds, subBounds image.Rectangle, scale float64) error {
	needLock := r.concurrent && (paint.visual || paint.native == nil)
	locked := false
	if needLock {
		defer func() {
			if locked {
				r.visualMu.Unlock()
			}
		}()
	}
	stride := bounds.Dx()
	for y := subBounds.Min.Y; y < subBounds.Max.Y; y++ {
		rowBase := (y - bounds.Min.Y) * stride
		for x := subBounds.Min.X; x < subBounds.Max.X; x++ {
			if mask.AlphaAt(x, y).A == 0 {
				continue
			}
			if needLock && !locked {
				r.visualMu.Lock()
				locked = true
			}
			point := Point{(float64(x) + .5) / scale, (float64(y) + .5) / scale}
			value, err := r.samplePrintPaint(node, paint, point, scenePixelCenter(point))
			if err != nil {
				return err
			}
			at := rowBase + x - bounds.Min.X
			surface[at], err = r.printOver(value, surface[at], locked)
			if err != nil {
				return err
			}
		}
	}
	return nil
}

// drawPrintColor 复用区域覆盖和层级隔离规则，在八通道表面按实际相交子区域完成合成
// 入参: node 节点, target 背景表面, bounds 子像素范围, isoDepth 当前隔离嵌套深度, worker 工作Goroutine独占状态
// 返回: error 采样、资源或颜色错误
func (r *sceneRenderer) drawPrintColor(node *sceneNode, target []printNativeColor, bounds image.Rectangle, isoDepth int, worker *sceneWorkerState) error {
	if err := r.charge(1); err != nil {
		return err
	}
	samples := r.options.samples
	coarse := image.Rect(bounds.Min.X/samples, bounds.Min.Y/samples, bounds.Max.X/samples, bounds.Max.Y/samples)
	nodeTile := node.bounds.Intersect(coarse)
	if node.opacity == 0 || nodeTile.Empty() {
		return nil
	}
	isolated := node.opacity != 1 || node.mask != nil || node.clip != nil || node.negative
	surface := target
	surfaceBounds := bounds
	drawBounds := coarse
	nextDepth := isoDepth
	if isolated {
		isoBounds := image.Rect(nodeTile.Min.X*samples, nodeTile.Min.Y*samples, nodeTile.Max.X*samples, nodeTile.Max.Y*samples).Intersect(bounds)
		if isoBounds.Empty() {
			return nil
		}
		isoBuf, err := r.acquirePrintIsolatedSurface(isoBounds, isoDepth, worker)
		if err != nil {
			return err
		}
		defer func() {
			reserved := isoBuf.reserved
			isoBuf.reserved = 0
			r.releaseLive(reserved)
		}()
		surface = isoBuf.pixels
		surfaceBounds = isoBounds
		drawBounds = nodeTile
		nextDepth = isoDepth + 1
	}
	scale := float64(samples)
	for _, paint := range node.paints {
		paintTile := paint.bounds.Intersect(drawBounds)
		if paintTile.Empty() {
			continue
		}
		subBounds := image.Rect(paintTile.Min.X*samples, paintTile.Min.Y*samples, paintTile.Max.X*samples, paintTile.Max.Y*samples).Intersect(surfaceBounds)
		if subBounds.Empty() {
			continue
		}
		regions := paint.regions
		if len(paint.regionBounds) == len(paint.regions) {
			filtered := worker.regions[:0]
			for i, rb := range paint.regionBounds {
				if rb.Overlaps(paintTile) {
					filtered = append(filtered, paint.regions[i])
				}
			}
			worker.regions = filtered
			if len(filtered) == 0 {
				continue
			}
			regions = filtered
		}
		minY, maxY := float64(subBounds.Min.Y), float64(subBounds.Max.Y)
		if paint.aliased {
			minY, maxY = float64(paintTile.Min.Y), float64(paintTile.Max.Y)
		}
		var edgeCost uint64
		for _, region := range regions {
			edgeCost += sceneRegionEdgeCost(region, minY, maxY)
		}
		if err := r.charge(uint64(subBounds.Dx())*uint64(subBounds.Dy()) + edgeCost); err != nil {
			return err
		}
		mask, err := r.coverageScratch(regions, paint.aliased, subBounds, &worker.mask, worker)
		if err != nil {
			return err
		}
		if err := r.drawPrintColorPaint(node, paint, mask, surface, surfaceBounds, subBounds, scale); err != nil {
			return err
		}
	}
	for _, child := range node.children {
		if err := r.drawPrintColor(child, surface, surfaceBounds, nextDepth, worker); err != nil {
			return err
		}
	}
	if !isolated {
		return nil
	}
	var clip *image.Alpha
	if node.clip != nil {
		minY, maxY := float64(surfaceBounds.Min.Y), float64(surfaceBounds.Max.Y)
		if node.aliased {
			minY, maxY = float64(nodeTile.Min.Y), float64(nodeTile.Max.Y)
		}
		if err := r.charge(sceneRegionEdgeCost(*node.clip, minY, maxY)); err != nil {
			return err
		}
		var err error
		clip, err = r.coverageScratch([]rasterRegion{*node.clip}, node.aliased, surfaceBounds, &worker.clip, worker)
		if err != nil {
			return err
		}
	}
	needMaskLock := r.concurrent && node.maskVisual
	maskLocked := false
	if needMaskLock {
		defer func() {
			if maskLocked {
				r.visualMu.Unlock()
			}
		}()
	}
	srcStride := surfaceBounds.Dx()
	dstStride := bounds.Dx()
	for y := surfaceBounds.Min.Y; y < surfaceBounds.Max.Y; y++ {
		srcRowBase := (y - surfaceBounds.Min.Y) * srcStride
		dstRowBase := (y - bounds.Min.Y) * dstStride
		for x := surfaceBounds.Min.X; x < surfaceBounds.Max.X; x++ {
			srcAt := srcRowBase + x - surfaceBounds.Min.X
			value := surface[srcAt]
			if value.alpha == 0 || clip != nil && clip.AlphaAt(x, y).A == 0 {
				continue
			}
			if err := r.charge(8); err != nil {
				return err
			}
			point := Point{(float64(x) + .5) / scale, (float64(y) + .5) / scale}
			if node.nativeMask != nil {
				if needMaskLock && !maskLocked {
					r.visualMu.Lock()
					maskLocked = true
				}
				mask, err := node.nativeMask(point, scenePixelCenter(point))
				if err != nil {
					return err
				}
				value.alpha *= mask.alpha
			} else if node.mask != nil {
				if needMaskLock && !maskLocked {
					r.visualMu.Lock()
					maskLocked = true
				}
				mask, err := node.mask(point, scenePixelCenter(point))
				if err != nil {
					return err
				}
				value.alpha *= mask.a
			}
			value.alpha *= node.opacity
			if node.negative {
				var err error
				value, err = r.printConvert(value, &printWorkingSpace{space: ColorSRGB, channels: 3}, maskLocked)
				if err != nil {
					return err
				}
				for i := range 3 {
					value.value[i] = 1 - value.value[i]
				}
			}
			dstAt := dstRowBase + x - bounds.Min.X
			var err error
			target[dstAt], err = r.printOver(value, target[dstAt], maskLocked)
			if err != nil {
				return err
			}
		}
	}
	return nil
}

// averagePrintColor 在工作空间按预乘覆盖率降采样，均匀原生内区不执行RGB往返
// 入参: pixels 子像素表面, bounds 子像素范围, x, y 输出位置
// 返回: printNativeColor 降采样结果, error 转换或预算错误
func (r *sceneRenderer) averagePrintColor(pixels []printNativeColor, bounds image.Rectangle, x, y int) (printNativeColor, error) {
	samples := r.options.samples
	first := pixels[(y*samples-bounds.Min.Y)*bounds.Dx()+x*samples-bounds.Min.X]
	uniform := true
	for j := range samples {
		for i := range samples {
			value := pixels[(y*samples+j-bounds.Min.Y)*bounds.Dx()+x*samples+i-bounds.Min.X]
			if value != first {
				uniform = false
			}
		}
	}
	if uniform {
		return first, nil
	}
	working := first.blend
	sideSpace := r.printSideSpace
	for j := range samples {
		for i := range samples {
			value := pixels[(y*samples+j-bounds.Min.Y)*bounds.Dx()+x*samples+i-bounds.Min.X]
			if working == nil && value.blend != nil && value.alpha != 0 {
				working = value.blend
			}
			if sideSpace != nil && working != sideSpace && value.alpha != 0 && value.blend != nil && working != nil && !printWorkingEquivalent(working, value.blend) {
				working = sideSpace
				r.options.device.printDiagnostic("PrintSide", "overlapping source-page blend policies use the shared sRGB side space")
			}
		}
	}
	intent := printWorkingIntent(working)
	result := printNativeColor{space: working, blend: working, intent: intent}
	count := 3
	if working != nil {
		count = working.channels
	}
	factor := 1 / float64(samples*samples)
	reported := false
	for j := range samples {
		for i := range samples {
			value := pixels[(y*samples+j-bounds.Min.Y)*bounds.Dx()+x*samples+i-bounds.Min.X]
			if !reported && value.intent != IntentDefault && value.intent != intent {
				r.options.device.printDiagnostic("PrintColor", "mixed colors use the blend group output intent; per-object destination recommendations apply only before blending")
				reported = true
			}
			if value.alpha == 0 {
				continue
			}
			var err error
			value, err = r.printConvert(value, working, false)
			if err != nil {
				return printNativeColor{}, err
			}
			weight := value.alpha * factor
			result.alpha += weight
			for channel := range count {
				result.value[channel] += value.value[channel] * weight
			}
		}
	}
	if result.alpha != 0 {
		for channel := range count {
			result.value[channel] /= result.alpha
		}
	}
	return result, nil
}

// samplePrintColorNode 在单个位置完成视觉画刷的原生分量隔离合成
// 入参: node 节点, point, center 设备坐标
// 返回: printNativeColor 颜色, error 几何、采样或预算错误
func (r *sceneRenderer) samplePrintColorNode(node *sceneNode, point, center Point) (printNativeColor, error) {
	if err := r.charge(1); err != nil {
		return printNativeColor{}, err
	}
	if node.opacity == 0 {
		return printNativeColor{}, nil
	}
	if node.clip != nil {
		inside, err := r.regionContains(*node.clip, point, center, node.aliased)
		if err != nil || !inside {
			return printNativeColor{}, err
		}
	}
	var result printNativeColor
	for _, paint := range node.paints {
		inside := false
		for _, region := range paint.regions {
			var err error
			inside, err = r.regionContains(region, point, center, paint.aliased)
			if err != nil {
				return printNativeColor{}, err
			}
			if inside {
				break
			}
		}
		if !inside {
			continue
		}
		value, err := r.samplePrintPaint(node, paint, point, center)
		if err != nil {
			return printNativeColor{}, err
		}
		result, err = value.over(result, r)
		if err != nil {
			return printNativeColor{}, err
		}
	}
	for _, child := range node.children {
		value, err := r.samplePrintColorNode(child, point, center)
		if err != nil {
			return printNativeColor{}, err
		}
		result, err = value.over(result, r)
		if err != nil {
			return printNativeColor{}, err
		}
	}
	if node.nativeMask != nil {
		mask, err := node.nativeMask(point, center)
		if err != nil {
			return printNativeColor{}, err
		}
		result.alpha *= mask.alpha
	} else if node.mask != nil {
		mask, err := node.mask(point, center)
		if err != nil {
			return printNativeColor{}, err
		}
		result.alpha *= mask.a
	}
	result.alpha *= node.opacity
	if node.negative && result.alpha != 0 {
		var err error
		result, err = result.convert(&printWorkingSpace{space: ColorSRGB, channels: 3}, r)
		if err != nil {
			return printNativeColor{}, err
		}
		for i := range 3 {
			result.value[i] = 1 - result.value[i]
		}
	}
	return result, nil
}

// printColorImage 先选择有效图像ICC，设备执行在实际需要时才准备源转换
// 入参: brush 图像画刷, part 图像部件, source 不可变原始图像
// 返回: *rasterImage 具有独立颜色选择的视图, error 引用、profile或资源错误
func (c *sceneImageCache) printColorImage(brush *Brush, part string, source *rasterImage) (*rasterImage, error) {
	if err := checkContext(c.context); err != nil {
		return nil, err
	}
	if brush.ImageProfileURI == "" && len(source.profile) == 0 {
		return source, nil
	}
	if c.colors == nil {
		return nil, fmt.Errorf("%w: print image ICC loader", ErrUnsupported)
	}
	var associatedErr error
	if brush.ImageProfileURI != "" {
		profile, unusable, err := c.colors.profileUsability(brush.Part, brush.ImageProfileURI, c.context)
		if err != nil && !unusable {
			return nil, err
		}
		if err == nil {
			compatible, e := imageICCCompatible(source, profile)
			if e != nil {
				err = e
			} else if compatible {
				value := *source
				value.selectedProfile = profile
				value.associatedProfile = true
				return &value, nil
			} else {
				if c.format == FormatXPS {
					return defaultImageProfile(source), nil
				}
				err = fmt.Errorf("%w: associated print image profile channels", ErrInvalid)
			}
		}
		associatedErr = err
		if c.format == FormatXPS && err != nil {
			return nil, err
		}
	}
	if len(source.profile) != 0 {
		profile, err := c.colors.embeddedProfile(part, source.profile, source.profileCompressed)
		if err != nil {
			return nil, errors.Join(associatedErr, err)
		}
		compatible, err := imageICCCompatible(source, profile)
		if err != nil {
			return nil, errors.Join(associatedErr, err)
		}
		if !compatible {
			if c.format == FormatXPS {
				return defaultImageProfile(source), nil
			}
			return nil, errors.Join(associatedErr, fmt.Errorf("%w: embedded print image profile channels", ErrInvalid))
		}
		value := *source
		value.selectedProfile = profile
		return &value, nil
	}
	return nil, associatedErr
}

// newRenderPrintColorLinearTable 预计算八位sRGB解码，避免在每个目标像素内重复执行幂运算
// 返回: [256]float64 按八位通道值索引的有限线性分量表
func newRenderPrintColorLinearTable() [256]float64 {
	var result [256]float64
	for i := range result {
		result[i] = renderSRGBToLinear(float64(i) / 255)
	}
	return result
}

// validatePrintColor 校验目标页颜色模式与设备、驱动色深组合是否合法
// 入参: value 目标页颜色设置
// 返回: error 模式或色深组合错误
func validatePrintColor(value PrintColor) error {
	switch value.Mode {
	case PrintColorOriginal:
		if value.DeviceBitsPerPixel != 0 || value.DriverBitsPerPixel != 0 {
			return fmt.Errorf("%w: unspecified print output color has bit depth", ErrInvalid)
		}
	case PrintColorPreserve, PrintColorGrayscale, PrintColorMonochrome:
		if value.DeviceBitsPerPixel < 0 || value.DriverBitsPerPixel < 0 {
			return fmt.Errorf("%w: print output color bit depth", ErrInvalid)
		}
	default:
		return fmt.Errorf("%w: print output color mode %d", ErrInvalid, value.Mode)
	}
	return nil
}

// renderPrintOutputColor 按目标页颜色模式将非预乘sRGB像素转换为NRGBA并保留alpha通道
// 入参: value 非预乘八位sRGB像素, mode 目标页颜色模式
// 返回: color.NRGBA 转换后的像素, error 模式错误
func renderPrintOutputColor(value color.NRGBA, mode PrintColorMode) (color.NRGBA, error) {
	switch mode {
	case PrintColorOriginal, PrintColorPreserve:
		return value, nil
	case PrintColorGrayscale, PrintColorMonochrome:
	default:
		return color.NRGBA{}, fmt.Errorf("%w: print output color mode %d", ErrInvalid, mode)
	}
	luminance := 0.2126*renderPrintColorLinearTable[value.R] + 0.7152*renderPrintColorLinearTable[value.G] + 0.0722*renderPrintColorLinearTable[value.B]
	var level uint8
	if mode == PrintColorMonochrome {
		if luminance >= 0.5 {
			level = 255
		}
	} else {
		level = uint8(math.Floor(colorClamp(renderLinearToSRGB(luminance))*255 + 0.5))
	}
	return color.NRGBA{R: level, G: level, B: level, A: value.A}, nil
}

// filteredVisual 在所选混合空间复用有界视觉积分，不经过RGB或八位中间图像
// 入参: source 已准备的视觉过滤器
// 返回: printNativeSample 保留最多八个分量的积分采样器
func (c *printColorRuntime) filteredVisual(source *visualBrushFilter) printNativeSample {
	working := c.working
	count := (working.channels + 2) / 3
	var filters [3]visualBrushFilter
	for plane := range count {
		filters[plane] = *source
		filters[plane].read = func(point, center Point) (renderColor, error) {
			value, err := c.renderer.samplePrintColorNode(source.node, point, center)
			if err != nil {
				return renderColor{}, err
			}
			value, err = value.convert(working, c.renderer)
			if err != nil {
				return renderColor{}, err
			}
			c.renderer.printMixIntent(working, value.intent)
			var values [3]float64
			for j := range 3 {
				if channel := plane*3 + j; channel < working.channels {
					values[j] = value.value[channel] * value.alpha
				}
			}
			return renderColor{r: values[0], g: values[1], b: values[2], a: value.alpha}, nil
		}
	}
	intent := printWorkingIntent(working)
	return func(point, center Point) (printNativeColor, error) {
		result := printNativeColor{space: working, blend: working, intent: intent}
		for plane := range count {
			value, err := filters[plane].sample(point, center)
			if err != nil {
				return printNativeColor{}, err
			}
			result.alpha = value.a
			if value.a == 0 {
				continue
			}
			for j, component := range [3]float64{value.r, value.g, value.b} {
				if channel := plane*3 + j; channel < working.channels {
					result.value[channel] = component / value.a
				}
			}
		}
		return result, nil
	}
}

// profileData 按包根或嵌入数据读取ICC，计入共用的数量和字节预算
// 入参: ref 票据资源描述
// 返回: *iccProfile 只读profile，未声明为nil, error 资源或解析错误
func (c *printColorRuntime) profileData(ref PrintColorProfile) (*iccProfile, error) {
	if ref.URI != "" && len(ref.Data) != 0 {
		return nil, fmt.Errorf("%w: ambiguous print profile", ErrInvalid)
	}
	if ref.URI != "" {
		if c.colors.profiles[strings.ToLower(ref.URI)] == nil {
			size, err := c.colors.pkg.partSize(strings.ToLower(ref.URI))
			if err != nil {
				return nil, err
			}
			if err := c.renderer.charge(size); err != nil {
				return nil, err
			}
		}
		return c.colors.profile("/", ref.URI)
	}
	if len(ref.Data) == 0 {
		return nil, nil
	}
	key := fmt.Sprintf("#print:%x", sha256.Sum256(ref.Data))
	if p := c.colors.profiles[key]; p != nil {
		return p, nil
	}
	if err := c.renderer.charge(uint64(len(ref.Data))); err != nil {
		return nil, err
	}
	if len(c.colors.profiles)+len(c.colors.profileErrors) >= c.colors.maxProfiles || int64(len(ref.Data)) > c.colors.bytes {
		return nil, fmt.Errorf("%w: print ICC budget", ErrLimit)
	}
	return c.colors.cacheProfile(key, ref.Data)
}

// newPrintWorkingSpace 建立明确意图的ICC编码，使用时才准备所需方向
// 入参: profile ICC，nil采用space, space 内建编码, intent 连接意图, r 场景渲染器
// 返回: *printWorkingSpace 独立编码, error 方向、表或预算错误
func newPrintWorkingSpace(profile *iccProfile, space ColorSpace, intent RenderingIntent, r *sceneRenderer) (*printWorkingSpace, error) {
	result := &printWorkingSpace{profile: profile, space: space, channels: 3, renderer: r}
	if profile == nil {
		return result, nil
	}
	if err := r.charge(uint64(len(profile.data))); err != nil {
		return nil, err
	}
	if intent == IntentDefault {
		intent = IntentRelativeColorimetric
	}
	result.intent, result.channels = intent, profile.channels
	result.hash = sha256.Sum256(profile.data)
	return result, nil
}

// xyz 将非预乘分量连接到D50物理XYZ，保留扩展范围
// 入参: values 编码分量
// 返回: [3]float64 PCS, error 变换或数据错误
func (s *printWorkingSpace) xyz(values [8]float64) ([3]float64, error) {
	if s == nil {
		return [3]float64{values[0], values[1], values[2]}, nil
	}
	if s.profile != nil {
		if s.forward == nil {
			if err := s.renderer.charge(uint64(len(s.profile.data))); err != nil {
				return [3]float64{}, err
			}
			var err error
			s.forward, err = prepareICCTransform(s.profile, uint32(s.intent-1))
			if err != nil {
				return [3]float64{}, err
			}
		}
		if err := s.renderer.charge(printICCSourceWork(s.forward)); err != nil {
			return [3]float64{}, err
		}
		return s.forward.toXYZ(values[:s.channels])
	}
	rgb := [3]float64{values[0], values[1], values[2]}
	if s.space == ColorSRGB {
		for i := range rgb {
			rgb[i] = renderSRGBToLinear(colorClamp(rgb[i]))
		}
	}
	return iccMatrixColor(iccPCSFromLinearRGB, rgb), nil
}

// encode 将D50物理XYZ连接到工作编码，不量化中间分量
// 入参: xyz PCS
// 返回: [8]float64 工作分量, error 变换错误
func (s *printWorkingSpace) encode(xyz [3]float64) ([8]float64, error) {
	if s == nil {
		return [8]float64{xyz[0], xyz[1], xyz[2]}, nil
	}
	if s.profile != nil {
		if s.reverse == nil {
			if err := s.renderer.charge(uint64(len(s.profile.data))); err != nil {
				return [8]float64{}, err
			}
			var err error
			s.reverse, err = prepareICCTarget(s.profile, uint32(s.intent-1), s.renderer.options.context)
			if err != nil {
				return [8]float64{}, err
			}
		}
		if err := s.renderer.charge(iccTargetWork(s.reverse)); err != nil {
			return [8]float64{}, err
		}
		return s.reverse.fromXYZ(xyz)
	}
	rgb := iccMatrixColor(iccPCSDisplayMatrix, xyz)
	if s.space == ColorSRGB {
		for i := range rgb {
			rgb[i] = renderLinearToSRGB(colorClamp(rgb[i]))
		}
	}
	return [8]float64{rgb[0], rgb[1], rgb[2]}, nil
}

// convert 保持相同编码的原始分量，否则通过PCS作一次明确连接
// 入参: target 目标工作编码, r 场景渲染器
// 返回: printNativeColor 目标编码颜色, error 预算或变换错误
func (c printNativeColor) convert(target *printWorkingSpace, r *sceneRenderer) (printNativeColor, error) {
	if c.space == target || c.alpha == 0 || c.space != nil && target != nil && c.space.profile != nil && target.profile != nil && c.space.hash == target.hash {
		c.space = target
		return c, nil
	}
	if err := r.charge(128); err != nil {
		return printNativeColor{}, err
	}
	xyz, err := c.space.xyz(c.value)
	if err != nil {
		return printNativeColor{}, err
	}
	value, err := target.encode(xyz)
	if err != nil {
		return printNativeColor{}, err
	}
	c.value, c.space = value, target
	return c, nil
}

// over 按当前源页混合空间执行source-over，满覆盖前景不丢失原生编码身份
// 入参: background 背景颜色, r 场景渲染器
// 返回: printNativeColor 合成颜色, error 变换或预算错误
func (c printNativeColor) over(background printNativeColor, r *sceneRenderer) (printNativeColor, error) {
	if c.alpha == 0 {
		return background, nil
	}
	if c.alpha == 1 || background.alpha == 0 {
		return c, nil
	}
	working := c.blend
	if r.printSideSpace != nil && background.blend != nil && working != nil && !printWorkingEquivalent(working, background.blend) {
		working = r.printSideSpace
		r.options.device.printDiagnostic("PrintSide", "overlapping source-page blend policies use the shared sRGB side space")
	}
	foreground, err := c.convert(working, r)
	if err != nil {
		return printNativeColor{}, err
	}
	back, err := background.convert(working, r)
	if err != nil {
		return printNativeColor{}, err
	}
	alpha := foreground.alpha + back.alpha*(1-foreground.alpha)
	count := 3
	if working != nil {
		count = working.channels
	}
	for i := range count {
		foreground.value[i] = (foreground.value[i]*foreground.alpha + back.value[i]*back.alpha*(1-foreground.alpha)) / alpha
	}
	foreground.alpha = alpha
	foreground.blend = working
	foreground.intent = r.printMixIntent(working, c.intent, background.intent)
	return foreground, nil
}

// printWorkingEquivalent 比较混合编码及组输出政策，不以分配地址区分等价源页
// 入参: a, b 两个混合空间
// 返回: bool 是否可直接共享混合编码和输出意图
func printWorkingEquivalent(a, b *printWorkingSpace) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || a.intent != b.intent || a.outputIntent != b.outputIntent || a.channels != b.channels {
		return false
	}
	if a.profile == nil || b.profile == nil {
		return a.profile == nil && b.profile == nil && a.space == b.space
	}
	return a.hash == b.hash
}

// printWorkingIntent 解析给定混合空间的有效组输出意图，缺省回退至相对色度
// 入参: working 所选混合编码
// 返回: RenderingIntent 混合profile意图或页面缺省相对色度
func printWorkingIntent(working *printWorkingSpace) RenderingIntent {
	intent := IntentRelativeColorimetric
	if working != nil && working.intent != IntentDefault {
		intent = working.intent
	}
	if working != nil && working.outputIntent != IntentDefault {
		intent = working.outputIntent
	}
	return intent
}

// printMixIntent 为实际混合后的颜色选择组输出意图，不对每个源先作目标往返
// 入参: working 所选混合编码, intents 参与混合的对象目标意图
// 返回: RenderingIntent 混合profile意图或页面缺省相对色度
func (r *sceneRenderer) printMixIntent(working *printWorkingSpace, intents ...RenderingIntent) RenderingIntent {
	intent := printWorkingIntent(working)
	for _, source := range intents {
		if source != IntentDefault && source != intent {
			r.options.device.printDiagnostic("PrintColor", "mixed colors use the blend group output intent; per-object destination recommendations apply only before blending")
			break
		}
	}
	return intent
}

// native 校验源profile是否匹配当前设备条件与原生ICC清单
// 入参: profile 颜色profile
// 返回: bool 是否允许保留原生分量, error 身份比较预算或取消错误
func (c *printColorRuntime) native(profile *iccProfile) (bool, error) {
	if result, present := c.nativeMatch[profile]; present {
		return result, nil
	}
	if profile != nil {
		work := uint64(len(profile.data))
		if c.options != nil {
			for _, data := range c.options.NativeProfiles {
				work += uint64(len(data))
			}
		}
		if err := c.renderer.charge(work); err != nil {
			return false, err
		}
	}
	result := c.matchNative(profile)
	c.nativeMatch[profile] = result
	return result, nil
}

// matchNative 检查一次完整profile身份，结果由源页运行时缓存
// 入参: profile 源ICC
// 返回: bool 是否适用于当前设备条件
func (c *printColorRuntime) matchNative(profile *iccProfile) bool {
	if profile == nil || profile.class == "nmcl" || profile.class == "link" || profile.class == "abst" {
		return false
	}
	if c.plan.Management != PrintColorManagementNone && (c.nativeProfile == nil || !bytes.Equal(profile.data, c.nativeProfile.data)) {
		return false
	}
	if c.options == nil || c.options.Conditions == "" || c.device == nil || len(c.options.Colorants) != profile.channels || profile.channels != c.device.channels || profile.space != c.device.profile.space {
		return false
	}
	for _, data := range c.options.NativeProfiles {
		if bytes.Equal(data, profile.data) {
			return true
		}
	}
	return false
}

// sourceIntent 按profile属性、票据及方言缺省决定当前源连接意图
// 入参: profile 源ICC, raster 是否为图像
// 返回: RenderingIntent 有效意图
func (c *printColorRuntime) sourceIntent(profile *iccProfile, raster bool) RenderingIntent {
	if c.options != nil && c.options.Override && c.target.sourceIntent != IntentDefault {
		return c.target.sourceIntent
	}
	if profile != nil {
		return RenderingIntent(profile.intent + 1)
	}
	if c.plan.Intent != IntentDefault {
		return c.plan.Intent
	}
	if c.format == FormatOpenXPS && raster {
		return IntentPerceptual
	}
	return IntentRelativeColorimetric
}

// destinationIntent 按页面意图及对象类别决定目标渲染意图
// 入参: profile 源ICC, raster 是否为图像
// 返回: RenderingIntent 目标意图
func (c *printColorRuntime) destinationIntent(profile *iccProfile, raster bool) RenderingIntent {
	if c.options != nil && c.options.Override && c.target.explicitIntent != IntentDefault {
		return c.target.explicitIntent
	}
	if c.plan.Intent != IntentDefault {
		return c.plan.Intent
	}
	if c.format == FormatOpenXPS && raster && (profile == nil || profile.space == "RGB " || profile.space == "CMYK" || profile.space == "GRAY") {
		return IntentPerceptual
	}
	return IntentRelativeColorimetric
}

// color 将源分量连接到PCS，已验证的output-ready颜色直接保留设备编码
// 入参: profile 源ICC，nil表示内建编码, value 原始分量, alpha 透明度, space 内建源编码, raster 是否为图像
// 返回: printNativeColor 非预乘颜色, error 变换或预算错误
func (c *printColorRuntime) color(profile *iccProfile, value [8]float64, alpha float64, space ColorSpace, raster bool) (printNativeColor, error) {
	result := printNativeColor{value: value, alpha: alpha, blend: c.working, intent: c.destinationIntent(profile, raster)}
	native, err := c.native(profile)
	if err != nil {
		return printNativeColor{}, err
	}
	if native {
		result.space = c.device
		return result, nil
	}
	if alpha == 0 {
		return printNativeColor{}, nil
	}
	if c.plan.Management == PrintColorManagementNone {
		verified, err := c.native(c.device.profile)
		if err != nil {
			return printNativeColor{}, err
		}
		if profile == nil && space == ColorSRGB && c.device.channels == 3 && verified {
			result.space = c.device
			return result, nil
		}
		return printNativeColor{}, fmt.Errorf("%w: unverified already-managed print color", ErrUnsupported)
	}
	if c.target.sourceIntent != IntentDefault && c.target.sourceIntent != c.sourceIntent(profile, raster) || c.target.explicitIntent != IntentDefault && c.target.explicitIntent != result.intent {
		return printNativeColor{}, fmt.Errorf("%w: explicit print intent requires color override", ErrUnsupported)
	}
	var xyz [3]float64
	if profile != nil {
		transform, e := c.sourceTransform(profile, raster)
		if e != nil {
			return printNativeColor{}, e
		}
		if e := c.renderer.charge(printICCSourceWork(transform)); e != nil {
			return printNativeColor{}, e
		}
		xyz, err = transform.toXYZ(value[:transform.inputChannels()])
	} else {
		builtin := printWorkingSpace{space: space, channels: 3}
		xyz, err = builtin.xyz(value)
	}
	if err != nil {
		return printNativeColor{}, err
	}
	result.value = [8]float64{xyz[0], xyz[1], xyz[2]}
	return result, nil
}

// sourceTransform 按源页实际意图复用准备结果，不在逐像素阶段重新解析profile
// 入参: profile 已解析源ICC, raster 是否为图像
// 返回: *iccTransform 源连接, error 表、预算或取消错误
func (c *printColorRuntime) sourceTransform(profile *iccProfile, raster bool) (*iccTransform, error) {
	intent := c.sourceIntent(profile, raster)
	values := c.transforms[profile]
	if transform := values[intent-1]; transform != nil {
		return transform, nil
	}
	if err := c.renderer.charge(uint64(len(profile.data))); err != nil {
		return nil, err
	}
	transform, err := prepareICCTransform(profile, uint32(intent-1))
	if err != nil {
		return nil, err
	}
	values[intent-1] = transform
	c.transforms[profile] = values
	return transform, nil
}

// printPixel 将完整高精度颜色编码为设备分量，只在最终写入时量化
// 入参: x, y 输出坐标, value 合成结果, r 场景渲染器
// 返回: error 转换、预算或数值错误
func (s *deviceRenderState) printPixel(x, y int, value printNativeColor, r *sceneRenderer) error {
	if !geometryFinite(value.alpha) || value.alpha < 0 || value.alpha > 1 {
		return fmt.Errorf("%w: print output alpha", ErrLimit)
	}
	var channels [8]float64
	alpha := uint16(math.Floor(colorClamp(value.alpha)*65535 + .5))
	if alpha != 0 {
		if value.space != nil && value.space.profile != nil && value.space.hash == s.printProfileHash {
			channels = value.value
		} else {
			xyz, err := value.space.xyz(value.value)
			if err != nil {
				return err
			}
			intent := value.intent
			if intent == IntentDefault {
				intent = IntentRelativeColorimetric
			}
			target := s.printTarget[intent-1]
			if target == nil {
				if err := r.charge(uint64(len(s.target.profile.data))); err != nil {
					return err
				}
				target, err = prepareICCTarget(s.target.profile, uint32(intent-1), r.options.context)
				if err != nil {
					return err
				}
				s.printTarget[intent-1] = target
			}
			if err := r.charge(iccTargetWork(target)); err != nil {
				return err
			}
			channels, err = target.fromXYZ(xyz)
			if err != nil {
				return err
			}
		}
	}
	if err := r.charge(uint64(8 + s.result.Channels*4)); err != nil {
		return err
	}
	at := (y-s.result.Rect.Min.Y)*s.result.Stride + (x-s.result.Rect.Min.X)*(s.result.Channels+1)
	for i := range s.result.Channels {
		if !geometryFinite(channels[i]) {
			return fmt.Errorf("%w: print output component", ErrLimit)
		}
		s.result.Pix[at+i] = uint16(math.Floor(colorClamp(channels[i])*65535 + 0.5))
	}
	s.result.Pix[at+s.result.Channels] = alpha
	return nil
}

// newPrintColorRuntime 验证页面颜色计划和显式设备目标，准备所有实际需要的连接
// 入参: plan 页面计划, options 设备条件, colors 共用ICC缓存, r 场景渲染器
// 返回: *printColorRuntime 页面独立政策, error 目标冲突、资源或能力错误
func newPrintColorRuntime(plan *PrintColorPlan, options *PrintColorOptions, colors *sceneColorCache, r *sceneRenderer) (*printColorRuntime, error) {
	if plan == nil {
		plan = &PrintColorPlan{}
	}
	if r.options.device == nil {
		return nil, fmt.Errorf("%w: print color requires explicit device output", ErrUnsupported)
	}
	c := &printColorRuntime{plan: plan, options: options, colors: colors, target: r.options.device, format: r.options.format, renderer: r, transforms: make(map[*iccProfile][4]*iccTransform), nativeMatch: make(map[*iccProfile]bool)}
	if options != nil && options.Override {
		c.target.printDiagnostic("PrintColor", "explicit device color override enabled")
	}
	for _, test := range []struct {
		value   string
		allowed []string
	}{
		{plan.Management, []string{"", PrintColorManagementNone, PrintColorManagementDevice, PrintColorManagementDriver, PrintColorManagementSystem}},
		{plan.DeviceUsage, []string{"", PrintColorDeviceUsageMatchToDefault, PrintColorDeviceUsageOverrideDeviceDefault}},
		{plan.SourceSpace, []string{"", PrintColorSourceSpaceNone, PrintColorSourceSpaceRGB, PrintColorSourceSpaceCMYK}},
		{plan.DestinationMode, []string{"", PrintColorDestinationModeApplication, PrintColorDestinationModeDriverConfiguration}},
		{plan.BlendSpace, []string{"", PrintColorBlendSpaceSRGB, PrintColorBlendSpaceScRGB, PrintColorBlendSpaceICCProfile}},
	} {
		valid := false
		for _, name := range test.allowed {
			if test.value == name {
				valid = true
			}
		}
		if !valid {
			return nil, fmt.Errorf("%w: print color plan option", ErrInvalid)
		}
	}
	if plan.Intent > IntentAbsoluteColorimetric {
		return nil, fmt.Errorf("%w: print color plan intent", ErrInvalid)
	}
	if (plan.Source.URI != "" || len(plan.Source.Data) != 0) && plan.SourceSpace != PrintColorSourceSpaceRGB && plan.SourceSpace != PrintColorSourceSpaceCMYK {
		return nil, fmt.Errorf("%w: print source profile selection", ErrInvalid)
	}
	if (plan.Destination.URI != "" || len(plan.Destination.Data) != 0) && plan.DestinationMode != PrintColorDestinationModeApplication {
		return nil, fmt.Errorf("%w: print destination profile selection", ErrInvalid)
	}
	if options != nil {
		if len(options.NativeProfiles) > colors.maxProfiles || len(options.Colorants) > 8 {
			return nil, fmt.Errorf("%w: print native profile count", ErrLimit)
		}
		remaining := r.options.profileBytes
		for _, data := range options.NativeProfiles {
			if int64(len(data)) > remaining {
				return nil, fmt.Errorf("%w: print native profile bytes", ErrLimit)
			}
			remaining -= int64(len(data))
		}
		seen := make(map[string]bool)
		for _, name := range options.Colorants {
			if name == "" || seen[name] {
				return nil, fmt.Errorf("%w: print device colorant identity", ErrInvalid)
			}
			seen[name] = true
		}
		if len(options.NativeProfiles) != 0 && (options.Conditions == "" || len(options.Colorants) != c.target.target.profile.channels) {
			return nil, fmt.Errorf("%w: print native device conditions", ErrInvalid)
		}
	}
	destination, err := c.profileData(plan.Destination)
	if err != nil {
		return nil, err
	}
	if plan.DestinationMode == PrintColorDestinationModeApplication && destination == nil {
		return nil, fmt.Errorf("%w: application print destination", ErrUnsupported)
	}
	if destination != nil && !bytes.Equal(destination.data, c.target.target.profile.data) && (options == nil || !options.Override) {
		return nil, fmt.Errorf("%w: explicit and ticket print destination conflict", ErrUnsupported)
	}
	if plan.DestinationMode == PrintColorDestinationModeDriverConfiguration && (options == nil || !bytes.Equal(options.Profile, c.target.target.profile.data)) {
		return nil, fmt.Errorf("%w: unresolved driver color profile", ErrUnsupported)
	}
	c.nativeProfile, err = c.profileData(plan.Device)
	if err != nil {
		return nil, err
	}
	if plan.DeviceUsage == PrintColorDeviceUsageOverrideDeviceDefault && c.nativeProfile != nil && !bytes.Equal(c.nativeProfile.data, c.target.target.profile.data) && (options == nil || !options.Override) {
		return nil, fmt.Errorf("%w: override device profile target conflict", ErrUnsupported)
	}
	c.source, err = c.profileData(plan.Source)
	if err != nil {
		return nil, err
	}
	if c.source == nil && (plan.SourceSpace == PrintColorSourceSpaceRGB || plan.SourceSpace == PrintColorSourceSpaceCMYK) {
		return nil, fmt.Errorf("%w: missing print source profile", ErrUnsupported)
	}
	if c.nativeProfile == nil && plan.DeviceUsage == PrintColorDeviceUsageOverrideDeviceDefault {
		return nil, fmt.Errorf("%w: missing device override profile", ErrUnsupported)
	}
	if c.source != nil && (plan.SourceSpace == PrintColorSourceSpaceRGB && c.source.space != "RGB " || plan.SourceSpace == PrintColorSourceSpaceCMYK && c.source.space != "CMYK") {
		return nil, fmt.Errorf("%w: print source profile model", ErrInvalid)
	}
	c.device, err = newPrintWorkingSpace(c.target.target.profile, ColorUnknown, IntentRelativeColorimetric, r)
	if err != nil {
		return nil, err
	}
	c.working = &printWorkingSpace{space: ColorSRGB, channels: 3, intent: c.destinationIntent(nil, false)}
	if plan.BlendSpace == PrintColorBlendSpaceScRGB {
		c.working.space = ColorScRGB
	}
	if plan.BlendSpace == PrintColorBlendSpaceICCProfile {
		p, e := c.profileData(plan.Blend)
		if e != nil {
			return nil, e
		}
		valid := p != nil && p.class == "prtr"
		for _, name := range []string{"A2B0", "A2B1", "A2B2", "B2A0", "B2A1", "B2A2"} {
			if p == nil || p.tag(name) == nil {
				valid = false
			}
		}
		if valid {
			c.working, err = newPrintWorkingSpace(p, ColorUnknown, RenderingIntent(p.intent+1), r)
			if err != nil {
				return nil, err
			}
			if plan.Intent != IntentDefault || options != nil && options.Override && c.target.explicitIntent != IntentDefault {
				c.working.outputIntent = c.destinationIntent(nil, false)
			}
		} else {
			c.target.printDiagnostic("PageBlendColorSpace", "ICC blend profile ignored: output class and six transform tables required")
		}
	}
	return c, nil
}

// printICCSourceWork 计算源管线每次求值的保守工作权重，包含全部CLUT角点
// 入参: transform 已准备源连接
// 返回: uint64 本次求值工作量
func printICCSourceWork(transform *iccTransform) uint64 {
	work := uint64(64 + transform.inputChannels()*8)
	if transform.pipeline != nil {
		for _, stage := range transform.pipeline.stages {
			switch stage.kind {
			case iccStageCLUT:
				work += uint64((1 << len(stage.grid)) * stage.outputs * 2)
			case iccStageMatrix:
				work += 24
			case iccStageCurves:
				work += uint64(len(stage.curves) * 4)
			}
		}
	}
	return work
}
