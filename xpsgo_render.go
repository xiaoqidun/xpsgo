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
	"errors"
	"fmt"
	"image"
	"image/color"
	"math"
	"strings"
	"sync"
)

const (
	// IntentDefault 表示采用当前入口默认的ICC渲染意图
	IntentDefault RenderingIntent = iota
	// IntentPerceptual 表示感知渲染意图
	IntentPerceptual
	// IntentRelativeColorimetric 表示相对色度渲染意图
	IntentRelativeColorimetric
	// IntentSaturation 表示饱和度渲染意图
	IntentSaturation
	// IntentAbsoluteColorimetric 表示绝对色度渲染意图
	IntentAbsoluteColorimetric
)

// renderSurfacePoolMax 定义标准渲染表面复用池的单缓冲区像素上限
const renderSurfacePoolMax = 32 * 8 * 32 * 8

// renderSurfacePool 复用隔离合成与图块光栅化所需的像素缓冲
var renderSurfacePool sync.Pool

// RenderLimits 规定单次绘制的资源上限，零值字段采用DefaultRenderLimits默认值，负值返回ErrInvalid
// MaxPixels累计输出与活动隔离表面像素，MaxImagePixels按RGBA64容量计入原生图像存储，MaxWork累计节点、边与像素操作
// 设备输出另将目标ICC及转换权重计入预算，输出分量缓冲另受DeviceColorTarget.MaxBytes约束
type RenderLimits struct {
	MaxPixels       int
	MaxElements     int
	MaxEdges        int
	MaxWork         uint64
	MaxGlyphs       int
	MaxFonts        int
	MaxFontBytes    int64
	MaxImages       int
	MaxImagePixels  uint64
	MaxImageBytes   int64
	MaxProfiles     int
	MaxProfileBytes int64
}

// RenderOptions 设置页面绘制参数，零值字段采用DefaultRenderOptions默认值，不修改页面内容
// DPI默认96（先应用Transform再按DPI缩放），Region为nil取变换后整像素范围，Background为nil默认白色（color.Transparent输出透明底）
// ColorSpace预览默认ColorSRGB、设备默认ColorScRGB，Samples可选1/2/4/8（默认8），Tolerance默认0.025像素，Workers零值自动按核数选择
type RenderOptions struct {
	DPI        float64
	Transform  *Matrix
	Region     *image.Rectangle
	Background color.Color
	ColorSpace ColorSpace
	Samples    int
	Tolerance  float64
	Workers    int
	Limits     RenderLimits
}

// RenderingIntent 指定ICC转换意图，零值表示使用当前入口约定的缺省策略
type RenderingIntent uint8

// DeviceColorTarget 指定设备输出目标ICC及源渲染意图，Profile调用期间不得修改且读取量计入MaxProfileBytes
// Intent默认相对色度作用于最终合成颜色，SourceIntent缺省沿用源策略，打印设备入口另按PrintColorPlan与Override仲裁
// MaxBytes限制输出分量缓冲区大小，零值默认64MiB
type DeviceColorTarget struct {
	Profile      []byte
	Intent       RenderingIntent
	SourceIntent RenderingIntent
	MaxBytes     int64
}

// DeviceImage 保存目标ICC编码的非预乘十六位分量图像，不实现image.Image
// 每像素依次存储Channels个设备分量与一个线性alpha，Stride以uint16计，Rect保留设备坐标，全透明像素各项为零
// Space为四字节ICC颜色空间标识，Profile为目标ICC独立副本，Diagnostics记录打印颜色执行诊断
type DeviceImage struct {
	Pix         []uint16
	Stride      int
	Rect        image.Rectangle
	Channels    int
	Space       string
	Profile     []byte
	Diagnostics []Diagnostic
}

// deviceRenderState 保存本次绘制的目标转换及输出，不跨调用共享可变状态
type deviceRenderState struct {
	target           *iccTargetTransform
	sourceIntent     RenderingIntent
	explicitIntent   RenderingIntent
	maxBytes         int64
	prepareWork      uint64
	pixelWork        uint64
	result           *DeviceImage
	printTarget      [4]*iccTargetTransform
	diagnostics      []Diagnostic
	printProfileHash [32]byte
	diagMu           sync.Mutex
}

// renderSurface 保存统一工作空间中的预乘像素，用于图块及隔离合成，不承担页面遍历
type renderSurface struct {
	bounds   image.Rectangle
	space    renderColorSpace
	pixels   []renderColor
	reserved int
}

// sceneColorCache 复用单次绘制的配置文件和渲染意图转换，不跨阅读器共享状态
type sceneColorCache struct {
	pkg             *packageReader
	profiles        map[string]*iccProfile
	profileErrors   map[string]error
	transforms      map[string][4]*iccTransform
	transformErrors map[string][4]error
	bytes           int64
	maxProfiles     int
	sourceIntent    RenderingIntent
}

// String 返回ICC渲染意图的名称
// 返回: string 渲染意图名称
func (i RenderingIntent) String() string {
	switch i {
	case IntentDefault:
		return "Default"
	case IntentPerceptual:
		return "Perceptual"
	case IntentRelativeColorimetric:
		return "RelativeColorimetric"
	case IntentSaturation:
		return "Saturation"
	case IntentAbsoluteColorimetric:
		return "AbsoluteColorimetric"
	default:
		return fmt.Sprintf("RenderingIntent(%d)", i)
	}
}

// DefaultRenderLimits 返回默认的单次绘制资源上限
// 返回: RenderLimits 资源上限
func DefaultRenderLimits() RenderLimits {
	o := defaultSceneRenderOptions()
	return RenderLimits{MaxPixels: o.pixels, MaxElements: o.elements, MaxEdges: o.edges, MaxWork: o.work, MaxGlyphs: o.glyphs, MaxFonts: o.fonts, MaxFontBytes: o.fontBytes, MaxImages: o.images, MaxImagePixels: o.imagePixels, MaxImageBytes: o.imageBytes, MaxProfiles: o.profiles, MaxProfileBytes: o.profileBytes}
}

// DefaultRenderOptions 返回九十六DPI、白色背景及八倍线性采样的默认绘制参数
// 返回: RenderOptions 绘制参数
func DefaultRenderOptions() RenderOptions {
	o := defaultSceneRenderOptions()
	return RenderOptions{DPI: 96, Background: color.White, ColorSpace: ColorSRGB, Samples: o.samples, Tolerance: o.tolerance, Limits: DefaultRenderLimits()}
}

// Render 绘制指定页面，支持并发调用；关闭阅读器会等待绘制结束
// 错误或取消时不返回部分图像，Context在绘制步骤检查取消且不承诺中断底层ReaderAt正在进行的读取
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的页面序号, options 绘制参数，nil表示默认配置
// 返回: *image.NRGBA 独立页面图像，Bounds保留设备坐标, error 读取、参数、绘制或取消错误
func (r *Reader) Render(ctx context.Context, pageIndex int, options *RenderOptions) (*image.NRGBA, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.renderSelectedPage(ctx, options, func(ctx context.Context) (*Page, error) {
		return r.readPageHeader(pageIndex, nil, ctx)
	}, nil)
}

// RenderPart 按包内部件URI绘制固定页面（含主索引外辅助页），并发安全并沿用Render的参数与预算
// 错误或取消时不返回部分图像，Context在绘制步骤检查取消且不中断底层ReaderAt读取
// 入参: ctx 取消Context，nil采用Background, part 页面部件的包根URI，不含查询或片段, options 绘制参数，nil采用默认值
// 返回: *image.NRGBA 独立页面图像，Bounds保留设备坐标, error 状态、URI、读取、绘制或取消错误
func (r *Reader) RenderPart(ctx context.Context, part string, options *RenderOptions) (*image.NRGBA, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.renderSelectedPage(ctx, options, func(ctx context.Context) (*Page, error) {
		return r.readPagePartHeader(part, nil, ctx)
	}, nil)
}

// renderSelectedPage 在分配像素前验证页面头和输出范围，索引与部件入口共用绘制流程
// 入参: ctx 取消Context, options 公开绘制参数, load 页面头读取器, device 可选设备输出状态
// 返回: *image.NRGBA 独立图像，失败为nil, error 参数、读取、预算、绘制或取消错误
func (r *Reader) renderSelectedPage(ctx context.Context, options *RenderOptions, load func(context.Context) (*Page, error), device *deviceRenderState) (*image.NRGBA, error) {
	if r.closed {
		return nil, ErrClosed
	}
	configuration := RenderOptions{}
	if options != nil {
		configuration = *options
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	settings, transform, err := configuration.settings(ctx)
	if err != nil {
		return nil, err
	}
	if device != nil {
		if err := device.apply(&settings); err != nil {
			return nil, err
		}
	}
	page, err := load(settings.context)
	if err != nil {
		return nil, err
	}
	var bounds image.Rectangle
	if configuration.Region != nil {
		bounds = *configuration.Region
	} else {
		bounds, err = renderPageBounds(page, transform, settings.samples)
		if err != nil {
			return nil, err
		}
	}
	if _, err := validateSceneOutput(bounds, transform, settings); err != nil {
		return nil, err
	}
	page, err = r.readPageSceneContent(page, false, nil, settings.context)
	if err != nil {
		return nil, err
	}
	result, err := r.renderLoadedPage(page, transform, bounds, settings)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// settings 规范化公开绘制参数并建立页面到设备的变换，不分配像素表面
// 入参: ctx 取消Context
// 返回: sceneRenderOptions 内部绘制参数, Matrix 有效变换, error 参数或数值范围错误
func (o RenderOptions) settings(ctx context.Context) (sceneRenderOptions, Matrix, error) {
	settings := defaultSceneRenderOptions()
	settings.context = normalizeContext(ctx)
	dpi := o.DPI
	if dpi == 0 {
		dpi = 96
	}
	if !geometryFinite(dpi, o.Tolerance) || dpi < 0 || o.Tolerance < 0 || o.Workers < 0 || o.Samples != 0 && o.Samples != 1 && o.Samples != 2 && o.Samples != 4 && o.Samples != 8 {
		return settings, Matrix{}, fmt.Errorf("%w: render resolution or sampling", ErrInvalid)
	}
	settings.workers = o.Workers
	if o.Samples != 0 {
		settings.samples = o.Samples
	}
	if o.Tolerance != 0 {
		settings.tolerance = o.Tolerance
	}
	switch o.ColorSpace {
	case ColorUnknown, ColorSRGB:
	case ColorScRGB:
		settings.space = renderScRGB
	default:
		return settings, Matrix{}, fmt.Errorf("%w: render blend color space", ErrInvalid)
	}
	if err := o.Limits.apply(&settings); err != nil {
		return settings, Matrix{}, err
	}
	bg := o.Background
	if bg == nil {
		bg = color.White
	}
	pixel := color.NRGBA64Model.Convert(bg).(color.NRGBA64)
	if pixel.A != 0 {
		background := Color{Space: ColorSRGB, Alpha: float64(pixel.A) / 65535, Components: []float64{float64(pixel.R) / 65535, float64(pixel.G) / 65535, float64(pixel.B) / 65535}}
		value, err := renderColorFromColor(background, settings.space)
		if err != nil {
			return settings, Matrix{}, err
		}
		settings.background = value
	}
	transform := Matrix{A: dpi / 96, D: dpi / 96}
	if transform.A == 0 {
		return settings, Matrix{}, fmt.Errorf("%w: render resolution precision", ErrLimit)
	}
	if o.Transform != nil {
		if !geometryFillMatrixFinite(*o.Transform) {
			return settings, Matrix{}, fmt.Errorf("%w: render transform", ErrInvalid)
		}
		transform = transform.Mul(*o.Transform)
	}
	if !geometryFillMatrixFinite(transform) {
		return settings, Matrix{}, fmt.Errorf("%w: render transform range", ErrLimit)
	}
	return settings, transform, nil
}

// apply 将非零公开资源上限应用到独立绘制配置，负值不得替代默认值
// 入参: options 内部绘制配置
// 返回: error 无效资源上限错误
func (limits RenderLimits) apply(options *sceneRenderOptions) error {
	for _, field := range []struct {
		value int
		to    *int
	}{{limits.MaxPixels, &options.pixels}, {limits.MaxElements, &options.elements}, {limits.MaxEdges, &options.edges}, {limits.MaxGlyphs, &options.glyphs}, {limits.MaxFonts, &options.fonts}, {limits.MaxImages, &options.images}, {limits.MaxProfiles, &options.profiles}} {
		if field.value < 0 {
			return fmt.Errorf("%w: negative render resource limit", ErrInvalid)
		}
		if field.value != 0 {
			*field.to = field.value
		}
	}
	if limits.MaxEdges > rasterMaxEdges {
		return fmt.Errorf("%w: render max edges", ErrLimit)
	}
	for _, field := range []struct {
		value int64
		to    *int64
	}{{limits.MaxFontBytes, &options.fontBytes}, {limits.MaxImageBytes, &options.imageBytes}, {limits.MaxProfileBytes, &options.profileBytes}} {
		if field.value < 0 {
			return fmt.Errorf("%w: negative render byte limit", ErrInvalid)
		}
		if field.value != 0 {
			*field.to = field.value
		}
	}
	if limits.MaxWork != 0 {
		options.work = limits.MaxWork
	}
	if limits.MaxImagePixels != 0 {
		options.imagePixels = limits.MaxImagePixels
	}
	return nil
}

// renderPageBounds 取页面四角经有效变换后的最小整像素范围，转换为整数前检查设备坐标上限
// 入参: page 页面尺寸, transform 有效变换, samples 线性采样数
// 返回: image.Rectangle 保留设备原点的整像素范围, error 数值或坐标容量错误
func renderPageBounds(page *Page, transform Matrix, samples int) (image.Rectangle, error) {
	minimum, maximum := Point{math.Inf(1), math.Inf(1)}, Point{math.Inf(-1), math.Inf(-1)}
	for _, corner := range []Point{{}, {page.Width, 0}, {page.Width, page.Height}, {0, page.Height}} {
		point := transform.Transform(corner)
		if !geometryFinite(point.X, point.Y) {
			return image.Rectangle{}, fmt.Errorf("%w: render page bounds", ErrLimit)
		}
		minimum.X, minimum.Y = min(minimum.X, point.X), min(minimum.Y, point.Y)
		maximum.X, maximum.Y = max(maximum.X, point.X), max(maximum.Y, point.Y)
	}
	x0, y0, x1, y1 := math.Floor(minimum.X), math.Floor(minimum.Y), math.Ceil(maximum.X), math.Ceil(maximum.Y)
	limit := float64((1 << 30) / samples)
	if x0 < -limit || y0 < -limit || x1 > limit || y1 > limit {
		return image.Rectangle{}, fmt.Errorf("%w: render device bounds", ErrLimit)
	}
	return image.Rect(int(x0), int(y0), int(x1), int(y1)), nil
}

// printDiagnostic 在单次设备输出中按元素及内容去重有限种颜色政策诊断
// 入参: element 标准元素或执行阶段, message 固定政策说明
func (s *deviceRenderState) printDiagnostic(element, message string) {
	s.diagMu.Lock()
	defer s.diagMu.Unlock()
	for _, value := range s.diagnostics {
		if value.Element == element && value.Message == message {
			return
		}
	}
	s.diagnostics = append(s.diagnostics, Diagnostic{Element: element, Message: message})
}

// RenderDevice 按显式目标ICC绘制页面，不经过八位sRGB预览或提交打印作业
// ColorSpace未指定时采用scRGB合成以保留扩展色域，显式sRGB仍采用现有sRGB合成策略
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的页面序号, device 必需的目标配置, options 绘制参数
// 返回: *DeviceImage 独立设备分量，失败为nil, error 参数、资源、转换或取消错误
func (r *Reader) RenderDevice(ctx context.Context, pageIndex int, device *DeviceColorTarget, options *RenderOptions) (*DeviceImage, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	configuration := deviceRenderConfiguration(options)
	state, err := newDeviceRenderStateMode(ctx, device, configuration, false)
	if err != nil {
		return nil, err
	}
	_, err = r.renderSelectedPage(ctx, &configuration, func(ctx context.Context) (*Page, error) {
		return r.readPageHeader(pageIndex, nil, ctx)
	}, state)
	return state.output(err)
}

// RenderPartDevice 按包内部件URI绘制辅助页面，与RenderDevice共用目标编码及预算
// 入参: ctx 取消Context，nil采用Background, part 页面包根URI, device 必需的目标配置, options 绘制参数
// 返回: *DeviceImage 独立设备分量，失败为nil, error 状态、资源、转换或取消错误
func (r *Reader) RenderPartDevice(ctx context.Context, part string, device *DeviceColorTarget, options *RenderOptions) (*DeviceImage, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	configuration := deviceRenderConfiguration(options)
	state, err := newDeviceRenderStateMode(ctx, device, configuration, false)
	if err != nil {
		return nil, err
	}
	_, err = r.renderSelectedPage(ctx, &configuration, func(ctx context.Context) (*Page, error) {
		return r.readPagePartHeader(part, nil, ctx)
	}, state)
	return state.output(err)
}

// deviceRenderConfiguration 复制绘制配置并为设备输出选择缺省线性合成空间
// 入参: options 可选绘制参数
// 返回: RenderOptions 本次调用独占的参数
func deviceRenderConfiguration(options *RenderOptions) RenderOptions {
	var result RenderOptions
	if options != nil {
		result = *options
	}
	if result.ColorSpace == ColorUnknown {
		result.ColorSpace = ColorScRGB
	}
	return result
}

// newDeviceRenderStateMode 在打印原生输出时延后准备未使用的目标转换方向
// 入参: ctx 取消Context, options 目标配置, render 绘制预算, lazy 是否按实际使用准备目标表
// 返回: *deviceRenderState 私有状态, error 配置、profile或预算错误
func newDeviceRenderStateMode(ctx context.Context, options *DeviceColorTarget, render RenderOptions, lazy bool) (*deviceRenderState, error) {
	settings, _, err := render.settings(ctx)
	if err != nil {
		return nil, err
	}
	if err := checkContext(settings.context); err != nil {
		return nil, err
	}
	if options == nil || len(options.Profile) == 0 || options.Intent > IntentAbsoluteColorimetric || options.SourceIntent > IntentAbsoluteColorimetric || options.MaxBytes < 0 {
		return nil, fmt.Errorf("%w: device color target", ErrInvalid)
	}
	if settings.profiles < 1 || int64(len(options.Profile)) > settings.profileBytes {
		return nil, fmt.Errorf("%w: device target profile budget", ErrLimit)
	}
	if uint64(len(options.Profile)) > settings.work {
		return nil, fmt.Errorf("%w: device target preparation work", ErrLimit)
	}
	data := append([]byte(nil), options.Profile...)
	profile, err := parseICCProfile(data)
	if err != nil {
		return nil, err
	}
	if len(profile.data) != len(data) {
		return nil, fmt.Errorf("%w: trailing target ICC data", ErrInvalid)
	}
	intent := uint32(1)
	if options.Intent != IntentDefault {
		intent = uint32(options.Intent - 1)
	}
	target, err := newICCTarget(profile, intent)
	if err != nil {
		return nil, err
	}
	if !lazy {
		target, err = prepareICCTargetDirection(target, settings.context)
		if err != nil {
			return nil, err
		}
	}
	limit := options.MaxBytes
	if limit == 0 {
		limit = 64 << 20
	}
	work := uint64(8 + profile.channels*4)
	if !lazy {
		work = iccTargetWork(target)
	}
	return &deviceRenderState{target: target, sourceIntent: options.SourceIntent, explicitIntent: options.Intent, maxBytes: limit, prepareWork: uint64(len(data)), pixelWork: work, printProfileHash: sha256.Sum256(data)}, nil
}

// iccTargetWork 预计算每像素转换权重，纳入网格角点、曲线和逆采样表查找上界
// 入参: target 已准备的目标转换
// 返回: uint64 有界工作量权重
func iccTargetWork(target *iccTargetTransform) uint64 {
	work := uint64(32 + target.profile.channels*8)
	if target.pipeline != nil {
		for _, stage := range target.pipeline.stages {
			switch stage.kind {
			case iccStageCLUT:
				work += uint64((1 << len(stage.grid)) * stage.outputs * 2)
			case iccStageMatrix:
				work += 24
			case iccStageCurves:
				work += uint64(len(stage.curves) * 4)
			}
		}
	} else {
		for _, prepared := range target.inverse[:target.profile.channels] {
			curve := prepared.curve
			if curve.kind == iccCurveSampled {
				for count := len(curve.values) / curve.precision; count > 0; count /= 2 {
					work += 4
				}
			}
		}
	}
	return work
}

// apply 将目标ICC占用计入共享profile预算，源资源仍使用同一绘制缓存及剩余额度
// 入参: settings 本次绘制设置
// 返回: error profile预算或取消错误
func (s *deviceRenderState) apply(settings *sceneRenderOptions) error {
	if err := checkContext(settings.context); err != nil {
		return err
	}
	if settings.profiles < 1 || int64(len(s.target.profile.data)) > settings.profileBytes {
		return fmt.Errorf("%w: device target profile budget", ErrLimit)
	}
	settings.profiles--
	settings.profileBytes -= int64(len(s.target.profile.data))
	if s.prepareWork > settings.work {
		return fmt.Errorf("%w: device target preparation work", ErrLimit)
	}
	settings.work -= s.prepareWork
	settings.device = s
	return nil
}

// allocate 检查设备缓冲区字节数及整数容量后建立独立输出
// 入参: bounds 已通过场景输出检查的设备范围
// 返回: error 输出字节预算错误
func (s *deviceRenderState) allocate(bounds image.Rectangle) error {
	if err := s.validateBounds(bounds); err != nil {
		return err
	}
	channels := s.target.profile.channels
	count := uint64(bounds.Dx()) * uint64(bounds.Dy())
	stride := uint64(bounds.Dx()) * uint64(channels+1)
	words := count * uint64(channels+1)
	s.result = &DeviceImage{Pix: make([]uint16, int(words)), Stride: int(stride), Rect: bounds, Channels: channels, Space: s.target.profile.space, Profile: s.target.profile.data}
	return nil
}

// validateBounds 在场景资源加载前检查目标分量容量，不分配缓冲区
// 入参: bounds 已通过尺寸及像素数检查的设备范围
// 返回: error 输出字节或整数容量错误
func (s *deviceRenderState) validateBounds(bounds image.Rectangle) error {
	channels := uint64(s.target.profile.channels + 1)
	count := uint64(bounds.Dx()) * uint64(bounds.Dy())
	if count > uint64(s.maxBytes)/2/channels || count > uint64(^uint(0)>>1)/2/channels || uint64(bounds.Dx()) > uint64(^uint(0)>>1)/channels {
		return fmt.Errorf("%w: device output byte budget", ErrLimit)
	}
	return nil
}

// pixel 将降采样后的高精度合成值直接连接至目标ICC，alpha不进入ICC管线
// 入参: x, y 设备坐标, c 预乘工作颜色, space 合成空间, mode 打印颜色策略
// 返回: error 非法颜色、数值或目标变换错误
func (s *deviceRenderState) pixel(x, y int, c renderColor, space renderColorSpace, mode PrintColorMode) error {
	if err := c.validate(); err != nil {
		return err
	}
	offset := (y-s.result.Rect.Min.Y)*s.result.Stride + (x-s.result.Rect.Min.X)*(s.result.Channels+1)
	alpha := uint16(math.Floor(c.a*65535 + 0.5))
	if alpha == 0 {
		return nil
	}
	linear := [3]float64{c.r / c.a, c.g / c.a, c.b / c.a}
	if space == renderSRGB {
		for axis := range 3 {
			linear[axis] = renderSRGBToLinear(linear[axis])
		}
	}
	if mode == PrintColorGrayscale || mode == PrintColorMonochrome {
		luminance := colorClamp(0.2126*linear[0] + 0.7152*linear[1] + 0.0722*linear[2])
		if mode == PrintColorMonochrome {
			if luminance < 0.5 {
				luminance = 0
			} else {
				luminance = 1
			}
		}
		linear = [3]float64{luminance, luminance, luminance}
	}
	value, err := s.target.fromXYZ(iccMatrixColor(iccPCSFromLinearRGB, linear))
	if err != nil {
		return err
	}
	for channel, sample := range value[:s.result.Channels] {
		if !geometryFinite(sample) {
			return fmt.Errorf("%w: device output sample", ErrLimit)
		}
		s.result.Pix[offset+channel] = uint16(math.Floor(colorClamp(sample)*65535 + 0.5))
	}
	s.result.Pix[offset+s.result.Channels] = alpha
	return nil
}

// output 只在完整绘制成功时交付设备图像，失败不暴露部分分量
// 入参: err 共享绘制流程返回的错误
// 返回: *DeviceImage 完整结果, error 绘制或内部状态错误
func (s *deviceRenderState) output(err error) (*DeviceImage, error) {
	if err != nil {
		return nil, err
	}
	if s.result == nil {
		return nil, fmt.Errorf("%w: missing device output", ErrInvalid)
	}
	s.diagMu.Lock()
	s.result.Diagnostics = append([]Diagnostic(nil), s.diagnostics...)
	s.diagMu.Unlock()
	return s.result, nil
}

// validateRenderSurface 校验隔离表面的工作空间、坐标范围与像素预算
// 入参: bounds 像素坐标范围, space 合成空间, maxPixels 本次允许的像素数
// 返回: int 表面像素总数, error 参数或资源限制错误
func validateRenderSurface(bounds image.Rectangle, space renderColorSpace, maxPixels int) (int, error) {
	if space != renderSRGB && space != renderScRGB {
		return 0, fmt.Errorf("%w: surface color space", ErrUnsupported)
	}
	if maxPixels < 0 || bounds.Min.X > bounds.Max.X || bounds.Min.Y > bounds.Max.Y {
		return 0, fmt.Errorf("%w: surface bounds or pixel budget", ErrInvalid)
	}
	if bounds.Min.X < -(1<<30) || bounds.Min.Y < -(1<<30) || bounds.Max.X > 1<<30 || bounds.Max.Y > 1<<30 {
		return 0, fmt.Errorf("%w: surface coordinate range", ErrLimit)
	}
	width, height := uint64(int64(bounds.Max.X)-int64(bounds.Min.X)), uint64(int64(bounds.Max.Y)-int64(bounds.Min.Y))
	if width > rasterMaxDimension || height > rasterMaxDimension {
		return 0, fmt.Errorf("%w: surface dimensions", ErrLimit)
	}
	count := width * height
	if count > uint64(maxPixels) || count > uint64(^uint(0)>>1)/32 {
		return 0, fmt.Errorf("%w: surface pixel budget", ErrLimit)
	}
	return int(count), nil
}

// allocRenderSurface 按已校验尺寸从对象池或堆分配清零的隔离渲染表面
// 入参: bounds 像素坐标范围, space 合成空间, count 已校验的表面像素总数
// 返回: *renderSurface 独立透明表面
func allocRenderSurface(bounds image.Rectangle, space renderColorSpace, count int) *renderSurface {
	var pixels []renderColor
	if count > 0 && count <= renderSurfacePoolMax {
		if pooled, ok := renderSurfacePool.Get().(*[]renderColor); ok && pooled != nil && cap(*pooled) >= count {
			pixels = (*pooled)[:count]
			clear(pixels)
		}
	}
	if pixels == nil {
		pixels = make([]renderColor, count)
	}
	return &renderSurface{bounds: bounds, space: space, pixels: pixels}
}

// releaseRenderSurface 将常规尺寸图块表面的像素缓冲归还有界对象池，超大缓冲交由GC回收
// 入参: s 不再使用的临时渲染表面
func releaseRenderSurface(s *renderSurface) {
	if s == nil || s.pixels == nil {
		return
	}
	if cap(s.pixels) > 0 && cap(s.pixels) <= renderSurfacePoolMax {
		buf := s.pixels[:cap(s.pixels)]
		renderSurfacePool.Put(&buf)
	}
	s.pixels = nil
	s.reserved = 0
}

// paintBinarySolid 以二值覆盖掩模快速合成已校验纯色画刷，逐比特保持source-over公式
// 入参: mask 仅含零与满覆盖的二值掩模, fg 已校验的预乘纯色
// 返回: error 扩展空间溢出错误
func (s *renderSurface) paintBinarySolid(mask *image.Alpha, fg renderColor) error {
	if fg.a == 0 {
		return nil
	}
	bounds := s.bounds.Intersect(mask.Bounds())
	width := bounds.Dx()
	if width <= 0 || bounds.Dy() <= 0 {
		return nil
	}
	surfStride := s.bounds.Dx()
	surfColOff := bounds.Min.X - s.bounds.Min.X
	maskColOff := bounds.Min.X - mask.Rect.Min.X
	rem := 1 - fg.a
	if s.space == renderSRGB {
		if fg.a == 1 {
			for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
				mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
				sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
				maskRow := mask.Pix[mOff : mOff+width]
				dstRow := s.pixels[sOff : sOff+width]
				for col, alpha := range maskRow {
					if alpha != 0 {
						dstRow[col] = fg
					}
				}
			}
			return nil
		}
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
			sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
			maskRow := mask.Pix[mOff : mOff+width]
			dstRow := s.pixels[sOff : sOff+width]
			for col, alpha := range maskRow {
				if alpha != 0 {
					d := dstRow[col]
					dstRow[col] = renderColor{fg.r + d.r*rem, fg.g + d.g*rem, fg.b + d.b*rem, fg.a + d.a*rem}
				}
			}
		}
		return nil
	}
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
		sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
		maskRow := mask.Pix[mOff : mOff+width]
		dstRow := s.pixels[sOff : sOff+width]
		for col, alpha := range maskRow {
			if alpha == 0 {
				continue
			}
			d := dstRow[col]
			r := fg.r + d.r*rem
			g := fg.g + d.g*rem
			b := fg.b + d.b*rem
			a := fg.a + d.a*rem
			if !geometryFinite(r, g, b, a) {
				return fmt.Errorf("%w: compositor arithmetic overflow", ErrLimit)
			}
			dstRow[col] = renderColor{r, g, b, a}
		}
	}
	return nil
}

// paintBinaryGradient 以二值覆盖掩模零分配采样并合成渐变画刷
// 入参: mask 二值覆盖掩模, scale 子像素缩放倍率, sampler 只读渐变采样器
// 返回: error 采样或合成错误
func (s *renderSurface) paintBinaryGradient(mask *image.Alpha, scale float64, sampler *gradientSampler) error {
	bounds := s.bounds.Intersect(mask.Bounds())
	width := bounds.Dx()
	if width <= 0 || bounds.Dy() <= 0 {
		return nil
	}
	surfStride := s.bounds.Dx()
	surfColOff := bounds.Min.X - s.bounds.Min.X
	maskColOff := bounds.Min.X - mask.Rect.Min.X
	isSRGB := s.space == renderSRGB
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		py := (float64(y) + 0.5) / scale
		mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
		sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
		maskRow := mask.Pix[mOff : mOff+width]
		dstRow := s.pixels[sOff : sOff+width]
		for col, alpha := range maskRow {
			if alpha == 0 {
				continue
			}
			px := (float64(bounds.Min.X+col) + 0.5) / scale
			fg, err := sampler.sampleRenderColor(Point{px, py}, s.space)
			if err != nil {
				return err
			}
			if fg.a == 0 {
				continue
			}
			rem := 1 - fg.a
			d := dstRow[col]
			r := fg.r + d.r*rem
			g := fg.g + d.g*rem
			b := fg.b + d.b*rem
			a := fg.a + d.a*rem
			if !isSRGB && !geometryFinite(r, g, b, a) {
				return fmt.Errorf("%w: compositor arithmetic overflow", ErrLimit)
			}
			dstRow[col] = renderColor{r, g, b, a}
		}
	}
	return nil
}

// paintBinaryImage 以二值覆盖掩模与独占缓存采样并合成图像画刷，支持多核并发零竞争运行
// 入参: mask 二值覆盖掩模, scale 子像素缩放倍率, sampler 图像画刷采样器, cache 工作Goroutine独占缓存, concurrent 是否并发阶段
// 返回: error 采样或合成错误
func (s *renderSurface) paintBinaryImage(mask *image.Alpha, scale float64, sampler *imageSampler, cache *imageSampleCache, concurrent bool) error {
	bounds := s.bounds.Intersect(mask.Bounds())
	width := bounds.Dx()
	if width <= 0 || bounds.Dy() <= 0 {
		return nil
	}
	cache.valid = false
	surfStride := s.bounds.Dx()
	surfColOff := bounds.Min.X - s.bounds.Min.X
	maskColOff := bounds.Min.X - mask.Rect.Min.X
	isSRGB := s.space == renderSRGB
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		py := (float64(y) + 0.5) / scale
		cy := math.Floor(py) + 0.5
		mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
		sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
		maskRow := mask.Pix[mOff : mOff+width]
		dstRow := s.pixels[sOff : sOff+width]
		for col, alpha := range maskRow {
			if alpha == 0 {
				continue
			}
			px := (float64(bounds.Min.X+col) + 0.5) / scale
			fg, err := sampler.sampleAtCached(Point{px, py}, Point{math.Floor(px) + 0.5, cy}, cache, concurrent)
			if err != nil {
				return err
			}
			if fg.a == 0 {
				continue
			}
			rem := 1 - fg.a
			d := dstRow[col]
			r := fg.r + d.r*rem
			g := fg.g + d.g*rem
			b := fg.b + d.b*rem
			a := fg.a + d.a*rem
			if !isSRGB && !geometryFinite(r, g, b, a) {
				return fmt.Errorf("%w: compositor arithmetic overflow", ErrLimit)
			}
			dstRow[col] = renderColor{r, g, b, a}
		}
	}
	return nil
}

// paintBinarySample 以二值覆盖掩模采样通用画刷并合成，可选互斥锁在整块首次有效采样前加锁保护非并发安全画刷
// 入参: mask 二值覆盖掩模, scale 子像素缩放倍率, sample 颜色采样器, lock 可选并发保护锁
// 返回: error 采样或合成错误
func (s *renderSurface) paintBinarySample(mask *image.Alpha, scale float64, sample sceneSample, lock *sync.Mutex) error {
	bounds := s.bounds.Intersect(mask.Bounds())
	width := bounds.Dx()
	if width <= 0 || bounds.Dy() <= 0 {
		return nil
	}
	locked := false
	if lock != nil {
		defer func() {
			if locked {
				lock.Unlock()
			}
		}()
	}
	surfStride := s.bounds.Dx()
	surfColOff := bounds.Min.X - s.bounds.Min.X
	maskColOff := bounds.Min.X - mask.Rect.Min.X
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		py := (float64(y) + 0.5) / scale
		cy := math.Floor(py) + 0.5
		mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
		sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
		maskRow := mask.Pix[mOff : mOff+width]
		dstRow := s.pixels[sOff : sOff+width]
		for col, alpha := range maskRow {
			if alpha == 0 {
				continue
			}
			if lock != nil && !locked {
				lock.Lock()
				locked = true
			}
			px := (float64(bounds.Min.X+col) + 0.5) / scale
			fg, err := sample(Point{px, py}, Point{math.Floor(px) + 0.5, cy})
			if err != nil {
				return err
			}
			if err := fg.validate(); err != nil {
				return err
			}
			if fg.a == 0 {
				continue
			}
			pixel, err := renderSourceOver(fg, dstRow[col])
			if err != nil {
				return err
			}
			dstRow[col] = pixel
		}
	}
	return nil
}

// paintBinarySampleCached 以二值覆盖掩模和工作Goroutine独占缓存采样通用画刷并合成
// 入参: mask 二值覆盖掩模, scale 子像素缩放倍率, sample 带缓存的颜色采样器, cache 工作Goroutine独占缓存, lock 可选并发保护锁
// 返回: error 采样或合成错误
func (s *renderSurface) paintBinarySampleCached(mask *image.Alpha, scale float64, sample sceneSampleCached, cache *imageSampleCache, lock *sync.Mutex) error {
	bounds := s.bounds.Intersect(mask.Bounds())
	width := bounds.Dx()
	if width <= 0 || bounds.Dy() <= 0 {
		return nil
	}
	locked := false
	if lock != nil {
		defer func() {
			if locked {
				lock.Unlock()
			}
		}()
	}
	surfStride := s.bounds.Dx()
	surfColOff := bounds.Min.X - s.bounds.Min.X
	maskColOff := bounds.Min.X - mask.Rect.Min.X
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		py := (float64(y) + 0.5) / scale
		cy := math.Floor(py) + 0.5
		mOff := (y-mask.Rect.Min.Y)*mask.Stride + maskColOff
		sOff := (y-s.bounds.Min.Y)*surfStride + surfColOff
		maskRow := mask.Pix[mOff : mOff+width]
		dstRow := s.pixels[sOff : sOff+width]
		for col, alpha := range maskRow {
			if alpha == 0 {
				continue
			}
			if lock != nil && !locked {
				lock.Lock()
				locked = true
			}
			px := (float64(bounds.Min.X+col) + 0.5) / scale
			fg, err := sample(Point{px, py}, Point{math.Floor(px) + 0.5, cy}, cache)
			if err != nil {
				return err
			}
			if err := fg.validate(); err != nil {
				return err
			}
			if fg.a == 0 {
				continue
			}
			pixel, err := renderSourceOver(fg, dstRow[col])
			if err != nil {
				return err
			}
			dstRow[col] = pixel
		}
	}
	return nil
}

// profile 按定义部件解析ICC引用，在解压前检查内容类型和字节预算
// 入参: part 定义部件, uri 配置文件引用
// 返回: *iccProfile 只读配置文件, error 引用、封装或资源错误
func (c *sceneColorCache) profile(part, uri string) (result *iccProfile, err error) {
	result, _, err = c.profileUsability(part, uri, nil)
	return result, err
}

// colorProfileUnusable 仅分类完整ICC数据的解析或转换错误，不用于包读取及引用错误
// 入参: err ICC解析或转换错误
// 返回: bool 是否为不可用配置文件，预算和取消始终不可回退
func colorProfileUnusable(err error) bool {
	return !errors.Is(err, ErrLimit) && !errors.Is(err, context.Canceled) && !errors.Is(err, context.DeadlineExceeded) && (errors.Is(err, ErrInvalid) || errors.Is(err, ErrUnsupported))
}

// cacheProfile 将已读ICC字节计入预算并缓存解析结果，失败也占用配置文件名额
// 入参: key 已规范化缓存键, data 已通过字节预算检查的完整ICC
// 返回: *iccProfile 只读配置文件, error 原始ICC解析错误
func (c *sceneColorCache) cacheProfile(key string, data []byte) (*iccProfile, error) {
	c.bytes -= int64(len(data))
	profile, err := parseICCProfile(data)
	if err != nil {
		if c.profileErrors == nil {
			c.profileErrors = make(map[string]error)
		}
		c.profileErrors[key] = err
		return nil, err
	}
	c.profiles[key] = profile
	return profile, nil
}

// profileUsability 共用关联ICC的引用、预算、缓存和读取路径，仅对ICC解析失败标记不可用
// 入参: part 定义部件, uri 配置文件引用, ctx 可选取消Context
// 返回: *iccProfile 只读配置文件, bool 是否为ICC内容不可用, error 引用、读取或解析错误
func (c *sceneColorCache) profileUsability(part, uri string, ctx context.Context) (result *iccProfile, unusable bool, err error) {
	if err := checkContext(ctx); err != nil {
		return nil, false, err
	}
	part, err = resolvePart(part, uri)
	if err != nil {
		return nil, false, err
	}
	return c.profileResolved(part, ctx)
}

// profileResolved 按已规范化部件名称读取并缓存ICC，供配置查询与转换查找复用
// 入参: part 已解析的规范化部件名, ctx 可选取消Context
// 返回: *iccProfile 只读配置文件, bool 是否为ICC内容不可用, error 读取或解析错误
func (c *sceneColorCache) profileResolved(part string, ctx context.Context) (result *iccProfile, unusable bool, err error) {
	defer func() {
		if err != nil {
			err = wrapPartError(part, "", err)
		}
	}()
	key := strings.ToLower(part)
	if value := c.profiles[key]; value != nil {
		return value, false, nil
	}
	if err := c.profileErrors[key]; err != nil {
		return nil, colorProfileUnusable(err), err
	}
	if len(c.profiles)+len(c.profileErrors) >= c.maxProfiles {
		return nil, false, fmt.Errorf("%w: render color profile count", ErrLimit)
	}
	size, err := c.pkg.partSize(key)
	if err != nil {
		return nil, false, err
	}
	if c.bytes < 0 || size > uint64(c.bytes) {
		return nil, false, fmt.Errorf("%w: render color profile byte budget", ErrLimit)
	}
	media, err := c.pkg.contentType(part)
	if err != nil {
		return nil, false, err
	}
	if !strings.EqualFold(media, "application/vnd.ms-color.iccprofile") {
		return nil, false, fmt.Errorf("%w: color profile content type %q", ErrInvalid, media)
	}
	data, err := c.pkg.readPart(part)
	if err != nil {
		return nil, false, err
	}
	if err := checkContext(ctx); err != nil {
		c.bytes -= int64(len(data))
		return nil, false, err
	}
	profile, err := c.cacheProfile(key, data)
	if err != nil {
		return nil, colorProfileUnusable(err), err
	}
	return profile, false, nil
}

// transform 选择并缓存指定意图的源转换，部件身份按OPC规则忽略大小写
// 入参: part 定义部件, uri 配置文件引用, intent ICC渲染意图
// 返回: *iccTransform 只读转换, error 配置文件、能力或意图错误
func (c *sceneColorCache) transform(part, uri string, intent uint32) (*iccTransform, error) {
	part, err := resolvePart(part, uri)
	if err != nil {
		return nil, err
	}
	profile, _, err := c.profileResolved(part, nil)
	if err != nil {
		return nil, err
	}
	value, err := c.profileTransform(strings.ToLower(part), profile, intent)
	if err != nil {
		return nil, wrapPartError(part, "", err)
	}
	return value, nil
}

// profileTransform 缓存各渲染意图的转换或确定性失败，避免关联和内嵌配置文件被重复解析
// 入参: key 配置文件缓存键, profile 只读配置文件, intent ICC渲染意图
// 返回: *iccTransform 只读转换, error 配置文件、能力或意图错误
func (c *sceneColorCache) profileTransform(key string, profile *iccProfile, intent uint32) (*iccTransform, error) {
	if c.sourceIntent != IntentDefault {
		intent = uint32(c.sourceIntent - 1)
	}
	if intent > 3 {
		return nil, fmt.Errorf("%w: render color intent", ErrInvalid)
	}
	values := c.transforms[key]
	if values[intent] != nil {
		return values[intent], nil
	}
	if err := c.transformErrors[key][intent]; err != nil {
		return nil, err
	}
	value, err := prepareICCTransform(profile, intent)
	if err != nil {
		if c.transformErrors == nil {
			c.transformErrors = make(map[string][4]error)
		}
		failures := c.transformErrors[key]
		failures[intent] = err
		c.transformErrors[key] = failures
		return nil, err
	}
	values[intent] = value
	c.transforms[key] = values
	return value, nil
}

// vector 将ContextColor按矢量内容的缺省相对色度意图转换为非预乘scRGB
// 入参: part 颜色定义部件, value 非预乘源颜色
// 返回: Color 线性RGB颜色, error 配置文件、通道或数值错误
func (c *sceneColorCache) vector(part string, value Color) (Color, error) {
	if value.Space != ColorContext {
		return value, nil
	}
	if !geometryFinite(value.Alpha) || value.Alpha < 0 || value.Alpha > 1 {
		return Color{}, fmt.Errorf("%w: context color alpha", ErrInvalid)
	}
	transform, err := c.transform(part, value.ProfileURI, 1)
	if err != nil {
		return Color{}, err
	}
	input := value.Components
	var scaled [8]float64
	if transform.pipeline != nil && transform.pipeline.inputPrecision != 0 {
		if len(input) != transform.profile.channels || len(input) > len(scaled) {
			return Color{}, fmt.Errorf("%w: context color channel count", ErrInvalid)
		}
		scale := 255.0
		if transform.pipeline.inputPrecision == 2 {
			scale = 65535
		}
		for i, component := range input {
			if !geometryFinite(component) {
				return Color{}, fmt.Errorf("%w: context color value", ErrInvalid)
			}
			scaled[i] = math.Floor(colorClamp(component)*scale+0.5) / scale
		}
		input = scaled[:len(input)]
	}
	rgb, err := transform.linearRGB(input)
	if err != nil {
		return Color{}, err
	}
	return Color{Space: ColorScRGB, Alpha: value.Alpha, Components: []float64{rgb[0], rgb[1], rgb[2]}}, nil
}

// color 保持普通RGB颜色不变，仅对配置文件颜色调用本次绘制的转换器
// 入参: part 颜色定义部件, value 源颜色
// 返回: Color 可供合成的RGB颜色, error 颜色转换或能力错误
func (r *sceneRenderer) color(part string, value Color) (Color, error) {
	if value.Space != ColorContext {
		return value, nil
	}
	if r.options.color == nil {
		return Color{}, fmt.Errorf("%w: scene color source is unavailable", ErrUnsupported)
	}
	return r.options.color(part, value)
}

// gradientBrush 仅在存在配置文件颜色时复制停靠点，保留共享画刷和源颜色
// 入参: brush 源渐变画刷
// 返回: *Brush 转换后的独立画刷或原画刷, error 颜色转换错误
func (r *sceneRenderer) gradientBrush(brush *Brush) (*Brush, error) {
	var converted *Brush
	for i, stop := range brush.Stops {
		if stop.Color.Space != ColorContext {
			continue
		}
		if converted == nil {
			value := *brush
			value.Stops = append([]GradientStop(nil), brush.Stops...)
			converted = &value
		}
		color, err := r.color(brush.Part, stop.Color)
		if err != nil {
			return nil, fmt.Errorf("gradient stop %d: %w", i, err)
		}
		converted.Stops[i].Color = color
	}
	if converted != nil {
		return converted, nil
	}
	return brush, nil
}
