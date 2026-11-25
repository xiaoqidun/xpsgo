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
	"errors"
	"fmt"
	"image"
	"math"
	"sync"

	"github.com/xiaoqidun/jxrgo"
)

// jxrRowCacheMaxBytes 定义单个JPEG XR两行滑动缓存允许占用的最大内存字节数
const jxrRowCacheMaxBytes = 32 << 20

// jxrSampleNative 等常量表示JPEG XR渲染采样阶段选择的数据通道视图
const (
	jxrSampleNative jxrSampleMode = iota
	jxrSampleRGB
	jxrSampleLinear
)

// jxrSampleMode 表示JPEG XR采样器读取原生分量、设备域RGB或线性scRGB的模式
type jxrSampleMode uint8

// jxrLinearKey 唯一标识一组按需缓存的JPEG XR线性读取器参数
type jxrLinearKey struct {
	applyCICP   bool
	applyICC    bool
	intent      jxrgo.RenderingIntent
	hdrPeakNits float64
}

// jxrImage 保存独立解码图像的原生通道与按需缓存读取器，取样时处理非预乘，不复制整幅像素
type jxrImage struct {
	bounds        image.Rectangle
	raster        *jxrgo.Raster
	info          jxrgo.Info
	components    [iccMaxChannels + 1]jxrgo.Component
	limits        jxrgo.Limits
	channels      int
	alpha         bool
	premultiplied bool
	linear        bool
	ycc           bool
	units         uint64
	readerMu      sync.Mutex
	rgbReader     *jxrgo.RGBReader
	linearReaders map[jxrLinearKey]*jxrgo.LinearReader
	rowPool       sync.Pool
}

// jxrRowBuffer 保存JPEG XR单行批量读取的可复用通道、四分量行与位模式缓冲
type jxrRowBuffer struct {
	channels [iccMaxChannels][]float64
	alpha    []float64
	rgba     []float64
	bits     []uint32
}

// jxrRowCache 保存单工作Goroutine独占的两行滑动行缓存及读取器引用，避免双线性采样重复逐像素读取
type jxrRowCache struct {
	source       *jxrImage
	mode         jxrSampleMode
	key          jxrLinearKey
	linearReader *jxrgo.LinearReader
	rgbReader    *jxrgo.RGBReader
	rows         [2]jxrRowBuffer
	ys           [2]int
	valid        [2]bool
}

// jxrDecodeWorkersKey 用于在Context中传递本次绘制允许的JPEG XR解码并发上限
type jxrDecodeWorkersKey struct{}

// withJXRDecodeWorkers 将绘制选项中的显式并发上限附着至图像解码Context
// 入参: ctx 基础取消Context, workers 绘制并发上限，零值保持自动策略
// 返回: context.Context 携带并发上限的Context
func withJXRDecodeWorkers(ctx context.Context, workers int) context.Context {
	if workers <= 0 {
		return ctx
	}
	return context.WithValue(ctx, jxrDecodeWorkersKey{}, workers)
}

// jxrDecodeWorkers 根据Context并发上限、像素规模与内存预算计算JPEG XR有效解码工作数
// 入参: ctx 解码Context, maxPixels 剩余像素预算, memoryLimit 可用解码内存上限
// 返回: int 合法的解码并发工作数
func jxrDecodeWorkers(ctx context.Context, maxPixels, memoryLimit uint64) int {
	requested, _ := ctx.Value(jxrDecodeWorkersKey{}).(int)
	if requested == 1 || maxPixels < 16384 || memoryLimit < 4<<20 {
		return 1
	}
	tasks := int(min(maxPixels/4096, 64))
	return budgetXPSWorkers(resolveXPSWorkers(requested, tasks), memoryLimit, 2<<20)
}

// jxrDecodeMemoryLimit 依据字节与像素预算推导JPEG XR解码工作内存上限，执行饱和防溢出保护
// 入参: inputBytes 输入文件字节数, maxPixels 剩余RGBA64等价容量, maxBytes 调用方声明的图像字节上限
// 返回: uint64 受地址空间保护的工作内存上限
func jxrDecodeMemoryLimit(inputBytes, maxPixels, maxBytes uint64) uint64 {
	const maxAddressable = uint64(^uint(0) >> 1)
	limit := uint64(rasterMaxWork)
	if maxBytes > limit {
		limit = min(maxBytes, maxAddressable)
	}
	if inputBytes > limit {
		limit = min(inputBytes, maxAddressable)
	}
	var pixelBytes uint64
	if maxPixels > maxAddressable/16 {
		pixelBytes = maxAddressable
	} else {
		pixelBytes = maxPixels * 16
	}
	if pixelBytes > limit {
		limit = pixelBytes
	}
	return limit
}

// selectJXRPrimaryImage 在JPEG XR多图容器中跳过Preview目录并选出首个主图索引及信息
// 入参: ctx 取消Context, decoder 已初始化的JPEG XR解码器
// 返回: int 选中的图像目录索引, jxrgo.Info 选中图像元数据, error 目录读取、取消或仅含预览图错误
func selectJXRPrimaryImage(ctx context.Context, decoder *jxrgo.Decoder) (int, jxrgo.Info, error) {
	count, err := decoder.ImageCount(ctx)
	if err != nil {
		return 0, jxrgo.Info{}, jxrImageError(err)
	}
	if count <= 1 {
		info := decoder.Info()
		if info.ImageType&jxrgo.ImageTypePreview != 0 {
			return 0, jxrgo.Info{}, fmt.Errorf("%w: JPEG XR container has only preview image", ErrInvalid)
		}
		return 0, info, nil
	}
	for index := range count {
		info, err := decoder.ImageInfo(ctx, index)
		if err != nil {
			return 0, jxrgo.Info{}, jxrImageError(err)
		}
		if info.ImageType&jxrgo.ImageTypePreview == 0 {
			return index, info, nil
		}
	}
	return 0, jxrgo.Info{}, fmt.Errorf("%w: JPEG XR container has no primary image", ErrInvalid)
}

// jxrImageCICP 将JXRGo的CICP色彩编码结构转换为文档图像统一的四元组描述
// 入参: encoding 可选JPEG XR CICP编码声明
// 返回: *imageCICP 统一CICP四元组，空指针保持nil
func jxrImageCICP(encoding *jxrgo.ColorEncoding) *imageCICP {
	if encoding == nil {
		return nil
	}
	return &imageCICP{
		primaries: encoding.Primaries,
		transfer:  encoding.Transfer,
		matrix:    encoding.Matrix,
		fullRange: encoding.FullRange,
	}
}

// jxrImageColorSpace 将JXRGo颜色空间枚举映射为公开图像源色彩空间类别
// 入参: space JXRGo颜色空间标识
// 返回: ImageColorSpace 公开图像源色彩空间
func jxrImageColorSpace(space jxrgo.ColorSpace) ImageColorSpace {
	switch space {
	case jxrgo.ColorGray:
		return ImageColorGray
	case jxrgo.ColorRGB:
		return ImageColorRGB
	case jxrgo.ColorYCC:
		return ImageColorYCC
	case jxrgo.ColorCMYK, jxrgo.ColorCMYKDirect:
		return ImageColorCMYK
	case jxrgo.ColorMultiChannel:
		return ImageColorMultiChannel
	default:
		return ImageColorUnknown
	}
}

// jxrEXIFOrientation 将JPEG XR的0至7方向枚举转换为EXIF/TIFF Tag 274的1至8方向编码
// 入参: orientation JXRGo声明方向
// 返回: uint32 标准EXIF/TIFF方向值（1至8）
func jxrEXIFOrientation(orientation jxrgo.Orientation) uint32 {
	switch orientation {
	case jxrgo.OrientationNone:
		return 1
	case jxrgo.OrientationFlipY:
		return 4
	case jxrgo.OrientationFlipX:
		return 2
	case jxrgo.OrientationFlipXY:
		return 3
	case jxrgo.OrientationRotate90:
		return 6
	case jxrgo.OrientationRotate90FlipY:
		return 7
	case jxrgo.OrientationRotate90FlipX:
		return 5
	case jxrgo.OrientationRotate90FlipXY:
		return 8
	default:
		return 1
	}
}

// jxrIsFloating 判断JPEG XR颜色通道是否采用IEEE半精度或单精度浮点样本编码
// 入参: info JPEG XR图像元数据
// 返回: bool 是否为浮点样本
func jxrIsFloating(info jxrgo.Info) bool {
	count := min(info.Channels, len(info.Components))
	for i := range count {
		if info.Components[i].Format == jxrgo.SampleFloat {
			return true
		}
	}
	return false
}

// jxrIntentFromICC 将ICC头部标准意图编码映射为JXRGo渲染意图枚举
// 入参: intent ICC意图编号，0感知、1相对、2饱和度、3绝对
// 返回: jxrgo.RenderingIntent 对应的JXRGo渲染意图
func jxrIntentFromICC(intent uint32) jxrgo.RenderingIntent {
	switch intent {
	case 0:
		return jxrgo.IntentPerceptual
	case 2:
		return jxrgo.IntentSaturation
	case 3:
		return jxrgo.IntentAbsolute
	default:
		return jxrgo.IntentRelative
	}
}

// jxrIntentFromRender 将公开RenderingIntent映射为JXRGo渲染意图枚举
// 入参: intent 文档渲染意图
// 返回: jxrgo.RenderingIntent 对应的JXRGo渲染意图
func jxrIntentFromRender(intent RenderingIntent) jxrgo.RenderingIntent {
	switch intent {
	case IntentPerceptual:
		return jxrgo.IntentPerceptual
	case IntentSaturation:
		return jxrgo.IntentSaturation
	case IntentAbsoluteColorimetric:
		return jxrgo.IntentAbsolute
	default:
		return jxrgo.IntentRelative
	}
}

// decodeJXRImage 使用JXRGo重建主图原生分量并完整保留内嵌ICC及CICP元数据，不在解码期固化颜色管线
// 入参: ctx 已规范化取消Context, data JPEG XR文件, maxPixels 剩余RGBA64等价容量, maxBytes 调用方图像字节上限
// 返回: *rasterImage 独立原生图像, error 数据、能力、资源或取消错误
func decodeJXRImage(ctx context.Context, data []byte, maxPixels, maxBytes uint64) (*rasterImage, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if maxPixels == 0 {
		return nil, fmt.Errorf("%w: JPEG XR document pixel capacity", ErrLimit)
	}
	if maxBytes > 0 && uint64(len(data)) > maxBytes {
		return nil, fmt.Errorf("%w: JPEG XR input byte budget", ErrLimit)
	}
	memoryLimit := jxrDecodeMemoryLimit(uint64(len(data)), maxPixels, maxBytes)
	workers := jxrDecodeWorkers(ctx, maxPixels, memoryLimit)
	limits := jxrgo.Limits{MaxInputBytes: uint64(max(1, len(data))), MaxPixels: maxPixels, MaxMemoryBytes: memoryLimit}
	decoder, err := jxrgo.NewDecoderAt(ctx, bytes.NewReader(data), int64(len(data)), &jxrgo.DecodeOptions{Workers: workers, Limits: limits})
	if err != nil {
		return nil, jxrImageError(err)
	}
	defer decoder.Close()
	if decoder.Info().Format != jxrgo.FormatJXR {
		return nil, fmt.Errorf("%w: JPEG XR requires a file container", ErrInvalid)
	}
	imageIndex, info, err := selectJXRPrimaryImage(ctx, decoder)
	if err != nil {
		return nil, err
	}
	stride := info.Channels
	if info.Alpha {
		stride++
	}
	if info.Channels < 1 || info.Channels > iccMaxChannels || len(info.Components) != stride {
		return nil, fmt.Errorf("%w: JPEG XR component count", ErrUnsupported)
	}
	ycc := false
	switch info.ColorSpace {
	case jxrgo.ColorGray, jxrgo.ColorRGB, jxrgo.ColorCMYK, jxrgo.ColorCMYKDirect, jxrgo.ColorMultiChannel:
	case jxrgo.ColorYCC:
		if info.Channels != 3 {
			return nil, fmt.Errorf("%w: JPEG XR YCC component count", ErrUnsupported)
		}
		ycc = true
	default:
		return nil, fmt.Errorf("%w: JPEG XR document color interpretation", ErrUnsupported)
	}
	storage := 0
	for _, component := range info.Components {
		if !ycc && (component.Bounds != info.Bounds || component.XStep != 1 || component.YStep != 1) {
			return nil, fmt.Errorf("%w: JPEG XR subsampled document components", ErrUnsupported)
		}
		width := 2
		if component.Precision == 32 && (component.Format == jxrgo.SampleFloat || component.Format == jxrgo.SampleFixed) {
			width = 4
		}
		storage += width
	}
	units := uint64((storage + 7) / 8)
	count := uint64(info.Bounds.Dx()) * uint64(info.Bounds.Dy())
	if info.Bounds.Min != (image.Point{}) || info.Bounds.Empty() || info.Bounds.Dx() > rasterMaxDimension || info.Bounds.Dy() > rasterMaxDimension || count > maxPixels/units {
		return nil, fmt.Errorf("%w: JPEG XR document pixel capacity", ErrLimit)
	}
	var raster *jxrgo.Raster
	if imageIndex == 0 {
		raster, err = decoder.Decode(ctx)
	} else {
		raster, err = decoder.DecodeImage(ctx, imageIndex)
	}
	if err != nil {
		return nil, jxrImageError(err)
	}
	_ = decoder.Close()
	premultiplied := info.Premultiplied && info.Alpha
	view := &jxrImage{
		bounds:        info.Bounds,
		raster:        raster,
		info:          info,
		limits:        limits,
		channels:      info.Channels,
		alpha:         info.Alpha,
		premultiplied: premultiplied,
		linear:        info.Linear,
		ycc:           ycc,
		units:         units,
	}
	for index := range stride {
		component, err := raster.Component(index)
		if err != nil {
			return nil, jxrImageError(err)
		}
		view.components[index] = component
	}
	for index := range stride {
		isAlpha := view.alpha && index == view.channels
		compInfo := view.components[index].Info()
		if compInfo.Format == jxrgo.SampleFloat || isAlpha && view.linear {
			if err := validateJXRFiniteComponent(ctx, view.components[index], compInfo.Bounds, isAlpha); err != nil {
				return nil, err
			}
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return &rasterImage{
		jxr:          view,
		dpi:          Point{info.Resolution.X, info.Resolution.Y},
		channels:     info.Channels,
		profile:      info.ICCProfile,
		cicp:         jxrImageCICP(info.ColorEncoding),
		srgb:         info.ColorHint == jxrgo.ColorHintSRGB,
		linear:       info.Linear,
		multiChannel: info.ColorSpace == jxrgo.ColorMultiChannel,
		colorSpace:   jxrImageColorSpace(info.ColorSpace),
		hasAlpha:     info.Alpha,
		bitDepth:     int(info.Components[0].Precision),
		floating:     jxrIsFloating(info),
		orientation:  jxrEXIFOrientation(info.Orientation),
	}, nil
}

// validateJXRFiniteComponent 批量校验浮点或线性透明分量的有限性，浮点通道使用位模式行读取避免逐像素转换
// 入参: ctx 取消Context, component 分量视图, bounds 分量自身像素范围, isAlpha 是否为透明度分量
// 返回: error 取消、读取或非有限数值错误
func validateJXRFiniteComponent(ctx context.Context, component jxrgo.Component, bounds image.Rectangle, isAlpha bool) error {
	label := "JPEG XR non-finite color"
	if isAlpha {
		label = "JPEG XR non-finite alpha"
	}
	info := component.Info()
	switch info.Format {
	case jxrgo.SampleUnsigned, jxrgo.SampleFixed, jxrgo.SampleRGBE:
		return checkContext(ctx)
	case jxrgo.SampleFloat:
		if info.Precision == 32 || info.Precision == 16 {
			mask := uint32(0x7f800000)
			if info.Precision == 16 {
				mask = 0x7c00
			}
			row := make([]uint32, bounds.Dx())
			for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
				if err := checkContext(ctx); err != nil {
					return err
				}
				if err := component.ReadRowBits(y, row); err != nil {
					return jxrImageError(err)
				}
				for _, bits := range row {
					if bits&mask == mask {
						return fmt.Errorf("%w: %s", ErrUnsupported, label)
					}
				}
			}
			return nil
		}
	}
	row := make([]float64, bounds.Dx())
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if err := component.ReadRow(y, row); err != nil {
			return jxrImageError(err)
		}
		for _, value := range row {
			if !geometryFinite(value) {
				return fmt.Errorf("%w: %s", ErrUnsupported, label)
			}
		}
	}
	return nil
}

// jxrUnpremultiply 展开JPEG XR预乘颜色分量，扩展范围通道保留原始域并统一拒绝非有限结果
// 入参: value 源颜色分量, alpha 已校验的单位区间透明度, preserveExtended 是否保留超单位区间分量
// 返回: float64 非预乘颜色分量, error 非有限颜色错误
func jxrUnpremultiply(value, alpha float64, preserveExtended bool) (float64, error) {
	if !geometryFinite(value) {
		return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
	}
	if alpha == 0 {
		return 0, nil
	}
	unpremultiplied := value / alpha
	if !geometryFinite(unpremultiplied) {
		return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
	}
	if preserveExtended {
		return unpremultiplied, nil
	}
	return colorClamp(unpremultiplied), nil
}

// jxrEffectiveChromaOffset 返回子采样分量的有效色度相位偏移，未知相位采用ITU-T T.832默认居中相位
// 入参: offset 声明的相位偏移, step 下采样步长, known 是否显式声明相位
// 返回: float64 有效相位偏移
func jxrEffectiveChromaOffset(offset float64, step uint8, known bool) float64 {
	if known {
		return offset
	}
	return float64(step-1) * 0.5
}

// jxrResampleAxis 按源分量相位步长计算主网格坐标在子采样平面上的双线性邻点与权重
// 入参: at 零起点主网格坐标, count 子采样轴长度, offset 有效相位偏移, step 下采样步长
// 返回: int 低索引, int 高索引, float64 插值权重
func jxrResampleAxis(at, count int, offset float64, step uint8) (int, int, float64) {
	if count <= 1 || step <= 1 {
		idx := max(0, min(count-1, at))
		return idx, idx, 0
	}
	position := (float64(at) - offset) / float64(step)
	position = max(0, min(float64(count-1), position))
	low := int(math.Floor(position))
	return low, min(low+1, count-1), position - float64(low)
}

// jxrSampleComponent 在主图网格读取单个源分量，子采样分量执行零分配相位双线性上采样
// 入参: comp 源分量视图, x, y 主图坐标, bounds 主图范围
// 返回: float64 原生源分量数值, error 取样或非有限插值错误
func jxrSampleComponent(comp jxrgo.Component, x, y int, bounds image.Rectangle) (float64, error) {
	info := comp.Info()
	if info.XStep == 1 && info.YStep == 1 && info.Bounds == bounds {
		value, err := comp.Sample(x, y)
		if err != nil {
			return 0, jxrImageError(err)
		}
		return value, nil
	}
	ox := jxrEffectiveChromaOffset(info.XOffset, info.XStep, info.XPositionKnown)
	oy := jxrEffectiveChromaOffset(info.YOffset, info.YStep, info.YPositionKnown)
	x0, x1, fx := jxrResampleAxis(x-bounds.Min.X, info.Bounds.Dx(), ox, info.XStep)
	y0, y1, fy := jxrResampleAxis(y-bounds.Min.Y, info.Bounds.Dy(), oy, info.YStep)
	bx, by := info.Bounds.Min.X, info.Bounds.Min.Y
	if fx == 0 && fy == 0 {
		value, err := comp.Sample(bx+x0, by+y0)
		if err != nil {
			return 0, jxrImageError(err)
		}
		return value, nil
	}
	var values [4]float64
	for idx, pt := range [4]image.Point{{x0, y0}, {x1, y0}, {x0, y1}, {x1, y1}} {
		if idx&1 != 0 && fx == 0 || idx&2 != 0 && fy == 0 {
			continue
		}
		v, err := comp.Sample(bx+pt.X, by+pt.Y)
		if err != nil {
			return 0, jxrImageError(err)
		}
		if !geometryFinite(v) {
			return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
		}
		values[idx] = v
	}
	return (values[0]*(1-fx)+values[1]*fx)*(1-fy) + (values[2]*(1-fx)+values[3]*fx)*fy, nil
}

// getLinearReader 线程安全地按参数键复用或懒创建JXRGo线性读取器
// 入参: key 线性读取配置键
// 返回: *jxrgo.LinearReader 只读并发安全的线性读取器, error 构建失败错误
func (source *jxrImage) getLinearReader(key jxrLinearKey) (*jxrgo.LinearReader, error) {
	source.readerMu.Lock()
	defer source.readerMu.Unlock()
	if reader := source.linearReaders[key]; reader != nil {
		return reader, nil
	}
	opts := jxrgo.LinearOptions{
		Filter:        jxrgo.ResampleBilinear,
		ApplyCICP:     key.applyCICP,
		ApplyICC:      key.applyICC,
		Intent:        key.intent,
		HDRPeakNits:   key.hdrPeakNits,
		Unpremultiply: true,
		Limits:        source.limits,
	}
	reader, err := source.raster.NewLinearReader(context.Background(), &opts)
	if err != nil {
		return nil, jxrImageError(err)
	}
	if source.linearReaders == nil {
		source.linearReaders = make(map[jxrLinearKey]*jxrgo.LinearReader)
	}
	source.linearReaders[key] = reader
	return reader, nil
}

// getRGBReader 线程安全地复用或懒创建JXRGo设备域非线性RGB读取器
// 返回: *jxrgo.RGBReader 只读并发安全的设备RGB读取器, error 构建失败错误
func (source *jxrImage) getRGBReader() (*jxrgo.RGBReader, error) {
	source.readerMu.Lock()
	defer source.readerMu.Unlock()
	if source.rgbReader != nil {
		return source.rgbReader, nil
	}
	opts := jxrgo.RGBOptions{
		Filter:          jxrgo.ResampleBilinear,
		ApplyCICPMatrix: source.info.ColorEncoding != nil,
		Unpremultiply:   true,
		Limits:          source.limits,
	}
	reader, err := source.raster.NewRGBReader(context.Background(), &opts)
	if err != nil {
		return nil, jxrImageError(err)
	}
	source.rgbReader = reader
	return reader, nil
}

// sampleRow4 复用对象池行缓冲经指定行读取函数提取单像素三通道与透明度
// 入参: read 行读取回调, x, y 像素坐标, components 至少三通道输出缓冲
// 返回: float64 有限且归一化的透明度, error 读取或非有限数值错误
func (source *jxrImage) sampleRow4(read func(context.Context, int, []float64) error, x, y int, components []float64) (float64, error) {
	need := source.bounds.Dx() * 4
	var holder *[]float64
	if pooled, ok := source.rowPool.Get().(*[]float64); ok && pooled != nil && cap(*pooled) >= need {
		holder = pooled
		*holder = (*holder)[:need]
	} else {
		buf := make([]float64, need)
		holder = &buf
	}
	row := *holder
	err := read(context.Background(), y, row)
	if err != nil {
		source.rowPool.Put(holder)
		return 0, jxrImageError(err)
	}
	at := (x - source.bounds.Min.X) * 4
	r, g, b, alpha := row[at], row[at+1], row[at+2], row[at+3]
	source.rowPool.Put(holder)
	if !geometryFinite(alpha) {
		return 0, fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
	}
	if !geometryFinite(r, g, b) {
		return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
	}
	components[0], components[1], components[2] = r, g, b
	return colorClamp(alpha), nil
}

// sampleLinear 经缓存线性读取器按单行采样YCC或CICP线性scRGB颜色及透明度
// 入参: x, y 像素位置, components 至少三通道颜色缓冲区, key 线性读取配置键
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (source *jxrImage) sampleLinear(x, y int, components []float64, key jxrLinearKey) (float64, error) {
	reader, err := source.getLinearReader(key)
	if err != nil {
		return 0, err
	}
	return source.sampleRow4(reader.ReadRow, x, y, components)
}

// sampleRGB 经缓存设备RGB读取器按单行采样YCC解码后的非线性设备RGB颜色及透明度
// 入参: x, y 像素位置, components 至少三通道颜色缓冲区
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (source *jxrImage) sampleRGB(x, y int, components []float64) (float64, error) {
	reader, err := source.getRGBReader()
	if err != nil {
		return 0, err
	}
	return source.sampleRow4(reader.ReadRow, x, y, components)
}

// readRow4 经四分量行读取器批量读取整行颜色与透明度并原地校验有限性及钳位透明度
// 入参: read 行读取回调, y 图像行坐标, buf 可复用行缓冲
// 返回: error 行读取或非有限数值错误
func (source *jxrImage) readRow4(read func(context.Context, int, []float64) error, y int, buf *jxrRowBuffer) error {
	width := source.bounds.Dx()
	need := width * 4
	if cap(buf.rgba) < need {
		buf.rgba = make([]float64, need)
	} else {
		buf.rgba = buf.rgba[:need]
	}
	if err := read(context.Background(), y, buf.rgba); err != nil {
		return jxrImageError(err)
	}
	for x := range width {
		at := x * 4
		r, g, b, alpha := buf.rgba[at], buf.rgba[at+1], buf.rgba[at+2], buf.rgba[at+3]
		if !geometryFinite(alpha) {
			return fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
		}
		if !geometryFinite(r, g, b) {
			return fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
		}
		buf.rgba[at+3] = colorClamp(alpha)
	}
	return nil
}

// sample 忠实读取源空间原生分量并展开预乘，子采样YCC按源相位上采样，不套用ICC或显示颜色转换
// 入参: x, y 像素位置, components 颜色分量缓冲区
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (source *jxrImage) sample(x, y int, components []float64) (float64, error) {
	alpha := 1.0
	if source.alpha {
		var value float64
		var err error
		if source.ycc {
			value, err = jxrSampleComponent(source.components[source.channels], x, y, source.bounds)
		} else {
			value, err = source.components[source.channels].Sample(x, y)
			if err != nil {
				err = jxrImageError(err)
			}
		}
		if err != nil {
			return 0, err
		}
		if !geometryFinite(value) {
			return 0, fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
		}
		alpha = colorClamp(value)
	}
	premultiplied := source.premultiplied && source.alpha
	if !premultiplied && source.linear && !source.ycc {
		for channel := range source.channels {
			value, err := source.components[channel].Sample(x, y)
			if err != nil {
				return 0, jxrImageError(err)
			}
			if !geometryFinite(value) {
				return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
			}
			components[channel] = value
		}
		return alpha, nil
	}
	for channel := range source.channels {
		comp := source.components[channel]
		var value float64
		var err error
		if source.ycc {
			value, err = jxrSampleComponent(comp, x, y, source.bounds)
		} else {
			value, err = comp.Sample(x, y)
			if err != nil {
				err = jxrImageError(err)
			}
		}
		if err != nil {
			return 0, err
		}
		preserveExtended := source.linear || comp.Info().Format != jxrgo.SampleUnsigned
		if premultiplied {
			value, err = jxrUnpremultiply(value, alpha, preserveExtended)
			if err != nil {
				return 0, err
			}
		} else if !geometryFinite(value) {
			return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
		}
		if !preserveExtended {
			value = math.Floor(colorClamp(value)*65535+0.5) / 65535
		}
		components[channel] = value
	}
	if !source.linear {
		alpha = math.Floor(alpha*65535+0.5) / 65535
	}
	return alpha, nil
}

// readRow 批量读取整行原生分量并执行非预乘展开与十六位舍入，结果与逐像素sample一致
// 入参: y 图像行坐标, buf 调用方独占的可复用行缓冲
// 返回: error 行读取或非有限颜色及透明度错误
func (source *jxrImage) readRow(y int, buf *jxrRowBuffer) error {
	width := source.bounds.Dx()
	for channel := range source.channels {
		if cap(buf.channels[channel]) < width {
			buf.channels[channel] = make([]float64, width)
		} else {
			buf.channels[channel] = buf.channels[channel][:width]
		}
	}
	if source.alpha {
		if cap(buf.alpha) < width {
			buf.alpha = make([]float64, width)
		} else {
			buf.alpha = buf.alpha[:width]
		}
		alphaRow := buf.alpha[:width]
		alphaComp := source.components[source.channels]
		alphaInfo := alphaComp.Info()
		if source.ycc && (alphaInfo.XStep != 1 || alphaInfo.YStep != 1 || alphaInfo.Bounds != source.bounds) {
			for x := range width {
				v, err := jxrSampleComponent(alphaComp, source.bounds.Min.X+x, y, source.bounds)
				if err != nil {
					return err
				}
				alphaRow[x] = v
			}
		} else if err := alphaComp.ReadRow(y, alphaRow); err != nil {
			return jxrImageError(err)
		}
		for x, value := range alphaRow {
			if !geometryFinite(value) {
				return fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
			}
			alphaRow[x] = colorClamp(value)
		}
	}
	premultiplied := source.premultiplied && source.alpha
	for channel := range source.channels {
		row := buf.channels[channel][:width]
		component := source.components[channel]
		info := component.Info()
		subsampled := source.ycc && (info.XStep != 1 || info.YStep != 1 || info.Bounds != source.bounds)
		preserveExtended := source.linear || info.Format != jxrgo.SampleUnsigned
		if !subsampled && !preserveExtended && !premultiplied && !info.Inverted && (info.Precision == 8 || info.Precision == 16) {
			if cap(buf.bits) < width {
				buf.bits = make([]uint32, width)
			}
			bitsRow := buf.bits[:width]
			if err := component.ReadRowBits(y, bitsRow); err != nil {
				return jxrImageError(err)
			}
			if info.Precision == 8 {
				for x, value := range bitsRow {
					if value > 255 {
						value = 255
					}
					row[x] = float64(value*257) / 65535
				}
			} else {
				for x, value := range bitsRow {
					if value > 65535 {
						value = 65535
					}
					row[x] = float64(value) / 65535
				}
			}
			continue
		}
		if subsampled {
			for x := range width {
				v, err := jxrSampleComponent(component, source.bounds.Min.X+x, y, source.bounds)
				if err != nil {
					return err
				}
				row[x] = v
			}
		} else if err := component.ReadRow(y, row); err != nil {
			return jxrImageError(err)
		}
		if premultiplied {
			alphaRow := buf.alpha[:width]
			if preserveExtended {
				for x, value := range row {
					unpremultiplied, err := jxrUnpremultiply(value, alphaRow[x], true)
					if err != nil {
						return err
					}
					row[x] = unpremultiplied
				}
			} else {
				for x, value := range row {
					unpremultiplied, err := jxrUnpremultiply(value, alphaRow[x], false)
					if err != nil {
						return err
					}
					row[x] = math.Floor(colorClamp(unpremultiplied)*65535+0.5) / 65535
				}
			}
		} else if preserveExtended {
			for _, value := range row {
				if !geometryFinite(value) {
					return fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
				}
			}
		} else {
			for x, value := range row {
				if !geometryFinite(value) {
					return fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
				}
				row[x] = math.Floor(colorClamp(value)*65535+0.5) / 65535
			}
		}
	}
	if source.alpha && !source.linear {
		alphaRow := buf.alpha[:width]
		for x, value := range alphaRow {
			alphaRow[x] = math.Floor(value*65535+0.5) / 65535
		}
	}
	return nil
}

// jxrRowCacheBytes 计算单个JPEG XR两行滑动缓存所需字节数，供受控内存预算判定使用
// 入参: source 只读JPEG XR视图, mode 采样模式
// 返回: uint64 两行滑动缓存估算字节数
func jxrRowCacheBytes(source *jxrImage, mode jxrSampleMode) uint64 {
	width := source.bounds.Dx()
	if width <= 0 {
		return 0
	}
	if mode != jxrSampleNative {
		return uint64(width) * 4 * 8 * 2
	}
	planes := uint64(source.channels)
	if source.alpha {
		planes++
	}
	return uint64(width) * (planes*8 + 4) * 2
}

// sample 优先从两行滑动缓存返回整行批量读取的结果，支持原生、设备域RGB及线性scRGB三种模式
// 入参: source 只读JPEG XR视图, x, y 像素坐标, components 输出颜色分量缓冲区, mode 采样模式, key 线性读取配置键
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (cache *jxrRowCache) sample(source *jxrImage, x, y int, components []float64, mode jxrSampleMode, key jxrLinearKey) (float64, error) {
	needBytes := jxrRowCacheBytes(source, mode)
	limit := uint64(jxrRowCacheMaxBytes)
	if source.limits.MaxMemoryBytes > 0 && source.limits.MaxMemoryBytes < limit {
		limit = source.limits.MaxMemoryBytes
	}
	if cache == nil || needBytes == 0 || needBytes > limit || x < source.bounds.Min.X || x >= source.bounds.Max.X || y < source.bounds.Min.Y || y >= source.bounds.Max.Y {
		switch mode {
		case jxrSampleLinear:
			return source.sampleLinear(x, y, components, key)
		case jxrSampleRGB:
			return source.sampleRGB(x, y, components)
		default:
			return source.sample(x, y, components)
		}
	}
	if cache.source != source || cache.mode != mode || mode == jxrSampleLinear && cache.key != key {
		cache.source = source
		cache.mode = mode
		cache.key = key
		cache.linearReader = nil
		cache.rgbReader = nil
		cache.valid = [2]bool{}
	}
	slot := y & 1
	if !cache.valid[slot] || cache.ys[slot] != y {
		switch mode {
		case jxrSampleLinear:
			if cache.linearReader == nil {
				reader, err := source.getLinearReader(key)
				if err != nil {
					return 0, err
				}
				cache.linearReader = reader
			}
			if err := source.readRow4(cache.linearReader.ReadRow, y, &cache.rows[slot]); err != nil {
				return 0, err
			}
		case jxrSampleRGB:
			if cache.rgbReader == nil {
				reader, err := source.getRGBReader()
				if err != nil {
					return 0, err
				}
				cache.rgbReader = reader
			}
			if err := source.readRow4(cache.rgbReader.ReadRow, y, &cache.rows[slot]); err != nil {
				return 0, err
			}
		default:
			if err := source.readRow(y, &cache.rows[slot]); err != nil {
				return 0, err
			}
		}
		cache.ys[slot] = y
		cache.valid[slot] = true
	}
	col := x - source.bounds.Min.X
	row := &cache.rows[slot]
	if mode != jxrSampleNative {
		at := col * 4
		components[0], components[1], components[2] = row.rgba[at], row.rgba[at+1], row.rgba[at+2]
		return row.rgba[at+3], nil
	}
	for channel := range source.channels {
		components[channel] = row.channels[channel][col]
	}
	if !source.alpha {
		return 1, nil
	}
	return row.alpha[col], nil
}

// jxrImageError 将独立编解码器错误映射到文档引擎分类，保留原始原因及取消错误
// 入参: err 独立解码错误
// 返回: error 文档层错误
func jxrImageError(err error) error {
	var category error
	switch {
	case errors.Is(err, jxrgo.ErrInvalid):
		category = ErrInvalid
	case errors.Is(err, jxrgo.ErrUnsupported):
		category = ErrUnsupported
	case errors.Is(err, jxrgo.ErrLimit):
		category = ErrLimit
	default:
		return err
	}
	return fmt.Errorf("%w: JPEG XR: %w", category, err)
}
