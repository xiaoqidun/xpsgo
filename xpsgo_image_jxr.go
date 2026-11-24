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

	"github.com/xiaoqidun/jxrgo"
)

// jxrRowCacheMaxWidth 定义JPEG XR扫描行缓存支持的最大宽度
const jxrRowCacheMaxWidth = 4096

// jxrImage 保存独立解码图像的原生通道视图，取样时处理非预乘，不复制整幅像素
type jxrImage struct {
	bounds        image.Rectangle
	components    [9]jxrgo.Component
	channels      int
	alpha         bool
	premultiplied bool
	linear        bool
	units         uint64
}

// jxrRowBuffer 保存JPEG XR单行批量读取的可复用通道与位模式缓冲
type jxrRowBuffer struct {
	channels [8][]float64
	alpha    []float64
	bits     []uint32
}

// jxrRowCache 保存单工作Goroutine独占的两行滑动行缓存，避免双线性采样重复逐像素读取
type jxrRowCache struct {
	source *jxrImage
	rows   [2]jxrRowBuffer
	ys     [2]int
	valid  [2]bool
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

// decodeJXRImage 使用JXRGo重建原生分量，并结合调用方字节与像素预算推导工作内存上限
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
	info := decoder.Info()
	if info.Format != jxrgo.FormatJXR {
		return nil, fmt.Errorf("%w: JPEG XR requires a file container", ErrInvalid)
	}
	stride := info.Channels
	if info.Alpha {
		stride++
	}
	if info.Channels < 1 || info.Channels > 8 || len(info.Components) != stride {
		return nil, fmt.Errorf("%w: JPEG XR component count", ErrUnsupported)
	}
	switch info.ColorSpace {
	case jxrgo.ColorGray, jxrgo.ColorRGB, jxrgo.ColorCMYK, jxrgo.ColorCMYKDirect, jxrgo.ColorMultiChannel:
	default:
		return nil, fmt.Errorf("%w: JPEG XR document color interpretation", ErrUnsupported)
	}
	storage := 0
	for _, component := range info.Components {
		if component.Bounds != info.Bounds || component.XStep != 1 || component.YStep != 1 {
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
	raster, err := decoder.Decode(ctx)
	if err != nil {
		return nil, jxrImageError(err)
	}
	_ = decoder.Close()
	premultiplied := info.Premultiplied && info.Alpha
	view := &jxrImage{bounds: info.Bounds, channels: info.Channels, alpha: info.Alpha, premultiplied: premultiplied, linear: info.Linear, units: units}
	for index := range stride {
		component, err := raster.Component(index)
		if err != nil {
			return nil, jxrImageError(err)
		}
		view.components[index] = component
	}
	if view.alpha && view.linear {
		if err := validateJXRLinearAlpha(ctx, view.components[view.channels], info.Bounds); err != nil {
			return nil, err
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return &rasterImage{jxr: view, dpi: Point{info.Resolution.X, info.Resolution.Y}, channels: info.Channels, profile: info.ICCProfile, linear: info.Linear, multiChannel: info.ColorSpace == jxrgo.ColorMultiChannel}, nil
}

// validateJXRLinearAlpha 批量校验线性透明度分量的有限性，浮点通道使用位模式行读取避免逐像素转换
// 入参: ctx 取消Context, component 透明度分量视图, bounds 图像范围
// 返回: error 取消、读取或非有限透明度错误
func validateJXRLinearAlpha(ctx context.Context, component jxrgo.Component, bounds image.Rectangle) error {
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
			for y := range bounds.Dy() {
				if err := checkContext(ctx); err != nil {
					return err
				}
				if err := component.ReadRowBits(y, row); err != nil {
					return jxrImageError(err)
				}
				for _, bits := range row {
					if bits&mask == mask {
						return fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
					}
				}
			}
			return nil
		}
	}
	row := make([]float64, bounds.Dx())
	for y := range bounds.Dy() {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if err := component.ReadRow(y, row); err != nil {
			return jxrImageError(err)
		}
		for _, alpha := range row {
			if !geometryFinite(alpha) {
				return fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
			}
		}
	}
	return nil
}

// jxrUnpremultiply 展开JPEG XR预乘颜色分量，线性空间保留扩展高光并统一拒绝非有限结果
// 入参: value 源颜色分量, alpha 已校验的单位区间透明度, linear 是否为线性颜色空间
// 返回: float64 非预乘颜色分量, error 非有限颜色错误
func jxrUnpremultiply(value, alpha float64, linear bool) (float64, error) {
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
	if linear {
		return unpremultiplied, nil
	}
	return colorClamp(unpremultiplied), nil
}

// sample 读取原生分量并展开预乘，非预乘线性颜色保留扩展范围，整数采用十六位取样
// 入参: x, y 像素位置, components 颜色分量缓冲区
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (source *jxrImage) sample(x, y int, components []float64) (float64, error) {
	alpha := 1.0
	if source.alpha {
		value, err := source.components[source.channels].Sample(x, y)
		if err != nil {
			return 0, jxrImageError(err)
		}
		if !geometryFinite(value) {
			return 0, fmt.Errorf("%w: JPEG XR non-finite alpha", ErrUnsupported)
		}
		alpha = colorClamp(value)
	}
	premultiplied := source.premultiplied && source.alpha
	if !premultiplied && source.linear {
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
		value, err := source.components[channel].Sample(x, y)
		if err != nil {
			return 0, jxrImageError(err)
		}
		if premultiplied {
			value, err = jxrUnpremultiply(value, alpha, source.linear)
			if err != nil {
				return 0, err
			}
		} else if !geometryFinite(value) {
			return 0, fmt.Errorf("%w: JPEG XR non-finite color", ErrUnsupported)
		}
		if !source.linear {
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
		if err := source.components[source.channels].ReadRow(y, alphaRow); err != nil {
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
		if !source.linear && !premultiplied && info.Format == jxrgo.SampleUnsigned && !info.Inverted && (info.Precision == 8 || info.Precision == 16) {
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
		if err := component.ReadRow(y, row); err != nil {
			return jxrImageError(err)
		}
		if premultiplied {
			alphaRow := buf.alpha[:width]
			if source.linear {
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
		} else if source.linear {
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

// sample 优先从两行滑动缓存返回整行批量读取的结果，超宽或越界时回退单像素取样
// 入参: source 只读JPEG XR视图, x, y 像素坐标, components 输出颜色分量缓冲区
// 返回: float64 有限且归一化的透明度, error 取样或数值错误
func (cache *jxrRowCache) sample(source *jxrImage, x, y int, components []float64) (float64, error) {
	width := source.bounds.Dx()
	if cache == nil || width <= 0 || width > jxrRowCacheMaxWidth || x < source.bounds.Min.X || x >= source.bounds.Max.X || y < source.bounds.Min.Y || y >= source.bounds.Max.Y {
		return source.sample(x, y, components)
	}
	if cache.source != source {
		cache.source = source
		cache.valid = [2]bool{}
	}
	slot := y & 1
	if !cache.valid[slot] || cache.ys[slot] != y {
		if err := source.readRow(y, &cache.rows[slot]); err != nil {
			return 0, err
		}
		cache.ys[slot] = y
		cache.valid[slot] = true
	}
	col := x - source.bounds.Min.X
	row := &cache.rows[slot]
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
