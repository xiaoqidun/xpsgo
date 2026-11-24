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
	"compress/zlib"
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"hash/crc32"
	"image"
	"image/color"
	"image/jpeg"
	"image/png"
	"io"
	"maps"
	"slices"
	"strings"
)

// rasterImage 保存图像原生分量、颜色解释及物理分辨率
type rasterImage struct {
	pixels            image.Image
	native            *imageComponents
	jxr               *jxrImage
	dpi               Point
	channels          int
	profile           []byte
	profileCompressed bool
	transform         *iccTransform
	selectedProfile   *iccProfile
	associatedProfile bool
	linear            bool
	multiChannel      bool
}

// sceneImageCache 按包内部件身份复用本次绘制的图像，并限制解压字节及解码像素
type sceneImageCache struct {
	pkg        *packageReader
	images     map[string]*rasterImage
	bytes      int64
	pixels     uint64
	maxImages  int
	colors     *sceneColorCache
	context    context.Context
	format     Format
	deferColor bool
}

// imageComponents 保存非预乘设备分量，整数保留十六位精度，浮点保留扩展范围
type imageComponents struct {
	bounds   image.Rectangle
	channels int
	alpha    bool
	values   []uint16
	floating []float64
}

// ImageOptions 设置图像读取的字节及解码容量上限，零值采用默认值
// MaxPixels按RGBA64存储容量计费，多通道及浮点图像采用解码器的容量折算
type ImageOptions struct {
	MaxBytes  int64
	MaxPixels uint64
}

// ImageResource 保存原始图像部件、解码样本及未应用的内嵌ICC，不以显示转换替代源数据
// Data和Profile独立拥有字节；Profile为解压后的ICC，未内嵌时为空
// Resolution单位为DPI，图像元数据未声明物理分辨率时缺省为96
type ImageResource struct {
	Part        string
	ContentType string
	Resolution  Point
	Data        []byte
	Profile     []byte
	source      *rasterImage
}

// rasterMetadata 保存图像分辨率、原生通道数及内嵌配置文件
type rasterMetadata struct {
	dpi               Point
	channels          int
	profile           []byte
	profileCompressed bool
	jpegProcess       byte
}

// pngCompressionLayout 保存连续IDAT块的物理范围，范围内只包含图像压缩流及块封装
type pngCompressionLayout struct {
	start int
	end   int
}

// pngCompressionSink 保存有界压缩候选，容量不足后继续接收但不保存，便于完整校验原压缩流
type pngCompressionSink struct {
	buffer compressionBuffer
	full   bool
}

// pngCompressedReader 顺序读取已校验的连续IDAT载荷，不合并分配原压缩数据或吞掉zlib末尾字节
type pngCompressedReader struct {
	data  []byte
	start int
	end   int
	next  int
	limit int
}

// losslessHuffman 保存无损JPEG差值类别的规范码区间及符号视图
type losslessHuffman struct {
	first   [16]uint32
	count   [16]uint32
	index   [16]int
	symbols []byte
}

// losslessBits 保存JPEG字节填充、剩余位及标记读取状态
type losslessBits struct {
	data []byte
	pos  int
	word uint32
	left uint
}

// load 根据画刷定义位置解析图像资源，不以文件扩展名选择解码器
// 入参: brush 图像画刷
// 返回: *rasterImage 已解码图像, error 部件、解码、颜色或资源错误
func (c *sceneImageCache) load(brush *Brush) (*rasterImage, error) {
	part, err := resolvePart(brush.Part, brush.ImageSource)
	if err != nil {
		return nil, err
	}
	key := strings.ToLower(part)
	if value := c.images[key]; value != nil {
		return c.colorImage(brush, part, value)
	}
	if len(c.images) >= c.maxImages {
		return nil, fmt.Errorf("%w: render image count", ErrLimit)
	}
	size, err := c.pkg.partSize(key)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if c.bytes < 0 || size > uint64(c.bytes) {
		return nil, &PartError{Part: part, Err: fmt.Errorf("%w: render image byte budget", ErrLimit)}
	}
	media, err := c.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	data, err := c.pkg.readPart(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	decoded, err := decodeRasterImageWithMemory(normalizeContext(c.context), data, media, c.pixels, uint64(c.bytes))
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	c.bytes -= int64(len(data))
	c.pixels -= decoded.pixelUnits()
	c.images[key] = decoded
	return c.colorImage(brush, part, decoded)
}

// decodeRasterImageContext 检查取消状态并按内容类型解码，JPEG XR各解码阶段使用同一Context
// 入参: ctx 取消Context, data 图像字节, media 声明内容类型, maxPixels 剩余RGBA64容量
// 返回: *rasterImage 原生图像, error 数据、能力、资源或取消错误
func decodeRasterImageContext(ctx context.Context, data []byte, media string, maxPixels uint64) (*rasterImage, error) {
	return decodeRasterImageWithMemory(ctx, data, media, maxPixels, 0)
}

// decodeRasterImageWithMemory 检查取消状态并按内容类型解码，同时向JPEG XR传递字节上限预算
// 入参: ctx 取消Context, data 图像字节, media 声明内容类型, maxPixels 剩余RGBA64容量, maxBytes 图像字节上限
// 返回: *rasterImage 原生图像, error 数据、能力、资源或取消错误
func decodeRasterImageWithMemory(ctx context.Context, data []byte, media string, maxPixels, maxBytes uint64) (*rasterImage, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	var config image.Config
	var metadata rasterMetadata
	var err error
	switch strings.ToLower(media) {
	case "image/png":
		metadata, err = pngImageMetadata(data)
		if err == nil {
			config, err = png.DecodeConfig(bytes.NewReader(data))
		}
	case "image/jpeg":
		metadata, err = jpegImageMetadata(data, 64<<20)
		if err == nil && metadata.jpegProcess == 0xc3 {
			return decodeLosslessJPEGImage(data, metadata, maxPixels)
		}
		if err == nil {
			config, err = jpeg.DecodeConfig(bytes.NewReader(data))
		}
	case "image/tiff":
		return decodeTIFFImage(data, maxPixels)
	case "image/vnd.ms-photo":
		return decodeJXRImage(ctx, data, maxPixels, maxBytes)
	default:
		return nil, fmt.Errorf("%w: unexpected image content type %q", ErrInvalid, media)
	}
	if err != nil {
		return nil, rasterImageDecodeError(err)
	}
	if config.Width <= 0 || config.Height <= 0 {
		return nil, fmt.Errorf("%w: empty image", ErrInvalid)
	}
	count := uint64(config.Width) * uint64(config.Height)
	if config.Width > rasterMaxDimension || config.Height > rasterMaxDimension || count > maxPixels || count > uint64(^uint(0)>>1)/8 {
		return nil, fmt.Errorf("%w: decoded image pixels", ErrLimit)
	}
	var decoded image.Image
	if strings.EqualFold(media, "image/png") {
		decoded, err = png.Decode(bytes.NewReader(data))
	} else {
		decoded, err = jpeg.Decode(bytes.NewReader(data))
	}
	if err != nil {
		return nil, rasterImageDecodeError(err)
	}
	if decoded.Bounds() != image.Rect(0, 0, config.Width, config.Height) {
		return nil, fmt.Errorf("%w: inconsistent decoded image dimensions", ErrInvalid)
	}
	return &rasterImage{pixels: decoded, dpi: metadata.dpi, channels: metadata.channels, profile: metadata.profile, profileCompressed: metadata.profileCompressed}, nil
}

// rasterImageDecodeError 保留资源和能力错误，不将标准解码器的能力缺失误判为无效图像
// 入参: err 图像读取错误
// 返回: error 带数据、能力或资源分类的错误
func rasterImageDecodeError(err error) error {
	if errors.Is(err, ErrInvalid) || errors.Is(err, ErrUnsupported) || errors.Is(err, ErrLimit) {
		return err
	}
	var unsupported jpeg.UnsupportedError
	if errors.As(err, &unsupported) {
		return fmt.Errorf("%w: image decode: %w", ErrUnsupported, err)
	}
	return fmt.Errorf("%w: image decode: %w", ErrInvalid, err)
}

// newImageComponents 检查设备通道和存储预算后分配连续样本，预算按RGBA64容量折算
// 入参: bounds 图像范围, channels 颜色通道数, alpha 是否包含透明度, maxPixels 剩余RGBA64像素容量
// 返回: *imageComponents 原生分量图像, error 结构或资源错误
func newImageComponents(bounds image.Rectangle, channels int, alpha bool, maxPixels uint64) (*imageComponents, error) {
	if bounds.Empty() || bounds.Min.X != 0 || bounds.Min.Y != 0 || channels < 1 || channels > 8 {
		return nil, fmt.Errorf("%w: image component layout", ErrInvalid)
	}
	stride := channels
	if alpha {
		stride++
	}
	count := uint64(bounds.Dx()) * uint64(bounds.Dy())
	units := uint64((stride + 3) / 4)
	if bounds.Dx() > rasterMaxDimension || bounds.Dy() > rasterMaxDimension || count > maxPixels/units || count > uint64(^uint(0)>>1)/uint64(2*stride) {
		return nil, fmt.Errorf("%w: image component storage", ErrLimit)
	}
	return &imageComponents{bounds: bounds, channels: channels, alpha: alpha, values: make([]uint16, int(count)*stride)}, nil
}

// bounds 取得标准图像或设备分量图像的范围，不构造虚假的RGB像素
// 返回: image.Rectangle 源图像范围，缺少图像时为空
func (source *rasterImage) bounds() image.Rectangle {
	if source.jxr != nil {
		return source.jxr.bounds
	}
	if source.native != nil {
		return source.native.bounds
	}
	if source.pixels != nil {
		return source.pixels.Bounds()
	}
	return image.Rectangle{}
}

// pixelUnits 计算图像占用的RGBA64容量，向上折算多通道及透明度存储
// 返回: uint64 本次绘制的解码容量计费
func (source *rasterImage) pixelUnits() uint64 {
	bounds := source.bounds()
	units := uint64(bounds.Dx()) * uint64(bounds.Dy())
	if source.jxr != nil {
		return units * source.jxr.units
	}
	if source.native != nil {
		stride := source.native.channels
		if source.native.alpha {
			stride++
		}
		if source.native.floating != nil {
			units *= uint64(stride)
		} else {
			units *= uint64((stride + 3) / 4)
		}
	}
	return units
}

// imageSourcePixel 直接读取标准解码图像的非预乘十六位颜色，常见图像不经Interface装箱分配临时对象
// 入参: pixels 已解码图像, x 有效横坐标, y 有效纵坐标
// 返回: color.NRGBA64 未应用ICC的解码颜色
func imageSourcePixel(pixels image.Image, x, y int) color.NRGBA64 {
	switch pixels := pixels.(type) {
	case *image.NRGBA64:
		return pixels.NRGBA64At(x, y)
	case *image.NRGBA:
		value := pixels.NRGBAAt(x, y)
		return color.NRGBA64{R: uint16(value.R) * 257, G: uint16(value.G) * 257, B: uint16(value.B) * 257, A: uint16(value.A) * 257}
	case *image.Gray16:
		value := pixels.Gray16At(x, y).Y
		return color.NRGBA64{R: value, G: value, B: value, A: 65535}
	case *image.Gray:
		value := uint16(pixels.GrayAt(x, y).Y) * 257
		return color.NRGBA64{R: value, G: value, B: value, A: 65535}
	case *image.YCbCr:
		value := pixels.YCbCrAt(x, y)
		r, g, b, _ := value.RGBA()
		return color.NRGBA64{R: uint16(r), G: uint16(g), B: uint16(b), A: 65535}
	case *image.NYCbCrA:
		value := pixels.NYCbCrAAt(x, y)
		r, g, b, _ := value.YCbCr.RGBA()
		return color.NRGBA64{R: uint16(r), G: uint16(g), B: uint16(b), A: uint16(value.A) * 257}
	case *image.RGBA64:
		value := pixels.RGBA64At(x, y)
		return imageUnassociatedPixel(uint32(value.R), uint32(value.G), uint32(value.B), uint32(value.A))
	case *image.RGBA:
		value := pixels.RGBAAt(x, y)
		return imageUnassociatedPixel(uint32(value.R)*257, uint32(value.G)*257, uint32(value.B)*257, uint32(value.A)*257)
	default:
		return imageSourceColor(pixels.At(x, y))
	}
}

// imageSourceColor 保留已有非预乘颜色的隐藏分量，其他标准颜色按RGBA约定展开
// 入参: value 已解码颜色
// 返回: color.NRGBA64 十六位非预乘颜色
func imageSourceColor(value color.Color) color.NRGBA64 {
	switch value := value.(type) {
	case color.NRGBA64:
		return value
	case color.NRGBA:
		return color.NRGBA64{R: uint16(value.R) * 257, G: uint16(value.G) * 257, B: uint16(value.B) * 257, A: uint16(value.A) * 257}
	default:
		r, g, b, a := value.RGBA()
		return imageUnassociatedPixel(r, g, b, a)
	}
}

// imageUnassociatedPixel 按标准库颜色约定展开预乘分量，保持十六位整数除法的舍入规则
// 入参: r 预乘红分量, g 预乘绿分量, b 预乘蓝分量, a 透明度，均不超过65535
// 返回: color.NRGBA64 非预乘颜色
func imageUnassociatedPixel(r, g, b, a uint32) color.NRGBA64 {
	if a == 0 {
		return color.NRGBA64{}
	}
	if a != 65535 {
		r, g, b = r*65535/a, g*65535/a, b*65535/a
	}
	return color.NRGBA64{R: uint16(r), G: uint16(g), B: uint16(b), A: uint16(a)}
}

// DefaultImageOptions 返回图像读取的默认字节上限及解码容量
// 返回: ImageOptions 默认参数
func DefaultImageOptions() ImageOptions {
	return ImageOptions{MaxBytes: DefaultLimits().MaxPartBytes, MaxPixels: 1 << 24}
}

// Image 读取指定包内图像部件并保留源样本与内嵌ICC，不应用关联ICC颜色转换
// 读取和解码边界检查ctx取消信号及options字节与像素容量上限
// 入参: ctx 取消Context，nil采用Background, part 图像部件的包根URI, options 图像参数，nil采用默认值
// 返回: *ImageResource 独立图像数据, error 输入、解码、资源或取消错误
func (r *Reader) Image(ctx context.Context, part string, options *ImageOptions) (*ImageResource, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readImage(ctx, part, options)
}

// readImage 在调用方持有读锁时加载独立图像，供图像与缩略图读取共用预算及解码路径
// 入参: ctx 已规范化取消Context, part 图像部件名, options 字节及像素参数
// 返回: *ImageResource 独立图像, error 引用、解码或资源错误
func (r *Reader) readImage(ctx context.Context, part string, options *ImageOptions) (*ImageResource, error) {
	configuration := DefaultImageOptions()
	if options != nil {
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxPixels != 0 {
			configuration.MaxPixels = options.MaxPixels
		}
	}
	if configuration.MaxBytes < 1 {
		return nil, fmt.Errorf("%w: image byte limit", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	part, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	media, err := r.pkg.contentType(part)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	data, err := r.pkg.readItems(strings.ToLower(part), min(configuration.MaxBytes, r.limits.MaxPartBytes))
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	source, err := decodeRasterImageWithMemory(ctx, data, media, configuration.MaxPixels, uint64(configuration.MaxBytes))
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	profile := source.profile
	if source.profileCompressed {
		profile, err = inflatePNGProfile(profile, configuration.MaxBytes-int64(len(data)))
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
	} else {
		profile = bytes.Clone(profile)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return &ImageResource{Part: part, ContentType: media, Resolution: source.dpi, Data: data, Profile: profile, source: source}, nil
}

// Bounds 返回解码图像的像素范围，空资源返回空范围
// 返回: image.Rectangle 像素范围
func (r *ImageResource) Bounds() image.Rectangle {
	if r == nil || r.source == nil {
		return image.Rectangle{}
	}
	return r.source.bounds()
}

// Channels 返回源颜色通道数，不含透明度通道，空资源返回零
// 返回: int 颜色通道数
func (r *ImageResource) Channels() int {
	if r == nil || r.source == nil {
		return 0
	}
	return imageColorChannels(r.source)
}

// Linear 报告解码样本是否采用线性色值，不对设备颜色或ICC作假定
// 返回: bool 是否为线性色值
func (r *ImageResource) Linear() bool {
	return r != nil && r.source != nil && r.source.linear
}

// MultiChannel 报告源图像是否属于N色通道，不将通道数恰为三或四的N色图像误作RGB或CMYK
// 返回: bool 是否为N色图像
func (r *ImageResource) MultiChannel() bool {
	return r != nil && r.source != nil && r.source.multiChannel
}

// Pixels 返回已有标准图像表示，不转换原生多通道或浮点样本，也不应用ICC
// 返回图像归属当前资源独占，修改其可变像素会影响后续Sample结果
// 返回: image.Image 解码图像, error 需经Sample读取原生分量时返回ErrUnsupported
func (r *ImageResource) Pixels() (image.Image, error) {
	if r == nil || r.source == nil {
		return nil, fmt.Errorf("%w: empty image resource", ErrInvalid)
	}
	if r.source.pixels == nil {
		return nil, fmt.Errorf("%w: image requires native component access", ErrUnsupported)
	}
	return r.source.pixels, nil
}

// Sample 将解码后的非预乘源颜色分量写入调用方缓冲区，不进行ICC或RGB显示转换
// 整数分量归一到0至1，浮点分量保留扩展范围；多出的缓冲区位置保持不变
// 入参: x 像素横坐标, y 像素纵坐标, components 至少容纳Channels个分量的缓冲区
// 返回: float64 透明度，未含透明度时为1, error 空资源、越界或缓冲区错误
func (r *ImageResource) Sample(x, y int, components []float64) (float64, error) {
	if r == nil || r.source == nil || !image.Pt(x, y).In(r.Bounds()) || len(components) < r.Channels() {
		return 0, fmt.Errorf("%w: image sample coordinates or buffer", ErrInvalid)
	}
	source := r.source
	if source.jxr != nil {
		return source.jxr.sample(x, y, components)
	}
	if native := source.native; native != nil {
		stride := native.channels
		if native.alpha {
			stride++
		}
		start := ((y-native.bounds.Min.Y)*native.bounds.Dx() + x - native.bounds.Min.X) * stride
		alpha := 1.0
		if native.floating != nil {
			copy(components, native.floating[start:start+native.channels])
			if native.alpha {
				alpha = native.floating[start+native.channels]
			}
		} else {
			for channel, value := range native.values[start : start+native.channels] {
				components[channel] = float64(value) / 65535
			}
			if native.alpha {
				alpha = float64(native.values[start+native.channels]) / 65535
			}
		}
		return alpha, nil
	}
	if pixels, ok := source.pixels.(*image.CMYK); ok {
		value := pixels.CMYKAt(x, y)
		components[0], components[1], components[2], components[3] = float64(value.C)/255, float64(value.M)/255, float64(value.Y)/255, float64(value.K)/255
		return 1, nil
	}
	value := imageSourcePixel(source.pixels, x, y)
	components[0] = float64(value.R) / 65535
	if r.Channels() == 3 {
		components[1], components[2] = float64(value.G)/65535, float64(value.B)/65535
	}
	return float64(value.A) / 65535, nil
}

// pngImageMetadata 读取分辨率和内嵌配置文件，不应用XPS要求忽略的颜色提示块
// 入参: data 完整PNG数据
// 返回: rasterMetadata 图像元数据, error 数据或资源错误
func pngImageMetadata(data []byte) (rasterMetadata, error) {
	metadata := rasterMetadata{dpi: Point{96, 96}}
	if !bytes.HasPrefix(data, []byte("\x89PNG\r\n\x1a\n")) {
		return rasterMetadata{}, fmt.Errorf("%w: PNG signature", ErrInvalid)
	}
	seen := false
	profileSeen, srgbSeen, imageSeen := false, false, false
	for pos := uint64(8); pos < uint64(len(data)); {
		if uint64(len(data))-pos < 12 {
			return rasterMetadata{}, fmt.Errorf("%w: truncated PNG chunk", ErrInvalid)
		}
		size := uint64(binary.BigEndian.Uint32(data[pos:]))
		if size > uint64(len(data))-pos-12 {
			return rasterMetadata{}, fmt.Errorf("%w: PNG chunk size", ErrInvalid)
		}
		chunk := data[pos+4 : pos+8+size]
		if crc32.ChecksumIEEE(chunk) != binary.BigEndian.Uint32(data[pos+8+size:]) {
			return rasterMetadata{}, fmt.Errorf("%w: PNG chunk checksum", ErrInvalid)
		}
		switch string(chunk[:4]) {
		case "IHDR":
			if pos != 8 || size != 13 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG header placement", ErrInvalid)
			}
			metadata.channels = 3
			if chunk[13] == 0 || chunk[13] == 4 {
				metadata.channels = 1
			}
		case "IDAT":
			imageSeen = true
		case "pHYs":
			if seen || size != 9 || chunk[12] > 1 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG physical dimensions", ErrInvalid)
			}
			seen = true
			if chunk[12] == 1 {
				x, y := binary.BigEndian.Uint32(chunk[4:]), binary.BigEndian.Uint32(chunk[8:])
				if x == 0 || y == 0 {
					return rasterMetadata{}, fmt.Errorf("%w: zero PNG resolution", ErrInvalid)
				}
				metadata.dpi = Point{float64(x) * 0.0254, float64(y) * 0.0254}
			}
		case "iCCP":
			if profileSeen || srgbSeen || imageSeen {
				return rasterMetadata{}, fmt.Errorf("%w: PNG profile placement", ErrInvalid)
			}
			profileSeen = true
			profile, err := pngICCStream(chunk[4:])
			if err != nil {
				return rasterMetadata{}, err
			}
			metadata.profile = profile
			metadata.profileCompressed = true
		case "sRGB":
			if profileSeen || srgbSeen || imageSeen || size != 1 || chunk[4] > 3 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG sRGB chunk", ErrInvalid)
			}
			srgbSeen = true
		case "IEND":
			if size != 0 || pos+12 != uint64(len(data)) {
				return rasterMetadata{}, fmt.Errorf("%w: PNG ending", ErrInvalid)
			}
			return metadata, nil
		}
		pos += size + 12
	}
	return rasterMetadata{}, fmt.Errorf("%w: missing PNG ending", ErrInvalid)
}

// jpegImageMetadata 按EXIF优先于JFIF解析分辨率，并按片段序号合并内嵌ICC配置文件
// 入参: data 完整JPEG数据, maxProfileBytes 配置文件字节上限
// 返回: rasterMetadata 图像元数据, error 标记、元数据或资源错误
func jpegImageMetadata(data []byte, maxProfileBytes int64) (rasterMetadata, error) {
	if !bytes.HasPrefix(data, []byte{0xff, 0xd8}) {
		return rasterMetadata{}, fmt.Errorf("%w: JPEG signature", ErrInvalid)
	}
	metadata := rasterMetadata{dpi: Point{96, 96}}
	var exif Point
	hasExif := false
	var profiles [256][]byte
	profileCount, profileSize := 0, int64(0)
	entropy := false
	for pos := 2; pos < len(data); {
		if data[pos] != 0xff {
			if !entropy {
				return rasterMetadata{}, fmt.Errorf("%w: JPEG marker", ErrInvalid)
			}
			pos++
			continue
		}
		for pos < len(data) && data[pos] == 0xff {
			pos++
		}
		if pos == len(data) {
			break
		}
		marker := data[pos]
		pos++
		if entropy && (marker == 0 || marker >= 0xd0 && marker <= 0xd7) {
			continue
		}
		entropy = false
		if marker == 0xd9 {
			if hasExif {
				metadata.dpi = exif
			}
			if profileCount != 0 {
				for i := 1; i <= profileCount; i++ {
					if profiles[i] == nil {
						return rasterMetadata{}, fmt.Errorf("%w: missing JPEG ICC fragment", ErrInvalid)
					}
				}
				metadata.profile = make([]byte, 0, int(profileSize))
				for i := 1; i <= profileCount; i++ {
					metadata.profile = append(metadata.profile, profiles[i]...)
				}
			}
			return metadata, nil
		}
		if marker == 1 {
			continue
		}
		if len(data)-pos < 2 {
			break
		}
		size := int(binary.BigEndian.Uint16(data[pos:]))
		if size < 2 || size > len(data)-pos {
			return rasterMetadata{}, fmt.Errorf("%w: JPEG marker length", ErrInvalid)
		}
		payload := data[pos+2 : pos+size]
		pos += size
		switch {
		case marker >= 0xc0 && marker <= 0xcf && marker != 0xc4 && marker != 0xc8 && marker != 0xcc:
			if len(payload) < 6 || metadata.channels != 0 {
				return rasterMetadata{}, fmt.Errorf("%w: JPEG frame metadata", ErrInvalid)
			}
			metadata.channels = int(payload[5])
			metadata.jpegProcess = marker
		case marker == 0xe0 && bytes.HasPrefix(payload, []byte("JFIF\x00")):
			if len(payload) < 14 {
				return rasterMetadata{}, fmt.Errorf("%w: truncated JFIF", ErrInvalid)
			}
			unit, x, y := payload[7], binary.BigEndian.Uint16(payload[8:]), binary.BigEndian.Uint16(payload[10:])
			if unit > 2 || x == 0 || y == 0 {
				return rasterMetadata{}, fmt.Errorf("%w: JFIF density", ErrInvalid)
			}
			if unit != 0 {
				factor := 1.0
				if unit == 2 {
					factor = 2.54
				}
				metadata.dpi = Point{float64(x) * factor, float64(y) * factor}
			}
		case marker == 0xe1 && bytes.HasPrefix(payload, []byte("Exif\x00\x00")):
			value, present, err := exifImageResolution(payload[6:])
			if err != nil {
				return rasterMetadata{}, err
			}
			if present {
				if hasExif && exif != value {
					return rasterMetadata{}, fmt.Errorf("%w: conflicting EXIF resolution", ErrInvalid)
				}
				exif, hasExif = value, true
			}
		case marker == 0xe2 && bytes.HasPrefix(payload, []byte("ICC_PROFILE\x00")):
			if len(payload) <= 14 {
				return rasterMetadata{}, fmt.Errorf("%w: JPEG ICC fragment header", ErrInvalid)
			}
			index, count := int(payload[12]), int(payload[13])
			if index == 0 || count == 0 || index > count || profiles[index] != nil || profileCount != 0 && profileCount != count {
				return rasterMetadata{}, fmt.Errorf("%w: JPEG ICC fragment sequence", ErrInvalid)
			}
			profileCount = count
			if maxProfileBytes < 0 || int64(len(payload)-14) > maxProfileBytes-profileSize {
				return rasterMetadata{}, fmt.Errorf("%w: JPEG ICC byte budget", ErrLimit)
			}
			profiles[index] = payload[14:]
			profileSize += int64(len(payload) - 14)
		}
		entropy = marker == 0xda
	}
	return rasterMetadata{}, fmt.Errorf("%w: truncated JPEG", ErrInvalid)
}

// exifImageResolution 从EXIF首个图像目录读取分辨率，忽略缩略图及显示方向提示
// 入参: data 去除EXIF前缀的TIFF数据
// 返回: Point 分辨率, bool 是否指定物理分辨率, error 目录或数值错误
func exifImageResolution(data []byte) (Point, bool, error) {
	invalid := fmt.Errorf("%w: EXIF resolution metadata", ErrInvalid)
	if len(data) < 8 {
		return Point{}, false, invalid
	}
	var order binary.ByteOrder
	switch string(data[:2]) {
	case "II":
		order = binary.LittleEndian
	case "MM":
		order = binary.BigEndian
	default:
		return Point{}, false, invalid
	}
	if order.Uint16(data[2:]) != 42 {
		return Point{}, false, invalid
	}
	pos := uint64(order.Uint32(data[4:]))
	if pos < 8 || pos > uint64(len(data))-2 {
		return Point{}, false, invalid
	}
	count := uint64(order.Uint16(data[pos:]))
	if count*12+6 > uint64(len(data))-pos {
		return Point{}, false, invalid
	}
	dpi := Point{}
	unit := uint16(2)
	seen := [3]bool{}
	hasColor := false
	for i := uint64(0); i < count; i++ {
		entry := data[pos+2+12*i : pos+14+12*i]
		tag := order.Uint16(entry)
		if tag == 34665 {
			if hasColor || order.Uint16(entry[2:]) != 4 || order.Uint32(entry[4:]) != 1 {
				return Point{}, false, invalid
			}
			hasColor = true
			offset := uint64(order.Uint32(entry[8:]))
			if offset == pos {
				return Point{}, false, invalid
			}
			if err := exifImageColor(data, order, offset); err != nil {
				return Point{}, false, err
			}
		}
		if tag != 282 && tag != 283 && tag != 296 {
			continue
		}
		index := int(tag - 282)
		if tag == 296 {
			index = 2
		}
		if seen[index] || order.Uint32(entry[4:]) != 1 {
			return Point{}, false, invalid
		}
		seen[index] = true
		if tag == 296 {
			if order.Uint16(entry[2:]) != 3 {
				return Point{}, false, invalid
			}
			unit = order.Uint16(entry[8:])
			continue
		}
		if order.Uint16(entry[2:]) != 5 {
			return Point{}, false, invalid
		}
		offset := uint64(order.Uint32(entry[8:]))
		if offset > uint64(len(data))-8 {
			return Point{}, false, invalid
		}
		n, d := order.Uint32(data[offset:]), order.Uint32(data[offset+4:])
		if n == 0 || d == 0 {
			return Point{}, false, invalid
		}
		if tag == 282 {
			dpi.X = float64(n) / float64(d)
		} else {
			dpi.Y = float64(n) / float64(d)
		}
	}
	if unit < 1 || unit > 3 || seen[0] != seen[1] {
		return Point{}, false, invalid
	}
	if !seen[0] || unit == 1 {
		return Point{}, false, nil
	}
	if unit == 3 {
		dpi.X *= 2.54
		dpi.Y *= 2.54
	}
	return dpi, true, nil
}

// exifImageColor 校验EXIF颜色空间声明，未校准颜色由ICC或像素格式解释
// 入参: data TIFF数据, order 字节序, offset EXIF目录偏移
// 返回: error 目录错误或颜色能力错误
func exifImageColor(data []byte, order binary.ByteOrder, offset uint64) error {
	if len(data) < 2 || offset < 8 || offset > uint64(len(data))-2 {
		return fmt.Errorf("%w: EXIF color directory offset", ErrInvalid)
	}
	count := uint64(order.Uint16(data[offset:]))
	if count*12+6 > uint64(len(data))-offset {
		return fmt.Errorf("%w: EXIF color directory size", ErrInvalid)
	}
	seen := false
	for i := uint64(0); i < count; i++ {
		entry := data[offset+2+12*i : offset+14+12*i]
		if order.Uint16(entry) != 0xa001 {
			continue
		}
		if seen || order.Uint16(entry[2:]) != 3 || order.Uint32(entry[4:]) != 1 {
			return fmt.Errorf("%w: EXIF color space tag", ErrInvalid)
		}
		seen = true
		if value := order.Uint16(entry[8:]); value != 1 && value != 0xffff {
			return fmt.Errorf("%w: EXIF color space %d", ErrUnsupported, value)
		}
	}
	return nil
}

// pngICCStream 检查配置文件关键字和压缩方法，保留压缩流供颜色选择阶段使用
// 入参: data iCCP块内容
// 返回: []byte 压缩流视图, error 关键字或压缩方法错误
func pngICCStream(data []byte) ([]byte, error) {
	end := bytes.IndexByte(data, 0)
	if end < 1 || end > 79 || len(data)-end < 3 || data[end+1] != 0 || data[0] == ' ' || data[end-1] == ' ' {
		return nil, fmt.Errorf("%w: PNG ICC keyword or compression method", ErrInvalid)
	}
	space := false
	for _, value := range data[:end] {
		if value < 32 || value > 126 && value < 161 || space && value == ' ' {
			return nil, fmt.Errorf("%w: PNG ICC keyword", ErrInvalid)
		}
		space = value == ' '
	}
	return data[end+2:], nil
}

// inflatePNGProfile 在受限缓冲区中解压已选用的配置文件，不解压被关联配置文件覆盖的数据
// 入参: data zlib压缩流, limit 解压字节上限
// 返回: []byte ICC字节, error 压缩或资源错误
func inflatePNGProfile(data []byte, limit int64) ([]byte, error) {
	if limit < 0 || limit >= int64(^uint(0)>>1) {
		return nil, fmt.Errorf("%w: PNG ICC byte budget", ErrLimit)
	}
	input := bytes.NewReader(data)
	decoder, err := zlib.NewReader(input)
	if err != nil {
		return nil, fmt.Errorf("%w: PNG ICC compression: %w", ErrInvalid, err)
	}
	defer decoder.Close()
	profile, err := io.ReadAll(io.LimitReader(decoder, limit+1))
	if int64(len(profile)) > limit {
		return nil, fmt.Errorf("%w: PNG ICC byte budget", ErrLimit)
	}
	if err != nil || input.Len() != 0 {
		return nil, fmt.Errorf("%w: PNG ICC stream", ErrInvalid)
	}
	return profile, nil
}

// imageColorChannels 取得原生颜色通道数，透明度不计入配置文件输入
// 入参: source 源图像
// 返回: int 颜色通道数
func imageColorChannels(source *rasterImage) int {
	if source.channels != 0 {
		return source.channels
	}
	if source.native != nil {
		return source.native.channels
	}
	switch source.pixels.(type) {
	case *image.Gray, *image.Gray16:
		return 1
	case *image.CMYK:
		return 4
	default:
		return 3
	}
}

// imageProfileCompatible 检查配置文件分量数，三通道N色图像允许标准规定的双色配置文件忽略第三通道
// 入参: source 原生图像, transform 配置文件转换
// 返回: bool 配置文件是否适用于源颜色通道
func imageProfileCompatible(source *rasterImage, transform *iccTransform) bool {
	channels := imageColorChannels(source)
	return transform.inputChannels() == channels || source.multiChannel && channels == 3 && transform.inputChannels() == 2
}

// imageICCCompatible 检查原生像素与ICC输入分量，不以设备坐标数替代命名色色调数
// 入参: source 原生图像, profile 已解析ICC
// 返回: bool 分量是否兼容, error 命名色数据错误
func imageICCCompatible(source *rasterImage, profile *iccProfile) (bool, error) {
	channels := profile.channels
	if profile.class == "nmcl" {
		named, err := parseICCNamedColor(profile)
		if err != nil {
			return false, err
		}
		channels = len(named)
	}
	count := imageColorChannels(source)
	return channels == count || source.multiChannel && count == 3 && channels == 2, nil
}

// imageICCIntent 根据图像颜色模型选择缺省源渲染意图，不改变目标显示策略
// 入参: profile 已解析源配置文件
// 返回: uint32 ICC源渲染意图
func imageICCIntent(profile *iccProfile) uint32 {
	if profile.space == "RGB " && profile.class != "nmcl" {
		return 0
	}
	return 1
}

// embedded 复用图像内部配置文件，将其解压字节和数量纳入本次绘制的颜色预算
// 入参: part 图像部件, data 配置文件数据, compressed 是否采用PNG的zlib压缩
// 返回: *iccTransform 对应图像模型的源转换, error 封装、能力或资源错误
func (c *sceneColorCache) embedded(part string, data []byte, compressed bool) (*iccTransform, error) {
	profile, err := c.embeddedProfile(part, data, compressed)
	if err != nil {
		return nil, err
	}
	return c.profileTransform(strings.ToLower(part)+"#embedded", profile, imageICCIntent(profile))
}

// embeddedProfile 读取并缓存图像内ICC，不提前准备尚未使用的转换方向
// 入参: part 图像部件, data ICC数据, compressed 是否为zlib
// 返回: *iccProfile 完整只读profile, error 编码或预算错误
func (c *sceneColorCache) embeddedProfile(part string, data []byte, compressed bool) (*iccProfile, error) {
	key := strings.ToLower(part) + "#embedded"
	profile := c.profiles[key]
	if profile == nil {
		if err := c.profileErrors[key]; err != nil {
			return nil, err
		}
		if len(c.profiles)+len(c.profileErrors) >= c.maxProfiles || c.bytes < 0 {
			return nil, fmt.Errorf("%w: embedded image profile budget", ErrLimit)
		}
		if compressed {
			value, err := inflatePNGProfile(data, c.bytes)
			if err != nil {
				return nil, err
			}
			data = value
		}
		if int64(len(data)) > c.bytes {
			return nil, fmt.Errorf("%w: embedded image profile byte budget", ErrLimit)
		}
		value, err := c.cacheProfile(key, data)
		if err != nil {
			return nil, err
		}
		profile = value
	}
	return profile, nil
}

// colorImage 按关联优先、内嵌其次选择兼容ICC并构建独立颜色视图，OpenXPS缺失可用ICC时报错
// 入参: brush 图像画刷, part 图像部件, source 已解码图像
// 返回: *rasterImage 带独立颜色解释的图像视图, error 配置文件、能力或资源错误
func (c *sceneImageCache) colorImage(brush *Brush, part string, source *rasterImage) (result *rasterImage, err error) {
	if c.deferColor {
		return c.printColorImage(brush, part, source)
	}
	if err := checkContext(c.context); err != nil {
		return nil, err
	}
	if brush.ImageProfileURI == "" && len(source.profile) == 0 {
		return source, nil
	}
	if c.colors == nil {
		return nil, fmt.Errorf("%w: image color resource loader is unavailable", ErrUnsupported)
	}
	defer func() {
		if err != nil {
			err = &PartError{Part: part, Err: err}
		}
	}()
	var transform *iccTransform
	var associatedErr error
	if brush.ImageProfileURI != "" {
		profile, unusable, e := c.colors.profileUsability(brush.Part, brush.ImageProfileURI, c.context)
		if e != nil && !unusable {
			return nil, e
		}
		if e == nil {
			if c.format == FormatXPS {
				compatible, err := imageICCCompatible(source, profile)
				if err != nil {
					return nil, err
				}
				if !compatible {
					return defaultImageProfile(source), nil
				}
			}
			transform, e = c.colors.transform(brush.Part, brush.ImageProfileURI, imageICCIntent(profile))
			if e != nil && !colorProfileUnusable(e) {
				return nil, e
			}
		}
		if e == nil && !imageProfileCompatible(source, transform) {
			if c.format == FormatXPS {
				return defaultImageProfile(source), nil
			}
			transform = nil
			profilePart, _ := resolvePart(brush.Part, brush.ImageProfileURI)
			e = &PartError{Part: profilePart, Err: fmt.Errorf("%w: associated image profile channels", ErrInvalid)}
		}
		associatedErr = e
		if c.format == FormatXPS && e != nil {
			return nil, e
		}
	}
	if transform == nil && len(source.profile) != 0 {
		transform, err = c.colors.embedded(part, source.profile, source.profileCompressed)
		if e := checkContext(c.context); e != nil {
			return nil, e
		}
		if err != nil {
			if !colorProfileUnusable(err) {
				return nil, err
			}
			return nil, errors.Join(associatedErr, err)
		}
		if !imageProfileCompatible(source, transform) {
			if c.format == FormatXPS {
				return defaultImageProfile(source), nil
			}
			return nil, errors.Join(associatedErr, fmt.Errorf("%w: embedded image profile channels", ErrInvalid))
		}
	}
	if transform == nil {
		return nil, associatedErr
	}
	if err := checkContext(c.context); err != nil {
		return nil, err
	}
	value := *source
	value.transform = transform
	return &value, nil
}

// defaultImageProfile 建立采用像素默认编码的视图，不修改原始图像或其嵌入资产
// 入参: source 原始图像
// 返回: *rasterImage 不执行不兼容ICC的独立视图
func defaultImageProfile(source *rasterImage) *rasterImage {
	value := *source
	value.profile, value.transform = nil, nil
	value.selectedProfile = nil
	value.associatedProfile = false
	value.profileCompressed = false
	return &value
}

// standaloneImageColor 准备未绑定包内资源的图像配置文件，不猜测关联配置文件的位置
// 入参: source 图像资源
// 返回: *rasterImage 颜色解释独立的图像视图, error 配置文件或能力错误
func standaloneImageColor(source *rasterImage) (*rasterImage, error) {
	if source.transform != nil || source.selectedProfile != nil || len(source.profile) == 0 {
		return source, nil
	}
	data := source.profile
	if source.profileCompressed {
		value, err := inflatePNGProfile(data, 64<<20)
		if err != nil {
			return nil, err
		}
		data = value
	}
	profile, err := parseICCProfile(data)
	if err != nil {
		return nil, err
	}
	transform, err := prepareICCTransform(profile, imageICCIntent(profile))
	if err != nil {
		return nil, err
	}
	if !imageProfileCompatible(source, transform) {
		return nil, fmt.Errorf("%w: embedded image profile channels", ErrInvalid)
	}
	value := *source
	value.transform = transform
	return &value, nil
}

// RecompressImages 无损重压缩PNG图像数据，保留像素、ICC与安全辅助块并仅提交更小候选，不改变部件URI和页面引用
// 未识别或不可安全复制的块与其他格式原样保留并记入结果，保留原包签名且不自动重签
// 入参: ctx 取消Context，nil采用Background, options 扫描及工作参数，nil采用包上限
// 返回: []ResourceOptimization 按部件名排列的图像结果，失败为nil, error 结构、扫描、许可或取消错误
func (p *Package) RecompressImages(ctx context.Context, options *OptimizationOptions) ([]ResourceOptimization, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	configuration := OptimizationOptions{MaxBytes: p.limits.MaxPackageBytes, MaxWork: p.limits.MaxXMLNodes}
	if options != nil {
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxWork != 0 {
			configuration.MaxWork = options.MaxWork
		}
	}
	if configuration.MaxBytes < 1 || configuration.MaxWork < 1 {
		return nil, fmt.Errorf("%w: image recompression limits", ErrInvalid)
	}
	r, err := p.reader(ctx)
	if err != nil {
		return nil, err
	}
	defer r.Close()
	budget := resourceMergeBudget{bytes: configuration.MaxBytes, work: configuration.MaxWork, seen: make(map[string]bool), context: ctx}
	compressor, err := zlib.NewWriterLevel(io.Discard, zlib.BestCompression)
	if err != nil {
		return nil, err
	}
	defer compressor.Close()
	buffer := make([]byte, 32<<10)
	var candidate pngCompressionSink
	var result []ResourceOptimization
	pending := make(map[string]packagePart)
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		part := p.parts[key]
		if !requiredResourceMedia(requiredImage, part.media) {
			continue
		}
		entry := ResourceOptimization{Part: part.name, OriginalBytes: int64(len(part.data)), Bytes: int64(len(part.data))}
		if err := p.editable(part.name); err != nil {
			entry.Err = err
			result = append(result, entry)
			continue
		}
		if !strings.EqualFold(part.media, "image/png") {
			entry.Err = &PartError{Part: part.name, Err: fmt.Errorf("%w: image recompression format %s", ErrUnsupported, part.media)}
			result = append(result, entry)
			continue
		}
		if err := budget.part(key, len(part.data)); err != nil {
			return nil, err
		}
		encoded, err := recompressPNG(part.data, p.maxImagePixels, &budget, compressor, &candidate, buffer)
		if err != nil {
			if !errors.Is(err, ErrUnsupported) {
				return nil, &PartError{Part: part.name, Err: err}
			}
			entry.Err = &PartError{Part: part.name, Err: err}
		} else if len(encoded) != 0 {
			entry.Bytes, entry.Changed = int64(len(encoded)), true
			pending[key] = packagePart{name: part.name, media: part.media, data: encoded}
		}
		result = append(result, entry)
	}
	if len(pending) == 0 {
		return result, checkContext(ctx)
	}
	q := p.signingCopy()
	for key, part := range pending {
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		q.total -= int64(len(q.parts[key].data) - len(part.data))
		q.parts[key], q.dirty[key] = part, true
	}
	verified, err := q.reader(ctx)
	if err != nil {
		return nil, err
	}
	verified.Close()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p.parts, p.dirty, p.total = q.parts, q.dirty, q.total
	return result, nil
}

// Write 接收压缩输出，容量耗尽时放弃候选而不终止输入校验
// 入参: data 压缩字节
// 返回: int 已接收字节数, error 缓冲错误
func (s *pngCompressionSink) Write(data []byte) (int, error) {
	if !s.full {
		if _, err := s.buffer.Write(data); err != nil {
			s.full = true
		}
	}
	return len(data), nil
}

// recompressPNG 重压缩原过滤行并合并连续IDAT，其他块逐字节保留，不将整幅图像展开为像素
// 入参: data 原PNG, maxPixels 图像像素上限, budget 扫描预算, compressor 复用压缩器, candidate 复用候选, buffer 复用扫描缓冲
// 返回: []byte 更小的独立候选，无收益时为nil, error 数据、能力、预算或取消错误
func recompressPNG(data []byte, maxPixels uint64, budget *resourceMergeBudget, compressor *zlib.Writer, candidate *pngCompressionSink, buffer []byte) ([]byte, error) {
	if err := budget.charge(1 + max(0, len(data)-1)/4096); err != nil {
		return nil, err
	}
	if _, err := pngImageMetadata(data); err != nil {
		return nil, err
	}
	config, err := png.DecodeConfig(bytes.NewReader(data))
	if err != nil {
		return nil, rasterImageDecodeError(err)
	}
	if config.Width < 1 || config.Height < 1 || config.Width > rasterMaxDimension || config.Height > rasterMaxDimension || uint64(config.Width)*uint64(config.Height) > maxPixels {
		return nil, fmt.Errorf("%w: PNG recompression pixels", ErrLimit)
	}
	layout, err := pngCompressionChunks(data, budget)
	if err != nil {
		return nil, err
	}
	candidate.buffer.reset(min(compressionBufferLimit, layout.end-layout.start-12))
	candidate.full = false
	compressor.Reset(candidate)
	input := pngCompressedReader{data: data, next: layout.start, limit: layout.end}
	decoder, err := zlib.NewReader(&input)
	if err != nil {
		return nil, fmt.Errorf("%w: PNG image compression: %w", ErrInvalid, err)
	}
	defer decoder.Close()
	if err := recompressPNGScanlines(decoder, compressor, data[24:29], config.Width, config.Height, budget, buffer); err != nil {
		return nil, err
	}
	var last [1]byte
	n, err := decoder.Read(last[:])
	if n != 0 || err != io.EOF {
		return nil, fmt.Errorf("%w: PNG filtered data ending", ErrInvalid)
	}
	if _, err := input.ReadByte(); err != io.EOF {
		return nil, fmt.Errorf("%w: trailing PNG compressed data", ErrInvalid)
	}
	if err := compressor.Close(); err != nil {
		return nil, err
	}
	if err := budget.charge(1); err != nil {
		return nil, err
	}
	if candidate.full || candidate.buffer.Len()+12 >= layout.end-layout.start {
		return nil, nil
	}
	payload := candidate.buffer.Bytes()
	output := make([]byte, 0, len(data)-(layout.end-layout.start)+len(payload)+12)
	output = append(output, data[:layout.start]...)
	output = binary.BigEndian.AppendUint32(output, uint32(len(payload)))
	start := len(output)
	output = append(output, "IDAT"...)
	output = append(output, payload...)
	output = binary.BigEndian.AppendUint32(output, crc32.ChecksumIEEE(output[start:]))
	output = append(output, data[layout.end:]...)
	return output, nil
}

// pngCompressionChunks 校验IDAT连续性及编辑器复制规则，未知不可安全复制块阻止修改而非被删除
// 入参: data 已校验块长度及CRC的PNG, budget 遍历预算
// 返回: pngCompressionLayout IDAT范围, error 块顺序、能力或预算错误
func pngCompressionChunks(data []byte, budget *resourceMergeBudget) (pngCompressionLayout, error) {
	var layout pngCompressionLayout
	ended, palette := false, false
	for position := 8; position < len(data); {
		if err := budget.charge(1); err != nil {
			return pngCompressionLayout{}, err
		}
		size := int(binary.BigEndian.Uint32(data[position:]))
		kind := data[position+4 : position+8]
		for _, value := range kind {
			if value < 'A' || value > 'Z' && value < 'a' || value > 'z' {
				return pngCompressionLayout{}, fmt.Errorf("%w: PNG chunk type", ErrInvalid)
			}
		}
		if kind[2]&32 != 0 {
			return pngCompressionLayout{}, fmt.Errorf("%w: PNG reserved chunk bit", ErrInvalid)
		}
		end := position + size + 12
		if string(kind) == "IDAT" {
			if ended {
				return pngCompressionLayout{}, fmt.Errorf("%w: nonconsecutive PNG image chunks", ErrInvalid)
			}
			if layout.start == 0 {
				layout.start = position
			}
			layout.end = end
		} else {
			ended = layout.start != 0
			switch string(kind) {
			case "IHDR":
				if position != 8 {
					return pngCompressionLayout{}, fmt.Errorf("%w: repeated PNG header", ErrInvalid)
				}
			case "IEND":
			case "PLTE":
				if palette || ended {
					return pngCompressionLayout{}, fmt.Errorf("%w: PNG palette placement", ErrInvalid)
				}
				palette = true
			default:
				if kind[0]&32 == 0 || kind[3]&32 == 0 && !slices.Contains([]string{"tRNS", "cHRM", "gAMA", "iCCP", "sBIT", "sRGB", "bKGD", "hIST", "pHYs", "sPLT", "tIME"}, string(kind)) {
					return pngCompressionLayout{}, fmt.Errorf("%w: PNG preserved chunk %s", ErrUnsupported, kind)
				}
			}
		}
		position = end
	}
	if layout.start == 0 {
		return pngCompressionLayout{}, fmt.Errorf("%w: missing PNG image data", ErrInvalid)
	}
	return layout, nil
}

// recompressPNGScanlines 按原色型及Adam7分组校验过滤行，只复制过滤字节和压缩前数据
// 入参: input 解压流, output 压缩器, header IHDR后五字节, width, height 图像尺寸, budget 累计扫描预算, buffer 复用缓冲
// 返回: error 过滤行、压缩、扫描预算或取消错误
func recompressPNGScanlines(input io.Reader, output io.Writer, header []byte, width, height int, budget *resourceMergeBudget, buffer []byte) error {
	channels := 0
	switch header[1] {
	case 0, 3:
		channels = 1
	case 2:
		channels = 3
	case 4:
		channels = 2
	case 6:
		channels = 4
	}
	passes := [][4]int{{0, 0, 1, 1}}
	if header[4] == 1 {
		passes = [][4]int{{0, 0, 8, 8}, {4, 0, 8, 8}, {0, 4, 4, 8}, {2, 0, 4, 4}, {0, 2, 2, 4}, {1, 0, 2, 2}, {0, 1, 1, 2}}
	}
	var filter [1]byte
	for _, pass := range passes {
		if width <= pass[0] || height <= pass[1] {
			continue
		}
		columns := (width - pass[0] + pass[2] - 1) / pass[2]
		rows := (height - pass[1] + pass[3] - 1) / pass[3]
		rowBytes := (int64(columns)*int64(channels)*int64(header[0]) + 7) / 8
		for range rows {
			if err := budget.charge(1); err != nil {
				return err
			}
			if rowBytes+1 > budget.bytes {
				return fmt.Errorf("%w: PNG decompression scan budget", ErrLimit)
			}
			budget.bytes -= rowBytes + 1
			if _, err := io.ReadFull(input, filter[:]); err != nil || filter[0] > 4 {
				return fmt.Errorf("%w: PNG filtered scanline", ErrInvalid)
			}
			if n, err := output.Write(filter[:]); err != nil {
				return err
			} else if n != 1 {
				return io.ErrShortWrite
			}
			for remaining := rowBytes; remaining > 0; {
				if err := budget.charge(1); err != nil {
					return err
				}
				count := int(min(remaining, int64(len(buffer))))
				if _, err := io.ReadFull(input, buffer[:count]); err != nil {
					return fmt.Errorf("%w: PNG filtered scanline data: %w", ErrInvalid, err)
				}
				if n, err := output.Write(buffer[:count]); err != nil {
					return err
				} else if n != count {
					return io.ErrShortWrite
				}
				remaining -= int64(count)
			}
		}
	}
	return nil
}

// Read 读取当前压缩载荷片段并跳过块封装，允许空IDAT块
// 入参: output 读取缓冲区
// 返回: int 已读字节数, error 流结束信息
func (r *pngCompressedReader) Read(output []byte) (int, error) {
	if len(output) == 0 {
		return 0, nil
	}
	for r.start == r.end {
		if r.next == r.limit {
			return 0, io.EOF
		}
		size := int(binary.BigEndian.Uint32(r.data[r.next:]))
		r.start, r.end = r.next+8, r.next+8+size
		r.next = r.end + 4
	}
	count := copy(output, r.data[r.start:r.end])
	r.start += count
	return count, nil
}

// ReadByte 为zlib提供精确逐字节读取，避免额外缓冲隐藏末尾未消费的数据
// 返回: byte 压缩字节, error 流结束信息
func (r *pngCompressedReader) ReadByte() (byte, error) {
	var value [1]byte
	_, err := r.Read(value[:])
	return value[0], err
}

// decodeLosslessJPEGImage 解码灰度或明确标识RGB分量的无损JPEG，逐扫描保留原始精度与颜色配置文件
// 入参: data 完整码流, metadata 图像元数据, maxPixels 剩余像素预算
// 返回: *rasterImage 解码图像, error 数据、能力或资源错误
func decodeLosslessJPEGImage(data []byte, metadata rasterMetadata, maxPixels uint64) (*rasterImage, error) {
	if uint64(len(data)) > rasterMaxWork {
		return nil, fmt.Errorf("%w: lossless JPEG input budget", ErrLimit)
	}
	stream, err := normalizeTIFFJPEG(data, false, tiffJPEGTable{})
	if err != nil {
		return nil, err
	}
	if stream.process != 0xc3 {
		return nil, fmt.Errorf("%w: lossless JPEG frame process", ErrInvalid)
	}
	if stream.components != 1 && stream.components != 3 {
		return nil, fmt.Errorf("%w: lossless JPEG color component interpretation", ErrUnsupported)
	}
	var frame []byte
	var huffman [4]losslessHuffman
	var restart uint16
	var covered uint8
	var out *rasterImage
	for pos := 2; pos < len(stream.data); {
		for pos < len(stream.data) && stream.data[pos] == 0xff {
			pos++
		}
		if pos == len(stream.data) {
			return nil, fmt.Errorf("%w: lossless JPEG marker", ErrInvalid)
		}
		marker := stream.data[pos]
		pos++
		if marker == 0xd9 {
			if out == nil || covered != uint8(1<<stream.components)-1 || pos != len(stream.data) {
				return nil, fmt.Errorf("%w: incomplete lossless JPEG components", ErrInvalid)
			}
			return out, nil
		}
		if len(stream.data)-pos < 2 {
			return nil, fmt.Errorf("%w: lossless JPEG marker length", ErrInvalid)
		}
		size := int(binary.BigEndian.Uint16(stream.data[pos:]))
		if size < 2 || size > len(stream.data)-pos {
			return nil, fmt.Errorf("%w: lossless JPEG marker range", ErrInvalid)
		}
		payload := stream.data[pos+2 : pos+size]
		pos += size
		switch marker {
		case 0xc3:
			if len(payload) != 6+3*stream.components || payload[0] < 2 || payload[0] > 16 {
				return nil, fmt.Errorf("%w: lossless JPEG frame", ErrInvalid)
			}
			width, height := int(binary.BigEndian.Uint16(payload[3:])), int(binary.BigEndian.Uint16(payload[1:]))
			if width == 0 || height == 0 {
				return nil, fmt.Errorf("%w: lossless JPEG frame dimensions", ErrInvalid)
			}
			pixels := uint64(width) * uint64(height)
			if pixels > maxPixels || pixels > uint64(^uint(0)>>1)/8 || pixels > rasterMaxWork/uint64(stream.components) {
				return nil, fmt.Errorf("%w: lossless JPEG decoded pixels", ErrLimit)
			}
			var identities [256]bool
			for c := range stream.components {
				identity := payload[6+c*3]
				if identities[identity] || payload[8+c*3] != 0 {
					return nil, fmt.Errorf("%w: lossless JPEG frame component", ErrInvalid)
				}
				identities[identity] = true
				if payload[7+c*3] != 0x11 {
					return nil, fmt.Errorf("%w: subsampled lossless JPEG components", ErrUnsupported)
				}
				if stream.components == 3 && identity != "RGB"[c] {
					return nil, fmt.Errorf("%w: unspecified lossless JPEG RGB component mapping", ErrUnsupported)
				}
			}
			frame = payload
			out = &rasterImage{pixels: image.NewNRGBA64(image.Rect(0, 0, width, height)), dpi: metadata.dpi, channels: stream.components, profile: metadata.profile}
		case 0xc4:
			for len(payload) != 0 {
				selector := payload[0]
				payload = payload[1:]
				size := 16
				for _, count := range payload[:16] {
					size += int(count)
				}
				if selector>>4 == 0 {
					huffman[selector&15], err = readLosslessHuffman(payload[:size])
					if err != nil {
						return nil, err
					}
				}
				payload = payload[size:]
			}
		case 0xdd:
			if len(payload) != 2 {
				return nil, fmt.Errorf("%w: lossless JPEG restart header", ErrInvalid)
			}
			restart = binary.BigEndian.Uint16(payload)
		case 0xda:
			end, err := losslessJPEGEntropyEnd(stream.data, pos)
			if err != nil {
				return nil, err
			}
			mask, err := decodeLosslessJPEGScan(out, frame, payload, stream.data[pos:end], huffman, restart, covered)
			if err != nil {
				return nil, err
			}
			covered |= mask
			pos = end
		}
	}
	return nil, fmt.Errorf("%w: missing lossless JPEG end marker", ErrInvalid)
}

// losslessJPEGEntropyEnd 定位扫描末尾并检查独立扫描的首个重启序号
// 入参: data 完整码流, pos 熵编码起点
// 返回: int 后继标记起点, error 截断或重启错误
func losslessJPEGEntropyEnd(data []byte, pos int) (int, error) {
	first := true
	for pos < len(data) {
		if data[pos] != 0xff {
			pos++
			continue
		}
		start := pos
		for pos < len(data) && data[pos] == 0xff {
			pos++
		}
		if pos == len(data) {
			break
		}
		marker := data[pos]
		if marker != 0 && (marker < 0xd0 || marker > 0xd7) {
			return start, nil
		}
		if marker != 0 {
			if first && marker != 0xd0 {
				return 0, fmt.Errorf("%w: lossless JPEG first restart sequence", ErrInvalid)
			}
			first = false
		}
		pos++
	}
	return 0, fmt.Errorf("%w: lossless JPEG entropy end", ErrInvalid)
}

// decodeLosslessJPEGScan 校验当前扫描的分量和码表，只更新对应颜色通道
// 入参: out 目标图像, frame 帧定义, scan 扫描定义, data 熵编码, huffman 当前码表, restart 重启间隔, covered 已解码分量
// 返回: uint8 本次分量标记, error 参数、重复分量或熵编码错误
func decodeLosslessJPEGScan(out *rasterImage, frame, scan, data []byte, huffman [4]losslessHuffman, restart uint16, covered uint8) (uint8, error) {
	if out == nil || len(scan) < 4 || scan[0] == 0 || int(scan[0]) > out.channels || len(scan) != 4+2*int(scan[0]) {
		return 0, fmt.Errorf("%w: lossless JPEG scan size", ErrInvalid)
	}
	predictor, point := uint32(scan[len(scan)-3]), uint32(scan[len(scan)-1])
	if predictor < 1 || predictor > 7 || scan[len(scan)-2] != 0 || point >= uint32(frame[0]) {
		return 0, fmt.Errorf("%w: lossless JPEG prediction parameters", ErrInvalid)
	}
	l := tiffLegacyJPEG{channels: int(scan[0]), lossless: true, bits: uint32(frame[0]), restart: restart}
	var components [4]int
	var mask uint8
	for index := range l.channels {
		identity, selector := scan[1+index*2], scan[2+index*2]
		component := -1
		for c := range out.channels {
			if frame[6+c*3] == identity {
				component = c
				break
			}
		}
		if component < 0 || (covered|mask)&(1<<component) != 0 || selector&15 != 0 || selector>>4 > 3 || huffman[selector>>4].symbols == nil {
			return 0, fmt.Errorf("%w: lossless JPEG scan component", ErrInvalid)
		}
		mask |= 1 << component
		components[index] = component
		l.huffman[index] = huffman[selector>>4]
		l.scanOrder[index] = byte(index)
		l.predictor[index], l.point[index] = predictor, point
	}
	if err := l.losslessBlockDecode(out, data, out.bounds(), 1, components[:l.channels]); err != nil {
		return 0, err
	}
	return mask, nil
}

// readLosslessHuffman 校验规范霍夫曼码及差值类别，拒绝全一编码和不完整定义
// 入参: data 十六项码长计数及类别符号
// 返回: losslessHuffman 只读解码表, error 码表错误
func readLosslessHuffman(data []byte) (losslessHuffman, error) {
	var h losslessHuffman
	if len(data) < 17 {
		return h, fmt.Errorf("%w: lossless JPEG Huffman size", ErrInvalid)
	}
	code, index := uint32(0), 0
	for i, count := range data[:16] {
		h.first[i], h.count[i], h.index[i] = code, uint32(count), index
		code += uint32(count)
		index += int(count)
		if code >= 1<<uint(i+1) {
			return h, fmt.Errorf("%w: lossless JPEG Huffman code space", ErrInvalid)
		}
		code <<= 1
	}
	if index == 0 || index > 17 || len(data) != 16+index {
		return h, fmt.Errorf("%w: lossless JPEG Huffman symbols", ErrInvalid)
	}
	var seen [17]bool
	for _, symbol := range data[16:] {
		if symbol > 16 || seen[symbol] {
			return h, fmt.Errorf("%w: lossless JPEG difference category", ErrInvalid)
		}
		seen[symbol] = true
	}
	h.symbols = data[16:]
	return h, nil
}

// bits 读取高位优先的熵编码位，处理字节填充但不越过重启标记
// 入参: count 所需位数，范围零到十六
// 返回: uint32 读取值, error 截断或标记错误
func (b *losslessBits) bits(count uint) (uint32, error) {
	if count > 16 {
		return 0, fmt.Errorf("%w: lossless JPEG bit count", ErrInvalid)
	}
	for b.left < count {
		if b.pos >= len(b.data) {
			return 0, fmt.Errorf("%w: lossless JPEG entropy end", ErrInvalid)
		}
		value := b.data[b.pos]
		b.pos++
		if value == 0xff {
			if b.pos >= len(b.data) || b.data[b.pos] != 0 {
				return 0, fmt.Errorf("%w: lossless JPEG entropy stuffing", ErrInvalid)
			}
			b.pos++
		}
		b.word = b.word<<8 | uint32(value)
		b.left += 8
	}
	b.left -= count
	return b.word >> b.left & uint32(1<<count-1), nil
}

// difference 解码有符号模差值，十六类差值无需附加位
// 入参: h 当前分量的霍夫曼码表
// 返回: int 差值, error 类别或熵编码错误
func (b *losslessBits) difference(h *losslessHuffman) (int, error) {
	code := uint32(0)
	for length := range 16 {
		bit, err := b.bits(1)
		if err != nil {
			return 0, err
		}
		code = code<<1 | bit
		if code < h.first[length] || code-h.first[length] >= h.count[length] {
			continue
		}
		category := uint(h.symbols[h.index[length]+int(code-h.first[length])])
		if category == 16 {
			return 32768, nil
		}
		value, err := b.bits(category)
		if err != nil {
			return 0, err
		}
		if category != 0 && value < 1<<(category-1) {
			return int(value) - (1<<category - 1), nil
		}
		return int(value), nil
	}
	return 0, fmt.Errorf("%w: lossless JPEG Huffman code", ErrInvalid)
}

// align 检查熵编码段末尾的全一填充位，并移到字节边界
// 返回: error 填充错误
func (b *losslessBits) align() error {
	if b.left > 7 || b.word&uint32(1<<b.left-1) != uint32(1<<b.left-1) {
		return fmt.Errorf("%w: lossless JPEG entropy padding", ErrInvalid)
	}
	b.left = 0
	return nil
}

// restart 读取行边界的重启标记，首个编号可由外层TIFF条带的全局相位决定
// 入参: previous 前次编号，负值表示尚无编号
// 返回: int 当前编号, error 标记错误
func (b *losslessBits) restart(previous int) (int, error) {
	if err := b.align(); err != nil {
		return 0, err
	}
	if b.pos == len(b.data) || b.data[b.pos] != 0xff {
		return 0, fmt.Errorf("%w: lossless JPEG missing restart", ErrInvalid)
	}
	for b.pos < len(b.data) && b.data[b.pos] == 0xff {
		b.pos++
	}
	if b.pos == len(b.data) {
		return 0, fmt.Errorf("%w: lossless JPEG truncated restart", ErrInvalid)
	}
	marker := b.data[b.pos]
	b.pos++
	if marker < 0xd0 || marker > 0xd7 || previous >= 0 && int(marker-0xd0) != (previous+1)&7 {
		return 0, fmt.Errorf("%w: lossless JPEG restart sequence", ErrInvalid)
	}
	return int(marker - 0xd0), nil
}

// losslessPrediction 用完整有符号整数计算七种空间预测，右移采用算术右移
// 入参: selection 预测编号, left 左邻样本, above 上邻样本, diagonal 左上样本
// 返回: int 预测值，不裁剪到输入精度
func losslessPrediction(selection uint32, left, above, diagonal int) int {
	switch selection {
	case 1:
		return left
	case 2:
		return above
	case 3:
		return diagonal
	case 4:
		return left + above - diagonal
	case 5:
		return left + ((above - diagonal) >> 1)
	case 6:
		return above + ((left - diagonal) >> 1)
	default:
		return (left + above) >> 1
	}
}
