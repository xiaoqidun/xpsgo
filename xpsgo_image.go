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
	"math"
	"slices"
	"strings"

	"github.com/xiaoqidun/jxrgo"
)

const (
	// ImageColorUnknown 表示未知图像源色彩空间
	ImageColorUnknown ImageColorSpace = iota
	// ImageColorGray 表示灰度图像源色彩空间
	ImageColorGray
	// ImageColorRGB 表示红绿蓝图像源色彩空间
	ImageColorRGB
	// ImageColorYCC 表示亮度色度YCC图像源色彩空间
	ImageColorYCC
	// ImageColorCMYK 表示青品黄黑CMYK图像源色彩空间
	ImageColorCMYK
	// ImageColorMultiChannel 表示通用多通道N色图像源色彩空间
	ImageColorMultiChannel
)

// losslessColorGray 等常量表示独立无损JPEG解析确定的源色彩空间类别
const (
	losslessColorGray losslessJPEGColor = iota + 1
	losslessColorRGB
	losslessColorYCbCr
	losslessColorCMYK
	losslessColorYCCK
)

// ImageColorSpace 表示解码图像的源色彩空间类别
type ImageColorSpace uint8

// ImageCICP 保存图像声明的ITU-T H.273 CICP色彩编码四元组
type ImageCICP struct {
	Primaries uint8
	Transfer  uint8
	Matrix    uint8
	FullRange bool
}

// ImageInfo 保存从PNG、JPEG、TIFF或JPEG XR文件头提取的轻量元数据，不含解码像素缓冲
type ImageInfo struct {
	Part          string
	ContentType   string
	Width         int
	Height        int
	DPIX          float64
	DPIY          float64
	ColorSpace    ImageColorSpace
	HasAlpha      bool
	BitDepth      int
	IsFloat       bool
	Orientation   uint32
	HasICCProfile bool
	HasCICP       bool
}

// ImageConvertOptions 设置图像色彩管理导出的外挂ICC配置、渲染意图、HDR峰值、背景合成色、打印色彩策略及预算上限
type ImageConvertOptions struct {
	Profile     []byte
	Intent      RenderingIntent
	HDRPeakNits float64
	ColorMode   PrintColorMode
	Negative    bool
	Background  color.Color
	Limits      Limits
}

// losslessJPEGColor 表示独立无损JPEG解析确定的源色彩空间
type losslessJPEGColor uint8

// imageCICP 保存图像声明的CICP色彩编码标识，对应ITU-T H.273四元组
type imageCICP struct {
	primaries uint8
	transfer  uint8
	matrix    uint8
	fullRange bool
}

// imageGammaChroma 保存PNG gAMA与cHRM声明的伽马与CIE色度坐标
type imageGammaChroma struct {
	hasGamma bool
	gamma    float64
	hasChrm  bool
	whiteX   float64
	whiteY   float64
	redX     float64
	redY     float64
	greenX   float64
	greenY   float64
	blueX    float64
	blueY    float64
}

// rasterImage 保存图像原生分量、颜色解释、源格式元数据及物理分辨率
type rasterImage struct {
	pixels            image.Image
	native            *imageComponents
	jxr               *jxrImage
	dpi               Point
	channels          int
	profile           []byte
	profileCompressed bool
	cicp              *imageCICP
	gammaChroma       *imageGammaChroma
	srgb              bool
	hdrPeakNits       float64
	transform         *iccTransform
	selectedProfile   *iccProfile
	associatedProfile bool
	linear            bool
	multiChannel      bool
	colorSpace        ImageColorSpace
	hasAlpha          bool
	bitDepth          int
	floating          bool
	orientation       uint32
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

// rasterMetadata 保存图像分辨率、原生通道数、颜色空间、位深、透明度、方向及颜色提示元数据
type rasterMetadata struct {
	dpi                Point
	channels           int
	colorSpace         ImageColorSpace
	hasAlpha           bool
	bitDepth           int
	floating           bool
	orientation        uint32
	profile            []byte
	profileCompressed  bool
	cicp               *imageCICP
	gammaChroma        *imageGammaChroma
	srgb               bool
	hdrPeakNits        float64
	jpegProcess        byte
	jpegJFIF           bool
	jpegAdobe          bool
	jpegAdobeTransform byte
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
	orientation := metadata.orientation
	if orientation == 0 {
		orientation = 1
	}
	out := &rasterImage{
		pixels:            decoded,
		dpi:               metadata.dpi,
		channels:          metadata.channels,
		profile:           metadata.profile,
		profileCompressed: metadata.profileCompressed,
		cicp:              metadata.cicp,
		gammaChroma:       metadata.gammaChroma,
		srgb:              metadata.srgb,
		hdrPeakNits:       metadata.hdrPeakNits,
		colorSpace:        metadata.colorSpace,
		hasAlpha:          metadata.hasAlpha,
		bitDepth:          metadata.bitDepth,
		floating:          metadata.floating,
		orientation:       orientation,
	}
	if orientation > 1 {
		applyTIFFOrientation(out, orientation)
	}
	return out, nil
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

// DefaultImageOptions 返回图像读取的默认字节上限及解码容量
// 返回: ImageOptions 默认参数
func DefaultImageOptions() ImageOptions {
	return ImageOptions{MaxBytes: DefaultLimits().MaxPartBytes, MaxPixels: 1 << 24}
}

// ImageInfo 仅解析PNG、JPEG、TIFF或JPEG XR文件头返回尺寸、分辨率、色彩空间、位深、方向与ICC/CICP标记，完全不解码像素
// 入参: ctx 取消Context，nil采用Background, part 图像部件包根URI
// 返回: *ImageInfo 轻量图像头元数据, error 状态、媒体类型、文件头、预算或取消错误
func (r *Reader) ImageInfo(ctx context.Context, part string) (*ImageInfo, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	media, err := r.pkg.contentType(canonical)
	if err != nil {
		return nil, &PartError{Part: canonical, Err: err}
	}
	if !requiredResourceMedia(requiredImage, media) {
		return nil, &PartError{Part: canonical, Err: fmt.Errorf("%w: unexpected image content type %q", ErrInvalid, media)}
	}
	key := strings.ToLower(canonical)
	switch strings.ToLower(media) {
	case "image/png":
		stream, err := r.pkg.openPartStream(ctx, key, PartReadOptions{MaxBytes: r.limits.MaxPartBytes})
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		defer stream.Close()
		info, err := readPNGImageInfo(ctx, stream, canonical, media, r.limits.MaxPartBytes)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		return info, nil
	case "image/jpeg":
		stream, err := r.pkg.openPartStream(ctx, key, PartReadOptions{MaxBytes: r.limits.MaxPartBytes})
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		defer stream.Close()
		info, err := readJPEGImageInfo(ctx, stream, canonical, media)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		return info, nil
	case "image/tiff":
		data, err := r.pkg.readItemsContext(ctx, key, r.limits.MaxPartBytes)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		info, err := readTIFFImageInfo(data, canonical, media)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		return info, nil
	case "image/vnd.ms-photo":
		data, err := r.pkg.readItemsContext(ctx, key, r.limits.MaxPartBytes)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		info, err := readJXRImageInfo(ctx, data, canonical, media, uint64(r.limits.MaxPartBytes))
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		return info, nil
	default:
		return nil, &PartError{Part: canonical, Err: fmt.Errorf("%w: unexpected image content type %q", ErrInvalid, media)}
	}
}

// DecodeImageRows 按行流式解码并色彩管理导出包内图像为八位非预乘sRGB行字节，JPEG XR优先走条带级流式转换
// 回调按y从0到Height-1递增接收Width*4字节行切片，缓冲在行间复用，调用方不得跨回调长期持有切片
// 入参: ctx 取消Context，nil采用Background, part 图像部件包根URI, options 图像解码选项，nil采用默认值, convert 色彩转换选项，nil采用默认值, fn 逐行消费回调
// 返回: error 状态、参数、媒体类型、解码、色彩、回调或取消错误
func (r *Reader) DecodeImageRows(ctx context.Context, part string, options *ImageOptions, convert *ImageConvertOptions, fn func(y int, nrgba []byte) error) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	if fn == nil {
		return fmt.Errorf("%w: nil image row consumer", ErrInvalid)
	}
	cfg, maxConvertBytes, err := validateImageConvertOptions(convert)
	if err != nil {
		return err
	}
	if err := r.readLock(); err != nil {
		return err
	}
	imgCfg := DefaultImageOptions()
	if options != nil {
		if options.MaxBytes != 0 {
			imgCfg.MaxBytes = options.MaxBytes
		}
		if options.MaxPixels != 0 {
			imgCfg.MaxPixels = options.MaxPixels
		}
	}
	if imgCfg.MaxBytes < 1 {
		r.mu.RUnlock()
		return fmt.Errorf("%w: image byte limit", ErrInvalid)
	}
	canonical, err := opcPartName(part)
	if err != nil {
		r.mu.RUnlock()
		return err
	}
	media, err := r.pkg.contentType(canonical)
	if err != nil {
		r.mu.RUnlock()
		return &PartError{Part: canonical, Err: err}
	}
	if !requiredResourceMedia(requiredImage, media) {
		r.mu.RUnlock()
		return &PartError{Part: canonical, Err: fmt.Errorf("%w: unexpected image content type %q", ErrInvalid, media)}
	}
	data, err := r.pkg.readItemsContext(ctx, strings.ToLower(canonical), min(imgCfg.MaxBytes, r.limits.MaxPartBytes))
	r.mu.RUnlock()
	if err != nil {
		return &PartError{Part: canonical, Err: err}
	}
	if strings.EqualFold(media, "image/vnd.ms-photo") {
		var callbackErr error
		rowFn := func(y int, nrgba []byte) error {
			if err := fn(y, nrgba); err != nil {
				callbackErr = err
				return err
			}
			return nil
		}
		handled, jxrErr := decodeJXRImageRows(ctx, data, imgCfg.MaxPixels, min(uint64(imgCfg.MaxBytes), maxConvertBytes), cfg, rowFn)
		if callbackErr != nil {
			return callbackErr
		}
		if handled || jxrErr != nil {
			if jxrErr != nil {
				return &PartError{Part: canonical, Err: jxrErr}
			}
			return nil
		}
	}
	source, err := decodeRasterImageWithMemory(ctx, data, media, imgCfg.MaxPixels, uint64(imgCfg.MaxBytes))
	if err != nil {
		return &PartError{Part: canonical, Err: err}
	}
	res := &ImageResource{Part: canonical, ContentType: media, Resolution: source.dpi, Data: data, source: source}
	return res.exportRowsNRGBA(ctx, cfg, maxConvertBytes, fn)
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

// String 返回图像源色彩空间的可读名称
// 返回: string 色彩空间名称
func (s ImageColorSpace) String() string {
	switch s {
	case ImageColorUnknown:
		return "Unknown"
	case ImageColorGray:
		return "Gray"
	case ImageColorRGB:
		return "RGB"
	case ImageColorYCC:
		return "YCC"
	case ImageColorCMYK:
		return "CMYK"
	case ImageColorMultiChannel:
		return "MultiChannel"
	default:
		return fmt.Sprintf("ImageColorSpace(%d)", s)
	}
}

// MultiChannel 报告源图像是否属于N色通道，不将通道数恰为三或四的N色图像误作RGB或CMYK
// 返回: bool 是否为N色图像
func (r *ImageResource) MultiChannel() bool {
	return r != nil && r.source != nil && r.source.multiChannel
}

// ColorSpace 返回源图像的色彩空间类别，精确区分灰度、RGB、YCC、CMYK及通用多通道
// 返回: ImageColorSpace 源色彩空间，空资源返回ImageColorUnknown
func (r *ImageResource) ColorSpace() ImageColorSpace {
	if r == nil || r.source == nil {
		return ImageColorUnknown
	}
	if r.source.colorSpace != ImageColorUnknown {
		return r.source.colorSpace
	}
	if r.source.jxr != nil {
		return jxrImageColorSpace(r.source.jxr.info.ColorSpace)
	}
	if r.source.multiChannel {
		return ImageColorMultiChannel
	}
	switch imageColorChannels(r.source) {
	case 1:
		return ImageColorGray
	case 3:
		return ImageColorRGB
	case 4:
		return ImageColorCMYK
	default:
		return ImageColorMultiChannel
	}
}

// HasAlpha 报告源图像是否包含透明度通道或PNG tRNS简单透明声明
// 返回: bool 是否包含透明度通道
func (r *ImageResource) HasAlpha() bool {
	if r == nil || r.source == nil {
		return false
	}
	if r.source.hasAlpha {
		return true
	}
	if r.source.colorSpace != ImageColorUnknown {
		return false
	}
	if r.source.jxr != nil {
		return r.source.jxr.alpha
	}
	if r.source.native != nil {
		return r.source.native.alpha
	}
	switch r.source.pixels.(type) {
	case *image.NRGBA, *image.NRGBA64, *image.RGBA, *image.RGBA64, *image.NYCbCrA, *image.Alpha, *image.Alpha16:
		return true
	default:
		return false
	}
}

// BitDepth 返回源图像单颜色分量的位深，空资源返回零
// 返回: int 每分量位深
func (r *ImageResource) BitDepth() int {
	if r == nil || r.source == nil {
		return 0
	}
	if r.source.bitDepth > 0 {
		return r.source.bitDepth
	}
	if r.source.jxr != nil && len(r.source.jxr.info.Components) > 0 {
		return int(r.source.jxr.info.Components[0].Precision)
	}
	if r.source.native != nil {
		if r.source.native.floating != nil {
			return 32
		}
		return 16
	}
	if r.source.pixels == nil {
		return 0
	}
	switch r.source.pixels.(type) {
	case *image.NRGBA64, *image.RGBA64, *image.Gray16, *image.Alpha16:
		return 16
	default:
		return 8
	}
}

// IsFloating 报告源图像是否采用浮点样本编码（如16F/32F JPEG XR或SampleFormat=3 TIFF）
// 返回: bool 是否为浮点样本
func (r *ImageResource) IsFloating() bool {
	if r == nil || r.source == nil {
		return false
	}
	if r.source.floating {
		return true
	}
	if r.source.jxr != nil {
		return jxrIsFloating(r.source.jxr.info)
	}
	return r.source.native != nil && r.source.native.floating != nil
}

// Orientation 返回原始文件声明的EXIF/TIFF/JXR方向编号（1至8），未声明时返回1，空资源返回0
// 解码样本与导出图像均已应用该方向纠正，调用方可据此判断Data原始字节能否免旋转透传
// 返回: uint32 原始方向编号
func (r *ImageResource) Orientation() uint32 {
	if r == nil || r.source == nil {
		return 0
	}
	if r.source.orientation >= 1 && r.source.orientation <= 8 {
		return r.source.orientation
	}
	if r.source.jxr != nil {
		return jxrEXIFOrientation(r.source.jxr.info.Orientation)
	}
	return 1
}

// SRGB 报告源图像是否显式声明sRGB标识（如PNG sRGB块或JPEG XR sRGB颜色提示）
// 返回: bool 是否显式声明sRGB
func (r *ImageResource) SRGB() bool {
	return r != nil && r.source != nil && r.source.srgb
}

// CICP 返回源图像声明的ITU-T H.273 CICP四元组独立副本，未声明时返回nil
// 返回: *ImageCICP 独立CICP副本
func (r *ImageResource) CICP() *ImageCICP {
	if r == nil || r.source == nil || r.source.cicp == nil {
		return nil
	}
	c := r.source.cicp
	return &ImageCICP{Primaries: c.primaries, Transfer: c.transfer, Matrix: c.matrix, FullRange: c.fullRange}
}

// HDRPeakNits 返回源图像元数据声明的HDR峰值亮度（单位cd/m²），未声明时返回零
// 返回: float64 峰值亮度
func (r *ImageResource) HDRPeakNits() float64 {
	if r == nil || r.source == nil {
		return 0
	}
	return r.source.hdrPeakNits
}

// ToNRGBA 按完整色彩管理管线将已方向纠正的源图像导出为八位非预乘sRGB图像，并发安全且不修改原资源
// 支持外挂ICC覆盖、内嵌ICC、CICP、PNG gAMA/cHRM、BT.2446色调映射、背景合成以及打印负片与灰度黑白模式
// 入参: ctx 取消Context，nil采用Background, opts 转换选项，nil采用默认值
// 返回: *image.NRGBA 独立八位非预乘图像, error 参数、配置、预算、转换或取消错误
func (r *ImageResource) ToNRGBA(ctx context.Context, opts *ImageConvertOptions) (*image.NRGBA, error) {
	ctx = normalizeContext(ctx)
	cfg, bounds, maxBytes, err := imageConvertValidate(ctx, r, opts, 4)
	if err != nil {
		return nil, err
	}
	out := image.NewNRGBA(bounds)
	width := bounds.Dx()
	if handled, err := r.convertJXRDisplayRows(ctx, bounds, cfg, false, func(y int) []byte {
		rowOff := (y - bounds.Min.Y) * out.Stride
		return out.Pix[rowOff : rowOff+width*4]
	}, nil); handled || err != nil {
		if err != nil {
			return nil, err
		}
		return out, nil
	}
	sampler, err := prepareImageConvertSampler(r, cfg, maxBytes)
	if err != nil {
		return nil, err
	}
	var bgLinear [3]float64
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	var jxrCache jxrRowCache
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		rowOff := (y - bounds.Min.Y) * out.Stride
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			if (x-bounds.Min.X)&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
			}
			c, err := sampler.pixelColorWithCache(x, y, &jxrCache)
			if err != nil {
				return nil, err
			}
			lin, alpha, err := imageConvertLinearPixelWithBG(c, sampler.toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode)
			if err != nil {
				return nil, err
			}
			a8 := colorQuantize8(alpha)
			if a8 == 0 {
				continue
			}
			off := rowOff + (x-bounds.Min.X)*4
			out.Pix[off] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[0])))
			out.Pix[off+1] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[1])))
			out.Pix[off+2] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[2])))
			out.Pix[off+3] = a8
		}
	}
	return out, checkContext(ctx)
}

// ToNRGBA64 按完整色彩管理管线将已方向纠正的源图像导出为十六位非预乘sRGB图像，并发安全且不修改原资源
// 入参: ctx 取消Context，nil采用Background, opts 转换选项，nil采用默认值
// 返回: *image.NRGBA64 独立十六位非预乘图像, error 参数、配置、预算、转换或取消错误
func (r *ImageResource) ToNRGBA64(ctx context.Context, opts *ImageConvertOptions) (*image.NRGBA64, error) {
	ctx = normalizeContext(ctx)
	cfg, bounds, maxBytes, err := imageConvertValidate(ctx, r, opts, 8)
	if err != nil {
		return nil, err
	}
	out := image.NewNRGBA64(bounds)
	width := bounds.Dx()
	if handled, err := r.convertJXRDisplayRows(ctx, bounds, cfg, true, func(y int) []byte {
		rowOff := (y - bounds.Min.Y) * out.Stride
		return out.Pix[rowOff : rowOff+width*8]
	}, nil); handled || err != nil {
		if err != nil {
			return nil, err
		}
		return out, nil
	}
	sampler, err := prepareImageConvertSampler(r, cfg, maxBytes)
	if err != nil {
		return nil, err
	}
	var bgLinear [3]float64
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	var jxrCache jxrRowCache
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		rowOff := (y - bounds.Min.Y) * out.Stride
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			if (x-bounds.Min.X)&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
			}
			c, err := sampler.pixelColorWithCache(x, y, &jxrCache)
			if err != nil {
				return nil, err
			}
			lin, alpha, err := imageConvertLinearPixelWithBG(c, sampler.toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode)
			if err != nil {
				return nil, err
			}
			a16 := colorQuantize16(alpha)
			if a16 == 0 {
				continue
			}
			off := rowOff + (x-bounds.Min.X)*8
			binary.BigEndian.PutUint16(out.Pix[off:], colorQuantize16(renderLinearToSRGB(colorClamp(lin[0]))))
			binary.BigEndian.PutUint16(out.Pix[off+2:], colorQuantize16(renderLinearToSRGB(colorClamp(lin[1]))))
			binary.BigEndian.PutUint16(out.Pix[off+4:], colorQuantize16(renderLinearToSRGB(colorClamp(lin[2]))))
			binary.BigEndian.PutUint16(out.Pix[off+6:], a16)
		}
	}
	return out, checkContext(ctx)
}

// ToCMYK 将已方向纠正的源图像导出为八位CMYK图像，并发安全且不修改原资源
// 当源为CMYK且无外挂非CMYK配置、未启用反相及灰度单色模式时直接无损导出并附带对应CMYK ICC副本，否则经sRGB换算并返回nil配置
// 未指定Background时全透明像素输出CMYK零值（0,0,0,0），指定Background时按透明度合成背景色
// 入参: ctx 取消Context，nil采用Background, opts 转换选项，nil采用默认值
// 返回: *image.CMYK 独立八位CMYK图像, []byte 对应CMYK ICC副本或nil, error 参数、配置、预算、转换或取消错误
func (r *ImageResource) ToCMYK(ctx context.Context, opts *ImageConvertOptions) (*image.CMYK, []byte, error) {
	ctx = normalizeContext(ctx)
	cfg, bounds, maxBytes, err := imageConvertValidate(ctx, r, opts, 4)
	if err != nil {
		return nil, nil, err
	}
	direct := r.ColorSpace() == ImageColorCMYK && !cfg.Negative && cfg.ColorMode != PrintColorGrayscale && cfg.ColorMode != PrintColorMonochrome
	var directProfile []byte
	if direct {
		profileBytes := cfg.Profile
		profileLabel := "associated"
		if len(profileBytes) == 0 {
			embedded, err := imageEmbeddedProfileBytes(r.source, maxBytes)
			if err != nil {
				return nil, nil, err
			}
			profileBytes = embedded
			profileLabel = "embedded"
		}
		if len(profileBytes) > 0 {
			parsed, err := parseICCProfile(profileBytes)
			if err != nil {
				return nil, nil, err
			}
			compatible, err := imageICCCompatible(r.source, parsed)
			if err != nil {
				return nil, nil, err
			}
			if !compatible {
				return nil, nil, fmt.Errorf("%w: %s image profile channels", ErrInvalid, profileLabel)
			}
			if parsed.space == "CMYK" && parsed.class != "nmcl" {
				directProfile = bytes.Clone(profileBytes)
			} else {
				direct = false
			}
		}
	}
	if direct {
		out, err := exportDirectCMYK(ctx, r.source, bounds, cfg.Background)
		if err != nil {
			return nil, nil, err
		}
		return out, directProfile, nil
	}
	sampler, err := prepareImageConvertSampler(r, cfg, maxBytes)
	if err != nil {
		return nil, nil, err
	}
	var bgLinear [3]float64
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	out := image.NewCMYK(bounds)
	var jxrCache jxrRowCache
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		rowOff := (y - bounds.Min.Y) * out.Stride
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			if (x-bounds.Min.X)&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return nil, nil, err
				}
			}
			c, err := sampler.pixelColorWithCache(x, y, &jxrCache)
			if err != nil {
				return nil, nil, err
			}
			lin, alpha, err := imageConvertLinearPixelWithBG(c, sampler.toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode)
			if err != nil {
				return nil, nil, err
			}
			if colorQuantize8(alpha) == 0 {
				continue
			}
			r8 := colorQuantize8(renderLinearToSRGB(colorClamp(lin[0])))
			g8 := colorQuantize8(renderLinearToSRGB(colorClamp(lin[1])))
			b8 := colorQuantize8(renderLinearToSRGB(colorClamp(lin[2])))
			cv, mv, yv, kv := color.RGBToCMYK(r8, g8, b8)
			off := rowOff + (x-bounds.Min.X)*4
			out.Pix[off], out.Pix[off+1], out.Pix[off+2], out.Pix[off+3] = cv, mv, yv, kv
		}
	}
	return out, nil, checkContext(ctx)
}

// ToGray 按完整色彩管理管线与BT.709亮度规则导出已方向纠正的八位灰度图像，并发安全且不修改原资源
// 支持原生单通道灰度、外挂与内嵌ICC、CICP、BT.2446色调映射、背景合成、负片反相及黑白单色阈值模式
// 入参: ctx 取消Context，nil采用Background, opts 转换选项，nil采用默认值
// 返回: *image.Gray 独立八位灰度图像, error 参数、配置、预算、转换或取消错误
func (r *ImageResource) ToGray(ctx context.Context, opts *ImageConvertOptions) (*image.Gray, error) {
	ctx = normalizeContext(ctx)
	cfg, bounds, maxBytes, err := imageConvertValidate(ctx, r, opts, 1)
	if err != nil {
		return nil, err
	}
	sampler, err := prepareImageConvertSampler(r, cfg, maxBytes)
	if err != nil {
		return nil, err
	}
	var bgLinear [3]float64
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	out := image.NewGray(bounds)
	var jxrCache jxrRowCache
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		rowOff := (y - bounds.Min.Y) * out.Stride
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			if (x-bounds.Min.X)&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
			}
			c, err := sampler.pixelColorWithCache(x, y, &jxrCache)
			if err != nil {
				return nil, err
			}
			lin, alpha, err := imageConvertLinearPixelWithBG(c, sampler.toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode)
			if err != nil {
				return nil, err
			}
			if colorQuantize8(alpha) == 0 {
				continue
			}
			lum := colorClamp(0.2126*lin[0] + 0.7152*lin[1] + 0.0722*lin[2])
			out.Pix[rowOff+x-bounds.Min.X] = colorQuantize8(renderLinearToSRGB(lum))
		}
	}
	return out, checkContext(ctx)
}

// AlphaMask 独立导出已方向纠正源图像的八位透明度蒙版，无透明度通道时全图填充255
// 入参: ctx 取消Context，nil采用Background
// 返回: *image.Gray 独立八位Alpha通道图像, error 空资源、预算、读取或取消错误
func (r *ImageResource) AlphaMask(ctx context.Context) (*image.Gray, error) {
	ctx = normalizeContext(ctx)
	_, bounds, _, err := imageConvertValidate(ctx, r, nil, 1)
	if err != nil {
		return nil, err
	}
	mask := image.NewGray(bounds)
	width := bounds.Dx()
	if !r.HasAlpha() {
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := (y - bounds.Min.Y) * mask.Stride
			for x := range width {
				mask.Pix[rowOff+x] = 255
			}
		}
		return mask, checkContext(ctx)
	}
	source := r.source
	if source.jxr != nil {
		alphaRow := make([]float64, width)
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			if err := source.jxr.readAlphaRow(y, alphaRow); err != nil {
				return nil, err
			}
			rowOff := (y - bounds.Min.Y) * mask.Stride
			for x := range width {
				mask.Pix[rowOff+x] = colorQuantize8(alphaRow[x])
			}
		}
		return mask, checkContext(ctx)
	}
	if native := source.native; native != nil {
		stride := native.channels + 1
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := (y - bounds.Min.Y) * mask.Stride
			for x := bounds.Min.X; x < bounds.Max.X; x++ {
				at := ((y-native.bounds.Min.Y)*native.bounds.Dx() + x - native.bounds.Min.X) * stride
				if native.floating != nil {
					v := native.floating[at+native.channels]
					if !geometryFinite(v) {
						return nil, fmt.Errorf("%w: non-finite alpha sample", ErrUnsupported)
					}
					mask.Pix[rowOff+x-bounds.Min.X] = colorQuantize8(colorClamp(v))
				} else {
					mask.Pix[rowOff+x-bounds.Min.X] = colorQuantize8(float64(native.values[at+native.channels]) / 65535)
				}
			}
		}
		return mask, checkContext(ctx)
	}
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		rowOff := (y - bounds.Min.Y) * mask.Stride
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			px := imagePixel(source.pixels, x, y)
			mask.Pix[rowOff+x-bounds.Min.X] = colorQuantize8(float64(px.A) / 65535)
		}
	}
	return mask, checkContext(ctx)
}

// validateImageConvertOptions 规范化并校验色彩转换选项及预算上限
// 入参: opts 可选转换选项
// 返回: ImageConvertOptions 规范化选项, uint64 有效内存字节上限, error 选项或预算错误
func validateImageConvertOptions(opts *ImageConvertOptions) (ImageConvertOptions, uint64, error) {
	var cfg ImageConvertOptions
	if opts != nil {
		cfg = *opts
	}
	if cfg.Intent > IntentAbsoluteColorimetric || cfg.ColorMode > PrintColorMonochrome || !geometryFinite(cfg.HDRPeakNits) || cfg.HDRPeakNits < 0 {
		return ImageConvertOptions{}, 0, fmt.Errorf("%w: image convert options", ErrInvalid)
	}
	if cfg.Limits.MaxPartBytes < 0 || cfg.Limits.MaxPackageBytes < 0 || cfg.Limits.MaxMetadataBytes < 0 || cfg.Limits.MaxPartCount < 0 || cfg.Limits.MaxXMLDepth < 0 || cfg.Limits.MaxXMLNodes < 0 || cfg.Limits.MaxXMLBindings < 0 || cfg.Limits.MaxPageCount < 0 {
		return ImageConvertOptions{}, 0, fmt.Errorf("%w: negative image convert limits", ErrInvalid)
	}
	maxBytes := uint64(DefaultLimits().MaxPartBytes)
	if cfg.Limits.MaxPartBytes > 0 {
		maxBytes = uint64(cfg.Limits.MaxPartBytes)
	}
	if cfg.Limits.MaxPackageBytes > 0 && uint64(cfg.Limits.MaxPackageBytes) < maxBytes {
		maxBytes = uint64(cfg.Limits.MaxPackageBytes)
	}
	if uint64(len(cfg.Profile)) > maxBytes {
		return ImageConvertOptions{}, 0, fmt.Errorf("%w: image convert profile budget", ErrLimit)
	}
	return cfg, maxBytes, nil
}

// imageConvertValidate 校验图像导出参数、取消状态及输出缓冲与外挂配置的内存预算上限
// 入参: ctx 已规范化取消Context, r 图像资源, opts 可选转换选项, bytesPerPixel 单像素输出字节数
// 返回: ImageConvertOptions 规范化选项, image.Rectangle 图像范围, uint64 有效内存字节预算, error 参数、资源或取消错误
func imageConvertValidate(ctx context.Context, r *ImageResource, opts *ImageConvertOptions, bytesPerPixel uint64) (ImageConvertOptions, image.Rectangle, uint64, error) {
	if err := checkContext(ctx); err != nil {
		return ImageConvertOptions{}, image.Rectangle{}, 0, err
	}
	if r == nil || r.source == nil || r.source.bounds().Empty() {
		return ImageConvertOptions{}, image.Rectangle{}, 0, fmt.Errorf("%w: empty image resource", ErrInvalid)
	}
	cfg, maxBytes, err := validateImageConvertOptions(opts)
	if err != nil {
		return ImageConvertOptions{}, image.Rectangle{}, 0, err
	}
	bounds := r.source.bounds()
	w, h := bounds.Dx(), bounds.Dy()
	if w > rasterMaxDimension || h > rasterMaxDimension {
		return ImageConvertOptions{}, image.Rectangle{}, 0, fmt.Errorf("%w: image convert dimensions", ErrLimit)
	}
	pixels := uint64(w) * uint64(h)
	if pixels > maxBytes/bytesPerPixel || pixels > uint64(^uint(0)>>1)/bytesPerPixel {
		return ImageConvertOptions{}, image.Rectangle{}, 0, fmt.Errorf("%w: image convert memory budget", ErrLimit)
	}
	return cfg, bounds, maxBytes, nil
}

// imageConvertBackground 将可选背景色换算为非预乘线性sRGB三分量与八位CMYK四分量
// 入参: bg 背景色
// 返回: [3]float64 线性sRGB背景色, [4]uint8 八位CMYK背景色
func imageConvertBackground(bg color.Color) ([3]float64, [4]uint8) {
	nrgba := color.NRGBAModel.Convert(bg).(color.NRGBA)
	lin := [3]float64{
		renderSRGBToLinear(float64(nrgba.R) / 255),
		renderSRGBToLinear(float64(nrgba.G) / 255),
		renderSRGBToLinear(float64(nrgba.B) / 255),
	}
	if cmyk, ok := bg.(color.CMYK); ok {
		return lin, [4]uint8{cmyk.C, cmyk.M, cmyk.Y, cmyk.K}
	}
	c, m, y, k := color.RGBToCMYK(nrgba.R, nrgba.G, nrgba.B)
	return lin, [4]uint8{c, m, y, k}
}

// imageConvertLinearPixelWithBG 对线性scRGB预乘像素执行色调映射、可选背景合成、反相与灰度黑白转换
// 入参: c 线性scRGB预乘像素, toneMapPeak HDR色调映射峰值亮度, hasBG 是否启用背景合成, bgLinear 线性sRGB背景色, negative 是否反相, mode 打印输出色彩模式
// 返回: [3]float64 最终非预乘线性RGB分量, float64 最终归一化透明度, error 数值范围错误
func imageConvertLinearPixelWithBG(c renderColor, toneMapPeak float64, hasBG bool, bgLinear [3]float64, negative bool, mode PrintColorMode) ([3]float64, float64, error) {
	if c.a == 0 {
		if !hasBG {
			return [3]float64{}, 0, nil
		}
		lin, _, err := applyPrintLinearColor(bgLinear, negative, mode)
		if err != nil {
			return [3]float64{}, 0, err
		}
		return lin, 1, nil
	}
	lin := [3]float64{c.r / c.a, c.g / c.a, c.b / c.a}
	if toneMapPeak > 0 {
		lin = renderBT2446MethodA(lin, toneMapPeak)
	}
	alpha := colorClamp(c.a)
	if hasBG {
		inv := 1 - alpha
		lin[0] = lin[0]*alpha + bgLinear[0]*inv
		lin[1] = lin[1]*alpha + bgLinear[1]*inv
		lin[2] = lin[2]*alpha + bgLinear[2]*inv
		alpha = 1
	}
	lin, _, err := applyPrintLinearColor(lin, negative, mode)
	if err != nil {
		return [3]float64{}, 0, err
	}
	return lin, alpha, nil
}

// zeroTransparentNRGBARow 将八位NRGBA行中全透明像素的RGB分量清零，与透明黑契约对齐
// 入参: row 长度为4*width的八位NRGBA行切片
func zeroTransparentNRGBARow(row []byte) {
	for i := 0; i+3 < len(row); i += 4 {
		if row[i+3] == 0 {
			row[i], row[i+1], row[i+2] = 0, 0, 0
		}
	}
}

// zeroTransparentNRGBA64Row 将大端十六位NRGBA64行中全透明像素的RGB分量清零
// 入参: row 长度为8*width的十六位NRGBA64行切片
func zeroTransparentNRGBA64Row(row []byte) {
	for i := 0; i+7 < len(row); i += 8 {
		if row[i+6] == 0 && row[i+7] == 0 {
			clear(row[i : i+6])
		}
	}
}

// convertJXRDisplayRows 使用JXRGo原生色彩转换器逐行导出八位或十六位NRGBA行，不适用时返回false由上层回退
// 入参: ctx 已规范化取消Context, bounds 图像范围, cfg 已校验转换选项, wide 是否导出十六位NRGBA64, rowDst 返回第y行目标写入切片的回调, onRow 单行写完后的可选回调
// 返回: bool 是否已由JXRGo原生路径完成转换, error 转换、回调或取消错误
func (r *ImageResource) convertJXRDisplayRows(ctx context.Context, bounds image.Rectangle, cfg ImageConvertOptions, wide bool, rowDst func(y int) []byte, onRow func(y int, row []byte) error) (bool, error) {
	if r.source.jxr == nil {
		return false, nil
	}
	jxr := r.source.jxr
	conv, usable, err := jxrDisplayConverter(ctx, jxr.info, cfg, jxr.limits)
	if err != nil || !usable {
		return false, err
	}
	width := bounds.Dx()
	toneMapPeak := jxrExtraToneMapPeak(jxr.info, cfg)
	hasBG := cfg.Background != nil
	var bgLinear [3]float64
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	fast := !hasBG && !cfg.Negative && cfg.ColorMode == PrintColorOriginal && toneMapPeak == 0
	var linRow []float64
	if !fast {
		linRow = make([]float64, width*4)
	}
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return true, err
		}
		dstRow := rowDst(y)
		if fast {
			if wide {
				if err := conv.ConvertRowNRGBA64(ctx, jxr.raster, y, dstRow); err != nil {
					return true, jxrImageError(err)
				}
				if jxr.alpha {
					zeroTransparentNRGBA64Row(dstRow)
				}
			} else {
				if err := conv.ConvertRowNRGBA(ctx, jxr.raster, y, dstRow); err != nil {
					return true, jxrImageError(err)
				}
				if jxr.alpha {
					zeroTransparentNRGBARow(dstRow)
				}
			}
		} else {
			if err := conv.ConvertRowLinear(ctx, jxr.raster, y, linRow); err != nil {
				return true, jxrImageError(err)
			}
			if wide {
				err = finishLinearRowToNRGBA64(linRow, width, toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode, dstRow)
			} else {
				err = finishLinearRowToNRGBA(linRow, width, toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode, dstRow)
			}
			if err != nil {
				return true, err
			}
		}
		if onRow != nil {
			if err := onRow(y-bounds.Min.Y, dstRow); err != nil {
				return true, err
			}
		}
	}
	return true, checkContext(ctx)
}

// finishLinearPixel 对单像素非预乘线性RGBA执行有限性检查、色调映射、背景合成及打印色彩转换
// 入参: r, g, b, a 非预乘线性RGBA分量, toneMapPeak 额外BT.2446峰值亮度，零禁用, hasBG 是否启用背景合成, bgLinear 线性背景色, negative 是否反相, mode 打印色彩模式
// 返回: [3]float64 输出线性RGB分量, float64 输出归一化透明度, error 非有限像素或数值范围错误
func finishLinearPixel(r, g, b, a, toneMapPeak float64, hasBG bool, bgLinear [3]float64, negative bool, mode PrintColorMode) ([3]float64, float64, error) {
	if !geometryFinite(r, g, b, a) {
		return [3]float64{}, 0, fmt.Errorf("%w: non-finite linear image pixel", ErrUnsupported)
	}
	alpha := colorClamp(a)
	lin := [3]float64{r, g, b}
	if alpha == 0 {
		if !hasBG {
			return [3]float64{}, 0, nil
		}
		lin, alpha = bgLinear, 1
	} else {
		if toneMapPeak > 0 {
			lin = renderBT2446MethodA(lin, toneMapPeak)
		}
		if hasBG {
			inv := 1 - alpha
			lin[0] = lin[0]*alpha + bgLinear[0]*inv
			lin[1] = lin[1]*alpha + bgLinear[1]*inv
			lin[2] = lin[2]*alpha + bgLinear[2]*inv
			alpha = 1
		}
	}
	outLin, _, err := applyPrintLinearColor(lin, negative, mode)
	if err != nil {
		return [3]float64{}, 0, err
	}
	return outLin, alpha, nil
}

// finishLinearRowToNRGBA 将单行非预乘线性scRGB与Alpha执行可选色调映射、背景合成、反相与打印模式转换并写入八位NRGBA行
// 入参: src 长度为4*width的线性RGBA浮点行, width 像素宽度, toneMapPeak 额外BT.2446峰值亮度，零禁用, hasBG 是否启用背景合成, bgLinear 线性背景色, negative 是否反相, mode 打印色彩模式, dst 目标八位NRGBA行
// 返回: error 数值范围错误
func finishLinearRowToNRGBA(src []float64, width int, toneMapPeak float64, hasBG bool, bgLinear [3]float64, negative bool, mode PrintColorMode, dst []byte) error {
	for x := range width {
		at := x * 4
		outLin, alpha, err := finishLinearPixel(src[at], src[at+1], src[at+2], src[at+3], toneMapPeak, hasBG, bgLinear, negative, mode)
		if err != nil {
			return err
		}
		a8 := colorQuantize8(alpha)
		if a8 == 0 {
			dst[at], dst[at+1], dst[at+2], dst[at+3] = 0, 0, 0, 0
			continue
		}
		dst[at] = colorQuantize8(renderLinearToSRGB(colorClamp(outLin[0])))
		dst[at+1] = colorQuantize8(renderLinearToSRGB(colorClamp(outLin[1])))
		dst[at+2] = colorQuantize8(renderLinearToSRGB(colorClamp(outLin[2])))
		dst[at+3] = a8
	}
	return nil
}

// finishLinearRowToNRGBA64 将单行非预乘线性scRGB与Alpha执行可选色调映射、背景合成、反相与打印模式转换并写入十六位大端NRGBA64行
// 入参: src 长度为4*width的线性RGBA浮点行, width 像素宽度, toneMapPeak 额外BT.2446峰值亮度，零禁用, hasBG 是否启用背景合成, bgLinear 线性背景色, negative 是否反相, mode 打印色彩模式, dst 目标十六位NRGBA64行
// 返回: error 数值范围错误
func finishLinearRowToNRGBA64(src []float64, width int, toneMapPeak float64, hasBG bool, bgLinear [3]float64, negative bool, mode PrintColorMode, dst []byte) error {
	for x := range width {
		at := x * 4
		outOff := x * 8
		outLin, alpha, err := finishLinearPixel(src[at], src[at+1], src[at+2], src[at+3], toneMapPeak, hasBG, bgLinear, negative, mode)
		if err != nil {
			return err
		}
		a16 := colorQuantize16(alpha)
		if a16 == 0 {
			clear(dst[outOff : outOff+8])
			continue
		}
		binary.BigEndian.PutUint16(dst[outOff:], colorQuantize16(renderLinearToSRGB(colorClamp(outLin[0]))))
		binary.BigEndian.PutUint16(dst[outOff+2:], colorQuantize16(renderLinearToSRGB(colorClamp(outLin[1]))))
		binary.BigEndian.PutUint16(dst[outOff+4:], colorQuantize16(renderLinearToSRGB(colorClamp(outLin[2]))))
		binary.BigEndian.PutUint16(dst[outOff+6:], a16)
	}
	return nil
}

// exportRowsNRGBA 使用单行缓冲将已解码图像逐行色彩管理后回调给调用方，无需分配整帧NRGBA输出
// 入参: ctx 已规范化取消Context, cfg 已校验转换选项, maxBytes 内存字节预算, fn 逐行回调
// 返回: error 采样、转换、回调或取消错误
func (r *ImageResource) exportRowsNRGBA(ctx context.Context, cfg ImageConvertOptions, maxBytes uint64, fn func(y int, nrgba []byte) error) error {
	bounds := r.source.bounds()
	width := bounds.Dx()
	rowBuf := make([]byte, width*4)
	if handled, err := r.convertJXRDisplayRows(ctx, bounds, cfg, false, func(int) []byte { return rowBuf }, fn); handled || err != nil {
		return err
	}
	var bgLinear [3]float64
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, _ = imageConvertBackground(cfg.Background)
	}
	sampler, err := prepareImageConvertSampler(r, cfg, maxBytes)
	if err != nil {
		return err
	}
	var jxrCache jxrRowCache
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		if err := checkContext(ctx); err != nil {
			return err
		}
		clear(rowBuf)
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			if (x-bounds.Min.X)&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return err
				}
			}
			c, err := sampler.pixelColorWithCache(x, y, &jxrCache)
			if err != nil {
				return err
			}
			lin, alpha, err := imageConvertLinearPixelWithBG(c, sampler.toneMapPeak, hasBG, bgLinear, cfg.Negative, cfg.ColorMode)
			if err != nil {
				return err
			}
			a8 := colorQuantize8(alpha)
			if a8 == 0 {
				continue
			}
			off := (x - bounds.Min.X) * 4
			rowBuf[off] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[0])))
			rowBuf[off+1] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[1])))
			rowBuf[off+2] = colorQuantize8(renderLinearToSRGB(colorClamp(lin[2])))
			rowBuf[off+3] = a8
		}
		if err := fn(y-bounds.Min.Y, rowBuf); err != nil {
			return err
		}
	}
	return checkContext(ctx)
}

// readPNGImageInfo 仅流式读取PNG在首个IDAT之前的头部元数据块，不解压像素数据
// 入参: ctx 已规范化取消Context, stream 只读流, part 部件包根URI, media 内容类型, maxBytes 单块字节上限
// 返回: *ImageInfo 轻量图像头元数据, error 签名、块结构、CRC、预算或取消错误
func readPNGImageInfo(ctx context.Context, stream io.Reader, part, media string, maxBytes int64) (*ImageInfo, error) {
	var sig [8]byte
	if _, err := io.ReadFull(stream, sig[:]); err != nil {
		return nil, fmt.Errorf("%w: PNG signature", ErrInvalid)
	}
	if !bytes.Equal(sig[:], []byte("\x89PNG\r\n\x1a\n")) {
		return nil, fmt.Errorf("%w: PNG signature", ErrInvalid)
	}
	info := &ImageInfo{Part: part, ContentType: media, DPIX: 96, DPIY: 96, Orientation: 1}
	hasIHDR := false
	var header [8]byte
	var crcBuf [4]byte
	for {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if _, err := io.ReadFull(stream, header[:]); err != nil {
			return nil, fmt.Errorf("%w: truncated PNG chunk", ErrInvalid)
		}
		size := uint64(binary.BigEndian.Uint32(header[:4]))
		kind := string(header[4:8])
		if !hasIHDR && kind != "IHDR" {
			return nil, fmt.Errorf("%w: PNG header placement", ErrInvalid)
		}
		switch kind {
		case "IHDR":
			if hasIHDR || size != 13 {
				return nil, fmt.Errorf("%w: PNG header placement", ErrInvalid)
			}
			var payload [13]byte
			if _, err := io.ReadFull(stream, payload[:]); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG IHDR", ErrInvalid)
			}
			if _, err := io.ReadFull(stream, crcBuf[:]); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG CRC", ErrInvalid)
			}
			h := crc32.NewIEEE()
			_, _ = h.Write(header[4:8])
			_, _ = h.Write(payload[:])
			if h.Sum32() != binary.BigEndian.Uint32(crcBuf[:]) {
				return nil, fmt.Errorf("%w: PNG chunk checksum", ErrInvalid)
			}
			w := binary.BigEndian.Uint32(payload[0:4])
			ht := binary.BigEndian.Uint32(payload[4:8])
			if w == 0 || ht == 0 {
				return nil, fmt.Errorf("%w: empty PNG image", ErrInvalid)
			}
			if w > rasterMaxDimension || ht > rasterMaxDimension {
				return nil, fmt.Errorf("%w: PNG image dimensions", ErrLimit)
			}
			info.Width, info.Height = int(w), int(ht)
			info.BitDepth = int(payload[8])
			info.ColorSpace = ImageColorRGB
			switch payload[9] {
			case 0:
				info.ColorSpace = ImageColorGray
			case 2:
				info.ColorSpace = ImageColorRGB
			case 3:
				info.ColorSpace = ImageColorRGB
				info.BitDepth = 8
			case 4:
				info.ColorSpace = ImageColorGray
				info.HasAlpha = true
			case 6:
				info.ColorSpace = ImageColorRGB
				info.HasAlpha = true
			default:
				return nil, fmt.Errorf("%w: PNG color type %d", ErrInvalid, payload[9])
			}
			hasIHDR = true
		case "pHYs":
			if size != 9 {
				return nil, fmt.Errorf("%w: PNG physical dimensions", ErrInvalid)
			}
			var payload [9]byte
			if _, err := io.ReadFull(stream, payload[:]); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG pHYs", ErrInvalid)
			}
			if _, err := io.ReadFull(stream, crcBuf[:]); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG CRC", ErrInvalid)
			}
			h := crc32.NewIEEE()
			_, _ = h.Write(header[4:8])
			_, _ = h.Write(payload[:])
			if h.Sum32() != binary.BigEndian.Uint32(crcBuf[:]) {
				return nil, fmt.Errorf("%w: PNG chunk checksum", ErrInvalid)
			}
			if payload[8] > 1 {
				return nil, fmt.Errorf("%w: PNG physical dimensions", ErrInvalid)
			}
			x, y := binary.BigEndian.Uint32(payload[0:4]), binary.BigEndian.Uint32(payload[4:8])
			if payload[8] == 1 {
				if x == 0 || y == 0 {
					return nil, fmt.Errorf("%w: zero PNG resolution", ErrInvalid)
				}
				info.DPIX, info.DPIY = float64(x)*0.0254, float64(y)*0.0254
			} else if x != 0 && y != 0 {
				info.DPIX, info.DPIY = 96, 96*(float64(y)/float64(x))
			}
		case "tRNS":
			info.HasAlpha = true
			if _, err := io.CopyN(io.Discard, stream, int64(size)+4); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG tRNS", ErrInvalid)
			}
		case "iCCP":
			info.HasICCProfile = true
			if _, err := io.CopyN(io.Discard, stream, int64(size)+4); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG iCCP", ErrInvalid)
			}
		case "cICP":
			if size != 4 {
				return nil, fmt.Errorf("%w: PNG cICP chunk", ErrInvalid)
			}
			info.HasCICP = true
			if _, err := io.CopyN(io.Discard, stream, int64(size)+4); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG cICP", ErrInvalid)
			}
		case "IDAT":
			return info, checkContext(ctx)
		case "IEND":
			return nil, fmt.Errorf("%w: PNG missing IDAT", ErrInvalid)
		default:
			if maxBytes > 0 && size > uint64(maxBytes) {
				return nil, fmt.Errorf("%w: PNG chunk size", ErrLimit)
			}
			if _, err := io.CopyN(io.Discard, stream, int64(size)+4); err != nil {
				return nil, fmt.Errorf("%w: truncated PNG chunk payload", ErrInvalid)
			}
		}
	}
}

// readJPEGImageInfo 仅流式扫描JPEG标记段至首个SOS或EOI即停止，不解码熵编码图像流
// 入参: ctx 已规范化取消Context, stream 只读流, part 部件包根URI, media 内容类型
// 返回: *ImageInfo 视觉方向规范化后的图像头元数据, error 标记、元数据或取消错误
func readJPEGImageInfo(ctx context.Context, stream io.Reader, part, media string) (*ImageInfo, error) {
	var soi [2]byte
	if _, err := io.ReadFull(stream, soi[:]); err != nil || soi[0] != 0xff || soi[1] != 0xd8 {
		return nil, fmt.Errorf("%w: JPEG signature", ErrInvalid)
	}
	info := &ImageInfo{Part: part, ContentType: media, DPIX: 96, DPIY: 96, Orientation: 1}
	hasFrame := false
	var exifDPI Point
	hasExif, exifAbsolute, jfifAbsolute, hasOrient := false, false, false, false
	var single [1]byte
	var lengthBuf [2]byte
	for {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if _, err := io.ReadFull(stream, single[:]); err != nil {
			return nil, fmt.Errorf("%w: truncated JPEG", ErrInvalid)
		}
		if single[0] != 0xff {
			return nil, fmt.Errorf("%w: JPEG marker", ErrInvalid)
		}
		for single[0] == 0xff {
			if _, err := io.ReadFull(stream, single[:]); err != nil {
				return nil, fmt.Errorf("%w: truncated JPEG marker", ErrInvalid)
			}
		}
		marker := single[0]
		if marker == 0xd9 || marker == 0xda {
			break
		}
		if marker == 0x01 || marker >= 0xd0 && marker <= 0xd7 {
			continue
		}
		if _, err := io.ReadFull(stream, lengthBuf[:]); err != nil {
			return nil, fmt.Errorf("%w: truncated JPEG marker length", ErrInvalid)
		}
		size := int(binary.BigEndian.Uint16(lengthBuf[:]))
		if size < 2 {
			return nil, fmt.Errorf("%w: JPEG marker length", ErrInvalid)
		}
		payloadLen := size - 2
		needPayload := marker >= 0xc0 && marker <= 0xcf && marker != 0xc4 && marker != 0xc8 && marker != 0xcc || marker == 0xe0 || marker == 0xe1 || marker == 0xe2
		if !needPayload {
			if _, err := io.CopyN(io.Discard, stream, int64(payloadLen)); err != nil {
				return nil, fmt.Errorf("%w: truncated JPEG segment", ErrInvalid)
			}
			continue
		}
		payload := make([]byte, payloadLen)
		if _, err := io.ReadFull(stream, payload); err != nil {
			return nil, fmt.Errorf("%w: truncated JPEG segment", ErrInvalid)
		}
		switch {
		case marker >= 0xc0 && marker <= 0xcf && marker != 0xc4 && marker != 0xc8 && marker != 0xcc:
			if len(payload) < 6 || hasFrame {
				return nil, fmt.Errorf("%w: JPEG frame metadata", ErrInvalid)
			}
			h := int(binary.BigEndian.Uint16(payload[1:3]))
			w := int(binary.BigEndian.Uint16(payload[3:5]))
			if w == 0 || h == 0 {
				return nil, fmt.Errorf("%w: empty JPEG image", ErrInvalid)
			}
			if w > rasterMaxDimension || h > rasterMaxDimension {
				return nil, fmt.Errorf("%w: JPEG image dimensions", ErrLimit)
			}
			info.Width, info.Height = w, h
			info.BitDepth = int(payload[0])
			switch payload[5] {
			case 0:
				return nil, fmt.Errorf("%w: JPEG frame component count", ErrInvalid)
			case 1:
				info.ColorSpace = ImageColorGray
			case 3:
				info.ColorSpace = ImageColorRGB
			case 4:
				info.ColorSpace = ImageColorCMYK
			default:
				info.ColorSpace = ImageColorMultiChannel
			}
			hasFrame = true
		case marker == 0xe0 && bytes.HasPrefix(payload, []byte("JFIF\x00")):
			if len(payload) < 14 {
				return nil, fmt.Errorf("%w: truncated JFIF", ErrInvalid)
			}
			unit, x, y := payload[7], binary.BigEndian.Uint16(payload[8:]), binary.BigEndian.Uint16(payload[10:])
			if unit > 2 || x == 0 || y == 0 {
				return nil, fmt.Errorf("%w: JFIF density", ErrInvalid)
			}
			if unit == 0 {
				info.DPIX, info.DPIY = 96, 96*(float64(y)/float64(x))
				jfifAbsolute = false
			} else {
				factor := 1.0
				if unit == 2 {
					factor = 2.54
				}
				info.DPIX, info.DPIY = float64(x)*factor, float64(y)*factor
				jfifAbsolute = true
			}
		case marker == 0xe1 && bytes.HasPrefix(payload, []byte("Exif\x00\x00")):
			value, present, absolute, orientation, hasOrientation, err := exifImageMetadata(payload[6:])
			if err != nil {
				return nil, err
			}
			if present {
				if hasExif && (exifDPI != value || exifAbsolute != absolute) {
					return nil, fmt.Errorf("%w: conflicting EXIF resolution", ErrInvalid)
				}
				exifDPI, hasExif, exifAbsolute = value, true, absolute
			}
			if hasOrientation {
				if hasOrient && info.Orientation != orientation {
					return nil, fmt.Errorf("%w: conflicting EXIF orientation", ErrInvalid)
				}
				info.Orientation, hasOrient = orientation, true
			}
		case marker == 0xe2 && bytes.HasPrefix(payload, []byte("ICC_PROFILE\x00")):
			if len(payload) <= 14 {
				return nil, fmt.Errorf("%w: JPEG ICC fragment header", ErrInvalid)
			}
			info.HasICCProfile = true
		}
	}
	if !hasFrame {
		return nil, fmt.Errorf("%w: missing JPEG frame header", ErrInvalid)
	}
	if hasExif && (exifAbsolute || !jfifAbsolute) {
		info.DPIX, info.DPIY = exifDPI.X, exifDPI.Y
	}
	if info.Orientation >= 5 && info.Orientation <= 8 {
		info.Width, info.Height = info.Height, info.Width
		info.DPIX, info.DPIY = info.DPIY, info.DPIX
	}
	return info, checkContext(ctx)
}

// imageEmbeddedProfileBytes 在预算内提取源图像内嵌ICC的未压缩字节视图，不修改源图像状态
// 入参: source 只读栅格图像, maxBytes 允许的最大字节预算
// 返回: []byte 未压缩ICC字节，无内嵌时为nil, error 解压或预算错误
func imageEmbeddedProfileBytes(source *rasterImage, maxBytes uint64) ([]byte, error) {
	if source == nil || len(source.profile) == 0 {
		return nil, nil
	}
	if source.profileCompressed {
		limit := int64(min(maxBytes, uint64(DefaultLimits().MaxPartBytes)))
		return inflatePNGProfile(source.profile, limit)
	}
	if uint64(len(source.profile)) > maxBytes {
		return nil, fmt.Errorf("%w: embedded image profile budget", ErrLimit)
	}
	return source.profile, nil
}

// prepareImageConvertSampler 在源图像的浅拷贝只读视图上构建色彩管理采样器，不修改原ImageResource状态
// 入参: r 只读图像资源, cfg 已校验转换选项, maxBytes 内存字节上限
// 返回: *imageSampler 线性scRGB输出采样器, error 配置解析、通道不匹配或管线错误
func prepareImageConvertSampler(r *ImageResource, cfg ImageConvertOptions, maxBytes uint64) (*imageSampler, error) {
	view := *r.source
	if !geometryFinite(view.dpi.X, view.dpi.Y) || view.dpi.X <= 0 || view.dpi.Y <= 0 {
		view.dpi = Point{96, 96}
	}
	if len(cfg.Profile) > 0 {
		profile, err := parseICCProfile(bytes.Clone(cfg.Profile))
		if err != nil {
			return nil, err
		}
		compatible, err := imageICCCompatible(&view, profile)
		if err != nil {
			return nil, err
		}
		if !compatible {
			return nil, fmt.Errorf("%w: associated image profile channels", ErrInvalid)
		}
		iccIntent := imageICCIntent(profile)
		if cfg.Intent != IntentDefault {
			iccIntent = uint32(cfg.Intent - 1)
		}
		transform, err := prepareICCTransform(profile, iccIntent)
		if err != nil {
			return nil, err
		}
		view.transform = transform
		view.selectedProfile = profile
		view.associatedProfile = true
		view.profile = nil
		view.profileCompressed = false
	} else if !(view.jxr == nil && imageCICPUsable(view.cicp)) && len(view.profile) > 0 {
		embedded, err := imageEmbeddedProfileBytes(&view, maxBytes)
		if err != nil {
			return nil, err
		}
		profile, err := parseICCProfile(embedded)
		if err != nil {
			return nil, err
		}
		iccIntent := imageICCIntent(profile)
		if cfg.Intent != IntentDefault {
			iccIntent = uint32(cfg.Intent - 1)
		}
		transform, err := prepareICCTransform(profile, iccIntent)
		if err != nil {
			return nil, err
		}
		if !imageProfileCompatible(&view, transform) {
			return nil, fmt.Errorf("%w: embedded image profile channels", ErrInvalid)
		}
		view.transform = transform
		view.selectedProfile = nil
		view.associatedProfile = false
	}
	bounds := view.bounds()
	brush := Brush{
		Kind:     BrushImage,
		Opacity:  1,
		Viewbox:  Rect{Width: float64(bounds.Dx()) * 96 / view.dpi.X, Height: float64(bounds.Dy()) * 96 / view.dpi.Y},
		Viewport: Rect{Width: float64(bounds.Dx()), Height: float64(bounds.Dy())},
	}
	return newImageSampler(&brush, &view, IdentityMatrix(), renderScRGB, false, cfg.Intent, cfg.HDRPeakNits)
}

// exportDirectCMYK 直接无损导出已方向纠正的原生CMYK样本为八位CMYK图像，支持JXR整数行快路径、透明清零与背景合成
// 入参: ctx 已规范化取消Context, source 只读CMYK栅格图像, bounds 图像范围, background 可选合成背景色
// 返回: *image.CMYK 独立八位CMYK图像, error 采样、数值或取消错误
func exportDirectCMYK(ctx context.Context, source *rasterImage, bounds image.Rectangle, background color.Color) (*image.CMYK, error) {
	out := image.NewCMYK(bounds)
	width := bounds.Dx()
	hasBG := background != nil
	var bgCMYK [4]uint8
	if hasBG {
		_, bgCMYK = imageConvertBackground(background)
	}
	blendCMYK := func(dst []byte, c, m, y, k, alpha uint8) {
		if alpha == 255 {
			dst[0], dst[1], dst[2], dst[3] = c, m, y, k
			return
		}
		if alpha == 0 {
			if hasBG {
				dst[0], dst[1], dst[2], dst[3] = bgCMYK[0], bgCMYK[1], bgCMYK[2], bgCMYK[3]
			} else {
				dst[0], dst[1], dst[2], dst[3] = 0, 0, 0, 0
			}
			return
		}
		if !hasBG {
			dst[0], dst[1], dst[2], dst[3] = c, m, y, k
			return
		}
		a := float64(alpha) / 255
		inv := 1 - a
		dst[0] = colorQuantize8((float64(c)*a + float64(bgCMYK[0])*inv) / 255)
		dst[1] = colorQuantize8((float64(m)*a + float64(bgCMYK[1])*inv) / 255)
		dst[2] = colorQuantize8((float64(y)*a + float64(bgCMYK[2])*inv) / 255)
		dst[3] = colorQuantize8((float64(k)*a + float64(bgCMYK[3])*inv) / 255)
	}
	if src, ok := source.pixels.(*image.CMYK); ok {
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			sOff := src.PixOffset(bounds.Min.X, y)
			dOff := out.PixOffset(bounds.Min.X, y)
			copy(out.Pix[dOff:dOff+width*4], src.Pix[sOff:sOff+width*4])
		}
		return out, checkContext(ctx)
	}
	if source.jxr != nil {
		if !source.jxr.alpha {
			fastOK := true
			for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
				rowOff := (y - bounds.Min.Y) * out.Stride
				if err := source.jxr.raster.ReadRowCMYK(y, out.Pix[rowOff:rowOff+width*4]); err != nil {
					if y == bounds.Min.Y && errors.Is(err, jxrgo.ErrUnsupported) {
						fastOK = false
						break
					}
					return nil, jxrImageError(err)
				}
			}
			if fastOK {
				return out, checkContext(ctx)
			}
		} else {
			fastOK := true
			cmykRow := make([]byte, width*4)
			alphaRow := make([]byte, width)
			for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
				if err := source.jxr.raster.ReadRowCMYKAlpha(y, cmykRow, alphaRow); err != nil {
					if y == bounds.Min.Y && errors.Is(err, jxrgo.ErrUnsupported) {
						fastOK = false
						break
					}
					return nil, jxrImageError(err)
				}
				rowOff := (y - bounds.Min.Y) * out.Stride
				for x := range width {
					at := x * 4
					blendCMYK(out.Pix[rowOff+at:rowOff+at+4], cmykRow[at], cmykRow[at+1], cmykRow[at+2], cmykRow[at+3], alphaRow[x])
				}
			}
			if fastOK {
				return out, checkContext(ctx)
			}
		}
		var jxrCache jxrRowCache
		var components [iccMaxChannels]float64
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := (y - bounds.Min.Y) * out.Stride
			for x := bounds.Min.X; x < bounds.Max.X; x++ {
				if (x-bounds.Min.X)&1023 == 0 {
					if err := checkContext(ctx); err != nil {
						return nil, err
					}
				}
				alpha, err := jxrCache.sample(source.jxr, x, y, components[:], jxrSampleNative, jxrLinearKey{})
				if err != nil {
					return nil, err
				}
				for ch := range 4 {
					if !geometryFinite(components[ch]) {
						return nil, fmt.Errorf("%w: non-finite CMYK sample", ErrUnsupported)
					}
				}
				off := rowOff + (x-bounds.Min.X)*4
				a8 := uint8(255)
				if source.jxr.alpha {
					a8 = colorQuantize8(colorClamp(alpha))
				}
				blendCMYK(out.Pix[off:off+4], colorQuantize8(components[0]), colorQuantize8(components[1]), colorQuantize8(components[2]), colorQuantize8(components[3]), a8)
			}
		}
		return out, checkContext(ctx)
	}
	if native := source.native; native != nil {
		stride := native.channels
		if native.alpha {
			stride++
		}
		for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := (y - bounds.Min.Y) * out.Stride
			for x := bounds.Min.X; x < bounds.Max.X; x++ {
				if (x-bounds.Min.X)&1023 == 0 {
					if err := checkContext(ctx); err != nil {
						return nil, err
					}
				}
				at := ((y-native.bounds.Min.Y)*native.bounds.Dx() + x - native.bounds.Min.X) * stride
				off := rowOff + (x-bounds.Min.X)*4
				a8 := uint8(255)
				if native.floating != nil {
					if native.alpha {
						av := native.floating[at+native.channels]
						if !geometryFinite(av) {
							return nil, fmt.Errorf("%w: non-finite CMYK alpha", ErrUnsupported)
						}
						a8 = colorQuantize8(colorClamp(av))
					}
					var c4 [4]uint8
					for ch := range 4 {
						v := native.floating[at+ch]
						if !geometryFinite(v) {
							return nil, fmt.Errorf("%w: non-finite CMYK sample", ErrUnsupported)
						}
						c4[ch] = colorQuantize8(v)
					}
					blendCMYK(out.Pix[off:off+4], c4[0], c4[1], c4[2], c4[3], a8)
				} else {
					if native.alpha {
						a8 = colorQuantize8(float64(native.values[at+native.channels]) / 65535)
					}
					blendCMYK(
						out.Pix[off:off+4],
						colorQuantize8(float64(native.values[at])/65535),
						colorQuantize8(float64(native.values[at+1])/65535),
						colorQuantize8(float64(native.values[at+2])/65535),
						colorQuantize8(float64(native.values[at+3])/65535),
						a8,
					)
				}
			}
		}
		return out, checkContext(ctx)
	}
	return nil, fmt.Errorf("%w: unavailable CMYK source pixels", ErrUnsupported)
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
	value := imagePixel(source.pixels, x, y)
	components[0] = float64(value.R) / 65535
	if r.Channels() == 3 {
		components[1], components[2] = float64(value.G)/65535, float64(value.B)/65535
	}
	return float64(value.A) / 65535, nil
}

// pngImageMetadata 读取分辨率、CICP色彩编码、sRGB、HDR亮度块、内嵌配置文件与gAMA/cHRM，按PNG第三版规则校验块顺序与优先级
// 入参: data 完整PNG数据
// 返回: rasterMetadata 图像元数据, error 数据或资源错误
func pngImageMetadata(data []byte) (rasterMetadata, error) {
	metadata := rasterMetadata{dpi: Point{96, 96}, orientation: 1}
	if !bytes.HasPrefix(data, []byte("\x89PNG\r\n\x1a\n")) {
		return rasterMetadata{}, fmt.Errorf("%w: PNG signature", ErrInvalid)
	}
	seen := false
	profileSeen, srgbSeen, cicpSeen, gamaSeen, chrmSeen, mdcvSeen, clliSeen, paletteSeen, imageSeen := false, false, false, false, false, false, false, false, false
	var gammaChroma imageGammaChroma
	var mdcvMaxNits, clliMaxNits float64
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
			bitDepth := int(chunk[12])
			metadata.channels = 3
			metadata.colorSpace = ImageColorRGB
			metadata.bitDepth = bitDepth
			switch chunk[13] {
			case 0:
				metadata.channels = 1
				metadata.colorSpace = ImageColorGray
			case 3:
				metadata.bitDepth = 8
			case 4:
				metadata.channels = 1
				metadata.colorSpace = ImageColorGray
				metadata.hasAlpha = true
			case 6:
				metadata.hasAlpha = true
			}
		case "PLTE":
			paletteSeen = true
		case "tRNS":
			metadata.hasAlpha = true
		case "IDAT":
			imageSeen = true
		case "cICP":
			if cicpSeen || paletteSeen || imageSeen || size != 4 || chunk[7] > 1 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cICP chunk", ErrInvalid)
			}
			cicpSeen = true
			metadata.cicp = &imageCICP{primaries: chunk[4], transfer: chunk[5], matrix: chunk[6], fullRange: chunk[7] == 1}
		case "mDCV":
			if mdcvSeen || paletteSeen || imageSeen || size != 24 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG mDCV chunk", ErrInvalid)
			}
			for i := range 4 {
				cx := binary.BigEndian.Uint16(chunk[4+i*4:])
				cy := binary.BigEndian.Uint16(chunk[6+i*4:])
				if cx > 50000 || cy > 50000 || uint32(cx)+uint32(cy) > 50000 {
					return rasterMetadata{}, fmt.Errorf("%w: PNG mDCV chromaticity", ErrInvalid)
				}
			}
			maxLum := binary.BigEndian.Uint32(chunk[20:])
			minLum := binary.BigEndian.Uint32(chunk[24:])
			if minLum > maxLum || maxLum > 0 && minLum == maxLum {
				return rasterMetadata{}, fmt.Errorf("%w: PNG mDCV luminance", ErrInvalid)
			}
			mdcvSeen = true
			if maxLum > 0 {
				mdcvMaxNits = float64(maxLum) / 10000
			}
		case "cLLI":
			if clliSeen || paletteSeen || imageSeen || size != 8 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cLLI chunk", ErrInvalid)
			}
			maxCLL := binary.BigEndian.Uint32(chunk[4:])
			maxFALL := binary.BigEndian.Uint32(chunk[8:])
			if maxCLL > 0 && maxFALL > maxCLL {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cLLI luminance", ErrInvalid)
			}
			clliSeen = true
			if maxCLL > 0 {
				clliMaxNits = float64(maxCLL) / 10000
			}
		case "pHYs":
			if seen || imageSeen || size != 9 || chunk[12] > 1 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG physical dimensions", ErrInvalid)
			}
			seen = true
			x, y := binary.BigEndian.Uint32(chunk[4:]), binary.BigEndian.Uint32(chunk[8:])
			if chunk[12] == 1 {
				if x == 0 || y == 0 {
					return rasterMetadata{}, fmt.Errorf("%w: zero PNG resolution", ErrInvalid)
				}
				metadata.dpi = Point{float64(x) * 0.0254, float64(y) * 0.0254}
			} else if x != 0 && y != 0 {
				metadata.dpi = Point{96, 96 * (float64(y) / float64(x))}
			}
		case "iCCP":
			if profileSeen || srgbSeen || paletteSeen || imageSeen {
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
			if profileSeen || srgbSeen || paletteSeen || imageSeen || size != 1 || chunk[4] > 3 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG sRGB chunk", ErrInvalid)
			}
			srgbSeen = true
			metadata.srgb = true
		case "gAMA":
			if gamaSeen || paletteSeen || imageSeen || size != 4 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG gAMA chunk", ErrInvalid)
			}
			raw := binary.BigEndian.Uint32(chunk[4:])
			if raw == 0 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG gAMA zero value", ErrInvalid)
			}
			gamaSeen = true
			gammaChroma.hasGamma = true
			gammaChroma.gamma = float64(raw) / 100000
		case "cHRM":
			if chrmSeen || paletteSeen || imageSeen || size != 32 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cHRM chunk", ErrInvalid)
			}
			wx := float64(binary.BigEndian.Uint32(chunk[4:])) / 100000
			wy := float64(binary.BigEndian.Uint32(chunk[8:])) / 100000
			rx := float64(binary.BigEndian.Uint32(chunk[12:])) / 100000
			ry := float64(binary.BigEndian.Uint32(chunk[16:])) / 100000
			gx := float64(binary.BigEndian.Uint32(chunk[20:])) / 100000
			gy := float64(binary.BigEndian.Uint32(chunk[24:])) / 100000
			bx := float64(binary.BigEndian.Uint32(chunk[28:])) / 100000
			by := float64(binary.BigEndian.Uint32(chunk[32:])) / 100000
			if !(wx > 0 && wy > 0 && wx+wy < 1 && rx >= 0 && ry > 0 && rx+ry <= 1 && gx >= 0 && gy > 0 && gx+gy <= 1 && bx >= 0 && by > 0 && bx+by <= 1) {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cHRM coordinates", ErrInvalid)
			}
			if math.Abs((rx-bx)*(gy-by)-(gx-bx)*(ry-by)) <= 1e-9 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cHRM degenerate primaries", ErrInvalid)
			}
			_, kr, kb, ok := cicpChromaticityToSRGB([3][2]float64{{rx, ry}, {gx, gy}, {bx, by}}, [2]float64{wx, wy})
			if !ok || kr <= 0 || kb <= 0 || 1-kr-kb <= 0 {
				return rasterMetadata{}, fmt.Errorf("%w: PNG cHRM chromaticity", ErrInvalid)
			}
			chrmSeen = true
			gammaChroma.hasChrm = true
			gammaChroma.whiteX, gammaChroma.whiteY = wx, wy
			gammaChroma.redX, gammaChroma.redY = rx, ry
			gammaChroma.greenX, gammaChroma.greenY = gx, gy
			gammaChroma.blueX, gammaChroma.blueY = bx, by
		case "IEND":
			if size != 0 || pos+12 != uint64(len(data)) {
				return rasterMetadata{}, fmt.Errorf("%w: PNG ending", ErrInvalid)
			}
			if clliMaxNits > 0 {
				metadata.hdrPeakNits = clliMaxNits
			} else if mdcvMaxNits > 0 {
				metadata.hdrPeakNits = mdcvMaxNits
			}
			if !imageCICPUsable(metadata.cicp) && !profileSeen && !srgbSeen && (gamaSeen || chrmSeen) {
				gc := gammaChroma
				metadata.gammaChroma = &gc
			}
			return metadata, nil
		}
		pos += size + 12
	}
	return rasterMetadata{}, fmt.Errorf("%w: missing PNG ending", ErrInvalid)
}

// jpegImageMetadata 按绝对物理单位EXIF优先于JFIF解析分辨率与方向，并按片段序号合并内嵌ICC配置文件
// 入参: data 完整JPEG数据, maxProfileBytes 配置文件字节上限
// 返回: rasterMetadata 图像元数据, error 标记、元数据或资源错误
func jpegImageMetadata(data []byte, maxProfileBytes int64) (rasterMetadata, error) {
	if !bytes.HasPrefix(data, []byte{0xff, 0xd8}) {
		return rasterMetadata{}, fmt.Errorf("%w: JPEG signature", ErrInvalid)
	}
	metadata := rasterMetadata{dpi: Point{96, 96}, orientation: 1}
	var exif Point
	hasExif, exifAbsolute, jfifAbsolute, hasOrient := false, false, false, false
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
			if hasExif && (exifAbsolute || !jfifAbsolute) {
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
			metadata.bitDepth = int(payload[0])
			metadata.channels = int(payload[5])
			metadata.jpegProcess = marker
			switch metadata.channels {
			case 1:
				metadata.colorSpace = ImageColorGray
			case 3:
				metadata.colorSpace = ImageColorRGB
			case 4:
				metadata.colorSpace = ImageColorCMYK
			}
		case marker == 0xe0 && bytes.HasPrefix(payload, []byte("JFIF\x00")):
			if len(payload) < 14 {
				return rasterMetadata{}, fmt.Errorf("%w: truncated JFIF", ErrInvalid)
			}
			metadata.jpegJFIF = true
			unit, x, y := payload[7], binary.BigEndian.Uint16(payload[8:]), binary.BigEndian.Uint16(payload[10:])
			if unit > 2 || x == 0 || y == 0 {
				return rasterMetadata{}, fmt.Errorf("%w: JFIF density", ErrInvalid)
			}
			if unit == 0 {
				metadata.dpi = Point{96, 96 * (float64(y) / float64(x))}
				jfifAbsolute = false
			} else {
				factor := 1.0
				if unit == 2 {
					factor = 2.54
				}
				metadata.dpi = Point{float64(x) * factor, float64(y) * factor}
				jfifAbsolute = true
			}
		case marker == 0xee && len(payload) >= 12 && bytes.HasPrefix(payload, []byte("Adobe")):
			metadata.jpegAdobe = true
			metadata.jpegAdobeTransform = payload[11]
		case marker == 0xe1 && bytes.HasPrefix(payload, []byte("Exif\x00\x00")):
			value, present, absolute, orientation, hasOrientation, err := exifImageMetadata(payload[6:])
			if err != nil {
				return rasterMetadata{}, err
			}
			if present {
				if hasExif && (exif != value || exifAbsolute != absolute) {
					return rasterMetadata{}, fmt.Errorf("%w: conflicting EXIF resolution", ErrInvalid)
				}
				exif, hasExif, exifAbsolute = value, true, absolute
			}
			if hasOrientation {
				if hasOrient && metadata.orientation != orientation {
					return rasterMetadata{}, fmt.Errorf("%w: conflicting EXIF orientation", ErrInvalid)
				}
				metadata.orientation, hasOrient = orientation, true
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

// exifImageMetadata 从EXIF首个图像目录读取分辨率、绝对物理单位标志与方向Tag 274
// 入参: data 去除EXIF前缀的TIFF数据
// 返回: Point 分辨率, bool 是否指定分辨率, bool 是否具备绝对物理单位, uint32 方向编号, bool 是否声明方向, error 目录或数值错误
func exifImageMetadata(data []byte) (Point, bool, bool, uint32, bool, error) {
	invalid := fmt.Errorf("%w: EXIF resolution metadata", ErrInvalid)
	if len(data) < 8 {
		return Point{}, false, false, 0, false, invalid
	}
	var order binary.ByteOrder
	switch string(data[:2]) {
	case "II":
		order = binary.LittleEndian
	case "MM":
		order = binary.BigEndian
	default:
		return Point{}, false, false, 0, false, invalid
	}
	if order.Uint16(data[2:]) != 42 {
		return Point{}, false, false, 0, false, invalid
	}
	pos := uint64(order.Uint32(data[4:]))
	if pos < 8 || pos > uint64(len(data))-2 {
		return Point{}, false, false, 0, false, invalid
	}
	count := uint64(order.Uint16(data[pos:]))
	if count*12+6 > uint64(len(data))-pos {
		return Point{}, false, false, 0, false, invalid
	}
	dpi := Point{}
	unit := uint16(2)
	seen := [3]bool{}
	hasColor := false
	orientation := uint32(0)
	seenOrient := false
	for i := uint64(0); i < count; i++ {
		entry := data[pos+2+12*i : pos+14+12*i]
		tag := order.Uint16(entry)
		if tag == 274 {
			if seenOrient || order.Uint16(entry[2:]) != 3 || order.Uint32(entry[4:]) != 1 {
				return Point{}, false, false, 0, false, invalid
			}
			value := uint32(order.Uint16(entry[8:]))
			if value < 1 || value > 8 {
				return Point{}, false, false, 0, false, invalid
			}
			orientation, seenOrient = value, true
			continue
		}
		if tag == 34665 {
			if hasColor || order.Uint16(entry[2:]) != 4 || order.Uint32(entry[4:]) != 1 {
				return Point{}, false, false, 0, false, invalid
			}
			hasColor = true
			offset := uint64(order.Uint32(entry[8:]))
			if offset == pos {
				return Point{}, false, false, 0, false, invalid
			}
			if err := exifImageColor(data, order, offset); err != nil {
				return Point{}, false, false, 0, false, err
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
			return Point{}, false, false, 0, false, invalid
		}
		seen[index] = true
		if tag == 296 {
			if order.Uint16(entry[2:]) != 3 {
				return Point{}, false, false, 0, false, invalid
			}
			unit = order.Uint16(entry[8:])
			continue
		}
		if order.Uint16(entry[2:]) != 5 {
			return Point{}, false, false, 0, false, invalid
		}
		offset := uint64(order.Uint32(entry[8:]))
		if offset > uint64(len(data))-8 {
			return Point{}, false, false, 0, false, invalid
		}
		n, d := order.Uint32(data[offset:]), order.Uint32(data[offset+4:])
		if n == 0 || d == 0 {
			return Point{}, false, false, 0, false, invalid
		}
		if tag == 282 {
			dpi.X = float64(n) / float64(d)
		} else {
			dpi.Y = float64(n) / float64(d)
		}
	}
	if unit < 1 || unit > 3 || seen[0] != seen[1] {
		return Point{}, false, false, 0, false, invalid
	}
	if !seen[0] {
		return Point{}, false, false, orientation, seenOrient, nil
	}
	if unit == 1 {
		return Point{96, 96 * (dpi.Y / dpi.X)}, true, false, orientation, seenOrient, nil
	}
	if unit == 3 {
		dpi.X *= 2.54
		dpi.Y *= 2.54
	}
	return dpi, true, true, orientation, seenOrient, nil
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
	if brush.ImageProfileURI == "" && (source.jxr == nil && imageCICPUsable(source.cicp) || len(source.profile) == 0) {
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
	if transform == nil && (source.jxr != nil || !imageCICPUsable(source.cicp)) && len(source.profile) != 0 {
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
	if source.transform != nil || source.selectedProfile != nil || source.jxr == nil && imageCICPUsable(source.cicp) || len(source.profile) == 0 {
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
				if kind[0]&32 == 0 || kind[3]&32 == 0 && !slices.Contains([]string{"tRNS", "cHRM", "gAMA", "iCCP", "sBIT", "sRGB", "cICP", "mDCv", "cLLi", "mDCV", "cLLI", "bKGD", "hIST", "pHYs", "sPLT", "tIME"}, string(kind)) {
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

// resolveLosslessJPEGColor 按APP14、APP0及帧分量标识确定无损JPEG色彩空间
// 入参: components 已校验为1、3或4的分量数, ids 帧分量标识, jfif 是否存在APP0 JFIF, adobe 是否存在APP14 Adobe, transform Adobe色彩变换码
// 返回: losslessJPEGColor 色彩空间类型, error 未支持的色彩解释错误
func resolveLosslessJPEGColor(components int, ids [4]byte, jfif, adobe bool, transform byte) (losslessJPEGColor, error) {
	switch components {
	case 1:
		return losslessColorGray, nil
	case 3:
		three := [3]byte{ids[0], ids[1], ids[2]}
		if adobe {
			switch transform {
			case 0:
				if three != [3]byte{'R', 'G', 'B'} && three != [3]byte{1, 2, 3} {
					return 0, fmt.Errorf("%w: unspecified lossless JPEG RGB component mapping", ErrUnsupported)
				}
				return losslessColorRGB, nil
			case 1:
				if three != [3]byte{1, 2, 3} && three != [3]byte{'Y', 'C', 'c'} {
					return 0, fmt.Errorf("%w: unspecified lossless JPEG YCbCr component mapping", ErrUnsupported)
				}
				return losslessColorYCbCr, nil
			default:
				return 0, fmt.Errorf("%w: lossless JPEG Adobe color transform %d", ErrUnsupported, transform)
			}
		}
		if jfif {
			if three != [3]byte{1, 2, 3} && three != [3]byte{'R', 'G', 'B'} {
				return 0, fmt.Errorf("%w: unspecified lossless JPEG JFIF component mapping", ErrUnsupported)
			}
			return losslessColorYCbCr, nil
		}
		if three == [3]byte{'R', 'G', 'B'} || three == [3]byte{1, 2, 3} {
			return losslessColorRGB, nil
		}
		return 0, fmt.Errorf("%w: unspecified lossless JPEG RGB component mapping", ErrUnsupported)
	default:
		if !adobe {
			return 0, fmt.Errorf("%w: lossless JPEG color component interpretation", ErrUnsupported)
		}
		switch transform {
		case 0:
			return losslessColorCMYK, nil
		case 2:
			return losslessColorYCCK, nil
		default:
			return 0, fmt.Errorf("%w: lossless JPEG Adobe color transform %d", ErrUnsupported, transform)
		}
	}
}

// losslessYCbCrToRGB16 按ITU-T T.871将十六位归一化YCbCr分量转换为十六位RGB分量
// 入参: y, cb, cr 归一化十六位分量, mid 对应采样精度的零色度中点
// 返回: uint16 红色分量, uint16 绿色分量, uint16 蓝色分量
func losslessYCbCrToRGB16(y, cb, cr uint16, mid float64) (uint16, uint16, uint16) {
	yf := float64(y)
	cbf := float64(cb) - mid
	crf := float64(cr) - mid
	clamp16 := func(v float64) uint16 {
		if v <= 0 {
			return 0
		}
		if v >= 65535 {
			return 65535
		}
		return uint16(math.Round(v))
	}
	return clamp16(yf + 1.402*crf), clamp16(yf - 0.344136*cbf - 0.714136*crf), clamp16(yf + 1.772*cbf)
}

// convertLosslessJPEGColor 在全部扫描完成后按源色彩空间原地转换像素分量
// 入参: out 解码目标图像, space 已判定的色彩空间, bits 帧样本精度
func convertLosslessJPEGColor(out *rasterImage, space losslessJPEGColor, bits uint32) {
	mid := float64(uint32(1<<(bits-1)) * 65535 / ((1 << bits) - 1))
	switch space {
	case losslessColorYCbCr:
		pixels := out.pixels.(*image.NRGBA64)
		for at := 0; at < len(pixels.Pix); at += 8 {
			yVal := binary.BigEndian.Uint16(pixels.Pix[at:])
			cbVal := binary.BigEndian.Uint16(pixels.Pix[at+2:])
			crVal := binary.BigEndian.Uint16(pixels.Pix[at+4:])
			r, g, b := losslessYCbCrToRGB16(yVal, cbVal, crVal, mid)
			binary.BigEndian.PutUint16(pixels.Pix[at:], r)
			binary.BigEndian.PutUint16(pixels.Pix[at+2:], g)
			binary.BigEndian.PutUint16(pixels.Pix[at+4:], b)
		}
	case losslessColorCMYK:
		values := out.native.values
		for i, v := range values {
			values[i] = 65535 - v
		}
	case losslessColorYCCK:
		values := out.native.values
		for at := 0; at < len(values); at += 4 {
			c, m, y := losslessYCbCrToRGB16(values[at], values[at+1], values[at+2], mid)
			values[at], values[at+1], values[at+2], values[at+3] = c, m, y, 65535-values[at+3]
		}
	}
}

// decodeLosslessJPEGImage 解码灰度、RGB、YCbCr、CMYK或YCCK无损JPEG，逐扫描保留原始精度与颜色配置文件
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
	if stream.components != 1 && stream.components != 3 && stream.components != 4 {
		return nil, fmt.Errorf("%w: lossless JPEG color component interpretation", ErrUnsupported)
	}
	var frame []byte
	var huffman [4]losslessHuffman
	var restart uint16
	var covered uint8
	var colorSpace losslessJPEGColor
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
			convertLosslessJPEGColor(out, colorSpace, uint32(frame[0]))
			if metadata.orientation > 1 {
				applyTIFFOrientation(out, metadata.orientation)
			}
			return out, nil
		}
		if marker == 1 {
			continue
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
			var ids [4]byte
			for c := range stream.components {
				identity := payload[6+c*3]
				if identities[identity] || payload[8+c*3] != 0 {
					return nil, fmt.Errorf("%w: lossless JPEG frame component", ErrInvalid)
				}
				identities[identity] = true
				if payload[7+c*3] != 0x11 {
					return nil, fmt.Errorf("%w: subsampled lossless JPEG components", ErrUnsupported)
				}
				if c < len(ids) {
					ids[c] = identity
				}
			}
			colorSpace, err = resolveLosslessJPEGColor(stream.components, ids, metadata.jpegJFIF, metadata.jpegAdobe, metadata.jpegAdobeTransform)
			if err != nil {
				return nil, err
			}
			frame = payload
			orientation := metadata.orientation
			if orientation == 0 {
				orientation = 1
			}
			imgSpace := ImageColorRGB
			if colorSpace == losslessColorGray {
				imgSpace = ImageColorGray
			} else if colorSpace == losslessColorCMYK || colorSpace == losslessColorYCCK {
				imgSpace = ImageColorCMYK
			}
			if stream.components == 4 {
				native, err := newImageComponents(image.Rect(0, 0, width, height), 4, false, maxPixels)
				if err != nil {
					return nil, err
				}
				out = &rasterImage{native: native, dpi: metadata.dpi, channels: 4, profile: metadata.profile, colorSpace: imgSpace, bitDepth: int(frame[0]), orientation: orientation}
			} else {
				out = &rasterImage{pixels: image.NewNRGBA64(image.Rect(0, 0, width, height)), dpi: metadata.dpi, channels: stream.components, profile: metadata.profile, colorSpace: imgSpace, bitDepth: int(frame[0]), orientation: orientation}
			}
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
	if restart != 0 && int(restart)%out.bounds().Dx() != 0 {
		return 0, fmt.Errorf("%w: lossless JPEG restart interval", ErrInvalid)
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
