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
	"encoding/binary"
	"errors"
	"fmt"
	"image"
	"image/color"
	"image/jpeg"
	"io"
	"math"
	"math/bits"
)

// tiffDirectory 保存首个图像目录及原始字节或按需随机读取器，不读取后续目录
type tiffDirectory struct {
	data  []byte
	ra    io.ReaderAt
	size  uint64
	ctx   context.Context
	order binary.ByteOrder
	entry map[uint16][]byte
}

// tiffLayout 保存条带或图块的存储尺寸、位置索引及经过校验的字节范围
type tiffLayout struct {
	height         int
	blockWidth     int
	blockHeight    int
	across         int
	blocksPerPlane int
	planes         int
	count          int
	rowBytes       int
	rowChannels    int
	ycbcrSubX      int
	ycbcrSubY      int
	chromaRowBytes int
	tiled          bool
	offsets        []byte
	counts         []byte
	offsetWidth    int
	countWidth     int
}

// tiffYCbCrSpec 保存非JPEG压缩YCbCr图像的色度子采样、亮度系数及参考黑白电平参数
type tiffYCbCrSpec struct {
	subX      int
	subY      int
	lumaRed   float64
	lumaGreen float64
	lumaBlue  float64
	refBW     [6]float64
}

// tiffLegacyJPEG 保存旧式TIFF/JPEG的分量码表、抽样及重启参数
type tiffLegacyJPEG struct {
	tables        []byte
	sampling      [4]byte
	quant         [4]byte
	dc            [4]byte
	ac            [4]byte
	scanOrder     [4]byte
	channels      int
	restart       uint16
	interchange   bool
	strictRestart bool
	lossless      bool
	bits          uint32
	predictor     [4]uint32
	point         [4]uint32
	huffman       [4]losslessHuffman
}

// tiffLegacyHeader 保存基线JPEG头中的原始码表、帧、扫描及重启定义
type tiffLegacyHeader struct {
	quant   [4][]byte
	huffman [8][]byte
	frame   []byte
	scan    []byte
	restart uint16
}

// tiffHeader 保存首个TIFF目录完成标准校验后的头元数据，供零像素读头与解码路径共享
type tiffHeader struct {
	dir             *tiffDirectory
	width           uint32
	height          uint32
	compression     uint32
	jpegCompression bool
	orientation     uint32
	photo           uint32
	channels        uint32
	base            uint32
	sampleFormat    uint32
	bits            uint32
	alpha           uint32
	dpi             Point
	colorChannels   int
	colorSpace      ImageColorSpace
	bitDepth        int
}

// tiffPixelFormat 保存已经校验的样本布局、有符号值域及颜色解释
type tiffPixelFormat struct {
	order        binary.ByteOrder
	photo        uint32
	bits         uint32
	channels     uint32
	alpha        uint32
	sampleFormat uint32
	palette      []byte
	hasSMin      bool
	hasSMax      bool
	sMin         [5]float64
	sMax         [5]float64
	ycbcr        tiffYCbCrSpec
}

// tiffDecodeSpec 保存完成全部IFD标签、样本布局、压缩参数与块边界校验的TIFF解码规格，供整图与流式解码共用
type tiffDecodeSpec struct {
	hdr         *tiffHeader
	layout      tiffLayout
	format      tiffPixelFormat
	profile     []byte
	fillOrder   uint32
	predictor   uint32
	fax         bool
	faxOptions  uint32
	jpegTables  tiffJPEGTable
	legacy      tiffLegacyJPEG
	legacyExtra tiffLegacyExtraJPEG
}

// readTIFFDirectory 读取经典TIFF头及首个目录，限制目录项数量
// 入参: data 图像字节
// 返回: *tiffDirectory 图像目录, error 数据或资源错误
func readTIFFDirectory(data []byte) (*tiffDirectory, error) {
	if len(data) < 8 {
		return nil, fmt.Errorf("%w: TIFF header", ErrInvalid)
	}
	d := &tiffDirectory{data: data, entry: make(map[uint16][]byte)}
	switch string(data[:2]) {
	case "II":
		d.order = binary.LittleEndian
	case "MM":
		d.order = binary.BigEndian
	default:
		return nil, fmt.Errorf("%w: TIFF byte order", ErrInvalid)
	}
	if d.order.Uint16(data[2:]) != 42 {
		return nil, fmt.Errorf("%w: TIFF version", ErrUnsupported)
	}
	offset := uint64(d.order.Uint32(data[4:]))
	if offset < 8 || offset+2 > uint64(len(data)) {
		return nil, fmt.Errorf("%w: TIFF directory offset", ErrInvalid)
	}
	count := uint64(d.order.Uint16(data[offset:]))
	if count > 4096 {
		return nil, fmt.Errorf("%w: TIFF directory entries", ErrLimit)
	}
	if count == 0 || offset+2+count*12+4 > uint64(len(data)) {
		return nil, fmt.Errorf("%w: TIFF directory size", ErrInvalid)
	}
	for i := range count {
		entry := data[offset+2+i*12 : offset+2+(i+1)*12]
		tag := d.order.Uint16(entry)
		if d.entry[tag] != nil {
			return nil, fmt.Errorf("%w: duplicate TIFF tag %d", ErrInvalid, tag)
		}
		d.entry[tag] = entry
	}
	return d, nil
}

// tiffReadAtExact 按指定偏移从io.ReaderAt精确读取目标字节长度，保留取消与预算错误
// 入参: ctx 取消Context, ra 按需随机读取器, dst 目标缓冲, offset 起始偏移
// 返回: error 取消、预算或读取截断错误
func tiffReadAtExact(ctx context.Context, ra io.ReaderAt, dst []byte, offset int64) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if len(dst) == 0 {
		return nil
	}
	n, err := ra.ReadAt(dst, offset)
	if err != nil && !(err == io.EOF && n == len(dst)) {
		if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
			return err
		}
		return fmt.Errorf("%w: TIFF read", ErrInvalid)
	}
	if n != len(dst) {
		return fmt.Errorf("%w: truncated TIFF data", ErrInvalid)
	}
	return checkContext(ctx)
}

// readTIFFDirectoryAt 通过io.ReaderAt按需读取经典TIFF头及首个IFD目录，不读取后续目录或像素数据
// 入参: ctx 取消Context, ra 按需随机读取器, size 逻辑文件总字节数
// 返回: *tiffDirectory 按需读取目录, error 取消、头结构或资源错误
func readTIFFDirectoryAt(ctx context.Context, ra io.ReaderAt, size int64) (*tiffDirectory, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if size < 8 {
		return nil, fmt.Errorf("%w: TIFF header", ErrInvalid)
	}
	var head [8]byte
	if err := tiffReadAtExact(ctx, ra, head[:], 0); err != nil {
		return nil, err
	}
	d := &tiffDirectory{ra: ra, size: uint64(size), ctx: ctx, entry: make(map[uint16][]byte)}
	switch string(head[:2]) {
	case "II":
		d.order = binary.LittleEndian
	case "MM":
		d.order = binary.BigEndian
	default:
		return nil, fmt.Errorf("%w: TIFF byte order", ErrInvalid)
	}
	if d.order.Uint16(head[2:]) != 42 {
		return nil, fmt.Errorf("%w: TIFF version", ErrUnsupported)
	}
	offset := uint64(d.order.Uint32(head[4:]))
	if offset < 8 || offset+2 > d.size {
		return nil, fmt.Errorf("%w: TIFF directory offset", ErrInvalid)
	}
	var countBuf [2]byte
	if err := tiffReadAtExact(ctx, ra, countBuf[:], int64(offset)); err != nil {
		return nil, err
	}
	count := uint64(d.order.Uint16(countBuf[:]))
	if count > 4096 {
		return nil, fmt.Errorf("%w: TIFF directory entries", ErrLimit)
	}
	if count == 0 || offset+2+count*12+4 > d.size {
		return nil, fmt.Errorf("%w: TIFF directory size", ErrInvalid)
	}
	rawEntries := make([]byte, int(count*12))
	if err := tiffReadAtExact(ctx, ra, rawEntries, int64(offset+2)); err != nil {
		return nil, err
	}
	for i := range count {
		entry := rawEntries[i*12 : (i+1)*12]
		tag := d.order.Uint16(entry)
		if d.entry[tag] != nil {
			return nil, fmt.Errorf("%w: duplicate TIFF tag %d", ErrInvalid, tag)
		}
		d.entry[tag] = entry
	}
	return d, nil
}

// slice 按偏移和字节数取得目录外部载荷，内存模式零拷贝切片，随机读取模式按需读取
// 入参: offset 起始偏移, size 载荷字节数
// 返回: []byte 载荷字节, error 越界、预算或取消错误
func (d *tiffDirectory) slice(offset, size uint64) ([]byte, error) {
	if d.ra != nil {
		if offset > d.size || size > d.size-offset {
			return nil, fmt.Errorf("%w: TIFF field offset", ErrInvalid)
		}
		buf := make([]byte, int(size))
		if err := tiffReadAtExact(d.ctx, d.ra, buf, int64(offset)); err != nil {
			return nil, err
		}
		return buf, nil
	}
	if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
		return nil, fmt.Errorf("%w: TIFF field offset", ErrInvalid)
	}
	return d.data[offset : offset+size], nil
}

// field 检查字段类型与数量后取得数据，不复制字段内容
// 入参: tag 字段标识, count 所需数量, long 是否接受LONG类型
// 返回: []byte 字段数据, int 单项字节数, error 字段错误
func (d *tiffDirectory) field(tag uint16, count int, long bool) ([]byte, int, error) {
	entry := d.entry[tag]
	if entry == nil {
		return nil, 0, fmt.Errorf("%w: missing TIFF tag %d", ErrInvalid, tag)
	}
	typ := d.order.Uint16(entry[2:])
	width := 2
	if typ == 4 && long {
		width = 4
	} else if typ != 3 {
		return nil, 0, fmt.Errorf("%w: TIFF tag %d type", ErrInvalid, tag)
	}
	if count < 0 || uint64(d.order.Uint32(entry[4:])) != uint64(count) {
		return nil, 0, fmt.Errorf("%w: TIFF tag %d count", ErrInvalid, tag)
	}
	size := uint64(count) * uint64(width)
	if size <= 4 {
		return entry[8 : 8+size], width, nil
	}
	offset := uint64(d.order.Uint32(entry[8:]))
	raw, err := d.slice(offset, size)
	if err != nil {
		if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
			return nil, 0, err
		}
		return nil, 0, fmt.Errorf("%w: TIFF tag %d offset", ErrInvalid, tag)
	}
	return raw, width, nil
}

// byteField 读取UNDEFINED字段，保留字节流自身的编码及字节序
// 入参: tag 字段标识, limit 字节上限
// 返回: []byte 字段视图，缺省时为nil, error 字段或资源错误
func (d *tiffDirectory) byteField(tag uint16, limit uint64) ([]byte, error) {
	entry := d.entry[tag]
	if entry == nil {
		return nil, nil
	}
	if d.order.Uint16(entry[2:]) != 7 {
		return nil, fmt.Errorf("%w: TIFF byte tag %d type", ErrInvalid, tag)
	}
	size := uint64(d.order.Uint32(entry[4:]))
	if size > limit {
		return nil, fmt.Errorf("%w: TIFF byte tag %d budget", ErrLimit, tag)
	}
	if size <= 4 {
		return entry[8 : 8+size], nil
	}
	offset := uint64(d.order.Uint32(entry[8:]))
	if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
		return nil, fmt.Errorf("%w: TIFF byte tag %d offset", ErrInvalid, tag)
	}
	return d.data[offset : offset+size], nil
}

// number 读取单个无符号整数，字段缺省时返回指定值
// 入参: tag 字段标识, fallback 缺省值, long 是否接受LONG类型
// 返回: uint32 字段值, error 字段错误
func (d *tiffDirectory) number(tag uint16, fallback uint32, long bool) (uint32, error) {
	if d.entry[tag] == nil {
		return fallback, nil
	}
	data, width, err := d.field(tag, 1, long)
	if err != nil {
		return 0, err
	}
	return d.integer(data, width), nil
}

// integer 按字段宽度和文件字节序读取无符号整数
// 入参: data 已检查长度的数据, width 单项字节数
// 返回: uint32 字段值
func (d *tiffDirectory) integer(data []byte, width int) uint32 {
	if width == 2 {
		return uint32(d.order.Uint16(data))
	}
	return d.order.Uint32(data)
}

// resolution 读取横纵分辨率，无物理单位时按九十六像素基准保持像素纵横比
// 返回: Point 横纵分辨率, error 字段错误
func (d *tiffDirectory) resolution() (Point, error) {
	unit, err := d.number(296, 2, false)
	if err != nil {
		return Point{}, err
	}
	if unit < 1 || unit > 3 {
		return Point{}, fmt.Errorf("%w: TIFF resolution unit", ErrInvalid)
	}
	value := [2]float64{96, 96}
	var present [2]bool
	for i, tag := range [2]uint16{282, 283} {
		entry := d.entry[tag]
		if entry == nil {
			continue
		}
		if d.order.Uint16(entry[2:]) != 5 || d.order.Uint32(entry[4:]) != 1 {
			return Point{}, fmt.Errorf("%w: TIFF resolution field", ErrInvalid)
		}
		offset := uint64(d.order.Uint32(entry[8:]))
		raw, err := d.slice(offset, 8)
		if err != nil {
			if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
				return Point{}, err
			}
			return Point{}, fmt.Errorf("%w: TIFF resolution offset", ErrInvalid)
		}
		n, q := d.order.Uint32(raw), d.order.Uint32(raw[4:])
		if n == 0 || q == 0 {
			return Point{}, fmt.Errorf("%w: TIFF resolution value", ErrInvalid)
		}
		value[i] = float64(n) / float64(q)
		present[i] = true
		if unit == 3 {
			value[i] *= 2.54
		}
	}
	if unit == 1 {
		if !present[0] || !present[1] || value[0] == value[1] {
			return Point{96, 96}, nil
		}
		return Point{96, 96 * (value[1] / value[0])}, nil
	}
	return Point{value[0], value[1]}, nil
}

// parseTIFFHeader 统一解析并严格校验TIFF首个IFD目录头部标签，供ImageInfo、整图解码与流式逐行解码共用
// 入参: data 完整TIFF图像字节
// 返回: *tiffHeader 已校验TIFF头元数据, error 目录、标签、压缩或能力错误
func parseTIFFHeader(data []byte) (*tiffHeader, error) {
	d, err := readTIFFDirectory(data)
	if err != nil {
		return nil, err
	}
	return parseTIFFHeaderFromDirectory(d)
}

// parseTIFFHeaderFromDirectory 从已读取的首个TIFF目录解析并校验全部头元数据标签
// 入参: d 已读取的TIFF首目录
// 返回: *tiffHeader 已校验TIFF头元数据, error 标签、压缩或能力错误
func parseTIFFHeaderFromDirectory(d *tiffDirectory) (*tiffHeader, error) {
	width, err := d.number(256, 0, true)
	if err != nil {
		return nil, err
	}
	height, err := d.number(257, 0, true)
	if err != nil {
		return nil, err
	}
	if width == 0 || height == 0 {
		return nil, fmt.Errorf("%w: empty TIFF image", ErrInvalid)
	}
	if width > rasterMaxDimension || height > rasterMaxDimension {
		return nil, fmt.Errorf("%w: TIFF image dimensions", ErrLimit)
	}
	compression, err := d.number(259, 1, false)
	if err != nil {
		return nil, err
	}
	if compression != 1 && compression != 2 && compression != 3 && compression != 4 && compression != 5 && compression != 6 && compression != 7 && compression != 8 && compression != 32773 && compression != 32946 {
		return nil, fmt.Errorf("%w: TIFF compression %d", ErrUnsupported, compression)
	}
	orientation, err := d.number(274, 1, false)
	if err != nil {
		return nil, err
	}
	if orientation < 1 || orientation > 8 {
		return nil, fmt.Errorf("%w: TIFF orientation", ErrInvalid)
	}
	if d.entry[262] == nil {
		return nil, fmt.Errorf("%w: missing TIFF photometric interpretation", ErrInvalid)
	}
	photo, err := d.number(262, 0, false)
	if err != nil {
		return nil, err
	}
	jpegCompression := compression == 6 || compression == 7
	if photo > 3 && photo != 5 && photo != 6 {
		return nil, fmt.Errorf("%w: TIFF photometric interpretation %d", ErrUnsupported, photo)
	}
	channels, err := d.number(277, 1, false)
	if err != nil {
		return nil, err
	}
	base := uint32(1)
	if photo == 2 || photo == 6 {
		base = 3
	}
	if photo == 5 {
		base = 4
		inkSet, e := d.number(332, 1, false)
		if e != nil {
			return nil, e
		}
		inks, e := d.number(334, 4, false)
		if e != nil {
			return nil, e
		}
		if inkSet != 1 {
			return nil, fmt.Errorf("%w: TIFF separated ink set", ErrUnsupported)
		}
		if inks != 4 {
			return nil, fmt.Errorf("%w: TIFF CMYK ink count", ErrInvalid)
		}
	}
	if channels < base || channels > base+1 || photo == 3 && channels != 1 {
		return nil, fmt.Errorf("%w: TIFF sample count", ErrUnsupported)
	}
	sampleFormat := uint32(1)
	if d.entry[339] != nil {
		field, _, e := d.field(339, int(channels), false)
		if e != nil {
			return nil, e
		}
		sampleFormat = uint32(d.order.Uint16(field))
		if sampleFormat < 1 || sampleFormat > 3 {
			return nil, fmt.Errorf("%w: TIFF sample format", ErrUnsupported)
		}
		for i := 1; i < int(channels); i++ {
			if uint32(d.order.Uint16(field[2*i:])) != sampleFormat {
				return nil, fmt.Errorf("%w: mixed TIFF sample formats", ErrUnsupported)
			}
		}
	}
	bits := uint32(1)
	if d.entry[258] != nil {
		field, _, e := d.field(258, int(channels), false)
		if e != nil {
			return nil, e
		}
		bits = uint32(d.order.Uint16(field))
		for i := 1; i < int(channels); i++ {
			if uint32(d.order.Uint16(field[2*i:])) != bits {
				return nil, fmt.Errorf("%w: mixed TIFF sample depths", ErrUnsupported)
			}
		}
	}
	switch sampleFormat {
	case 1:
		if bits != 1 && bits != 4 && bits != 8 && bits != 16 || (photo == 2 || photo == 5 || photo == 6) && bits < 8 || photo == 3 && bits == 16 || channels > base && bits < 8 {
			return nil, fmt.Errorf("%w: TIFF sample depth", ErrUnsupported)
		}
	case 2:
		if bits != 8 && bits != 16 || photo == 3 || photo == 6 {
			return nil, fmt.Errorf("%w: TIFF signed sample depth", ErrUnsupported)
		}
	case 3:
		if bits != 32 || photo == 3 || photo == 6 {
			return nil, fmt.Errorf("%w: TIFF floating sample depth", ErrUnsupported)
		}
	}
	alpha := uint32(0)
	if d.entry[338] != nil {
		if channels != base+1 {
			return nil, fmt.Errorf("%w: unexpected TIFF extra sample", ErrInvalid)
		}
		alpha, err = d.number(338, 0, false)
		if err != nil {
			return nil, err
		}
		if alpha > 2 {
			return nil, fmt.Errorf("%w: TIFF alpha interpretation", ErrUnsupported)
		}
	} else if channels > base {
		return nil, fmt.Errorf("%w: missing TIFF ExtraSamples", ErrInvalid)
	}
	dpi, err := d.resolution()
	if err != nil {
		return nil, err
	}
	colorChannels := 3
	colorSpace := ImageColorRGB
	if photo <= 1 {
		colorChannels = 1
		colorSpace = ImageColorGray
	} else if photo == 5 {
		colorChannels = 4
		colorSpace = ImageColorCMYK
	}
	bitDepth := int(bits)
	if photo == 3 {
		bitDepth = 16
	}
	return &tiffHeader{
		dir:             d,
		width:           width,
		height:          height,
		compression:     compression,
		jpegCompression: jpegCompression,
		orientation:     orientation,
		photo:           photo,
		channels:        channels,
		base:            base,
		sampleFormat:    sampleFormat,
		bits:            bits,
		alpha:           alpha,
		dpi:             dpi,
		colorChannels:   colorChannels,
		colorSpace:      colorSpace,
		bitDepth:        bitDepth,
	}, nil
}

// tiffHeaderToImageInfo 将已校验的TIFF首目录头信息转换为视觉方向规范化的ImageInfo
// 入参: hdr 已校验TIFF头元数据, part 部件包根URI, media 内容类型
// 返回: *ImageInfo 视觉方向规范化后的图像头信息
func tiffHeaderToImageInfo(hdr *tiffHeader, part, media string) *ImageInfo {
	w, h := int(hdr.width), int(hdr.height)
	dpiX, dpiY := hdr.dpi.X, hdr.dpi.Y
	if hdr.orientation >= 5 && hdr.orientation <= 8 {
		w, h = h, w
		dpiX, dpiY = dpiY, dpiX
	}
	return &ImageInfo{
		Part:          part,
		ContentType:   media,
		Width:         w,
		Height:        h,
		DPIX:          dpiX,
		DPIY:          dpiY,
		ColorSpace:    hdr.colorSpace,
		HasAlpha:      hdr.alpha != 0,
		BitDepth:      hdr.bitDepth,
		IsFloat:       hdr.sampleFormat == 3,
		Orientation:   hdr.orientation,
		HasICCProfile: hdr.dir.entry[34675] != nil,
	}
}

// readTIFFImageInfo 仅解析TIFF首个IFD目录标签返回轻量图像元数据，不解码任何条带或图块像素
// 入参: data 完整TIFF图像字节, part 部件包根URI, media 内容类型
// 返回: *ImageInfo 视觉方向规范化后的图像头信息, error 目录、标签或能力错误
func readTIFFImageInfo(data []byte, part, media string) (*ImageInfo, error) {
	hdr, err := parseTIFFHeader(data)
	if err != nil {
		return nil, err
	}
	return tiffHeaderToImageInfo(hdr, part, media), nil
}

// readTIFFImageInfoAt 基于io.ReaderAt按需读取TIFF首个IFD目录标签返回轻量元数据，不读入像素载荷
// 入参: ctx 取消Context, ra 图像按需随机读取器, size 图像逻辑总字节数, part 部件包根URI, media 内容类型
// 返回: *ImageInfo 视觉方向规范化后的图像头信息, error 取消、预算、目录、标签或能力错误
func readTIFFImageInfoAt(ctx context.Context, ra io.ReaderAt, size int64, part, media string) (*ImageInfo, error) {
	d, err := readTIFFDirectoryAt(ctx, ra, size)
	if err != nil {
		return nil, err
	}
	hdr, err := parseTIFFHeaderFromDirectory(d)
	if err != nil {
		return nil, err
	}
	return tiffHeaderToImageInfo(hdr, part, media), nil
}

// rationalSlice 读取指定数量的RATIONAL字段为浮点数切片，字段缺省时返回present=false
// 入参: tag 字段标识, count 所需有理数个数
// 返回: []float64 浮点数切片, bool 字段是否存在, error 字段类型、数量、偏移或除零错误
func (d *tiffDirectory) rationalSlice(tag uint16, count int) ([]float64, bool, error) {
	entry := d.entry[tag]
	if entry == nil {
		return nil, false, nil
	}
	if d.order.Uint16(entry[2:]) != 5 || d.order.Uint32(entry[4:]) != uint32(count) {
		return nil, false, fmt.Errorf("%w: TIFF rational tag %d", ErrInvalid, tag)
	}
	offset := uint64(d.order.Uint32(entry[8:]))
	size := uint64(count) * 8
	if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
		return nil, false, fmt.Errorf("%w: TIFF rational tag %d offset", ErrInvalid, tag)
	}
	values := make([]float64, count)
	for i := range count {
		n := d.order.Uint32(d.data[offset+uint64(i)*8:])
		q := d.order.Uint32(d.data[offset+uint64(i)*8+4:])
		if q == 0 {
			return nil, false, fmt.Errorf("%w: TIFF rational tag %d denominator", ErrInvalid, tag)
		}
		values[i] = float64(n) / float64(q)
	}
	return values, true, nil
}

// parseNonJPEGYCbCr 解析非JPEG压缩YCbCr图像的色度子采样、亮度系数、参考黑白电平与色度定位并校验约束
// 入参: bits 样本位深, channels 样本通道数, base 基础颜色通道数, predictor 水平预测器标识
// 返回: tiffYCbCrSpec 已校验YCbCr参数, error 字段、预测器或能力错误
func (d *tiffDirectory) parseNonJPEGYCbCr(bits, channels, base, predictor uint32) (tiffYCbCrSpec, error) {
	if bits != 8 && bits != 16 {
		return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF YCbCr precision", ErrUnsupported)
	}
	subX, subY := 2, 2
	if d.entry[530] != nil {
		field, _, err := d.field(530, 2, false)
		if err != nil {
			return tiffYCbCrSpec{}, err
		}
		subX = int(d.order.Uint16(field))
		subY = int(d.order.Uint16(field[2:]))
	}
	if subX != 1 && subX != 2 && subX != 4 || subY != 1 && subY != 2 && subY != 4 {
		return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF YCbCr subsampling", ErrUnsupported)
	}
	if subX > 1 || subY > 1 {
		if predictor != 1 {
			return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF subsampled YCbCr predictor", ErrUnsupported)
		}
		if channels != base {
			return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF subsampled YCbCr extra sample", ErrUnsupported)
		}
	}
	pos, err := d.number(531, 1, false)
	if err != nil {
		return tiffYCbCrSpec{}, err
	}
	if pos != 1 && pos != 2 {
		return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF YCbCr positioning", ErrUnsupported)
	}
	spec := tiffYCbCrSpec{
		subX:      subX,
		subY:      subY,
		lumaRed:   0.299,
		lumaGreen: 0.587,
		lumaBlue:  0.114,
		refBW:     [6]float64{0, 255, 128, 255, 128, 255},
	}
	if bits == 16 {
		spec.refBW = [6]float64{0, 65535, 32768, 65535, 32768, 65535}
	}
	if coeffs, ok, err := d.rationalSlice(529, 3); err != nil {
		return tiffYCbCrSpec{}, err
	} else if ok {
		if coeffs[0] <= 0 || coeffs[1] <= 0 || coeffs[2] <= 0 || coeffs[0] >= 1 || coeffs[2] >= 1 {
			return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF YCbCr coefficients", ErrInvalid)
		}
		spec.lumaRed, spec.lumaGreen, spec.lumaBlue = coeffs[0], coeffs[1], coeffs[2]
	}
	if refBW, ok, err := d.rationalSlice(532, 6); err != nil {
		return tiffYCbCrSpec{}, err
	} else if ok {
		if refBW[1] == refBW[0] || refBW[3] == refBW[2] || refBW[5] == refBW[4] {
			return tiffYCbCrSpec{}, fmt.Errorf("%w: TIFF ReferenceBlackWhite range", ErrInvalid)
		}
		copy(spec.refBW[:], refBW)
	}
	return spec, nil
}

// parseTIFFDecodeSpec 统一校验TIFF目录样本布局、ICC配置、预测器、传真、YCbCr与JPEG参数及全部块偏移，供整图与流式解码共用
// 当allowJPEG为false且遇到JPEG压缩或转置方向时返回nil规格与nil错误，提示流式路径平滑回退整图解码
// 入参: data 完整TIFF字节, maxPixels 像素容量上限, profileLimit ICC配置字节上限，零采用64MiB, allowJPEG 是否允许JPEG及转置方向
// 返回: *tiffDecodeSpec 已校验解码规格, error 结构、能力或资源错误
func parseTIFFDecodeSpec(data []byte, maxPixels, profileLimit uint64, allowJPEG bool) (*tiffDecodeSpec, error) {
	hdr, err := parseTIFFHeader(data)
	if err != nil {
		return nil, err
	}
	if !allowJPEG && (hdr.jpegCompression || hdr.orientation >= 5) {
		return nil, nil
	}
	d := hdr.dir
	width, height := hdr.width, hdr.height
	pixels := uint64(width) * uint64(height)
	if pixels > maxPixels || pixels > uint64(^uint(0)>>1)/8 {
		return nil, fmt.Errorf("%w: decoded TIFF pixels", ErrLimit)
	}
	compression, jpegCompression := hdr.compression, hdr.jpegCompression
	photo, channels, base := hdr.photo, hdr.channels, hdr.base
	sampleFormat, bits, alpha := hdr.sampleFormat, hdr.bits, hdr.alpha
	var sMin, sMax [5]float64
	var hasSMin, hasSMax bool
	if sampleFormat == 2 {
		defaultMin, defaultMax := -128.0, 127.0
		if bits == 16 {
			defaultMin, defaultMax = -32768.0, 32767.0
		}
		for i := range int(channels) {
			sMin[i], sMax[i] = defaultMin, defaultMax
		}
		if d.entry[340] != nil {
			values, err := d.sampleRange(340, int(channels))
			if err != nil {
				return nil, err
			}
			copy(sMin[:], values)
			hasSMin = true
		}
		if d.entry[341] != nil {
			values, err := d.sampleRange(341, int(channels))
			if err != nil {
				return nil, err
			}
			copy(sMax[:], values)
			hasSMax = true
		}
		for i := range int(channels) {
			if !geometryFinite(sMin[i], sMax[i]) || sMax[i] <= sMin[i] {
				return nil, fmt.Errorf("%w: TIFF signed sample range", ErrInvalid)
			}
		}
	}
	fillOrder, err := d.number(266, 1, false)
	if err != nil {
		return nil, err
	}
	if fillOrder != 1 && fillOrder != 2 {
		return nil, fmt.Errorf("%w: TIFF fill order", ErrInvalid)
	}
	if fillOrder == 2 && bits != 1 {
		return nil, fmt.Errorf("%w: TIFF low-bit-order sample format", ErrUnsupported)
	}
	planar, err := d.number(284, 1, false)
	if err != nil {
		return nil, err
	}
	if planar != 1 && planar != 2 {
		return nil, fmt.Errorf("%w: TIFF planar configuration", ErrInvalid)
	}
	if profileLimit == 0 {
		profileLimit = 64 << 20
	}
	profile, err := d.byteField(34675, profileLimit)
	if err != nil {
		return nil, err
	}
	if profile != nil && len(profile) == 0 {
		return nil, fmt.Errorf("%w: empty TIFF ICC profile", ErrInvalid)
	}
	if d.entry[34665] != nil {
		offset, e := d.number(34665, 0, true)
		if e != nil {
			return nil, e
		}
		if e = exifImageColor(data, d.order, uint64(offset)); e != nil {
			return nil, e
		}
	}
	predictor, err := d.number(317, 1, false)
	if err != nil {
		return nil, err
	}
	if predictor < 1 || predictor > 3 || predictor == 2 && (sampleFormat == 3 || bits < 8) || predictor == 3 && (sampleFormat != 3 || bits != 32) {
		return nil, fmt.Errorf("%w: TIFF predictor", ErrUnsupported)
	}
	fax := compression >= 2 && compression <= 4
	faxOptions := uint32(0)
	if fax {
		if bits != 1 || channels != 1 || photo > 1 || predictor != 1 || sampleFormat != 1 {
			return nil, fmt.Errorf("%w: TIFF fax sample layout", ErrInvalid)
		}
		if compression == 3 || compression == 4 {
			tag := uint16(292)
			if compression == 4 {
				tag = 293
			}
			faxOptions, err = d.number(tag, 0, true)
			if err != nil {
				return nil, err
			}
		}
	}
	var ycbcr tiffYCbCrSpec
	subX, subY := 1, 1
	if !jpegCompression && photo == 6 {
		ycbcr, err = d.parseNonJPEGYCbCr(bits, channels, base, predictor)
		if err != nil {
			return nil, err
		}
		subX, subY = ycbcr.subX, ycbcr.subY
	}
	var jpegTables tiffJPEGTable
	var legacy tiffLegacyJPEG
	var legacyExtra tiffLegacyExtraJPEG
	if jpegCompression {
		if photo == 3 || predictor != 1 || sampleFormat != 1 || planar == 2 && channels > 1 || channels != base && photo != 2 && photo != 5 {
			return nil, fmt.Errorf("%w: TIFF JPEG sample layout", ErrUnsupported)
		}
		if photo == 6 {
			if bits != 8 {
				return nil, fmt.Errorf("%w: TIFF JPEG YCbCr precision", ErrUnsupported)
			}
			if err := d.jpegColor(); err != nil {
				return nil, err
			}
		}
		if compression == 7 {
			jpegTables, err = d.jpegTables()
			if err != nil {
				return nil, err
			}
		}
		if compression == 6 {
			if channels > 4 {
				legacyExtra, err = d.legacyExtraJPEG(width, height, channels, bits)
			} else {
				legacy, err = d.legacyJPEG(width, height, photo, channels, bits)
			}
			if err != nil {
				return nil, err
			}
		}
	}
	layout, err := d.imageLayout(width, height, channels, bits, compression, planar, subX, subY)
	if err != nil {
		return nil, err
	}
	var palette []byte
	if photo == 3 {
		palette, _, err = d.field(320, 3*(1<<bits), false)
		if err != nil {
			return nil, err
		}
	}
	overhead := uint64(layout.count)
	if jpegCompression {
		overhead *= 4096
	}
	var compressedBytes uint64
	for i := range layout.count {
		offset, size := layout.block(d, i)
		if offset > uint64(len(data)) || size > uint64(len(data))-offset {
			return nil, fmt.Errorf("%w: TIFF block offset", ErrInvalid)
		}
		compressedBytes += size + uint64(len(jpegTables.data)) + uint64(len(legacy.tables))
		if compressedBytes > uint64(len(data))+pixels*8+overhead || compressedBytes+overhead > rasterMaxWork {
			return nil, fmt.Errorf("%w: TIFF block work", ErrLimit)
		}
	}
	return &tiffDecodeSpec{
		hdr:         hdr,
		layout:      layout,
		format:      tiffPixelFormat{order: d.order, photo: photo, bits: bits, channels: channels, alpha: alpha, sampleFormat: sampleFormat, palette: palette, hasSMin: hasSMin, hasSMax: hasSMax, sMin: sMin, sMax: sMax, ycbcr: ycbcr},
		profile:     profile,
		fillOrder:   fillOrder,
		predictor:   predictor,
		fax:         fax,
		faxOptions:  faxOptions,
		jpegTables:  jpegTables,
		legacy:      legacy,
		legacyExtra: legacyExtra,
	}, nil
}

// decodeTIFFImage 解码首个目录的条带或分块图像，保持16位颜色及独立透明度并按Tag 274规范化视觉方向
// 入参: data 图像字节, maxPixels 剩余像素预算
// 返回: *rasterImage 图像与分辨率, error 数据、能力或资源错误
func decodeTIFFImage(data []byte, maxPixels uint64) (*rasterImage, error) {
	spec, err := parseTIFFDecodeSpec(data, maxPixels, 64<<20, true)
	if err != nil {
		return nil, err
	}
	hdr := spec.hdr
	d, layout, format := hdr.dir, spec.layout, spec.format
	width, height := hdr.width, hdr.height
	compression, jpegCompression := hdr.compression, hdr.jpegCompression
	orientation, photo, channels, base := hdr.orientation, hdr.photo, hdr.channels, hdr.base
	sampleFormat, bits, alpha := hdr.sampleFormat, hdr.bits, hdr.alpha
	fillOrder, predictor, fax, faxOptions := spec.fillOrder, spec.predictor, spec.fax, spec.faxOptions
	jpegTables, legacy, legacyExtra := spec.jpegTables, spec.legacy, spec.legacyExtra
	result := &rasterImage{
		dpi:         hdr.dpi,
		channels:    hdr.colorChannels,
		profile:     spec.profile,
		colorSpace:  hdr.colorSpace,
		hasAlpha:    alpha != 0,
		bitDepth:    hdr.bitDepth,
		floating:    sampleFormat == 3,
		orientation: orientation,
	}
	bounds := image.Rect(0, 0, int(width), int(height))
	var out *image.NRGBA64
	if sampleFormat == 3 {
		result.native, err = newTIFFFloatComponents(bounds, hdr.colorChannels, alpha != 0, maxPixels)
		if err != nil {
			return nil, err
		}
		result.linear = photo != 5
	} else if photo == 5 {
		result.native, err = newImageComponents(bounds, 4, alpha != 0, maxPixels)
		if err != nil {
			return nil, err
		}
	} else {
		out = image.NewNRGBA64(bounds)
		result.pixels = out
	}
	var buffer, combined, floatScratch, reverseScratch []byte
	if !jpegCompression {
		buffer = make([]byte, layout.blockBufferSize())
		if layout.planes > 1 && !(photo == 6 && (layout.ycbcrSubX > 1 || layout.ycbcrSubY > 1)) {
			combined = make([]byte, layout.rowBytes*layout.planes)
		}
		if predictor == 3 {
			floatScratch = make([]byte, layout.rowBytes)
		}
	}
	var jpegFrame tiffJPEGTable
	subsampledYCbCr := !jpegCompression && photo == 6 && (layout.ycbcrSubX > 1 || layout.ycbcrSubY > 1)
	for i := range layout.blocksPerPlane {
		region := layout.region(i)
		visible := region.Intersect(bounds)
		if jpegCompression {
			offset, size := layout.block(d, i)
			block := data[offset : offset+size]
			if compression == 6 {
				if legacyExtra.stream.data != nil {
					if layout.count != 1 || region.Dx() != int(width) || region.Dy() != int(height) {
						return nil, fmt.Errorf("%w: TIFF multiscan interchange block mapping", ErrUnsupported)
					}
					if !bytes.Equal(block, legacyExtra.entropy) {
						return nil, fmt.Errorf("%w: TIFF multiscan interchange strip data", ErrInvalid)
					}
					if err := d.jpegBlock(result, legacyExtra.stream.data, tiffJPEGTable{}, &jpegFrame, region, layout.tiled, photo, bits); err != nil {
						return nil, err
					}
					continue
				}
				if legacy.lossless {
					if channels != base {
						raw, err := tiffJPEGSampleBuffer(region, int(channels))
						if err != nil {
							return nil, err
						}
						if err := legacy.losslessBlockDecode(raw, block, raw.bounds(), photo, nil); err != nil {
							return nil, err
						}
						format.writeJPEGSamples(result, raw.native, region)
						continue
					}
					if err := legacy.losslessBlockDecode(result, block, region, photo, nil); err != nil {
						return nil, err
					}
					continue
				}
				if legacy.interchange && layout.tiled && region.Dx() < int(width) && region.Dy() != 8*int(legacy.sampling[0]&15) {
					return nil, fmt.Errorf("%w: TIFF JPEG interchange tile height", ErrInvalid)
				}
				block, err = legacy.stream(block, region)
				if err != nil {
					return nil, err
				}
			}
			if err := d.jpegBlock(result, block, jpegTables, &jpegFrame, region, layout.tiled, photo, bits); err != nil {
				return nil, err
			}
			continue
		}
		planeOffsets, planeNeedRev, err := decodeTIFFBlockPlanes(buffer, data, d, layout, i, region, compression, fillOrder, fax, faxOptions, &reverseScratch)
		if err != nil {
			return nil, err
		}
		if subsampledYCbCr {
			for y := range visible.Dy() {
				format.writeSubsampledYCbCrRow(out, visible.Min.X, visible.Min.Y+y, visible.Dx(), y, layout, buffer, planeOffsets)
			}
			continue
		}
		planeSize := layout.rowBytes * region.Dy()
		for y := range visible.Dy() {
			for plane := range layout.planes {
				row := buffer[planeOffsets[plane]+y*layout.rowBytes : planeOffsets[plane]+(y+1)*layout.rowBytes]
				if planeNeedRev[plane] {
					reverseTIFFBits(row)
				}
				if predictor == 2 {
					restoreTIFFPredictor(row, layout.rowChannels, int(bits), d.order)
				} else if predictor == 3 {
					restoreTIFFFloatPredictor(row, floatScratch, layout.rowChannels, d.order)
				}
			}
			row := buffer[y*layout.rowBytes : (y+1)*layout.rowBytes]
			if layout.planes > 1 {
				interleaveTIFFPlaneRows(combined, buffer, planeSize, layout.rowBytes, y, visible.Dx(), layout.planes, int(bits/8))
				row = combined
			}
			if sampleFormat == 3 {
				if err := format.writeFloatRange(result.native, visible.Min.X, visible.Min.Y+y, visible.Dx(), row); err != nil {
					return nil, err
				}
			} else if result.native != nil {
				format.writeComponentRange(result.native, visible.Min.X, visible.Min.Y+y, visible.Dx(), row)
			} else {
				format.writeRowRange(out, visible.Min.X, visible.Min.Y+y, visible.Dx(), row)
			}
		}
	}
	if orientation > 1 {
		applyTIFFOrientation(result, orientation)
	}
	return result, nil
}

// decodeTIFFBlockPlanes 解压单个条带或图块的全部平面到复用缓冲并记录各平面偏移及解包后位反转标记
// 入参: buffer 复用解压缓冲, data 完整TIFF字节, d 目录, layout 存储布局, blockIdx 平面内块号, region 块矩形, compression 压缩标识, fillOrder 位序标识, fax 是否传真压缩, faxOptions 传真选项, reverseScratch 可复用位反转临时缓冲
// 返回: [5]int 各平面起始偏移, [5]bool 各平面是否需逐行反转位序, error 解码错误
func decodeTIFFBlockPlanes(buffer, data []byte, d *tiffDirectory, layout tiffLayout, blockIdx int, region image.Rectangle, compression, fillOrder uint32, fax bool, faxOptions uint32, reverseScratch *[]byte) ([5]int, [5]bool, error) {
	var offsets [5]int
	var needRev [5]bool
	pos := 0
	for plane := range layout.planes {
		planeSize, packRowBytes := layout.planeBufferSize(plane, region.Dy())
		offsets[plane] = pos
		strip := buffer[pos : pos+planeSize]
		pos += planeSize
		offset, size := layout.block(d, plane*layout.blocksPerPlane+blockIdx)
		if fax {
			if err := faxStrip(strip, data[offset:offset+size], region.Dx(), compression, fillOrder, faxOptions); err != nil {
				return offsets, needRev, err
			}
		} else {
			rev, err := decodeTIFFBlockPayload(strip, data[offset:offset+size], compression, fillOrder, packRowBytes, reverseScratch)
			if err != nil {
				return offsets, needRev, err
			}
			needRev[plane] = rev
		}
	}
	return offsets, needRev, nil
}

// decodeTIFFImageRows 按单Strip或单Tile-Row增量流式解码非JPEG非转置TIFF并逐行色彩管理输出，峰值内存远低于整帧缓冲
// 对JPEG压缩TIFF或需转置方向（EXIF 5至8）返回handled=false由上层平滑回退整帧解码路径
// 入参: ctx 已规范化取消Context, data 完整TIFF字节, maxPixels 像素容量上限, profileBudget 色彩配置字节上限, stripBudget 显式收紧的解压带内存上限，零表示跟随像素解码预算, cfg 已校验色彩转换选项, fn 逐行消费回调
// 返回: bool 是否已由流式路径处理, error 解码、色彩、预算、回调或取消错误
func decodeTIFFImageRows(ctx context.Context, data []byte, maxPixels, profileBudget, stripBudget uint64, cfg ImageConvertOptions, fn func(y int, nrgba []byte) error) (bool, error) {
	if err := checkContext(ctx); err != nil {
		return false, err
	}
	spec, err := parseTIFFDecodeSpec(data, maxPixels, profileBudget, false)
	if err != nil {
		return false, err
	}
	if spec == nil {
		return false, nil
	}
	hdr, layout, format := spec.hdr, spec.layout, spec.format
	d := hdr.dir
	width, height := hdr.width, hdr.height
	compression, photo, sampleFormat, bits, alpha := hdr.compression, hdr.photo, hdr.sampleFormat, hdr.bits, hdr.alpha
	fillOrder, predictor, fax, faxOptions := spec.fillOrder, spec.predictor, spec.fax, spec.faxOptions
	bandHeight := 1
	if layout.tiled {
		bandHeight = min(layout.blockHeight, int(height))
	}
	peakMem := uint64(layout.blockBufferSize())
	if layout.tiled {
		pixelBytes := uint64(8)
		if sampleFormat == 3 {
			stride := uint64(hdr.colorChannels)
			if alpha != 0 {
				stride++
			}
			pixelBytes = stride * 8
		} else if photo == 5 {
			stride := uint64(4)
			if alpha != 0 {
				stride++
			}
			pixelBytes = stride * 2
		}
		peakMem += uint64(width) * uint64(bandHeight) * pixelBytes
	}
	if stripBudget > 0 && peakMem > stripBudget {
		return false, fmt.Errorf("%w: TIFF strip buffer memory budget", ErrLimit)
	}
	bandBounds := image.Rect(0, 0, int(width), bandHeight)
	bandRaster := &rasterImage{
		dpi:         hdr.dpi,
		channels:    hdr.colorChannels,
		profile:     spec.profile,
		colorSpace:  hdr.colorSpace,
		hasAlpha:    alpha != 0,
		bitDepth:    hdr.bitDepth,
		floating:    sampleFormat == 3,
		orientation: 1,
	}
	var bandOut *image.NRGBA64
	if sampleFormat == 3 {
		bandRaster.native, err = newTIFFFloatComponents(bandBounds, hdr.colorChannels, alpha != 0, maxPixels)
		if err != nil {
			return false, err
		}
		bandRaster.linear = photo != 5
	} else if photo == 5 {
		bandRaster.native, err = newImageComponents(bandBounds, 4, alpha != 0, maxPixels)
		if err != nil {
			return false, err
		}
	} else {
		bandOut = image.NewNRGBA64(bandBounds)
		bandRaster.pixels = bandOut
	}
	sampler, err := prepareImageConvertSampler(&ImageResource{source: bandRaster}, cfg, profileBudget)
	if err != nil {
		return false, err
	}
	var bgLinear [3]float64
	bgAlpha := 0.0
	hasBG := cfg.Background != nil
	if hasBG {
		bgLinear, bgAlpha, _ = imageConvertBackground(cfg.Background)
	}
	subsampledYCbCr := photo == 6 && (layout.ycbcrSubX > 1 || layout.ycbcrSubY > 1)
	buffer := make([]byte, layout.blockBufferSize())
	var combined, floatScratch, reverseScratch []byte
	if layout.planes > 1 && !subsampledYCbCr {
		combined = make([]byte, layout.rowBytes*layout.planes)
	}
	if predictor == 3 {
		floatScratch = make([]byte, layout.rowBytes)
	}
	rowBuf := make([]byte, int(width)*4)
	reverseY := hdr.orientation == 3 || hdr.orientation == 4
	flipX := hdr.orientation == 2 || hdr.orientation == 3
	outY := 0
	var jxrCache jxrRowCache
	if layout.tiled {
		tileRows := (int(height) + layout.blockHeight - 1) / layout.blockHeight
		for rowBandStep := range tileRows {
			if err := checkContext(ctx); err != nil {
				return true, err
			}
			ty := rowBandStep
			if reverseY {
				ty = tileRows - 1 - rowBandStep
			}
			visH := min(layout.blockHeight, int(height)-ty*layout.blockHeight)
			for tx := range layout.across {
				if err := checkContext(ctx); err != nil {
					return true, err
				}
				blockIdx := ty*layout.across + tx
				region := layout.region(blockIdx)
				visX := region.Min.X
				visW := min(region.Dx(), int(width)-visX)
				if visW <= 0 {
					continue
				}
				planeOffsets, planeNeedRev, err := decodeTIFFBlockPlanes(buffer, data, d, layout, blockIdx, region, compression, fillOrder, fax, faxOptions, &reverseScratch)
				if err != nil {
					return true, err
				}
				if subsampledYCbCr {
					for y := range visH {
						format.writeSubsampledYCbCrRow(bandOut, visX, y, visW, y, layout, buffer, planeOffsets)
					}
					continue
				}
				planeSize := layout.rowBytes * region.Dy()
				for y := range visH {
					for plane := range layout.planes {
						row := buffer[planeOffsets[plane]+y*layout.rowBytes : planeOffsets[plane]+(y+1)*layout.rowBytes]
						if planeNeedRev[plane] {
							reverseTIFFBits(row)
						}
						if predictor == 2 {
							restoreTIFFPredictor(row, layout.rowChannels, int(bits), d.order)
						} else if predictor == 3 {
							restoreTIFFFloatPredictor(row, floatScratch, layout.rowChannels, d.order)
						}
					}
					row := buffer[y*layout.rowBytes : (y+1)*layout.rowBytes]
					if layout.planes > 1 {
						interleaveTIFFPlaneRows(combined, buffer, planeSize, layout.rowBytes, y, visW, layout.planes, int(bits/8))
						row = combined
					}
					if sampleFormat == 3 {
						if err := format.writeFloatRange(bandRaster.native, visX, y, visW, row); err != nil {
							return true, err
						}
					} else if bandRaster.native != nil {
						format.writeComponentRange(bandRaster.native, visX, y, visW, row)
					} else {
						format.writeRowRange(bandOut, visX, y, visW, row)
					}
				}
			}
			for yStep := range visH {
				if err := checkContext(ctx); err != nil {
					return true, err
				}
				y := yStep
				if reverseY {
					y = visH - 1 - yStep
				}
				if err := convertSamplerRowToNRGBA(ctx, sampler, &jxrCache, 0, y, int(width), flipX, hasBG, bgLinear, bgAlpha, cfg.Negative, cfg.ColorMode, rowBuf); err != nil {
					return true, err
				}
				if err := fn(outY, rowBuf); err != nil {
					return true, err
				}
				outY++
			}
		}
		return true, checkContext(ctx)
	}
	for step := range layout.blocksPerPlane {
		if err := checkContext(ctx); err != nil {
			return true, err
		}
		stripIdx := step
		if reverseY {
			stripIdx = layout.blocksPerPlane - 1 - step
		}
		region := layout.region(stripIdx)
		stripRows := region.Dy()
		planeOffsets, planeNeedRev, err := decodeTIFFBlockPlanes(buffer, data, d, layout, stripIdx, region, compression, fillOrder, fax, faxOptions, &reverseScratch)
		if err != nil {
			return true, err
		}
		planeSize := layout.rowBytes * stripRows
		for rowStep := range stripRows {
			if err := checkContext(ctx); err != nil {
				return true, err
			}
			y := rowStep
			if reverseY {
				y = stripRows - 1 - rowStep
			}
			if subsampledYCbCr {
				format.writeSubsampledYCbCrRow(bandOut, 0, 0, int(width), y, layout, buffer, planeOffsets)
			} else {
				for plane := range layout.planes {
					row := buffer[planeOffsets[plane]+y*layout.rowBytes : planeOffsets[plane]+(y+1)*layout.rowBytes]
					if planeNeedRev[plane] {
						reverseTIFFBits(row)
					}
					if predictor == 2 {
						restoreTIFFPredictor(row, layout.rowChannels, int(bits), d.order)
					} else if predictor == 3 {
						restoreTIFFFloatPredictor(row, floatScratch, layout.rowChannels, d.order)
					}
				}
				row := buffer[y*layout.rowBytes : (y+1)*layout.rowBytes]
				if layout.planes > 1 {
					interleaveTIFFPlaneRows(combined, buffer, planeSize, layout.rowBytes, y, int(width), layout.planes, int(bits/8))
					row = combined
				}
				if sampleFormat == 3 {
					if err := format.writeFloatRange(bandRaster.native, 0, 0, int(width), row); err != nil {
						return true, err
					}
				} else if bandRaster.native != nil {
					format.writeComponentRange(bandRaster.native, 0, 0, int(width), row)
				} else {
					format.writeRowRange(bandOut, 0, 0, int(width), row)
				}
			}
			if err := convertSamplerRowToNRGBA(ctx, sampler, &jxrCache, 0, 0, int(width), flipX, hasBG, bgLinear, bgAlpha, cfg.Negative, cfg.ColorMode, rowBuf); err != nil {
				return true, err
			}
			if err := fn(outY, rowBuf); err != nil {
				return true, err
			}
			outY++
		}
	}
	return true, checkContext(ctx)
}

// sampleRange 解析SMinSampleValue或SMaxSampleValue的逐通道标量范围，允许单值广播到全部通道
// 入参: tag 字段标识, channels 图像样本通道数
// 返回: []float64 逐通道范围值, error 字段类型、数量、偏移或数值错误
func (d *tiffDirectory) sampleRange(tag uint16, channels int) ([]float64, error) {
	entry := d.entry[tag]
	typ := d.order.Uint16(entry[2:])
	count := d.order.Uint32(entry[4:])
	if count != 1 && int(count) != channels {
		return nil, fmt.Errorf("%w: TIFF sample range tag %d count", ErrInvalid, tag)
	}
	var width uint64
	switch typ {
	case 1, 6:
		width = 1
	case 3, 8:
		width = 2
	case 4, 9, 11:
		width = 4
	case 5, 10, 12:
		width = 8
	default:
		return nil, fmt.Errorf("%w: TIFF sample range tag %d type", ErrInvalid, tag)
	}
	size := uint64(count) * width
	var raw []byte
	if size <= 4 {
		raw = entry[8 : 8+size]
	} else {
		offset := uint64(d.order.Uint32(entry[8:]))
		if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
			return nil, fmt.Errorf("%w: TIFF sample range tag %d offset", ErrInvalid, tag)
		}
		raw = d.data[offset : offset+size]
	}
	result := make([]float64, channels)
	for i := range int(count) {
		slice := raw[uint64(i)*width:]
		var v float64
		switch typ {
		case 1:
			v = float64(slice[0])
		case 6:
			v = float64(int8(slice[0]))
		case 3:
			v = float64(d.order.Uint16(slice))
		case 8:
			v = float64(int16(d.order.Uint16(slice)))
		case 4:
			v = float64(d.order.Uint32(slice))
		case 9:
			v = float64(int32(d.order.Uint32(slice)))
		case 5:
			n, q := d.order.Uint32(slice), d.order.Uint32(slice[4:])
			if q == 0 {
				return nil, fmt.Errorf("%w: TIFF sample range rational denominator", ErrInvalid)
			}
			v = float64(n) / float64(q)
		case 10:
			n, q := int32(d.order.Uint32(slice)), int32(d.order.Uint32(slice[4:]))
			if q == 0 {
				return nil, fmt.Errorf("%w: TIFF sample range rational denominator", ErrInvalid)
			}
			v = float64(n) / float64(q)
		case 11:
			v = float64(math.Float32frombits(d.order.Uint32(slice)))
		case 12:
			v = math.Float64frombits(d.order.Uint64(slice))
		}
		if !geometryFinite(v) {
			return nil, fmt.Errorf("%w: TIFF sample range non-finite value", ErrInvalid)
		}
		result[i] = v
	}
	if count == 1 {
		for i := 1; i < channels; i++ {
			result[i] = result[0]
		}
	}
	return result, nil
}

// tiffOrientedPoint 按TIFF Tag 274定义将存储坐标映射到视觉方向坐标
// 入参: x, y 存储坐标, w, h 存储宽高, orientation 方向编号2到8
// 返回: int 视觉横坐标, int 视觉纵坐标
func tiffOrientedPoint(x, y, w, h int, orientation uint32) (int, int) {
	switch orientation {
	case 2:
		return w - 1 - x, y
	case 3:
		return w - 1 - x, h - 1 - y
	case 4:
		return x, h - 1 - y
	case 5:
		return y, x
	case 6:
		return h - 1 - y, x
	case 7:
		return h - 1 - y, w - 1 - x
	case 8:
		return y, w - 1 - x
	default:
		return x, y
	}
}

// applyTIFFOrientation 按EXIF/TIFF Tag 274对解码后的像素缓冲执行旋转或镜像变换，并在轴交换时同步交换DPI
// 入参: result 已解码的栅格图像, orientation 合法方向值2到8
func applyTIFFOrientation(result *rasterImage, orientation uint32) {
	bounds := result.bounds()
	w, h := bounds.Dx(), bounds.Dy()
	dstW, dstH := w, h
	if orientation >= 5 {
		dstW, dstH = h, w
		result.dpi = Point{result.dpi.Y, result.dpi.X}
	}
	dstBounds := image.Rect(0, 0, dstW, dstH)
	if result.native != nil {
		src := result.native
		stride := src.channels
		if src.alpha {
			stride++
		}
		dst := &imageComponents{bounds: dstBounds, channels: src.channels, alpha: src.alpha}
		if src.floating != nil {
			dst.floating = make([]float64, len(src.floating))
			for y := range h {
				for x := range w {
					dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
					sAt := (y*w + x) * stride
					dAt := (dy*dstW + dx) * stride
					copy(dst.floating[dAt:dAt+stride], src.floating[sAt:sAt+stride])
				}
			}
		} else {
			dst.values = make([]uint16, len(src.values))
			for y := range h {
				for x := range w {
					dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
					sAt := (y*w + x) * stride
					dAt := (dy*dstW + dx) * stride
					copy(dst.values[dAt:dAt+stride], src.values[sAt:sAt+stride])
				}
			}
		}
		result.native = dst
		return
	}
	switch src := result.pixels.(type) {
	case *image.NRGBA64:
		dst := image.NewNRGBA64(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				sAt := src.PixOffset(bounds.Min.X+x, bounds.Min.Y+y)
				dAt := dst.PixOffset(dx, dy)
				copy(dst.Pix[dAt:dAt+8], src.Pix[sAt:sAt+8])
			}
		}
		result.pixels = dst
	case *image.NRGBA:
		dst := image.NewNRGBA(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				sAt := src.PixOffset(bounds.Min.X+x, bounds.Min.Y+y)
				dAt := dst.PixOffset(dx, dy)
				copy(dst.Pix[dAt:dAt+4], src.Pix[sAt:sAt+4])
			}
		}
		result.pixels = dst
	case *image.RGBA:
		dst := image.NewRGBA(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				sAt := src.PixOffset(bounds.Min.X+x, bounds.Min.Y+y)
				dAt := dst.PixOffset(dx, dy)
				copy(dst.Pix[dAt:dAt+4], src.Pix[sAt:sAt+4])
			}
		}
		result.pixels = dst
	case *image.Gray:
		dst := image.NewGray(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				dst.Pix[dst.PixOffset(dx, dy)] = src.Pix[src.PixOffset(bounds.Min.X+x, bounds.Min.Y+y)]
			}
		}
		result.pixels = dst
	case *image.CMYK:
		dst := image.NewCMYK(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				sAt := src.PixOffset(bounds.Min.X+x, bounds.Min.Y+y)
				dAt := dst.PixOffset(dx, dy)
				copy(dst.Pix[dAt:dAt+4], src.Pix[sAt:sAt+4])
			}
		}
		result.pixels = dst
	case *image.YCbCr:
		dst := image.NewNRGBA(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				sx, sy := bounds.Min.X+x, bounds.Min.Y+y
				ci := src.COffset(sx, sy)
				r, g, b := color.YCbCrToRGB(src.Y[src.YOffset(sx, sy)], src.Cb[ci], src.Cr[ci])
				dAt := dst.PixOffset(dx, dy)
				dst.Pix[dAt], dst.Pix[dAt+1], dst.Pix[dAt+2], dst.Pix[dAt+3] = r, g, b, 255
			}
		}
		result.pixels = dst
	case image.Image:
		dst := image.NewNRGBA64(dstBounds)
		for y := range h {
			for x := range w {
				dx, dy := tiffOrientedPoint(x, y, w, h, orientation)
				dst.SetNRGBA64(dx, dy, imagePixel(src, bounds.Min.X+x, bounds.Min.Y+y))
			}
		}
		result.pixels = dst
	}
}

// restoreTIFFFloatPredictor 按TIFF技术说明3恢复浮点水平差分及大端字节平面重排
// 入参: row 当前行字节, scratch 同长临时缓冲, channels 行内通道数, order 文件字节序
func restoreTIFFFloatPredictor(row, scratch []byte, channels int, order binary.ByteOrder) {
	for i := channels; i < len(row); i++ {
		row[i] += row[i-channels]
	}
	copy(scratch, row)
	samples := len(row) / 4
	for i := range samples {
		value := uint32(scratch[i])<<24 | uint32(scratch[samples+i])<<16 | uint32(scratch[2*samples+i])<<8 | uint32(scratch[3*samples+i])
		order.PutUint32(row[i*4:], value)
	}
}

// interleaveTIFFPlaneRows 将分离平面块中的当前可见行重组为交织样本行
// 入参: dst 交织行缓冲, planes 全部平面解压缓冲, planeSize 单平面块字节数, rowBytes 单平面行字节数, y 块内行号, width 可见列数, count 平面数, sampleBytes 单样本字节数
func interleaveTIFFPlaneRows(dst, planes []byte, planeSize, rowBytes, y, width, count, sampleBytes int) {
	pixelBytes := count * sampleBytes
	for plane := range count {
		src := planes[plane*planeSize+y*rowBytes:]
		for x := range width {
			copy(dst[x*pixelBytes+plane*sampleBytes:x*pixelBytes+(plane+1)*sampleBytes], src[x*sampleBytes:(x+1)*sampleBytes])
		}
	}
}

// newTIFFFloatComponents 按浮点样本容量检查预算并分配连续扩展范围分量
// 入参: bounds 图像范围, channels 颜色通道数, alpha 是否包含透明度, maxPixels 剩余RGBA64像素容量
// 返回: *imageComponents 浮点原生分量图像, error 结构或资源错误
func newTIFFFloatComponents(bounds image.Rectangle, channels int, alpha bool, maxPixels uint64) (*imageComponents, error) {
	if bounds.Empty() || bounds.Min.X != 0 || bounds.Min.Y != 0 || channels < 1 || channels > 8 {
		return nil, fmt.Errorf("%w: image component layout", ErrInvalid)
	}
	stride := channels
	if alpha {
		stride++
	}
	count := uint64(bounds.Dx()) * uint64(bounds.Dy())
	units := uint64(stride)
	if bounds.Dx() > rasterMaxDimension || bounds.Dy() > rasterMaxDimension || count > maxPixels/units || count > uint64(^uint(0)>>1)/uint64(8*stride) {
		return nil, fmt.Errorf("%w: image component storage", ErrLimit)
	}
	return &imageComponents{bounds: bounds, channels: channels, alpha: alpha, floating: make([]float64, int(count)*stride)}, nil
}

// restoreTIFFPredictor 逐行恢复同一颜色通道的水平差分，16位样本遵循文件字节序
// 入参: row 当前行字节, channels 通道数, bits 样本位数, order 文件字节序
func restoreTIFFPredictor(row []byte, channels, bits int, order binary.ByteOrder) {
	step := channels * (bits / 8)
	if bits == 8 {
		for i := step; i < len(row); i++ {
			row[i] += row[i-step]
		}
		return
	}
	for i := step; i < len(row); i += 2 {
		order.PutUint16(row[i:], order.Uint16(row[i:])+order.Uint16(row[i-step:]))
	}
}

// reverseTIFFBits 将低位优先的二值样本恢复为内部高位优先布局，不用于LZW码字位序
// 入参: row 已解压的二值图像行
func reverseTIFFBits(row []byte) {
	for i, value := range row {
		row[i] = bits.Reverse8(value)
	}
}

// decodeTIFFBlockPayload 解压非传真TIFF块载荷，1-bit低位优先压缩流同时兼容标准像素位序与libtiff流位反转编码
// 入参: dst 目标字节, src 压缩块字节, compression 压缩标识, fillOrder 位序标识, rowBytes 每行字节数, reverseScratch 可复用位反转临时缓冲
// 返回: bool 解压后像素行是否仍需执行reverseTIFFBits, error 数据或能力错误
func decodeTIFFBlockPayload(dst, src []byte, compression, fillOrder uint32, rowBytes int, reverseScratch *[]byte) (bool, error) {
	if fillOrder != 2 || compression == 1 {
		err := decodeTIFFStrip(dst, src, compression, rowBytes)
		return fillOrder == 2, err
	}
	if err := decodeTIFFStrip(dst, src, compression, rowBytes); err == nil {
		return true, nil
	}
	buf := *reverseScratch
	if cap(buf) < len(src) {
		buf = make([]byte, len(src))
	} else {
		buf = buf[:len(src)]
	}
	for i, value := range src {
		buf[i] = bits.Reverse8(value)
	}
	*reverseScratch = buf
	if err := decodeTIFFStrip(dst, buf, compression, rowBytes); err != nil {
		return false, err
	}
	return false, nil
}

// decodeTIFFStrip 将条带解压到已限定大小的缓冲区，未压缩条带允许尾部对齐填充，拒绝不足的数据
// 入参: dst 目标字节, src 条带字节, compression 压缩标识, rowBytes 每行字节数
// 返回: error 数据或能力错误
func decodeTIFFStrip(dst, src []byte, compression uint32, rowBytes int) error {
	switch compression {
	case 1:
		if len(src) < len(dst) {
			return fmt.Errorf("%w: TIFF uncompressed strip length", ErrInvalid)
		}
		copy(dst, src[:len(dst)])
		return nil
	case 5:
		return decodeTIFFLZW(dst, src)
	case 8, 32946:
		return decodeTIFFDeflate(dst, src)
	case 32773:
		return decodeTIFFPackBits(dst, src, rowBytes)
	default:
		return fmt.Errorf("%w: TIFF compression %d", ErrUnsupported, compression)
	}
}

// decodeTIFFPackBits 按行解码字节游程，不允许游程跨越行边界
// 入参: dst 目标字节, src 条带字节, rowBytes 每行字节数
// 返回: error 游程或长度错误
func decodeTIFFPackBits(dst, src []byte, rowBytes int) error {
	if rowBytes <= 0 || len(dst)%rowBytes != 0 {
		return fmt.Errorf("%w: TIFF PackBits row size", ErrInvalid)
	}
	pos := 0
	for len(src) > 0 {
		code := int(int8(src[0]))
		src = src[1:]
		if code == -128 {
			continue
		}
		count := code + 1
		if code < 0 {
			count = 1 - code
		}
		if pos == len(dst) || count > rowBytes-pos%rowBytes || count > len(dst)-pos {
			return fmt.Errorf("%w: TIFF PackBits run length", ErrInvalid)
		}
		if code < 0 {
			if len(src) == 0 {
				return fmt.Errorf("%w: TIFF PackBits repeated byte", ErrInvalid)
			}
			for i := range count {
				dst[pos+i] = src[0]
			}
			src = src[1:]
		} else {
			if len(src) < count {
				return fmt.Errorf("%w: TIFF PackBits literal bytes", ErrInvalid)
			}
			copy(dst[pos:pos+count], src[:count])
			src = src[count:]
		}
		pos += count
	}
	if pos != len(dst) {
		return fmt.Errorf("%w: short TIFF PackBits strip", ErrInvalid)
	}
	return nil
}

// decodeTIFFLZW 解码高位优先的TIFF变长码，按提前扩位规则维护有界字典
// 入参: dst 目标字节, src 条带字节
// 返回: error 码字、字典或长度错误
func decodeTIFFLZW(dst, src []byte) error {
	var prefix [4096]uint16
	var suffix [4096]byte
	var stack [4096]byte
	width, next, previous := uint(9), uint16(258), uint16(4096)
	var bit uint64
	pos, started := 0, false
	for {
		if bit+uint64(width) > uint64(len(src))*8 {
			return fmt.Errorf("%w: TIFF LZW end code", ErrInvalid)
		}
		at, shift := int(bit/8), uint(bit%8)
		window := uint32(src[at])<<16 | uint32(src[at+1])<<8
		if shift+width > 16 {
			window |= uint32(src[at+2])
		}
		code := uint16(window>>(24-shift-width)) & uint16(1<<width-1)
		bit += uint64(width)
		if !started && code != 256 {
			return fmt.Errorf("%w: TIFF LZW initial clear code", ErrInvalid)
		}
		started = true
		if code == 256 {
			width, next, previous = 9, 258, 4096
			continue
		}
		if code == 257 {
			if pos != len(dst) {
				return fmt.Errorf("%w: short TIFF LZW strip", ErrInvalid)
			}
			return nil
		}
		current, n := code, 0
		if code == next && previous != 4096 {
			current = previous
			stack[0] = 0
			n = 1
		} else if code >= next {
			return fmt.Errorf("%w: TIFF LZW dictionary code", ErrInvalid)
		}
		for current >= 258 {
			if current >= next || n >= len(stack)-1 || prefix[current] >= current {
				return fmt.Errorf("%w: TIFF LZW dictionary chain", ErrInvalid)
			}
			stack[n] = suffix[current]
			n++
			current = prefix[current]
		}
		if current >= 256 {
			return fmt.Errorf("%w: TIFF LZW literal code", ErrInvalid)
		}
		first := byte(current)
		stack[n] = first
		n++
		if code == next {
			stack[0] = first
		}
		if n > len(dst)-pos {
			return fmt.Errorf("%w: excessive TIFF LZW output", ErrInvalid)
		}
		for i := n - 1; i >= 0; i-- {
			dst[pos] = stack[i]
			pos++
		}
		if previous != 4096 && next < 4096 {
			prefix[next], suffix[next] = previous, first
			next++
			if width < 12 && next == 1<<width-1 {
				width++
			}
		}
		previous = code
	}
}

// imageLayout 校验条带与图块组织，计入分离平面、子采样YCbCr及边界填充的解码工作量和临时内存
// 入参: width 图像宽度, height 图像高度, channels 样本数, bits 样本位数, compression 压缩标识, planar 平面布局, subX 水平色度子采样因子, subY 垂直色度子采样因子
// 返回: tiffLayout 存储布局, error 字段或资源错误
func (d *tiffDirectory) imageLayout(width, height, channels, bits, compression, planar uint32, subX, subY int) (tiffLayout, error) {
	l := tiffLayout{height: int(height), blockWidth: int(width), across: 1, ycbcrSubX: subX, ycbcrSubY: subY}
	for _, tag := range []uint16{322, 323, 324, 325} {
		l.tiled = l.tiled || d.entry[tag] != nil
	}
	offsetTag, countTag := uint16(273), uint16(279)
	if l.tiled {
		for _, tag := range []uint16{273, 278, 279} {
			if d.entry[tag] != nil {
				return l, fmt.Errorf("%w: mixed TIFF strip and tile fields", ErrInvalid)
			}
		}
		for _, tag := range []uint16{322, 323, 324, 325} {
			if d.entry[tag] == nil {
				return l, fmt.Errorf("%w: missing TIFF tile tag %d", ErrInvalid, tag)
			}
		}
		w, err := d.number(322, 0, true)
		if err != nil {
			return l, err
		}
		h, err := d.number(323, 0, true)
		if err != nil {
			return l, err
		}
		multiple := uint32(16)
		if compression == 6 {
			multiple = 8
		}
		if w == 0 || h == 0 || w%multiple != 0 || h%multiple != 0 {
			return l, fmt.Errorf("%w: TIFF tile dimensions", ErrInvalid)
		}
		if w > rasterMaxDimension || h > rasterMaxDimension {
			return l, fmt.Errorf("%w: TIFF tile dimensions", ErrLimit)
		}
		l.blockWidth, l.blockHeight = int(w), int(h)
		l.across = int((uint64(width) + uint64(w) - 1) / uint64(w))
		offsetTag, countTag = 324, 325
		if d.order.Uint16(d.entry[offsetTag][2:]) != 4 {
			return l, fmt.Errorf("%w: TIFF tile offset type", ErrInvalid)
		}
	} else {
		rows, err := d.number(278, ^uint32(0), true)
		if err != nil {
			return l, err
		}
		if rows == 0 {
			return l, fmt.Errorf("%w: TIFF rows per strip", ErrInvalid)
		}
		l.blockHeight = int(min(rows, height))
	}
	planes, rowChannels := uint64(1), uint64(channels)
	if planar == 2 && channels > 1 {
		planes, rowChannels = uint64(channels), 1
	}
	down := (uint64(height) + uint64(l.blockHeight) - 1) / uint64(l.blockHeight)
	blocksPerPlane := uint64(l.across) * down
	count := blocksPerPlane * planes
	var rowBytes, chromaRowBytes, blockTotalBytes, decodedBytes uint64
	if subX > 1 || subY > 1 {
		sampleBytes := uint64(bits / 8)
		if planes == 1 {
			unitsX := (uint64(l.blockWidth) + uint64(subX) - 1) / uint64(subX)
			unitsY := (uint64(l.blockHeight) + uint64(subY) - 1) / uint64(subY)
			rowBytes = unitsX * (uint64(subX)*uint64(subY) + 2) * sampleBytes
			blockTotalBytes = rowBytes * unitsY
			if l.tiled {
				decodedBytes = blockTotalBytes * blocksPerPlane
			} else {
				totalUnitsY := (uint64(height)+uint64(subY)-1)/uint64(subY) + down
				decodedBytes = rowBytes * totalUnitsY
			}
		} else {
			rowBytes = uint64(l.blockWidth) * sampleBytes
			chromaRowBytes = ((uint64(l.blockWidth) + uint64(subX) - 1) / uint64(subX)) * sampleBytes
			chromaBlockH := (uint64(l.blockHeight) + uint64(subY) - 1) / uint64(subY)
			blockTotalBytes = rowBytes*uint64(l.blockHeight) + 2*chromaRowBytes*chromaBlockH
			if l.tiled {
				decodedBytes = blockTotalBytes * blocksPerPlane
			} else {
				totalChromaH := (uint64(height)+uint64(subY)-1)/uint64(subY) + down
				decodedBytes = rowBytes*uint64(height) + 2*chromaRowBytes*totalChromaH
			}
		}
	} else {
		rowBytes = (uint64(l.blockWidth)*rowChannels*uint64(bits) + 7) / 8
		blockTotalBytes = rowBytes * uint64(l.blockHeight) * planes
		decodedBytes = rowBytes * uint64(height) * planes
		if l.tiled {
			decodedBytes = blockTotalBytes * blocksPerPlane
		}
	}
	if blocksPerPlane > rasterMaxWork/planes || blockTotalBytes > 64<<20 || decodedBytes > rasterMaxWork || rowBytes > uint64(^uint(0)>>1)/planes || chromaRowBytes > uint64(^uint(0)>>1) {
		return l, fmt.Errorf("%w: TIFF block decoding budget", ErrLimit)
	}
	l.blocksPerPlane, l.planes, l.count, l.rowBytes, l.rowChannels, l.chromaRowBytes = int(blocksPerPlane), int(planes), int(count), int(rowBytes), int(rowChannels), int(chromaRowBytes)
	var err error
	l.offsets, l.offsetWidth, err = d.field(offsetTag, l.count, true)
	if err != nil {
		return l, err
	}
	l.counts, l.countWidth, err = d.field(countTag, l.count, true)
	if err != nil {
		return l, err
	}
	return l, nil
}

// blockBufferSize 计算单个条带或图块包含全部平面时的最大解压缓冲字节数
// 返回: int 最大解压缓冲字节数
func (l tiffLayout) blockBufferSize() int {
	total := 0
	for plane := range l.planes {
		size, _ := l.planeBufferSize(plane, l.blockHeight)
		total += size
	}
	return total
}

// planeBufferSize 计算指定平面在给定块高度下的解压字节数及PackBits行宽
// 入参: plane 平面序号, blockHeight 当前块高度
// 返回: int 平面解压字节数, int PackBits单行字节数
func (l tiffLayout) planeBufferSize(plane, blockHeight int) (int, int) {
	if l.ycbcrSubX > 1 || l.ycbcrSubY > 1 {
		if l.planes == 1 {
			unitsY := (blockHeight + l.ycbcrSubY - 1) / l.ycbcrSubY
			return l.rowBytes * unitsY, l.rowBytes
		}
		if plane == 0 {
			return l.rowBytes * blockHeight, l.rowBytes
		}
		chromaH := (blockHeight + l.ycbcrSubY - 1) / l.ycbcrSubY
		return l.chromaRowBytes * chromaH, l.chromaRowBytes
	}
	return l.rowBytes * blockHeight, l.rowBytes
}

// region 取得独立压缩块的完整矩形，图块保留图像边界外的填充范围
// 入参: index 已校验的块索引
// 返回: image.Rectangle 存储矩形
func (l tiffLayout) region(index int) image.Rectangle {
	x, y := 0, index*l.blockHeight
	if l.tiled {
		x, y = index%l.across*l.blockWidth, index/l.across*l.blockHeight
	}
	height := l.blockHeight
	if !l.tiled {
		height = min(height, l.height-y)
	}
	return image.Rect(x, y, x+l.blockWidth, y+height)
}

// block 取得已校验字段中的压缩块偏移和字节数
// 入参: d 所属目录, index 块索引
// 返回: uint64 文件偏移, uint64 字节数
func (l tiffLayout) block(d *tiffDirectory, index int) (uint64, uint64) {
	return uint64(d.integer(l.offsets[index*l.offsetWidth:], l.offsetWidth)), uint64(d.integer(l.counts[index*l.countWidth:], l.countWidth))
}

// legacyJPEG 读取TIFF/JPEG字段，码表按JPEG字节序解释，不采用应用标记的颜色定义
// 入参: width 图像宽度, height 图像高度, photo TIFF颜色解释, channels 分量数, bits 样本位数
// 返回: tiffLegacyJPEG 独立块重建参数, error 字段、码表或能力错误
func (d *tiffDirectory) legacyJPEG(width, height, photo, channels, bits uint32) (tiffLegacyJPEG, error) {
	l := tiffLegacyJPEG{channels: int(channels)}
	if d.entry[512] == nil {
		return l, fmt.Errorf("%w: missing TIFF JPEG process", ErrInvalid)
	}
	process, err := d.number(512, 0, false)
	if err != nil {
		return l, err
	}
	if process != 1 {
		if process == 14 {
			return d.legacyLosslessJPEG(width, height, photo, channels, bits)
		}
		return l, fmt.Errorf("%w: TIFF JPEG process", ErrInvalid)
	}
	if bits != 8 {
		return l, fmt.Errorf("%w: TIFF baseline JPEG precision", ErrInvalid)
	}
	if channels < 1 || channels > 4 {
		return l, fmt.Errorf("%w: TIFF JPEG component count", ErrUnsupported)
	}
	for c := range l.channels {
		l.sampling[c] = 0x11
		l.scanOrder[c] = byte(c)
	}
	if photo == 6 {
		x, y := uint32(2), uint32(2)
		if d.entry[530] != nil {
			field, _, e := d.field(530, 2, false)
			if e != nil {
				return l, e
			}
			x, y = uint32(d.order.Uint16(field)), uint32(d.order.Uint16(field[2:]))
		}
		if x != 1 && x != 2 && x != 4 || y != 1 && y != 2 && y != 4 {
			return l, fmt.Errorf("%w: TIFF JPEG sampling factors", ErrInvalid)
		}
		if x*y+2 > 10 {
			return l, fmt.Errorf("%w: TIFF JPEG MCU component blocks", ErrInvalid)
		}
		l.sampling[0] = byte(x<<4 | y)
	}
	restart, err := d.number(515, 0, false)
	if err != nil {
		return l, err
	}
	l.restart = uint16(restart)
	l.tables = []byte{0xff, 0xd8}
	var definitions [3][4][]byte
	var counts [3]int
	for kind, tag := range []uint16{519, 520, 521} {
		entry := d.entry[tag]
		if entry == nil || d.order.Uint16(entry[2:]) != 4 {
			return l, fmt.Errorf("%w: TIFF JPEG table offset field %d", ErrInvalid, tag)
		}
		field, _, e := d.field(tag, l.channels, true)
		if e != nil {
			return l, e
		}
		for c := range l.channels {
			offset := uint64(d.order.Uint32(field[c*4:]))
			size := uint64(64)
			marker := byte(0xdb)
			if tag != 519 {
				marker = 0xc4
				if offset > uint64(len(d.data)) || uint64(len(d.data))-offset < 16 {
					return l, fmt.Errorf("%w: TIFF JPEG Huffman table offset", ErrInvalid)
				}
				size = 16
				for _, count := range d.data[offset : offset+16] {
					size += uint64(count)
				}
			}
			if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
				return l, fmt.Errorf("%w: TIFF JPEG table range", ErrInvalid)
			}
			definition := d.data[offset : offset+size]
			id := counts[kind]
			for slot := range counts[kind] {
				if bytes.Equal(definitions[kind][slot], definition) {
					id = slot
					break
				}
			}
			selector := byte(id)
			if tag == 521 {
				selector |= 0x10
			}
			if tag != 519 && id > 1 {
				return l, fmt.Errorf("%w: TIFF baseline JPEG Huffman table count", ErrUnsupported)
			}
			switch tag {
			case 519:
				l.quant[c] = byte(id)
			case 520:
				l.dc[c] = byte(id)
			case 521:
				l.ac[c] = byte(id)
			}
			if id < counts[kind] {
				continue
			}
			definitions[kind][id] = definition
			counts[kind]++
			payload := make([]byte, 1+int(size))
			payload[0] = selector
			copy(payload[1:], d.data[offset:offset+size])
			if _, _, e := tiffJPEGSlots(payload, marker); e != nil {
				return l, e
			}
			if tag == 520 {
				for _, symbol := range payload[17:] {
					if symbol > 11 {
						return l, fmt.Errorf("%w: TIFF baseline JPEG DC category", ErrInvalid)
					}
				}
			}
			l.tables = appendTIFFJPEGMarker(l.tables, marker, payload)
		}
	}
	interchange, err := d.legacyInterchange()
	if err != nil {
		return l, err
	}
	if interchange != nil {
		stream, e := normalizeTIFFJPEG(interchange, false, tiffJPEGTable{})
		if e != nil {
			return l, e
		}
		if stream.process != 0xc0 || stream.components != l.channels || !bytes.Equal(stream.sampling[:l.channels], l.sampling[:l.channels]) {
			return l, fmt.Errorf("%w: TIFF JPEG interchange frame", ErrInvalid)
		}
		config, e := jpeg.DecodeConfig(bytes.NewReader(stream.data))
		if e != nil {
			return l, tiffJPEGDecodeError(e)
		}
		if config.Width != int(width) || config.Height != int(height) {
			return l, fmt.Errorf("%w: TIFF JPEG interchange dimensions", ErrInvalid)
		}
		if err := l.checkInterchange(stream.data); err != nil {
			return l, err
		}
		l.interchange = true
	}
	return l, nil
}

// legacyInterchange 读取可选JPEG交换码流，非零偏移必须具有完整且有界的长度字段
// 返回: []byte 码流视图，缺省时为nil, error 字段或资源错误
func (d *tiffDirectory) legacyInterchange() ([]byte, error) {
	if d.entry[513] != nil && d.order.Uint16(d.entry[513][2:]) != 4 {
		return nil, fmt.Errorf("%w: TIFF JPEG interchange offset type", ErrInvalid)
	}
	offset, err := d.number(513, 0, true)
	if err != nil || offset == 0 {
		return nil, err
	}
	if d.entry[514] == nil || d.order.Uint16(d.entry[514][2:]) != 4 {
		return nil, fmt.Errorf("%w: TIFF JPEG interchange length field", ErrInvalid)
	}
	length, err := d.number(514, 0, true)
	if err != nil {
		return nil, err
	}
	if length < 4 || uint64(offset) > uint64(len(d.data)) || uint64(length) > uint64(len(d.data))-uint64(offset) {
		return nil, fmt.Errorf("%w: TIFF JPEG interchange range", ErrInvalid)
	}
	if length > rasterMaxWork {
		return nil, fmt.Errorf("%w: TIFF JPEG interchange budget", ErrLimit)
	}
	return d.data[uint64(offset) : uint64(offset)+uint64(length)], nil
}

// readTIFFLegacyHeader 读取已规范化码流的基线头，保留码表视图用于跨字段一致性检查
// 入参: data 完整码流或内部码表头
// 返回: tiffLegacyHeader 头定义, error 结构错误
func readTIFFLegacyHeader(data []byte) (tiffLegacyHeader, error) {
	var h tiffLegacyHeader
	for pos := 2; pos < len(data); {
		if data[pos] != 0xff {
			return h, fmt.Errorf("%w: TIFF JPEG header marker", ErrInvalid)
		}
		for pos < len(data) && data[pos] == 0xff {
			pos++
		}
		if len(data)-pos < 3 {
			return h, fmt.Errorf("%w: TIFF JPEG header marker length", ErrInvalid)
		}
		marker := data[pos]
		pos++
		length := int(binary.BigEndian.Uint16(data[pos:]))
		if length < 2 || length > len(data)-pos {
			return h, fmt.Errorf("%w: TIFF JPEG header length", ErrInvalid)
		}
		payload := data[pos+2 : pos+length]
		pos += length
		switch marker {
		case 0xdb, 0xc4:
			for len(payload) > 0 {
				selector := payload[0]
				payload = payload[1:]
				size := 64 * (1 + int(selector>>4))
				if marker == 0xc4 {
					if len(payload) < 16 || selector>>4 > 1 {
						return h, fmt.Errorf("%w: TIFF JPEG header Huffman table", ErrInvalid)
					}
					size = 16
					for _, count := range payload[:16] {
						size += int(count)
					}
				}
				if selector&15 > 3 || selector>>4 > 1 || size > len(payload) {
					return h, fmt.Errorf("%w: TIFF JPEG header table range", ErrInvalid)
				}
				if marker == 0xdb {
					h.quant[selector&15] = payload[:size]
				} else {
					h.huffman[int(selector&15)+int(selector>>4)*4] = payload[:size]
				}
				payload = payload[size:]
			}
		case 0xc0, 0xc3:
			h.frame = payload
		case 0xdd:
			if len(payload) != 2 {
				return h, fmt.Errorf("%w: TIFF JPEG restart header", ErrInvalid)
			}
			h.restart = binary.BigEndian.Uint16(payload)
		case 0xda:
			h.scan = payload
			return h, nil
		default:
			return h, fmt.Errorf("%w: TIFF baseline JPEG header marker", ErrInvalid)
		}
	}
	return h, nil
}

// checkInterchange 核对交换码流和TIFF字段的逐分量码表及扫描定义，不按码表编号直接比较内容
// 入参: data 已规范化的完整交换码流
// 返回: error 冲突或结构错误
func (l *tiffLegacyJPEG) checkInterchange(data []byte) error {
	source, err := readTIFFLegacyHeader(data)
	if err != nil {
		return err
	}
	tables, err := readTIFFLegacyHeader(l.tables)
	if err != nil {
		return err
	}
	if len(source.frame) != 6+3*l.channels || source.frame[0] != 8 || len(source.scan) != 4+2*l.channels || int(source.scan[0]) != l.channels || !bytes.Equal(source.scan[len(source.scan)-3:], []byte{0, 63, 0}) || source.restart != l.restart {
		return fmt.Errorf("%w: TIFF JPEG interchange scan definition", ErrInvalid)
	}
	var seen [4]bool
	for scanIndex := range l.channels {
		identity := source.scan[1+scanIndex*2]
		component := -1
		for c := range l.channels {
			if source.frame[6+c*3] == identity {
				component = c
				break
			}
		}
		if component < 0 || seen[component] {
			return fmt.Errorf("%w: TIFF JPEG interchange component identity", ErrInvalid)
		}
		seen[component] = true
		l.scanOrder[scanIndex] = byte(component)
		quant := source.frame[8+component*3]
		selectors := source.scan[2+scanIndex*2]
		if quant > 3 || selectors>>4 > 1 || selectors&15 > 1 || len(source.quant[quant]) == 0 || len(source.huffman[selectors>>4]) == 0 || len(source.huffman[4+int(selectors&15)]) == 0 {
			return fmt.Errorf("%w: TIFF JPEG interchange table selector", ErrInvalid)
		}
		if !bytes.Equal(source.quant[quant], tables.quant[l.quant[component]]) || !bytes.Equal(source.huffman[selectors>>4], tables.huffman[l.dc[component]]) || !bytes.Equal(source.huffman[4+int(selectors&15)], tables.huffman[4+int(l.ac[component])]) {
			return fmt.Errorf("%w: conflicting TIFF JPEG interchange tables", ErrInvalid)
		}
	}
	return nil
}

// appendTIFFJPEGMarker 写入有长度字段的JPEG标记，负载已经过调用方校验
// 入参: dst 目标码流, marker 标记编号, payload 标记负载
// 返回: []byte 追加后的码流
func appendTIFFJPEGMarker(dst []byte, marker byte, payload []byte) []byte {
	size := len(payload) + 2
	dst = append(dst, 0xff, marker, byte(size>>8), byte(size))
	return append(dst, payload...)
}

// stream 将独立熵编码块重建为完整JPEG码流，重启编号转换为块内的顺序
// 入参: entropy TIFF熵编码字节, region 完整存储矩形
// 返回: []byte JPEG码流, error 码流或资源错误
func (l *tiffLegacyJPEG) stream(entropy []byte, region image.Rectangle) ([]byte, error) {
	if region.Dx() < 1 || region.Dy() < 1 || region.Dx() > 65535 || region.Dy() > 65535 {
		return nil, fmt.Errorf("%w: TIFF JPEG frame dimensions", ErrLimit)
	}
	if uint64(len(entropy))+uint64(len(l.tables))+128 > rasterMaxWork {
		return nil, fmt.Errorf("%w: TIFF JPEG block budget", ErrLimit)
	}
	data := make([]byte, 0, len(entropy)+len(l.tables)+128)
	data = append(data, l.tables...)
	frame := []byte{8, byte(region.Dy() >> 8), byte(region.Dy()), byte(region.Dx() >> 8), byte(region.Dx()), byte(l.channels)}
	scan := []byte{byte(l.channels)}
	for c := range l.channels {
		frame = append(frame, byte(c+1), l.sampling[c], l.quant[c])
		component := l.scanOrder[c]
		scan = append(scan, component+1, l.dc[component]<<4|l.ac[component])
	}
	data = appendTIFFJPEGMarker(data, 0xc0, frame)
	if l.restart != 0 {
		data = appendTIFFJPEGMarker(data, 0xdd, []byte{byte(l.restart >> 8), byte(l.restart)})
	}
	scan = append(scan, 0, 63, 0)
	data = appendTIFFJPEGMarker(data, 0xda, scan)
	previous, local := -1, byte(0)
	for pos := 0; pos < len(entropy); {
		if entropy[pos] != 0xff {
			data = append(data, entropy[pos])
			pos++
			continue
		}
		start := pos
		for pos < len(entropy) && entropy[pos] == 0xff {
			pos++
		}
		if pos == len(entropy) {
			return nil, fmt.Errorf("%w: TIFF JPEG entropy marker", ErrInvalid)
		}
		marker := entropy[pos]
		pos++
		if marker == 0 && pos-start == 2 {
			data = append(data, 0xff, 0)
		} else if marker >= 0xd0 && marker <= 0xd7 {
			if l.restart == 0 || previous >= 0 && int(marker-0xd0) != (previous+1)&7 {
				return nil, fmt.Errorf("%w: TIFF JPEG entropy restart sequence", ErrInvalid)
			}
			previous = int(marker - 0xd0)
			data = append(data, 0xff, 0xd0+local)
			local = (local + 1) & 7
		} else {
			return nil, fmt.Errorf("%w: TIFF JPEG entropy marker %x", ErrInvalid, marker)
		}
	}
	data = append(data, 0xff, 0xd9)
	return data, nil
}

// signedSample16 将全通道有符号二进制补码样本按SMinSampleValue/SMaxSampleValue或标准有符号范围线性映射到十六位
// 入参: raw 原始位宽样本值, channel 通道序号, scale 无符号位宽缩放因子
// 返回: uint16 十六位归一化样本
func (f *tiffPixelFormat) signedSample16(raw uint16, channel int, scale uint16) uint16 {
	if !f.hasSMin && !f.hasSMax {
		if f.bits == 16 {
			return raw ^ 0x8000
		}
		return (raw ^ 0x80) * scale
	}
	var v float64
	if f.bits == 16 {
		v = float64(int16(raw))
	} else {
		v = float64(int8(raw))
	}
	norm := (v - f.sMin[channel]) / (f.sMax[channel] - f.sMin[channel])
	if norm <= 0 {
		return 0
	}
	if norm >= 1 {
		return 65535
	}
	return uint16(math.Round(norm * 65535))
}

// tiffClampUint16 将浮点色彩值钳位并四舍五入为十六位无符号整数样本
// 入参: v 待量化浮点样本值
// 返回: uint16 十六位无符号样本
func tiffClampUint16(v float64) uint16 {
	if v <= 0 {
		return 0
	}
	if v >= 65535 {
		return 65535
	}
	return uint16(math.Round(v))
}

// ycbcrToNRGBA64 按TIFF 6.0第21节系数与参考黑白电平将YCbCr编码样本转换为十六位非预乘RGB像素
// 入参: yCode 亮度编码值, cbCode 蓝色色差编码值, crCode 红色色差编码值, alpha 十六位透明度
// 返回: color.NRGBA64 十六位非预乘颜色
func (f *tiffPixelFormat) ycbcrToNRGBA64(yCode, cbCode, crCode float64, alpha uint16) color.NRGBA64 {
	codingY, codingC, scaleOut := 255.0, 127.0, 257.0
	if f.bits == 16 {
		codingY, codingC, scaleOut = 65535.0, 32767.0, 1.0
	}
	yVal := (yCode - f.ycbcr.refBW[0]) * codingY / (f.ycbcr.refBW[1] - f.ycbcr.refBW[0])
	cbVal := (cbCode - f.ycbcr.refBW[2]) * codingC / (f.ycbcr.refBW[3] - f.ycbcr.refBW[2])
	crVal := (crCode - f.ycbcr.refBW[4]) * codingC / (f.ycbcr.refBW[5] - f.ycbcr.refBW[4])
	rNorm := crVal*(2-2*f.ycbcr.lumaRed) + yVal
	bNorm := cbVal*(2-2*f.ycbcr.lumaBlue) + yVal
	gNorm := (yVal - f.ycbcr.lumaBlue*bNorm - f.ycbcr.lumaRed*rNorm) / f.ycbcr.lumaGreen
	return color.NRGBA64{
		R: tiffClampUint16(rNorm * scaleOut),
		G: tiffClampUint16(gNorm * scaleOut),
		B: tiffClampUint16(bNorm * scaleOut),
		A: alpha,
	}
}

// readSampleCode 按像素位深与文件字节序读取单个无符号整数编码值
// 入参: buf 样本字节切片, offset 字节偏移
// 返回: float64 原始样本编码值
func (f *tiffPixelFormat) readSampleCode(buf []byte, offset int) float64 {
	if f.bits == 16 {
		return float64(f.order.Uint16(buf[offset:]))
	}
	return float64(buf[offset])
}

// writeSubsampledYCbCrRow 将子采样Chunky或Planar YCbCr块中的指定可见行转换为RGB并写入目标图像
// 入参: out 目标图像, x0 目标起始列, dstY 目标行号, width 可见列数, srcY 块内源行号, layout 块布局, block 已解压块缓冲, planeOffsets 各平面偏移
func (f *tiffPixelFormat) writeSubsampledYCbCrRow(out *image.NRGBA64, x0, dstY, width, srcY int, layout tiffLayout, block []byte, planeOffsets [5]int) {
	subX, subY := layout.ycbcrSubX, layout.ycbcrSubY
	sampleBytes := int(f.bits / 8)
	if layout.planes == 1 {
		uy, ly := srcY/subY, srcY%subY
		unitSamples := subX*subY + 2
		unitRowOff := uy * layout.rowBytes
		for x := range width {
			ux, lx := x/subX, x%subX
			unitOff := unitRowOff + ux*unitSamples*sampleBytes
			yCode := f.readSampleCode(block, unitOff+(ly*subX+lx)*sampleBytes)
			cbCode := f.readSampleCode(block, unitOff+(subX*subY)*sampleBytes)
			crCode := f.readSampleCode(block, unitOff+(subX*subY+1)*sampleBytes)
			out.SetNRGBA64(x0+x, dstY, f.ycbcrToNRGBA64(yCode, cbCode, crCode, 65535))
		}
		return
	}
	cy := srcY / subY
	yRowOff := planeOffsets[0] + srcY*layout.rowBytes
	cbRowOff := planeOffsets[1] + cy*layout.chromaRowBytes
	crRowOff := planeOffsets[2] + cy*layout.chromaRowBytes
	for x := range width {
		cx := x / subX
		yCode := f.readSampleCode(block, yRowOff+x*sampleBytes)
		cbCode := f.readSampleCode(block, cbRowOff+cx*sampleBytes)
		crCode := f.readSampleCode(block, crRowOff+cx*sampleBytes)
		out.SetNRGBA64(x0+x, dstY, f.ycbcrToNRGBA64(yCode, cbCode, crCode, 65535))
	}
}

// writeRowRange 将压缩块中的可见行区间转换为非预乘16位颜色，不读取边界填充
// 入参: out 目标图像, x0 目标起始列, y 目标行号, width 可见列数, row 完整存储行
func (f *tiffPixelFormat) writeRowRange(out *image.NRGBA64, x0, y, width int, row []byte) {
	scale := uint16(65535 / ((1 << f.bits) - 1))
	for x := range width {
		var sample [4]uint16
		for c := range int(f.channels) {
			bit := (x*int(f.channels) + c) * int(f.bits)
			switch f.bits {
			case 16:
				raw := f.order.Uint16(row[bit/8:])
				if f.sampleFormat == 2 {
					sample[c] = f.signedSample16(raw, c, 1)
				} else {
					sample[c] = raw
				}
			case 8:
				raw := uint16(row[bit/8])
				if f.sampleFormat == 2 {
					sample[c] = f.signedSample16(raw, c, scale)
				} else {
					sample[c] = raw
				}
			default:
				sample[c] = uint16(row[bit/8]>>uint(8-int(f.bits)-bit%8)) & uint16((1<<f.bits)-1)
			}
		}
		var pixel color.NRGBA64
		if f.photo == 3 {
			stride := 2 * (1 << f.bits)
			index := int(sample[0]) * 2
			pixel = color.NRGBA64{f.order.Uint16(f.palette[index:]), f.order.Uint16(f.palette[stride+index:]), f.order.Uint16(f.palette[2*stride+index:]), 65535}
		} else if f.photo == 6 {
			alpha := uint16(65535)
			if f.alpha != 0 {
				alpha = sample[f.channels-1] * scale
			}
			pixel = f.ycbcrToNRGBA64(float64(sample[0]), float64(sample[1]), float64(sample[2]), alpha)
			if f.alpha == 1 {
				if pixel.A == 0 {
					pixel.R, pixel.G, pixel.B = 0, 0, 0
				} else {
					pixel.R = imageUnassociateSample(pixel.R, pixel.A)
					pixel.G = imageUnassociateSample(pixel.G, pixel.A)
					pixel.B = imageUnassociateSample(pixel.B, pixel.A)
				}
			}
		} else {
			if f.sampleFormat != 2 {
				for c := range int(f.channels) {
					sample[c] *= scale
				}
			}
			if f.alpha == 1 {
				for c := range int(f.channels) - 1 {
					sample[c] = imageUnassociateSample(sample[c], sample[f.channels-1])
				}
			}
			if f.photo == 0 {
				sample[0] = 65535 - sample[0]
			}
			pixel = color.NRGBA64{sample[0], sample[0], sample[0], 65535}
			if f.photo == 2 {
				pixel.G, pixel.B = sample[1], sample[2]
			}
			if f.alpha != 0 {
				pixel.A = sample[f.channels-1]
				if f.alpha == 1 && pixel.A == 0 {
					pixel.R, pixel.G, pixel.B = 0, 0, 0
				}
			}
		}
		out.SetNRGBA64(x0+x, y, pixel)
	}
}

// imageUnassociateSample 还原16位原生预乘分量并四舍五入，舍弃超出单位区间的发光部分
// 入参: value 预乘分量, alpha 透明度
// 返回: uint16 非预乘单位区间分量
func imageUnassociateSample(value, alpha uint16) uint16 {
	if alpha == 0 {
		return 0
	}
	return uint16(min(65535, (uint32(value)*65535+uint32(alpha)/2)/uint32(alpha)))
}

// writeComponentRange 将压缩块的可见行区间写入原生分量图像，透明度不参与颜色转换
// 入参: out 原生分量图像, x0 目标起始列, y 目标行, width 可见列数, row 完整存储行
func (f *tiffPixelFormat) writeComponentRange(out *imageComponents, x0, y, width int, row []byte) {
	stride := out.channels
	if out.alpha {
		stride++
	}
	scale := uint16(65535 / ((1 << f.bits) - 1))
	for x := range width {
		var sample [5]uint16
		for channel := range int(f.channels) {
			at := (x*int(f.channels) + channel) * int(f.bits/8)
			if f.bits == 16 {
				value := f.order.Uint16(row[at:])
				if f.sampleFormat == 2 {
					sample[channel] = f.signedSample16(value, channel, 1)
				} else {
					sample[channel] = value
				}
			} else {
				value := uint16(row[at])
				if f.sampleFormat == 2 {
					sample[channel] = f.signedSample16(value, channel, scale)
				} else {
					sample[channel] = value * scale
				}
			}
		}
		at := (y*out.bounds.Dx() + x0 + x) * stride
		for channel := range out.channels {
			value := sample[channel]
			if f.alpha == 1 {
				value = imageUnassociateSample(value, sample[f.channels-1])
			}
			out.values[at+channel] = value
		}
		if out.alpha {
			out.values[at+out.channels] = sample[f.channels-1]
		}
	}
}

// writeFloatRange 将32位浮点存储行的可见区间写入扩展范围原生分量，校验全部通道有限性并按需展开预乘透明度
// 入参: out 浮点原生分量图像, x0 目标起始列, y 目标行, width 可见列数, row 完整交织存储行
// 返回: error 预乘、颜色或透明度非有限错误
func (f *tiffPixelFormat) writeFloatRange(out *imageComponents, x0, y, width int, row []byte) error {
	stride := out.channels
	if out.alpha {
		stride++
	}
	for x := range width {
		var sample [5]float64
		for channel := range int(f.channels) {
			at := (x*int(f.channels) + channel) * 4
			sample[channel] = float64(math.Float32frombits(f.order.Uint32(row[at:])))
		}
		alpha := 1.0
		if f.alpha != 0 {
			alpha = sample[f.channels-1]
			if !geometryFinite(alpha) {
				return fmt.Errorf("%w: TIFF non-finite alpha", ErrUnsupported)
			}
			alpha = colorClamp(alpha)
		}
		at := (y*out.bounds.Dx() + x0 + x) * stride
		for channel := range out.channels {
			value := sample[channel]
			if !geometryFinite(value) {
				return fmt.Errorf("%w: TIFF non-finite color", ErrUnsupported)
			}
			if f.alpha == 1 {
				if alpha == 0 {
					value = 0
				} else {
					value /= alpha
					if !geometryFinite(value) {
						return fmt.Errorf("%w: TIFF non-finite color", ErrUnsupported)
					}
					if f.photo == 0 {
						value = 1 - value
					}
				}
			} else if f.photo == 0 {
				value = 1 - value
			}
			out.floating[at+channel] = value
		}
		if out.alpha {
			out.floating[at+out.channels] = alpha
		}
	}
	return nil
}
