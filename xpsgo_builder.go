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
	"fmt"
	"hash/crc32"
	"image"
	"image/color"
	"image/draw"
	"image/jpeg"
	"image/png"
	"io"
	"math"
	"net/url"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/xiaoqidun/jxrgo"
)

const (
	// ImageFormatAuto 表示按源图像色彩模型与质量配置自动选择编码格式
	ImageFormatAuto ImageEncodeFormat = iota
	// ImageFormatPNG 表示编码为标准PNG图像
	ImageFormatPNG
	// ImageFormatJPEG 表示编码为标准JPEG图像
	ImageFormatJPEG
	// ImageFormatTIFF 表示编码为标准Baseline TIFF图像
	ImageFormatTIFF
	// ImageFormatJXR 表示编码为标准JPEG XR图像
	ImageFormatJXR
)

const (
	// TIFFCompressionNone 表示不压缩TIFF像素数据
	TIFFCompressionNone TIFFCompression = iota
	// TIFFCompressionPackBits 表示采用TIFF PackBits字节游程无损压缩
	TIFFCompressionPackBits
	// TIFFCompressionDeflate 表示采用Adobe Deflate无损压缩，部分老旧Windows XPS消费者兼容性弱于TIFFCompressionLZW与TIFFCompressionPackBits
	TIFFCompressionDeflate
	// TIFFCompressionLZW 表示采用TIFF 6.0标准MSB优先LZW无损压缩
	TIFFCompressionLZW
	// TIFFCompressionCCITTGroup4 表示采用ITU-T T.6二维游程无损压缩，输出1位二值黑白TIFF图像
	TIFFCompressionCCITTGroup4
)

// tiffTargetStripBytes 定义多Strip TIFF写出时单条带的目标未压缩字节数
const tiffTargetStripBytes = 64 << 10

// pngStreamIDATChunk 定义逐行流式PNG编码器的单个IDAT块目标载荷长度
const pngStreamIDATChunk = 32 << 10

// ColorCMYK16Model 表示每通道16位无符号CMYK图像的标准颜色转换模型
var ColorCMYK16Model color.Model = color.ModelFunc(cmyk16Model)

// tiffFaxWhiteEncode 保存ITU-T T.4/T.6白色游程的编码表，高16位为位宽，低16位为MSB码字
var tiffFaxWhiteEncode = buildTIFFFaxEncodeTable([]string{
	"00110101", "000111", "0111", "1000", "1011", "1100", "1110", "1111",
	"10011", "10100", "00111", "01000", "001000", "000011", "110100", "110101",
	"101010", "101011", "0100111", "0001100", "0001000", "0010111", "0000011", "0000100",
	"0101000", "0101011", "0010011", "0100100", "0011000", "00000010", "00000011", "00011010",
	"00011011", "00010010", "00010011", "00010100", "00010101", "00010110", "00010111", "00101000",
	"00101001", "00101010", "00101011", "00101100", "00101101", "00000100", "00000101", "00001010",
	"00001011", "01010010", "01010011", "01010100", "01010101", "00100100", "00100101", "01011000",
	"01011001", "01011010", "01011011", "01001010", "01001011", "00110010", "00110011", "00110100",
	"11011", "10010", "010111", "0110111", "00110110", "00110111", "01100100", "01100101",
	"01101000", "01100111", "011001100", "011001101", "011010010", "011010011", "011010100", "011010101",
	"011010110", "011010111", "011011000", "011011001", "011011010", "011011011", "010011000", "010011001",
	"010011010", "011000", "010011011", "00000001000", "00000001100", "00000001101", "000000010010", "000000010011",
	"000000010100", "000000010101", "000000010110", "000000010111", "000000011100", "000000011101", "000000011110", "000000011111",
})

// tiffFaxBlackEncode 保存ITU-T T.4/T.6黑色游程的编码表，高16位为位宽，低16位为MSB码字
var tiffFaxBlackEncode = buildTIFFFaxEncodeTable([]string{
	"0000110111", "010", "11", "10", "011", "0011", "0010", "00011",
	"000101", "000100", "0000100", "0000101", "0000111", "00000100", "00000111", "000011000",
	"0000010111", "0000011000", "0000001000", "00001100111", "00001101000", "00001101100", "00000110111", "00000101000",
	"00000010111", "00000011000", "000011001010", "000011001011", "000011001100", "000011001101", "000001101000", "000001101001",
	"000001101010", "000001101011", "000011010010", "000011010011", "000011010100", "000011010101", "000011010110", "000011010111",
	"000001101100", "000001101101", "000011011010", "000011011011", "000001010100", "000001010101", "000001010110", "000001010111",
	"000001100100", "000001100101", "000001010010", "000001010011", "000000100100", "000000110111", "000000111000", "000000100111",
	"000000101000", "000001011000", "000001011001", "000000101011", "000000101100", "000001011010", "000001100110", "000001100111",
	"0000001111", "000011001000", "000011001001", "000001011011", "000000110011", "000000110100", "000000110101", "0000001101100",
	"0000001101101", "0000001001010", "0000001001011", "0000001001100", "0000001001101", "0000001110010", "0000001110011", "0000001110100",
	"0000001110101", "0000001110110", "0000001110111", "0000001010010", "0000001010011", "0000001010100", "0000001010101", "0000001011010",
	"0000001011011", "0000001100100", "0000001100101", "00000001000", "00000001100", "00000001101", "000000010010", "000000010011",
	"000000010100", "000000010101", "000000010110", "000000010111", "000000011100", "000000011101", "000000011110", "000000011111",
})

// ImageEncodeFormat 表示写侧嵌入Go图像时使用的编码格式
type ImageEncodeFormat uint8

// TIFFCompression 表示写侧编码TIFF图像时使用的无损压缩方式
type TIFFCompression uint8

// ImageEncodeOptions 设置Go图像编码的格式、TIFF压缩方式、质量、分辨率、ICC配置文件与内容去重选项
// Quality在1至99时启用有损编码，0或100在JXR下采用无损编码，在JPEG下0采用默认质量90；TIFFCompression仅在输出TIFF时生效
type ImageEncodeOptions struct {
	Format          ImageEncodeFormat
	TIFFCompression TIFFCompression
	Quality         int
	DPIX            float64
	DPIY            float64
	ICCProfile      []byte
	Deduplicate     bool
}

// AddImageOptions 设置原始图像字节嵌入时的去重等选项
type AddImageOptions struct {
	Deduplicate bool
}

// ResourceEntry 表示资源字典中的单条有序键与类型化资源定义
// Value支持*Brush、*Geometry、*Matrix、Matrix、*Path、*Glyphs与*Canvas
type ResourceEntry struct {
	Key   string
	Value any
}

// ResourceDictionary 表示页面或画布的内联资源字典、远程字典引用或独立远程资源字典
// Source非空时表示引用远程字典部件且Entries必须为空
type ResourceDictionary struct {
	Source  string
	Entries []ResourceEntry
}

// GlyphsBuildOptions 设置GlyphsBuilder构建字形元素时的双向级别、竖排、模拟样式、画刷、步进省略与缺字策略
// OmitDefaultAdvanceWidth启用且Tracking为零时省略与字体默认步进等价的AdvanceWidth；RejectMissingGlyphs启用时遇到缺字返回ErrInvalid
type GlyphsBuildOptions struct {
	BidiLevel               int
	IsSideways              bool
	StyleSimulations        StyleSimulation
	Fill                    *Brush
	CaretStops              string
	DeviceFontName          string
	Name                    string
	Language                *string
	NavigateURI             *string
	Opacity                 *float64
	RenderTransform         *Matrix
	RenderTransformResource string
	Clip                    *Geometry
	OpacityMask             *Brush
	Tracking                float64
	OmitDefaultAdvanceWidth bool
	RejectMissingGlyphs     bool
}

// GlyphBuildItem 表示复合簇构建器中的单个显式字形条目，AdvanceWidth、UOffset与VOffset采用1/100 em单位
// 默认输出GlyphID；OmitGlyphID为true时省略字形索引并交由UnicodeString单码点查cmap
type GlyphBuildItem struct {
	GlyphID         uint16
	OmitGlyphID     bool
	AdvanceWidth    float64
	HasAdvanceWidth bool
	UOffset         float64
	HasUOffset      bool
	VOffset         float64
	HasVOffset      bool
}

// GlyphBuildCluster 表示复合簇构建器中的逻辑文本片段及其对应的一个或多个字形条目
type GlyphBuildCluster struct {
	Text   string
	Glyphs []GlyphBuildItem
}

// GlyphsBuilder 基于字体资源与字号构建严格合标的XPS Glyphs绘制元素
type GlyphsBuilder struct {
	fontURI string
	font    *FontResource
	emSize  float64
}

// GeometryBuilder 通过链式子路径与曲线段操作构建类型化XPS路径几何
type GeometryBuilder struct {
	fillRule          GeometryFillRule
	figures           []GeometryFigure
	current           int
	hasCurrent        bool
	stroked           bool
	transform         *Matrix
	transformResource string
	err               error
}

// ColorCMYK16 表示每通道16位无符号精度的CMYK颜色
type ColorCMYK16 struct {
	C uint16
	M uint16
	Y uint16
	K uint16
}

// ImageCMYK16 表示每通道16位无符号精度的CMYK内存图像，Pix按大端C、M、Y、K顺序存放每像素8字节
type ImageCMYK16 struct {
	Pix    []uint8
	Stride int
	Rect   image.Rectangle
}

// OutlineBuilderOptions 设置目录书签构建器的默认目录语言及基准部件路径
// DocumentPart为空默认使用/Documents/1/FixedDoc.fdoc，SequencePart为空默认使用/FixedDocSeq.fdseq，StructurePart为空默认取DocumentPart同目录下的Structure1.struct
type OutlineBuilderOptions struct {
	Language      string
	StructurePart string
	DocumentPart  string
	SequencePart  string
}

// OutlineEntryOptions 设置单个目录书签节点的可选xml:lang语言覆盖
type OutlineEntryOptions struct {
	Language string
}

// OutlineBuilder 协同构建合标的XPS DocumentOutline目录树并自动为目标Page补齐与去重LinkTargets
type OutlineBuilder struct {
	language      string
	structurePart string
	documentPart  string
	sequencePart  string
	entries       []OutlineEntry
	stories       []Story
	usedAnchors   map[string]*Page
	autoSeq       int
	err           error
}

// tiffStripSpec 描述多Strip TIFF的像素布局、压缩方式、分辨率与可选ICC配置
type tiffStripSpec struct {
	width        int
	height       int
	rowsPerStrip int
	spp          uint16
	bps          uint16
	photometric  uint16
	extraSample  uint16
	hasExtra     bool
	compression  TIFFCompression
	dpix         float64
	dpiy         float64
	icc          []byte
}

// tiffBitWriter 按MSB优先顺序向有界缓冲写出变长位码流
type tiffBitWriter struct {
	out   []byte
	acc   uint64
	bits  uint
	limit int64
}

// pngIDATWriter 将zlib压缩流分块封装为标准PNG IDAT数据块写入底层输出流
type pngIDATWriter struct {
	w   io.Writer
	buf []byte
}

// pngRowEncoder 逐行接收原始扫描行并流式写出合规PNG字节流，不缓冲整幅未压缩图像
type pngRowEncoder struct {
	w        io.Writer
	idat     pngIDATWriter
	zw       *zlib.Writer
	height   int
	rowBytes int
	rows     int
	closed   bool
}

// StoryFragmentsBuilder 链式构建合标的XPS StoryFragments页面故事片段与语义结构树
type StoryFragmentsBuilder struct {
	part      string
	fragments []StoryFragment
	err       error
}

// String 返回图像编码格式的可读名称
// 返回: string 格式名称
func (f ImageEncodeFormat) String() string {
	switch f {
	case ImageFormatAuto:
		return "auto"
	case ImageFormatPNG:
		return "png"
	case ImageFormatJPEG:
		return "jpeg"
	case ImageFormatTIFF:
		return "tiff"
	case ImageFormatJXR:
		return "jxr"
	default:
		return fmt.Sprintf("ImageEncodeFormat(%d)", f)
	}
}

// String 返回TIFF压缩方式的可读名称
// 返回: string 压缩方式名称
func (c TIFFCompression) String() string {
	switch c {
	case TIFFCompressionNone:
		return "none"
	case TIFFCompressionPackBits:
		return "packbits"
	case TIFFCompressionDeflate:
		return "deflate"
	case TIFFCompressionLZW:
		return "lzw"
	case TIFFCompressionCCITTGroup4:
		return "ccitt-group4"
	default:
		return fmt.Sprintf("TIFFCompression(%d)", c)
	}
}

// RGBA 将16位CMYK颜色转换为标准Go预乘16位RGBA四元组，实现color.Color标准Interface
// 返回: uint32 红色分量, uint32 绿色分量, uint32 蓝色分量, uint32 不透明Alpha分量
func (c ColorCMYK16) RGBA() (uint32, uint32, uint32, uint32) {
	w := uint32(65535 - c.K)
	r := uint32(65535-c.C) * w / 65535
	g := uint32(65535-c.M) * w / 65535
	b := uint32(65535-c.Y) * w / 65535
	return r, g, b, 0xffff
}

// cmyk16Model 将任意Go颜色转换为16位CMYK颜色
// 入参: c 源Go颜色
// 返回: color.Color 转换后的ColorCMYK16颜色
func cmyk16Model(c color.Color) color.Color {
	if value, ok := c.(ColorCMYK16); ok {
		return value
	}
	if value, ok := c.(color.CMYK); ok {
		return ColorCMYK16{C: uint16(value.C) * 257, M: uint16(value.M) * 257, Y: uint16(value.Y) * 257, K: uint16(value.K) * 257}
	}
	r, g, b, _ := c.RGBA()
	w := max(r, g, b)
	if w == 0 {
		return ColorCMYK16{K: 0xffff}
	}
	return ColorCMYK16{
		C: uint16((w - r) * 65535 / w),
		M: uint16((w - g) * 65535 / w),
		Y: uint16((w - b) * 65535 / w),
		K: uint16(65535 - w),
	}
}

// NewImageCMYK16 创建指定矩形范围的16位CMYK内存图像
// 入参: r 像素矩形范围
// 返回: *ImageCMYK16 初始化完成的16位CMYK图像
func NewImageCMYK16(r image.Rectangle) *ImageCMYK16 {
	w, h := r.Dx(), r.Dy()
	stride := 8 * w
	return &ImageCMYK16{Pix: make([]uint8, stride*h), Stride: stride, Rect: r}
}

// ColorModel 返回16位CMYK图像的颜色模型
// 返回: color.Model 16位CMYK颜色模型
func (p *ImageCMYK16) ColorModel() color.Model {
	return ColorCMYK16Model
}

// Bounds 返回16位CMYK图像的像素边界矩形
// 返回: image.Rectangle 图像边界矩形
func (p *ImageCMYK16) Bounds() image.Rectangle {
	return p.Rect
}

// At 返回指定坐标处的16位CMYK颜色
// 入参: x 横坐标, y 纵坐标
// 返回: color.Color 像素颜色
func (p *ImageCMYK16) At(x, y int) color.Color {
	return p.CMYK16At(x, y)
}

// CMYK16At 读取指定坐标处的强类型16位CMYK颜色，越界时返回零值
// 入参: x 横坐标, y 纵坐标
// 返回: ColorCMYK16 像素16位CMYK颜色
func (p *ImageCMYK16) CMYK16At(x, y int) ColorCMYK16 {
	if !(image.Point{X: x, Y: y}.In(p.Rect)) {
		return ColorCMYK16{}
	}
	off := p.PixOffset(x, y)
	return ColorCMYK16{
		C: binary.BigEndian.Uint16(p.Pix[off:]),
		M: binary.BigEndian.Uint16(p.Pix[off+2:]),
		Y: binary.BigEndian.Uint16(p.Pix[off+4:]),
		K: binary.BigEndian.Uint16(p.Pix[off+6:]),
	}
}

// SetCMYK16 写入指定坐标处的16位CMYK颜色，越界时忽略
// 入参: x 横坐标, y 纵坐标, c 目标16位CMYK颜色
func (p *ImageCMYK16) SetCMYK16(x, y int, c ColorCMYK16) {
	if !(image.Point{X: x, Y: y}.In(p.Rect)) {
		return
	}
	off := p.PixOffset(x, y)
	binary.BigEndian.PutUint16(p.Pix[off:], c.C)
	binary.BigEndian.PutUint16(p.Pix[off+2:], c.M)
	binary.BigEndian.PutUint16(p.Pix[off+4:], c.Y)
	binary.BigEndian.PutUint16(p.Pix[off+6:], c.K)
}

// PixOffset 计算指定坐标在Pix缓冲中的起始字节偏移
// 入参: x 横坐标, y 纵坐标
// 返回: int 字节偏移量
func (p *ImageCMYK16) PixOffset(x, y int) int {
	return (y-p.Rect.Min.Y)*p.Stride + (x-p.Rect.Min.X)*8
}

// Opaque 报告16位CMYK图像恒为完全不透明
// 返回: bool 恒为true
func (p *ImageCMYK16) Opaque() bool {
	return true
}

// NewOutlineBuilder 创建通用XPS目录书签构建器，自动协调相对OutlineTarget URI与页面LinkTargets
// 入参: language 目录默认xml:lang语言标签，为空时依次取options.Language或"und", options 可选部件基准路径配置，nil采用默认路径
// 返回: *OutlineBuilder 目录书签构建器
func NewOutlineBuilder(language string, options *OutlineBuilderOptions) *OutlineBuilder {
	b := &OutlineBuilder{
		language:     language,
		documentPart: "/Documents/1/FixedDoc.fdoc",
		sequencePart: "/FixedDocSeq.fdseq",
		usedAnchors:  make(map[string]*Page),
	}
	if options != nil {
		if b.language == "" && options.Language != "" {
			b.language = options.Language
		}
		if options.DocumentPart != "" {
			part, err := opcPartName(options.DocumentPart)
			if err != nil {
				b.err = err
				return b
			}
			b.documentPart = part
		}
		if options.SequencePart != "" {
			part, err := opcPartName(options.SequencePart)
			if err != nil {
				b.err = err
				return b
			}
			b.sequencePart = part
		}
		if options.StructurePart != "" {
			part, err := opcPartName(options.StructurePart)
			if err != nil {
				b.err = err
				return b
			}
			b.structurePart = part
		}
	}
	if b.language == "" {
		b.language = "und"
	}
	if !fixedLanguageTag(b.language) {
		b.err = fmt.Errorf("%w: invalid outline language %q", ErrInvalid, b.language)
		return b
	}
	if b.structurePart == "" {
		b.structurePart = b.documentPart[:strings.LastIndexByte(b.documentPart, '/')+1] + "Structure1.struct"
	}
	return b
}

// AddPage 添加指向目标Page及可选锚点的目录书签节点，自动为Page补齐页级锚点名与去重后的LinkTargets
// anchor为空时复用Page.Name或自动生成唯一页级锚点名；anchor非空且页内不存在同名元素时在Page.Name为空的情况下自动绑定至Page.Name
// 入参: page 目标页面指针, anchor 可选页内元素或页级锚点名称, description 书签标题文本, level 目录层级，0或1表示一级书签, options 可选语言覆盖配置，nil继承目录语言
// 返回: *OutlineBuilder 当前构建器
func (b *OutlineBuilder) AddPage(page *Page, anchor, description string, level int32, options *OutlineEntryOptions) *OutlineBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if page == nil {
		b.err = fmt.Errorf("%w: outline target page is nil", ErrInvalid)
		return b
	}
	lang, err := b.validateEntryArgs(description, level, options)
	if err != nil {
		b.err = err
		return b
	}
	resolved := anchor
	if resolved == "" {
		if page.Name != "" {
			resolved = page.Name
		} else {
			for {
				b.autoSeq++
				candidate := "OutlineTarget" + strconv.Itoa(b.autoSeq)
				if _, taken := b.usedAnchors[candidate]; taken {
					continue
				}
				if pageHasNamedElement(page.Elements, candidate, 0) {
					continue
				}
				resolved = candidate
				page.Name = candidate
				break
			}
		}
	}
	if !fixedNamePattern(resolved) {
		b.err = fmt.Errorf("%w: invalid outline anchor name %q", ErrInvalid, resolved)
		return b
	}
	if page.Name != resolved && !pageHasNamedElement(page.Elements, resolved, 0) {
		if page.Name != "" {
			b.err = fmt.Errorf("%w: outline anchor %q not found on page with existing Name %q", ErrInvalid, resolved, page.Name)
			return b
		}
		page.Name = resolved
	}
	if owner, exists := b.usedAnchors[resolved]; exists && owner != page {
		b.err = fmt.Errorf("%w: duplicate outline anchor %q across different pages", ErrInvalid, resolved)
		return b
	}
	b.usedAnchors[resolved] = page
	if !slices.Contains(page.LinkTargets, resolved) {
		page.LinkTargets = append(page.LinkTargets, resolved)
	}
	target, err := InternalNavigateURI(b.structurePart, b.documentPart, resolved)
	if err != nil {
		b.err = err
		return b
	}
	if level == 0 {
		level = 1
	}
	b.entries = append(b.entries, OutlineEntry{Level: level, Target: target, Description: description, Language: lang})
	return b
}

// AddPageNumber 添加按一基全局页号定位的目录书签节点，遵循ECMA-388 [M9.8]指向FixedDocumentSequence
// 入参: pageNumber 一基全局页号, description 书签标题文本, level 目录层级，0或1表示一级书签, options 可选语言覆盖配置，nil继承目录语言
// 返回: *OutlineBuilder 当前构建器
func (b *OutlineBuilder) AddPageNumber(pageNumber int, description string, level int32, options *OutlineEntryOptions) *OutlineBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if pageNumber < 1 {
		b.err = fmt.Errorf("%w: outline page number must be positive: %d", ErrInvalid, pageNumber)
		return b
	}
	lang, err := b.validateEntryArgs(description, level, options)
	if err != nil {
		b.err = err
		return b
	}
	target, err := InternalNavigateURI(b.structurePart, b.sequencePart, strconv.Itoa(pageNumber))
	if err != nil {
		b.err = err
		return b
	}
	if level == 0 {
		level = 1
	}
	b.entries = append(b.entries, OutlineEntry{Level: level, Target: target, Description: description, Language: lang})
	return b
}

// SetStories 附加有序故事定义以便与目录书签一同产出完整DocumentStructure
// 入参: stories 故事列表，空切片清空已有故事
// 返回: *OutlineBuilder 当前构建器
func (b *OutlineBuilder) SetStories(stories []Story) *OutlineBuilder {
	if b == nil || b.err != nil {
		return b
	}
	b.stories = make([]Story, len(stories))
	for i, story := range stories {
		copied := Story{Name: story.Name, Fragments: make([]StoryFragmentReference, len(story.Fragments))}
		for j, ref := range story.Fragments {
			if ref.FragmentName != nil {
				name := *ref.FragmentName
				ref.FragmentName = &name
			}
			copied.Fragments[j] = ref
		}
		b.stories[i] = copied
	}
	return b
}

// Build 校验累计状态并返回可直接传入Package.SetDocumentStructure或StreamWriter.SetDocumentStructure的独立DocumentStructure
// 返回: *DocumentStructure 合规文档结构模型, error 构建过程中记录的参数、语言、锚点或空目录错误
func (b *OutlineBuilder) Build() (*DocumentStructure, error) {
	if b == nil {
		return nil, fmt.Errorf("%w: nil outline builder", ErrInvalid)
	}
	if b.err != nil {
		return nil, b.err
	}
	if len(b.entries) == 0 {
		return nil, fmt.Errorf("%w: outline requires at least one entry", ErrInvalid)
	}
	entries := make([]OutlineEntry, len(b.entries))
	for i, entry := range b.entries {
		if entry.Language != nil {
			lang := *entry.Language
			entry.Language = &lang
		}
		entries[i] = entry
	}
	var stories []Story
	if len(b.stories) != 0 {
		stories = make([]Story, len(b.stories))
		for i, story := range b.stories {
			copied := Story{Name: story.Name, Fragments: make([]StoryFragmentReference, len(story.Fragments))}
			for j, ref := range story.Fragments {
				if ref.FragmentName != nil {
					name := *ref.FragmentName
					ref.FragmentName = &name
				}
				copied.Fragments[j] = ref
			}
			stories[i] = copied
		}
	}
	return &DocumentStructure{
		Part:    b.structurePart,
		Outline: &DocumentOutline{Language: b.language, Entries: entries},
		Stories: stories,
	}, nil
}

// validateEntryArgs 校验目录书签条目的描述文本、层级及可选语言标签
// 入参: description 书签标题, level 目录层级, options 可选语言覆盖选项
// 返回: *string 可选语言指针，继承默认语言时为nil, error 参数或语言标签错误
func (b *OutlineBuilder) validateEntryArgs(description string, level int32, options *OutlineEntryOptions) (*string, error) {
	if description == "" || !xmlTextValid(description) {
		return nil, fmt.Errorf("%w: invalid outline description", ErrInvalid)
	}
	if level < 0 {
		return nil, fmt.Errorf("%w: invalid outline level %d", ErrInvalid, level)
	}
	if options == nil || options.Language == "" {
		return nil, nil
	}
	if !fixedLanguageTag(options.Language) {
		return nil, fmt.Errorf("%w: invalid outline entry language %q", ErrInvalid, options.Language)
	}
	lang := options.Language
	return &lang, nil
}

// pageHasNamedElement 递归检查页面直接视觉元素树中是否存在指定Name，不进入VisualBrush与资源字典
// 入参: elements 待检索绘制元素列表, target 目标Name, depth 当前嵌套深度
// 返回: bool 是否存在同名元素
func pageHasNamedElement(elements []Element, target string, depth int) bool {
	if depth >= 256 {
		return false
	}
	for _, elem := range elements {
		props := contentProperties(elem)
		if props != nil && props.Name == target {
			return true
		}
		if canvas, ok := elem.(*Canvas); ok && len(canvas.Elements) != 0 {
			if pageHasNamedElement(canvas.Elements, target, depth+1) {
				return true
			}
		}
	}
	return false
}

// EncodeCaretStops 将逻辑光标停靠标志切片编码为符合ECMA-388规范的十六进制CaretStops属性字符串
// 每四位大端打包为一个大写十六进制字符，不足四位时末位低比特补零，与ParseCaretStops严格互逆
// 入参: stops 逻辑光标停靠标志切片，长度须为对应UTF-16码元数加一且至少为1
// 返回: string 规范化十六进制CaretStops字符串, error 空切片等参数错误
func EncodeCaretStops(stops []bool) (string, error) {
	if len(stops) == 0 {
		return "", fmt.Errorf("%w: CaretStops requires at least one position", ErrInvalid)
	}
	const hexDigits = "0123456789ABCDEF"
	digits := len(stops) / 4
	if len(stops)%4 != 0 {
		digits++
	}
	out := make([]byte, digits)
	for i := range digits {
		var nibble byte
		base := i * 4
		for bit := range 4 {
			idx := base + bit
			if idx < len(stops) && stops[idx] {
				nibble |= 8 >> uint(bit)
			}
		}
		out[i] = hexDigits[nibble]
	}
	return string(out), nil
}

// ParseFontResource 从原始单面SFNT或TTC/OTC字体字节解析只读FontResource，供写侧GlyphsBuilder等直接复用
// 入参: ctx 取消Context，nil采用Background, data 原始字体字节, collectionIndex 零基字体面索引
// 返回: *FontResource 已解析字体资源, error 字体封装、度量或取消错误
func ParseFontResource(ctx context.Context, data []byte, collectionIndex uint32) (*FontResource, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if len(data) == 0 {
		return nil, fmt.Errorf("%w: empty font data", ErrInvalid)
	}
	cloned := bytes.Clone(data)
	face, err := parseFontFace(cloned, collectionIndex)
	if err != nil {
		return nil, err
	}
	source, err := newFontSource(face)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	names := parseFontResourceNames(face)
	style := fontResourceStyle(face, source.metrics)
	fsType, permission, _ := fontResourceEmbedding(source.metrics.os2)
	return buildFontResource("", collectionIndex, face.collection || collectionIndex != 0, false, face, source, cloned, names, style, fsType, permission), nil
}

// NewGlyphsBuilder 创建基于指定字体URI、可选字体资源与字号的Glyphs构建器
// 入参: fontURI 字体部件URI，可携带#index集合索引, font 已解析字体资源，纯GID构建时可为nil, emSize 字号，以1/96英寸计
// 返回: *GlyphsBuilder 字形构建器
func NewGlyphsBuilder(fontURI string, font *FontResource, emSize float64) *GlyphsBuilder {
	return &GlyphsBuilder{fontURI: fontURI, font: font, emSize: emSize}
}

// BuildText 利用字体资源自动查cmap与水平或竖排度量，生成严格合标的Glyphs元素
// 自动处理UTF-16代理对簇、1/100 em步进换算、粗体模拟步进补偿、竖排与双向级别校验
// 入参: ctx 取消Context，nil采用Background, text 原始Unicode文本, origin 文本基线起点坐标, options 构建选项，nil采用默认值
// 返回: *Glyphs 严格合标的字形元素, error 字体、参数、文本或取消错误
func (b *GlyphsBuilder) BuildText(ctx context.Context, text string, origin Point, options *GlyphsBuildOptions) (*Glyphs, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if b == nil || b.font == nil {
		return nil, fmt.Errorf("%w: glyphs builder requires font resource for BuildText", ErrInvalid)
	}
	if text == "" || !utf8.ValidString(text) {
		return nil, fmt.Errorf("%w: BuildText requires non-empty valid UTF-8 text", ErrInvalid)
	}
	glyphs, opts, err := b.initGlyphs(origin, options)
	if err != nil {
		return nil, err
	}
	glyphs.Text = text
	if glyphs.CaretStops != "" {
		if _, err := ParseCaretStops(glyphs.CaretStops, EscapeUnicodeString(glyphs.Text)); err != nil {
			return nil, err
		}
	}
	boldExtra := 0.0
	if opts.StyleSimulations == StyleSimulationBold || opts.StyleSimulations == StyleSimulationBoldItalic {
		boldExtra = 2
	}
	omitDefaultAdv := opts.OmitDefaultAdvanceWidth && opts.Tracking == 0
	clusters := make([]GlyphCluster, 0, len(text))
	for _, r := range text {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		gid, ok := b.font.RuneGlyph(r)
		if !ok && opts.RejectMissingGlyphs {
			return nil, fmt.Errorf("%w: missing glyph for rune %U", ErrInvalid, r)
		}
		var advanceEm float64
		if opts.IsSideways {
			advanceEm, err = b.font.GlyphVerticalAdvance(gid)
		} else {
			advanceEm, err = b.font.GlyphAdvance(gid)
		}
		if err != nil {
			return nil, err
		}
		adv100 := advanceEm*100 + boldExtra + opts.Tracking
		if !geometryFinite(adv100) || adv100 < 0 {
			return nil, fmt.Errorf("%w: invalid computed glyph advance", ErrInvalid)
		}
		entry := GlyphIndex{Index: gid, HasIndex: true}
		if !omitDefaultAdv {
			entry.AdvanceWidth = adv100
			entry.HasAdvanceWidth = true
		}
		codeUnits := 1
		hasMapping := false
		if r > 0xffff {
			codeUnits = 2
			hasMapping = true
		}
		clusters = append(clusters, GlyphCluster{CodeUnitCount: codeUnits, HasMapping: hasMapping, Glyphs: []GlyphIndex{entry}})
	}
	glyphs.Indices = clusters
	return glyphs, nil
}

// BuildClusters 根据显式文本片段与字形列表构建严格合标的复合簇Glyphs元素，支持无cmap字体纯GID输出
// 自动计算UTF-16码元数并按标准生成簇映射前缀，保留显式步进、UOffset与VOffset
// 入参: ctx 取消Context，nil采用Background, clusters 显式字形簇列表, origin 文本基线起点坐标, options 构建选项，nil采用默认值
// 返回: *Glyphs 严格合标的字形元素, error 参数、簇结构、字形范围或取消错误
func (b *GlyphsBuilder) BuildClusters(ctx context.Context, clusters []GlyphBuildCluster, origin Point, options *GlyphsBuildOptions) (*Glyphs, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if b == nil || len(clusters) == 0 {
		return nil, fmt.Errorf("%w: glyphs builder requires non-empty clusters", ErrInvalid)
	}
	glyphs, opts, err := b.initGlyphs(origin, options)
	if err != nil {
		return nil, err
	}
	var textBuilder strings.Builder
	hasAnyText := false
	for _, cluster := range clusters {
		if !utf8.ValidString(cluster.Text) {
			return nil, fmt.Errorf("%w: invalid UTF-8 in cluster text", ErrInvalid)
		}
		if cluster.Text != "" {
			hasAnyText = true
			textBuilder.WriteString(cluster.Text)
		}
	}
	glyphs.Text = textBuilder.String()
	if glyphs.CaretStops != "" {
		if _, err := ParseCaretStops(glyphs.CaretStops, EscapeUnicodeString(glyphs.Text)); err != nil {
			return nil, err
		}
	}
	boldExtra := 0.0
	if opts.StyleSimulations == StyleSimulationBold || opts.StyleSimulations == StyleSimulationBoldItalic {
		boldExtra = 2
	}
	omitDefaultAdv := opts.OmitDefaultAdvanceWidth && opts.Tracking == 0 && b.font != nil
	indices := make([]GlyphCluster, 0, len(clusters))
	for _, cluster := range clusters {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if len(cluster.Glyphs) == 0 {
			return nil, fmt.Errorf("%w: empty glyph list in cluster", ErrInvalid)
		}
		if hasAnyText && cluster.Text == "" {
			return nil, fmt.Errorf("%w: mixed empty and non-empty cluster text", ErrInvalid)
		}
		codeUnits := 1
		scalarCount := 0
		var singleRune rune
		if hasAnyText {
			codeUnits = 0
			for _, r := range cluster.Text {
				if scalarCount == 0 {
					singleRune = r
				}
				scalarCount++
				codeUnits++
				if r > 0xffff {
					codeUnits++
				}
			}
		}
		entries := make([]GlyphIndex, 0, len(cluster.Glyphs))
		for _, item := range cluster.Glyphs {
			hasIndex := !item.OmitGlyphID
			var resolvedGID uint16
			hasResolvedGID := false
			if !hasIndex {
				if !hasAnyText || len(cluster.Glyphs) != 1 || scalarCount != 1 {
					return nil, fmt.Errorf("%w: omitted glyph ID requires single Unicode scalar cluster", ErrInvalid)
				}
				if b.font != nil {
					gid, ok := b.font.RuneGlyph(singleRune)
					if !ok && opts.RejectMissingGlyphs {
						return nil, fmt.Errorf("%w: missing glyph for rune %U", ErrInvalid, singleRune)
					}
					resolvedGID, hasResolvedGID = gid, true
				}
			} else {
				if opts.RejectMissingGlyphs && item.GlyphID == 0 {
					return nil, fmt.Errorf("%w: missing glyph index 0 rejected", ErrInvalid)
				}
				if b.font != nil && int(item.GlyphID) >= b.font.GlyphCount {
					return nil, fmt.Errorf("%w: glyph index %d exceeds font glyph count", ErrInvalid, item.GlyphID)
				}
				resolvedGID, hasResolvedGID = item.GlyphID, b.font != nil
			}
			hasAdv := item.HasAdvanceWidth || item.AdvanceWidth != 0
			advVal := item.AdvanceWidth
			if hasAdv && (!geometryFinite(advVal) || advVal < 0) {
				return nil, fmt.Errorf("%w: invalid cluster glyph advance", ErrInvalid)
			}
			if hasAdv && omitDefaultAdv && hasResolvedGID {
				var defaultAdvEm float64
				if opts.IsSideways {
					defaultAdvEm, err = b.font.GlyphVerticalAdvance(resolvedGID)
				} else {
					defaultAdvEm, err = b.font.GlyphAdvance(resolvedGID)
				}
				if err == nil && math.Abs(advVal-(defaultAdvEm*100+boldExtra)) <= 1e-9 {
					hasAdv = false
					advVal = 0
				}
			}
			hasU := item.HasUOffset || item.UOffset != 0
			if hasU && !geometryFinite(item.UOffset) {
				return nil, fmt.Errorf("%w: invalid cluster glyph UOffset", ErrInvalid)
			}
			hasV := item.HasVOffset || item.VOffset != 0
			if hasV && !geometryFinite(item.VOffset) {
				return nil, fmt.Errorf("%w: invalid cluster glyph VOffset", ErrInvalid)
			}
			entries = append(entries, GlyphIndex{
				Index:           item.GlyphID,
				HasIndex:        hasIndex,
				AdvanceWidth:    advVal,
				HasAdvanceWidth: hasAdv,
				UOffset:         item.UOffset,
				HasUOffset:      hasU,
				VOffset:         item.VOffset,
				HasVOffset:      hasV,
			})
		}
		if !hasAnyText {
			for _, entry := range entries {
				indices = append(indices, GlyphCluster{CodeUnitCount: 1, Glyphs: []GlyphIndex{entry}})
			}
			continue
		}
		hasGlyphCount := len(entries) > 1
		hasMapping := hasGlyphCount || codeUnits > 1
		indices = append(indices, GlyphCluster{
			CodeUnitCount: codeUnits,
			HasMapping:    hasMapping,
			HasGlyphCount: hasGlyphCount,
			Glyphs:        entries,
		})
	}
	glyphs.Indices = indices
	return glyphs, nil
}

// initGlyphs 校验构建器与通用字形选项并初始化目标Glyphs结构体
// 入参: origin 基线起点坐标, options 可选构建选项
// 返回: *Glyphs 已初始化的字形元素, GlyphsBuildOptions 规范化后的选项, error 校验错误
func (b *GlyphsBuilder) initGlyphs(origin Point, options *GlyphsBuildOptions) (*Glyphs, GlyphsBuildOptions, error) {
	if b.fontURI == "" || !geometryFinite(b.emSize, origin.X, origin.Y) || b.emSize < 0 {
		return nil, GlyphsBuildOptions{}, fmt.Errorf("%w: invalid glyphs builder parameters", ErrInvalid)
	}
	if _, _, _, err := ParseFontURI(b.fontURI); err != nil {
		return nil, GlyphsBuildOptions{}, err
	}
	opts := GlyphsBuildOptions{StyleSimulations: StyleSimulationNone}
	if options != nil {
		opts = *options
		if opts.StyleSimulations == "" {
			opts.StyleSimulations = StyleSimulationNone
		}
	}
	if opts.BidiLevel < 0 || opts.BidiLevel > 61 || opts.IsSideways && opts.BidiLevel&1 != 0 || !geometryFinite(opts.Tracking) {
		return nil, GlyphsBuildOptions{}, fmt.Errorf("%w: invalid glyphs bidi, sideways or tracking option", ErrInvalid)
	}
	switch opts.StyleSimulations {
	case StyleSimulationNone, StyleSimulationBold, StyleSimulationItalic, StyleSimulationBoldItalic:
	default:
		return nil, GlyphsBuildOptions{}, fmt.Errorf("%w: invalid glyphs style simulation", ErrInvalid)
	}
	opacity := 1.0
	if opts.Opacity != nil {
		opacity = *opts.Opacity
		if !geometryFinite(opacity) || opacity < 0 || opacity > 1 {
			return nil, GlyphsBuildOptions{}, fmt.Errorf("%w: invalid glyphs opacity", ErrInvalid)
		}
	}
	if opts.CaretStops != "" {
		for i := 0; i < len(opts.CaretStops); i++ {
			if opcHex(opts.CaretStops[i]) < 0 {
				return nil, GlyphsBuildOptions{}, fmt.Errorf("%w: invalid glyphs CaretStops hex", ErrInvalid)
			}
		}
	}
	glyphs := NewGlyphs(b.fontURI, b.emSize, "")
	glyphs.Origin = origin
	glyphs.BidiLevel = opts.BidiLevel
	glyphs.IsSideways = opts.IsSideways
	glyphs.StyleSimulations = opts.StyleSimulations
	glyphs.Fill = opts.Fill
	glyphs.CaretStops = opts.CaretStops
	glyphs.DeviceFontName = opts.DeviceFontName
	glyphs.Name = opts.Name
	if opts.Language != nil {
		v := *opts.Language
		glyphs.Language = &v
	}
	if opts.NavigateURI != nil {
		v := *opts.NavigateURI
		glyphs.NavigateURI = &v
	}
	glyphs.Opacity = opacity
	if opts.RenderTransform != nil {
		v := *opts.RenderTransform
		glyphs.RenderTransform = &v
	}
	glyphs.RenderTransformResource = opts.RenderTransformResource
	glyphs.Clip = opts.Clip
	glyphs.OpacityMask = opts.OpacityMask
	return glyphs, opts, nil
}

// SRGBColor8 构造精确8位非预乘sRGB颜色模型
// 入参: r 红色分量, g 绿色分量, b 蓝色分量, a 不透明度分量
// 返回: Color sRGB颜色模型
func SRGBColor8(r, g, b, a uint8) Color {
	return Color{Space: ColorSRGB, Alpha: float64(a) / 255, Components: []float64{float64(r) / 255, float64(g) / 255, float64(b) / 255}}
}

// SRGBColorFloat 将浮点RGBA分量裁剪并精确量化为满足8位无损编码要求的sRGB颜色模型
// 入参: r 红色归一化分量, g 绿色归一化分量, b 蓝色归一化分量, a 不透明度归一化分量
// 返回: Color 量化后的sRGB颜色模型
func SRGBColorFloat(r, g, b, a float64) Color {
	return Color{Space: ColorSRGB, Alpha: quantizeUnitSRGB8(a), Components: []float64{quantizeUnitSRGB8(r), quantizeUnitSRGB8(g), quantizeUnitSRGB8(b)}}
}

// quantizeUnitSRGB8 将浮点分量限制在零至一区间并量化为8位精确表示值
// 入参: value 原始浮点分量
// 返回: float64 精确8位分量值
func quantizeUnitSRGB8(value float64) float64 {
	if math.IsNaN(value) || value <= 0 {
		return 0
	}
	if value >= 1 {
		return 1
	}
	return quantizeSRGB8(value)
}

// ScRGBColor 构造线性宽色域scRGB颜色模型
// 入参: a 不透明度分量, r 红色线性分量, g 绿色线性分量, b 蓝色线性分量
// 返回: Color scRGB颜色模型
func ScRGBColor(a, r, g, b float64) Color {
	return Color{Space: ColorScRGB, Alpha: a, Components: []float64{r, g, b}}
}

// ContextColor 构造基于ICC配置文件的上下文颜色模型，保留独立分量切片副本
// 入参: profileURI ICC配置文件部件URI, alpha 不透明度分量, components 配置文件色彩空间通道分量
// 返回: Color 上下文颜色模型
func ContextColor(profileURI string, alpha float64, components ...float64) Color {
	return Color{Space: ColorContext, ProfileURI: profileURI, Alpha: alpha, Components: slices.Clone(components)}
}

// LinearGradientBrush 创建不透明线性渐变画刷，使用绝对坐标系、sRGB插值与Pad延展默认值
// 入参: start 渐变起点, end 渐变终点, stops 渐变停靠点切片
// 返回: *Brush 线性渐变画刷模型
func LinearGradientBrush(start, end Point, stops []GradientStop) *Brush {
	cloned := make([]GradientStop, len(stops))
	for i, stop := range stops {
		stop.Color.Components = slices.Clone(stop.Color.Components)
		cloned[i] = stop
	}
	return &Brush{Kind: BrushLinearGradient, Opacity: 1, StartPoint: start, EndPoint: end, Stops: cloned}
}

// RadialGradientBrush 创建不透明径向渐变画刷，使用绝对坐标系、sRGB插值与Pad延展默认值
// 入参: center 渐变椭圆中心, origin 渐变焦点, rx 水平半径, ry 垂直半径, stops 渐变停靠点切片
// 返回: *Brush 径向渐变画刷模型
func RadialGradientBrush(center, origin Point, rx, ry float64, stops []GradientStop) *Brush {
	cloned := make([]GradientStop, len(stops))
	for i, stop := range stops {
		stop.Color.Components = slices.Clone(stop.Color.Components)
		cloned[i] = stop
	}
	return &Brush{Kind: BrushRadialGradient, Opacity: 1, Center: center, GradientOrigin: origin, RadiusX: rx, RadiusY: ry, Stops: cloned}
}

// VisualBrush 创建不透明非平铺视觉画刷
// 入参: viewbox 视觉源内容区域, viewport 目标绘制视口区域, visual 视觉绘制元素
// 返回: *Brush 视觉画刷模型
func VisualBrush(viewbox, viewport Rect, visual Element) *Brush {
	return &Brush{Kind: BrushVisual, Opacity: 1, Viewbox: viewbox, Viewport: viewport, TileMode: TileNone, Visual: visual}
}

// ColorConvertedImageBrush 创建带ICC色彩配置转换的不透明非平铺图像画刷
// 入参: imageSource 图像部件URI, profileURI ICC配置文件部件URI, viewbox 源图像区域, viewport 目标绘制视口区域
// 返回: *Brush 色彩转换图像画刷模型
func ColorConvertedImageBrush(imageSource, profileURI string, viewbox, viewport Rect) *Brush {
	return &Brush{Kind: BrushImage, Opacity: 1, ImageSource: imageSource, ImageProfileURI: profileURI, Viewbox: viewbox, Viewport: viewport, TileMode: TileNone}
}

// StaticBrush 创建指向指定资源字典键的静态资源画刷引用
// 入参: key 资源字典键名
// 返回: *Brush 静态资源画刷引用模型
func StaticBrush(key string) *Brush {
	return &Brush{ResourceKey: key, Opacity: 1}
}

// StaticGeometry 创建指向指定资源字典键的静态资源几何引用
// 入参: key 资源字典键名
// 返回: *Geometry 静态资源几何引用模型
func StaticGeometry(key string) *Geometry {
	return &Geometry{ResourceKey: key}
}

// NewGeometryBuilder 创建指定填充规则的路径几何链式构建器，默认启用填充与描边标志
// 入参: fillRule 几何填充规则
// 返回: *GeometryBuilder 路径几何构建器
func NewGeometryBuilder(fillRule GeometryFillRule) *GeometryBuilder {
	return &GeometryBuilder{fillRule: fillRule, current: -1, stroked: true}
}

// MoveTo 开始新的子路径并将当前点移动至指定坐标，新子路径默认填充且未闭合
// 入参: p 子路径起点坐标
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) MoveTo(p Point) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !geometryFinite(p.X, p.Y) {
		b.err = fmt.Errorf("%w: non-finite geometry MoveTo point", ErrInvalid)
		return b
	}
	b.figures = append(b.figures, GeometryFigure{StartPoint: p, IsFilled: true})
	b.current = len(b.figures) - 1
	b.hasCurrent = true
	return b
}

// LineTo 从当前点添加直线段至指定终点
// 入参: p 直线终点坐标
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) LineTo(p Point) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent || !geometryFinite(p.X, p.Y) {
		b.err = fmt.Errorf("%w: invalid geometry LineTo state or point", ErrInvalid)
		return b
	}
	b.figures[b.current].Segments = append(b.figures[b.current].Segments, GeometrySegment{Kind: GeometryLine, Point: p, IsStroked: b.stroked})
	return b
}

// CubicTo 从当前点添加三次贝塞尔曲线段至指定终点
// 入参: c1 第一控制点, c2 第二控制点, p 曲线终点
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) CubicTo(c1, c2, p Point) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent || !geometryFinite(c1.X, c1.Y, c2.X, c2.Y, p.X, p.Y) {
		b.err = fmt.Errorf("%w: invalid geometry CubicTo state or points", ErrInvalid)
		return b
	}
	b.figures[b.current].Segments = append(b.figures[b.current].Segments, GeometrySegment{Kind: GeometryCubic, Control1: c1, Control2: c2, Point: p, IsStroked: b.stroked})
	return b
}

// QuadTo 从当前点添加二次贝塞尔曲线段至指定终点
// 入参: c1 控制点, p 曲线终点
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) QuadTo(c1, p Point) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent || !geometryFinite(c1.X, c1.Y, p.X, p.Y) {
		b.err = fmt.Errorf("%w: invalid geometry QuadTo state or points", ErrInvalid)
		return b
	}
	b.figures[b.current].Segments = append(b.figures[b.current].Segments, GeometrySegment{Kind: GeometryQuadratic, Control1: c1, Point: p, IsStroked: b.stroked})
	return b
}

// ArcTo 从当前点添加椭圆弧段至指定终点，旋转角度以度计
// 入参: rx 椭圆水平半径, ry 椭圆垂直半径, rotation 椭圆旋转角度, largeArc 是否取大弧, sweepClockwise 是否顺时针扫掠, p 圆弧终点
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) ArcTo(rx, ry, rotation float64, largeArc, sweepClockwise bool, p Point) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent || !geometryFinite(rx, ry, rotation, p.X, p.Y) || rx < 0 || ry < 0 {
		b.err = fmt.Errorf("%w: invalid geometry ArcTo parameters", ErrInvalid)
		return b
	}
	b.figures[b.current].Segments = append(b.figures[b.current].Segments, GeometrySegment{Kind: GeometryArc, RadiusX: rx, RadiusY: ry, RotationAngle: rotation, IsLargeArc: largeArc, SweepClockwise: sweepClockwise, Point: p, IsStroked: b.stroked})
	return b
}

// Close 将当前子路径标记为闭合
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) Close() *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent {
		b.err = fmt.Errorf("%w: cannot Close before MoveTo", ErrInvalid)
		return b
	}
	b.figures[b.current].IsClosed = true
	return b
}

// SetFilled 设置当前子路径是否参与填充计算
// 入参: filled 是否填充
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) SetFilled(filled bool) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !b.hasCurrent {
		b.err = fmt.Errorf("%w: cannot SetFilled before MoveTo", ErrInvalid)
		return b
	}
	b.figures[b.current].IsFilled = filled
	return b
}

// SetStroked 设置后续新增路径段是否参与描边绘制
// 入参: stroked 是否描边
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) SetStroked(stroked bool) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	b.stroked = stroked
	return b
}

// SetTransform 为目标几何设置局部仿射变换矩阵
// 入参: m 仿射变换矩阵
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) SetTransform(m Matrix) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !geometryFillMatrixFinite(m) {
		b.err = fmt.Errorf("%w: non-finite geometry transform matrix", ErrInvalid)
		return b
	}
	copied := m
	b.transform = &copied
	b.transformResource = ""
	return b
}

// SetTransformResource 为目标几何设置变换矩阵静态资源键引用
// 入参: key 资源字典中的MatrixTransform键名
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) SetTransformResource(key string) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !fixedNamePattern(key) {
		b.err = fmt.Errorf("%w: invalid geometry transform resource key", ErrInvalid)
		return b
	}
	b.transform = nil
	b.transformResource = key
	return b
}

// Rect 追加一个闭合矩形子路径
// 入参: r 轴对齐矩形区域
// 返回: *GeometryBuilder 当前构建器
func (b *GeometryBuilder) Rect(r Rect) *GeometryBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if !geometryFinite(r.X, r.Y, r.Width, r.Height) {
		b.err = fmt.Errorf("%w: non-finite geometry Rect", ErrInvalid)
		return b
	}
	return b.MoveTo(Point{X: r.X, Y: r.Y}).LineTo(Point{X: r.X + r.Width, Y: r.Y}).LineTo(Point{X: r.X + r.Width, Y: r.Y + r.Height}).LineTo(Point{X: r.X, Y: r.Y + r.Height}).Close()
}

// Build 校验累计状态并返回独立的Geometry路径几何模型
// 返回: *Geometry 路径几何模型, error 构建过程中记录的参数或填充规则错误
func (b *GeometryBuilder) Build() (*Geometry, error) {
	if b == nil {
		return nil, fmt.Errorf("%w: nil geometry builder", ErrInvalid)
	}
	if b.err != nil {
		return nil, b.err
	}
	if b.fillRule > GeometryNonZero {
		return nil, fmt.Errorf("%w: invalid geometry fill rule", ErrInvalid)
	}
	figures := make([]GeometryFigure, len(b.figures))
	for i, fig := range b.figures {
		fig.Segments = slices.Clone(fig.Segments)
		figures[i] = fig
	}
	var transform *Matrix
	if b.transform != nil {
		copied := *b.transform
		transform = &copied
	}
	return &Geometry{FillRule: b.fillRule, Figures: figures, Transform: transform, TransformResource: b.transformResource}, nil
}

// EncodeResourceDictionary 将独立远程资源字典编码为UTF-8 XML，执行键名、类型、顺序与静态引用校验
// 入参: ctx 取消Context，nil采用Background, output 输出流, dict 资源字典模型，Source必须为空, options 编码选项，nil采用默认值
// 返回: int64 已写字节数, error 模型、校验、取消或写出错误
func EncodeResourceDictionary(ctx context.Context, output io.Writer, dict *ResourceDictionary, options *EncodeOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if output == nil || dict == nil {
		return 0, fmt.Errorf("%w: missing resource dictionary or output", ErrInvalid)
	}
	root, limits, err := encodeResourceDictionaryRoot(ctx, dict, options)
	if err != nil {
		return 0, err
	}
	return writeEncodedXMLNode(ctx, output, root, limits.MaxPartBytes)
}

// InternalNavigateURI 构造符合ECMA-388与XPS 1.0导航约束的相对内部导航URI
// 按[M9.4]与[M9.8]依据标准扩展名(.fpage与.fdoc)启发式拦截指向FixedPage的命名或页码片段以及指向FixedDocument的页码片段
// 若目标部件采用非标准自定义扩展名，本函数仅执行词法与相对路径校验，完整部件角色合规性在包写出或读取校验阶段确认
// 入参: sourcePart 来源部件URI, targetPart 目标部件URI, targetName 可选目标链接名称或页码片段
// 返回: string 规范化相对导航URI, error 部件名、锚点或导航规则错误
func InternalNavigateURI(sourcePart, targetPart, targetName string) (string, error) {
	source, err := opcPartName(sourcePart)
	if err != nil {
		return "", err
	}
	target, err := opcPartName(targetPart)
	if err != nil {
		return "", err
	}
	rel, err := relativePart(source, target)
	if err != nil {
		return "", err
	}
	if targetName == "" {
		return rel, nil
	}
	if !xmlTextValid(targetName) || strings.ContainsAny(targetName, "# \t\r\n") {
		return "", fmt.Errorf("%w: invalid navigation target name %q", ErrInvalid, targetName)
	}
	lowerTarget := strings.ToLower(target)
	if linkPageNumber(targetName) {
		if strings.HasSuffix(lowerTarget, ".fpage") || strings.HasSuffix(lowerTarget, ".fdoc") {
			return "", fmt.Errorf("%w: M9.8 page address must target FixedDocumentSequence", ErrInvalid)
		}
	} else {
		if strings.HasSuffix(lowerTarget, ".fpage") {
			return "", fmt.Errorf("%w: M9.4 named address must target FixedDocument or FixedDocumentSequence", ErrInvalid)
		}
		if !fixedNamePattern(targetName) {
			return "", fmt.Errorf("%w: invalid named navigation target %q", ErrInvalid, targetName)
		}
	}
	u := url.URL{Fragment: targetName}
	return rel + u.String(), nil
}

// encodeGoImageWithLimits 将标准Go图像按指定格式、压缩方式、质量、分辨率、ICC配置与像素上限编码为XPS支持的图像字节
// 入参: ctx 取消Context, img 源Go图像, options 编码选项，nil采用默认值, maxBytes 输出字节上限, maxPixels 像素总数上限，0采用默认上限
// 返回: []byte 编码后图像字节, string 媒体类型, string 扩展名, error 编码、配置、预算或取消错误
func encodeGoImageWithLimits(ctx context.Context, img image.Image, options *ImageEncodeOptions, maxBytes int64, maxPixels uint64) ([]byte, string, string, error) {
	if err := checkContext(ctx); err != nil {
		return nil, "", "", err
	}
	if img == nil {
		return nil, "", "", fmt.Errorf("%w: nil image", ErrInvalid)
	}
	bounds := img.Bounds()
	if bounds.Empty() {
		return nil, "", "", fmt.Errorf("%w: empty image bounds", ErrInvalid)
	}
	if maxPixels == 0 {
		maxPixels = DefaultImageOptions().MaxPixels
	}
	w, h := bounds.Dx(), bounds.Dy()
	if w > rasterMaxDimension || h > rasterMaxDimension || uint64(w) > maxPixels/uint64(h) {
		return nil, "", "", fmt.Errorf("%w: image exceeds MaxImagePixels", ErrLimit)
	}
	cfg := ImageEncodeOptions{Format: ImageFormatAuto}
	if options != nil {
		cfg = *options
	}
	if cfg.Format > ImageFormatJXR || cfg.TIFFCompression > TIFFCompressionCCITTGroup4 || cfg.Quality < 0 || cfg.Quality > 100 {
		return nil, "", "", fmt.Errorf("%w: invalid image encode format, TIFF compression or quality", ErrInvalid)
	}
	if cfg.DPIX < 0 || cfg.DPIY < 0 || math.IsNaN(cfg.DPIX) || math.IsInf(cfg.DPIX, 0) || math.IsNaN(cfg.DPIY) || math.IsInf(cfg.DPIY, 0) {
		return nil, "", "", fmt.Errorf("%w: invalid image DPI", ErrInvalid)
	}
	if cfg.DPIX > 0 && cfg.DPIY == 0 {
		cfg.DPIY = cfg.DPIX
	} else if cfg.DPIY > 0 && cfg.DPIX == 0 {
		cfg.DPIX = cfg.DPIY
	}
	format := cfg.Format
	if format == ImageFormatAuto {
		format = chooseAutoImageFormat(img, cfg.Quality)
	}
	if len(cfg.ICCProfile) != 0 {
		parsed, err := validateCreatedICCProfile(cfg.ICCProfile, ctx)
		if err != nil {
			return nil, "", "", err
		}
		if parsed.class == "link" || parsed.class == "abst" {
			return nil, "", "", fmt.Errorf("%w: ICC profile class cannot be embedded in an image", ErrInvalid)
		}
		if targetSpace := encodedGoImageColorSpace(img, format, cfg.TIFFCompression); targetSpace == "" || parsed.space != targetSpace {
			return nil, "", "", fmt.Errorf("%w: ICC profile color space %q is incompatible with encoded %q image", ErrInvalid, parsed.space, targetSpace)
		}
	}
	switch format {
	case ImageFormatPNG:
		data, err := encodeGoImagePNG(ctx, img, cfg.DPIX, cfg.DPIY, cfg.ICCProfile, maxBytes)
		return data, "image/png", "png", err
	case ImageFormatJPEG:
		data, err := encodeGoImageJPEG(ctx, img, cfg.Quality, cfg.DPIX, cfg.DPIY, cfg.ICCProfile, maxBytes)
		return data, "image/jpeg", "jpg", err
	case ImageFormatTIFF:
		data, err := encodeGoImageTIFF(ctx, img, cfg.TIFFCompression, cfg.DPIX, cfg.DPIY, cfg.ICCProfile, maxBytes, maxPixels)
		return data, "image/tiff", "tif", err
	case ImageFormatJXR:
		data, err := encodeGoImageJXR(ctx, img, cfg, maxBytes, maxPixels)
		return data, "image/vnd.ms-photo", "jxr", err
	default:
		return nil, "", "", fmt.Errorf("%w: unsupported image encode format", ErrUnsupported)
	}
}

// encodedGoImageColorSpace 推导源Go图像按选定输出格式与压缩方式编码后的ICC色彩空间标识
// 入参: img 源Go图像, format 已确定的输出格式, tiffComp TIFF压缩方式
// 返回: string 目标编码图像对应的四字节ICC色彩空间签名
func encodedGoImageColorSpace(img image.Image, format ImageEncodeFormat, tiffComp TIFFCompression) string {
	switch format {
	case ImageFormatPNG:
		switch img.(type) {
		case *image.Gray, *image.Gray16:
			return "GRAY"
		default:
			return "RGB "
		}
	case ImageFormatJPEG:
		if _, ok := img.(*image.Gray); ok {
			return "GRAY"
		}
		return "RGB "
	case ImageFormatTIFF:
		if tiffComp == TIFFCompressionCCITTGroup4 {
			return "GRAY"
		}
		switch img.(type) {
		case *image.Gray, *image.Gray16:
			return "GRAY"
		case *image.CMYK, *ImageCMYK16:
			return "CMYK"
		default:
			return "RGB "
		}
	case ImageFormatJXR:
		switch img.(type) {
		case *image.Gray, *image.Gray16:
			return "GRAY"
		case *image.CMYK:
			return "CMYK"
		default:
			return "RGB "
		}
	default:
		return ""
	}
}

// chooseAutoImageFormat 按源图像色彩模型、透明度与有损质量选项自动选择最优XPS图像格式
// 入参: img 源Go图像, quality 编码质量参数
// 返回: ImageEncodeFormat 选定格式
func chooseAutoImageFormat(img image.Image, quality int) ImageEncodeFormat {
	if _, ok := img.(*ImageCMYK16); ok {
		return ImageFormatTIFF
	}
	if _, ok := img.(*image.CMYK); ok {
		return ImageFormatJXR
	}
	switch img.(type) {
	case *image.NRGBA64, *image.RGBA64, *image.Gray16:
		if quality > 0 && quality < 100 {
			return ImageFormatJXR
		}
		return ImageFormatPNG
	}
	if quality > 0 && quality < 100 && goImageIsOpaque(img) {
		return ImageFormatJPEG
	}
	return ImageFormatPNG
}

// goImageIsOpaque 判断源图像所有像素是否完全不透明
// 入参: img 源Go图像
// 返回: bool 是否完全不透明
func goImageIsOpaque(img image.Image) bool {
	type opaqueChecker interface {
		Opaque() bool
	}
	if checker, ok := img.(opaqueChecker); ok {
		return checker.Opaque()
	}
	bounds := img.Bounds()
	for y := bounds.Min.Y; y < bounds.Max.Y; y++ {
		for x := bounds.Min.X; x < bounds.Max.X; x++ {
			_, _, _, a := img.At(x, y).RGBA()
			if a != 0xffff {
				return false
			}
		}
	}
	return true
}

// encodeGoImagePNG 编码标准PNG并在需要时注入pHYs分辨率块与iCCP色彩配置块
// 入参: ctx 取消Context, img 源Go图像, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节, maxBytes 字节上限
// 返回: []byte PNG字节, error 编码、预算或取消错误
func encodeGoImagePNG(ctx context.Context, img image.Image, dpix, dpiy float64, icc []byte, maxBytes int64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if _, _, err := encodePNGPhysPixels(dpix, dpiy); err != nil {
		return nil, err
	}
	var raw bytes.Buffer
	counted := packageOutput{writer: &raw, context: ctx, limit: maxBytes}
	if err := png.Encode(&counted, img); err != nil {
		return nil, err
	}
	data := raw.Bytes()
	if dpix == 0 && dpiy == 0 && len(icc) == 0 {
		return data, nil
	}
	if len(data) < 33 {
		return nil, fmt.Errorf("%w: truncated encoded PNG", ErrInvalid)
	}
	ihdrLen := binary.BigEndian.Uint32(data[8:12])
	insertPos := 8 + 12 + int(ihdrLen)
	if insertPos > len(data) {
		return nil, fmt.Errorf("%w: malformed encoded PNG IHDR", ErrInvalid)
	}
	var out bytes.Buffer
	outCounted := packageOutput{writer: &out, context: ctx, limit: maxBytes}
	if _, err := outCounted.Write(data[:insertPos]); err != nil {
		return nil, err
	}
	if err := encodePNGMetaChunks(&outCounted, dpix, dpiy, icc); err != nil {
		return nil, err
	}
	if _, err := outCounted.Write(data[insertPos:]); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

// encodePNGPhysPixels 校验并将浮点DPI换算为PNG pHYs块使用的每米像素数
// 入参: dpix 水平DPI, dpiy 垂直DPI
// 返回: uint32 水平每米像素数, uint32 垂直每米像素数, error 越界错误
func encodePNGPhysPixels(dpix, dpiy float64) (uint32, uint32, error) {
	if dpix <= 0 || dpiy <= 0 {
		return 0, 0, nil
	}
	pxf := math.Round(dpix / 0.0254)
	pyf := math.Round(dpiy / 0.0254)
	if !(pxf <= 0x7fffffff && pyf <= 0x7fffffff) {
		return 0, 0, fmt.Errorf("%w: PNG DPI exceeds pHYs limit", ErrInvalid)
	}
	px, py := uint32(pxf), uint32(pyf)
	if px == 0 {
		px = 1
	}
	if py == 0 {
		py = 1
	}
	return px, py, nil
}

// encodePNGMetaChunks 按标准块顺序向输出流写入可选的iCCP色彩配置块与pHYs物理分辨率块
// 入参: w 输出流, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节
// 返回: error 压缩、校验或写出错误
func encodePNGMetaChunks(w io.Writer, dpix, dpiy float64, icc []byte) error {
	if len(icc) != 0 {
		var compressed bytes.Buffer
		zw := zlib.NewWriter(&compressed)
		if _, err := zw.Write(icc); err != nil {
			_ = zw.Close()
			return err
		}
		if err := zw.Close(); err != nil {
			return err
		}
		payload := make([]byte, 0, 13+compressed.Len())
		payload = append(payload, []byte("ICC Profile")...)
		payload = append(payload, 0, 0)
		payload = append(payload, compressed.Bytes()...)
		if err := writePNGChunk(w, "iCCP", payload); err != nil {
			return err
		}
	}
	if dpix > 0 && dpiy > 0 {
		px, py, err := encodePNGPhysPixels(dpix, dpiy)
		if err != nil {
			return err
		}
		var phys [9]byte
		binary.BigEndian.PutUint32(phys[0:4], px)
		binary.BigEndian.PutUint32(phys[4:8], py)
		phys[8] = 1
		if err := writePNGChunk(w, "pHYs", phys[:]); err != nil {
			return err
		}
	}
	return nil
}

// newPNGRowEncoder 初始化逐行流式PNG编码器并写出PNG文件签名、IHDR及可选iCCP和pHYs块
// 入参: ctx 取消Context, w 目标输出流, width 图像宽度, height 图像高度, bitDepth 采样位深，支持8或16, colorType PNG色彩类型，支持0、2、4或6, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节
// 返回: *pngRowEncoder 逐行PNG编码器, error 参数、预算、取消或写出错误
func newPNGRowEncoder(ctx context.Context, w io.Writer, width, height int, bitDepth, colorType uint8, dpix, dpiy float64, icc []byte) (*pngRowEncoder, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if w == nil || width < 1 || height < 1 || width > rasterMaxDimension || height > rasterMaxDimension {
		return nil, fmt.Errorf("%w: invalid streaming PNG dimensions or writer", ErrInvalid)
	}
	if bitDepth != 8 && bitDepth != 16 {
		return nil, fmt.Errorf("%w: unsupported streaming PNG bit depth %d", ErrInvalid, bitDepth)
	}
	var channels int
	switch colorType {
	case 0:
		channels = 1
	case 2:
		channels = 3
	case 4:
		channels = 2
	case 6:
		channels = 4
	default:
		return nil, fmt.Errorf("%w: unsupported streaming PNG color type %d", ErrInvalid, colorType)
	}
	rowBytes64 := int64(width) * int64(channels) * int64(bitDepth/8)
	if rowBytes64 <= 0 || rowBytes64 > int64(^uint(0)>>1) {
		return nil, fmt.Errorf("%w: streaming PNG row length overflow", ErrLimit)
	}
	if _, _, err := encodePNGPhysPixels(dpix, dpiy); err != nil {
		return nil, err
	}
	if _, err := w.Write([]byte{0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n'}); err != nil {
		return nil, err
	}
	var ihdr [13]byte
	binary.BigEndian.PutUint32(ihdr[0:4], uint32(width))
	binary.BigEndian.PutUint32(ihdr[4:8], uint32(height))
	ihdr[8] = bitDepth
	ihdr[9] = colorType
	if err := writePNGChunk(w, "IHDR", ihdr[:]); err != nil {
		return nil, err
	}
	if err := encodePNGMetaChunks(w, dpix, dpiy, icc); err != nil {
		return nil, err
	}
	enc := &pngRowEncoder{
		w:        w,
		idat:     pngIDATWriter{w: w, buf: make([]byte, 0, pngStreamIDATChunk)},
		height:   height,
		rowBytes: int(rowBytes64),
	}
	enc.zw = zlib.NewWriter(&enc.idat)
	return enc, nil
}

// Write 接收zlib压缩数据并在缓冲达到块上限时封装为标准IDAT块写出
// 入参: p 压缩数据切片
// 返回: int 已接收字节数, error 写出错误
func (w *pngIDATWriter) Write(p []byte) (int, error) {
	total := len(p)
	for len(p) > 0 {
		space := cap(w.buf) - len(w.buf)
		if space == 0 {
			if err := w.flush(); err != nil {
				return total - len(p), err
			}
			space = cap(w.buf)
		}
		take := min(len(p), space)
		w.buf = append(w.buf, p[:take]...)
		p = p[take:]
	}
	return total, nil
}

// flush 将缓冲区中尚未落盘的压缩字节写出为单个IDAT块
// 返回: error 写出错误
func (w *pngIDATWriter) flush() error {
	if len(w.buf) == 0 {
		return nil
	}
	err := writePNGChunk(w.w, "IDAT", w.buf)
	w.buf = w.buf[:0]
	return err
}

// writeRow 写入单条未滤波扫描行并推进流式zlib压缩
// 入参: ctx 取消Context, row 原始扫描行字节，长度必须等于rowBytes
// 返回: error 行数、长度、取消或写出错误
func (e *pngRowEncoder) writeRow(ctx context.Context, row []byte) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if e.closed {
		return fmt.Errorf("%w: streaming PNG encoder is closed", ErrClosed)
	}
	if e.rows >= e.height {
		return fmt.Errorf("%w: streaming PNG row count exceeds height", ErrInvalid)
	}
	if len(row) != e.rowBytes {
		return fmt.Errorf("%w: streaming PNG row length mismatch: got %d want %d", ErrInvalid, len(row), e.rowBytes)
	}
	var filter [1]byte
	if _, err := e.zw.Write(filter[:]); err != nil {
		return err
	}
	if _, err := e.zw.Write(row); err != nil {
		return err
	}
	e.rows++
	return nil
}

// close 校验已写入行数与高度匹配、刷新尾块IDAT并写出IEND结束块
// 入参: ctx 取消Context
// 返回: error 行数不足、压缩、取消或写出错误
func (e *pngRowEncoder) close(ctx context.Context) error {
	if e.closed {
		return nil
	}
	e.closed = true
	if err := checkContext(ctx); err != nil {
		_ = e.zw.Close()
		return err
	}
	if e.rows != e.height {
		_ = e.zw.Close()
		return fmt.Errorf("%w: streaming PNG wrote %d of %d rows", ErrInvalid, e.rows, e.height)
	}
	if err := e.zw.Close(); err != nil {
		return err
	}
	if err := e.idat.flush(); err != nil {
		return err
	}
	return writePNGChunk(e.w, "IEND", nil)
}

// writePNGChunk 写入带长度、类型标识与CRC32的标准PNG数据块
// 入参: w 输出流, chunkType 四字节块类型, payload 块载荷
// 返回: error 写入错误
func writePNGChunk(w io.Writer, chunkType string, payload []byte) error {
	var header [8]byte
	binary.BigEndian.PutUint32(header[0:4], uint32(len(payload)))
	copy(header[4:8], chunkType)
	if _, err := w.Write(header[:]); err != nil {
		return err
	}
	if _, err := w.Write(payload); err != nil {
		return err
	}
	sum := crc32.NewIEEE()
	_, _ = sum.Write(header[4:8])
	_, _ = sum.Write(payload)
	var tail [4]byte
	binary.BigEndian.PutUint32(tail[:], sum.Sum32())
	_, err := w.Write(tail[:])
	return err
}

// encodeGoImageJPEG 编码标准JPEG并按需写入APP0 JFIF分辨率与APP2 ICC_PROFILE分段
// 入参: ctx 取消Context, img 源Go图像, quality 质量参数，0采用90, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节, maxBytes 字节上限
// 返回: []byte JPEG字节, error 编码、预算或取消错误
func encodeGoImageJPEG(ctx context.Context, img image.Image, quality int, dpix, dpiy float64, icc []byte, maxBytes int64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	var dx, dy uint16
	if dpix > 0 && dpiy > 0 {
		var err error
		dx, err = encodeJPEGDPI(dpix)
		if err != nil {
			return nil, err
		}
		dy, err = encodeJPEGDPI(dpiy)
		if err != nil {
			return nil, err
		}
	}
	if quality == 0 {
		quality = 90
	}
	src := img
	if _, isCMYK := img.(*image.CMYK); isCMYK {
		bounds := img.Bounds()
		rgba := image.NewRGBA(bounds)
		draw.Draw(rgba, bounds, img, bounds.Min, draw.Src)
		src = rgba
	}
	var raw bytes.Buffer
	counted := packageOutput{writer: &raw, context: ctx, limit: maxBytes}
	if err := jpeg.Encode(&counted, src, &jpeg.Options{Quality: quality}); err != nil {
		return nil, err
	}
	data := raw.Bytes()
	if dpix == 0 && dpiy == 0 && len(icc) == 0 {
		return data, nil
	}
	if len(data) < 2 || data[0] != 0xff || data[1] != 0xd8 {
		return nil, fmt.Errorf("%w: malformed encoded JPEG", ErrInvalid)
	}
	var out bytes.Buffer
	outCounted := packageOutput{writer: &out, context: ctx, limit: maxBytes}
	if _, err := outCounted.Write(data[:2]); err != nil {
		return nil, err
	}
	rest := data[2:]
	if len(rest) >= 4 && rest[0] == 0xff && rest[1] == 0xe0 {
		segLen := int(binary.BigEndian.Uint16(rest[2:4]))
		if 2+segLen <= len(rest) && segLen >= 16 && bytes.Equal(rest[4:9], []byte{'J', 'F', 'I', 'F', 0}) {
			if dpix > 0 && dpiy > 0 {
				rest = rest[2+segLen:]
			} else {
				if _, err := outCounted.Write(rest[:2+segLen]); err != nil {
					return nil, err
				}
				rest = rest[2+segLen:]
			}
		}
	}
	if dpix > 0 && dpiy > 0 {
		jfif := []byte{0xff, 0xe0, 0x00, 0x10, 'J', 'F', 'I', 'F', 0x00, 0x01, 0x01, 0x01, byte(dx >> 8), byte(dx), byte(dy >> 8), byte(dy), 0x00, 0x00}
		if _, err := outCounted.Write(jfif); err != nil {
			return nil, err
		}
	}
	if len(icc) != 0 {
		const maxChunk = 65519
		count := (len(icc) + maxChunk - 1) / maxChunk
		if count > 255 {
			return nil, fmt.Errorf("%w: ICC profile exceeds JPEG APP2 segment limit", ErrLimit)
		}
		for idx := range count {
			start := idx * maxChunk
			end := min(start+maxChunk, len(icc))
			chunk := icc[start:end]
			segLen := uint16(2 + 14 + len(chunk))
			header := make([]byte, 18)
			header[0], header[1] = 0xff, 0xe2
			binary.BigEndian.PutUint16(header[2:4], segLen)
			copy(header[4:16], []byte("ICC_PROFILE\x00"))
			header[16] = byte(idx + 1)
			header[17] = byte(count)
			if _, err := outCounted.Write(header); err != nil {
				return nil, err
			}
			if _, err := outCounted.Write(chunk); err != nil {
				return nil, err
			}
		}
	}
	if _, err := outCounted.Write(rest); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

// encodeJPEGDPI 校验并将浮点DPI转换为JFIF 16位无符号整数分辨率，超出65535返回ErrInvalid
// 入参: value 浮点分辨率
// 返回: uint16 JFIF分辨率值, error 越界错误
func encodeJPEGDPI(value float64) (uint16, error) {
	rounded := math.Round(value)
	if !(rounded <= 65535) {
		return 0, fmt.Errorf("%w: JPEG DPI exceeds JFIF uint16 limit", ErrInvalid)
	}
	if rounded < 1 {
		return 1, nil
	}
	return uint16(rounded), nil
}

// encodeGoImageTIFF 编码标准Little-Endian多Strip Baseline TIFF，支持无压缩、PackBits、Adobe Deflate、LZW与1位CCITT Group 4压缩及灰度、RGB、RGBA、16位、8/16位CMYK、DPI与ICC标签
// 压缩模式下按目标Strip大小逐条带编码并约束中间像素缓冲，防止低maxBytes预算下的无界大内存分配
// 入参: ctx 取消Context, img 源Go图像, compression 无损压缩方式, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节, maxBytes 字节上限, maxPixels 像素总数上限
// 返回: []byte TIFF字节, error 编码、预算或取消错误
func encodeGoImageTIFF(ctx context.Context, img image.Image, compression TIFFCompression, dpix, dpiy float64, icc []byte, maxBytes int64, maxPixels uint64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	bounds := img.Bounds()
	w, h := bounds.Dx(), bounds.Dy()
	if w <= 0 || h <= 0 || w > rasterMaxDimension || h > rasterMaxDimension || maxPixels > 0 && uint64(w) > maxPixels/uint64(h) {
		return nil, fmt.Errorf("%w: encoded TIFF exceeds pixel budget", ErrLimit)
	}
	spec := tiffStripSpec{
		width:       w,
		height:      h,
		compression: compression,
		dpix:        dpix,
		dpiy:        dpiy,
		icc:         icc,
	}
	var rowBytes int
	var fillRow func(dst []byte, y int)
	if compression == TIFFCompressionCCITTGroup4 {
		spec.spp, spec.bps, spec.photometric = 1, 1, 0
		rowBytes = (w + 7) / 8
		fillRow = func(dst []byte, y int) {
			clear(dst)
			sy := bounds.Min.Y + y
			switch typed := img.(type) {
			case *image.Gray:
				rowOff := typed.PixOffset(bounds.Min.X, sy)
				for x := range w {
					if typed.Pix[rowOff+x] < 128 {
						dst[x>>3] |= 1 << uint(7-x&7)
					}
				}
			case *image.Gray16:
				for x := range w {
					if typed.Gray16At(bounds.Min.X+x, sy).Y < 32768 {
						dst[x>>3] |= 1 << uint(7-x&7)
					}
				}
			default:
				for x := range w {
					if color.GrayModel.Convert(img.At(bounds.Min.X+x, sy)).(color.Gray).Y < 128 {
						dst[x>>3] |= 1 << uint(7-x&7)
					}
				}
			}
		}
	} else {
		switch typed := img.(type) {
		case *image.Gray:
			spec.spp, spec.bps, spec.photometric = 1, 8, 1
			rowBytes = w
			fillRow = func(dst []byte, y int) {
				rowOff := typed.PixOffset(bounds.Min.X, bounds.Min.Y+y)
				copy(dst, typed.Pix[rowOff:rowOff+w])
			}
		case *image.Gray16:
			spec.spp, spec.bps, spec.photometric = 1, 16, 1
			rowBytes = w * 2
			fillRow = func(dst []byte, y int) {
				sy := bounds.Min.Y + y
				for x := range w {
					binary.LittleEndian.PutUint16(dst[x*2:], typed.Gray16At(bounds.Min.X+x, sy).Y)
				}
			}
		case *image.CMYK:
			spec.spp, spec.bps, spec.photometric = 4, 8, 5
			rowBytes = w * 4
			fillRow = func(dst []byte, y int) {
				rowOff := typed.PixOffset(bounds.Min.X, bounds.Min.Y+y)
				copy(dst, typed.Pix[rowOff:rowOff+w*4])
			}
		case *ImageCMYK16:
			spec.spp, spec.bps, spec.photometric = 4, 16, 5
			rowBytes = w * 8
			fillRow = func(dst []byte, y int) {
				sy := bounds.Min.Y + y
				for x := range w {
					c := typed.CMYK16At(bounds.Min.X+x, sy)
					off := x * 8
					binary.LittleEndian.PutUint16(dst[off:], c.C)
					binary.LittleEndian.PutUint16(dst[off+2:], c.M)
					binary.LittleEndian.PutUint16(dst[off+4:], c.Y)
					binary.LittleEndian.PutUint16(dst[off+6:], c.K)
				}
			}
		case *image.NRGBA64:
			spec.spp, spec.bps, spec.photometric, spec.extraSample, spec.hasExtra = 4, 16, 2, 2, true
			rowBytes = w * 8
			fillRow = func(dst []byte, y int) {
				sy := bounds.Min.Y + y
				for x := range w {
					c := typed.NRGBA64At(bounds.Min.X+x, sy)
					off := x * 8
					binary.LittleEndian.PutUint16(dst[off:], c.R)
					binary.LittleEndian.PutUint16(dst[off+2:], c.G)
					binary.LittleEndian.PutUint16(dst[off+4:], c.B)
					binary.LittleEndian.PutUint16(dst[off+6:], c.A)
				}
			}
		case *image.RGBA64:
			spec.spp, spec.bps, spec.photometric, spec.extraSample, spec.hasExtra = 4, 16, 2, 1, true
			rowBytes = w * 8
			fillRow = func(dst []byte, y int) {
				sy := bounds.Min.Y + y
				for x := range w {
					c := typed.RGBA64At(bounds.Min.X+x, sy)
					off := x * 8
					binary.LittleEndian.PutUint16(dst[off:], c.R)
					binary.LittleEndian.PutUint16(dst[off+2:], c.G)
					binary.LittleEndian.PutUint16(dst[off+4:], c.B)
					binary.LittleEndian.PutUint16(dst[off+6:], c.A)
				}
			}
		default:
			if goImageIsOpaque(img) {
				spec.spp, spec.bps, spec.photometric = 3, 8, 2
				rowBytes = w * 3
				fillRow = func(dst []byte, y int) {
					sy := bounds.Min.Y + y
					for x := range w {
						c := color.NRGBAModel.Convert(img.At(bounds.Min.X+x, sy)).(color.NRGBA)
						off := x * 3
						dst[off], dst[off+1], dst[off+2] = c.R, c.G, c.B
					}
				}
			} else {
				spec.spp, spec.bps, spec.photometric, spec.extraSample, spec.hasExtra = 4, 8, 2, 2, true
				rowBytes = w * 4
				fillRow = func(dst []byte, y int) {
					sy := bounds.Min.Y + y
					for x := range w {
						c := color.NRGBAModel.Convert(img.At(bounds.Min.X+x, sy)).(color.NRGBA)
						off := x * 4
						dst[off], dst[off+1], dst[off+2], dst[off+3] = c.R, c.G, c.B, c.A
					}
				}
			}
		}
	}
	if compression == TIFFCompressionNone && int64(h) > maxBytes/int64(rowBytes) {
		return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	rowsPerStrip, err := tiffRowsPerStrip(rowBytes, h, maxBytes)
	if err != nil {
		return nil, err
	}
	spec.rowsPerStrip = rowsPerStrip
	stripCount := (h + rowsPerStrip - 1) / rowsPerStrip
	strips := make([][]byte, 0, stripCount)
	rawBuf := make([]byte, rowsPerStrip*rowBytes)
	usedBytes := int64(8)
	for y := 0; y < h; y += rowsPerStrip {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		rows := min(rowsPerStrip, h-y)
		chunk := rawBuf[:rows*rowBytes]
		for row := range rows {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			fillRow(chunk[row*rowBytes:(row+1)*rowBytes], y+row)
		}
		remaining := maxBytes - usedBytes
		if remaining <= 0 {
			return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		encoded, err := encodeTIFFStripData(ctx, chunk, w, rows, rowBytes, compression, remaining)
		if err != nil {
			return nil, err
		}
		if compression == TIFFCompressionNone {
			encoded = bytes.Clone(encoded)
		}
		usedBytes += int64(len(encoded))
		if usedBytes > maxBytes || usedBytes > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		strips = append(strips, encoded)
	}
	return encodeTIFFStrips(ctx, spec, strips, maxBytes)
}

// tiffRowsPerStrip 按单条带64KiB目标大小及maxBytes预算计算多Strip TIFF每条带行数
// 入参: rowBytes 单扫描行字节长度, height 图像总行数, maxBytes 输出与中间缓冲字节上限
// 返回: int 每条带行数, error 参数或预算错误
func tiffRowsPerStrip(rowBytes, height int, maxBytes int64) (int, error) {
	if rowBytes <= 0 || height <= 0 || maxBytes <= 0 {
		return 0, fmt.Errorf("%w: invalid TIFF strip dimensions or budget", ErrInvalid)
	}
	if int64(rowBytes) > maxBytes || int64(rowBytes) > math.MaxUint32 {
		return 0, fmt.Errorf("%w: encoded TIFF row exceeds byte budget", ErrLimit)
	}
	budget := min(int64(tiffTargetStripBytes), maxBytes)
	rows := int(budget / int64(rowBytes))
	if rows < 1 {
		rows = 1
	}
	if rows > height {
		rows = height
	}
	return rows, nil
}

// encodeTIFFStripData 将单个TIFF条带的原始未压缩像素按指定压缩算法编码
// 入参: ctx 取消Context, raw 单条带未压缩像素字节, width 图像像素宽度, rows 条带行数, rowBytes 单行字节数, compression 无损压缩方式, maxBytes 输出字节上限
// 返回: []byte 条带编码字节, error 压缩、预算或取消错误
func encodeTIFFStripData(ctx context.Context, raw []byte, width, rows, rowBytes int, compression TIFFCompression, maxBytes int64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if rowBytes <= 0 || rows <= 0 || len(raw) != rows*rowBytes {
		return nil, fmt.Errorf("%w: invalid TIFF strip raw size", ErrInvalid)
	}
	switch compression {
	case TIFFCompressionNone:
		if int64(len(raw)) > maxBytes || int64(len(raw)) > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded TIFF strip exceeds byte budget", ErrLimit)
		}
		return raw, nil
	case TIFFCompressionPackBits:
		return encodeTIFFPackBits(ctx, raw, rowBytes, maxBytes)
	case TIFFCompressionDeflate:
		return encodeTIFFDeflate(ctx, raw, maxBytes)
	case TIFFCompressionLZW:
		return encodeTIFFLZW(ctx, raw, maxBytes)
	case TIFFCompressionCCITTGroup4:
		return encodeTIFFCCITTGroup4(ctx, raw, width, rows, maxBytes)
	default:
		return nil, fmt.Errorf("%w: unsupported TIFF compression %d", ErrInvalid, compression)
	}
}

// encodeTIFFStrips 将已压缩的一个或多个TIFF条带与IFD目录装配为完整Little-Endian Baseline TIFF字节
// 入参: ctx 取消Context, spec 图像与条带规格, strips 已编码条带切片, maxBytes 总输出字节上限
// 返回: []byte 完整TIFF字节, error 参数、偏移、预算或取消错误
func encodeTIFFStrips(ctx context.Context, spec tiffStripSpec, strips [][]byte, maxBytes int64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if spec.width <= 0 || spec.height <= 0 || spec.rowsPerStrip <= 0 || len(strips) == 0 {
		return nil, fmt.Errorf("%w: invalid TIFF strip assembly spec", ErrInvalid)
	}
	expectedStrips := (spec.height + spec.rowsPerStrip - 1) / spec.rowsPerStrip
	if len(strips) != expectedStrips {
		return nil, fmt.Errorf("%w: TIFF strip count mismatch: got %d want %d", ErrInvalid, len(strips), expectedStrips)
	}
	offsets := make([]uint32, len(strips))
	counts := make([]uint32, len(strips))
	cursor := int64(8)
	for i, strip := range strips {
		if int64(len(strip)) > math.MaxUint32 || cursor+int64(len(strip)) > maxBytes || cursor+int64(len(strip)) > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		offsets[i] = uint32(cursor)
		counts[i] = uint32(len(strip))
		cursor += int64(len(strip))
	}
	pad := cursor & 1
	ifdOffset := cursor + pad
	if ifdOffset > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	ifdBytes, err := encodeTIFFIFD(spec, offsets, counts, uint32(ifdOffset))
	if err != nil {
		return nil, err
	}
	total := ifdOffset + int64(len(ifdBytes))
	if total > maxBytes || total > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	out := make([]byte, int(total))
	copy(out[0:2], "II")
	binary.LittleEndian.PutUint16(out[2:4], 42)
	binary.LittleEndian.PutUint32(out[4:8], uint32(ifdOffset))
	pos := 8
	for _, strip := range strips {
		copy(out[pos:], strip)
		pos += len(strip)
	}
	copy(out[int(ifdOffset):], ifdBytes)
	return out, checkContext(ctx)
}

// encodeTIFFIFD 按TIFF 6.0规范将目录项按Tag升序编码为含附加数据区的IFD二进制块
// 入参: spec 图像与压缩规格, stripOffsets 各条带文件偏移数组, stripCounts 各条带字节长度数组, ifdOffset 本IFD块在文件中的起始偏移
// 返回: []byte 完整IFD与外部字段数据区字节, error 标签、DPI或范围错误
func encodeTIFFIFD(spec tiffStripSpec, stripOffsets, stripCounts []uint32, ifdOffset uint32) ([]byte, error) {
	if len(stripOffsets) == 0 || len(stripOffsets) != len(stripCounts) {
		return nil, fmt.Errorf("%w: invalid TIFF strip offset/count arrays", ErrInvalid)
	}
	dpix, dpiy := spec.dpix, spec.dpiy
	if dpix == 0 || dpiy == 0 {
		dpix, dpiy = 96, 96
	}
	xNum := math.Round(dpix * 1000)
	yNum := math.Round(dpiy * 1000)
	if !(xNum <= math.MaxUint32 && yNum <= math.MaxUint32) {
		return nil, fmt.Errorf("%w: TIFF DPI exceeds rational range", ErrInvalid)
	}
	if xNum < 1 {
		xNum = 1
	}
	if yNum < 1 {
		yNum = 1
	}
	var compressionTag uint32
	switch spec.compression {
	case TIFFCompressionNone:
		compressionTag = 1
	case TIFFCompressionPackBits:
		compressionTag = 32773
	case TIFFCompressionDeflate:
		compressionTag = 8
	case TIFFCompressionLZW:
		compressionTag = 5
	case TIFFCompressionCCITTGroup4:
		compressionTag = 4
	default:
		return nil, fmt.Errorf("%w: unsupported TIFF compression %d", ErrInvalid, spec.compression)
	}
	type tiffEntry struct {
		tag   uint16
		kind  uint16
		count uint32
		value uint32
		extra []byte
	}
	entries := make([]tiffEntry, 0, 16)
	entries = append(entries,
		tiffEntry{tag: 256, kind: 4, count: 1, value: uint32(spec.width)},
		tiffEntry{tag: 257, kind: 4, count: 1, value: uint32(spec.height)},
	)
	if spec.spp == 1 {
		entries = append(entries, tiffEntry{tag: 258, kind: 3, count: 1, value: uint32(spec.bps)})
	} else {
		bpsBytes := make([]byte, int(spec.spp)*2)
		for i := range int(spec.spp) {
			binary.LittleEndian.PutUint16(bpsBytes[i*2:], spec.bps)
		}
		entries = append(entries, tiffEntry{tag: 258, kind: 3, count: uint32(spec.spp), extra: bpsBytes})
	}
	xRat := make([]byte, 8)
	binary.LittleEndian.PutUint32(xRat[0:4], uint32(xNum))
	binary.LittleEndian.PutUint32(xRat[4:8], 1000)
	yRat := make([]byte, 8)
	binary.LittleEndian.PutUint32(yRat[0:4], uint32(yNum))
	binary.LittleEndian.PutUint32(yRat[4:8], 1000)
	var offsetEntry, countEntry tiffEntry
	if len(stripOffsets) == 1 {
		offsetEntry = tiffEntry{tag: 273, kind: 4, count: 1, value: stripOffsets[0]}
		countEntry = tiffEntry{tag: 279, kind: 4, count: 1, value: stripCounts[0]}
	} else {
		offBytes := make([]byte, len(stripOffsets)*4)
		cntBytes := make([]byte, len(stripCounts)*4)
		for i := range stripOffsets {
			binary.LittleEndian.PutUint32(offBytes[i*4:], stripOffsets[i])
			binary.LittleEndian.PutUint32(cntBytes[i*4:], stripCounts[i])
		}
		offsetEntry = tiffEntry{tag: 273, kind: 4, count: uint32(len(stripOffsets)), extra: offBytes}
		countEntry = tiffEntry{tag: 279, kind: 4, count: uint32(len(stripCounts)), extra: cntBytes}
	}
	entries = append(entries,
		tiffEntry{tag: 259, kind: 3, count: 1, value: compressionTag},
		tiffEntry{tag: 262, kind: 3, count: 1, value: uint32(spec.photometric)},
		offsetEntry,
		tiffEntry{tag: 277, kind: 3, count: 1, value: uint32(spec.spp)},
		tiffEntry{tag: 278, kind: 4, count: 1, value: uint32(spec.rowsPerStrip)},
		countEntry,
		tiffEntry{tag: 282, kind: 5, count: 1, extra: xRat},
		tiffEntry{tag: 283, kind: 5, count: 1, extra: yRat},
		tiffEntry{tag: 296, kind: 3, count: 1, value: 2},
	)
	if spec.compression == TIFFCompressionCCITTGroup4 {
		entries = append(entries, tiffEntry{tag: 293, kind: 4, count: 1, value: 0})
	}
	if spec.hasExtra {
		entries = append(entries, tiffEntry{tag: 338, kind: 3, count: 1, value: uint32(spec.extraSample)})
	}
	if len(spec.icc) != 0 {
		if int64(len(spec.icc)) > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		entries = append(entries, tiffEntry{tag: 34675, kind: 7, count: uint32(len(spec.icc)), extra: spec.icc})
	}
	slices.SortFunc(entries, func(a, b tiffEntry) int { return int(a.tag) - int(b.tag) })
	ifdSize := int64(2 + len(entries)*12 + 4)
	total := ifdSize
	for _, entry := range entries {
		if len(entry.extra) > 4 {
			total += int64(len(entry.extra) + (len(entry.extra) & 1))
		}
	}
	if int64(ifdOffset)+total > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded TIFF IFD exceeds offset limit", ErrLimit)
	}
	out := make([]byte, int(total))
	binary.LittleEndian.PutUint16(out[0:], uint16(len(entries)))
	cursor := int(ifdSize)
	for i, entry := range entries {
		pos := 2 + i*12
		binary.LittleEndian.PutUint16(out[pos:], entry.tag)
		binary.LittleEndian.PutUint16(out[pos+2:], entry.kind)
		binary.LittleEndian.PutUint32(out[pos+4:], entry.count)
		if len(entry.extra) == 0 {
			binary.LittleEndian.PutUint32(out[pos+8:], entry.value)
		} else if len(entry.extra) <= 4 {
			copy(out[pos+8:], entry.extra)
		} else {
			binary.LittleEndian.PutUint32(out[pos+8:], ifdOffset+uint32(cursor))
			copy(out[cursor:], entry.extra)
			cursor += len(entry.extra) + (len(entry.extra) & 1)
		}
	}
	return out, nil
}

// writeBits 将无符号整数的低length位按MSB优先写入有界字节流
// 入参: code 待写入码字, length 位宽（1至24）
// 返回: error 字节预算错误
func (w *tiffBitWriter) writeBits(code uint32, length uint) error {
	w.acc = w.acc<<length | uint64(code&((uint32(1)<<length)-1))
	w.bits += length
	for w.bits >= 8 {
		w.bits -= 8
		if int64(len(w.out))+1 > w.limit {
			return fmt.Errorf("%w: encoded TIFF bitstream exceeds byte budget", ErrLimit)
		}
		w.out = append(w.out, byte(w.acc>>w.bits))
	}
	return nil
}

// flush 将未满一字节的尾部残余位低位补零并写入输出缓冲
// 返回: error 字节预算错误
func (w *tiffBitWriter) flush() error {
	if w.bits == 0 {
		return nil
	}
	if int64(len(w.out))+1 > w.limit {
		return fmt.Errorf("%w: encoded TIFF bitstream exceeds byte budget", ErrLimit)
	}
	w.out = append(w.out, byte(w.acc<<(8-w.bits)))
	w.bits = 0
	w.acc = 0
	return nil
}

// encodeTIFFLZW 按TIFF 6.0规范以MSB优先变长码执行LZW无损压缩，与decodeTIFFLZW严格互逆
// 入参: ctx 取消Context, data 条带原始字节, maxBytes 输出字节上限
// 返回: []byte LZW压缩条带字节, error 预算或取消错误
func encodeTIFFLZW(ctx context.Context, data []byte, maxBytes int64) ([]byte, error) {
	limit := min(maxBytes, int64(math.MaxUint32))
	bw := tiffBitWriter{out: make([]byte, 0, min(int64(len(data)), limit)), limit: limit}
	const clearCode = 256
	const eoiCode = 257
	const tableSize = 8192
	const tableMask = tableSize - 1
	var keys [tableSize]uint32
	var vals [tableSize]uint16
	var gens [tableSize]uint32
	gen := uint32(1)
	width := uint(9)
	next := uint16(258)
	if err := bw.writeBits(clearCode, width); err != nil {
		return nil, err
	}
	if len(data) == 0 {
		if err := bw.writeBits(eoiCode, width); err != nil {
			return nil, err
		}
		if err := bw.flush(); err != nil {
			return nil, err
		}
		return bw.out, nil
	}
	w := uint16(data[0])
	for i := 1; i < len(data); i++ {
		if i&4095 == 0 {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
		}
		k := data[i]
		key := uint32(w)<<8 | uint32(k) | 0x80000000
		slot := int((key * 2654435761) >> 19 & tableMask)
		found := false
		for gens[slot] == gen {
			if keys[slot] == key {
				w = vals[slot]
				found = true
				break
			}
			slot = (slot + 1) & tableMask
		}
		if found {
			continue
		}
		if err := bw.writeBits(uint32(w), width); err != nil {
			return nil, err
		}
		keys[slot] = key
		vals[slot] = next
		gens[slot] = gen
		next++
		if next == 4094 {
			if err := bw.writeBits(clearCode, width); err != nil {
				return nil, err
			}
			width = 9
			next = 258
			gen++
			if gen == 0 {
				clear(gens[:])
				gen = 1
			}
		} else if width < 12 && next == uint16(1<<width) {
			width++
		}
		w = uint16(k)
	}
	if err := bw.writeBits(uint32(w), width); err != nil {
		return nil, err
	}
	if width < 12 && next == uint16(1<<width)-1 {
		width++
	}
	if err := bw.writeBits(eoiCode, width); err != nil {
		return nil, err
	}
	if err := bw.flush(); err != nil {
		return nil, err
	}
	return bw.out, checkContext(ctx)
}

// buildTIFFFaxEncodeTable 将104项T.4/T.6二进制字符串码表预编译为高16位位宽、低16位码字的查找数组
// 入参: codes 按0..63终止码与64..2560补充码顺序排列的码字切片
// 返回: [104]uint32 预编译编码查找表
func buildTIFFFaxEncodeTable(codes []string) [104]uint32 {
	var table [104]uint32
	for i, code := range codes {
		var bits uint32
		for _, ch := range code {
			bits = bits<<1 | uint32(ch-'0')
		}
		table[i] = uint32(len(code))<<16 | bits
	}
	return table
}

// writeTIFFFaxRun 按ITU-T T.4/T.6标准写出单色游程长度所需的零至多个补充码与唯一终止码
// 入参: bw MSB位流写入器, length 游程像素数, black 是否为黑色游程
// 返回: error 字节预算错误
func writeTIFFFaxRun(bw *tiffBitWriter, length int, black bool) error {
	table := &tiffFaxWhiteEncode
	if black {
		table = &tiffFaxBlackEncode
	}
	for length >= 2560 {
		entry := table[103]
		if err := bw.writeBits(entry&0xffff, uint(entry>>16)); err != nil {
			return err
		}
		length -= 2560
	}
	if length >= 64 {
		entry := table[63+length/64]
		if err := bw.writeBits(entry&0xffff, uint(entry>>16)); err != nil {
			return err
		}
		length %= 64
	}
	entry := table[length]
	return bw.writeBits(entry&0xffff, uint(entry>>16))
}

// extractTIFFFaxChanges 提取1位MSB打包二值扫描行中由白(0)到黑(1)及由黑到白的所有变色列位置
// 入参: row 单行1位打包位图, width 有效像素列数, dst 复用的变色点切片缓冲
// 返回: []int 严格递增且小于width的变色列号切片
func extractTIFFFaxChanges(row []byte, width int, dst []int) []int {
	changes := dst[:0]
	black := false
	x := 0
	for x < width {
		if x&7 == 0 && x+8 <= width {
			b := row[x>>3]
			if !black && b == 0 || black && b == 0xff {
				x += 8
				continue
			}
		}
		bit := (row[x>>3]>>uint(7-x&7))&1 != 0
		if bit != black {
			changes = append(changes, x)
			black = bit
		}
		x++
	}
	return changes
}

// encodeTIFFCCITTGroup4 按ITU-T T.6二维传真标准压缩1位MSB二值条带（0白1黑），输出含EOFB的Group 4位流
// 入参: ctx 取消Context, data 1位打包条带像素, width 像素宽度, rows 条带行数, maxBytes 输出字节上限
// 返回: []byte CCITT Group 4压缩条带字节, error 参数、预算或取消错误
func encodeTIFFCCITTGroup4(ctx context.Context, data []byte, width, rows int, maxBytes int64) ([]byte, error) {
	rowBytes := (width + 7) / 8
	if width <= 0 || rows <= 0 || len(data) != rows*rowBytes {
		return nil, fmt.Errorf("%w: invalid TIFF CCITT Group 4 strip layout", ErrInvalid)
	}
	limit := min(maxBytes, int64(math.MaxUint32))
	bw := tiffBitWriter{out: make([]byte, 0, min(int64(len(data)), limit)), limit: limit}
	reference := make([]int, 0, width+3)
	reference = append(reference, width, width, width)
	current := make([]int, 0, width+3)
	for y := range rows {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		row := data[y*rowBytes : (y+1)*rowBytes]
		current = extractTIFFFaxChanges(row, width, current)
		curLen := len(current)
		current = append(current, width, width, width)
		position, refCursor, curIdx := 0, 0, 0
		black, started := false, false
		for position < width {
			for curIdx < curLen && (current[curIdx] < position || started && current[curIdx] == position) {
				curIdx++
			}
			a1 := current[curIdx]
			a2 := current[curIdx+1]
			for refCursor < len(reference) && (reference[refCursor] < position || started && reference[refCursor] == position) {
				refCursor++
			}
			refIdx := refCursor
			if (refIdx&1 == 1) != black {
				refIdx++
			}
			b1, b2 := width, width
			if refIdx < len(reference) {
				b1 = reference[refIdx]
			}
			if refIdx+1 < len(reference) {
				b2 = reference[refIdx+1]
			}
			if b2 < a1 {
				if err := bw.writeBits(1, 4); err != nil {
					return nil, err
				}
				position = b2
				started = true
				continue
			}
			delta := a1 - b1
			if delta >= -3 && delta <= 3 {
				var code uint32
				var length uint
				switch delta {
				case 0:
					code, length = 1, 1
				case 1:
					code, length = 3, 3
				case -1:
					code, length = 2, 3
				case 2:
					code, length = 3, 6
				case -2:
					code, length = 2, 6
				case 3:
					code, length = 3, 7
				case -3:
					code, length = 2, 7
				}
				if err := bw.writeBits(code, length); err != nil {
					return nil, err
				}
				position = a1
				black = !black
				started = true
				continue
			}
			if err := bw.writeBits(1, 3); err != nil {
				return nil, err
			}
			if err := writeTIFFFaxRun(&bw, a1-position, black); err != nil {
				return nil, err
			}
			if err := writeTIFFFaxRun(&bw, a2-a1, !black); err != nil {
				return nil, err
			}
			position = a2
			started = true
		}
		reference, current = current, reference[:0]
	}
	if err := bw.writeBits(0x001001, 24); err != nil {
		return nil, err
	}
	if err := bw.flush(); err != nil {
		return nil, err
	}
	return bw.out, checkContext(ctx)
}

// encodeTIFFPackBits 按TIFF 6.0规范逐行执行PackBits无损字节游程编码，严格保证游程不跨越行边界
// 入参: ctx 取消Context, pixels 原始交织像素字节, rowBytes 单扫描行字节长度, maxBytes 输出字节上限
// 返回: []byte PackBits压缩条带字节, error 预算或取消错误
func encodeTIFFPackBits(ctx context.Context, pixels []byte, rowBytes int, maxBytes int64) ([]byte, error) {
	if rowBytes <= 0 || len(pixels)%rowBytes != 0 {
		return nil, fmt.Errorf("%w: invalid TIFF PackBits row length", ErrInvalid)
	}
	limit := min(maxBytes, int64(math.MaxUint32))
	out := make([]byte, 0, min(int64(len(pixels)), limit))
	for rowStart := 0; rowStart < len(pixels); rowStart += rowBytes {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		row := pixels[rowStart : rowStart+rowBytes]
		for pos := 0; pos < len(row); {
			run := 1
			for pos+run < len(row) && run < 128 && row[pos+run] == row[pos] {
				run++
			}
			if run >= 3 {
				if int64(len(out))+2 > limit {
					return nil, fmt.Errorf("%w: encoded TIFF PackBits exceeds byte budget", ErrLimit)
				}
				out = append(out, byte(int8(1-run)), row[pos])
				pos += run
				continue
			}
			litStart := pos
			pos += run
			for pos < len(row) && pos-litStart < 128 {
				nextRun := 1
				for pos+nextRun < len(row) && nextRun < 3 && row[pos+nextRun] == row[pos] {
					nextRun++
				}
				if nextRun >= 3 {
					break
				}
				pos++
			}
			litLen := pos - litStart
			if int64(len(out))+1+int64(litLen) > limit {
				return nil, fmt.Errorf("%w: encoded TIFF PackBits exceeds byte budget", ErrLimit)
			}
			out = append(out, byte(litLen-1))
			out = append(out, row[litStart:pos]...)
		}
	}
	return out, nil
}

// encodeTIFFDeflate 按Adobe TIFF Technical Note 3将条带像素编码为标准zlib无损压缩流
// 入参: ctx 取消Context, pixels 原始交织像素字节, maxBytes 输出字节上限
// 返回: []byte zlib压缩条带字节, error 压缩、预算或取消错误
func encodeTIFFDeflate(ctx context.Context, pixels []byte, maxBytes int64) ([]byte, error) {
	limit := min(maxBytes, int64(math.MaxUint32))
	var buf bytes.Buffer
	counted := packageOutput{writer: &buf, context: ctx, limit: limit}
	zw := zlib.NewWriter(&counted)
	const chunkSize = 32 << 10
	for start := 0; start < len(pixels); start += chunkSize {
		if err := checkContext(ctx); err != nil {
			_ = zw.Close()
			return nil, err
		}
		end := min(start+chunkSize, len(pixels))
		if _, err := zw.Write(pixels[start:end]); err != nil {
			_ = zw.Close()
			return nil, err
		}
	}
	if err := zw.Close(); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// encodeGoImageJXR 调用jxrgo编码标准JPEG XR图像并透传像素预算、字节预算、分辨率、质量与ICC配置参数
// 入参: ctx 取消Context, img 源Go图像, cfg 编码配置, maxBytes 字节上限, maxPixels 像素总数上限
// 返回: []byte JPEG XR字节, error 编码、预算或取消错误
func encodeGoImageJXR(ctx context.Context, img image.Image, cfg ImageEncodeOptions, maxBytes int64, maxPixels uint64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if maxPixels == 0 {
		maxPixels = DefaultImageOptions().MaxPixels
	}
	bounds := img.Bounds()
	if bounds.Empty() {
		return nil, fmt.Errorf("%w: empty image bounds", ErrInvalid)
	}
	w, h := bounds.Dx(), bounds.Dy()
	if w > rasterMaxDimension || h > rasterMaxDimension || uint64(w) > maxPixels/uint64(h) {
		return nil, fmt.Errorf("%w: image exceeds MaxImagePixels", ErrLimit)
	}
	opts := &jxrgo.EncodeOptions{MaxOutputBytes: uint64(maxBytes), Limits: jxrgo.Limits{MaxPixels: maxPixels}}
	if cfg.Quality > 0 && cfg.Quality < 100 {
		opts.Lossy = true
		opts.Quality = cfg.Quality
	}
	if cfg.DPIX > 0 && cfg.DPIY > 0 {
		opts.Resolution = &jxrgo.Resolution{X: cfg.DPIX, Y: cfg.DPIY}
	}
	if len(cfg.ICCProfile) != 0 {
		opts.ICCProfile = bytes.Clone(cfg.ICCProfile)
	}
	var out bytes.Buffer
	counted := packageOutput{writer: &out, context: ctx, limit: maxBytes}
	if err := jxrgo.EncodeContext(ctx, &counted, img, opts); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

// encodePNGFromRowsTo 通过逐行扫描回调流式编码标准PNG并写入目标输出流
// 入参: ctx 已规范化取消Context, w 目标输出流, options 图像尺寸、位深、色彩模型、分辨率与ICC配置, maxPixels 像素总数上限, readRow 按零基行号填充原始扫描行的回调
// 返回: error 参数、回调、编码、预算或取消错误
func encodePNGFromRowsTo(ctx context.Context, w io.Writer, options StreamImageRowOptions, maxPixels uint64, readRow func(y int, dst []byte) error) error {
	dpix, dpiy, bitDepth, colorType, rowBytes, err := validateStreamPNGRowOptions(ctx, options, maxPixels)
	if err != nil {
		return err
	}
	return encodePNGFromValidatedRowsTo(ctx, w, options, dpix, dpiy, bitDepth, colorType, rowBytes, readRow)
}

// encodePNGFromValidatedRowsTo 使用已校验PNG规格与扫描行宽流式编码标准PNG并写入目标输出流
// 入参: ctx 已规范化取消Context, w 目标输出流, options 图像尺寸与ICC配置, dpix 水平分辨率, dpiy 垂直分辨率, bitDepth 位深度, colorType PNG颜色类型, rowBytes 单行原始字节数, readRow 按零基行号填充原始扫描行的回调
// 返回: error 回调、编码、预算或取消错误
func encodePNGFromValidatedRowsTo(ctx context.Context, w io.Writer, options StreamImageRowOptions, dpix, dpiy float64, bitDepth int, colorType byte, rowBytes int, readRow func(y int, dst []byte) error) error {
	enc, err := newPNGRowEncoder(ctx, w, options.Width, options.Height, uint8(bitDepth), colorType, dpix, dpiy, options.ICCProfile)
	if err != nil {
		return err
	}
	rowBuf := make([]byte, rowBytes)
	for y := 0; y < options.Height; y++ {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if err := readRow(y, rowBuf); err != nil {
			return err
		}
		if err := enc.writeRow(ctx, rowBuf); err != nil {
			return err
		}
	}
	return enc.close(ctx)
}

// encodeTIFFFromRowsTo 通过逐行扫描回调按多Strip编码Little-Endian Baseline TIFF并直接写入目标输出流
// 无压缩模式恒定单条带内存直接前向写出；压缩模式复用单条带原始缓冲逐条带压缩并暂存压缩条带，全部压缩后释放原始缓冲并在写出时逐条释放压缩条带以降低内存峰值
// 入参: ctx 已规范化取消Context, w 目标输出流, options 图像尺寸、位深、色彩模型、压缩方式、分辨率与ICC配置, maxBytes 输出字节上限, maxPixels 像素总数上限, readRow 按零基行号填充原始像素的回调
// 返回: error 参数、回调、编码、预算或取消错误
func encodeTIFFFromRowsTo(ctx context.Context, w io.Writer, options StreamImageRowOptions, maxBytes int64, maxPixels uint64, readRow func(y int, dst []byte) error) error {
	spec, rowBytes, err := validateStreamTIFFRowOptions(ctx, options, maxPixels)
	if err != nil {
		return err
	}
	return encodeTIFFFromValidatedRowsTo(ctx, w, spec, rowBytes, maxBytes, readRow)
}

// encodeTIFFFromValidatedRowsTo 使用已校验TIFF规格与扫描行宽按多Strip编码Little-Endian Baseline TIFF并直接写入目标输出流
// 入参: ctx 已规范化取消Context, w 目标输出流, spec 已校验TIFF写入规格, rowBytes 单行原始字节数, maxBytes 输出字节上限, readRow 按零基行号填充原始像素的回调
// 返回: error 回调、编码、预算或取消错误
func encodeTIFFFromValidatedRowsTo(ctx context.Context, w io.Writer, spec tiffStripSpec, rowBytes int, maxBytes int64, readRow func(y int, dst []byte) error) error {
	rowsPerStrip, err := tiffRowsPerStrip(rowBytes, spec.height, maxBytes)
	if err != nil {
		return err
	}
	spec.rowsPerStrip = rowsPerStrip
	stripCount := (spec.height + rowsPerStrip - 1) / rowsPerStrip
	rawBuf := make([]byte, rowsPerStrip*rowBytes)
	fillStrip := func(startY, rows int) ([]byte, error) {
		chunk := rawBuf[:rows*rowBytes]
		for row := range rows {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			dst := chunk[row*rowBytes : (row+1)*rowBytes]
			if err := readRow(startY+row, dst); err != nil {
				return nil, err
			}
			if spec.bps == 16 {
				swapUint16Bytes(dst)
			}
		}
		return chunk, nil
	}
	if spec.compression == TIFFCompressionNone {
		if int64(spec.height) > maxBytes/int64(rowBytes) {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		offsets := make([]uint32, stripCount)
		counts := make([]uint32, stripCount)
		cursor := int64(8)
		for i := range stripCount {
			rows := min(rowsPerStrip, spec.height-i*rowsPerStrip)
			n := int64(rows * rowBytes)
			if cursor+n > maxBytes || cursor+n > math.MaxUint32 {
				return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
			}
			offsets[i] = uint32(cursor)
			counts[i] = uint32(n)
			cursor += n
		}
		pad := cursor & 1
		ifdOffset := cursor + pad
		if ifdOffset > math.MaxUint32 {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		ifdBytes, err := encodeTIFFIFD(spec, offsets, counts, uint32(ifdOffset))
		if err != nil {
			return err
		}
		if ifdOffset+int64(len(ifdBytes)) > maxBytes || ifdOffset+int64(len(ifdBytes)) > math.MaxUint32 {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		var header [8]byte
		copy(header[0:2], "II")
		binary.LittleEndian.PutUint16(header[2:4], 42)
		binary.LittleEndian.PutUint32(header[4:8], uint32(ifdOffset))
		if _, err := w.Write(header[:]); err != nil {
			return err
		}
		for i := range stripCount {
			rows := min(rowsPerStrip, spec.height-i*rowsPerStrip)
			chunk, err := fillStrip(i*rowsPerStrip, rows)
			if err != nil {
				return err
			}
			if _, err := w.Write(chunk); err != nil {
				return err
			}
		}
		if pad != 0 {
			if _, err := w.Write([]byte{0}); err != nil {
				return err
			}
		}
		_, err = w.Write(ifdBytes)
		return err
	}
	strips := make([][]byte, 0, stripCount)
	offsets := make([]uint32, stripCount)
	counts := make([]uint32, stripCount)
	cursor := int64(8)
	for i := range stripCount {
		rows := min(rowsPerStrip, spec.height-i*rowsPerStrip)
		chunk, err := fillStrip(i*rowsPerStrip, rows)
		if err != nil {
			return err
		}
		remaining := maxBytes - cursor
		if remaining <= 0 {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		encoded, err := encodeTIFFStripData(ctx, chunk, spec.width, rows, rowBytes, spec.compression, remaining)
		if err != nil {
			return err
		}
		if int64(len(encoded)) > math.MaxUint32 || cursor+int64(len(encoded)) > maxBytes || cursor+int64(len(encoded)) > math.MaxUint32 {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		offsets[i] = uint32(cursor)
		counts[i] = uint32(len(encoded))
		cursor += int64(len(encoded))
		strips = append(strips, encoded)
	}
	rawBuf = nil
	pad := cursor & 1
	ifdOffset := cursor + pad
	if ifdOffset > math.MaxUint32 {
		return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	ifdBytes, err := encodeTIFFIFD(spec, offsets, counts, uint32(ifdOffset))
	if err != nil {
		return err
	}
	if ifdOffset+int64(len(ifdBytes)) > maxBytes || ifdOffset+int64(len(ifdBytes)) > math.MaxUint32 {
		return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	var header [8]byte
	copy(header[0:2], "II")
	binary.LittleEndian.PutUint16(header[2:4], 42)
	binary.LittleEndian.PutUint32(header[4:8], uint32(ifdOffset))
	if _, err := w.Write(header[:]); err != nil {
		return err
	}
	for i := range strips {
		strip := strips[i]
		strips[i] = nil
		if _, err := w.Write(strip); err != nil {
			return err
		}
	}
	if pad != 0 {
		if _, err := w.Write([]byte{0}); err != nil {
			return err
		}
	}
	_, err = w.Write(ifdBytes)
	return err
}

// NewStoryFragmentsBuilder 创建页面故事片段链式构建器，part为空表示由宿主按默认规则分配部件路径
// 入参: part 可选部件URI，非空时校验为合规OPC部件路径
// 返回: *StoryFragmentsBuilder 故事片段构建器
func NewStoryFragmentsBuilder(part string) *StoryFragmentsBuilder {
	b := &StoryFragmentsBuilder{}
	if part != "" {
		normalized, err := opcPartName(part)
		if err != nil {
			b.err = err
			return b
		}
		b.part = normalized
	}
	return b
}

// AddFragment 新建故事片段并将其设为当前活动片段，后续内容追加操作将作用于该片段
// 入参: fragmentType 片段类型（如FragmentContent）, storyName 可选所属故事名称，空串省略, fragmentName 可选片段名称，空串省略且非空时要求storyName非空
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddFragment(fragmentType FragmentType, storyName, fragmentName string) *StoryFragmentsBuilder {
	if b == nil || b.err != nil {
		return b
	}
	switch fragmentType {
	case FragmentContent, FragmentHeader, FragmentFooter:
	default:
		b.err = fmt.Errorf("%w: unsupported StoryFragment type %q", ErrInvalid, fragmentType)
		return b
	}
	if fragmentName != "" && storyName == "" {
		b.err = fmt.Errorf("%w: StoryFragment FragmentName requires StoryName", ErrInvalid)
		return b
	}
	frag := StoryFragment{Type: fragmentType}
	if storyName != "" {
		s := storyName
		frag.StoryName = &s
	}
	if fragmentName != "" {
		f := fragmentName
		frag.FragmentName = &f
	}
	b.fragments = append(b.fragments, frag)
	return b
}

// SetBreaks 设置当前活动故事片段的前后分页断行标志
// 入参: before 是否在片段前断页, after 是否在片段后断页
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) SetBreaks(before, after bool) *StoryFragmentsBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if len(b.fragments) == 0 {
		b.err = fmt.Errorf("%w: no active StoryFragment for SetBreaks", ErrInvalid)
		return b
	}
	b.fragments[len(b.fragments)-1].BreakBefore = before
	b.fragments[len(b.fragments)-1].BreakAfter = after
	return b
}

// AddContent 向当前活动故事片段追加一个或多个语义结构节点，自动深拷贝防止调用方后续修改影响构建器状态
// 入参: nodes 待追加的语义结构节点列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddContent(nodes ...ContentStructure) *StoryFragmentsBuilder {
	if b == nil || b.err != nil {
		return b
	}
	if len(b.fragments) == 0 {
		b.err = fmt.Errorf("%w: no active StoryFragment for AddContent", ErrInvalid)
		return b
	}
	for _, node := range nodes {
		cloned, err := cloneStoryContentStructure(node, 0)
		if err != nil {
			b.err = err
			return b
		}
		b.fragments[len(b.fragments)-1].Content = append(b.fragments[len(b.fragments)-1].Content, cloned)
	}
	return b
}

// AddNamedElement 向当前活动故事片段追加一个引用页面命名元素的NamedElement节点
// 入参: nameRef 页面中对应元素的Name标识
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddNamedElement(nameRef string) *StoryFragmentsBuilder {
	return b.AddContent(NewStoryNamedElement(nameRef))
}

// AddParagraph 向当前活动故事片段追加一个包含若干命名元素引用的段落结构节点
// 入参: nameRefs 段落内按阅读顺序排列的页面元素Name标识列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddParagraph(nameRefs ...string) *StoryFragmentsBuilder {
	return b.AddContent(NewStoryParagraph(nameRefs...))
}

// AddFigure 向当前活动故事片段追加一个包含若干命名元素引用的插图结构节点
// 入参: nameRefs 插图内按阅读顺序排列的页面元素Name标识列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddFigure(nameRefs ...string) *StoryFragmentsBuilder {
	children := make([]ContentStructure, 0, len(nameRefs))
	for _, ref := range nameRefs {
		children = append(children, NewStoryNamedElement(ref))
	}
	return b.AddContent(ContentStructure{Kind: StructureFigure, Children: children})
}

// AddSection 向当前活动故事片段追加一个章节容器节点
// 入参: children 章节内部语义子节点列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddSection(children ...ContentStructure) *StoryFragmentsBuilder {
	return b.AddContent(ContentStructure{Kind: StructureSection, Children: children})
}

// AddList 向当前活动故事片段追加一个列表容器节点
// 入参: items 列表项子节点列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddList(items ...ContentStructure) *StoryFragmentsBuilder {
	return b.AddContent(ContentStructure{Kind: StructureList, Children: items})
}

// AddTable 向当前活动故事片段追加一个表格容器节点，传入直接行节点时自动归入表格行组以满足规范层级要求
// 入参: rows 表格行或行组子节点列表
// 返回: *StoryFragmentsBuilder 构建器本身以支持链式调用
func (b *StoryFragmentsBuilder) AddTable(rows ...ContentStructure) *StoryFragmentsBuilder {
	groups := make([]ContentStructure, 0, len(rows))
	var pending []ContentStructure
	flushRows := func() {
		if len(pending) != 0 {
			groups = append(groups, ContentStructure{Kind: StructureRowGroup, Children: pending})
			pending = nil
		}
	}
	for _, item := range rows {
		if item.Kind == StructureRow {
			pending = append(pending, item)
			continue
		}
		flushRows()
		groups = append(groups, item)
	}
	flushRows()
	return b.AddContent(ContentStructure{Kind: StructureTable, Children: groups})
}

// Err 返回故事片段构建器链式操作期间记录的首个错误
// 返回: error 首个错误，无错为nil
func (b *StoryFragmentsBuilder) Err() error {
	if b == nil {
		return fmt.Errorf("%w: nil StoryFragmentsBuilder", ErrInvalid)
	}
	return b.err
}

// Build 校验已添加片段并生成独立的StoryFragments模型，构建成功后可继续复用或安全传入SetStoryFragments
// 返回: *StoryFragments 独立的页面故事片段模型, error 参数或结构校验错误
func (b *StoryFragmentsBuilder) Build() (*StoryFragments, error) {
	if b == nil {
		return nil, fmt.Errorf("%w: nil StoryFragmentsBuilder", ErrInvalid)
	}
	if b.err != nil {
		return nil, b.err
	}
	if len(b.fragments) == 0 {
		return nil, fmt.Errorf("%w: StoryFragmentsBuilder requires at least one StoryFragment", ErrInvalid)
	}
	out := &StoryFragments{Part: b.part, Fragments: make([]StoryFragment, len(b.fragments))}
	for i, frag := range b.fragments {
		copied := StoryFragment{Type: frag.Type, BreakBefore: frag.BreakBefore, BreakAfter: frag.BreakAfter}
		if frag.StoryName != nil {
			s := *frag.StoryName
			copied.StoryName = &s
		}
		if frag.FragmentName != nil {
			f := *frag.FragmentName
			copied.FragmentName = &f
		}
		if len(frag.Content) != 0 {
			copied.Content = make([]ContentStructure, len(frag.Content))
			for j, node := range frag.Content {
				cloned, err := cloneStoryContentStructure(node, 0)
				if err != nil {
					return nil, err
				}
				copied.Content[j] = cloned
			}
		}
		out.Fragments[i] = copied
	}
	return out, nil
}

// NewStoryNamedElement 构造引用单个页面命名元素的StoryFragments语义叶节点
// 入参: nameRef 页面元素Name标识
// 返回: ContentStructure NamedElement节点
func NewStoryNamedElement(nameRef string) ContentStructure {
	return ContentStructure{Kind: StructureNamedElement, NameReference: nameRef}
}

// NewStoryParagraph 构造包含若干命名元素引用的段落语义节点
// 入参: nameRefs 段落内的页面元素Name标识列表
// 返回: ContentStructure 段落结构节点
func NewStoryParagraph(nameRefs ...string) ContentStructure {
	children := make([]ContentStructure, 0, len(nameRefs))
	for _, ref := range nameRefs {
		children = append(children, NewStoryNamedElement(ref))
	}
	return ContentStructure{Kind: StructureParagraph, Children: children}
}

// NewStoryListItem 构造可选项目符号引用的列表项语义节点
// 入参: marker 可选项目符号页面元素Name标识，空串省略, children 列表项内部子节点列表
// 返回: ContentStructure 列表项结构节点
func NewStoryListItem(marker string, children ...ContentStructure) ContentStructure {
	var ptr *string
	if marker != "" {
		m := marker
		ptr = &m
	}
	return ContentStructure{Kind: StructureListItem, Marker: ptr, Children: slices.Clone(children)}
}

// NewStoryTableRow 构造表格行语义节点
// 入参: cells 单元格子节点列表
// 返回: ContentStructure 表格行结构节点
func NewStoryTableRow(cells ...ContentStructure) ContentStructure {
	return ContentStructure{Kind: StructureRow, Children: slices.Clone(cells)}
}

// NewStoryTableCell 构造带跨行跨列属性的表格单元格语义节点
// 入参: rowSpan 跨行数，非正数按1处理, colSpan 跨列数，非正数按1处理, children 单元格内部子节点列表
// 返回: ContentStructure 表格单元格结构节点
func NewStoryTableCell(rowSpan, colSpan int, children ...ContentStructure) ContentStructure {
	if rowSpan <= 0 {
		rowSpan = 1
	}
	if colSpan <= 0 {
		colSpan = 1
	}
	return ContentStructure{Kind: StructureCell, RowSpan: int32(rowSpan), ColumnSpan: int32(colSpan), Children: slices.Clone(children)}
}

// cloneStoryContentStructure 递归校验并深拷贝故事内容语义节点，防止调用方修改共享切片
// 入参: node 源语义节点, depth 当前递归深度
// 返回: ContentStructure 独立语义节点副本, error 节点种类、空引用或深度超限错误
func cloneStoryContentStructure(node ContentStructure, depth int) (ContentStructure, error) {
	if depth > DefaultLimits().MaxXMLDepth {
		return ContentStructure{}, fmt.Errorf("%w: StoryFragments content depth", ErrLimit)
	}
	switch node.Kind {
	case StructureNamedElement:
		if strings.TrimSpace(node.NameReference) == "" {
			return ContentStructure{}, fmt.Errorf("%w: NamedElement requires NameReference", ErrInvalid)
		}
		if len(node.Children) != 0 {
			return ContentStructure{}, fmt.Errorf("%w: NamedElement cannot contain children", ErrInvalid)
		}
	case StructureSection, StructureParagraph, StructureFigure, StructureList, StructureListItem, StructureTable, StructureRowGroup, StructureRow, StructureCell:
	default:
		return ContentStructure{}, fmt.Errorf("%w: unsupported ContentStructure kind %q", ErrInvalid, node.Kind)
	}
	out := ContentStructure{
		Kind:          node.Kind,
		NameReference: node.NameReference,
		RowSpan:       node.RowSpan,
		ColumnSpan:    node.ColumnSpan,
	}
	if node.Marker != nil {
		m := *node.Marker
		out.Marker = &m
	}
	if len(node.Children) != 0 {
		out.Children = make([]ContentStructure, len(node.Children))
		for i, child := range node.Children {
			cloned, err := cloneStoryContentStructure(child, depth+1)
			if err != nil {
				return ContentStructure{}, err
			}
			out.Children[i] = cloned
		}
	}
	return out, nil
}
