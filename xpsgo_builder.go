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
	// TIFFCompressionDeflate 表示采用Adobe Deflate无损压缩
	TIFFCompressionDeflate
)

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
	default:
		return fmt.Sprintf("TIFFCompression(%d)", c)
	}
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
	if cfg.Format > ImageFormatJXR || cfg.TIFFCompression > TIFFCompressionDeflate || cfg.Quality < 0 || cfg.Quality > 100 {
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
		if targetSpace := encodedGoImageColorSpace(img, format); targetSpace == "" || parsed.space != targetSpace {
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

// encodedGoImageColorSpace 推导源Go图像按选定输出格式编码后的ICC色彩空间标识
// 入参: img 源Go图像, format 已确定的输出格式
// 返回: string 目标编码图像对应的四字节ICC色彩空间签名
func encodedGoImageColorSpace(img image.Image, format ImageEncodeFormat) string {
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
	case ImageFormatTIFF, ImageFormatJXR:
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
	var px, py uint32
	if dpix > 0 && dpiy > 0 {
		pxf := math.Round(dpix / 0.0254)
		pyf := math.Round(dpiy / 0.0254)
		if !(pxf <= 0x7fffffff && pyf <= 0x7fffffff) {
			return nil, fmt.Errorf("%w: PNG DPI exceeds pHYs limit", ErrInvalid)
		}
		px = uint32(pxf)
		py = uint32(pyf)
		if px == 0 {
			px = 1
		}
		if py == 0 {
			py = 1
		}
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
	if len(icc) != 0 {
		var compressed bytes.Buffer
		zw := zlib.NewWriter(&compressed)
		if _, err := zw.Write(icc); err != nil {
			_ = zw.Close()
			return nil, err
		}
		if err := zw.Close(); err != nil {
			return nil, err
		}
		payload := make([]byte, 0, 13+compressed.Len())
		payload = append(payload, []byte("ICC Profile")...)
		payload = append(payload, 0, 0)
		payload = append(payload, compressed.Bytes()...)
		if err := writePNGChunk(&outCounted, "iCCP", payload); err != nil {
			return nil, err
		}
	}
	if dpix > 0 && dpiy > 0 {
		var phys [9]byte
		binary.BigEndian.PutUint32(phys[0:4], px)
		binary.BigEndian.PutUint32(phys[4:8], py)
		phys[8] = 1
		if err := writePNGChunk(&outCounted, "pHYs", phys[:]); err != nil {
			return nil, err
		}
	}
	if _, err := outCounted.Write(data[insertPos:]); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
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

// encodeGoImageTIFF 编码标准Little-Endian Baseline TIFF，支持无压缩、PackBits与Adobe Deflate无损压缩以及灰度、RGB、RGBA、16位、CMYK、DPI和ICC标签
// 入参: ctx 取消Context, img 源Go图像, compression 无损压缩方式, dpix 水平DPI, dpiy 垂直DPI, icc 可选ICC配置字节, maxBytes 字节上限, maxPixels 像素总数上限
// 返回: []byte TIFF字节, error 编码、预算或取消错误
func encodeGoImageTIFF(ctx context.Context, img image.Image, compression TIFFCompression, dpix, dpiy float64, icc []byte, maxBytes int64, maxPixels uint64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
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
	bounds := img.Bounds()
	w, h := bounds.Dx(), bounds.Dy()
	var spp uint16
	var bps uint16
	var photometric uint16
	var extraSample uint16
	var hasExtra bool
	var pixels []byte
	pixelBudget := min(maxBytes, int64(math.MaxUint32))
	if compression != TIFFCompressionNone {
		maxRaw := uint64(math.MaxUint32)
		if maxPixels > 0 && maxPixels < maxRaw/8 {
			maxRaw = maxPixels * 8
		}
		pixelBudget = min(int64(maxRaw), int64(^uint(0)>>1))
	}
	checkPixelBudget := func(bytesPerPixel int64) error {
		if int64(w) <= 0 || int64(h) <= 0 || int64(w) > math.MaxUint32 || int64(h) > math.MaxUint32 || int64(w) > pixelBudget/bytesPerPixel || int64(h) > pixelBudget/(int64(w)*bytesPerPixel) {
			return fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		return nil
	}
	switch typed := img.(type) {
	case *image.Gray:
		spp, bps, photometric = 1, 8, 1
		if err := checkPixelBudget(1); err != nil {
			return nil, err
		}
		pixels = make([]byte, w*h)
		for y := range h {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := typed.PixOffset(bounds.Min.X, bounds.Min.Y+y)
			copy(pixels[y*w:(y+1)*w], typed.Pix[rowOff:rowOff+w])
		}
	case *image.Gray16:
		spp, bps, photometric = 1, 16, 1
		if err := checkPixelBudget(2); err != nil {
			return nil, err
		}
		pixels = make([]byte, w*h*2)
		for y := range h {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			for x := range w {
				v := typed.Gray16At(bounds.Min.X+x, bounds.Min.Y+y).Y
				binary.LittleEndian.PutUint16(pixels[(y*w+x)*2:], v)
			}
		}
	case *image.CMYK:
		spp, bps, photometric = 4, 8, 5
		if err := checkPixelBudget(4); err != nil {
			return nil, err
		}
		pixels = make([]byte, w*h*4)
		for y := range h {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			rowOff := typed.PixOffset(bounds.Min.X, bounds.Min.Y+y)
			copy(pixels[y*w*4:(y+1)*w*4], typed.Pix[rowOff:rowOff+w*4])
		}
	case *image.NRGBA64:
		spp, bps, photometric, extraSample, hasExtra = 4, 16, 2, 2, true
		if err := checkPixelBudget(8); err != nil {
			return nil, err
		}
		pixels = make([]byte, w*h*8)
		for y := range h {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			for x := range w {
				c := typed.NRGBA64At(bounds.Min.X+x, bounds.Min.Y+y)
				off := (y*w + x) * 8
				binary.LittleEndian.PutUint16(pixels[off:], c.R)
				binary.LittleEndian.PutUint16(pixels[off+2:], c.G)
				binary.LittleEndian.PutUint16(pixels[off+4:], c.B)
				binary.LittleEndian.PutUint16(pixels[off+6:], c.A)
			}
		}
	case *image.RGBA64:
		spp, bps, photometric, extraSample, hasExtra = 4, 16, 2, 1, true
		if err := checkPixelBudget(8); err != nil {
			return nil, err
		}
		pixels = make([]byte, w*h*8)
		for y := range h {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			for x := range w {
				c := typed.RGBA64At(bounds.Min.X+x, bounds.Min.Y+y)
				off := (y*w + x) * 8
				binary.LittleEndian.PutUint16(pixels[off:], c.R)
				binary.LittleEndian.PutUint16(pixels[off+2:], c.G)
				binary.LittleEndian.PutUint16(pixels[off+4:], c.B)
				binary.LittleEndian.PutUint16(pixels[off+6:], c.A)
			}
		}
	default:
		if goImageIsOpaque(img) {
			spp, bps, photometric = 3, 8, 2
			if err := checkPixelBudget(3); err != nil {
				return nil, err
			}
			pixels = make([]byte, w*h*3)
			for y := range h {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
				for x := range w {
					c := color.NRGBAModel.Convert(img.At(bounds.Min.X+x, bounds.Min.Y+y)).(color.NRGBA)
					off := (y*w + x) * 3
					pixels[off], pixels[off+1], pixels[off+2] = c.R, c.G, c.B
				}
			}
		} else {
			spp, bps, photometric, extraSample, hasExtra = 4, 8, 2, 2, true
			if err := checkPixelBudget(4); err != nil {
				return nil, err
			}
			pixels = make([]byte, w*h*4)
			for y := range h {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
				for x := range w {
					c := color.NRGBAModel.Convert(img.At(bounds.Min.X+x, bounds.Min.Y+y)).(color.NRGBA)
					off := (y*w + x) * 4
					pixels[off], pixels[off+1], pixels[off+2], pixels[off+3] = c.R, c.G, c.B, c.A
				}
			}
		}
	}
	rowBytes := w * int(spp) * int(bps/8)
	var compressionTag uint32
	var stripData []byte
	var err error
	switch compression {
	case TIFFCompressionNone:
		compressionTag = 1
		stripData = pixels
	case TIFFCompressionPackBits:
		compressionTag = 32773
		stripData, err = encodeTIFFPackBits(ctx, pixels, rowBytes, maxBytes)
	case TIFFCompressionDeflate:
		compressionTag = 8
		stripData, err = encodeTIFFDeflate(ctx, pixels, maxBytes)
	default:
		return nil, fmt.Errorf("%w: unsupported TIFF compression %d", ErrInvalid, compression)
	}
	if err != nil {
		return nil, err
	}
	type tiffEntry struct {
		tag   uint16
		kind  uint16
		count uint32
		value uint32
		extra []byte
	}
	var entries []tiffEntry
	entries = append(entries,
		tiffEntry{tag: 256, kind: 4, count: 1, value: uint32(w)},
		tiffEntry{tag: 257, kind: 4, count: 1, value: uint32(h)},
	)
	if spp == 1 {
		entries = append(entries, tiffEntry{tag: 258, kind: 3, count: 1, value: uint32(bps)})
	} else {
		bpsBytes := make([]byte, int(spp)*2)
		for i := range int(spp) {
			binary.LittleEndian.PutUint16(bpsBytes[i*2:], bps)
		}
		entries = append(entries, tiffEntry{tag: 258, kind: 3, count: uint32(spp), extra: bpsBytes})
	}
	xRat := make([]byte, 8)
	binary.LittleEndian.PutUint32(xRat[0:4], uint32(xNum))
	binary.LittleEndian.PutUint32(xRat[4:8], 1000)
	yRat := make([]byte, 8)
	binary.LittleEndian.PutUint32(yRat[0:4], uint32(yNum))
	binary.LittleEndian.PutUint32(yRat[4:8], 1000)
	entries = append(entries,
		tiffEntry{tag: 259, kind: 3, count: 1, value: compressionTag},
		tiffEntry{tag: 262, kind: 3, count: 1, value: uint32(photometric)},
		tiffEntry{tag: 273, kind: 4, count: 1, value: 8},
		tiffEntry{tag: 277, kind: 3, count: 1, value: uint32(spp)},
		tiffEntry{tag: 278, kind: 4, count: 1, value: uint32(h)},
		tiffEntry{tag: 279, kind: 4, count: 1, value: uint32(len(stripData))},
		tiffEntry{tag: 282, kind: 5, count: 1, extra: xRat},
		tiffEntry{tag: 283, kind: 5, count: 1, extra: yRat},
		tiffEntry{tag: 296, kind: 3, count: 1, value: 2},
	)
	if hasExtra {
		entries = append(entries, tiffEntry{tag: 338, kind: 3, count: 1, value: uint32(extraSample)})
	}
	if len(icc) != 0 {
		if int64(len(icc)) > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
		}
		entries = append(entries, tiffEntry{tag: 34675, kind: 7, count: uint32(len(icc)), extra: icc})
	}
	slices.SortFunc(entries, func(a, b tiffEntry) int { return int(a.tag) - int(b.tag) })
	pixelEnd := int64(8) + int64(len(stripData))
	pad := pixelEnd & 1
	ifdOffset := pixelEnd + pad
	ifdSize := int64(2 + len(entries)*12 + 4)
	extraOffset := ifdOffset + ifdSize
	total := extraOffset
	for _, entry := range entries {
		if len(entry.extra) > 4 {
			total += int64(len(entry.extra) + (len(entry.extra) & 1))
		}
	}
	if total > maxBytes || total > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded TIFF exceeds byte budget", ErrLimit)
	}
	out := make([]byte, int(total))
	copy(out[0:2], "II")
	binary.LittleEndian.PutUint16(out[2:4], 42)
	binary.LittleEndian.PutUint32(out[4:8], uint32(ifdOffset))
	copy(out[8:], stripData)
	binary.LittleEndian.PutUint16(out[int(ifdOffset):], uint16(len(entries)))
	cursor := int(extraOffset)
	for i, entry := range entries {
		pos := int(ifdOffset) + 2 + i*12
		binary.LittleEndian.PutUint16(out[pos:], entry.tag)
		binary.LittleEndian.PutUint16(out[pos+2:], entry.kind)
		binary.LittleEndian.PutUint32(out[pos+4:], entry.count)
		if len(entry.extra) == 0 {
			binary.LittleEndian.PutUint32(out[pos+8:], entry.value)
		} else if len(entry.extra) <= 4 {
			copy(out[pos+8:], entry.extra)
		} else {
			binary.LittleEndian.PutUint32(out[pos+8:], uint32(cursor))
			copy(out[cursor:], entry.extra)
			cursor += len(entry.extra) + (len(entry.extra) & 1)
		}
	}
	return out, nil
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
