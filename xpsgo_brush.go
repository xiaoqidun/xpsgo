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
	"errors"
	"fmt"
	"math"
	"math/big"
	"sort"
	"strings"
)

const (
	// BrushUnknown 表示未知画刷种类
	BrushUnknown BrushKind = iota
	// BrushSolidColor 表示纯色画刷
	BrushSolidColor
	// BrushLinearGradient 表示线性渐变画刷
	BrushLinearGradient
	// BrushRadialGradient 表示径向渐变画刷
	BrushRadialGradient
	// BrushImage 表示图像画刷
	BrushImage
	// BrushVisual 表示视觉画刷
	BrushVisual
)

const (
	// ColorInterpolationSRGB 表示在sRGB空间执行线性插值
	ColorInterpolationSRGB ColorInterpolationMode = iota
	// ColorInterpolationScRGB 表示在scRGB线性空间执行插值
	ColorInterpolationScRGB
)

const (
	// SpreadPad 表示渐变范围外延伸边缘颜色
	SpreadPad SpreadMethod = iota
	// SpreadReflect 表示渐变范围外镜像反射重复
	SpreadReflect
	// SpreadRepeat 表示渐变范围外直接周期重复
	SpreadRepeat
)

const (
	// TileNone 表示不平铺画刷内容
	TileNone TileMode = iota
	// TileRepeat 表示按视口直接重复平铺
	TileRepeat
	// TileFlipX 表示沿水平方向交替翻转平铺
	TileFlipX
	// TileFlipY 表示沿垂直方向交替翻转平铺
	TileFlipY
	// TileFlipXY 表示同时沿水平与垂直方向交替翻转平铺
	TileFlipXY
)

// gradientStopBucketCount 定义渐变色标索引分桶数量
const gradientStopBucketCount = 64

// BrushKind 表示固定布局画刷种类
type BrushKind uint8

// ColorInterpolationMode 表示渐变的颜色插值空间，不作用于alpha
type ColorInterpolationMode uint8

// SpreadMethod 表示初始渐变范围外的延展方式
type SpreadMethod uint8

// TileMode 表示图像及视觉画刷的平铺和交替翻转方式
type TileMode uint8

// GradientStop 保存声明顺序中的渐变停靠点，不排序或裁剪偏移
type GradientStop struct {
	Offset float64
	Color  Color
}

// Brush 保存画刷参数、未预乘颜色及图片或视觉内容引用
// Transform为nil时采用单位矩阵，坐标均使用绝对单位，ImageSource与ImageProfileURI相对于定义部件
// Visual由页面层按定义部件资源类型化，VisualReference为静态资源键
type Brush struct {
	Kind                   BrushKind
	Part                   string
	Opacity                float64
	Transform              *Matrix
	Color                  Color
	Stops                  []GradientStop
	ColorInterpolationMode ColorInterpolationMode
	SpreadMethod           SpreadMethod
	StartPoint             Point
	EndPoint               Point
	Center                 Point
	GradientOrigin         Point
	RadiusX                float64
	RadiusY                float64
	Viewbox                Rect
	Viewport               Rect
	TileMode               TileMode
	ImageSource            string
	ImageProfileURI        string
	Visual                 Element
	VisualReference        string
	visualElement          *xmlElement
}

// gradientSampleStop 保存已转换到插值空间的非预乘颜色及透明度
type gradientSampleStop struct {
	offset float64
	values [4]float64
}

// gradientSampler 保存独立且只读的渐变采样状态
type gradientSampler struct {
	kind       BrushKind
	space      ColorSpace
	spread     SpreadMethod
	opacity    float64
	inverse    Matrix
	stops      []gradientSampleStop
	start      Point
	end        Point
	origin     Point
	center     Point
	radius     Point
	constant   bool
	average    [4]float64
	singular   bool
	forward    Matrix
	linFast    bool
	linScale   float64
	linX       float64
	linY       float64
	linDenom   float64
	radFast    bool
	radDX      float64
	radDY      float64
	radA       float64
	unitStops  bool
	useBuckets bool
	bucketLo   [gradientStopBucketCount]uint16
	bucketHi   [gradientStopBucketCount]uint16
}

// String 返回画刷种类的名称
// 返回: string 画刷种类名称
func (k BrushKind) String() string {
	switch k {
	case BrushUnknown:
		return "Unknown"
	case BrushSolidColor:
		return "SolidColor"
	case BrushLinearGradient:
		return "LinearGradient"
	case BrushRadialGradient:
		return "RadialGradient"
	case BrushImage:
		return "Image"
	case BrushVisual:
		return "Visual"
	default:
		return fmt.Sprintf("BrushKind(%d)", k)
	}
}

// String 返回渐变颜色插值模式的名称
// 返回: string 颜色插值模式名称
func (m ColorInterpolationMode) String() string {
	switch m {
	case ColorInterpolationSRGB:
		return "SRgbLinearInterpolation"
	case ColorInterpolationScRGB:
		return "ScRgbLinearInterpolation"
	default:
		return fmt.Sprintf("ColorInterpolationMode(%d)", m)
	}
}

// String 返回渐变延展方式的名称
// 返回: string 渐变延展方式名称
func (m SpreadMethod) String() string {
	switch m {
	case SpreadPad:
		return "Pad"
	case SpreadReflect:
		return "Reflect"
	case SpreadRepeat:
		return "Repeat"
	default:
		return fmt.Sprintf("SpreadMethod(%d)", m)
	}
}

// String 返回画刷平铺模式的名称
// 返回: string 平铺模式名称
func (m TileMode) String() string {
	switch m {
	case TileNone:
		return "None"
	case TileRepeat:
		return "Tile"
	case TileFlipX:
		return "FlipX"
	case TileFlipY:
		return "FlipY"
	case TileFlipXY:
		return "FlipXY"
	default:
		return fmt.Sprintf("TileMode(%d)", m)
	}
}

// parseBrushElement 解析画刷元素属性、变换与停靠点，不加载外部资源或展开视觉子树
// 入参: node 画刷节点, resolveMatrix 矩阵资源解析回调, resource 是否为资源字典直接成员
// 返回: *Brush 画刷参数, error 结构或属性错误
func parseBrushElement(node *xmlElement, resolveMatrix func(string) (Matrix, error), resource bool) (*Brush, error) {
	if node == nil || node.Name.Space != xpsNamespace && node.Name.Space != openXPSNamespace {
		return nil, fmt.Errorf("%w: invalid brush namespace", ErrInvalid)
	}
	ns, name := node.Name.Space, node.Name.Local
	b := &Brush{Opacity: 1}
	allowed := []string{"Opacity"}
	switch name {
	case "SolidColorBrush":
		b.Kind = BrushSolidColor
		allowed = append(allowed, "Color")
	case "LinearGradientBrush", "RadialGradientBrush":
		allowed = append(allowed, "Transform", "ColorInterpolationMode", "SpreadMethod", "MappingMode")
		if name == "LinearGradientBrush" {
			b.Kind = BrushLinearGradient
			allowed = append(allowed, "StartPoint", "EndPoint")
		} else {
			b.Kind = BrushRadialGradient
			allowed = append(allowed, "Center", "GradientOrigin", "RadiusX", "RadiusY")
		}
	case "ImageBrush", "VisualBrush":
		allowed = append(allowed, "Transform", "Viewbox", "Viewport", "ViewboxUnits", "ViewportUnits", "TileMode")
		if name == "ImageBrush" {
			b.Kind = BrushImage
			allowed = append(allowed, "ImageSource")
		} else {
			b.Kind = BrushVisual
			allowed = append(allowed, "Visual")
		}
	default:
		return nil, fmt.Errorf("%w: unknown brush %q", ErrInvalid, name)
	}
	a, err := geometryXMLAttributes(node, ns, name, resource, allowed...)
	if err != nil {
		return nil, err
	}
	if text, ok := a["Opacity"]; ok {
		b.Opacity, err = xmlNumber(text)
		if err != nil || !geometryFinite(b.Opacity) || b.Opacity < 0 || b.Opacity > 1 {
			return nil, fmt.Errorf("%w: invalid brush Opacity %q", ErrInvalid, text)
		}
	}
	if b.Kind == BrushSolidColor {
		if len(node.Children) != 0 {
			return nil, fmt.Errorf("%w: SolidColorBrush cannot contain children", ErrInvalid)
		}
		text, err := geometryXMLRequired(a, "Color")
		if err != nil {
			return nil, err
		}
		b.Color, err = parseBrushColor(text, ns)
		if err != nil {
			return nil, err
		}
		return b, nil
	}
	transform, transformAttribute := a["Transform"]
	hasTransform := transformAttribute
	visual, hasVisual := a["Visual"]
	if hasVisual {
		key, reference, err := parseResourceReference(visual)
		if err != nil {
			return nil, err
		}
		if !reference {
			return nil, fmt.Errorf("%w: Visual requires a static resource reference", ErrInvalid)
		}
		b.VisualReference = key
	}
	hasStops := false
	for i, child := range node.Children {
		if child == nil || child.Name.Space != ns {
			return nil, fmt.Errorf("%w: invalid brush child namespace", ErrInvalid)
		}
		switch child.Name.Local {
		case name + ".Transform":
			if i != 0 || hasTransform {
				return nil, fmt.Errorf("%w: brush Transform must occur once before content", ErrInvalid)
			}
			m, err := brushTransformElement(child, ns)
			if err != nil {
				return nil, err
			}
			b.Transform = &m
			hasTransform = true
		case name + ".GradientStops":
			if b.Kind != BrushLinearGradient && b.Kind != BrushRadialGradient || hasStops {
				return nil, fmt.Errorf("%w: unexpected or duplicate GradientStops", ErrInvalid)
			}
			b.Stops, err = brushGradientStops(child, ns)
			if err != nil {
				return nil, err
			}
			hasStops = true
		case "VisualBrush.Visual":
			if b.Kind != BrushVisual || hasVisual {
				return nil, fmt.Errorf("%w: unexpected or duplicate brush Visual", ErrInvalid)
			}
			if _, err := geometryXMLAttributes(child, ns, "VisualBrush.Visual", false); err != nil {
				return nil, err
			}
			if len(child.Children) != 1 || child.Children[0] == nil {
				return nil, fmt.Errorf("%w: VisualBrush.Visual requires one visual", ErrInvalid)
			}
			v := child.Children[0]
			if v.Name.Space != ns || v.Name.Local != "Canvas" && v.Name.Local != "Path" && v.Name.Local != "Glyphs" {
				return nil, fmt.Errorf("%w: invalid VisualBrush visual element", ErrInvalid)
			}
			b.visualElement = v
			hasVisual = true
		default:
			return nil, fmt.Errorf("%w: unexpected brush child %q", ErrInvalid, child.Name.Local)
		}
	}
	if transformAttribute {
		m, err := geometryXMLTransform(transform, resolveMatrix)
		if err != nil {
			return nil, err
		}
		b.Transform = &m
	}
	if b.Kind == BrushLinearGradient || b.Kind == BrushRadialGradient {
		if !hasStops {
			return nil, fmt.Errorf("%w: gradient brush requires GradientStops", ErrInvalid)
		}
		if err := brushGradientAttributes(b, a); err != nil {
			return nil, err
		}
	} else {
		if err := brushTileAttributes(b, a); err != nil {
			return nil, err
		}
		if b.Kind == BrushImage {
			text, err := geometryXMLRequired(a, "ImageSource")
			if err != nil {
				return nil, err
			}
			b.ImageSource, b.ImageProfileURI, err = parseBrushImageSource(text)
			if err != nil {
				return nil, err
			}
		}
	}
	return b, nil
}

// brushTransformElement 解析画刷的内联MatrixTransform属性元素
// 入参: node Transform属性元素, ns 命名空间
// 返回: Matrix 局部变换, error 结构或矩阵错误
func brushTransformElement(node *xmlElement, ns string) (Matrix, error) {
	if _, err := geometryXMLAttributes(node, ns, node.Name.Local, false); err != nil {
		return Matrix{}, err
	}
	if len(node.Children) != 1 {
		return Matrix{}, fmt.Errorf("%w: brush Transform requires one MatrixTransform", ErrInvalid)
	}
	matrix := node.Children[0]
	a, err := geometryXMLAttributes(matrix, ns, "MatrixTransform", false, "Matrix")
	if err != nil {
		return Matrix{}, err
	}
	if len(matrix.Children) != 0 {
		return Matrix{}, fmt.Errorf("%w: MatrixTransform cannot contain children", ErrInvalid)
	}
	text, err := geometryXMLRequired(a, "Matrix")
	if err != nil {
		return Matrix{}, err
	}
	return ParseMatrix(text)
}

// brushGradientStops 解析至少两个停靠点，保留原始顺序、重复偏移及范围外偏移
// 入参: node 停靠点容器, ns 命名空间
// 返回: []GradientStop 停靠点, error 结构或颜色错误
func brushGradientStops(node *xmlElement, ns string) ([]GradientStop, error) {
	if _, err := geometryXMLAttributes(node, ns, node.Name.Local, false); err != nil {
		return nil, err
	}
	if len(node.Children) < 2 {
		return nil, fmt.Errorf("%w: gradient requires at least two stops", ErrInvalid)
	}
	stops := make([]GradientStop, 0, len(node.Children))
	for _, child := range node.Children {
		a, err := geometryXMLAttributes(child, ns, "GradientStop", false, "Color", "Offset")
		if err != nil {
			return nil, err
		}
		if len(child.Children) != 0 {
			return nil, fmt.Errorf("%w: GradientStop cannot contain children", ErrInvalid)
		}
		text, err := geometryXMLRequired(a, "Color")
		if err != nil {
			return nil, err
		}
		color, err := parseBrushColor(text, ns)
		if err != nil {
			return nil, err
		}
		text, err = geometryXMLRequired(a, "Offset")
		if err != nil {
			return nil, err
		}
		offset, err := xmlNumber(text)
		if err != nil || !geometryFinite(offset) {
			return nil, fmt.Errorf("%w: invalid gradient Offset %q", ErrInvalid, text)
		}
		stops = append(stops, GradientStop{Offset: offset, Color: color})
	}
	return stops, nil
}

// brushGradientAttributes 校验渐变画刷的必需坐标及可选模式
// 入参: b 待填充画刷, a 已校验的属性集合
// 返回: error 属性错误
func brushGradientAttributes(b *Brush, a map[string]string) error {
	if a["MappingMode"] != "Absolute" {
		return fmt.Errorf("%w: MappingMode must be explicitly Absolute", ErrInvalid)
	}
	if value, ok := a["ColorInterpolationMode"]; ok {
		switch value {
		case "SRgbLinearInterpolation":
		case "ScRgbLinearInterpolation":
			b.ColorInterpolationMode = ColorInterpolationScRGB
		default:
			return fmt.Errorf("%w: invalid ColorInterpolationMode %q", ErrInvalid, value)
		}
	}
	if value, ok := a["SpreadMethod"]; ok {
		switch value {
		case "Pad":
		case "Reflect":
			b.SpreadMethod = SpreadReflect
		case "Repeat":
			b.SpreadMethod = SpreadRepeat
		default:
			return fmt.Errorf("%w: invalid SpreadMethod %q", ErrInvalid, value)
		}
	}
	points := map[string]*Point{"StartPoint": &b.StartPoint, "EndPoint": &b.EndPoint}
	if b.Kind == BrushRadialGradient {
		points = map[string]*Point{"Center": &b.Center, "GradientOrigin": &b.GradientOrigin}
		for _, radius := range []struct {
			name string
			out  *float64
		}{{"RadiusX", &b.RadiusX}, {"RadiusY", &b.RadiusY}} {
			text, err := geometryXMLRequired(a, radius.name)
			if err != nil {
				return err
			}
			*radius.out, err = xmlNumber(text)
			if err != nil || !geometryFinite(*radius.out) || *radius.out < 0 {
				return fmt.Errorf("%w: invalid %s %q", ErrInvalid, radius.name, text)
			}
		}
	}
	for name, out := range points {
		text, err := geometryXMLRequired(a, name)
		if err != nil {
			return err
		}
		points, err := geometryXMLPoints(text, true, false)
		if err != nil {
			return err
		}
		*out = points[0]
	}
	return nil
}

// brushTileAttributes 校验图像和视觉画刷的矩形、单位与平铺模式
// 入参: b 待填充画刷, a 已校验的属性集合
// 返回: error 属性错误
func brushTileAttributes(b *Brush, a map[string]string) error {
	if a["ViewboxUnits"] != "Absolute" || a["ViewportUnits"] != "Absolute" {
		return fmt.Errorf("%w: ViewboxUnits and ViewportUnits must be explicitly Absolute", ErrInvalid)
	}
	for _, box := range []struct {
		name string
		out  *Rect
	}{{"Viewbox", &b.Viewbox}, {"Viewport", &b.Viewport}} {
		text, err := geometryXMLRequired(a, box.name)
		if err != nil {
			return err
		}
		*box.out, err = brushViewbox(text)
		if err != nil {
			return fmt.Errorf("%s: %w", box.name, err)
		}
	}
	if value, ok := a["TileMode"]; ok {
		switch value {
		case "None":
		case "Tile":
			b.TileMode = TileRepeat
		case "FlipX":
			b.TileMode = TileFlipX
		case "FlipY":
			b.TileMode = TileFlipY
		case "FlipXY":
			b.TileMode = TileFlipXY
		default:
			return fmt.Errorf("%w: invalid TileMode %q", ErrInvalid, value)
		}
	}
	return nil
}

// brushViewbox 解析ST_ViewBox，允许零宽高但禁止尺寸的负号
// 入参: text 四个逗号分隔的实数
// 返回: Rect 矩形, error 词法错误
func brushViewbox(text string) (Rect, error) {
	p := geometryScanner{text: text}
	p.space()
	var v [4]float64
	for i := range v {
		if i != 0 {
			p.separator(',')
		}
		if i >= 2 && p.peek() == '-' {
			p.fail("ST_ViewBox dimensions cannot have a negative sign")
		}
		v[i] = p.number()
	}
	p.space()
	if p.pos != len(text) {
		p.fail("unexpected trailing Viewbox data")
	}
	if p.err != nil {
		return Rect{}, p.err
	}
	return Rect{X: v[0], Y: v[1], Width: v[2], Height: v[3]}, nil
}

// parseBrushImageSource 解析图片引用或ColorConvertedBitmap表达式，保留定义部件相对URI
// 入参: text ImageSource属性原文
// 返回: string 图片引用, string 可选ICC引用, error 引用词法错误
func parseBrushImageSource(text string) (string, string, error) {
	trimmed := strings.TrimLeft(text, " \t\r\n")
	if !strings.HasPrefix(trimmed, "{") {
		value := strings.Join(strings.FieldsFunc(text, func(r rune) bool { return r == ' ' || r == '\t' || r == '\r' || r == '\n' }), " ")
		if err := brushPartReference(value); err != nil {
			return "", "", err
		}
		return value, "", nil
	}
	const prefix = "{ColorConvertedBitmap"
	if !strings.HasPrefix(trimmed, prefix) || len(trimmed) == len(prefix) || !xmlSpace(trimmed[len(prefix)]) {
		return "", "", fmt.Errorf("%w: invalid ColorConvertedBitmap expression", ErrInvalid)
	}
	body, suffix, ok := strings.Cut(trimmed[len(prefix):], "}")
	if !ok || !xmlWhitespace(suffix) || body == "" || xmlSpace(body[len(body)-1]) {
		return "", "", fmt.Errorf("%w: invalid ColorConvertedBitmap terminator", ErrInvalid)
	}
	values := strings.FieldsFunc(body, func(r rune) bool { return r == ' ' || r == '\t' || r == '\r' || r == '\n' })
	if len(values) != 2 {
		return "", "", fmt.Errorf("%w: ColorConvertedBitmap requires image and profile references", ErrInvalid)
	}
	for _, value := range values {
		if err := brushPartReference(value); err != nil {
			return "", "", err
		}
	}
	return values[0], values[1], nil
}

// brushTileFilter 识别设备空间内不足一个像素的图块轴，不受抗锯齿采样倍率影响
// 入参: viewport 初始图块, transform 画刷到设备的变换
// 返回: bool 是否平均横轴, bool 是否平均纵轴, error 数值范围错误
func brushTileFilter(viewport Rect, transform Matrix) (bool, bool, error) {
	x := math.Hypot(transform.A, transform.B) * viewport.Width
	y := math.Hypot(transform.C, transform.D) * viewport.Height
	if !geometryFinite(x, y) || x < 0 || y < 0 {
		return false, false, fmt.Errorf("%w: brush tile device extent", ErrLimit)
	}
	return x < 1, y < 1, nil
}

// newGradientSampler 预处理渐变画刷并构造独立采样器，重合线性轴取归一化区间预乘均色
// 入参: brush 已解析的渐变画刷, transform 元素及祖先的有效设备变换
// 返回: *gradientSampler 独立采样器, error 输入、能力或数值范围错误
func newGradientSampler(brush *Brush, transform Matrix) (*gradientSampler, error) {
	if brush == nil || brush.Kind != BrushLinearGradient && brush.Kind != BrushRadialGradient {
		return nil, fmt.Errorf("%w: expected gradient brush", ErrInvalid)
	}
	if brush.ColorInterpolationMode > ColorInterpolationScRGB || brush.SpreadMethod > SpreadRepeat || !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 || len(brush.Stops) < 2 {
		return nil, fmt.Errorf("%w: invalid gradient attributes or stops", ErrInvalid)
	}
	if !geometryFillMatrixFinite(transform) {
		return nil, fmt.Errorf("%w: non-finite gradient device transform", ErrInvalid)
	}
	if brush.Transform != nil {
		m := *brush.Transform
		if !geometryFillMatrixFinite(m) {
			return nil, fmt.Errorf("%w: non-finite gradient brush transform", ErrInvalid)
		}
		transform = transform.Mul(m)
		if !geometryFillMatrixFinite(transform) {
			return nil, fmt.Errorf("%w: gradient transform composition overflow", ErrLimit)
		}
	}
	s := &gradientSampler{kind: brush.Kind, space: ColorSRGB, spread: brush.SpreadMethod, opacity: brush.Opacity, inverse: IdentityMatrix(), start: brush.StartPoint, end: brush.EndPoint, origin: brush.GradientOrigin, center: brush.Center, radius: Point{brush.RadiusX, brush.RadiusY}}
	if brush.ColorInterpolationMode == ColorInterpolationScRGB {
		s.space = ColorScRGB
	}
	if s.kind == BrushLinearGradient {
		if !geometryFinite(s.start.X, s.start.Y, s.end.X, s.end.Y) {
			return nil, fmt.Errorf("%w: non-finite linear gradient", ErrInvalid)
		}
		s.start, s.end = transform.Transform(s.start), transform.Transform(s.end)
		if !geometryFinite(s.start.X, s.start.Y, s.end.X, s.end.Y) {
			return nil, fmt.Errorf("%w: transformed gradient endpoint overflow", ErrLimit)
		}
		if s.start == s.end {
			s.constant = true
		} else {
			dx, dy := s.end.X-s.start.X, s.end.Y-s.start.Y
			scale := max(math.Abs(dx), math.Abs(dy))
			if scale > 0 && geometryFinite(dx, dy, scale) {
				x, y := dx/scale, dy/scale
				denom := x*x + y*y
				if denom > 0 && geometryFinite(x, y, denom) {
					s.linFast, s.linScale, s.linX, s.linY, s.linDenom = true, scale, x, y, denom
				}
			}
		}
	} else if !geometryFinite(s.origin.X, s.origin.Y, s.center.X, s.center.Y, s.radius.X, s.radius.Y) || s.radius.X < 0 || s.radius.Y < 0 {
		return nil, fmt.Errorf("%w: invalid radial gradient", ErrInvalid)
	}
	if s.kind == BrushRadialGradient {
		inverse, err := transform.Inverse()
		if errors.Is(err, ErrInvalid) {
			s.singular, s.forward = true, transform
		} else if err != nil {
			return nil, err
		} else {
			s.inverse = inverse
		}
		if !s.singular && s.radius.X != 0 && s.radius.Y != 0 {
			dx, dy := (s.center.X-s.origin.X)/s.radius.X, (s.center.Y-s.origin.Y)/s.radius.Y
			a := dx*dx + dy*dy - 1
			if geometryFinite(dx, dy, a) && math.Abs(a) >= 1e-12 {
				s.radFast, s.radDX, s.radDY, s.radA = true, dx, dy, a
			}
		}
	}
	s.stops = make([]gradientSampleStop, len(brush.Stops))
	for i, stop := range brush.Stops {
		if !geometryFinite(stop.Offset) {
			return nil, fmt.Errorf("%w: non-finite gradient stop", ErrInvalid)
		}
		values, err := gradientColorValues(stop.Color, s.space)
		if err != nil {
			return nil, fmt.Errorf("gradient stop %d: %w", i, err)
		}
		s.stops[i] = gradientSampleStop{stop.Offset, values}
	}
	sort.SliceStable(s.stops, func(i, j int) bool { return s.stops[i].offset < s.stops[j].offset })
	stops := s.stops[:0]
	for i := 0; i < len(s.stops); {
		j := i + 1
		for j < len(s.stops) && s.stops[j].offset == s.stops[i].offset {
			j++
		}
		stops = append(stops, s.stops[i])
		if j-i > 1 {
			stops = append(stops, s.stops[j-1])
		}
		i = j
	}
	s.stops = stops
	s.boundary(0)
	s.boundary(1)
	if len(s.stops) == 2 && s.stops[0].offset == 0 && s.stops[1].offset == 1 {
		s.unitStops = true
	} else if len(s.stops) > 4 && len(s.stops) < 65535 {
		s.buildStopBuckets()
	}
	if s.constant {
		s.average = gradientAverage(s.stops)
	}
	return s, nil
}

// buildStopBuckets 为单位区间停靠点预构建精确索引桶，保持与二分搜索逐比特一致的查找结果
func (s *gradientSampler) buildStopBuckets() {
	n := len(s.stops)
	for b := range gradientStopBucketCount {
		loEdge := float64(b) / gradientStopBucketCount
		hiEdge := float64(b+1) / gradientStopBucketCount
		lo := 0
		hi := n
		for lo < hi {
			mid := int(uint(lo+hi) >> 1)
			if s.stops[mid].offset >= loEdge {
				hi = mid
			} else {
				lo = mid + 1
			}
		}
		s.bucketLo[b] = uint16(lo)
		hi = n
		for lo < hi {
			mid := int(uint(lo+hi) >> 1)
			if s.stops[mid].offset > hiEdge {
				hi = mid
			} else {
				lo = mid + 1
			}
		}
		s.bucketHi[b] = uint16(lo)
	}
	s.useBuckets = true
}

// gradientAverage 精确积分单位区间内的预乘渐变颜色，再还原非预乘分量，避免透明停靠点染色和中间溢出
// 入参: stops 已排序、补齐零与一端点的停靠点
// 返回: [4]float64 单位区间均色及平均透明度
func gradientAverage(stops []gradientSampleStop) [4]float64 {
	var sums [4]big.Rat
	for i := 1; i < len(stops); i++ {
		lo, hi := stops[i-1], stops[i]
		if lo.offset < 0 || hi.offset > 1 || lo.offset == hi.offset {
			continue
		}
		width := gradientDifference(hi.offset, lo.offset)
		a, b := new(big.Rat).SetFloat64(lo.values[3]), new(big.Rat).SetFloat64(hi.values[3])
		alpha := new(big.Rat).Mul(width, new(big.Rat).Add(a, b))
		sums[3].Add(&sums[3], alpha.Quo(alpha, big.NewRat(2, 1)))
		left := new(big.Rat).Add(new(big.Rat).Mul(a, big.NewRat(2, 1)), b)
		right := new(big.Rat).Add(a, new(big.Rat).Mul(b, big.NewRat(2, 1)))
		weight := new(big.Rat).Quo(width, big.NewRat(6, 1))
		for channel := range 3 {
			l := new(big.Rat).Mul(new(big.Rat).SetFloat64(lo.values[channel]), left)
			r := new(big.Rat).Mul(new(big.Rat).SetFloat64(hi.values[channel]), right)
			sums[channel].Add(&sums[channel], l.Mul(l.Add(l, r), weight))
		}
	}
	var values [4]float64
	if sums[3].Sign() == 0 {
		return values
	}
	values[3], _ = sums[3].Float64()
	for channel := range 3 {
		values[channel], _ = new(big.Rat).Quo(&sums[channel], &sums[3]).Float64()
	}
	return values
}

// gradientColorValues 转换非预乘RGB分量，向sRGB转换时裁剪色域，scRGB保留扩展分量
// 入参: color 源颜色, space 插值空间
// 返回: [4]float64 RGB及alpha, error 颜色数据或未实现ICC转换错误
func gradientColorValues(color Color, space ColorSpace) ([4]float64, error) {
	if !geometryFinite(color.Alpha) || color.Alpha < 0 || color.Alpha > 1 {
		return [4]float64{}, fmt.Errorf("%w: invalid gradient alpha", ErrInvalid)
	}
	alpha := color.Alpha
	color.Alpha = 1
	target := renderSRGB
	if space == ColorScRGB {
		target = renderScRGB
	}
	converted, err := renderColorFromColor(color, target)
	if err != nil {
		return [4]float64{}, err
	}
	return [4]float64{converted.r, converted.g, converted.b, alpha}, nil
}

// boundary 仅在缺少指定端点时插值补点并删除该侧范围外停靠点
// 入参: offset 端点偏移零或一
func (s *gradientSampler) boundary(offset float64) {
	i := sort.Search(len(s.stops), func(i int) bool { return s.stops[i].offset >= offset })
	if i < len(s.stops) && s.stops[i].offset == offset {
		return
	}
	var values [4]float64
	switch {
	case i == 0:
		values = s.stops[0].values
	case i == len(s.stops):
		values = s.stops[i-1].values
	default:
		lo, hi := s.stops[i-1], s.stops[i]
		values = gradientBlend(lo.values, hi.values, gradientFraction(offset, lo.offset, hi.offset))
	}
	stop := gradientSampleStop{offset, values}
	if offset == 0 {
		s.stops = append([]gradientSampleStop{stop}, s.stops[i:]...)
	} else {
		s.stops = append(s.stops[:i], stop)
	}
}

// gradientFraction 计算有序区间内的比例，避免相反符号端点相减溢出
// 入参: value 区间内数值, lo 左端点, hi 右端点
// 返回: float64 单位区间比例
func gradientFraction(value, lo, hi float64) float64 {
	span := hi - lo
	if math.IsInf(span, 0) {
		return (value/2 - lo/2) / (hi/2 - lo/2)
	}
	return (value - lo) / span
}

// gradientBlend 分别线性插值非预乘颜色和alpha，避免有限扩展分量相减溢出
// 入参: lo 左端颜色, hi 右端颜色, t 单位区间比例
// 返回: [4]float64 插值颜色及alpha
func gradientBlend(lo, hi [4]float64, t float64) [4]float64 {
	if t <= 0 {
		return lo
	}
	if t >= 1 {
		return hi
	}
	var result [4]float64
	for i := range result {
		if math.Signbit(lo[i]) != math.Signbit(hi[i]) {
			result[i] = (1-t)*lo[i] + t*hi[i]
		} else {
			result[i] = lo[i] + t*(hi[i]-lo[i])
		}
	}
	return result
}

// sampleValues 在设备空间零分配求值并返回插值空间内的非预乘RGB及停靠点alpha
// 入参: point 与构造时有效设备变换对应的设备采样点
// 返回: [4]float64 非预乘RGB及停靠点alpha, error 非有限输入或计算范围错误
func (s *gradientSampler) sampleValues(point Point) ([4]float64, error) {
	if s == nil || !geometryFinite(point.X, point.Y) {
		return [4]float64{}, fmt.Errorf("%w: invalid gradient sample", ErrInvalid)
	}
	if s.constant {
		return s.average, nil
	}
	var t float64
	var err error
	if s.kind == BrushLinearGradient {
		resolved := false
		if s.linFast {
			qx, qy := point.X-s.start.X, point.Y-s.start.Y
			if geometryFinite(qx, qy) {
				if cand := (qx/s.linScale*s.linX + qy/s.linScale*s.linY) / s.linDenom; geometryFinite(cand) {
					t, resolved = cand, true
				}
			}
		}
		if !resolved {
			t, err = gradientLinearParameter(point, s.start, s.end)
		}
	} else {
		var inside bool
		if s.singular {
			t, inside, err = s.radialSingularParameter(point)
		} else {
			p := s.inverse.Transform(point)
			if !geometryFinite(p.X, p.Y) {
				return [4]float64{}, fmt.Errorf("%w: gradient inverse coordinate overflow", ErrLimit)
			}
			t, inside, err = s.radialParameter(p)
		}
		if err == nil && (!inside || s.spread == SpreadPad && t > 1) {
			if s.spread == SpreadReflect {
				return s.at(0), nil
			}
			return s.at(1), nil
		}
	}
	if err != nil {
		return [4]float64{}, err
	}
	switch s.spread {
	case SpreadRepeat:
		t -= math.Floor(t)
	case SpreadReflect:
		t = math.Mod(t, 2)
		if t < 0 {
			t += 2
		}
		if t > 1 {
			t = 2 - t
		}
	}
	return s.at(t), nil
}

// sample 在设备空间取点，线性渐变向设备轴投影，径向渐变按变换后的椭圆族求值
// 入参: point 与构造时有效设备变换对应的设备采样点
// 返回: Color RGB及已乘画刷Opacity的alpha, error 非有限输入或计算范围错误
func (s *gradientSampler) sample(point Point) (Color, error) {
	values, err := s.sampleValues(point)
	if err != nil {
		return Color{}, err
	}
	return s.color(values), nil
}

// sampleRenderColor 在设备空间零分配求值并直接转换为目标合成空间的预乘颜色
// 入参: point 与构造时有效设备变换对应的设备采样点, target 目标合成空间
// 返回: renderColor 预乘颜色, error 非有限输入、计算范围或颜色空间错误
func (s *gradientSampler) sampleRenderColor(point Point, target renderColorSpace) (renderColor, error) {
	values, err := s.sampleValues(point)
	if err != nil {
		return renderColor{}, err
	}
	return imageRGBToRenderColor(values[0], values[1], values[2], values[3]*s.opacity, s.space, target)
}

// at 根据已排序停靠点求值，重合停靠点采用右连续规则，Pad外部保留首末颜色
// 入参: t 已应用延展规则的偏移
// 返回: [4]float64 非预乘RGB及alpha
func (s *gradientSampler) at(t float64) [4]float64 {
	if t < 0 {
		return s.stops[0].values
	}
	if t > 1 {
		return s.stops[len(s.stops)-1].values
	}
	if s.unitStops {
		if t == 0 {
			return s.stops[0].values
		}
		if t == 1 {
			return s.stops[1].values
		}
		return gradientBlend(s.stops[0].values, s.stops[1].values, t)
	}
	lo, hi := 0, len(s.stops)
	if s.useBuckets {
		bucket := int(t * gradientStopBucketCount)
		if bucket >= gradientStopBucketCount {
			bucket = gradientStopBucketCount - 1
		}
		lo, hi = int(s.bucketLo[bucket]), int(s.bucketHi[bucket])
	}
	i := lo
	if hi-lo <= 8 {
		for i < hi && s.stops[i].offset <= t {
			i++
		}
	} else {
		for lo < hi {
			mid := int(uint(lo+hi) >> 1)
			if s.stops[mid].offset > t {
				hi = mid
			} else {
				lo = mid + 1
			}
		}
		i = lo
	}
	if i == 0 {
		return s.stops[0].values
	}
	if i == len(s.stops) {
		return s.stops[i-1].values
	}
	low, high := s.stops[i-1], s.stops[i]
	return gradientBlend(low.values, high.values, gradientFraction(t, low.offset, high.offset))
}

// color 创建不与采样器共享分量切片的输出颜色
// 入参: values 非预乘RGB及停靠点alpha
// 返回: Color 插值空间颜色，不带原词法或ICC引用
func (s *gradientSampler) color(values [4]float64) Color {
	return Color{Space: s.space, Alpha: values[3] * s.opacity, Components: []float64{values[0], values[1], values[2]}}
}

// gradientLinearParameter 计算采样点在设备渐变轴上的正交投影，极端量级使用精确有理数
// 入参: p 设备采样点, start 设备轴起点, end 设备轴终点
// 返回: float64 渐变参数, error 参数超出有限范围错误
func gradientLinearParameter(p, start, end Point) (float64, error) {
	dx, dy, qx, qy := end.X-start.X, end.Y-start.Y, p.X-start.X, p.Y-start.Y
	scale := max(math.Abs(dx), math.Abs(dy))
	if scale > 0 && geometryFinite(dx, dy, qx, qy, scale) {
		x, y := dx/scale, dy/scale
		t := (qx/scale*x + qy/scale*y) / (x*x + y*y)
		if geometryFinite(t) {
			return t, nil
		}
	}
	x, y := gradientDifference(end.X, start.X), gradientDifference(end.Y, start.Y)
	qxExact, qyExact := gradientDifference(p.X, start.X), gradientDifference(p.Y, start.Y)
	n := new(big.Rat).Add(new(big.Rat).Mul(qxExact, x), new(big.Rat).Mul(qyExact, y))
	d := new(big.Rat).Add(new(big.Rat).Mul(x, x), new(big.Rat).Mul(y, y))
	t, _ := new(big.Rat).Quo(n, d).Float64()
	if !geometryFinite(t) {
		return 0, fmt.Errorf("%w: linear gradient parameter overflow", ErrLimit)
	}
	return t, nil
}

// radialParameter 求包含采样点的最小非负插值椭圆，不将外部原点移入椭圆
// 入参: p 画刷局部采样点
// 返回: float64 椭圆参数, bool 是否位于插值椭圆并集, error 数值范围错误
func (s *gradientSampler) radialParameter(p Point) (float64, bool, error) {
	if p == s.origin {
		return 0, true, nil
	}
	if !s.radFast {
		return s.radialExact(p)
	}
	dx, dy, a := s.radDX, s.radDY, s.radA
	qx, qy := (p.X-s.origin.X)/s.radius.X, (p.Y-s.origin.Y)/s.radius.Y
	b, c := qx*dx+qy*dy, qx*qx+qy*qy
	disc := b*b - a*c
	if !geometryFinite(b, c, disc) || c < 1e-200 || math.Abs(disc) <= 1e-12*(b*b+math.Abs(a*c)) {
		return s.radialExact(p)
	}
	if disc < 0 || a > 0 && b <= 0 {
		return 0, false, nil
	}
	root := math.Sqrt(disc)
	t := c / (b + root)
	if b < 0 {
		t = (root - b) / -a
	}
	if !geometryFinite(t) {
		return s.radialExact(p)
	}
	return t, true, nil
}

// gradientDifference 对有限浮点输入精确相减，避免中间溢出
// 入参: a 被减数, b 减数
// 返回: *big.Rat 精确差值
func gradientDifference(a, b float64) *big.Rat {
	return new(big.Rat).Sub(new(big.Rat).SetFloat64(a), new(big.Rat).SetFloat64(b))
}

// radialSingularParameter 在设备空间求退化椭圆族的最小包含参数，不对不可逆矩阵求逆
// 入参: p 有限设备采样点
// 返回: float64 椭圆参数, bool 是否位于退化椭圆族内, error 参数超出有限范围错误
func (s *gradientSampler) radialSingularParameter(p Point) (float64, bool, error) {
	m := s.forward
	if m.A == 0 && m.C == 0 {
		if p.X != m.E {
			return 0, false, nil
		}
		if m.B == 0 && m.D == 0 {
			return 0, p.Y == m.F, nil
		}
	} else if m.B == 0 && m.D == 0 && p.Y != m.F {
		return 0, false, nil
	}
	x, y := gradientDifference(p.X, m.E), gradientDifference(p.Y, m.F)
	u, v := m.A, m.B
	if u == 0 && v == 0 {
		u, v = m.C, m.D
	}
	cross := new(big.Rat).Sub(new(big.Rat).Mul(x, new(big.Rat).SetFloat64(v)), new(big.Rat).Mul(y, new(big.Rat).SetFloat64(u)))
	if cross.Sign() != 0 {
		return 0, false, nil
	}
	a, b, coordinate := m.A, m.C, x
	if u == 0 {
		a, b, coordinate = m.B, m.D, y
	}
	aa, bb := new(big.Rat).SetFloat64(a), new(big.Rat).SetFloat64(b)
	d := new(big.Rat).Add(new(big.Rat).Mul(aa, gradientDifference(s.center.X, s.origin.X)), new(big.Rat).Mul(bb, gradientDifference(s.center.Y, s.origin.Y)))
	origin := new(big.Rat).Add(new(big.Rat).Mul(aa, new(big.Rat).SetFloat64(s.origin.X)), new(big.Rat).Mul(bb, new(big.Rat).SetFloat64(s.origin.Y)))
	q := new(big.Rat).Sub(coordinate, origin)
	rx := new(big.Rat).Mul(aa, new(big.Rat).SetFloat64(s.radius.X))
	ry := new(big.Rat).Mul(bb, new(big.Rat).SetFloat64(s.radius.Y))
	radius := new(big.Rat).Add(new(big.Rat).Mul(rx, rx), new(big.Rat).Mul(ry, ry))
	quadratic := new(big.Rat).Sub(new(big.Rat).Mul(d, d), radius)
	return gradientRadialRoot(quadratic, new(big.Rat).Mul(q, d), new(big.Rat).Mul(q, q))
}

// radialExact 精确建立二次不等式并求最小根，兼容零半径、切线和极端量级
// 入参: p 画刷局部采样点
// 返回: float64 椭圆参数, bool 是否存在包含点的椭圆, error 参数超出有限范围错误
func (s *gradientSampler) radialExact(p Point) (float64, bool, error) {
	d := [2]*big.Rat{gradientDifference(s.center.X, s.origin.X), gradientDifference(s.center.Y, s.origin.Y)}
	q := [2]*big.Rat{gradientDifference(p.X, s.origin.X), gradientDifference(p.Y, s.origin.Y)}
	r := [2]float64{s.radius.X, s.radius.Y}
	var fixed *big.Rat
	for i := range 2 {
		if r[i] != 0 {
			continue
		}
		if d[i].Sign() == 0 {
			if q[i].Sign() != 0 {
				return 0, false, nil
			}
			continue
		}
		t := new(big.Rat).Quo(q[i], d[i])
		if t.Sign() < 0 || fixed != nil && fixed.Cmp(t) != 0 {
			return 0, false, nil
		}
		fixed = t
	}
	if fixed != nil {
		for i := range 2 {
			if r[i] == 0 {
				continue
			}
			residual := new(big.Rat).Sub(q[i], new(big.Rat).Mul(fixed, d[i]))
			width := new(big.Rat).Mul(fixed, new(big.Rat).SetFloat64(r[i]))
			if new(big.Rat).Abs(residual).Cmp(width) > 0 {
				return 0, false, nil
			}
		}
		t, _ := fixed.Float64()
		return gradientRadialResult(t)
	}
	a, b, c := big.NewRat(-1, 1), new(big.Rat), new(big.Rat)
	for i := range 2 {
		if r[i] == 0 {
			continue
		}
		radius := new(big.Rat).SetFloat64(r[i])
		di, qi := new(big.Rat).Quo(d[i], radius), new(big.Rat).Quo(q[i], radius)
		a.Add(a, new(big.Rat).Mul(di, di))
		b.Add(b, new(big.Rat).Mul(qi, di))
		c.Add(c, new(big.Rat).Mul(qi, qi))
	}
	return gradientRadialRoot(a, b, c)
}

// gradientRadialRoot 求解包含条件a*t²-2*b*t+c不大于零的最小非负根
// 入参: a 二次系数, b 一次系数的负二分之一, c 非负常数项
// 返回: float64 最小参数, bool 是否存在包含区间, error 参数超出有限范围错误
func gradientRadialRoot(a, b, c *big.Rat) (float64, bool, error) {
	if c.Sign() == 0 {
		return 0, true, nil
	}
	if a.Sign() >= 0 && b.Sign() <= 0 {
		return 0, false, nil
	}
	disc := new(big.Rat).Sub(new(big.Rat).Mul(b, b), new(big.Rat).Mul(a, c))
	if disc.Sign() < 0 {
		return 0, false, nil
	}
	bf := new(big.Float).SetPrec(256).SetRat(b)
	root := new(big.Float).SetPrec(256).Sqrt(new(big.Float).SetPrec(256).SetRat(disc))
	var value *big.Float
	if b.Sign() < 0 {
		n := new(big.Float).SetPrec(256).Sub(root, bf)
		value = n.Quo(n, new(big.Float).SetPrec(256).SetRat(new(big.Rat).Neg(a)))
	} else {
		n := new(big.Float).SetPrec(256).SetRat(c)
		value = n.Quo(n, new(big.Float).SetPrec(256).Add(bf, root))
	}
	t, _ := value.Float64()
	return gradientRadialResult(t)
}

// gradientRadialResult 检查有限非负椭圆参数
// 入参: t 待检查参数
// 返回: float64 参数, bool 是否有效, error 数值范围错误
func gradientRadialResult(t float64) (float64, bool, error) {
	if !geometryFinite(t) || t < 0 {
		return 0, false, fmt.Errorf("%w: radial gradient parameter overflow", ErrLimit)
	}
	return t, true, nil
}
