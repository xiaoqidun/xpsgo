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
	"cmp"
	"context"
	"encoding/binary"
	"fmt"
	"image/color"
	"math"
	"net/url"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

const (
	// ColorUnknown 表示未知源色彩空间
	ColorUnknown ColorSpace = iota
	// ColorSRGB 表示sRGB源色彩空间
	ColorSRGB
	// ColorScRGB 表示scRGB扩展线性色彩空间
	ColorScRGB
	// ColorContext 表示带ICC配置文件引用的ContextColor色彩空间
	ColorContext
)

// renderSRGB 等常量表示合成工作色彩空间
const (
	renderSRGB renderColorSpace = iota
	renderScRGB
)

// iccCurveIdentity 等常量表示ICC一维传递曲线编码类别
const (
	iccCurveIdentity iccCurveKind = iota
	iccCurveGamma
	iccCurveSampled
	iccCurveParametric
)

// iccStageMatrix 等常量表示ICC多阶段色彩转换步骤类型
const (
	iccStageMatrix iccStageKind = iota
	iccStageCurves
	iccStageCLUT
)

// colorDecimalPattern 匹配十进制颜色分量词法
var colorDecimalPattern = regexp.MustCompile(`^-?(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)$`)

// ColorSpace 表示颜色的源色彩空间
type ColorSpace uint8

// Color 保存非预乘颜色、源分量、原始词法及尚未解析的ICC部件引用
type Color struct {
	Space      ColorSpace
	Alpha      float64
	Components []float64
	ProfileURI string
	Raw        string
}

// renderColorSpace 表示页面与图层的合成工作色彩空间
type renderColorSpace uint8

// renderColor 保存工作空间内的预乘颜色，scRGB允许扩展分量，透明黑为零值
type renderColor struct {
	r float64
	g float64
	b float64
	a float64
}

// iccNamedColor 保存命名色的相对色度XYZ分量
type iccNamedColor struct {
	xyz [3]float64
}

// iccCurveKind 表示一维传递曲线的编码类型
type iccCurveKind uint8

// iccCurve 保存只读采样值或参数化曲线，不为大采样表重复分配浮点数组
type iccCurve struct {
	kind       iccCurveKind
	function   uint16
	parameters [7]float64
	values     []byte
	precision  int
}

// iccInverseCurve 保存已验证TRC的端点和分段值，避免逐像素重复计算准备阶段的幂函数
type iccInverseCurve struct {
	curve iccCurve
	first float64
	last  float64
	upper float64
}

// iccStageKind 表示色彩转换中的矩阵、逐通道曲线或多维查找表
type iccStageKind uint8

// iccStage 保存一个转换阶段，查找表字节与原配置文件共享只读存储
type iccStage struct {
	kind      iccStageKind
	matrix    [12]float64
	curves    []iccCurve
	grid      []int
	data      []byte
	precision int
	outputs   int
}

// iccPipeline 保存按处理顺序排列的转换阶段，输入输出均采用ICC归一化编码
type iccPipeline struct {
	inputs         int
	outputs        int
	stages         []iccStage
	legacyLab      bool
	inputPrecision int
}

// iccStageRange 记录处理元素范围，只有完全相同的曲线定义允许共享
type iccStageRange struct {
	offset uint64
	size   uint64
	curve  bool
}

// String 返回源色彩空间的文本表示
// 返回: string 色彩空间名称
func (s ColorSpace) String() string {
	switch s {
	case ColorUnknown:
		return "Unknown"
	case ColorSRGB:
		return "sRGB"
	case ColorScRGB:
		return "scRGB"
	case ColorContext:
		return "ContextColor"
	default:
		return fmt.Sprintf("ColorSpace(%d)", s)
	}
}

// ParseColor 解析sRGB、scRGB或ContextColor文本，不加载ICC配置文件或执行色彩转换
// sRGB、alpha及ContextColor分量裁剪到0至1，scRGB保留扩展分量，ContextColor允许1至8通道
// 入参: text 颜色属性文本
// 返回: Color 颜色数据, error 词法或引用错误
func ParseColor(text string) (Color, error) {
	s := strings.Trim(text, " \t\r\n")
	c := Color{Alpha: 1, Raw: text}
	switch {
	case strings.HasPrefix(s, "#"):
		if len(s) != 7 && len(s) != 9 {
			return Color{}, fmt.Errorf("%w: sRGB requires six or eight hexadecimal digits", ErrInvalid)
		}
		v, err := strconv.ParseUint(s[1:], 16, 32)
		if err != nil {
			return Color{}, fmt.Errorf("%w: invalid sRGB color %q", ErrInvalid, text)
		}
		c.Space = ColorSRGB
		c.Components = []float64{float64(v>>16&255) / 255, float64(v>>8&255) / 255, float64(v&255) / 255}
		if len(s) == 9 {
			c.Alpha = float64(v>>24) / 255
		}
	case strings.HasPrefix(s, "sc#"):
		v, err := colorComponents(s[3:], 3, 4)
		if err != nil {
			return Color{}, err
		}
		c.Space = ColorScRGB
		if len(v) == 4 {
			c.Alpha, v = colorClamp(v[0]), v[1:]
		}
		c.Components = v
	case strings.HasPrefix(s, "ContextColor"):
		const prefix = "ContextColor"
		if len(s) == len(prefix) || !xmlSpace(s[len(prefix)]) {
			return Color{}, fmt.Errorf("%w: missing ContextColor separator", ErrInvalid)
		}
		rest := strings.TrimLeft(s[len(prefix):], " \t\r\n")
		i := strings.IndexAny(rest, " \t\r\n")
		if i < 1 {
			return Color{}, fmt.Errorf("%w: missing ContextColor profile or components", ErrInvalid)
		}
		c.ProfileURI = rest[:i]
		if err := brushPartReference(c.ProfileURI); err != nil {
			return Color{}, fmt.Errorf("ContextColor profile: %w", err)
		}
		v, err := colorComponents(rest[i:], 2, 9)
		if err != nil {
			return Color{}, err
		}
		for i := range v {
			v[i] = colorClamp(v[i])
		}
		c.Space, c.Alpha, c.Components = ColorContext, v[0], v[1:]
	default:
		return Color{}, fmt.Errorf("%w: invalid color %q", ErrInvalid, text)
	}
	return c, nil
}

// colorComponents 解析受数量限制的十进制颜色分量，拒绝指数和前导加号
// 入参: text 逗号分隔文本, minimum 最少数量, maximum 最多数量
// 返回: []float64 有限分量, error 词法错误
func colorComponents(text string, minimum, maximum int) ([]float64, error) {
	count := strings.Count(text, ",") + 1
	if count < minimum || count > maximum {
		return nil, fmt.Errorf("%w: invalid color component count %d", ErrInvalid, count)
	}
	values := make([]float64, 0, count)
	for _, token := range strings.Split(text, ",") {
		token = strings.Trim(token, " \t\r\n")
		if !colorDecimalPattern.MatchString(token) {
			return nil, fmt.Errorf("%w: invalid color decimal %q", ErrInvalid, token)
		}
		value, err := strconv.ParseFloat(token, 64)
		if err != nil || !geometryFinite(value) {
			return nil, fmt.Errorf("%w: non-finite color component %q", ErrInvalid, token)
		}
		values = append(values, value)
	}
	return values, nil
}

// colorClamp 将透明度或ICC输入分量裁剪到单位区间
// 入参: value 有限分量
// 返回: float64 裁剪结果
func colorClamp(value float64) float64 {
	return min(1, max(0, value))
}

// parseBrushColor 按固定布局命名空间解析颜色并校验ContextColor通道数范围
// 入参: text 颜色文本, namespace XPS或OpenXPS命名空间
// 返回: Color 颜色数据, error 颜色或方言错误
func parseBrushColor(text, namespace string) (Color, error) {
	if namespace != xpsNamespace && namespace != openXPSNamespace {
		return Color{}, fmt.Errorf("%w: invalid color namespace", ErrInvalid)
	}
	c, err := ParseColor(text)
	if err != nil {
		return Color{}, err
	}
	if namespace == xpsNamespace && c.Space == ColorContext && len(c.Components) < 3 {
		return Color{}, fmt.Errorf("%w: XPS ContextColor requires three to eight channels", ErrInvalid)
	}
	return c, nil
}

// brushPartReference 校验包内部件引用的基本语法形式，保留相对路径与Unicode文本
// 入参: value 待检查引用
// 返回: error 非法引用错误
func brushPartReference(value string) error {
	if value == "" || !utf8.ValidString(value) || strings.ContainsAny(value, "\\?#<>\"{}|^`") || strings.HasPrefix(value, "//") {
		return fmt.Errorf("%w: invalid brush part reference %q", ErrInvalid, value)
	}
	for _, c := range value {
		if c < 0x20 || c == 0x7f || c == 0xfffe || c == 0xffff {
			return fmt.Errorf("%w: invalid character in brush part reference", ErrInvalid)
		}
	}
	u, err := url.Parse(value)
	if err != nil || u.Scheme != "" || u.Host != "" || u.Opaque != "" || u.User != nil {
		return fmt.Errorf("%w: brush reference must identify a package part", ErrInvalid)
	}
	if strings.HasSuffix(value, "/") || strings.HasSuffix(value, "/.") || strings.HasSuffix(value, "/..") || value == "." || value == ".." {
		return fmt.Errorf("%w: brush reference identifies a directory", ErrInvalid)
	}
	return nil
}

// renderColorFromColor 将非预乘源颜色转换至目标工作空间并预乘alpha，sRGB目标裁剪色域
// 入参: c 非预乘颜色, space 目标合成空间
// 返回: renderColor 预乘颜色, error 颜色结构或未支持的颜色转换错误
func renderColorFromColor(c Color, space renderColorSpace) (renderColor, error) {
	if space != renderSRGB && space != renderScRGB {
		return renderColor{}, fmt.Errorf("%w: compositor color space", ErrUnsupported)
	}
	if !geometryFinite(c.Alpha) {
		return renderColor{}, fmt.Errorf("%w: non-finite color alpha", ErrInvalid)
	}
	for _, value := range c.Components {
		if !geometryFinite(value) {
			return renderColor{}, fmt.Errorf("%w: non-finite color component", ErrInvalid)
		}
	}
	if c.Space == ColorContext {
		return renderColor{}, fmt.Errorf("%w: ICC color transform requires a color backend", ErrUnsupported)
	}
	if c.Space != ColorSRGB && c.Space != ColorScRGB || len(c.Components) != 3 {
		return renderColor{}, fmt.Errorf("%w: compositor requires an RGB source color", ErrInvalid)
	}
	channels := [3]float64{c.Components[0], c.Components[1], c.Components[2]}
	for i, value := range channels {
		if c.Space == ColorSRGB {
			if value < 0 || value > 1 {
				return renderColor{}, fmt.Errorf("%w: sRGB component outside unit range", ErrInvalid)
			}
			if space == renderScRGB {
				channels[i] = renderSRGBToLinear(value)
			}
		} else if space == renderSRGB {
			channels[i] = renderLinearToSRGB(colorClamp(value))
		}
	}
	alpha := colorClamp(c.Alpha)
	if alpha == 0 {
		return renderColor{}, nil
	}
	return renderColor{channels[0] * alpha, channels[1] * alpha, channels[2] * alpha, alpha}, nil
}

// renderSRGBToLinear 将归一化sRGB分量解码为线性光值
// 入参: value 单位区间内的有限sRGB分量
// 返回: float64 对应线性分量
func renderSRGBToLinear(value float64) float64 {
	if value <= 0.04045 {
		return value / 12.92
	}
	return math.Pow((value+0.055)/1.055, 2.4)
}

// renderLinearToSRGB 将归一化线性分量编码为sRGB值，不变换alpha
// 入参: value 单位区间内的有限线性分量
// 返回: float64 对应sRGB分量
func renderLinearToSRGB(value float64) float64 {
	if value == 1 {
		return 1
	}
	if value <= 0.0031308 {
		return 12.92 * value
	}
	return 1.055*math.Pow(value, 1.0/2.4) - 0.055
}

// validate 检查工作颜色的有限性及透明色合同，不裁剪扩展RGB分量
// 返回: error 非法数值或未支持的零alpha发光分量错误
func (c renderColor) validate() error {
	if !geometryFinite(c.r, c.g, c.b, c.a) || c.a < 0 || c.a > 1 {
		return fmt.Errorf("%w: invalid compositor color", ErrInvalid)
	}
	if c.a == 0 && (c.r != 0 || c.g != 0 || c.b != 0) {
		return fmt.Errorf("%w: nonzero premultiplied color with zero alpha", ErrUnsupported)
	}
	return nil
}

// renderSourceOver 在同一工作空间执行预乘source-over合成，不在合成期间裁剪色域
// 入参: source 前景预乘颜色, destination 背景预乘颜色
// 返回: renderColor 合成结果, error 非法输入或浮点溢出错误
func renderSourceOver(source, destination renderColor) (renderColor, error) {
	if err := source.validate(); err != nil {
		return renderColor{}, err
	}
	if err := destination.validate(); err != nil {
		return renderColor{}, err
	}
	remaining := 1 - source.a
	result := renderColor{
		source.r + destination.r*remaining,
		source.g + destination.g*remaining,
		source.b + destination.b*remaining,
		source.a + destination.a*remaining,
	}
	if !geometryFinite(result.r, result.g, result.b, result.a) {
		return renderColor{}, fmt.Errorf("%w: compositor arithmetic overflow", ErrLimit)
	}
	return result, nil
}

// renderColorModulate 将不透明度与覆盖率施加于预乘RGB和alpha
// 入参: c 预乘颜色, opacity 单位区间内的不透明度, coverage 单位区间内的覆盖率
// 返回: renderColor 调制结果, error 非法输入或不可表示的浮点下溢错误
func renderColorModulate(c renderColor, opacity, coverage float64) (renderColor, error) {
	if err := c.validate(); err != nil {
		return renderColor{}, err
	}
	if !geometryFinite(opacity, coverage) || opacity < 0 || opacity > 1 || coverage < 0 || coverage > 1 {
		return renderColor{}, fmt.Errorf("%w: opacity or coverage outside unit range", ErrInvalid)
	}
	factor := opacity * coverage
	if factor == 0 {
		if opacity != 0 && coverage != 0 && c.a != 0 {
			return renderColor{}, fmt.Errorf("%w: compositor modulation underflow", ErrLimit)
		}
		return renderColor{}, nil
	}
	result := renderColor{c.r * factor, c.g * factor, c.b * factor, c.a * factor}
	if result.a == 0 && (result.r != 0 || result.g != 0 || result.b != 0) {
		return renderColor{}, fmt.Errorf("%w: compositor alpha underflow", ErrLimit)
	}
	return result, nil
}

// renderColorToNRGBA 将工作空间预乘颜色还原、裁剪并量化为8位非预乘sRGB像素
// 入参: c 指定工作空间中的预乘颜色, space 工作空间
// 返回: color.NRGBA 非预乘sRGB像素, error 非法输入或未支持的工作空间错误
func renderColorToNRGBA(c renderColor, space renderColorSpace) (color.NRGBA, error) {
	if space != renderSRGB && space != renderScRGB {
		return color.NRGBA{}, fmt.Errorf("%w: compositor output color space", ErrUnsupported)
	}
	if err := c.validate(); err != nil {
		return color.NRGBA{}, err
	}
	alpha := uint8(math.Floor(c.a*255 + 0.5))
	if alpha == 0 {
		return color.NRGBA{}, nil
	}
	channels := [3]float64{c.r, c.g, c.b}
	var pixels [3]uint8
	for i, value := range channels {
		if value <= 0 {
			value = 0
		} else if value >= c.a {
			value = 1
		} else {
			value /= c.a
		}
		if space == renderScRGB {
			value = renderLinearToSRGB(value)
		}
		pixels[i] = uint8(math.Floor(colorClamp(value)*255 + 0.5))
	}
	return color.NRGBA{R: pixels[0], G: pixels[1], B: pixels[2], A: alpha}, nil
}

// parseICCNamedColor 读取namedColor2Type，区分设备坐标数与OpenXPS色调分量数
// 入参: profile 命名色配置文件
// 返回: []iccNamedColor 声明顺序的命名色, error 字段、编码或能力错误
func parseICCNamedColor(profile *iccProfile) ([]iccNamedColor, error) {
	if profile == nil || profile.pcs != "XYZ " && profile.pcs != "Lab " {
		return nil, fmt.Errorf("%w: ICC named connection space", ErrInvalid)
	}
	data := profile.tag("ncl2")
	if len(data) < 84 || string(data[:4]) != "ncl2" || binary.BigEndian.Uint32(data[4:]) != 0 {
		return nil, fmt.Errorf("%w: ICC named color header", ErrInvalid)
	}
	count, device := uint64(binary.BigEndian.Uint32(data[12:])), uint64(binary.BigEndian.Uint32(data[16:]))
	if device != 0 && device != uint64(profile.channels) {
		return nil, fmt.Errorf("%w: ICC named device coordinates", ErrInvalid)
	}
	stride := uint64(38) + 2*device
	end := uint64(84) + count*stride
	if count == 0 || end > uint64(len(data)) || uint64(len(data))-end > 3 {
		return nil, fmt.Errorf("%w: ICC named color size", ErrInvalid)
	}
	for _, value := range data[end:] {
		if value != 0 {
			return nil, fmt.Errorf("%w: ICC named color padding", ErrInvalid)
		}
	}
	if count > 8 {
		return nil, fmt.Errorf("%w: OpenXPS named color count", ErrUnsupported)
	}
	if err := iccNamedASCII(data[20:52]); err != nil {
		return nil, err
	}
	if err := iccNamedASCII(data[52:84]); err != nil {
		return nil, err
	}
	colors := make([]iccNamedColor, int(count))
	for i := range count {
		row := data[84+i*stride : 84+(i+1)*stride]
		if err := iccNamedASCII(row[:32]); err != nil {
			return nil, err
		}
		var pcs [3]uint16
		for axis := range 3 {
			pcs[axis] = binary.BigEndian.Uint16(row[32+axis*2:])
		}
		if profile.pcs == "XYZ " {
			for axis := range 3 {
				colors[i].xyz[axis] = float64(pcs[axis]) / 32768
			}
		} else {
			colors[i].xyz = iccLabToXYZ([3]float64{min(100, float64(pcs[0])*100/65280), float64(pcs[1])/256 - 128, float64(pcs[2])/256 - 128})
		}
	}
	return colors, nil
}

// iccNamedASCII 校验固定长度的零终止7位ASCII字段，不解释名称为文件或资源引用
// 入参: data 完整名称字段
// 返回: error 编码或终止错误
func iccNamedASCII(data []byte) error {
	end := bytes.IndexByte(data, 0)
	if end < 0 {
		return fmt.Errorf("%w: ICC named ASCII termination", ErrInvalid)
	}
	for _, value := range data[:end] {
		if value > 127 {
			return fmt.Errorf("%w: ICC named ASCII encoding", ErrInvalid)
		}
	}
	return nil
}

// inputChannels 取得转换所需分量数，命名色色调数量独立于可选设备坐标数量
// 返回: int 源分量数
func (t *iccTransform) inputChannels() int {
	if len(t.named) != 0 {
		return len(t.named)
	}
	return t.profile.channels
}

// namedXYZ 按相对白点的XYZ分量积混合命名色，单色按色调线性稀释
// 入参: input 各命名色的色调
// 返回: [3]float64 显示近似XYZ
func (t *iccTransform) namedXYZ(input []float64) [3]float64 {
	result := iccPCSWhite
	for i, color := range t.named {
		tint := colorClamp(input[i])
		for axis := range 3 {
			result[axis] *= 1 - tint + tint*color.xyz[axis]/iccPCSWhite[axis]
		}
	}
	return result
}

// parseICCCurve 解析curveType及五种parametricCurveType，返回未计末尾对齐的字节数
// 入参: data 曲线定义及可能的后续数据
// 返回: iccCurve 曲线, int 本曲线字节数, error 数据或资源错误
func parseICCCurve(data []byte) (iccCurve, int, error) {
	if len(data) < 12 || binary.BigEndian.Uint32(data[4:]) != 0 {
		return iccCurve{}, 0, fmt.Errorf("%w: ICC curve header", ErrInvalid)
	}
	switch string(data[:4]) {
	case "curv":
		count := uint64(binary.BigEndian.Uint32(data[8:]))
		if count > iccMaxCurveSamples {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC curve sample count", ErrLimit)
		}
		size := uint64(12) + 2*count
		if size > uint64(len(data)) {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC curve sample data", ErrInvalid)
		}
		curve := iccCurve{kind: iccCurveIdentity}
		if count == 1 {
			curve.kind = iccCurveGamma
			curve.parameters[0] = float64(binary.BigEndian.Uint16(data[12:])) / 256
		} else if count > 1 {
			curve.kind = iccCurveSampled
			curve.values = data[12:size]
			curve.precision = 2
		}
		return curve, int(size), nil
	case "para":
		function := binary.BigEndian.Uint16(data[8:])
		if function > 4 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve function", ErrUnsupported)
		}
		if binary.BigEndian.Uint16(data[10:]) != 0 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve reserved field", ErrInvalid)
		}
		count := [5]int{1, 3, 4, 5, 7}[function]
		size := 12 + 4*count
		if len(data) < size {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve parameters", ErrInvalid)
		}
		curve := iccCurve{kind: iccCurveParametric, function: function}
		for i := range count {
			curve.parameters[i] = iccFixed(data[12+i*4:])
		}
		if (function == 1 || function == 2) && curve.parameters[1] == 0 {
			return iccCurve{}, 0, fmt.Errorf("%w: ICC parametric curve division", ErrInvalid)
		}
		return curve, size, nil
	default:
		return iccCurve{}, 0, fmt.Errorf("%w: ICC curve type %q", ErrUnsupported, string(data[:4]))
	}
}

// evaluate 按ICC单位定义域求值并裁剪输出，不将gamma误解释为其倒数
// 入参: value 有限输入分量
// 返回: float64 单位区间输出, error 非实数函数或输入错误
func (c iccCurve) evaluate(value float64) (float64, error) {
	if !geometryFinite(value) {
		return 0, fmt.Errorf("%w: ICC curve input", ErrInvalid)
	}
	value = colorClamp(value)
	var result float64
	switch c.kind {
	case iccCurveIdentity:
		return value, nil
	case iccCurveGamma:
		result = math.Pow(value, c.parameters[0])
	case iccCurveSampled:
		if c.precision != 1 && c.precision != 2 {
			return 0, fmt.Errorf("%w: ICC curve sample precision", ErrInvalid)
		}
		count := len(c.values) / c.precision
		if count < 2 {
			return 0, fmt.Errorf("%w: ICC sampled curve", ErrInvalid)
		}
		position := value * float64(count-1)
		index := min(int(position), count-2)
		fraction := position - float64(index)
		var a, b float64
		if c.precision == 1 {
			a, b = float64(c.values[index])/255, float64(c.values[index+1])/255
		} else {
			a, b = float64(binary.BigEndian.Uint16(c.values[2*index:]))/65535, float64(binary.BigEndian.Uint16(c.values[2*index+2:]))/65535
		}
		result = a*(1-fraction) + b*fraction
	case iccCurveParametric:
		p := c.parameters
		switch c.function {
		case 0:
			result = math.Pow(value, p[0])
		case 1, 2:
			if value >= -p[2]/p[1] {
				result = math.Pow(p[1]*value+p[2], p[0])
			}
			if c.function == 2 {
				result += p[3]
			}
		case 3, 4:
			if value >= p[4] {
				result = math.Pow(p[1]*value+p[2], p[0])
				if c.function == 4 {
					result += p[5]
				}
			} else {
				result = p[3] * value
				if c.function == 4 {
					result += p[6]
				}
			}
		default:
			return 0, fmt.Errorf("%w: ICC curve function", ErrUnsupported)
		}
	default:
		return 0, fmt.Errorf("%w: ICC curve kind", ErrInvalid)
	}
	if math.IsNaN(result) {
		return 0, fmt.Errorf("%w: non-real ICC curve value", ErrInvalid)
	}
	return colorClamp(result), nil
}

// prepareICCInverseCurve 验证TRC并缓存求逆所需的端点及幂分段边界
// 入参: curve 原始曲线, ctx 取消Context
// 返回: iccInverseCurve 可直接求逆的曲线, error 能力、数值或取消错误
func prepareICCInverseCurve(curve iccCurve, ctx context.Context) (iccInverseCurve, error) {
	if err := validateICCInverseCurve(curve, ctx); err != nil {
		return iccInverseCurve{}, err
	}
	first, _ := curve.evaluate(0)
	last, _ := curve.evaluate(1)
	result := iccInverseCurve{curve: curve, first: first, last: last}
	if curve.kind == iccCurveParametric && curve.function >= 3 && curve.parameters[4] > 0 && curve.parameters[4] < 1 {
		result.upper, _ = curve.evaluate(curve.parameters[4])
	}
	return result, nil
}

// validateICCInverseCurve 检查可逆TRC的单调性，平坦段允许采用最左侧广义逆
// 入参: c 已解析曲线, ctx 取消Context
// 返回: error 非单调、常量、数值或取消错误
func validateICCInverseCurve(c iccCurve, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	a, err := c.evaluate(0)
	if err != nil {
		return err
	}
	b, err := c.evaluate(1)
	if err != nil {
		return err
	}
	if a == b {
		return fmt.Errorf("%w: constant ICC target curve", ErrUnsupported)
	}
	points := []float64{0, 1}
	if c.kind == iccCurveSampled {
		count := len(c.values) / c.precision
		previous := a
		for i := 1; i < count; i++ {
			if i&1023 == 0 {
				if err := checkContext(ctx); err != nil {
					return err
				}
			}
			value := iccInverseCurveSample(c, i)
			if b > a && value < previous || b < a && value > previous {
				return fmt.Errorf("%w: nonmonotonic ICC target curve", ErrUnsupported)
			}
			previous = value
		}
	} else if c.kind == iccCurveParametric {
		p := c.parameters
		boundary := 0.0
		if c.function == 1 || c.function == 2 {
			boundary = -p[2] / p[1]
		} else if c.function >= 3 {
			boundary = p[4]
		}
		if boundary > 0 && boundary < 1 {
			points = append(points, math.Nextafter(boundary, 0), boundary, math.Nextafter(boundary, 1))
		}
		if c.function == 0 && p[0] <= 0 || c.function != 0 && (p[0] <= 0 || p[1] <= 0) || c.function >= 3 && p[3] < 0 {
			return fmt.Errorf("%w: ICC target parametric curve inverse", ErrUnsupported)
		}
		if c.function != 0 && boundary < 1 && p[1]*max(0, boundary)+p[2] < 0 {
			return fmt.Errorf("%w: ICC target curve power domain", ErrUnsupported)
		}
	}
	slices.Sort(points)
	previous := a
	for _, point := range points {
		value, err := c.evaluate(point)
		if err != nil {
			return err
		}
		if b > a && value < previous || b < a && value > previous {
			return fmt.Errorf("%w: discontinuous ICC target curve inverse", ErrUnsupported)
		}
		previous = value
	}
	return checkContext(ctx)
}

// inverseICCCurve 求已验证TRC的最左侧广义逆，超出曲线值域时取最近端点
// 入参: prepared 已准备的单调曲线, value 有限目标值
// 返回: float64 单位区间设备分量
func inverseICCCurve(prepared iccInverseCurve, value float64) float64 {
	c := prepared.curve
	if c.kind == iccCurveIdentity {
		return colorClamp(value)
	}
	if c.kind == iccCurveGamma {
		return math.Pow(colorClamp(value), 1/c.parameters[0])
	}
	a, b := prepared.first, prepared.last
	increasing := b > a
	if increasing && value <= a || !increasing && value >= a {
		return 0
	}
	if increasing && value > b || !increasing && value < b {
		return 1
	}
	if c.kind == iccCurveSampled {
		count := len(c.values) / c.precision
		low, high := 0, count-1
		for low < high {
			mid := low + (high-low)/2
			v := iccInverseCurveSample(c, mid)
			if increasing && v < value || !increasing && v > value {
				low = mid + 1
			} else {
				high = mid
			}
		}
		if low == 0 {
			return 0
		}
		x0, x1 := float64(low-1)/float64(count-1), float64(low)/float64(count-1)
		y0, y1 := iccInverseCurveSample(c, low-1), iccInverseCurveSample(c, low)
		if y0 == y1 {
			return x0
		}
		return x0 + (x1-x0)*(value-y0)/(y1-y0)
	}
	p := c.parameters
	if c.function == 0 {
		return colorClamp(math.Pow(value, 1/p[0]))
	}
	offset, boundary := 0.0, -p[2]/p[1]
	if c.function == 2 {
		offset = p[3]
	}
	if c.function >= 3 {
		boundary = p[4]
		linearOffset := 0.0
		if c.function == 4 {
			offset, linearOffset = p[5], p[6]
		}
		if boundary > 0 {
			limit := min(1, boundary)
			if value <= colorClamp(p[3]*limit+linearOffset) && p[3] > 0 {
				return min(limit, colorClamp((value-linearOffset)/p[3]))
			}
			if boundary < 1 {
				if value <= prepared.upper {
					return boundary
				}
			}
		}
	}
	return colorClamp(max(boundary, (math.Pow(max(0, value-offset), 1/p[0])-p[2])/p[1]))
}

// iccInverseCurveSample 读取已验证采样表的节点值，不对整数索引重复执行曲线插值
// 入参: curve 有效采样曲线, index 有效节点索引
// 返回: float64 归一化节点值
func iccInverseCurveSample(curve iccCurve, index int) float64 {
	if curve.precision == 1 {
		return float64(curve.values[index]) / 255
	}
	return float64(binary.BigEndian.Uint16(curve.values[index*2:])) / 65535
}

// parseICCLUT 解析lut8Type和lut16Type，检查矩阵条件及全部表格范围后再建立视图
// 入参: data 标签字节, inputXYZ 输入是否为XYZ空间
// 返回: *iccPipeline 转换阶段, error 数据、能力或资源错误
func parseICCLUT(data []byte, inputXYZ bool) (*iccPipeline, error) {
	if len(data) < 48 || binary.BigEndian.Uint32(data[4:]) != 0 || data[11] != 0 {
		return nil, fmt.Errorf("%w: ICC LUT header", ErrInvalid)
	}
	precision, inputEntries, outputEntries, offset := 1, 256, 256, 48
	switch string(data[:4]) {
	case "mft1":
	case "mft2":
		if len(data) < 52 {
			return nil, fmt.Errorf("%w: ICC LUT16 header", ErrInvalid)
		}
		precision, offset = 2, 52
		inputEntries = int(binary.BigEndian.Uint16(data[48:]))
		outputEntries = int(binary.BigEndian.Uint16(data[50:]))
		if inputEntries < 2 || inputEntries > 4096 || outputEntries < 2 || outputEntries > 4096 {
			return nil, fmt.Errorf("%w: ICC LUT16 table count", ErrInvalid)
		}
	default:
		return nil, fmt.Errorf("%w: ICC LUT type %q", ErrUnsupported, string(data[:4]))
	}
	inputs, outputs, points := int(data[8]), int(data[9]), int(data[10])
	if inputs == 0 || outputs == 0 {
		return nil, fmt.Errorf("%w: ICC LUT channels", ErrInvalid)
	}
	if inputs > 8 || outputs > 8 {
		return nil, fmt.Errorf("%w: ICC LUT channel count", ErrUnsupported)
	}
	if points < 2 {
		return nil, fmt.Errorf("%w: ICC LUT grid", ErrInvalid)
	}
	matrix := iccStage{kind: iccStageMatrix}
	identity := true
	for i := range 9 {
		matrix.matrix[i] = iccFixed(data[12+4*i:])
		want := 0.0
		if i%4 == 0 {
			want = 1
		}
		identity = identity && matrix.matrix[i] == want
	}
	if !inputXYZ && !identity {
		return nil, fmt.Errorf("%w: ICC LUT matrix requires XYZ input", ErrInvalid)
	}
	if inputXYZ && inputs != 3 {
		return nil, fmt.Errorf("%w: ICC XYZ LUT input count", ErrInvalid)
	}
	cells := uint64(outputs)
	for range inputs {
		if cells > uint64(len(data))/uint64(points) {
			return nil, fmt.Errorf("%w: ICC LUT grid size", ErrInvalid)
		}
		cells *= uint64(points)
	}
	inputBytes := inputs * inputEntries * precision
	outputBytes := outputs * outputEntries * precision
	if cells > uint64(len(data))/uint64(precision) || uint64(offset+inputBytes+outputBytes)+cells*uint64(precision) > uint64(len(data)) {
		return nil, fmt.Errorf("%w: ICC LUT data size", ErrInvalid)
	}
	p := &iccPipeline{inputs: inputs, outputs: outputs, legacyLab: precision == 2, inputPrecision: precision}
	if inputXYZ && !identity {
		p.stages = append(p.stages, matrix)
	}
	input := iccStage{kind: iccStageCurves}
	for i := range inputs {
		first := offset + i*inputEntries*precision
		input.curves = append(input.curves, iccCurve{kind: iccCurveSampled, precision: precision, values: data[first : first+inputEntries*precision]})
	}
	p.stages = append(p.stages, input)
	offset += inputBytes
	clut := iccStage{kind: iccStageCLUT, precision: precision, outputs: outputs, data: data[offset : offset+int(cells)*precision]}
	for range inputs {
		clut.grid = append(clut.grid, points)
	}
	p.stages = append(p.stages, clut)
	offset += len(clut.data)
	output := iccStage{kind: iccStageCurves}
	for i := range outputs {
		first := offset + i*outputEntries*precision
		output.curves = append(output.curves, iccCurve{kind: iccCurveSampled, precision: precision, values: data[first : first+outputEntries*precision]})
	}
	p.stages = append(p.stages, output)
	return p, nil
}

// evaluate 执行有界归一化转换，保留阶段之间的浮点精度，不分配每个颜色的临时切片
// 入参: input 归一化源分量
// 返回: [8]float64 目标分量，数量由管线定义, error 输入或阶段错误
func (p *iccPipeline) evaluate(input []float64) ([8]float64, error) {
	if p == nil || len(input) != p.inputs || p.inputs < 1 || p.inputs > 8 || p.outputs < 1 || p.outputs > 8 {
		return [8]float64{}, fmt.Errorf("%w: ICC pipeline channels", ErrInvalid)
	}
	var values [8]float64
	for i, value := range input {
		if !geometryFinite(value) {
			return [8]float64{}, fmt.Errorf("%w: ICC pipeline input", ErrInvalid)
		}
		values[i] = colorClamp(value)
	}
	count := p.inputs
	for _, stage := range p.stages {
		switch stage.kind {
		case iccStageMatrix:
			if count != 3 {
				return [8]float64{}, fmt.Errorf("%w: ICC matrix stage channels", ErrInvalid)
			}
			original := values
			for row := range 3 {
				m := stage.matrix[row*3:]
				values[row] = colorClamp(m[0]*original[0] + m[1]*original[1] + m[2]*original[2] + stage.matrix[9+row])
			}
		case iccStageCurves:
			if len(stage.curves) != count {
				return [8]float64{}, fmt.Errorf("%w: ICC curve stage channels", ErrInvalid)
			}
			for i, curve := range stage.curves {
				value, err := curve.evaluate(values[i])
				if err != nil {
					return [8]float64{}, err
				}
				values[i] = value
			}
		case iccStageCLUT:
			var err error
			values, err = stage.lookup(values[:count])
			if err != nil {
				return [8]float64{}, err
			}
			count = stage.outputs
		default:
			return [8]float64{}, fmt.Errorf("%w: ICC stage kind", ErrInvalid)
		}
	}
	if count != p.outputs {
		return [8]float64{}, fmt.Errorf("%w: ICC pipeline output channels", ErrInvalid)
	}
	return values, nil
}

// lookup 按首通道变化最慢的表布局执行多线性插值，最多计算八维单元的256个角点
// 入参: input 当前阶段归一化分量
// 返回: [8]float64 插值输出, error 布局或参数错误
func (s iccStage) lookup(input []float64) ([8]float64, error) {
	n := len(s.grid)
	if n < 1 || n > 8 || len(input) != n || s.outputs < 1 || s.outputs > 8 || s.precision != 1 && s.precision != 2 {
		return [8]float64{}, fmt.Errorf("%w: ICC CLUT layout", ErrInvalid)
	}
	var fractions [8]float64
	var lower, stride [8]int
	cells := s.outputs
	for i := n - 1; i >= 0; i-- {
		if s.grid[i] < 2 || cells > len(s.data)/s.precision/s.grid[i] {
			return [8]float64{}, fmt.Errorf("%w: ICC CLUT data", ErrInvalid)
		}
		stride[i] = cells
		cells *= s.grid[i]
		if !geometryFinite(input[i]) {
			return [8]float64{}, fmt.Errorf("%w: ICC CLUT input", ErrInvalid)
		}
		position := colorClamp(input[i]) * float64(s.grid[i]-1)
		lower[i] = min(int(position), s.grid[i]-2)
		fractions[i] = position - float64(lower[i])
	}
	var out [8]float64
	for corner := 0; corner < 1<<n; corner++ {
		index, weight := 0, 1.0
		for i := range n {
			upper := corner >> i & 1
			index += (lower[i] + upper) * stride[i]
			if upper != 0 {
				weight *= fractions[i]
			} else {
				weight *= 1 - fractions[i]
			}
		}
		if weight == 0 {
			continue
		}
		for channel := range s.outputs {
			value := 0.0
			if s.precision == 1 {
				value = float64(s.data[index+channel]) / 255
			} else {
				value = float64(binary.BigEndian.Uint16(s.data[(index+channel)*2:])) / 65535
			}
			out[channel] += value * weight
		}
	}
	for channel := range s.outputs {
		out[channel] = colorClamp(out[channel])
	}
	return out, nil
}

// parseICCMultiLUT 解析正向或反向多阶段查找表，检查允许的阶段组合和共享曲线
// 入参: data lutAtoBType或lutBtoAType标签
// 返回: *iccPipeline 转换管线, error 数据、能力或资源错误
func parseICCMultiLUT(data []byte) (*iccPipeline, error) {
	if len(data) < 32 || binary.BigEndian.Uint32(data[4:]) != 0 || binary.BigEndian.Uint16(data[10:]) != 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT header", ErrInvalid)
	}
	reverse := string(data[:4]) == "mBA "
	if !reverse && string(data[:4]) != "mAB " {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT type", ErrUnsupported)
	}
	inputs, outputs := int(data[8]), int(data[9])
	if inputs == 0 || outputs == 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT channels", ErrInvalid)
	}
	if inputs > 8 || outputs > 8 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT channel count", ErrUnsupported)
	}
	var offsets [5]uint64
	for i := range offsets {
		offsets[i] = uint64(binary.BigEndian.Uint32(data[12+4*i:]))
		if offsets[i] != 0 && (offsets[i] < 32 || offsets[i]%4 != 0 || offsets[i] >= uint64(len(data))) {
			return nil, fmt.Errorf("%w: ICC multi-stage LUT offset", ErrInvalid)
		}
	}
	if offsets[0] == 0 || (offsets[1] == 0) != (offsets[2] == 0) || (offsets[3] == 0) != (offsets[4] == 0) || inputs != outputs && offsets[3] == 0 {
		return nil, fmt.Errorf("%w: ICC multi-stage LUT combination", ErrInvalid)
	}
	curveChannels := outputs
	lastChannels := inputs
	if reverse {
		curveChannels, lastChannels = inputs, outputs
	}
	if offsets[1] != 0 && curveChannels != 3 {
		return nil, fmt.Errorf("%w: ICC multi-stage matrix channels", ErrInvalid)
	}
	var stages [5]iccStage
	var ranges []iccStageRange
	for _, index := range []int{0, 2, 4} {
		if offsets[index] == 0 {
			continue
		}
		count := curveChannels
		if index == 4 {
			count = lastChannels
		}
		stage, spans, err := iccEmbeddedCurves(data, offsets[index], count)
		if err != nil {
			return nil, err
		}
		stages[index] = stage
		ranges = append(ranges, spans...)
	}
	if offsets[1] != 0 {
		at := offsets[1]
		if at+48 > uint64(len(data)) {
			return nil, fmt.Errorf("%w: ICC multi-stage matrix data", ErrInvalid)
		}
		stages[1].kind = iccStageMatrix
		for i := range 12 {
			stages[1].matrix[i] = iccFixed(data[at+uint64(i)*4:])
		}
		ranges = append(ranges, iccStageRange{offset: at, size: 48})
	}
	if offsets[3] != 0 {
		stage, size, err := iccEmbeddedCLUT(data[offsets[3]:], inputs, outputs)
		if err != nil {
			return nil, err
		}
		stages[3] = stage
		ranges = append(ranges, iccStageRange{offset: offsets[3], size: uint64(size)})
	}
	slices.SortFunc(ranges, func(a, b iccStageRange) int {
		if value := cmp.Compare(a.offset, b.offset); value != 0 {
			return value
		}
		return cmp.Compare(a.size, b.size)
	})
	for i := 1; i < len(ranges); i++ {
		a, b := ranges[i-1], ranges[i]
		if b.offset < a.offset+a.size && (!a.curve || !b.curve || a.offset != b.offset || a.size != b.size) {
			return nil, fmt.Errorf("%w: overlapping ICC processing elements", ErrInvalid)
		}
	}
	p := &iccPipeline{inputs: inputs, outputs: outputs}
	order := []int{4, 3, 2, 1, 0}
	if reverse {
		order = []int{0, 1, 2, 3, 4}
	}
	for _, index := range order {
		if offsets[index] != 0 {
			p.stages = append(p.stages, stages[index])
		}
	}
	return p, nil
}

// iccEmbeddedCurves 读取顺序排列的逐通道曲线，并保留各曲线独立范围以校验共享
// 入参: data 标签字节, offset 首条曲线偏移, count 通道数
// 返回: iccStage 曲线阶段, []iccStageRange 曲线范围, error 曲线或对齐错误
func iccEmbeddedCurves(data []byte, offset uint64, count int) (iccStage, []iccStageRange, error) {
	stage := iccStage{kind: iccStageCurves}
	var ranges []iccStageRange
	for index := range count {
		if offset >= uint64(len(data)) {
			return iccStage{}, nil, fmt.Errorf("%w: ICC embedded curve offset", ErrInvalid)
		}
		curve, size, err := parseICCCurve(data[offset:])
		if err != nil {
			return iccStage{}, nil, err
		}
		ranges = append(ranges, iccStageRange{offset, uint64(size), true})
		stage.curves = append(stage.curves, curve)
		end := offset + uint64(size)
		next := (end + 3) &^ uint64(3)
		if next > uint64(len(data)) {
			if index == count-1 && end == uint64(len(data)) {
				break
			}
			return iccStage{}, nil, fmt.Errorf("%w: ICC curve alignment", ErrInvalid)
		}
		for _, value := range data[end:next] {
			if value != 0 {
				return iccStage{}, nil, fmt.Errorf("%w: ICC curve padding", ErrInvalid)
			}
		}
		offset = next
	}
	return stage, ranges, nil
}

// iccEmbeddedCLUT 读取各轴独立网格的八位或十六位表，不为表格分配副本
// 入参: data CLUT定义及后续数据, inputs 输入通道数, outputs 输出通道数
// 返回: iccStage 查找表阶段, int 元素字节数, error 数据或资源错误
func iccEmbeddedCLUT(data []byte, inputs, outputs int) (iccStage, int, error) {
	if len(data) < 20 || inputs < 1 || inputs > 8 || outputs < 1 || outputs > 8 {
		return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT header", ErrInvalid)
	}
	precision := int(data[16])
	if precision != 1 && precision != 2 || data[17] != 0 || data[18] != 0 || data[19] != 0 {
		return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT precision", ErrInvalid)
	}
	for _, value := range data[inputs:16] {
		if value != 0 {
			return iccStage{}, 0, fmt.Errorf("%w: ICC unused CLUT grid", ErrInvalid)
		}
	}
	stage := iccStage{kind: iccStageCLUT, precision: precision, outputs: outputs}
	cells := uint64(outputs)
	for _, value := range data[:inputs] {
		if value < 2 {
			return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT grid", ErrInvalid)
		}
		if cells > uint64(len(data)-20)/uint64(precision)/uint64(value) {
			return iccStage{}, 0, fmt.Errorf("%w: ICC embedded CLUT size", ErrInvalid)
		}
		cells *= uint64(value)
		stage.grid = append(stage.grid, int(value))
	}
	size := 20 + int(cells)*precision
	stage.data = data[20:size]
	return stage, size, nil
}
