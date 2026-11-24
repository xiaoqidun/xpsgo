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
	"encoding/xml"
	"fmt"
	"math"
	"math/big"
	"strconv"
	"strings"
)

const (
	// GeometryEvenOdd 表示奇偶填充规则
	GeometryEvenOdd GeometryFillRule = iota
	// GeometryNonZero 表示非零环绕填充规则
	GeometryNonZero
)

const (
	// GeometryLine 表示直线段
	GeometryLine GeometrySegmentKind = iota
	// GeometryCubic 表示三次贝塞尔曲线段
	GeometryCubic
	// GeometryQuadratic 表示二次贝塞尔曲线段
	GeometryQuadratic
	// GeometryArc 表示椭圆圆弧段
	GeometryArc
)

// Point 表示二维坐标
type Point struct {
	X, Y float64
}

// Rect 表示由原点和宽高定义的轴对齐矩形
type Rect struct {
	X, Y, Width, Height float64
}

// Matrix 表示满足x'=A*x+C*y+E、y'=B*x+D*y+F的列向量仿射变换
type Matrix struct {
	A, B, C, D, E, F float64
}

// GeometryFillRule 表示几何整体的奇偶或非零填充规则
type GeometryFillRule uint8

// GeometrySegmentKind 表示规范化后的直线、三次曲线、二次曲线或圆弧类别
type GeometrySegmentKind uint8

// GeometrySegment 保存绝对终点、依次排列的控制点及圆弧参数，圆弧旋转角以度计
type GeometrySegment struct {
	Kind                            GeometrySegmentKind
	Point, Control1, Control2       Point
	RadiusX, RadiusY, RotationAngle float64
	IsLargeArc, SweepClockwise      bool
	IsStroked                       bool
}

// GeometryFigure 表示由起点、线段及闭合标志组成的子路径，闭合边不重复存入线段列表
type GeometryFigure struct {
	StartPoint Point
	Segments   []GeometrySegment
	IsClosed   bool
	IsFilled   bool
}

// Geometry 表示统一的局部坐标路径几何，Transform为nil时表示单位变换
type Geometry struct {
	FillRule  GeometryFillRule
	Figures   []GeometryFigure
	Transform *Matrix
}

// GeometrySyntaxError 记录几何或矩阵语法错误的零基字节偏移及原因
type GeometrySyntaxError struct {
	Offset  int
	Message string
}

// geometryScanner 保存严格词法扫描状态及首个错误位置
type geometryScanner struct {
	text string
	pos  int
	err  error
}

// geometryEdge 表示设备空间中保留方向的填充边
type geometryEdge struct {
	start, end Point
}

// geometryFillBuilder 保存填充边及实现资源预算，不修改输入几何
type geometryFillBuilder struct {
	edges     []geometryEdge
	tolerance float64
	maxEdges  int
	splits    int
}

// String 返回几何填充规则的名称
// 返回: string 填充规则名称
func (r GeometryFillRule) String() string {
	switch r {
	case GeometryEvenOdd:
		return "EvenOdd"
	case GeometryNonZero:
		return "NonZero"
	default:
		return fmt.Sprintf("GeometryFillRule(%d)", r)
	}
}

// String 返回几何线段类别的名称
// 返回: string 线段类别名称
func (k GeometrySegmentKind) String() string {
	switch k {
	case GeometryLine:
		return "Line"
	case GeometryCubic:
		return "Cubic"
	case GeometryQuadratic:
		return "Quadratic"
	case GeometryArc:
		return "Arc"
	default:
		return fmt.Sprintf("GeometrySegmentKind(%d)", k)
	}
}

// IdentityMatrix 创建单位矩阵
// 返回: Matrix 不改变坐标的仿射矩阵
func IdentityMatrix() Matrix {
	return Matrix{A: 1, D: 1}
}

// Transform 变换坐标
// 入参: p 待变换的点
// 返回: Point 变换后的坐标
func (m Matrix) Transform(p Point) Point {
	return Point{m.A*p.X + m.C*p.Y + m.E, m.B*p.X + m.D*p.Y + m.F}
}

// Mul 组合仿射矩阵，先应用n再应用m
// 入参: n 右乘矩阵
// 返回: Matrix 乘积m*n
func (m Matrix) Mul(n Matrix) Matrix {
	return Matrix{
		A: m.A*n.A + m.C*n.B,
		B: m.B*n.A + m.D*n.B,
		C: m.A*n.C + m.C*n.D,
		D: m.B*n.C + m.D*n.D,
		E: m.A*n.E + m.C*n.F + m.E,
		F: m.B*n.E + m.D*n.F + m.F,
	}
}

// Inverse 求逆矩阵，拒绝非有限、奇异及逆矩阵超出浮点范围的输入
// 返回: Matrix 逆矩阵, error 错误信息
func (m Matrix) Inverse() (Matrix, error) {
	if !geometryFillMatrixFinite(m) {
		return Matrix{}, fmt.Errorf("%w: matrix contains non-finite coefficients", ErrInvalid)
	}
	sx, sy := math.Max(math.Abs(m.A), math.Abs(m.B)), math.Max(math.Abs(m.C), math.Abs(m.D))
	if sx == 0 || sy == 0 {
		return Matrix{}, fmt.Errorf("%w: singular matrix", ErrInvalid)
	}
	a, b, c, d := m.A/sx, m.B/sx, m.C/sy, m.D/sy
	if (a == 0 && m.A != 0) || (b == 0 && m.B != 0) || (c == 0 && m.C != 0) || (d == 0 && m.D != 0) {
		return geometryExactInverse(m)
	}
	p, q := a*d, b*c
	det := (p - q) + (math.FMA(a, d, -p) - math.FMA(b, c, -q))
	if det == 0 {
		return geometryExactInverse(m)
	}
	n := Matrix{A: (d / det) / sx, B: (-b / det) / sy, C: (-c / det) / sx, D: (a / det) / sy}
	n.E, n.F = -(n.A*m.E + n.C*m.F), -(n.B*m.E + n.D*m.F)
	if !geometryFinite(n.A, n.B, n.C, n.D, n.E, n.F) {
		return geometryExactInverse(m)
	}
	return n, nil
}

// geometryExactInverse 精确计算极端量级矩阵的逆，避免中间结果溢出或下溢
// 入参: m 系数均为有限数值的矩阵
// 返回: Matrix 舍入到float64的逆矩阵, error 错误信息
func geometryExactInverse(m Matrix) (Matrix, error) {
	a, b := new(big.Rat).SetFloat64(m.A), new(big.Rat).SetFloat64(m.B)
	c, d := new(big.Rat).SetFloat64(m.C), new(big.Rat).SetFloat64(m.D)
	e, f := new(big.Rat).SetFloat64(m.E), new(big.Rat).SetFloat64(m.F)
	det := new(big.Rat).Sub(new(big.Rat).Mul(a, d), new(big.Rat).Mul(b, c))
	if det.Sign() == 0 {
		return Matrix{}, fmt.Errorf("%w: singular matrix", ErrInvalid)
	}
	numerators := []*big.Rat{
		d, new(big.Rat).Neg(b), new(big.Rat).Neg(c), a,
		new(big.Rat).Sub(new(big.Rat).Mul(c, f), new(big.Rat).Mul(d, e)),
		new(big.Rat).Sub(new(big.Rat).Mul(b, e), new(big.Rat).Mul(a, f)),
	}
	var v [6]float64
	for i, numerator := range numerators {
		v[i], _ = new(big.Rat).Quo(numerator, det).Float64()
	}
	if !geometryFinite(v[:]...) {
		return Matrix{}, fmt.Errorf("%w: inverse exceeds finite float64 range", ErrLimit)
	}
	return Matrix{v[0], v[1], v[2], v[3], v[4], v[5]}, nil
}

// ParseMatrix 解析六个逗号分隔的仿射矩阵系数
// 入参: s 逗号分隔的六个实数
// 返回: Matrix 仿射矩阵, error 错误信息
func ParseMatrix(s string) (Matrix, error) {
	p := geometryScanner{text: s}
	p.space()
	var v [6]float64
	for i := range v {
		if i > 0 {
			p.separator(',')
		}
		v[i] = p.number()
	}
	p.space()
	if p.pos != len(s) {
		p.fail("unexpected trailing matrix data")
	}
	if p.err != nil {
		return Matrix{}, p.err
	}
	return Matrix{v[0], v[1], v[2], v[3], v[4], v[5]}, nil
}

// Error 格式化语法错误
// 返回: string 包含字节偏移和原因的错误文本
func (e *GeometrySyntaxError) Error() string {
	if e == nil {
		return "<nil>"
	}
	return fmt.Sprintf("geometry syntax at byte %d: %s", e.Offset, e.Message)
}

// Unwrap 返回语法错误分类
// 返回: error 文档无效错误
func (e *GeometrySyntaxError) Unwrap() error {
	if e == nil {
		return nil
	}
	return ErrInvalid
}

// ParseGeometry 解析固定布局路径缩写语法并展开为绝对坐标几何，支持F0/F1及M/L/H/V/C/S/Q/A/Z命令
// 结果Transform为nil，子路径IsFilled与线段IsStroked均为true，Z仅置IsClosed而不追加闭合段
// 入参: s 可含首部F0/F1的Data或Clip文本
// 返回: *Geometry 绝对坐标几何, error 带位置的语法错误
func ParseGeometry(s string) (*Geometry, error) {
	return parseGeometryLimited(s, nil)
}

// parseGeometryLimited 共用缩写解析，在追加子路径和线段前检查调用方容量
// 入参: s 几何缩写, charge 新子路径及语义段计费回调，nil表示不额外限制
// 返回: *Geometry 绝对坐标几何, error 语法、预算或取消错误
func parseGeometryLimited(s string, charge func(int, int) error) (*Geometry, error) {
	p := geometryScanner{text: s}
	g := &Geometry{}
	p.space()
	if p.peek() == 'F' {
		p.pos++
		p.space()
		g.FillRule = GeometryFillRule(p.flag())
		p.space()
	}
	if p.peek() != 'M' && p.peek() != 'm' {
		p.fail("geometry must begin with M or m after optional F0/F1")
	}
	var current Point
	var figure *GeometryFigure
	for p.err == nil && p.pos < len(s) {
		cmd := p.peek()
		p.pos++
		upper := cmd
		if upper >= 'a' && upper <= 'z' {
			upper -= 'a' - 'A'
		}
		layout := ""
		switch upper {
		case 'M', 'L':
			layout = ","
		case 'H', 'V':
		case 'C':
			layout = ", , ,"
		case 'S', 'Q':
			layout = ", ,"
		case 'A':
			layout = ",    ,"
		case 'Z':
			if figure != nil {
				figure.IsClosed = true
				current = figure.StartPoint
				figure = nil
			}
			p.space()
			continue
		default:
			p.pos--
			p.fail(fmt.Sprintf("unsupported XPS command %q", cmd))
			continue
		}
		p.space()
		for p.err == nil {
			var v [7]float64
			for i := 0; i <= len(layout); i++ {
				if i > 0 {
					p.separator(layout[i-1])
				}
				if upper == 'A' && (i == 3 || i == 4) {
					v[i] = float64(p.flag())
				} else {
					v[i] = p.number()
				}
			}
			if p.err != nil {
				break
			}
			relative := cmd >= 'a' && cmd <= 'z'
			end := geometryPoint(v[0], v[1], current, relative)
			segment := GeometrySegment{Kind: GeometryLine, Point: end, IsStroked: true}
			if upper != 'M' && figure == nil {
				if charge != nil {
					if err := charge(1, 0); err != nil {
						return nil, err
					}
				}
				g.Figures = append(g.Figures, GeometryFigure{StartPoint: current, IsFilled: true})
				figure = &g.Figures[len(g.Figures)-1]
			}
			switch upper {
			case 'M':
				if charge != nil {
					if err := charge(1, 0); err != nil {
						return nil, err
					}
				}
				g.Figures = append(g.Figures, GeometryFigure{StartPoint: end, IsFilled: true})
				figure = &g.Figures[len(g.Figures)-1]
			case 'H':
				segment.Point = Point{end.X, current.Y}
			case 'V':
				segment.Point = Point{current.X, geometryPoint(0, v[0], current, relative).Y}
			case 'C':
				segment.Kind = GeometryCubic
				segment.Control1 = end
				segment.Control2 = geometryPoint(v[2], v[3], current, relative)
				segment.Point = geometryPoint(v[4], v[5], current, relative)
			case 'Q', 'S':
				segment.Kind = GeometryQuadratic
				segment.Control1 = end
				segment.Point = geometryPoint(v[2], v[3], current, relative)
				if upper == 'S' {
					segment.Kind = GeometryCubic
					segment.Control2 = end
					segment.Control1 = current
					if n := len(figure.Segments); n > 0 && figure.Segments[n-1].Kind == GeometryCubic {
						last := figure.Segments[n-1].Control2
						segment.Control1 = Point{current.X + (current.X - last.X), current.Y + (current.Y - last.Y)}
					}
				}
			case 'A':
				if v[0] < 0 || v[1] < 0 {
					p.fail("arc radii must not be negative")
				}
				segment = GeometrySegment{
					Kind: GeometryArc, Point: geometryPoint(v[5], v[6], current, relative),
					RadiusX: v[0], RadiusY: v[1], RotationAngle: v[2],
					IsLargeArc: v[3] == 1, SweepClockwise: v[4] == 1,
					IsStroked: true,
				}
			}
			if !geometryFinite(segment.Point.X, segment.Point.Y, segment.Control1.X, segment.Control1.Y, segment.Control2.X, segment.Control2.Y) {
				p.fail("resolved coordinates exceed finite float64 range")
			}
			current = segment.Point
			if upper != 'M' {
				if charge != nil {
					if err := charge(0, 1); err != nil {
						return nil, err
					}
				}
				figure.Segments = append(figure.Segments, segment)
			}
			space := p.space()
			next := p.peek()
			if next != '+' && next != '-' && next != '.' && (next < '0' || next > '9') {
				break
			}
			if upper == 'M' {
				p.fail("M accepts exactly one point; use an explicit L command")
			} else if !space {
				p.fail("repeated parameters require whitespace")
			}
		}
	}
	if p.err != nil {
		return nil, p.err
	}
	return g, nil
}

// Bounds 计算直线、贝塞尔曲线、椭圆弧及孤立起点的局部轴对齐边界，空几何返回零矩形
// 不应用Transform也不计描边宽度，超出浮点表示范围返回ErrLimit
// 返回: Rect 几何边界, error 错误信息
func (g *Geometry) Bounds() (Rect, error) {
	var minX, minY, maxX, maxY float64
	have := false
	if g == nil {
		return Rect{}, fmt.Errorf("%w: nil geometry", ErrInvalid)
	}
	for _, f := range g.Figures {
		current := f.StartPoint
		if !geometryFinite(current.X, current.Y) {
			return Rect{}, fmt.Errorf("%w: non-finite figure coordinate", ErrInvalid)
		}
		points := []Point{current}
		for _, s := range f.Segments {
			if !geometryFinite(s.Point.X, s.Point.Y) {
				return Rect{}, fmt.Errorf("%w: non-finite segment coordinate", ErrInvalid)
			}
			points = append(points, s.Point)
			switch s.Kind {
			case GeometryLine:
			case GeometryQuadratic, GeometryCubic:
				controls := []Point{current, s.Control1, s.Point}
				if s.Kind == GeometryCubic {
					controls = []Point{current, s.Control1, s.Control2, s.Point}
				}
				for _, p := range controls {
					if !geometryFinite(p.X, p.Y) {
						return Rect{}, fmt.Errorf("%w: non-finite curve coordinate", ErrInvalid)
					}
				}
				for _, axis := range []bool{false, true} {
					for _, t := range geometryExtrema(controls, axis) {
						if t > 0 && t < 1 {
							points = append(points, geometryBezier(controls, t))
						}
					}
				}
			case GeometryArc:
				extrema, err := geometryArcExtrema(current, s)
				if err != nil {
					return Rect{}, err
				}
				points = append(points, extrema...)
			default:
				return Rect{}, fmt.Errorf("%w: unknown geometry segment kind %d", ErrInvalid, s.Kind)
			}
			current = s.Point
		}
		for _, p := range points {
			if !geometryFinite(p.X, p.Y) {
				return Rect{}, fmt.Errorf("%w: computed coordinate exceeds finite float64 range", ErrLimit)
			}
			if !have {
				minX, minY, maxX, maxY, have = p.X, p.Y, p.X, p.Y, true
			}
			minX, minY = math.Min(minX, p.X), math.Min(minY, p.Y)
			maxX, maxY = math.Max(maxX, p.X), math.Max(maxY, p.Y)
		}
	}
	r := Rect{minX, minY, maxX - minX, maxY - minY}
	if r.X+r.Width < maxX {
		r.Width = math.Nextafter(r.Width, math.Inf(1))
	}
	if r.Y+r.Height < maxY {
		r.Height = math.Nextafter(r.Height, math.Inf(1))
	}
	if !geometryFinite(r.Width, r.Height) {
		return Rect{}, fmt.Errorf("%w: bounds exceed finite float64 range", ErrLimit)
	}
	return r, nil
}

// geometryArcExtrema 由椭圆弧端点参数方程求解轴向极值候选点
// 入参: start 圆弧起点, s 具有绝对终点的圆弧线段
// 返回: []Point 轴向边界候选点，各点仅一个分量对应弧段极值, error 错误信息
func geometryArcExtrema(start Point, s GeometrySegment) ([]Point, error) {
	rx, ry := s.RadiusX, s.RadiusY
	if !geometryFinite(rx, ry, s.RotationAngle) || rx < 0 || ry < 0 {
		return nil, fmt.Errorf("%w: invalid arc radii or rotation", ErrInvalid)
	}
	if start == s.Point || rx == 0 || ry == 0 {
		return nil, nil
	}
	if max(math.Abs(start.X), math.Abs(start.Y), math.Abs(s.Point.X), math.Abs(s.Point.Y), rx, ry) < 0x1p-500 {
		scaled := s
		scaled.RadiusX, scaled.RadiusY = math.Ldexp(rx, 512), math.Ldexp(ry, 512)
		scaled.Point = Point{math.Ldexp(s.Point.X, 512), math.Ldexp(s.Point.Y, 512)}
		points, err := geometryArcExtrema(Point{math.Ldexp(start.X, 512), math.Ldexp(start.Y, 512)}, scaled)
		if err != nil {
			return nil, err
		}
		var result []Point
		for _, p := range points {
			low, high := Point{}, Point{}
			low.X, high.X = geometryUnscaleInterval(p.X, 512)
			low.Y, high.Y = geometryUnscaleInterval(p.Y, 512)
			result = append(result, low, high)
		}
		return result, nil
	}
	sin, cos := geometryArcRotation(s.RotationAngle)
	dx, dy := geometryHalfDifference(start.X, s.Point.X), geometryHalfDifference(start.Y, s.Point.Y)
	chordExponent := 0
	if dx == 0 && dy == 0 {
		dx, dy = math.Ldexp(start.X-s.Point.X, 512)/2, math.Ldexp(start.Y-s.Point.Y, 512)/2
		chordExponent = -512
	}
	x := geometryLinearCombination(0, cos, dx, sin, dy)
	y := geometryLinearCombination(0, -sin, dx, cos, dy)
	if !geometryFinite(x, y) {
		return nil, fmt.Errorf("%w: rotated arc chord exceeds finite float64 range", ErrLimit)
	}
	u, v, norm, exponent := geometryArcRatios(x, rx, y, ry)
	exponent += chordExponent
	h := math.Ldexp(norm, exponent)
	if h > 1 {
		mx, ex := math.Frexp(rx)
		my, ey := math.Frexp(ry)
		rx, ry = math.Ldexp(mx*norm, ex+exponent), math.Ldexp(my*norm, ey+exponent)
		h = 1
		norm, exponent = 1, 0
	}
	if !geometryFinite(rx, ry) || norm == 0 {
		return nil, fmt.Errorf("%w: arc normalization exceeds float64 range", ErrLimit)
	}
	k := math.Sqrt((1 - h) * (1 + h))
	if s.IsLargeArc == s.SweepClockwise {
		k = -k
	}
	sweep := 2 * math.Asin(h)
	if s.IsLargeArc {
		sweep = 2*math.Pi - sweep
	}
	ax, bx, ay, by := rx*cos, -ry*sin, rx*sin, ry*cos
	var points []Point
	for axis, coefficients := range [][2]float64{{ax, bx}, {ay, by}} {
		support := math.Hypot(coefficients[0], coefficients[1])
		if !geometryFinite(support) {
			return nil, fmt.Errorf("%w: arc axis radius exceeds finite float64 range", ErrLimit)
		}
		if support == 0 {
			continue
		}
		chord, first, last := dx, start.X, s.Point.X
		if axis == 1 {
			chord, first, last = dy, start.Y, s.Point.Y
		}
		mc, ec := math.Frexp(chord)
		ms, es := math.Frexp(support)
		projection := math.Ldexp(mc/ms/norm, ec-es-exponent+chordExponent)
		projection = max(-1, min(1, projection))
		perpendicular := math.Copysign(math.Sqrt((1-projection)*(1+projection)), geometryLinearCombination(0, coefficients[1], u, -coefficients[0], v))
		midpoint := geometryHalfDifference(first, -last)
		tolerance := 32 * 0x1p-52 * min(1, sweep)
		for _, sign := range []float64{1, -1} {
			cross := sign * math.FMA(h, perpendicular, -k*projection)
			angle := math.Atan2(cross, sign*math.FMA(h, projection, k*perpendicular))
			if !s.SweepClockwise {
				angle = -angle
			}
			if (angle < -tolerance && (sweep < math.Pi || angle+2*math.Pi > sweep+tolerance)) || angle > sweep+tolerance {
				continue
			}
			centerOffset := k * perpendicular
			value := 0.0
			if sign*centerOffset >= 0 {
				gap := (geometryProductSquare(support, h) + geometryProductSquare(support, k*projection)) / (1 + math.Abs(centerOffset))
				value = midpoint + sign*gap
			} else {
				value = geometryLinearCombination(midpoint, support, sign, -support, centerOffset)
			}
			if !geometryFinite(value) {
				return nil, fmt.Errorf("%w: arc extrema exceed finite float64 range", ErrLimit)
			}
			p := start
			if axis == 0 {
				p.X = value
			} else {
				p.Y = value
			}
			points = append(points, p)
		}
	}
	return points, nil
}

// geometryUnscaleInterval 将缩放结果转换为向外舍入的区间，保留次正规数边界
// 入参: value 缩放后的数值, exponent 缩放指数
// 返回: float64 下界, float64 上界
func geometryUnscaleInterval(value float64, exponent int) (float64, float64) {
	v := math.Ldexp(value, -exponent)
	restored := math.Ldexp(v, exponent)
	if restored > value {
		return math.Nextafter(v, math.Inf(-1)), v
	}
	if restored < value {
		return v, math.Nextafter(v, math.Inf(1))
	}
	return v, v
}

// geometryArcRatios 用独立指数计算归一化弦向量，避免半径比例运算溢出
// 入参: x 横向半弦, rx 横向半径, y 纵向半弦, ry 纵向半径
// 返回: float64 横向单位分量, float64 纵向单位分量, float64 长度尾数, int 长度指数
func geometryArcRatios(x, rx, y, ry float64) (float64, float64, float64, int) {
	mx, ex := math.Frexp(x)
	mrx, erx := math.Frexp(rx)
	my, ey := math.Frexp(y)
	mry, ery := math.Frexp(ry)
	ex, ey = ex-erx, ey-ery
	exponent := max(ex, ey)
	if x == 0 {
		exponent = ey
	} else if y == 0 {
		exponent = ex
	}
	u, v := math.Ldexp(mx/mrx, ex-exponent), math.Ldexp(my/mry, ey-exponent)
	norm := math.Hypot(u, v)
	return u / norm, v / norm, norm, exponent
}

// geometryArcRotation 归约角度并保留直角的精确零值
// 入参: degrees 以度计的有限旋转角
// 返回: float64 正弦, float64 余弦
func geometryArcRotation(degrees float64) (float64, float64) {
	degrees = math.Remainder(degrees, 360)
	quadrant := math.Round(degrees / 90)
	sin, cos := math.Sincos((degrees - quadrant*90) * (math.Pi / 180))
	switch int(quadrant) {
	case 1:
		return cos, -sin
	case -1:
		return -cos, sin
	case 2, -2:
		return -sin, -cos
	default:
		return sin, cos
	}
}

// geometryHalfDifference 计算半差并规避异号大数相减溢出
// 入参: a 被减数, b 减数
// 返回: float64 半差
func geometryHalfDifference(a, b float64) float64 {
	d := a - b
	if math.IsInf(d, 0) {
		return a/2 - b/2
	}
	return d / 2
}

// geometryLinearCombination 计算含常数的二项线性组合，必要时精确消除中间溢出
// 入参: base 常数, a 第一系数, x 第一变量, b 第二系数, y 第二变量
// 返回: float64 舍入后的线性组合
func geometryLinearCombination(base, a, x, b, y float64) float64 {
	v := math.FMA(a, x, math.FMA(b, y, base))
	if geometryFinite(v) {
		return v
	}
	r := new(big.Rat).SetFloat64(base)
	r.Add(r, new(big.Rat).Mul(new(big.Rat).SetFloat64(a), new(big.Rat).SetFloat64(x)))
	r.Add(r, new(big.Rat).Mul(new(big.Rat).SetFloat64(b), new(big.Rat).SetFloat64(y)))
	v, _ = r.Float64()
	return v
}

// geometryProductSquare 按指数分解计算平方乘积，避免中间平方下溢
// 入参: factor 乘数, value 待平方数值
// 返回: float64 factor*value*value
func geometryProductSquare(factor, value float64) float64 {
	mf, ef := math.Frexp(factor)
	mv, ev := math.Frexp(value)
	return math.Ldexp(mf*mv*mv, ef+2*ev)
}

// geometryExtrema 求贝塞尔单轴驻点
// 入参: points 控制点, y 是否使用纵坐标
// 返回: []float64 导数的实根候选值
func geometryExtrema(points []Point, y bool) []float64 {
	var v [4]float64
	scale := 0.0
	for i, p := range points {
		v[i] = p.X
		if y {
			v[i] = p.Y
		}
		scale = math.Max(scale, math.Abs(v[i]))
	}
	if scale == 0 {
		return nil
	}
	for i := range points {
		v[i] /= scale
	}
	u, w := v[1]-v[0], v[2]-v[1]
	if len(points) == 3 {
		if u == w {
			return nil
		}
		return []float64{u / (u - w)}
	}
	a, b, c := u-2*w+(v[3]-v[2]), 2*(w-u), u
	if a == 0 {
		if b == 0 {
			return nil
		}
		return []float64{-c / b}
	}
	d := b*b - 4*a*c
	if d < 0 {
		return nil
	}
	if d == 0 {
		return []float64{-b / (2 * a)}
	}
	q := -0.5 * (b + math.Copysign(math.Sqrt(d), b))
	return []float64{q / a, c / q}
}

// geometryBezier 通过de Casteljau插值计算贝塞尔曲线点
// 入参: points 二次或三次控制点, t 曲线参数
// 返回: Point 插值坐标
func geometryBezier(points []Point, t float64) Point {
	var work [4]Point
	copy(work[:], points)
	for n := len(points) - 1; n > 0; n-- {
		for i := 0; i < n; i++ {
			work[i] = Point{(1-t)*work[i].X + t*work[i+1].X, (1-t)*work[i].Y + t*work[i+1].Y}
		}
	}
	return work[0]
}

// geometryPoint 换算绝对坐标
// 入参: x 横坐标, y 纵坐标, base 基点, relative 是否使用相对坐标
// 返回: Point 绝对坐标点
func geometryPoint(x, y float64, base Point, relative bool) Point {
	if relative {
		x, y = x+base.X, y+base.Y
	}
	return Point{x, y}
}

// geometryFinite 检查有限数值
// 入参: values 浮点数列表
// 返回: bool 所有数值均非NaN或无穷时为真
func geometryFinite(values ...float64) bool {
	for _, v := range values {
		if math.IsNaN(v) || math.IsInf(v, 0) {
			return false
		}
	}
	return true
}

// peek 查看当前字节
// 返回: byte 当前字节，结束时返回零
func (p *geometryScanner) peek() byte {
	if p.pos == len(p.text) {
		return 0
	}
	return p.text[p.pos]
}

// fail 记录首个错误
// 入参: message 错误原因
func (p *geometryScanner) fail(message string) {
	if p.err == nil {
		p.err = &GeometrySyntaxError{p.pos, message}
	}
}

// space 跳过XML空白
// 返回: bool 是否消费至少一个空格、制表符或换行符
func (p *geometryScanner) space() bool {
	start := p.pos
	for p.pos < len(p.text) {
		switch p.text[p.pos] {
		case ' ', '\t', '\r', '\n':
			p.pos++
		default:
			return p.pos != start
		}
	}
	return p.pos != start
}

// separator 消费指定分隔符，缺失时记录错误
// 入参: kind 逗号或必需空白
func (p *geometryScanner) separator(kind byte) {
	if p.err != nil {
		return
	}
	space := p.space()
	if kind == ' ' {
		if !space {
			p.fail("expected whitespace between parameters")
		}
		return
	}
	if p.peek() != ',' {
		p.fail("expected comma between coordinates")
		return
	}
	p.pos++
	p.space()
}

// flag 消费单字符布尔标志，其他字符记录错误
// 返回: byte 标志值0或1
func (p *geometryScanner) flag() byte {
	if p.err != nil {
		return 0
	}
	b := p.peek()
	if b != '0' && b != '1' {
		p.fail("expected flag 0 or 1")
		return 0
	}
	p.pos++
	return b - '0'
}

// number 消费规范实数，禁止尾随小数点、十六进制及非数值字面量
// 返回: float64 有限实数，失败时记录错误
func (p *geometryScanner) number() float64 {
	if p.err != nil {
		return 0
	}
	start := p.pos
	if p.peek() == '+' || p.peek() == '-' {
		p.pos++
	}
	digits := p.digits()
	if p.peek() == '.' {
		p.pos++
		if !p.digits() {
			p.fail("decimal point must be followed by digits")
			return 0
		}
	} else if !digits {
		p.fail("expected decimal number")
		return 0
	}
	if p.peek() == 'e' || p.peek() == 'E' {
		p.pos++
		if p.peek() == '+' || p.peek() == '-' {
			p.pos++
		}
		if !p.digits() {
			p.fail("exponent must contain digits")
			return 0
		}
	}
	v, err := strconv.ParseFloat(p.text[start:p.pos], 64)
	if err != nil || !geometryFinite(v) {
		p.fail("number exceeds finite float64 range")
	}
	return v
}

// digits 消费十进制数字
// 返回: bool 是否至少消费一位数字
func (p *geometryScanner) digits() bool {
	start := p.pos
	for p.peek() >= '0' && p.peek() <= '9' {
		p.pos++
	}
	return p.pos != start
}

// geometryFillEdges 按几何与设备变换将填充子路径细分展开为有向设备边，隐式闭合各填充轮廓
// 入参: g 输入几何, transform 设备变换, tolerance 正的有限误差容限, maxEdges 非负输出边数及细分预算
// 返回: []geometryEdge 有向填充边, error 非法输入、预算或数值范围错误
func geometryFillEdges(g *Geometry, transform Matrix, tolerance float64, maxEdges int) ([]geometryEdge, error) {
	if g == nil || !geometryFinite(tolerance) || tolerance <= 0 || maxEdges < 0 {
		return nil, fmt.Errorf("%w: invalid fill geometry or flattening parameters", ErrInvalid)
	}
	if g.FillRule != GeometryEvenOdd && g.FillRule != GeometryNonZero {
		return nil, fmt.Errorf("%w: invalid geometry fill rule", ErrInvalid)
	}
	if !geometryFillMatrixFinite(transform) || (g.Transform != nil && !geometryFillMatrixFinite(*g.Transform)) {
		return nil, fmt.Errorf("%w: non-finite fill transform", ErrInvalid)
	}
	if g.Transform != nil {
		transform = strokePathCompose(transform, *g.Transform)
		if !geometryFillMatrixFinite(transform) {
			return nil, fmt.Errorf("%w: fill transform composition overflow", ErrLimit)
		}
	}
	for _, figure := range g.Figures {
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return nil, fmt.Errorf("%w: non-finite fill start point", ErrInvalid)
		}
		for _, segment := range figure.Segments {
			if err := geometryFillValidateSegment(segment); err != nil {
				return nil, err
			}
		}
	}
	b := geometryFillBuilder{tolerance: tolerance, maxEdges: maxEdges}
	for _, figure := range g.Figures {
		if !figure.IsFilled {
			continue
		}
		start, err := geometryFillPoint(transform, figure.StartPoint)
		if err != nil {
			return nil, err
		}
		current, device := figure.StartPoint, start
		for _, segment := range figure.Segments {
			end, err := geometryFillPoint(transform, segment.Point)
			if err != nil {
				return nil, err
			}
			switch segment.Kind {
			case GeometryLine:
				err = b.edge(device, end)
			case GeometryQuadratic, GeometryCubic:
				var points [4]Point
				points[0] = device
				points[1], err = geometryFillPoint(transform, segment.Control1)
				n := 3
				if err == nil && segment.Kind == GeometryCubic {
					points[2], err = geometryFillPoint(transform, segment.Control2)
					n = 4
				}
				points[n-1] = end
				if err == nil {
					err = b.bezier(points, n, 0)
				}
			case GeometryArc:
				err = b.arc(current, segment, transform, device, end)
			}
			if err != nil {
				return nil, err
			}
			current, device = segment.Point, end
		}
		if err := b.edge(device, start); err != nil {
			return nil, err
		}
	}
	return b.edges, nil
}

// geometryFillMatrixFinite 检查仿射系数，不要求矩阵可逆
// 入参: m 待检查矩阵
// 返回: bool 系数是否均为有限值
func geometryFillMatrixFinite(m Matrix) bool {
	return geometryFinite(m.A, m.B, m.C, m.D, m.E, m.F)
}

// geometryFillValidateSegment 检查线段枚举及其有效参数，不解释未使用的控制点字段
// 入参: s 待检查线段
// 返回: error 非法线段错误
func geometryFillValidateSegment(s GeometrySegment) error {
	valid := geometryFinite(s.Point.X, s.Point.Y)
	switch s.Kind {
	case GeometryLine:
	case GeometryQuadratic:
		valid = valid && geometryFinite(s.Control1.X, s.Control1.Y)
	case GeometryCubic:
		valid = valid && geometryFinite(s.Control1.X, s.Control1.Y, s.Control2.X, s.Control2.Y)
	case GeometryArc:
		valid = valid && geometryFinite(s.RadiusX, s.RadiusY, s.RotationAngle) && s.RadiusX >= 0 && s.RadiusY >= 0
	default:
		valid = false
	}
	if !valid {
		return fmt.Errorf("%w: invalid fill segment", ErrInvalid)
	}
	return nil
}

// geometryFillPoint 计算设备坐标并检测结果溢出，允许有限乘积间的精确抵消
// 入参: m 有限仿射矩阵, p 有限坐标
// 返回: Point 设备坐标, error 超出浮点表示范围的错误
func geometryFillPoint(m Matrix, p Point) (Point, error) {
	q := Point{geometryLinearCombination(m.E, m.A, p.X, m.C, p.Y), geometryLinearCombination(m.F, m.B, p.X, m.D, p.Y)}
	if !geometryFinite(q.X, q.Y) {
		return Point{}, fmt.Errorf("%w: fill coordinate overflow", ErrLimit)
	}
	return q, nil
}

// edge 添加非退化有向边，分配前检查调用者给定的边数预算
// 入参: start 设备空间起点, end 设备空间终点
// 返回: error 边数预算错误
func (b *geometryFillBuilder) edge(start, end Point) error {
	if start == end {
		return nil
	}
	if len(b.edges) >= b.maxEdges {
		return fmt.Errorf("%w: fill edge budget exceeded", ErrLimit)
	}
	b.edges = append(b.edges, geometryEdge{start, end})
	return nil
}

// bezier 以控制多边形与同参数弦的偏差上界细分，保留闭环及共线回折
// 入参: points 设备空间控制点, n 控制点数量, depth 当前细分深度
// 返回: error 边数、细分或精度预算错误
func (b *geometryFillBuilder) bezier(points [4]Point, n, depth int) error {
	flat := true
	for i := 1; i < n-1; i++ {
		t := float64(i) / float64(n-1)
		chord := points[0]
		if points[0] != points[n-1] {
			chord = Point{geometryLinearCombination(0, 1-t, points[0].X, t, points[n-1].X), geometryLinearCombination(0, 1-t, points[0].Y, t, points[n-1].Y)}
		}
		if math.Hypot(points[i].X-chord.X, points[i].Y-chord.Y) > b.tolerance {
			flat = false
			break
		}
	}
	if flat {
		return b.edge(points[0], points[n-1])
	}
	if depth >= 64 || b.splits >= b.maxEdges {
		return fmt.Errorf("%w: fill curve subdivision budget exceeded", ErrLimit)
	}
	b.splits++
	work, left, right := points, [4]Point{}, [4]Point{}
	left[0], right[n-1] = points[0], points[n-1]
	for level := 1; level < n; level++ {
		for i := 0; i < n-level; i++ {
			work[i] = Point{geometryHalfDifference(work[i].X, -work[i+1].X), geometryHalfDifference(work[i].Y, -work[i+1].Y)}
		}
		left[level], right[n-level-1] = work[0], work[n-level-1]
	}
	if err := b.bezier(left, n, depth+1); err != nil {
		return err
	}
	return b.bezier(right, n, depth+1)
}

// arc 按端点参数方程与设备空间误差界将椭圆弧细分为有向线段
// 入参: start 局部起点, s 弧参数, m 设备变换, first 设备起点, last 设备终点
// 返回: error 数值表示或边数预算错误
func (b *geometryFillBuilder) arc(start Point, s GeometrySegment, m Matrix, first, last Point) error {
	if start == s.Point {
		return nil
	}
	if s.RadiusX == 0 || s.RadiusY == 0 {
		return b.edge(first, last)
	}
	if m.A == 0 && m.B == 0 && m.C == 0 && m.D == 0 {
		return nil
	}
	if max(math.Abs(start.X), math.Abs(start.Y), math.Abs(s.Point.X), math.Abs(s.Point.Y), s.RadiusX, s.RadiusY) < 0x1p-500 {
		start = Point{math.Ldexp(start.X, 512), math.Ldexp(start.Y, 512)}
		s.Point = Point{math.Ldexp(s.Point.X, 512), math.Ldexp(s.Point.Y, 512)}
		s.RadiusX, s.RadiusY = math.Ldexp(s.RadiusX, 512), math.Ldexp(s.RadiusY, 512)
		m.A, m.B, m.C, m.D = math.Ldexp(m.A, -512), math.Ldexp(m.B, -512), math.Ldexp(m.C, -512), math.Ldexp(m.D, -512)
		return b.arc(start, s, m, first, last)
	}
	rx, ry := s.RadiusX, s.RadiusY
	sin, cos := geometryArcRotation(s.RotationAngle)
	dx, dy := geometryHalfDifference(start.X, s.Point.X), geometryHalfDifference(start.Y, s.Point.Y)
	chordExponent := 0
	if dx == 0 && dy == 0 {
		dx, dy = math.Ldexp(start.X-s.Point.X, 512)/2, math.Ldexp(start.Y-s.Point.Y, 512)/2
		chordExponent = -512
	}
	x, y := geometryLinearCombination(0, cos, dx, sin, dy), geometryLinearCombination(0, -sin, dx, cos, dy)
	if !geometryFinite(x, y) {
		return fmt.Errorf("%w: fill arc chord overflow", ErrLimit)
	}
	u, v, norm, exponent := geometryArcRatios(x, rx, y, ry)
	if !geometryFinite(u, v, norm) || norm <= 0 {
		return fmt.Errorf("%w: fill arc chord precision exhausted", ErrLimit)
	}
	exponent += chordExponent
	h := math.Ldexp(norm, exponent)
	if h > 1 {
		mx, ex := math.Frexp(rx)
		my, ey := math.Frexp(ry)
		rx, ry = math.Ldexp(mx*norm, ex+exponent), math.Ldexp(my*norm, ey+exponent)
		h = 1
	}
	if !geometryFinite(rx, ry) {
		return fmt.Errorf("%w: fill arc normalization overflow", ErrLimit)
	}
	k := math.Sqrt((1 - h) * (1 + h))
	if s.IsLargeArc == s.SweepClockwise {
		k = -k
	}
	nx, ny := math.FMA(h, u, -k*v), math.FMA(h, v, k*u)
	linear := m
	linear.E, linear.F = 0, 0
	a, err := geometryFillPoint(linear, Point{rx * cos, rx * sin})
	if err != nil {
		return err
	}
	d, err := geometryFillPoint(linear, Point{-ry * sin, ry * cos})
	if err != nil {
		return err
	}
	p, err := geometryFillPoint(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{nx, ny})
	if err != nil {
		return err
	}
	q, err := geometryFillPoint(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{-ny, nx})
	if err != nil {
		return err
	}
	span := 2 * math.Asin(h)
	if s.IsLargeArc {
		span = 2*math.Pi - span
	}
	if !s.SweepClockwise {
		span = -span
	}
	scale := max(math.Abs(p.X), math.Abs(p.Y), math.Abs(q.X), math.Abs(q.Y))
	count, step := 1, span
	for math.Sqrt2*geometryProductSquare(scale, step/2) > b.tolerance/2 {
		if count > (b.maxEdges-len(b.edges))/2 {
			return fmt.Errorf("%w: fill arc subdivision budget exceeded", ErrLimit)
		}
		count *= 2
		step /= 2
	}
	computed, err := geometryFillArcPoint(first, p, q, span)
	if err != nil {
		return err
	}
	maxCoord := max(math.Abs(first.X), math.Abs(first.Y), math.Abs(last.X), math.Abs(last.Y), scale)
	if math.Hypot(computed.X-last.X, computed.Y-last.Y) > max(b.tolerance/2, 1e-9*max(1, maxCoord)) {
		return fmt.Errorf("%w: fill arc endpoint precision exceeds tolerance", ErrLimit)
	}
	previous := first
	for i := 1; i <= count; i++ {
		next := last
		if i != count {
			next, err = geometryFillArcPoint(first, p, q, step*float64(i))
			if err != nil {
				return err
			}
		}
		if err := b.edge(previous, next); err != nil {
			return err
		}
		previous = next
	}
	return nil
}

// geometryFillArcPoint 以相对角求设备空间弧点，避免直接计算cos(angle)-1的消减误差
// 入参: start 设备起点, p 径向向量, q 切向向量, angle 相对参数角
// 返回: Point 弧点, error 超出数值范围的错误
func geometryFillArcPoint(start, p, q Point, angle float64) (Point, error) {
	s := math.Sin(angle / 2)
	return geometryFillPoint(Matrix{A: p.X, B: p.Y, C: q.X, D: q.Y, E: start.X, F: start.Y}, Point{-2 * s * s, math.Sin(angle)})
}

// ParseGeometryXML 解析独立的PathGeometry XML元素并执行标记兼容性预处理，零值或nil上限采用默认值
// 独立元素不允许资源键，依赖资源字典的变换引用返回ErrUnsupported
// 入参: ctx 取消Context，nil采用Background, data 包含命名空间声明的XML数据, limits 可选XML资源上限，nil采用默认值
// 返回: *Geometry 保留局部变换及填充和描边标志的几何, error XML、语法、预算或取消错误
func ParseGeometryXML(ctx context.Context, data []byte, limits *Limits) (*Geometry, error) {
	ctx = normalizeContext(ctx)
	effective := DefaultLimits()
	if limits != nil {
		effective = mergeLimits(effective, *limits)
	}
	if err := validateLimits(effective); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if int64(len(data)) > min(effective.MaxPartBytes, effective.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: geometry XML exceeds part byte limit", ErrLimit)
	}
	root, err := decodeXMLReader(bytes.NewReader(data), effective, ctx, nil)
	if err != nil {
		return nil, err
	}
	ns := root.Name.Space
	if ns != xpsNamespace && ns != openXPSNamespace {
		return nil, fmt.Errorf("%w: geometry namespace %q", ErrUnsupported, ns)
	}
	root, err = preprocessXMLContext(root, []string{ns, ns + "/resourcedictionary-key"}, ctx)
	if err != nil {
		return nil, err
	}
	return parseGeometryElementLimited(root, nil, false, func(int, int) error { return checkContext(ctx) }, nil)
}

// parseGeometryElementLimited 复用只读轮廓但始终重新解析变换，避免跨页资源绑定串用
// 入参: node 几何节点, resolveMatrix 当前作用域矩阵解析器, resource 是否为定义, charge 容量回调, shared 同源已校验轮廓
// 返回: *Geometry 独立外壳及局部变换, error 校验、预算或取消错误
func parseGeometryElementLimited(node *xmlElement, resolveMatrix func(string) (Matrix, error), resource bool, charge func(int, int) error, shared *Geometry) (*Geometry, error) {
	if node == nil || node.Name.Space != xpsNamespace && node.Name.Space != openXPSNamespace {
		return nil, fmt.Errorf("%w: invalid geometry element namespace", ErrInvalid)
	}
	ns := node.Name.Space
	a, err := geometryXMLAttributes(node, ns, "PathGeometry", resource, "Figures", "FillRule", "Transform")
	if err != nil {
		return nil, err
	}
	g := &Geometry{}
	if shared != nil {
		g.Figures = shared.Figures
	}
	if value, ok := a["FillRule"]; ok {
		switch value {
		case "EvenOdd":
		case "NonZero":
			g.FillRule = GeometryNonZero
		default:
			return nil, fmt.Errorf("%w: invalid FillRule %q", ErrInvalid, value)
		}
	}
	figures, hasFigures := a["Figures"]
	transform, hasTransform := a["Transform"]
	for i, child := range node.Children {
		if child.Name.Space == ns && child.Name.Local == "PathGeometry.Transform" {
			if i != 0 || hasTransform {
				return nil, fmt.Errorf("%w: Transform must occur once before figures", ErrInvalid)
			}
			if _, err := geometryXMLAttributes(child, ns, "PathGeometry.Transform", false); err != nil {
				return nil, err
			}
			if len(child.Children) != 1 {
				return nil, fmt.Errorf("%w: Transform requires one MatrixTransform", ErrInvalid)
			}
			matrix := child.Children[0]
			attrs, err := geometryXMLAttributes(matrix, ns, "MatrixTransform", false, "Matrix")
			if err != nil {
				return nil, err
			}
			if len(matrix.Children) != 0 {
				return nil, fmt.Errorf("%w: MatrixTransform cannot contain children", ErrInvalid)
			}
			value, err := geometryXMLRequired(attrs, "Matrix")
			if err != nil {
				return nil, err
			}
			m, err := ParseMatrix(value)
			if err != nil {
				return nil, fmt.Errorf("Matrix: %w", err)
			}
			g.Transform = &m
			continue
		}
		if hasFigures {
			return nil, fmt.Errorf("%w: Figures cannot be combined with child figures", ErrInvalid)
		}
		if shared != nil {
			continue
		}
		figure, err := geometryXMLFigureLimited(child, ns, charge)
		if err != nil {
			return nil, err
		}
		g.Figures = append(g.Figures, figure)
	}
	if hasFigures && shared == nil {
		if strings.HasPrefix(strings.TrimLeft(figures, " \t\r\n"), "F") {
			return nil, fmt.Errorf("%w: Figures cannot specify F0 or F1", ErrInvalid)
		}
		parsed, err := parseGeometryLimited(figures, charge)
		if err != nil {
			return nil, fmt.Errorf("Figures: %w", err)
		}
		g.Figures = parsed.Figures
	}
	if hasTransform {
		m, err := geometryXMLTransform(transform, resolveMatrix)
		if err != nil {
			return nil, fmt.Errorf("Transform: %w", err)
		}
		g.Transform = &m
	}
	return g, nil
}

// geometryXMLFigureLimited 在展开子路径前计费，多段元素沿用同一累计预算
// 入参: node 子路径节点, ns 文档命名空间, charge 容量回调
// 返回: GeometryFigure 子路径, error 校验、预算或取消错误
func geometryXMLFigureLimited(node *xmlElement, ns string, charge func(int, int) error) (GeometryFigure, error) {
	if charge != nil {
		if err := charge(1, 0); err != nil {
			return GeometryFigure{}, err
		}
	}
	f := GeometryFigure{IsFilled: true}
	a, err := geometryXMLAttributes(node, ns, "PathFigure", false, "StartPoint", "IsClosed", "IsFilled")
	if err != nil {
		return GeometryFigure{}, err
	}
	value, err := geometryXMLRequired(a, "StartPoint")
	if err != nil {
		return GeometryFigure{}, err
	}
	points, err := geometryXMLPoints(value, true, false)
	if err != nil {
		return GeometryFigure{}, fmt.Errorf("StartPoint: %w", err)
	}
	f.StartPoint = points[0]
	if f.IsClosed, err = geometryXMLBool(a, "IsClosed", false); err != nil {
		return GeometryFigure{}, err
	}
	if f.IsFilled, err = geometryXMLBool(a, "IsFilled", true); err != nil {
		return GeometryFigure{}, err
	}
	if len(node.Children) == 0 {
		return GeometryFigure{}, fmt.Errorf("%w: PathFigure requires at least one segment", ErrInvalid)
	}
	for _, child := range node.Children {
		segments, err := geometryXMLSegmentsLimited(child, ns, charge)
		if err != nil {
			return GeometryFigure{}, err
		}
		f.Segments = append(f.Segments, segments...)
	}
	return f, nil
}

// geometryXMLSegmentsLimited 在点数组及语义段分配前检查容量，避免先展开大型Points
// 入参: node 段节点, ns 文档命名空间, charge 容量回调
// 返回: []GeometrySegment 规范化段, error 校验、预算或取消错误
func geometryXMLSegmentsLimited(node *xmlElement, ns string, charge func(int, int) error) ([]GeometrySegment, error) {
	if node == nil {
		return nil, fmt.Errorf("%w: nil segment", ErrInvalid)
	}
	name := node.Name.Local
	allowed := []string{"Points", "IsStroked"}
	stride, kind := 1, GeometryLine
	switch name {
	case "PolyLineSegment":
	case "PolyBezierSegment":
		stride, kind = 3, GeometryCubic
	case "PolyQuadraticBezierSegment":
		stride, kind = 2, GeometryQuadratic
	case "ArcSegment":
		allowed = []string{"Point", "Size", "RotationAngle", "IsLargeArc", "SweepDirection", "IsStroked"}
	default:
		return nil, fmt.Errorf("%w: unknown XPS segment %s", ErrInvalid, name)
	}
	a, err := geometryXMLAttributes(node, ns, name, false, allowed...)
	if err != nil {
		return nil, err
	}
	if len(node.Children) != 0 {
		return nil, fmt.Errorf("%w: %s cannot contain children", ErrInvalid, name)
	}
	stroked, err := geometryXMLBool(a, "IsStroked", true)
	if err != nil {
		return nil, err
	}
	if name == "ArcSegment" {
		if charge != nil {
			if err := charge(0, 1); err != nil {
				return nil, err
			}
		}
		for _, attr := range allowed[:5] {
			if _, err := geometryXMLRequired(a, attr); err != nil {
				return nil, err
			}
		}
		end, err := geometryXMLPoints(a["Point"], true, false)
		if err != nil {
			return nil, fmt.Errorf("Point: %w", err)
		}
		size, err := geometryXMLPoints(a["Size"], true, true)
		if err != nil {
			return nil, fmt.Errorf("Size: %w", err)
		}
		rotation, err := xmlNumber(a["RotationAngle"])
		if err != nil {
			return nil, fmt.Errorf("RotationAngle: %w", err)
		}
		large, err := geometryXMLBool(a, "IsLargeArc", false)
		if err != nil {
			return nil, err
		}
		sweep := a["SweepDirection"]
		if sweep != "Clockwise" && sweep != "Counterclockwise" {
			return nil, fmt.Errorf("%w: invalid SweepDirection %q", ErrInvalid, sweep)
		}
		return []GeometrySegment{{Kind: GeometryArc, Point: end[0], RadiusX: size[0].X, RadiusY: size[0].Y,
			RotationAngle: rotation, IsLargeArc: large, SweepClockwise: sweep == "Clockwise", IsStroked: stroked}}, nil
	}
	value, err := geometryXMLRequired(a, "Points")
	if err != nil {
		return nil, err
	}
	var pointCharge func(int) error
	if charge != nil {
		pointCharge = func(index int) error {
			if index%stride == 0 {
				return charge(0, 1)
			}
			return nil
		}
	}
	points, err := geometryXMLPointsLimited(value, false, false, pointCharge)
	if err != nil {
		return nil, fmt.Errorf("Points: %w", err)
	}
	if len(points)%stride != 0 {
		return nil, fmt.Errorf("%w: %s point count must be a multiple of %d", ErrInvalid, name, stride)
	}
	segments := make([]GeometrySegment, 0, len(points)/stride)
	for i := 0; i < len(points); i += stride {
		s := GeometrySegment{Kind: kind, Point: points[i+stride-1], IsStroked: stroked}
		if stride > 1 {
			s.Control1 = points[i]
		}
		if stride == 3 {
			s.Control2 = points[i+1]
		}
		segments = append(segments, s)
	}
	return segments, nil
}

// geometryXMLAttributes 校验元素名、文本、允许属性及资源键作用域
// 入参: node 元素, ns 命名空间, name 元素名称, resource 是否要求资源键, allowed 允许的无命名空间属性
// 返回: map[string]string 已校验属性, error 错误信息
func geometryXMLAttributes(node *xmlElement, ns, name string, resource bool, allowed ...string) (map[string]string, error) {
	if node == nil || node.Name != (xml.Name{Space: ns, Local: name}) {
		return nil, fmt.Errorf("%w: expected {%s}%s", ErrInvalid, ns, name)
	}
	if !xmlWhitespace(node.Text) {
		return nil, fmt.Errorf("%w: unexpected text in %s", ErrInvalid, name)
	}
	a := make(map[string]string)
	seen := make(map[xml.Name]bool)
	hasKey := false
	for _, attr := range node.Attr {
		if seen[attr.Name] {
			return nil, fmt.Errorf("%w: duplicate attribute %s", ErrInvalid, attr.Name.Local)
		}
		seen[attr.Name] = true
		if attr.Name.Space == xmlnsNamespace || attr.Name.Space == "" && attr.Name.Local == "xmlns" {
			continue
		}
		if resource && attr.Name.Space == ns+"/resourcedictionary-key" && attr.Name.Local == "Key" {
			if !fixedNamePattern(attr.Value) {
				return nil, fmt.Errorf("%w: invalid resource key %q", ErrInvalid, attr.Value)
			}
			hasKey = true
			continue
		}
		valid := false
		for _, key := range allowed {
			valid = valid || attr.Name.Space == "" && attr.Name.Local == key
		}
		if !valid {
			return nil, fmt.Errorf("%w: unexpected attribute {%s}%s on %s", ErrInvalid, attr.Name.Space, attr.Name.Local, name)
		}
		a[attr.Name.Local] = attr.Value
	}
	if resource && !hasKey {
		return nil, fmt.Errorf("%w: dictionary geometry requires a resource key", ErrInvalid)
	}
	return a, nil
}

// geometryXMLRequired 取得必须存在的属性，不将空字符串误作缺省值
// 入参: a 属性集合, name 属性名称
// 返回: string 属性文本, error 错误信息
func geometryXMLRequired(a map[string]string, name string) (string, error) {
	value, ok := a[name]
	if !ok {
		return "", fmt.Errorf("%w: missing %s", ErrInvalid, name)
	}
	return value, nil
}

// geometryXMLBool 按ST_Boolean解析布尔值，禁止数字布尔值
// 入参: a 属性集合, name 属性名, fallback 缺省值
// 返回: bool 属性值, error 错误信息
func geometryXMLBool(a map[string]string, name string, fallback bool) (bool, error) {
	value, ok := a[name]
	if !ok {
		return fallback, nil
	}
	switch strings.Trim(value, " \t\r\n") {
	case "true":
		return true, nil
	case "false":
		return false, nil
	default:
		return false, fmt.Errorf("%w: invalid %s boolean %q", ErrInvalid, name, value)
	}
}

// geometryXMLPoints 解析点或非空点集合，使用标准逗号及XML空白分隔
// 入参: text 属性文本, single 是否仅允许一个点, nonnegative 是否采用禁止负号的ST_PointGE0
// 返回: []Point 坐标集合, error 错误信息
func geometryXMLPoints(text string, single, nonnegative bool) ([]Point, error) {
	return geometryXMLPointsLimited(text, single, nonnegative, nil)
}

// geometryXMLPointsLimited 共用点词法解析，允许调用方在每个点追加前检查累计容量
// 入参: text 点文本, single 是否单点, nonnegative 是否非负, charge 零基点序号计费回调
// 返回: []Point 坐标集合, error 语法、预算或取消错误
func geometryXMLPointsLimited(text string, single, nonnegative bool, charge func(int) error) ([]Point, error) {
	p := geometryScanner{text: text}
	p.space()
	var points []Point
	for p.err == nil {
		var v [2]float64
		for i := range v {
			if i != 0 {
				p.separator(',')
			}
			if nonnegative && p.peek() == '-' {
				p.fail("ST_PointGE0 does not allow a negative sign")
			}
			v[i] = p.number()
		}
		if p.err != nil {
			break
		}
		if charge != nil {
			if err := charge(len(points)); err != nil {
				return nil, err
			}
		}
		points = append(points, Point{v[0], v[1]})
		space := p.space()
		if p.pos == len(text) {
			return points, nil
		}
		if single {
			p.fail("expected exactly one point")
		} else if !space {
			p.fail("expected whitespace between points")
		}
	}
	return nil, p.err
}

// geometryXMLTransform 解析矩阵属性或将合法资源键交给作用域解析器
// 入参: text 变换属性文本, resolve 资源解析回调
// 返回: Matrix 有限系数矩阵, error 错误信息
func geometryXMLTransform(text string, resolve func(string) (Matrix, error)) (Matrix, error) {
	trimmed := strings.TrimLeft(text, " \t\r\n")
	if !strings.HasPrefix(trimmed, "{") {
		return ParseMatrix(text)
	}
	p := geometryScanner{text: strings.TrimRight(trimmed, " \t\r\n")}
	const prefix = "{StaticResource"
	if !strings.HasPrefix(p.text, prefix) || !strings.HasSuffix(p.text, "}") {
		return Matrix{}, fmt.Errorf("%w: invalid matrix resource reference", ErrInvalid)
	}
	p.pos = len(prefix)
	if !p.space() || p.pos >= len(p.text)-1 {
		return Matrix{}, fmt.Errorf("%w: missing matrix resource key", ErrInvalid)
	}
	key := p.text[p.pos : len(p.text)-1]
	if !fixedNamePattern(key) {
		return Matrix{}, fmt.Errorf("%w: invalid matrix resource key %q", ErrInvalid, key)
	}
	if resolve == nil {
		return Matrix{}, fmt.Errorf("%w: matrix resource %q requires a resource scope", ErrUnsupported, key)
	}
	m, err := resolve(key)
	if err != nil {
		return Matrix{}, err
	}
	if !geometryFillMatrixFinite(m) {
		return Matrix{}, fmt.Errorf("%w: non-finite matrix resource %q", ErrInvalid, key)
	}
	return m, nil
}
