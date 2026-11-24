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
	"fmt"
	"math"
	"math/big"
	"sort"
)

// strokeCurve 保存描边空间中心线、正向端点单位切线及逐顶点累计弧长误差上界
type strokeCurve struct {
	points                   []Point
	lengthErrors             []float64
	startTangent, endTangent Point
	lengthError              float64
}

// strokeCurveBuilder 保存单段细分状态及调用者指定的误差和资源预算
type strokeCurveBuilder struct {
	result                     strokeCurve
	origin, last               Point
	device                     Matrix
	tolerance, lengthTolerance float64
	deviceNorm, originError    float64
	arcVectorError             float64
	maxPoints, splits          int
	angularTolerance, slope    float64
	angleSource                [4]strokeCurveExact
	angleInput                 [4]Point
	angleMatrix                Matrix
	arcStartZero, arcEndZero   bool
}

// strokeCurveExact 保存角度证书使用的精确二维控制点
type strokeCurveExact [2]*big.Rat

// strokeFlattenSegmentAngle 以独立位置、长度和描边空间切线角度约束展开原始段，pi禁用角度检查
// 入参: start 原始起点, segment 原始段, geometryTransform 几何变换, deviceTransform 设备变换, tolerance 设备位置容差, lengthTolerance 长度容差, angularTolerance 弧度角容差, maxPoints 点数及细分预算
// 返回: strokeCurve 中心线及原始端点切线, error 非法输入或无法证明误差界的资源及精度错误
func strokeFlattenSegmentAngle(start Point, segment GeometrySegment, geometryTransform, deviceTransform Matrix, tolerance, lengthTolerance, angularTolerance float64, maxPoints int) (strokeCurve, error) {
	if !geometryFinite(start.X, start.Y, tolerance, lengthTolerance, angularTolerance) || tolerance <= 0 || lengthTolerance <= 0 || angularTolerance <= 0 || angularTolerance > math.Pi || maxPoints < 0 || !geometryFillMatrixFinite(geometryTransform) || !geometryFillMatrixFinite(deviceTransform) {
		return strokeCurve{}, fmt.Errorf("%w: invalid stroke flattening parameters", ErrInvalid)
	}
	if err := geometryFillValidateSegment(segment); err != nil {
		return strokeCurve{}, err
	}
	if maxPoints < 2 {
		return strokeCurve{}, fmt.Errorf("%w: stroke point budget exceeded", ErrLimit)
	}
	first, firstError, err := strokeCurveAffine(geometryTransform, start, Point{}, false)
	if err != nil {
		return strokeCurve{}, err
	}
	last, _, err := strokeCurveAffine(geometryTransform, segment.Point, Point{}, false)
	if err != nil {
		return strokeCurve{}, err
	}
	deviceTransform.E, deviceTransform.F = 0, 0
	norm := math.Hypot(deviceTransform.A, deviceTransform.B) + math.Hypot(deviceTransform.C, deviceTransform.D)
	if deviceTransform.B == 0 && deviceTransform.C == 0 {
		norm = max(math.Abs(deviceTransform.A), math.Abs(deviceTransform.D))
	}
	b := strokeCurveBuilder{origin: first, last: last, device: deviceTransform, deviceNorm: norm, originError: firstError, tolerance: tolerance, lengthTolerance: lengthTolerance, maxPoints: maxPoints, angularTolerance: angularTolerance}
	if angularTolerance < math.Pi {
		b.slope = max(0, math.Nextafter(math.Tan(min(angularTolerance, math.Pi/2))*(1-0x1p-45), 0))
	}
	b.result.points = make([]Point, 1, 2)
	b.result.lengthErrors = make([]float64, 1, 2)
	b.result.points[0] = first
	var p [4]Point
	var radius [4]float64
	n := 2
	local := [4]Point{start, segment.Point}
	if segment.Kind == GeometryQuadratic {
		n, local = 3, [4]Point{start, segment.Control1, segment.Point}
	} else if segment.Kind == GeometryCubic {
		n, local = 4, [4]Point{start, segment.Control1, segment.Control2, segment.Point}
	}
	for i := 1; i < n; i++ {
		p[i], radius[i], err = strokeCurveAffine(geometryTransform, local[i], start, true)
		if err != nil {
			return strokeCurve{}, err
		}
	}
	if segment.Kind == GeometryArc && start != segment.Point && segment.RadiusX != 0 && segment.RadiusY != 0 {
		err = b.arc(start, segment, geometryTransform)
	} else {
		if angularTolerance < math.Pi {
			b.angleInput, b.angleMatrix = local, geometryTransform
		}
		for i := 1; i < n; i++ {
			b.result.startTangent, err = strokeCurveTangent(geometryTransform, local[0], local[i])
			if err != nil {
				return strokeCurve{}, err
			}
			if b.result.startTangent != (Point{}) {
				break
			}
		}
		for i := n - 2; i >= 0; i-- {
			b.result.endTangent, err = strokeCurveTangent(geometryTransform, local[i], local[n-1])
			if err != nil {
				return strokeCurve{}, err
			}
			if b.result.endTangent != (Point{}) {
				break
			}
		}
		if n == 2 {
			_, rounding, e := b.output(p[1], true)
			bound := strokeCurveUp(rounding + radius[1])
			margin := (bound + firstError) * norm
			if norm == 0 || bound+firstError == 0 {
				margin = 0
			}
			if e != nil || !geometryFinite(math.Hypot(p[1].X, p[1].Y), bound, margin) || bound > lengthTolerance || margin > tolerance {
				return strokeCurve{}, fmt.Errorf("%w: stroke line precision or length range exhausted", ErrLimit)
			}
			if !b.bezierAngle(p, radius, n, first, last, 0, 1) {
				return strokeCurve{}, fmt.Errorf("%w: stroke line angular precision exhausted", ErrLimit)
			}
			err = b.appendPoint(last, bound)
		} else {
			err = b.bezierStart(p, radius, n)
		}
	}
	if err != nil {
		return strokeCurve{}, err
	}
	if !geometryFinite(b.result.lengthError) || b.result.lengthError > lengthTolerance {
		return strokeCurve{}, fmt.Errorf("%w: stroke length precision exhausted", ErrLimit)
	}
	return b.result, nil
}

// strokeCurveAffine 以补偿残差计算常规仿射值，极端量级初始化才使用精确有理数
// 入参: m 仿射矩阵, p 目标点, base 差向量起点, vector 是否仅计算线性差向量
// 返回: Point 舍入结果, float64 舍入误差半径上界, error 表示范围错误
func strokeCurveAffine(m Matrix, p, base Point, vector bool) (Point, float64, error) {
	if m.A == 1 && m.B == 0 && m.C == 0 && m.D == 1 && (vector || m.E == 0 && m.F == 0) {
		if !vector {
			return p, 0, nil
		}
		q := Point{p.X - base.X, p.Y - base.Y}
		if geometryFinite(q.X, q.Y) {
			e := math.Hypot(strokeCurveSumError(p.X, -base.X, q.X), strokeCurveSumError(p.Y, -base.Y, q.Y))
			if geometryFinite(e) {
				return q, strokeCurveUp(e), nil
			}
		}
	}
	ordinary := true
	for _, value := range [...]float64{m.A, m.B, m.C, m.D, m.E, m.F, p.X, p.Y, base.X, base.Y} {
		if value != 0 && (math.Abs(value) < 0x1p-400 || math.Abs(value) > 0x1p400) {
			ordinary = false
			break
		}
	}
	if ordinary {
		x, y, ex, ey := p.X, p.Y, 0.0, 0.0
		if vector {
			x, y = p.X-base.X, p.Y-base.Y
			ex, ey = strokeCurveSumError(p.X, -base.X, x), strokeCurveSumError(p.Y, -base.Y, y)
			m.E, m.F = 0, 0
		}
		vx, rx := strokeCurveAffineAxis(m.A, m.C, m.E, x, y, ex, ey)
		vy, ry := strokeCurveAffineAxis(m.B, m.D, m.F, x, y, ex, ey)
		return Point{vx, vy}, strokeCurveUp(math.Hypot(rx, ry)), nil
	}
	return strokeCurveAffineExact(m, p, base, vector)
}

// strokeCurveAffineExact 用有理数处理极端量级和切线消减，不用于常规细分循环
// 入参: m 仿射矩阵, p 目标点, base 差向量起点, vector 是否计算线性差向量
// 返回: Point 舍入结果, float64 舍入误差半径, error 表示范围错误
func strokeCurveAffineExact(m Matrix, p, base Point, vector bool) (Point, float64, error) {
	var out Point
	var errors [2]float64
	for axis := 0; axis < 2; axis++ {
		a, c, e := m.A, m.C, m.E
		if axis == 1 {
			a, c, e = m.B, m.D, m.F
		}
		x, y := new(big.Rat).SetFloat64(p.X), new(big.Rat).SetFloat64(p.Y)
		if vector {
			x.Sub(x, new(big.Rat).SetFloat64(base.X))
			y.Sub(y, new(big.Rat).SetFloat64(base.Y))
			e = 0
		}
		x.Mul(x, new(big.Rat).SetFloat64(a))
		y.Mul(y, new(big.Rat).SetFloat64(c))
		x.Add(x, y).Add(x, new(big.Rat).SetFloat64(e))
		v, exact := x.Float64()
		if !geometryFinite(v) {
			return Point{}, 0, fmt.Errorf("%w: stroke coordinate overflow", ErrLimit)
		}
		if !exact {
			x.Sub(x, new(big.Rat).SetFloat64(v)).Abs(x)
			errors[axis], _ = x.Float64()
			errors[axis] = math.Nextafter(errors[axis], math.Inf(1))
		}
		if axis == 0 {
			out.X = v
		} else {
			out.Y = v
		}
	}
	return out, strokeCurveUp(math.Hypot(errors[0], errors[1])), nil
}

// strokeCurveTangent 从未平移的原始控制差求方向，消减区间改用精确运算
// 入参: m 几何矩阵, start 控制差起点, end 控制差终点
// 返回: Point 单位方向，精确零差返回零, error 非零方向无法表示的错误
func strokeCurveTangent(m Matrix, start, end Point) (Point, error) {
	v, radius, err := strokeCurveAffine(m, end, start, true)
	if err != nil {
		return Point{}, err
	}
	if radius > 0 && math.Hypot(v.X, v.Y) <= 16*radius {
		v, radius, err = strokeCurveAffineExact(m, end, start, true)
		if err != nil {
			return Point{}, err
		}
	}
	if v == (Point{}) {
		if radius != 0 {
			return Point{}, fmt.Errorf("%w: stroke tangent underflow", ErrLimit)
		}
		return Point{}, nil
	}
	return strokeOutlineDirection(Point{}, v), nil
}

// strokeCurveAffineAxis 通过TwoSum和FMA残差给出常规量级仿射运算的舍入半径
// 入参: a 横向系数, c 纵向系数, e 平移, x 横坐标, y 纵坐标, ex 横坐标误差, ey 纵坐标误差
// 返回: float64 舍入坐标, float64 误差上界
func strokeCurveAffineAxis(a, c, e, x, y, ex, ey float64) (float64, float64) {
	u, v := a*x, c*y
	s := u + v
	value := s + e
	bound := strokeCurveUp(math.Abs(math.FMA(a, x, -u)) + math.Abs(math.FMA(c, y, -v)))
	bound = strokeCurveUp(bound + strokeCurveSumError(u, v, s))
	bound = strokeCurveUp(bound + strokeCurveSumError(s, e, value))
	bound = strokeCurveUp(bound + strokeCurveUp(math.Abs(a)*ex))
	bound = strokeCurveUp(bound + strokeCurveUp(math.Abs(c)*ey))
	return value, bound
}

// strokeCurveUp 向外扩展非负误差，精确零不引入虚构误差
// 入参: value 非负数值
// 返回: float64 向上舍入的上界
func strokeCurveUp(value float64) float64 {
	if value == 0 {
		return 0
	}
	return math.Nextafter(value, math.Inf(1))
}

// strokeCurveRound 给出有限计算量的保守浮点舍入余量
// 入参: scale 计算尺度
// 返回: float64 舍入余量
func strokeCurveRound(scale float64) float64 {
	if scale == 0 {
		return 0
	}
	return max(math.SmallestNonzeroFloat64, math.Abs(scale)*0x1p-47)
}

// strokeCurveSumError 计算有限加法的舍入残差
// 入参: a 第一加数, b 第二加数, sum 已舍入和
// 返回: float64 绝对舍入误差
func strokeCurveSumError(a, b, sum float64) float64 {
	v := sum - a
	return math.Abs((a - (sum - v)) + (b - v))
}

// output 将相对点还原为描边坐标，并检查输出舍入和末点贴合误差
// 入参: p 相对点, final 是否使用原始终点
// 返回: Point 输出点, float64 位置误差半径, error 坐标溢出错误
func (b *strokeCurveBuilder) output(p Point, final bool) (Point, float64, error) {
	q := Point{b.origin.X + p.X, b.origin.Y + p.Y}
	if !geometryFinite(q.X, q.Y) {
		return Point{}, 0, fmt.Errorf("%w: stroke output coordinate overflow", ErrLimit)
	}
	e := math.Hypot(strokeCurveSumError(b.origin.X, p.X, q.X), strokeCurveSumError(b.origin.Y, p.Y, q.Y))
	if final {
		e += math.Hypot(q.X-b.last.X, q.Y-b.last.Y)
		q = b.last
	}
	return q, strokeCurveUp(e), nil
}

// split 检查深度、输出点数及累计二分工作预算
// 入参: depth 当前深度
// 返回: error 资源预算错误
func (b *strokeCurveBuilder) split(depth int) error {
	if depth >= 64 || b.splits >= b.maxPoints-2 {
		return fmt.Errorf("%w: stroke subdivision budget exceeded", ErrLimit)
	}
	b.splits++
	return nil
}

// appendPoint 同步追加端点与外舍入的累计误差，源参数连续叶的局部误差按三角不等式累加
// 入参: p 输出点, bound 当前真实叶弧长与相邻输出点精确弦长之差的绝对上界
// 返回: error 输出预算错误
func (b *strokeCurveBuilder) appendPoint(p Point, bound float64) error {
	if len(b.result.points) >= b.maxPoints {
		return fmt.Errorf("%w: stroke point budget exceeded", ErrLimit)
	}
	b.result.points = append(b.result.points, p)
	b.result.lengthError = strokeCurveUp(b.result.lengthError + bound)
	b.result.lengthErrors = append(b.result.lengthErrors, b.result.lengthError)
	return nil
}

// bezier 由控制多边形长度和同参数弦偏差双重约束二分曲线，保留共线回折
// 入参: p 相对控制点, radius 控制点舍入半径, n 控制点数量, depth 深度, budget 局部长度容差, lo 起始参数, hi 终止参数, final 是否包含原始末点
// 返回: error 精度或资源预算错误
func (b *strokeCurveBuilder) bezier(p [4]Point, radius [4]float64, n, depth int, budget, lo, hi float64, final bool) error {
	end, endError, err := b.output(p[n-1], final)
	if err != nil {
		return err
	}
	first, firstError, err := b.output(p[0], false)
	if err != nil {
		return err
	}
	previous := b.result.points[len(b.result.points)-1]
	firstError += math.Hypot(first.X-previous.X, first.Y-previous.Y)
	polygon := 0.0
	for i := 1; i < n; i++ {
		d := math.Hypot(p[i].X-p[i-1].X, p[i].Y-p[i-1].Y)
		polygon = strokeCurveUp(polygon + d + radius[i] + radius[i-1] + strokeCurveRound(d))
	}
	chord := math.Hypot(p[n-1].X-p[0].X, p[n-1].Y-p[0].Y)
	bound := strokeCurveUp(max(0, polygon-chord) + strokeCurveRound(chord) + firstError + endError + radius[0] + radius[n-1])
	flat := true
	positionError := max(firstError, endError) + b.originError
	for i := 1; i < n-1; i++ {
		t := float64(i) / float64(n-1)
		line := Point{geometryLinearCombination(0, 1-t, p[0].X, t, p[n-1].X), geometryLinearCombination(0, 1-t, p[0].Y, t, p[n-1].Y)}
		delta := Point{p[i].X - line.X, p[i].Y - line.Y}
		if !geometryFinite(delta.X, delta.Y) {
			flat = false
			continue
		}
		device, e := geometryFillPoint(b.device, delta)
		if e != nil {
			flat = false
			continue
		}
		localError := positionError + radius[i] + max(radius[0], radius[n-1]) + strokeCurveRound(max(math.Abs(line.X), math.Abs(line.Y), math.Abs(p[i].X), math.Abs(p[i].Y)))
		margin := localError * b.deviceNorm
		if localError == 0 {
			margin = 0
		}
		if !(math.Hypot(device.X, device.Y)+margin <= b.tolerance) {
			flat = false
		}
	}
	if flat && geometryFinite(bound) && bound <= budget/2 && b.bezierAngle(p, radius, n, previous, end, lo, hi) {
		return b.appendPoint(end, bound)
	}
	if err := b.split(depth); err != nil {
		return err
	}
	w, r, left, right, le, re := p, radius, [4]Point{}, [4]Point{}, [4]float64{}, [4]float64{}
	left[0], right[n-1], le[0], re[n-1] = p[0], p[n-1], radius[0], radius[n-1]
	for level := 1; level < n; level++ {
		for i := 0; i < n-level; i++ {
			q := Point{geometryHalfDifference(w[i].X, -w[i+1].X), geometryHalfDifference(w[i].Y, -w[i+1].Y)}
			average := geometryHalfDifference(r[i], -r[i+1])
			if average == 0 && (r[i] != 0 || r[i+1] != 0) {
				average = math.SmallestNonzeroFloat64
			}
			r[i] = strokeCurveUp(strokeCurveUp(average) + strokeCurveRound(max(math.Abs(q.X), math.Abs(q.Y))))
			w[i] = q
		}
		left[level], right[n-level-1] = w[0], w[n-level-1]
		le[level], re[n-level-1] = r[0], r[n-level-1]
	}
	mid := (lo + hi) / 2
	if b.angularTolerance < math.Pi && (mid == lo || mid == hi) {
		return fmt.Errorf("%w: stroke angular parameter precision exhausted", ErrLimit)
	}
	if err := b.bezier(left, le, n, depth+1, budget/2, lo, mid, false); err != nil {
		return err
	}
	return b.bezier(right, re, n, depth+1, budget/2, mid, hi, final)
}

// strokeCurveExactControls 精确变换原始控制差，供零导数及角度边界证书使用
// 入参: source 原始控制点, n 点数, m 几何变换
// 返回: [4]strokeCurveExact 相对首点的精确控制点
func strokeCurveExactControls(source [4]Point, n int, m Matrix) [4]strokeCurveExact {
	var out [4]strokeCurveExact
	for i := 0; i < n; i++ {
		dx := new(big.Rat).Sub(new(big.Rat).SetFloat64(source[i].X), new(big.Rat).SetFloat64(source[0].X))
		dy := new(big.Rat).Sub(new(big.Rat).SetFloat64(source[i].Y), new(big.Rat).SetFloat64(source[0].Y))
		for axis := 0; axis < 2; axis++ {
			a, c := m.A, m.C
			if axis == 1 {
				a, c = m.B, m.D
			}
			out[i][axis] = new(big.Rat).Add(new(big.Rat).Mul(dx, new(big.Rat).SetFloat64(a)), new(big.Rat).Mul(dy, new(big.Rat).SetFloat64(c)))
		}
	}
	return out
}

// strokeCurveExactLerp 对精确二维值进行仿射插值
// 入参: a 首值, b 末值, t 参数
// 返回: strokeCurveExact 插值结果
func strokeCurveExactLerp(a, b strokeCurveExact, t *big.Rat) strokeCurveExact {
	var out strokeCurveExact
	for axis := range out {
		out[axis] = new(big.Rat).Sub(b[axis], a[axis])
		out[axis].Mul(out[axis], t).Add(out[axis], a[axis])
	}
	return out
}

// strokeCurveExactSplit 按精确参数分割Bezier，保留非二进制尖点的位置和零导数
// 入参: p 控制点, n 点数, t 分割参数
// 返回: [4]strokeCurveExact 左段, [4]strokeCurveExact 右段
func strokeCurveExactSplit(p [4]strokeCurveExact, n int, t *big.Rat) ([4]strokeCurveExact, [4]strokeCurveExact) {
	var left, right [4]strokeCurveExact
	left[0], right[n-1] = p[0], p[n-1]
	for level := 1; level < n; level++ {
		for i := 0; i < n-level; i++ {
			p[i] = strokeCurveExactLerp(p[i], p[i+1], t)
		}
		left[level], right[n-level-1] = p[0], p[n-level-1]
	}
	return left, right
}

// strokeCurveExactFloat 将精确控制点转换为有限浮点及外扩误差半径
// 入参: value 精确二维值
// 返回: Point 近似值, float64 舍入半径, error 数值范围错误
func strokeCurveExactFloat(value strokeCurveExact) (Point, float64, error) {
	var p, e [2]float64
	for axis := range p {
		v, exact := value[axis].Float64()
		if !geometryFinite(v) {
			return Point{}, 0, fmt.Errorf("%w: stroke angular control overflow", ErrLimit)
		}
		p[axis] = v
		if !exact {
			r := new(big.Rat).Sub(value[axis], new(big.Rat).SetFloat64(v))
			r.Abs(r)
			e[axis], _ = r.Float64()
			e[axis] = math.Nextafter(e[axis], math.Inf(1))
		}
	}
	return Point{p[0], p[1]}, strokeCurveUp(math.Hypot(e[0], e[1])), nil
}

// strokeCurveExactCone 检查非负组合的导数向量是否位于实际输出弦的凸角锥中
// 入参: vector 精确导数向量, start 输出起点, end 输出终点, slope 保守角锥斜率
// 返回: bool 该向量是否获得证书，精确零向量不约束方向
func strokeCurveExactCone(vector strokeCurveExact, start, end Point, slope float64) bool {
	if vector[0].Sign() == 0 && vector[1].Sign() == 0 {
		return true
	}
	x := new(big.Rat).Sub(new(big.Rat).SetFloat64(end.X), new(big.Rat).SetFloat64(start.X))
	y := new(big.Rat).Sub(new(big.Rat).SetFloat64(end.Y), new(big.Rat).SetFloat64(start.Y))
	dot := new(big.Rat).Add(new(big.Rat).Mul(x, vector[0]), new(big.Rat).Mul(y, vector[1]))
	if dot.Sign() <= 0 {
		return false
	}
	cross := new(big.Rat).Sub(new(big.Rat).Mul(x, vector[1]), new(big.Rat).Mul(y, vector[0]))
	cross.Abs(cross)
	return cross.Cmp(dot.Mul(dot, new(big.Rat).SetFloat64(slope))) <= 0
}

// strokeCurveCone 检查带误差圆盘的导数控制向量，边界不确定时交给精确证书
// 入参: vector 导数向量, radius 误差半径, start 输出起点, end 输出终点, slope 角锥斜率
// 返回: int 正值表示已证明，负值表示证书不成立，零表示需要精确判定
func strokeCurveCone(vector Point, radius float64, start, end Point, slope float64) int {
	if vector == (Point{}) && radius == 0 {
		return 1
	}
	x, y := end.X-start.X, end.Y-start.Y
	scale, vscale := max(math.Abs(x), math.Abs(y)), max(math.Abs(vector.X), math.Abs(vector.Y))
	if !geometryFinite(scale, vscale, radius) || scale == 0 || vscale == 0 {
		return 0
	}
	e := (strokeCurveSumError(end.X, -start.X, x) + strokeCurveSumError(end.Y, -start.Y, y)) / scale
	x, y = x/scale, y/scale
	u, v := vector.X/vscale, vector.Y/vscale
	margin := strokeCurveUp(2*(radius/vscale+e) + 0x1p-45)
	dot, cross := math.FMA(x, u, y*v), math.FMA(x, v, -y*u)
	if dot-margin > 0 && math.Abs(cross)+margin <= slope*(dot-margin) {
		return 1
	}
	if dot+margin < 0 || math.Abs(cross)-margin > slope*max(0, dot+margin) {
		return -1
	}
	return 0
}

// bezierAngle 以导数Bernstein控制锥约束叶内所有非零切线，不使用参数采样替代证书
// 入参: p 近似控制点, radius 控制误差, n 点数, start 输出起点, end 输出终点, lo 参数下界, hi 参数上界
// 返回: bool 是否证明整叶满足角度约束
func (b *strokeCurveBuilder) bezierAngle(p [4]Point, radius [4]float64, n int, start, end Point, lo, hi float64) bool {
	if b.angularTolerance == math.Pi {
		return true
	}
	uncertain := false
	for i := 0; i < n-1; i++ {
		v, e, err := strokeCurveAffine(IdentityMatrix(), p[i+1], p[i], true)
		if err != nil {
			uncertain = true
			continue
		}
		verdict := strokeCurveCone(v, strokeCurveUp(e+radius[i]+radius[i+1]), start, end, b.slope)
		if verdict < 0 {
			return false
		}
		uncertain = uncertain || verdict == 0
	}
	if !uncertain {
		return true
	}
	if b.angleSource[0][0] == nil {
		b.angleSource = strokeCurveExactControls(b.angleInput, n, b.angleMatrix)
	}
	var derivative [4]strokeCurveExact
	for i := 0; i < n-1; i++ {
		for axis := 0; axis < 2; axis++ {
			derivative[i][axis] = new(big.Rat).Sub(b.angleSource[i+1][axis], b.angleSource[i][axis])
		}
	}
	if lo != 0 {
		_, derivative = strokeCurveExactSplit(derivative, n-1, new(big.Rat).SetFloat64(lo))
	}
	if hi != 1 {
		t := new(big.Rat).Sub(new(big.Rat).SetFloat64(hi), new(big.Rat).SetFloat64(lo))
		t.Quo(t, new(big.Rat).Sub(big.NewRat(1, 1), new(big.Rat).SetFloat64(lo)))
		derivative, _ = strokeCurveExactSplit(derivative, n-1, t)
	}
	for i := 0; i < n-1; i++ {
		if !strokeCurveExactCone(derivative[i], start, end, b.slope) {
			return false
		}
	}
	return true
}

// strokeCurveDerivativePolynomial 将精确Bezier导数转换为降序幂系数，省略公共正次数因子
// 入参: p 精确控制点, n 点数, axis 坐标轴
// 返回: [3]*big.Rat 二次、一次及常数系数
func strokeCurveDerivativePolynomial(p [4]strokeCurveExact, n, axis int) [3]*big.Rat {
	a, b := new(big.Rat), new(big.Rat)
	c := new(big.Rat).Sub(p[1][axis], p[0][axis])
	if n > 2 {
		d := new(big.Rat).Sub(p[2][axis], p[1][axis])
		b.Sub(d, c)
		if n > 3 {
			e := new(big.Rat).Sub(p[3][axis], p[2][axis])
			a.Sub(e, d).Sub(a, b)
			b.Mul(b, big.NewRat(2, 1))
		}
	}
	return [3]*big.Rat{a, b, c}
}

// strokeCurvePolynomialValue 精确计算二次多项式
// 入参: p 降序系数, t 参数
// 返回: *big.Rat 多项式值
func strokeCurvePolynomialValue(p [3]*big.Rat, t *big.Rat) *big.Rat {
	v := new(big.Rat).Mul(p[0], t)
	return v.Add(v, p[1]).Mul(v, t).Add(v, p[2])
}

// bezierStart 显式隔离共线回折及公共零导数尖点，使可处理零导数不触发无限二分
// 入参: p 浮点控制点, radius 舍入半径, n 点数
// 返回: error 精度或预算错误
func (b *strokeCurveBuilder) bezierStart(p [4]Point, radius [4]float64, n int) error {
	if b.angularTolerance == math.Pi || strokeCurveRegularBezier(p, radius, n) {
		return b.bezier(p, radius, n, 0, b.lengthTolerance, 0, 1, true)
	}
	b.angleSource = strokeCurveExactControls(b.angleInput, n, b.angleMatrix)
	collinear, axis := true, 0
	var direction strokeCurveExact
	for i := 1; i < n; i++ {
		x, y := b.angleSource[i][0], b.angleSource[i][1]
		if x.Sign() == 0 && y.Sign() == 0 {
			continue
		}
		if direction[0] == nil {
			direction = b.angleSource[i]
			if x.Sign() == 0 {
				axis = 1
			}
		} else if new(big.Rat).Mul(x, direction[1]).Cmp(new(big.Rat).Mul(y, direction[0])) != 0 {
			collinear = false
			break
		}
	}
	if collinear {
		return b.collinearBezier(n, axis)
	}
	x, y := strokeCurveDerivativePolynomial(b.angleSource, n, 0), strokeCurveDerivativePolynomial(b.angleSource, n, 1)
	var linear, constant *big.Rat
	if x[0].Sign() == 0 {
		linear, constant = x[1], x[2]
	} else if y[0].Sign() == 0 {
		linear, constant = y[1], y[2]
	} else {
		linear = new(big.Rat).Sub(new(big.Rat).Mul(x[1], y[0]), new(big.Rat).Mul(y[1], x[0]))
		constant = new(big.Rat).Sub(new(big.Rat).Mul(x[2], y[0]), new(big.Rat).Mul(y[2], x[0]))
	}
	if linear.Sign() != 0 {
		root := new(big.Rat).Neg(new(big.Rat).Quo(constant, linear))
		if root.Sign() > 0 && root.Cmp(big.NewRat(1, 1)) < 0 && strokeCurvePolynomialValue(x, root).Sign() == 0 && strokeCurvePolynomialValue(y, root).Sign() == 0 {
			if err := b.split(0); err != nil {
				return err
			}
			left, right := strokeCurveExactSplit(b.angleSource, n, root)
			for i, source := range [][4]strokeCurveExact{left, right} {
				b.angleSource = source
				for j := 0; j < n; j++ {
					var err error
					p[j], radius[j], err = strokeCurveExactFloat(source[j])
					if err != nil {
						return err
					}
				}
				if err := b.bezier(p, radius, n, 1, b.lengthTolerance/2, 0, 1, i == 1); err != nil {
					return err
				}
			}
			return nil
		}
	}
	return b.bezier(p, radius, n, 0, b.lengthTolerance, 0, 1, true)
}

// strokeCurveRegularBezier 通过单坐标导数控制区间严格同号排除内部零导数，避免常规曲线预先构造有理数
// 入参: p 浮点控制点, radius 舍入半径, n 点数
// 返回: bool 是否已证明至少一个导数分量始终非零
func strokeCurveRegularBezier(p [4]Point, radius [4]float64, n int) bool {
	for axis := 0; axis < 2; axis++ {
		positive, negative := true, true
		for i := 0; i < n-1; i++ {
			a, c := p[i].X, p[i+1].X
			if axis == 1 {
				a, c = p[i].Y, p[i+1].Y
			}
			d := c - a
			if !geometryFinite(d) {
				positive, negative = false, false
				break
			}
			e := strokeCurveUp(strokeCurveSumError(c, -a, d) + radius[i] + radius[i+1])
			positive = positive && d > e
			negative = negative && d < -e
		}
		if positive || negative {
			return true
		}
	}
	return false
}

// strokeCurveRootIntervals 以有理数及定向平方根隔离二次多项式的内部简单实根
// 入参: p 降序精确系数
// 返回: [][2]*big.Rat 有序根区间, error 无法隔离端点附近根的精度错误
func strokeCurveRootIntervals(p [3]*big.Rat) ([][2]*big.Rat, error) {
	var roots [][2]*big.Rat
	if p[0].Sign() == 0 {
		if p[1].Sign() != 0 {
			r := new(big.Rat).Neg(new(big.Rat).Quo(p[2], p[1]))
			roots = append(roots, [2]*big.Rat{r, r})
		}
	} else {
		discriminant := new(big.Rat).Sub(new(big.Rat).Mul(p[1], p[1]), new(big.Rat).Mul(big.NewRat(4, 1), new(big.Rat).Mul(p[0], p[2])))
		if discriminant.Sign() > 0 {
			lower := new(big.Float).SetPrec(256).SetMode(big.ToNegativeInf).SetRat(discriminant)
			upper := new(big.Float).SetPrec(256).SetMode(big.ToPositiveInf).SetRat(discriminant)
			lower.Sqrt(lower)
			upper.Sqrt(upper)
			lo, _ := lower.Rat(nil)
			hi, _ := upper.Rat(nil)
			denominator := new(big.Rat).Mul(big.NewRat(2, 1), p[0])
			for _, sign := range []int64{-1, 1} {
				a := new(big.Rat).Mul(big.NewRat(sign, 1), lo)
				c := new(big.Rat).Mul(big.NewRat(sign, 1), hi)
				a.Sub(a, p[1]).Quo(a, denominator)
				c.Sub(c, p[1]).Quo(c, denominator)
				if a.Cmp(c) > 0 {
					a, c = c, a
				}
				roots = append(roots, [2]*big.Rat{a, c})
			}
			if roots[0][0].Cmp(roots[1][0]) > 0 {
				roots[0], roots[1] = roots[1], roots[0]
			}
		}
	}
	inside := roots[:0]
	for _, root := range roots {
		if root[1].Sign() <= 0 || root[0].Cmp(big.NewRat(1, 1)) >= 0 {
			continue
		}
		if root[0].Sign() <= 0 || root[1].Cmp(big.NewRat(1, 1)) >= 0 {
			return nil, fmt.Errorf("%w: stroke stationary root isolation exhausted", ErrLimit)
		}
		inside = append(inside, root)
	}
	return inside, nil
}

// collinearBezier 对精确共线曲线按真实驻点划分单调区间，零导数不添加虚构角度
// 入参: n 控制点数, axis 非常量坐标轴
// 返回: error 误差、点数或根隔离错误
func (b *strokeCurveBuilder) collinearBezier(n, axis int) error {
	polynomial := strokeCurveDerivativePolynomial(b.angleSource, n, axis)
	roots, err := strokeCurveRootIntervals(polynomial)
	if err != nil {
		return err
	}
	zero, one := big.NewRat(0, 1), big.NewRat(1, 1)
	roots = append(roots, [2]*big.Rat{one, one})
	previousParameter, previousError := zero, 0.0
	lipschitz := new(big.Rat)
	for i := 1; i < n; i++ {
		x := new(big.Rat).Sub(b.angleSource[i][0], b.angleSource[i-1][0])
		y := new(big.Rat).Sub(b.angleSource[i][1], b.angleSource[i-1][1])
		x.Abs(x).Add(x, y.Abs(y))
		if x.Cmp(lipschitz) > 0 {
			lipschitz.Set(x)
		}
	}
	lipschitz.Mul(lipschitz, big.NewRat(int64(n-1), 1))
	for i, interval := range roots {
		if previousParameter.Cmp(interval[0]) >= 0 {
			return fmt.Errorf("%w: stroke stationary roots overlap", ErrLimit)
		}
		if i < len(roots)-1 {
			if err := b.split(0); err != nil {
				return err
			}
		}
		sample := new(big.Rat).Quo(new(big.Rat).Add(previousParameter, interval[0]), big.NewRat(2, 1))
		var direction strokeCurveExact
		for axis := range direction {
			direction[axis] = strokeCurvePolynomialValue(strokeCurveDerivativePolynomial(b.angleSource, n, axis), sample)
		}
		middle := new(big.Rat).Quo(new(big.Rat).Add(interval[0], interval[1]), big.NewRat(2, 1))
		left, _ := strokeCurveExactSplit(b.angleSource, n, middle)
		local, rounding, err := strokeCurveExactFloat(left[n-1])
		if err != nil {
			return err
		}
		uncertainty := new(big.Rat).Sub(interval[1], interval[0])
		uncertainty.Mul(uncertainty, lipschitz).Quo(uncertainty, big.NewRat(2, 1))
		parameterError, exact := uncertainty.Float64()
		if !exact {
			parameterError = math.Nextafter(parameterError, math.Inf(1))
		}
		end, outputError, err := b.output(local, i == len(roots)-1)
		if err != nil {
			return err
		}
		errorRadius := strokeCurveUp(rounding + parameterError + outputError)
		position := (errorRadius + b.originError) * b.deviceNorm
		if errorRadius+b.originError == 0 || b.deviceNorm == 0 {
			position = 0
		}
		if !geometryFinite(position, errorRadius) || position > b.tolerance || !strokeCurveExactCone(direction, b.result.points[len(b.result.points)-1], end, b.slope) {
			return fmt.Errorf("%w: stroke collinear angular or output precision exhausted", ErrLimit)
		}
		if err := b.appendPoint(end, strokeCurveUp(previousError+errorRadius)); err != nil {
			return err
		}
		previousParameter, previousError = interval[1], errorRadius
	}
	return nil
}

// arc 将端点弧参数转换为相对起点的椭圆参数，复用几何模块的半差及半径修正算法
// 入参: start 原始起点, s 弧参数, m 几何变换
// 返回: error 参数表示或细分错误
func (b *strokeCurveBuilder) arc(start Point, s GeometrySegment, m Matrix) error {
	if m.A == 0 && m.B == 0 && m.C == 0 && m.D == 0 {
		return b.appendPoint(b.last, 0)
	}
	if max(math.Abs(start.X), math.Abs(start.Y), math.Abs(s.Point.X), math.Abs(s.Point.Y), s.RadiusX, s.RadiusY) < 0x1p-500 {
		start = Point{math.Ldexp(start.X, 512), math.Ldexp(start.Y, 512)}
		s.Point = Point{math.Ldexp(s.Point.X, 512), math.Ldexp(s.Point.Y, 512)}
		s.RadiusX, s.RadiusY = math.Ldexp(s.RadiusX, 512), math.Ldexp(s.RadiusY, 512)
		for _, coefficient := range []*float64{&m.A, &m.B, &m.C, &m.D} {
			scaled := math.Ldexp(*coefficient, -512)
			if scaled == 0 && *coefficient != 0 {
				return fmt.Errorf("%w: stroke arc transform underflow", ErrLimit)
			}
			*coefficient = scaled
		}
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
		return fmt.Errorf("%w: stroke arc chord overflow", ErrLimit)
	}
	u, v, norm, exponent := geometryArcRatios(x, rx, y, ry)
	if !geometryFinite(u, v, norm) || norm <= 0 {
		return fmt.Errorf("%w: stroke arc normalization precision exhausted", ErrLimit)
	}
	exponent += chordExponent
	h := math.Ldexp(norm, exponent)
	root := -1.0
	if h >= 1-1e-7 && h <= 1+1e-7 && chordExponent == 0 {
		squared := strokeCurveArcSquaredChord(start, s.Point, rx, ry, sin, cos)
		if squared.Cmp(big.NewRat(1, 1)) <= 0 {
			value, _ := squared.Float64()
			h = math.Sqrt(value)
			squared.Sub(big.NewRat(1, 1), squared)
			value, _ = squared.Float64()
			root = math.Sqrt(value)
		} else {
			h, root = max(1, h), 0
		}
	}
	if h > 1 {
		mx, ex := math.Frexp(rx)
		my, ey := math.Frexp(ry)
		rx, ry = math.Ldexp(mx*norm, ex+exponent), math.Ldexp(my*norm, ey+exponent)
		h = 1
	}
	if !geometryFinite(rx, ry) || h == 0 {
		return fmt.Errorf("%w: stroke arc radius or angle range exhausted", ErrLimit)
	}
	k := math.Sqrt((1 - h) * (1 + h))
	if root >= 0 {
		k = root
	}
	span := 2 * math.Atan2(h, k)
	if s.IsLargeArc == s.SweepClockwise {
		k = -k
	}
	nx, ny := math.FMA(h, u, -k*v), math.FMA(h, v, k*u)
	m.E, m.F = 0, 0
	a, ae, err := strokeCurveAffine(m, Point{rx * cos, rx * sin}, Point{}, true)
	if err != nil {
		return err
	}
	d, de, err := strokeCurveAffine(m, Point{-ry * sin, ry * cos}, Point{}, true)
	if err != nil {
		return err
	}
	if (a == (Point{}) && ae != 0) || (d == (Point{}) && de != 0) {
		return fmt.Errorf("%w: stroke arc basis underflow", ErrLimit)
	}
	p, pe, err := strokeCurveAffine(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{nx, ny}, Point{}, true)
	if err != nil {
		return err
	}
	q, qe, err := strokeCurveAffine(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{-ny, nx}, Point{}, true)
	if err != nil {
		return err
	}
	b.arcVectorError = strokeCurveUp(pe + qe + 2*(ae+de))
	if s.IsLargeArc {
		span = 2*math.Pi - span
	}
	if !s.SweepClockwise {
		span = -span
	}
	b.result.startTangent = strokeCurveArcTangent(p, q, 0, span, false)
	ex, ey := math.FMA(-h, u, -k*v), math.FMA(-h, v, k*u)
	endRadial, err := geometryFillPoint(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{ex, ey})
	if err != nil {
		return err
	}
	endDerivative, err := geometryFillPoint(Matrix{A: a.X, B: a.Y, C: d.X, D: d.Y}, Point{-ey, ex})
	if err != nil {
		return err
	}
	b.result.endTangent = strokeCurveArcTangent(endRadial, endDerivative, 0, span, true)
	for _, end := range []bool{false, true} {
		radial, derivative := p, q
		if end {
			radial, derivative = endRadial, endDerivative
		}
		if math.Hypot(derivative.X, derivative.Y) <= strokeCurveRound(max(math.Abs(a.X), math.Abs(a.Y), math.Abs(d.X), math.Abs(d.Y))) {
			direction, e := strokeCurveArcPreciseDirection(x, y, rx, ry, sin, cos, chordExponent, m, s.IsLargeArc, s.SweepClockwise, end)
			if e != nil {
				return e
			}
			if direction == (Point{}) {
				if end {
					b.arcEndZero = true
				} else {
					b.arcStartZero = true
				}
				direction = strokeCurveArcTangent(radial, Point{}, 0, span, end)
			}
			if end {
				b.result.endTangent = direction
			} else {
				b.result.startTangent = direction
			}
		}
	}
	if b.angularTolerance < math.Pi && geometryMatrixSingular(m) {
		return b.collinearArc(p, q, span, m)
	}
	return b.arcInterval(p, q, 0, span, 0, b.lengthTolerance, true)
}

// collinearArc 在秩一投影下按解析驻点分割单调区间，避免非二进制弧回折无限二分
// 入参: p 径向量, q 切向量, span 有向参数角, m 秩一几何矩阵
// 返回: error 根归属、输出精度或预算错误
func (b *strokeCurveBuilder) collinearArc(p, q Point, span float64, m Matrix) error {
	direction := Point{m.A, m.B}
	if direction == (Point{}) {
		direction = Point{m.C, m.D}
	}
	axis := 0
	if math.Abs(direction.Y) > math.Abs(direction.X) {
		axis = 1
	}
	a, c, component := p.X, q.X, direction.X
	if axis == 1 {
		a, c, component = p.Y, q.Y, direction.Y
	}
	amplitude := math.Hypot(a, c)
	uncertainty := strokeCurveUp(4*b.arcVectorError + 8*strokeCurveRound(max(math.Abs(a), math.Abs(c))))
	if !geometryFinite(amplitude, uncertainty) || amplitude <= uncertainty {
		return fmt.Errorf("%w: stroke projected arc amplitude precision exhausted", ErrLimit)
	}
	phase := math.Atan2(c, a)
	guard := strokeCurveUp(8*uncertainty/amplitude + 0x1p-44)
	var cuts []float64
	for k := -3; k <= 3; k++ {
		angle := phase + float64(k)*math.Pi
		if math.Abs(angle) <= guard {
			if b.arcStartZero {
				continue
			}
			return fmt.Errorf("%w: stroke projected arc start root unresolved", ErrLimit)
		}
		if math.Abs(angle-span) <= guard {
			if b.arcEndZero {
				continue
			}
			return fmt.Errorf("%w: stroke projected arc end root unresolved", ErrLimit)
		}
		if angle/span > 0 && angle/span < 1 {
			cuts = append(cuts, angle)
		}
	}
	sort.Slice(cuts, func(i, j int) bool { return cuts[i]/span < cuts[j]/span })
	cuts = append(cuts, span)
	previousAngle, previousError := 0.0, 0.0
	for i, angle := range cuts {
		final := i == len(cuts)-1
		if !final {
			if err := b.split(0); err != nil {
				return err
			}
		}
		mid := (previousAngle + angle) / 2
		velocity := geometryLinearCombination(0, -a, math.Sin(mid), c, math.Cos(mid)) * math.Copysign(1, span)
		if math.Abs(velocity) <= uncertainty {
			return fmt.Errorf("%w: stroke projected arc direction unresolved", ErrLimit)
		}
		sign := math.Copysign(1, velocity) * math.Copysign(1, component)
		v := strokeCurveExact{new(big.Rat).SetFloat64(sign * direction.X), new(big.Rat).SetFloat64(sign * direction.Y)}
		var scalar *big.Rat
		if final {
			s := math.Sin(angle / 2)
			value := geometryLinearCombination(0, -2*s*s, a, math.Sin(angle), c)
			if !geometryFinite(value) {
				return fmt.Errorf("%w: stroke projected arc endpoint overflow", ErrLimit)
			}
			scalar = new(big.Rat).SetFloat64(value)
		} else {
			sign := math.Copysign(1, math.Cos(angle-phase))
			scalar = new(big.Rat).Sub(new(big.Rat).SetFloat64(sign*amplitude), new(big.Rat).SetFloat64(a))
		}
		var exact strokeCurveExact
		for j, coefficient := range []float64{direction.X, direction.Y} {
			exact[j] = new(big.Rat).Quo(new(big.Rat).Mul(scalar, new(big.Rat).SetFloat64(coefficient)), new(big.Rat).SetFloat64(component))
		}
		local, rounding, err := strokeCurveExactFloat(exact)
		if err != nil {
			return err
		}
		end, outputError, err := b.output(local, final)
		if err != nil {
			return err
		}
		errorRadius := strokeCurveUp(rounding + outputError + 2*uncertainty)
		position := (errorRadius + b.originError) * b.deviceNorm
		if b.deviceNorm == 0 {
			position = 0
		}
		if !geometryFinite(position, errorRadius) || position > b.tolerance || !strokeCurveExactCone(v, b.result.points[len(b.result.points)-1], end, b.slope) {
			return fmt.Errorf("%w: stroke projected arc angular or output precision exhausted", ErrLimit)
		}
		if err := b.appendPoint(end, strokeCurveUp(previousError+errorRadius)); err != nil {
			return err
		}
		previousAngle, previousError = angle, errorRadius
	}
	return nil
}

// strokeCurveArcSquaredChord 精确计算接近直径时的归一化半弦平方，保留小圆心偏移
// 入参: start 原始起点, end 原始终点, rx 横半径, ry 纵半径, sin 旋转正弦, cos 旋转余弦
// 返回: *big.Rat 归一化半弦平方
func strokeCurveArcSquaredChord(start, end Point, rx, ry, sin, cos float64) *big.Rat {
	dx := new(big.Rat).Sub(new(big.Rat).SetFloat64(start.X), new(big.Rat).SetFloat64(end.X))
	dy := new(big.Rat).Sub(new(big.Rat).SetFloat64(start.Y), new(big.Rat).SetFloat64(end.Y))
	dx.Quo(dx, big.NewRat(2, 1))
	dy.Quo(dy, big.NewRat(2, 1))
	x := new(big.Rat).Add(new(big.Rat).Mul(dx, new(big.Rat).SetFloat64(cos)), new(big.Rat).Mul(dy, new(big.Rat).SetFloat64(sin)))
	y := new(big.Rat).Add(new(big.Rat).Mul(dx, new(big.Rat).SetFloat64(-sin)), new(big.Rat).Mul(dy, new(big.Rat).SetFloat64(cos)))
	x.Quo(x, new(big.Rat).SetFloat64(rx))
	y.Quo(y, new(big.Rat).SetFloat64(ry))
	x.Mul(x, x)
	y.Mul(y, y)
	return x.Add(x, y)
}

// strokeCurveArcPreciseDirection 在端点导数接近消减极限时区分代数零与微小非零切线
// 入参: x 半弦横坐标, y 半弦纵坐标, rx 横半径, ry 纵半径, sin 旋转正弦, cos 旋转余弦, chordExponent 半弦二进制缩放指数, m 几何线性变换, large 大弧标志, clockwise 顺时针标志, end 终点标志
// 返回: Point 正向单位切线，精确零导数返回零, error 切线方向无法可靠表示的错误
func strokeCurveArcPreciseDirection(x, y, rx, ry, sin, cos float64, chordExponent int, m Matrix, large, clockwise, end bool) (Point, error) {
	rat := func(v float64) *big.Rat { return new(big.Rat).SetFloat64(v) }
	mul := func(a, b *big.Rat) *big.Rat { return new(big.Rat).Mul(a, b) }
	add := func(a, b *big.Rat) *big.Rat { return new(big.Rat).Add(a, b) }
	xr, yr, rxx, ryy := rat(x), rat(y), rat(rx), rat(ry)
	if chordExponent != 0 {
		shift := new(big.Int).Lsh(big.NewInt(1), uint(max(chordExponent, -chordExponent)))
		factor := new(big.Rat).SetInt(shift)
		if chordExponent < 0 {
			factor.Inv(factor)
		}
		xr.Mul(xr, factor)
		yr.Mul(yr, factor)
	}
	x2, y2, rx2, ry2 := mul(xr, xr), mul(yr, yr), mul(rxx, rxx), mul(ryy, ryy)
	denominator := add(mul(rx2, y2), mul(ry2, x2))
	if denominator.Sign() == 0 {
		return Point{}, fmt.Errorf("%w: stroke arc tangent normalization exhausted", ErrLimit)
	}
	radical := new(big.Rat).Quo(mul(rx2, ry2), denominator)
	radical.Sub(radical, rat(1))
	if radical.Sign() < 0 {
		radical.SetInt64(0)
	}
	ux := new(big.Rat).Neg(new(big.Rat).Quo(mul(rxx, yr), ryy))
	uy := new(big.Rat).Quo(mul(ryy, xr), rxx)
	if end {
		ux.Neg(ux)
		uy.Neg(uy)
	}
	vx, vy := new(big.Rat).Neg(xr), new(big.Rat).Neg(yr)
	if large == clockwise {
		vx.Neg(vx)
		vy.Neg(vy)
	}
	rotation := func(a, b float64) (*big.Rat, *big.Rat) {
		return add(mul(rat(a), rat(cos)), mul(rat(b), rat(sin))), add(mul(rat(-a), rat(sin)), mul(rat(b), rat(cos)))
	}
	var values [2]*big.Float
	for axis := range values {
		a, c := m.A, m.C
		if axis == 1 {
			a, c = m.B, m.D
		}
		l, r := rotation(a, c)
		u, v := add(mul(l, ux), mul(r, uy)), add(mul(l, vx), mul(r, vy))
		values[axis] = new(big.Float).SetPrec(256)
		if (u.Sign() == 0 && (v.Sign() == 0 || radical.Sign() == 0)) || (u.Sign()*v.Sign() < 0 && mul(u, u).Cmp(mul(radical, mul(v, v))) == 0) {
			continue
		}
		f := new(big.Float).SetPrec(256).SetRat(radical)
		f.Sqrt(f).Mul(f, new(big.Float).SetPrec(256).SetRat(v))
		fu := new(big.Float).SetPrec(256).SetRat(u)
		values[axis].Add(fu, f)
		magnitude := new(big.Float).SetPrec(256).Add(new(big.Float).Abs(fu), new(big.Float).Abs(f))
		threshold := new(big.Float).SetPrec(256).SetMantExp(magnitude, -200)
		if new(big.Float).Abs(values[axis]).Cmp(threshold) <= 0 {
			return Point{}, fmt.Errorf("%w: stroke arc tangent precision exhausted", ErrLimit)
		}
	}
	scale := new(big.Float).Abs(values[0])
	if other := new(big.Float).Abs(values[1]); other.Cmp(scale) > 0 {
		scale = other
	}
	if scale.Sign() == 0 {
		return Point{}, nil
	}
	dx, _ := new(big.Float).SetPrec(256).Quo(values[0], scale).Float64()
	dy, _ := new(big.Float).SetPrec(256).Quo(values[1], scale).Float64()
	norm := math.Hypot(dx, dy)
	if !clockwise {
		norm = -norm
	}
	return Point{dx / norm, dy / norm}, nil
}

// strokeCurveArcTangent 按正向参数求单位切线，零一阶导数时取单侧二阶导数
// 入参: p 径向量, q 切向量, angle 参数角, span 有向总角, end 是否为终点
// 返回: Point 单位切线，完全退化时为零
func strokeCurveArcTangent(p, q Point, angle, span float64, end bool) Point {
	s, c := math.Sincos(angle)
	sign := math.Copysign(1, span)
	v := Point{geometryLinearCombination(0, -s, p.X, c, q.X), geometryLinearCombination(0, -s, p.Y, c, q.Y)}
	if v == (Point{}) {
		sign = 1
		if end {
			sign = -1
		}
		v = Point{geometryLinearCombination(0, -c, p.X, -s, q.X), geometryLinearCombination(0, -c, p.Y, -s, q.Y)}
	}
	if v == (Point{}) || !geometryFinite(v.X, v.Y) {
		return Point{}
	}
	v = strokeOutlineDirection(Point{}, v)
	return Point{sign * v.X, sign * v.Y}
}

// arcAngle 以短弧导数的正弦插值区间证书检查所有切线，零端点需已有精确判定
// 入参: v0 首导数, v1 末导数, scale 计算尺度, lo 起始角, hi 终止角, start 输出起点, end 输出终点, final 是否为原始末点
// 返回: bool 是否证明整个参数区间位于凸角锥
func (b *strokeCurveBuilder) arcAngle(v0, v1 Point, scale, lo, hi float64, start, end Point, final bool) bool {
	if b.angularTolerance == math.Pi {
		return true
	}
	sign := math.Copysign(1, hi-lo)
	radius := strokeCurveUp(b.arcVectorError + 4*strokeCurveRound(scale))
	for i, v := range []Point{v0, v1} {
		if i == 0 && lo == 0 && b.arcStartZero || i == 1 && final && b.arcEndZero {
			continue
		}
		v = Point{sign * v.X, sign * v.Y}
		if strokeCurveCone(v, radius, start, end, b.slope) != 1 {
			return false
		}
	}
	return true
}

// arcInterval 由椭圆切线三角形长度上界及设备空间二阶导数界展开短弧
// 入参: p 径向量, q 切向量, lo 起始角, hi 终止角, depth 深度, budget 局部长度容差, final 是否包含原始末点
// 返回: error 精度或资源预算错误
func (b *strokeCurveBuilder) arcInterval(p, q Point, lo, hi float64, depth int, budget float64, final bool) error {
	step := hi - lo
	if math.Abs(step) <= math.Pi/2 {
		first, err := geometryFillArcPoint(Point{}, p, q, lo)
		if err != nil {
			return err
		}
		last, err := geometryFillArcPoint(Point{}, p, q, hi)
		if err != nil {
			return err
		}
		end, endError, err := b.output(last, final)
		if err != nil {
			return err
		}
		begin, beginError, err := b.output(first, false)
		if err != nil {
			return err
		}
		previous := b.result.points[len(b.result.points)-1]
		beginError += math.Hypot(begin.X-previous.X, begin.Y-previous.Y)
		s0, c0 := math.Sincos(lo)
		s1, c1 := math.Sincos(hi)
		v0 := Point{geometryLinearCombination(0, -s0, p.X, c0, q.X), geometryLinearCombination(0, -s0, p.Y, c0, q.Y)}
		v1 := Point{geometryLinearCombination(0, -s1, p.X, c1, q.X), geometryLinearCombination(0, -s1, p.Y, c1, q.Y)}
		upper := math.Abs(math.Tan(step/2)) * (math.Hypot(v0.X, v0.Y) + math.Hypot(v1.X, v1.Y))
		chord := math.Hypot(last.X-first.X, last.Y-first.Y)
		scale := max(math.Abs(p.X), math.Abs(p.Y), math.Abs(q.X), math.Abs(q.Y))
		evaluation := (strokeCurveRound(scale) + b.arcVectorError) * min(4, max(math.Abs(lo), math.Abs(hi)))
		bound := strokeCurveUp(max(0, upper-chord) + strokeCurveRound(upper+chord) + 2*evaluation + beginError + endError + b.arcVectorError*math.Abs(step))
		dp, ep := geometryFillPoint(b.device, p)
		dq, eq := geometryFillPoint(b.device, q)
		if ep == nil && eq == nil {
			deviceScale := max(math.Abs(dp.X), math.Abs(dp.Y), math.Abs(dq.X), math.Abs(dq.Y))
			position := math.Sqrt2 * geometryProductSquare(deviceScale, step/2)
			margin := (evaluation + max(beginError, endError) + b.originError) * b.deviceNorm
			if b.deviceNorm == 0 {
				margin = 0
			}
			if geometryFinite(bound, position, margin) && bound <= budget/2 && position+margin <= b.tolerance && b.arcAngle(v0, v1, scale, lo, hi, previous, end, final) {
				return b.appendPoint(end, bound)
			}
		}
	}
	if err := b.split(depth); err != nil {
		return err
	}
	mid := (lo + hi) / 2
	if mid == lo || mid == hi {
		return fmt.Errorf("%w: stroke arc subdivision precision exhausted", ErrLimit)
	}
	if err := b.arcInterval(p, q, lo, mid, depth+1, budget/2, false); err != nil {
		return err
	}
	return b.arcInterval(p, q, mid, hi, depth+1, budget/2, final)
}
