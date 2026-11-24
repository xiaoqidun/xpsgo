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
	"math/bits"
	"sort"
)

// strokeDashMaxPattern 等常量限制描边虚线展开上限
const (
	strokeDashMaxPattern = 4096
	strokeDashMaxWork    = 1 << 20
)

// errStrokePathRefine 表示当前弧长界不足以确定虚线端点，需要进一步细分
var errStrokePathRefine = fmt.Errorf("%w: stroke dash endpoint requires refinement", ErrLimit)

// strokeDashSpan 表示中心线距离域中的闭合虚线区间，包括零长区间
type strokeDashSpan struct {
	start float64
	end   float64
}

// strokeDashRun 保存一种虚线在距离域内的周期索引范围
type strokeDashRun struct {
	start *big.Rat
	end   *big.Rat
	first *big.Int
	count int
}

// strokeDashExactSpan 保存尚未舍入的虚线区间
type strokeDashExactSpan struct {
	start                    *big.Rat
	end                      *big.Rat
	startClipped, endClipped bool
}

// strokeDashBounds 保存虚线真实端点的舍入范围，标记是否在连续段边界截断
type strokeDashBounds struct {
	start, end               strokeDistanceRange
	startClipped, endClipped bool
}

// strokeDistanceRange 保存真实弧长或虚线距离的闭区间
type strokeDistanceRange struct {
	lower float64
	upper float64
}

// strokeOutlineStyle 保存已解析的折线描边样式，枚举值与Path属性一致
type strokeOutlineStyle struct {
	thickness float64
	startCap  LineCap
	endCap    LineCap
	join      LineJoin
	miter     float64
}

// strokeOutlineBuilder 在描边空间构造同向凸块，并在扩展后变换到设备空间
type strokeOutlineBuilder struct {
	fill      geometryFillBuilder
	transform Matrix
	radius    float64
}

// strokeRoundNumber 扩展区间端点查询，用于圆弧的切线三角形与共享截面误差证书
type strokeRoundNumber[T any] interface {
	strokeMiterNumber[T]
	atLeast(float64) bool
	upperAbs() float64
	near(float64, float64) bool
}

// strokeRoundBuilder 保存圆弧二分的数值区间及独立预算，成功前不写入公共边缓冲
type strokeRoundBuilder[T strokeRoundNumber[T]] struct {
	number    T
	source    *strokeOutlineBuilder
	center    Point
	points    []Point
	splits    int
	maxPoints int
	maxSplits int
}

// strokeMiterNumber 统一常规浮点与高精度区间的尖角公式，避免两条数值路径改变裁切语义
type strokeMiterNumber[T any] interface {
	constant(float64) T
	add(T) T
	sub(T) T
	mul(T) T
	quo(T) T
	square() T
	sqrt() T
	minimum(T) T
	coordinate(float64) (float64, bool)
}

// strokeMiterInterval 保存包含精确实数结果的浮点闭区间
type strokeMiterInterval struct {
	low, high float64
}

// strokeMiterWide 保存固定精度向外舍入区间，空端点表示本次精度不足
type strokeMiterWide struct {
	low, high *big.Float
	precision uint
}

// strokePathRun 保存相邻描边段及原始连接点，不把未描边断口当作新子路径端点
type strokePathRun struct {
	points       []Point
	joins        []bool
	directions   []strokePathDirection
	distance     []float64
	lengthErrors []float64
	lengthBounds []strokeDistanceRange
	start        bool
	end          bool
}

// strokePathDirection 保存原始顶点两侧的正向切线，零值表示使用细分弦方向
type strokePathDirection struct {
	incoming Point
	outgoing Point
}

// strokePathPiece 保存已完成虚线切分的中心线、端帽及原始连接点
type strokePathPiece struct {
	points      []Point
	joins       []bool
	directions  []strokePathDirection
	startDir    Point
	endDir      Point
	startCap    LineCap
	endCap      LineCap
	closed      bool
	figureStart bool
	figureEnd   bool
	positive    bool
}

// strokeDashSpansWithBounds 切分虚线并可选返回精确端点的浮点包围，不以舍入值判断原始端点
// 入参: length 连续段近似弧长, thickness 描边厚度, pattern 虚线数组, offset 序列偏移, maxSpans 区间上限, bounds 可选端点范围输出
// 返回: []strokeDashSpan 闭合虚线区间, error 参数或资源及精度错误
func strokeDashSpansWithBounds(length, thickness float64, pattern []float64, offset float64, maxSpans int, bounds *[]strokeDashBounds) ([]strokeDashSpan, error) {
	if bounds != nil {
		*bounds = nil
	}
	if !geometryFinite(length, thickness, offset) || length < 0 || thickness < 0 || len(pattern)%2 != 0 || maxSpans < 0 {
		return nil, fmt.Errorf("%w: invalid stroke dash parameters", ErrInvalid)
	}
	if len(pattern) > strokeDashMaxPattern {
		return nil, fmt.Errorf("%w: stroke dash pattern size", ErrLimit)
	}
	period := new(big.Rat)
	for _, value := range pattern {
		if !geometryFinite(value) || value < 0 {
			return nil, fmt.Errorf("%w: invalid stroke dash entry", ErrInvalid)
		}
		period.Add(period, new(big.Rat).SetFloat64(value))
	}
	if period.Sign() == 0 {
		if maxSpans == 0 {
			return nil, fmt.Errorf("%w: stroke dash span budget", ErrLimit)
		}
		if bounds != nil {
			*bounds = []strokeDashBounds{{start: strokeDistanceRange{0, 0}, end: strokeDistanceRange{length, length}, startClipped: true, endClipped: true}}
		}
		return []strokeDashSpan{{0, length}}, nil
	}
	if thickness == 0 {
		return nil, fmt.Errorf("%w: zero-thickness dash requires a device stroke policy", ErrUnsupported)
	}
	width := new(big.Rat).SetFloat64(thickness)
	distance := new(big.Rat).SetFloat64(length)
	extent := new(big.Rat).Quo(distance, width)
	phase := new(big.Rat).SetFloat64(offset)
	cycles := strokeDashInteger(new(big.Rat).Quo(phase, period), false)
	phase.Sub(phase, new(big.Rat).Mul(new(big.Rat).SetInt(cycles), period))
	prefix := new(big.Rat)
	var runs []strokeDashRun
	total := 0
	for i := 0; i < len(pattern); i += 2 {
		start := new(big.Rat).Sub(prefix, phase)
		end := new(big.Rat).Add(start, new(big.Rat).SetFloat64(pattern[i]))
		first := strokeDashInteger(new(big.Rat).Quo(new(big.Rat).Neg(end), period), true)
		last := strokeDashInteger(new(big.Rat).Quo(new(big.Rat).Sub(extent, start), period), false)
		count := new(big.Int).Sub(last, first)
		count.Add(count, big.NewInt(1))
		if count.Sign() > 0 {
			if count.Cmp(big.NewInt(int64(maxSpans-total))) > 0 {
				return nil, fmt.Errorf("%w: stroke dash span budget", ErrLimit)
			}
			n := int(count.Int64())
			total += n
			if total > (strokeDashMaxWork-2*len(pattern))/(2+bits.Len(uint(total))) {
				return nil, fmt.Errorf("%w: stroke dash work budget", ErrLimit)
			}
			runs = append(runs, strokeDashRun{start, end, first, n})
		}
		prefix.Add(prefix, new(big.Rat).SetFloat64(pattern[i]))
		prefix.Add(prefix, new(big.Rat).SetFloat64(pattern[i+1]))
	}
	if total == 0 {
		return nil, nil
	}
	exact := make([]strokeDashExactSpan, 0, total)
	for _, run := range runs {
		shift := new(big.Rat).Mul(new(big.Rat).SetInt(run.first), period)
		start := new(big.Rat).Add(run.start, shift)
		end := new(big.Rat).Add(run.end, shift)
		for i := 0; i < run.count; i++ {
			a, b := new(big.Rat).Set(start), new(big.Rat).Set(end)
			startClipped, endClipped := a.Sign() < 0, b.Cmp(extent) > 0
			if a.Sign() < 0 {
				a.SetInt64(0)
			}
			if b.Cmp(extent) > 0 {
				b.Set(extent)
			}
			exact = append(exact, strokeDashExactSpan{a.Mul(a, width), b.Mul(b, width), startClipped, endClipped})
			start.Add(start, period)
			end.Add(end, period)
		}
	}
	sort.Slice(exact, func(i, j int) bool {
		if order := exact[i].start.Cmp(exact[j].start); order != 0 {
			return order < 0
		}
		return exact[i].end.Cmp(exact[j].end) < 0
	})
	spans := make([]strokeDashSpan, total)
	var outputBounds []strokeDashBounds
	if bounds != nil {
		outputBounds = make([]strokeDashBounds, total)
	}
	for i, span := range exact {
		a, err := strokeDashCoordinate(span.start, distance, length)
		if err != nil {
			return nil, err
		}
		b, err := strokeDashCoordinate(span.end, distance, length)
		if err != nil {
			return nil, err
		}
		if span.start.Cmp(span.end) < 0 && a >= b {
			return nil, fmt.Errorf("%w: stroke dash length lost to rounding", ErrLimit)
		}
		if i > 0 && exact[i-1].end.Cmp(span.start) < 0 && spans[i-1].end >= a {
			return nil, fmt.Errorf("%w: stroke dash gap lost to rounding", ErrLimit)
		}
		spans[i] = strokeDashSpan{a, b}
		if bounds != nil {
			outputBounds[i] = strokeDashBounds{start: strokeDashDistanceRange(span.start), end: strokeDashDistanceRange(span.end), startClipped: span.startClipped, endClipped: span.endClipped}
		}
	}
	if bounds != nil {
		*bounds = outputBounds
	}
	return spans, nil
}

// strokeDashDistanceRange 将精确非负距离转换为最窄的浮点包围区间
// 入参: value 精确距离
// 返回: strokeDistanceRange 距离上下界，精确可表示时两者相等
func strokeDashDistanceRange(value *big.Rat) strokeDistanceRange {
	v, exact := value.Float64()
	if exact {
		return strokeDistanceRange{v, v}
	}
	if new(big.Rat).SetFloat64(v).Cmp(value) < 0 {
		return strokeDistanceRange{v, math.Nextafter(v, math.Inf(1))}
	}
	return strokeDistanceRange{math.Nextafter(v, math.Inf(-1)), v}
}

// strokeDashInteger 对精确有理数向指定方向取整
// 入参: value 待取整数值, ceiling 是否向正无穷取整
// 返回: *big.Int 整数结果
func strokeDashInteger(value *big.Rat, ceiling bool) *big.Int {
	q, r := new(big.Int), new(big.Int)
	q.QuoRem(value.Num(), value.Denom(), r)
	if r.Sign() != 0 {
		if ceiling && value.Sign() > 0 {
			q.Add(q, big.NewInt(1))
		} else if !ceiling && value.Sign() < 0 {
			q.Sub(q, big.NewInt(1))
		}
	}
	return q
}

// strokeDashCoordinate 舍入距离坐标并拒绝舍入造成的伪端点接触
// 入参: value 精确距离, extent 精确总弧长, length 总弧长浮点值
// 返回: float64 舍入距离, error 端点精度限制错误
func strokeDashCoordinate(value, extent *big.Rat, length float64) (float64, error) {
	f, _ := value.Float64()
	if !geometryFinite(f) || value.Sign() > 0 && f == 0 || value.Cmp(extent) < 0 && f == length {
		return 0, fmt.Errorf("%w: stroke dash endpoint contact lost to rounding", ErrLimit)
	}
	return f, nil
}

// strokeDistanceBounds 用绝对误差构造非负距离范围，精确距离不额外扩张
// 入参: value 距离近似值, errorBound 非负绝对误差
// 返回: strokeDistanceRange 向外舍入的距离范围
func strokeDistanceBounds(value, errorBound float64) strokeDistanceRange {
	if errorBound == 0 {
		return strokeDistanceRange{value, value}
	}
	return strokeDistanceRange{max(0, math.Nextafter(value-errorBound, math.Inf(-1))), math.Nextafter(value+errorBound, math.Inf(1))}
}

// strokePathChordLength 计算输出弦长及舍入余量，轴向与可证精确平方根保留零误差
// 入参: a 弦起点, b 弦终点
// 返回: float64 弦长, float64 绝对误差余量, error 长度超出表示范围错误
func strokePathChordLength(a, b Point) (float64, float64, error) {
	x, y := b.X-a.X, b.Y-a.Y
	length := math.Hypot(x, y)
	if !geometryFinite(x, y, length) {
		return 0, 0, fmt.Errorf("%w: stroke chord length range", ErrLimit)
	}
	errorBound := strokeCurveUp(strokeCurveSumError(b.X, -a.X, x) + strokeCurveSumError(b.Y, -a.Y, y))
	if x == 0 || y == 0 {
		return length, errorBound, nil
	}
	xx, yy := x*x, y*y
	square := xx + yy
	scaled := math.Abs(x) >= 0x1p-450 && math.Abs(y) >= 0x1p-450 && math.Abs(x) <= 0x1p450 && math.Abs(y) <= 0x1p450
	exact := errorBound == 0 && scaled && geometryFinite(square) && math.FMA(x, x, -xx) == 0 && math.FMA(y, y, -yy) == 0 && strokeCurveSumError(xx, yy, square) == 0 && math.FMA(length, length, -square) == 0
	if !exact {
		errorBound = strokeCurveUp(errorBound + strokeCurveRound(length))
	}
	return length, errorBound, nil
}

// strokePathMeasure 计算输出弦长前缀，并合并曲线展开、长度计算及求和误差
// 入参: run 含逐顶点曲线误差的描边连续段
// 返回: error 累计距离或误差超出表示范围错误
func strokePathMeasure(run *strokePathRun) error {
	run.distance = make([]float64, len(run.points))
	run.lengthBounds = make([]strokeDistanceRange, len(run.points))
	arithmetic := 0.0
	for i := 1; i < len(run.points); i++ {
		length, rounding, err := strokePathChordLength(run.points[i-1], run.points[i])
		if err != nil {
			return err
		}
		previous := run.distance[i-1]
		next := previous + length
		if !geometryFinite(next) || length > 0 && next <= previous {
			return fmt.Errorf("%w: stroke centerline length precision", ErrLimit)
		}
		arithmetic = strokeCurveUp(strokeCurveUp(arithmetic+rounding) + strokeCurveSumError(previous, length, next))
		errorBound := arithmetic
		if len(run.lengthErrors) != 0 {
			errorBound = strokeCurveUp(errorBound + run.lengthErrors[i])
		}
		bounds := strokeDistanceBounds(next, errorBound)
		bounds.lower = max(bounds.lower, run.lengthBounds[i-1].lower)
		bounds.upper = max(bounds.upper, run.lengthBounds[i-1].upper)
		if !geometryFinite(bounds.lower, bounds.upper) {
			return fmt.Errorf("%w: stroke length interval range", ErrLimit)
		}
		run.distance[i], run.lengthBounds[i] = next, bounds
	}
	return nil
}

// strokePathDashSpans 在真实总长范围内检查虚线接触关系，并验证内部端点的位置与方向
// 入参: run 含累计距离界的连续段, path 虚线样式, angle 允许的切线角误差, tolerance 弧长定位误差, maxSpans 片段数量上限, work 剩余定位工作量
// 返回: []strokeDashSpan 可在近似折线上截取的区间, error 精度或资源限制错误
func strokePathDashSpans(run strokePathRun, path *Path, angle, tolerance float64, maxSpans int, work *int) ([]strokeDashSpan, error) {
	cost := 2*len(path.StrokeDashArray) + 2
	if cost > *work {
		return nil, fmt.Errorf("%w: stroke dash localization work budget", ErrLimit)
	}
	*work -= cost
	last := len(run.distance) - 1
	length, extent := run.distance[last], run.lengthBounds[last]
	var bounds []strokeDashBounds
	cost = 16*bits.Len(uint(len(run.points))) + 8
	spans, err := strokeDashSpansWithBounds(extent.upper, path.StrokeThickness, path.StrokeDashArray, path.StrokeDashOffset, min(maxSpans, *work/cost), &bounds)
	if err != nil {
		return nil, err
	}
	*work -= cost * len(spans)
	for i, bound := range bounds {
		for j, endpoint := range []strokeDistanceRange{bound.start, bound.end} {
			clipped := j == 0 && bound.startClipped || j == 1 && bound.endClipped
			if !clipped && extent.lower != extent.upper && endpoint.lower <= extent.upper && endpoint.upper >= extent.lower {
				return nil, errStrokePathRefine
			}
			if clipped || endpoint.upper == 0 || endpoint.lower == length && endpoint.upper == length && extent.lower == extent.upper {
				continue
			}
			distance := spans[i].start
			if j == 1 {
				distance = spans[i].end
			}
			if err := strokePathDashEndpoint(run, endpoint, distance, j == 0, angle, tolerance, work); err != nil {
				return nil, err
			}
		}
		if bound.endClipped {
			spans[i].end = length
		}
	}
	return spans, nil
}

// strokePathDashEndpoint 联合检查距离范围内的候选弦方向，拒绝未确定的原始连接归属
// 入参: run 描边连续段, target 真实虚线距离范围, distance 输出折线距离, outgoing 是否采用出射侧, angle 总切线角预算, tolerance 距离定位预算, work 剩余候选弦检查次数
// 返回: error 需要继续细分或距离表示范围错误
func strokePathDashEndpoint(run strokePathRun, target strokeDistanceRange, distance float64, outgoing bool, angle, tolerance float64, work *int) error {
	n := len(run.points)
	first := sort.Search(n, func(i int) bool {
		if outgoing {
			return run.lengthBounds[i].upper > target.lower
		}
		return run.lengthBounds[i].upper >= target.lower
	})
	point, direction := strokePathPosition(run, distance, outgoing)
	if err := strokePathPositionCheck(run, distance, outgoing, point, tolerance/2); err != nil {
		return err
	}
	limit := 2 * math.Sin(angle/4) * (1 - 0x1p-45)
	rounding := max(distance-target.lower, target.upper-distance)
	found := false
	for i := max(1, first); i < n; i++ {
		if *work == 0 {
			return fmt.Errorf("%w: stroke dash candidate work budget", ErrLimit)
		}
		*work--
		left, right := run.lengthBounds[i-1], run.lengthBounds[i]
		if left.lower > target.upper || !outgoing && left.lower == target.upper {
			break
		}
		if run.points[i-1] == run.points[i] {
			if left != right {
				return errStrokePathRefine
			}
			continue
		}
		found = true
		for _, j := range []int{i - 1, i} {
			b, d := run.lengthBounds[j], run.distance[j]
			errorBound := strokeCurveUp(max(d-b.lower, b.upper-d) + rounding)
			if errorBound > tolerance/2 {
				return errStrokePathRefine
			}
			if run.joins[j] && b.lower <= target.upper && b.upper >= target.lower && (b.lower != b.upper || target.lower != target.upper) {
				return errStrokePathRefine
			}
		}
		candidate := strokeOutlineDirection(run.points[i-1], run.points[i])
		difference := math.Hypot(candidate.X-direction.X, candidate.Y-direction.Y)
		if difference != 0 && strokeCurveUp(difference+0x1p-45) > limit {
			return errStrokePathRefine
		}
	}
	if !found {
		return errStrokePathRefine
	}
	return nil
}

// strokePathPositionCheck 检查切分点相对精确线性插值的舍入误差，不能表示时不继续细分
// 入参: run 描边连续段, distance 输出距离, outgoing 单侧方向选择, point 待验证坐标, tolerance 局部位置误差预算
// 返回: error 插值坐标无法满足误差预算的错误
func strokePathPositionCheck(run strokePathRun, distance float64, outgoing bool, point Point, tolerance float64) error {
	if !geometryFinite(point.X, point.Y) {
		return fmt.Errorf("%w: stroke dash interpolation range", ErrLimit)
	}
	i := strokePathPositionIndex(run, distance, outgoing)
	d0, d1 := run.distance[i-1], run.distance[i]
	if distance == d0 || distance == d1 {
		return nil
	}
	c := strokeMiterInterval{}.constant
	fraction := c(distance).sub(c(d0)).quo(c(d1).sub(c(d0)))
	for _, values := range [][3]float64{{run.points[i-1].X, run.points[i].X, point.X}, {run.points[i-1].Y, run.points[i].Y, point.Y}} {
		a, b, value := values[0], values[1], values[2]
		interval := c(a).mul(c(1).sub(fraction)).add(c(b).mul(fraction))
		bound := strokeCurveUp(max(value-interval.low, interval.high-value))
		if geometryFinite(bound) && bound <= tolerance/2 {
			continue
		}
		ratio := new(big.Rat).Sub(new(big.Rat).SetFloat64(distance), new(big.Rat).SetFloat64(d0))
		denominator := new(big.Rat).Sub(new(big.Rat).SetFloat64(d1), new(big.Rat).SetFloat64(d0))
		ratio.Quo(ratio, denominator)
		exact := new(big.Rat).Sub(new(big.Rat).SetFloat64(b), new(big.Rat).SetFloat64(a))
		exact.Mul(exact, ratio).Add(exact, new(big.Rat).SetFloat64(a))
		exact.Sub(exact, new(big.Rat).SetFloat64(value)).Abs(exact)
		if exact.Cmp(new(big.Rat).SetFloat64(tolerance/2)) > 0 {
			return fmt.Errorf("%w: stroke dash interpolation precision", ErrLimit)
		}
	}
	return nil
}

// strokeOutlineCapValid 检查描边端帽枚举，不隐式填入默认样式
// 入参: cap 端帽属性值
// 返回: bool 是否为支持的端帽
func strokeOutlineCapValid(cap LineCap) bool {
	return cap == LineCapFlat || cap == LineCapSquare || cap == LineCapRound || cap == LineCapTriangle
}

// strokeOutlineDirection 计算不同有限端点之间的单位方向，避免差值及长度溢出
// 入参: p 起点, q 终点
// 返回: Point 单位方向
func strokeOutlineDirection(p, q Point) Point {
	x, y := q.X-p.X, q.Y-p.Y
	if !geometryFinite(x, y) {
		x, y = geometryHalfDifference(q.X, p.X), geometryHalfDifference(q.Y, p.Y)
	}
	scale := max(math.Abs(x), math.Abs(y))
	x, y = x/scale, y/scale
	norm := math.Hypot(x, y)
	return Point{x / norm, y / norm}
}

// segment 扩展线段两侧的半宽，先变换锚点再变换偏移以保留大坐标下的小笔宽
// 入参: p 局部起点, q 局部终点, direction 局部单位方向
// 返回: error 数值表示或边数预算错误
func (b *strokeOutlineBuilder) segment(p, q, direction Point) error {
	n := Point{-direction.Y, direction.X}
	var vertices [4]Point
	for i, entry := range []struct {
		p Point
		n Point
	}{{p, n}, {p, Point{-n.X, -n.Y}}, {q, Point{-n.X, -n.Y}}, {q, n}} {
		var err error
		vertices[i], err = b.outlinePoint(entry.p, entry.n, b.radius)
		if err != nil {
			return err
		}
	}
	for i, p := range vertices {
		if err := b.fill.edge(p, vertices[(i+1)%len(vertices)]); err != nil {
			return err
		}
	}
	return nil
}

// polygon 将局部凸多边形统一为正向绕序，再应用设备变换并添加闭合边
// 入参: center 局部锚点, points 缩放前的相对顶点，允许重复及共线顶点, scale 非负局部缩放
// 返回: error 数值表示或边数预算错误
func (b *strokeOutlineBuilder) polygon(center Point, points []Point, scale float64) error {
	for _, p := range points {
		if !geometryFinite(p.X, p.Y) {
			return fmt.Errorf("%w: stroke outline coordinate overflow", ErrLimit)
		}
	}
	sign := 0
	for i := 1; i+1 < len(points); i++ {
		if points[i] == points[0] || points[i+1] == points[0] {
			continue
		}
		sign = strokeOutlineTriangleSign([3]Point{points[0], points[i], points[i+1]})
		if sign != 0 {
			break
		}
	}
	if sign == 0 {
		return nil
	}
	first, err := b.outlinePoint(center, points[0], scale)
	if err != nil {
		return err
	}
	previous := first
	for j := 1; j < len(points); j++ {
		i := j
		if sign < 0 {
			i = len(points) - j
		}
		next, err := b.outlinePoint(center, points[i], scale)
		if err != nil {
			return err
		}
		if err := b.fill.edge(previous, next); err != nil {
			return err
		}
		previous = next
	}
	return b.fill.edge(previous, first)
}

// segmentDirections 以两端切线确定法向截面，用同向三角形覆盖允许折叠的笔画片段
// 入参: p 起点, q 终点, incoming 起点正向单位切线, outgoing 终点正向单位切线
// 返回: error 坐标表示或边数预算错误
func (b *strokeOutlineBuilder) segmentDirections(p, q, incoming, outgoing Point) error {
	if incoming == outgoing {
		return b.segment(p, q, incoming)
	}
	a := Point{-incoming.Y, incoming.X}
	z := Point{-outgoing.Y, outgoing.X}
	var vertices [4]Point
	for i, entry := range []struct {
		center Point
		offset Point
	}{{p, a}, {p, Point{-a.X, -a.Y}}, {q, Point{-z.X, -z.Y}}, {q, z}} {
		var err error
		vertices[i], err = b.outlinePoint(entry.center, entry.offset, b.radius)
		if err != nil {
			return err
		}
	}
	orientation := geometryMatrixOrientation(b.transform)
	for _, triangle := range [][3]Point{{vertices[0], vertices[1], vertices[2]}, {vertices[0], vertices[2], vertices[3]}} {
		sign := strokeOutlineTriangleSign(triangle)
		if sign == 0 || orientation == 0 {
			continue
		}
		if sign != orientation {
			triangle[1], triangle[2] = triangle[2], triangle[1]
		}
		for i, point := range triangle {
			if err := b.fill.edge(point, triangle[(i+1)%3]); err != nil {
				return err
			}
		}
	}
	return nil
}

// strokeOutlineTriangleSign 判定有限设备坐标三角形的绕向，近共线或溢出时精确计算
// 入参: points 三角形顶点
// 返回: int 正向为1，反向为负1，共线为0
func strokeOutlineTriangleSign(points [3]Point) int {
	a, b, c := points[0], points[1], points[2]
	x, y := (b.X-a.X)*(c.Y-a.Y), (b.Y-a.Y)*(c.X-a.X)
	bound := (math.Abs(x)+math.Abs(y))*8*(math.Nextafter(1, 2)-1) + 16*math.SmallestNonzeroFloat64
	if geometryFinite(x, y, bound, x-y) && math.Abs(x-y) > bound {
		if x > y {
			return 1
		}
		return -1
	}
	ax, ay := new(big.Rat).SetFloat64(a.X), new(big.Rat).SetFloat64(a.Y)
	bx, by := new(big.Rat).SetFloat64(b.X), new(big.Rat).SetFloat64(b.Y)
	cx, cy := new(big.Rat).SetFloat64(c.X), new(big.Rat).SetFloat64(c.Y)
	left := new(big.Rat).Mul(new(big.Rat).Sub(bx, ax), new(big.Rat).Sub(cy, ay))
	right := new(big.Rat).Mul(new(big.Rat).Sub(by, ay), new(big.Rat).Sub(cx, ax))
	return left.Cmp(right)
}

// round 添加正向参数角不大于半周的圆扇区，圆弧在设备空间受误差及细分预算约束
// 入参: center 局部圆心, from 单位起始半径, to 单位终止半径
// 返回: error 数值表示或预算错误
func (b *strokeOutlineBuilder) round(center, from, to Point) error {
	if !geometryFinite(center.X, center.Y, from.X, from.Y, to.X, to.Y, b.radius) || from == (Point{}) || to == (Point{}) || b.radius < 0 {
		return fmt.Errorf("%w: stroke round parameters", ErrInvalid)
	}
	turn := 0
	if from != to && from != (Point{-to.X, -to.Y}) {
		turn = strokeOutlineTriangleSign([3]Point{{}, from, to})
	}
	if turn < 0 {
		return fmt.Errorf("%w: stroke round exceeds half turn", ErrInvalid)
	}
	if turn == 0 && (from.X != 0 && math.Signbit(from.X) == math.Signbit(to.X) || from.X == 0 && math.Signbit(from.Y) == math.Signbit(to.Y)) {
		return nil
	}
	c, err := b.outlinePoint(center, Point{}, 1)
	if err != nil {
		return err
	}
	first, err := b.outlinePoint(center, from, b.radius)
	if err != nil {
		return err
	}
	last, err := b.outlinePoint(center, to, b.radius)
	if err != nil {
		return err
	}
	points, splits, ok, err := strokeRoundPoints(strokeMiterInterval{}, b, center, from, to, first, last, turn == 0)
	for precision := uint(128); !ok && err == nil && precision <= 4096; precision *= 2 {
		points, splits, ok, err = strokeRoundPoints(strokeMiterWide{precision: precision}, b, center, from, to, first, last, turn == 0)
	}
	if err != nil {
		return err
	}
	if !ok {
		return fmt.Errorf("%w: stroke round coordinate precision exceeds tolerance", ErrLimit)
	}
	b.fill.splits += splits
	previous := c
	for _, point := range points {
		if err := b.fill.edge(previous, point); err != nil {
			return err
		}
		previous = point
	}
	return b.fill.edge(previous, c)
}

// cap 构造半方形、半圆或等高三角形描边端帽
// 入参: p 端点, outward 向路径外侧的单位切向, cap 端帽枚举
// 返回: error 数值表示或预算错误
func (b *strokeOutlineBuilder) cap(p, outward Point, cap LineCap) error {
	n := Point{outward.Y, -outward.X}
	switch cap {
	case LineCapFlat:
		return nil
	case LineCapRound:
		return b.round(p, n, Point{-n.X, -n.Y})
	case LineCapSquare, LineCapTriangle:
		var vertices [4]Point
		right, err := b.outlinePoint(p, n, b.radius)
		if err != nil {
			return err
		}
		left, err := b.outlinePoint(p, Point{-n.X, -n.Y}, b.radius)
		if err != nil {
			return err
		}
		vertices[0] = right
		if cap == LineCapTriangle {
			vertices[1], err = b.outlinePoint(p, outward, b.radius)
			vertices[2] = left
			if err != nil {
				return err
			}
			return b.devicePolygon(vertices[:3])
		}
		vertices[1], err = b.outlineCombination(p, n, outward, b.radius)
		if err != nil {
			return err
		}
		vertices[2], err = b.outlineCombination(p, Point{-n.X, -n.Y}, outward, b.radius)
		if err != nil {
			return err
		}
		vertices[3] = left
		return b.devicePolygon(vertices[:])
	}
	return fmt.Errorf("%w: stroke cap", ErrInvalid)
}

// join 补齐路径外角连接，Miter超限时在角平分线法向平面裁剪
// 入参: p 连接点, incoming 入射单位方向, outgoing 出射单位方向, join 连接枚举, limit 有效尖角限制
// 返回: error 数值表示或预算错误
func (b *strokeOutlineBuilder) join(p, incoming, outgoing Point, join LineJoin, limit float64) error {
	if join == LineJoinMiter {
		return b.miter(p, incoming, outgoing, limit)
	}
	cross := strokeOutlineTriangleSign([3]Point{{}, incoming, outgoing})
	dot := incoming.X*outgoing.X + incoming.Y*outgoing.Y
	if cross == 0 && dot >= 0 {
		return nil
	}
	n1, n2 := Point{incoming.Y, -incoming.X}, Point{outgoing.Y, -outgoing.X}
	if cross < 0 {
		n1, n2 = Point{-n1.X, -n1.Y}, Point{-n2.X, -n2.Y}
	}
	if join == LineJoinRound {
		if cross < 0 {
			n1, n2 = n2, n1
		}
		return b.round(p, n1, n2)
	}
	if join == LineJoinBevel {
		return b.polygon(p, []Point{{}, n1, n2}, b.radius)
	}
	return fmt.Errorf("%w: stroke join", ErrInvalid)
}

// outlinePoint 在设备空间检查缩放偏移与锚点的总舍入误差，极端抵消时直接计算精确仿射式
// 入参: center 描边空间锚点, offset 未缩放偏移, scale 偏移比例
// 返回: Point 设备坐标, error 无法满足坐标误差预算的错误
func (b *strokeOutlineBuilder) outlinePoint(center, offset Point, scale float64) (Point, error) {
	return b.outlineCombination(center, offset, Point{}, scale)
}

// outlineCombination 保留两个方向分量之和与半宽乘积的完整仿射表达式，避免端帽角点预舍入
// 入参: center 描边空间锚点, offset 第一偏移, extra 第二偏移, scale 公共比例
// 返回: Point 设备坐标, error 表示范围或数值精度错误
func (b *strokeOutlineBuilder) outlineCombination(center, offset, extra Point, scale float64) (Point, error) {
	m := b.transform
	var result Point
	constant := strokeMiterInterval{}.constant
	x := constant(center.X).add(constant(offset.X).add(constant(extra.X)).mul(constant(scale)))
	y := constant(center.Y).add(constant(offset.Y).add(constant(extra.Y)).mul(constant(scale)))
	combined := Point{offset.X + extra.X, offset.Y + extra.Y}
	underflow := scale != 0 && (combined.X != 0 && math.Abs(combined.X*scale) < 0x1p-1022 || combined.Y != 0 && math.Abs(combined.Y*scale) < 0x1p-1022)
	for axis := 0; axis < 2; axis++ {
		a, c, e := m.A, m.C, m.E
		if axis == 1 {
			a, c, e = m.B, m.D, m.F
		}
		interval := x.mul(constant(a)).add(y.mul(constant(c))).add(constant(e))
		anchor := geometryLinearCombination(e, a, center.X, c, center.Y)
		value := math.NaN()
		if geometryFinite(anchor, combined.X*scale, combined.Y*scale) {
			value = geometryLinearCombination(anchor, a, combined.X*scale, c, combined.Y*scale)
		}
		bound := math.Nextafter(max(value-interval.low, interval.high-value), math.Inf(1))
		if underflow || !geometryFinite(value, bound) || bound > b.fill.tolerance/4 {
			xo := new(big.Rat).Add(new(big.Rat).SetFloat64(offset.X), new(big.Rat).SetFloat64(extra.X))
			yo := new(big.Rat).Add(new(big.Rat).SetFloat64(offset.Y), new(big.Rat).SetFloat64(extra.Y))
			xr := new(big.Rat).Add(new(big.Rat).SetFloat64(center.X), xo.Mul(xo, new(big.Rat).SetFloat64(scale)))
			yr := new(big.Rat).Add(new(big.Rat).SetFloat64(center.Y), yo.Mul(yo, new(big.Rat).SetFloat64(scale)))
			xr.Mul(xr, new(big.Rat).SetFloat64(a))
			yr.Mul(yr, new(big.Rat).SetFloat64(c))
			xr.Add(xr, yr).Add(xr, new(big.Rat).SetFloat64(e))
			value, _ = xr.Float64()
			if !geometryFinite(value) {
				return Point{}, fmt.Errorf("%w: stroke outline coordinate overflow", ErrLimit)
			}
			xr.Sub(xr, new(big.Rat).SetFloat64(value)).Abs(xr)
			if xr.Cmp(new(big.Rat).SetFloat64(b.fill.tolerance/4)) > 0 {
				return Point{}, fmt.Errorf("%w: stroke outline coordinate precision exceeds tolerance", ErrLimit)
			}
		}
		if axis == 0 {
			result.X = value
		} else {
			result.Y = value
		}
	}
	return result, nil
}

// devicePolygon 将已验证的设备多边形顶点按变换绕向加入统一覆盖，不再次变换坐标
// 入参: points 设备空间凸多边形顶点
// 返回: error 边数预算错误
func (b *strokeOutlineBuilder) devicePolygon(points []Point) error {
	orientation := geometryMatrixOrientation(b.transform)
	sign := 0
	for i := 1; i+1 < len(points) && sign == 0; i++ {
		sign = strokeOutlineTriangleSign([3]Point{points[0], points[i], points[i+1]})
	}
	if sign == 0 || orientation == 0 {
		return nil
	}
	previous := points[0]
	for j := 1; j < len(points); j++ {
		i := j
		if sign != orientation {
			i = len(points) - j
		}
		if err := b.fill.edge(previous, points[i]); err != nil {
			return err
		}
		previous = points[i]
	}
	return b.fill.edge(previous, points[0])
}

// atLeast 检查浮点区间下界是否达到指定阈值
// 入参: value 阈值
// 返回: bool 是否可以证明不小于阈值
func (v strokeMiterInterval) atLeast(value float64) bool {
	return v.low >= value
}

// upperAbs 提取浮点区间绝对值的可靠上界
// 返回: float64 绝对值上界，无效区间返回正无穷
func (v strokeMiterInterval) upperAbs() float64 {
	if math.IsNaN(v.low) || math.IsNaN(v.high) {
		return math.Inf(1)
	}
	return max(math.Abs(v.low), math.Abs(v.high))
}

// near 检查共享截面坐标相对完整浮点区间的误差
// 入参: value 既有设备坐标, tolerance 坐标轴误差预算
// 返回: bool 是否获得误差证书
func (v strokeMiterInterval) near(value, tolerance float64) bool {
	bound := math.Nextafter(max(value-v.low, v.high-value), math.Inf(1))
	return geometryFinite(v.low, v.high, value, bound) && bound <= tolerance
}

// atLeast 检查高精度区间下界是否达到指定阈值
// 入参: value 阈值
// 返回: bool 是否可以证明不小于阈值
func (v strokeMiterWide) atLeast(value float64) bool {
	return v.low != nil && v.low.Cmp(new(big.Float).SetFloat64(value)) >= 0
}

// upperAbs 向上舍入高精度区间绝对值上界
// 返回: float64 绝对值上界，无效或超范围区间返回正无穷
func (v strokeMiterWide) upperAbs() float64 {
	if v.low == nil {
		return math.Inf(1)
	}
	lo, hi := new(big.Float).Abs(v.low), new(big.Float).Abs(v.high)
	if lo.Cmp(hi) > 0 {
		hi = lo
	}
	value, accuracy := hi.Float64()
	if accuracy == big.Below {
		value = math.Nextafter(value, math.Inf(1))
	}
	return value
}

// near 检查共享截面坐标相对完整高精度区间的误差
// 入参: value 既有设备坐标, tolerance 坐标轴误差预算
// 返回: bool 是否获得误差证书
func (v strokeMiterWide) near(value, tolerance float64) bool {
	if v.low == nil || !geometryFinite(value) {
		return false
	}
	x := new(big.Float).SetFloat64(value)
	e0 := v.operation(x, new(big.Float).Neg(v.low), big.ToPositiveInf, '+')
	e1 := v.operation(v.high, new(big.Float).Neg(x), big.ToPositiveInf, '+')
	budget := new(big.Float).SetFloat64(tolerance)
	return e0.Cmp(budget) <= 0 && e1.Cmp(budget) <= 0
}

// strokeRoundNormalize 以区间平方根归一化非零方向
// 入参: vector 非零方向区间
// 返回: [2]T 单位方向区间
func strokeRoundNormalize[T strokeRoundNumber[T]](vector [2]T) [2]T {
	norm := vector[0].square().add(vector[1].square()).sqrt()
	return [2]T{vector[0].quo(norm), vector[1].quo(norm)}
}

// device 在完整设备仿射表达式末端计算圆上点或相对位移
// 入参: vector 单位方向或相对方向区间, relative 是否忽略锚点和平移
// 返回: [2]T 设备坐标或位移区间
func (b *strokeRoundBuilder[T]) device(vector [2]T, relative bool) [2]T {
	f := b.number.constant
	m := b.source.transform
	x, y := vector[0].mul(f(b.source.radius)), vector[1].mul(f(b.source.radius))
	if !relative {
		x, y = x.add(f(b.center.X)), y.add(f(b.center.Y))
	}
	x, y = x.mul(f(m.A)).add(y.mul(f(m.C))), x.mul(f(m.B)).add(y.mul(f(m.D)))
	if !relative {
		x, y = x.add(f(m.E)), y.add(f(m.F))
	}
	return [2]T{x, y}
}

// point 优先沿主体截面的仿射路径生成圆上点，不满足证书时采用区间中心候选
// 入参: vector 精确单位方向区间, approximate 常规浮点单位方向候选
// 返回: Point 设备坐标, bool 是否通过完整区间证书
func (b *strokeRoundBuilder[T]) point(vector [2]T, approximate Point) (Point, bool) {
	device := b.device(vector, false)
	tolerance := b.source.fill.tolerance / 8
	if geometryFinite(approximate.X, approximate.Y) {
		candidate, err := b.source.outlinePoint(b.center, approximate, b.source.radius)
		if err == nil && device[0].near(candidate.X, tolerance) && device[1].near(candidate.Y, tolerance) {
			return candidate, true
		}
	}
	x, okX := device[0].coordinate(tolerance)
	y, okY := device[1].coordinate(tolerance)
	return Point{x, y}, okX && okY
}

// arc 用圆弧切线三角形到弦的设备距离上界决定是否接受叶片
// 入参: u 单位起始方向, v 单位终止方向, approximateU 起始浮点候选, approximateV 终止浮点候选, last 共享终点坐标, depth 当前二分深度
// 返回: bool 是否通过数值证书, error 深度或细分预算错误
func (b *strokeRoundBuilder[T]) arc(u, v [2]T, approximateU, approximateV, last Point, depth int) (bool, error) {
	f := b.number.constant
	sum := [2]T{u[0].add(v[0]), u[1].add(v[1])}
	squared := sum[0].square().add(sum[1].square())
	if squared.atLeast(1) {
		difference := u[0].sub(v[0]).square().add(u[1].sub(v[1]).square())
		factor := difference.quo(squared.mul(f(2)))
		delta := b.device([2]T{sum[0].mul(factor), sum[1].mul(factor)}, true)
		for _, component := range delta {
			uncertainty := component.sub(component).upperAbs()
			if !geometryFinite(uncertainty) || uncertainty > max(b.source.fill.tolerance/32, component.upperAbs()*0x1p-32) {
				return false, nil
			}
		}
		bound := math.Nextafter(math.Hypot(delta[0].upperAbs(), delta[1].upperAbs()), math.Inf(1))
		if bound <= b.source.fill.tolerance/2 {
			if len(b.points) >= b.maxPoints {
				return false, fmt.Errorf("%w: stroke round edge budget exceeded", ErrLimit)
			}
			b.points = append(b.points, last)
			return true, nil
		}
	}
	if depth >= 64 {
		return false, nil
	}
	middle := strokeRoundNormalize(sum)
	approximate := strokeOutlineDirection(Point{}, Point{approximateU.X + approximateV.X, approximateU.Y + approximateV.Y})
	point, ok := b.point(middle, approximate)
	if !ok {
		return false, nil
	}
	if b.splits >= b.maxSplits {
		return false, fmt.Errorf("%w: stroke round subdivision budget exceeded", ErrLimit)
	}
	b.splits++
	if ok, err := b.arc(u, middle, approximateU, approximate, point, depth+1); !ok || err != nil {
		return ok, err
	}
	return b.arc(middle, v, approximate, approximateV, last, depth+1)
}

// strokeRoundPoints 生成带端点一致性与设备误差证书的圆弧折线，半周先沿正向垂线分为两段
// 入参: number 区间原型, source 描边构造器, center 圆心, from 起始方向, to 终止方向, first 共享起点, last 共享终点, opposite 是否完全反向
// 返回: []Point 圆弧点列, int 二分次数, bool 是否通过数值证书, error 资源预算错误
func strokeRoundPoints[T strokeRoundNumber[T]](number T, source *strokeOutlineBuilder, center, from, to, first, last Point, opposite bool) ([]Point, int, bool, error) {
	f := number.constant
	u := strokeRoundNormalize([2]T{f(from.X), f(from.Y)})
	v := strokeRoundNormalize([2]T{f(to.X), f(to.Y)})
	b := strokeRoundBuilder[T]{number: number, source: source, center: center, maxPoints: source.fill.maxEdges - len(source.fill.edges) - 1, maxSplits: source.fill.maxEdges - source.fill.splits}
	for _, entry := range []struct {
		vector [2]T
		point  Point
	}{{u, first}, {v, last}} {
		device := b.device(entry.vector, false)
		if !device[0].near(entry.point.X, source.fill.tolerance/8) || !device[1].near(entry.point.Y, source.fill.tolerance/8) {
			return nil, 0, false, nil
		}
	}
	if b.maxPoints < 2 || b.maxSplits < 0 {
		return nil, 0, false, fmt.Errorf("%w: stroke round edge budget exceeded", ErrLimit)
	}
	b.points = append(b.points, first)
	var ok bool
	var err error
	if opposite {
		middle := [2]T{f(0).sub(u[1]), u[0]}
		approximate := Point{-from.Y, from.X}
		point, precise := b.point(middle, approximate)
		if !precise {
			return nil, 0, false, nil
		}
		if b.maxSplits == 0 {
			return nil, 0, false, fmt.Errorf("%w: stroke round subdivision budget exceeded", ErrLimit)
		}
		b.splits = 1
		ok, err = b.arc(u, middle, from, approximate, point, 1)
		if ok && err == nil {
			ok, err = b.arc(middle, v, approximate, to, last, 1)
		}
	} else {
		ok, err = b.arc(u, v, from, to, last, 0)
	}
	if !ok || err != nil {
		return nil, 0, ok, err
	}
	return b.points, b.splits, true, nil
}

// constant 构造精确浮点常量区间
// 入参: value 有限常量
// 返回: strokeMiterInterval 单点区间
func (v strokeMiterInterval) constant(value float64) strokeMiterInterval {
	return strokeMiterInterval{value, value}
}

// add 向外舍入区间加法
// 入参: w 加数
// 返回: strokeMiterInterval 结果区间
func (v strokeMiterInterval) add(w strokeMiterInterval) strokeMiterInterval {
	return strokeMiterInterval{math.Nextafter(v.low+w.low, math.Inf(-1)), math.Nextafter(v.high+w.high, math.Inf(1))}
}

// sub 向外舍入区间减法
// 入参: w 减数
// 返回: strokeMiterInterval 结果区间
func (v strokeMiterInterval) sub(w strokeMiterInterval) strokeMiterInterval {
	return v.add(strokeMiterInterval{-w.high, -w.low})
}

// mul 向外舍入带符号区间乘法
// 入参: w 乘数
// 返回: strokeMiterInterval 结果区间
func (v strokeMiterInterval) mul(w strokeMiterInterval) strokeMiterInterval {
	a, b, c, d := v.low*w.low, v.low*w.high, v.high*w.low, v.high*w.high
	return strokeMiterInterval{math.Nextafter(min(a, b, c, d), math.Inf(-1)), math.Nextafter(max(a, b, c, d), math.Inf(1))}
}

// quo 向外舍入正除数区间除法，包含零的除数留给高精度路径
// 入参: w 正除数
// 返回: strokeMiterInterval 结果区间
func (v strokeMiterInterval) quo(w strokeMiterInterval) strokeMiterInterval {
	if w.low <= 0 {
		return strokeMiterInterval{math.NaN(), math.NaN()}
	}
	a, b, c, d := v.low/w.low, v.low/w.high, v.high/w.low, v.high/w.high
	return strokeMiterInterval{math.Nextafter(min(a, b, c, d), math.Inf(-1)), math.Nextafter(max(a, b, c, d), math.Inf(1))}
}

// square 保留平方的非负范围，避免重复变量依赖产生负下界
// 返回: strokeMiterInterval 平方区间
func (v strokeMiterInterval) square() strokeMiterInterval {
	a, b := v.low*v.low, v.high*v.high
	lo := min(a, b)
	if v.low <= 0 && v.high >= 0 {
		lo = 0
	}
	return strokeMiterInterval{max(0, math.Nextafter(lo, math.Inf(-1))), math.Nextafter(max(a, b), math.Inf(1))}
}

// sqrt 向外舍入非负区间平方根
// 返回: strokeMiterInterval 平方根区间
func (v strokeMiterInterval) sqrt() strokeMiterInterval {
	return strokeMiterInterval{max(0, math.Nextafter(math.Sqrt(max(0, v.low)), math.Inf(-1))), math.Nextafter(math.Sqrt(v.high), math.Inf(1))}
}

// minimum 包围两种尖角延伸长度的较小值，临界处不猜测裁切分支
// 入参: w 另一长度区间
// 返回: strokeMiterInterval 最小值区间
func (v strokeMiterInterval) minimum(w strokeMiterInterval) strokeMiterInterval {
	return strokeMiterInterval{min(v.low, w.low), min(v.high, w.high)}
}

// coordinate 仅在整个设备坐标区间满足绝对误差时接受舍入值
// 入参: tolerance 坐标轴误差预算
// 返回: float64 坐标, bool 是否获得有限误差证书
func (v strokeMiterInterval) coordinate(tolerance float64) (float64, bool) {
	value := v.low/2 + v.high/2
	errorBound := math.Nextafter(max(value-v.low, v.high-value), math.Inf(1))
	return value, geometryFinite(v.low, v.high, value, errorBound) && v.low <= v.high && errorBound <= tolerance
}

// constant 在当前精度构造精确的二进制浮点常量
// 入参: value 有限常量
// 返回: strokeMiterWide 单点区间
func (v strokeMiterWide) constant(value float64) strokeMiterWide {
	x := new(big.Float).SetPrec(v.precision).SetFloat64(value)
	return strokeMiterWide{x, x, v.precision}
}

// operation 对端点执行指定舍入方向的基本运算
// 入参: x 左值, y 右值, mode 舍入方向, operator 运算符
// 返回: *big.Float 运算结果
func (v strokeMiterWide) operation(x, y *big.Float, mode big.RoundingMode, operator byte) *big.Float {
	z := new(big.Float).SetPrec(v.precision).SetMode(mode)
	switch operator {
	case '+':
		return z.Add(x, y)
	case '*':
		return z.Mul(x, y)
	case '/':
		return z.Quo(x, y)
	default:
		return z.Sqrt(x)
	}
}

// add 计算向外舍入的高精度区间和
// 入参: w 加数
// 返回: strokeMiterWide 结果区间
func (v strokeMiterWide) add(w strokeMiterWide) strokeMiterWide {
	if v.low == nil || w.low == nil {
		return strokeMiterWide{precision: v.precision}
	}
	return strokeMiterWide{v.operation(v.low, w.low, big.ToNegativeInf, '+'), v.operation(v.high, w.high, big.ToPositiveInf, '+'), v.precision}
}

// sub 计算向外舍入的高精度区间差
// 入参: w 减数
// 返回: strokeMiterWide 结果区间
func (v strokeMiterWide) sub(w strokeMiterWide) strokeMiterWide {
	if w.low == nil {
		return strokeMiterWide{precision: v.precision}
	}
	return v.add(strokeMiterWide{new(big.Float).Neg(w.high), new(big.Float).Neg(w.low), v.precision})
}

// binary 计算乘除端点组合的向外舍入包围
// 入参: w 右区间, operator 乘法或除法
// 返回: strokeMiterWide 结果区间
func (v strokeMiterWide) binary(w strokeMiterWide, operator byte) strokeMiterWide {
	if v.low == nil || w.low == nil || operator == '/' && w.low.Sign() <= 0 {
		return strokeMiterWide{precision: v.precision}
	}
	var low, high *big.Float
	for _, x := range [2]*big.Float{v.low, v.high} {
		for _, y := range [2]*big.Float{w.low, w.high} {
			a, b := v.operation(x, y, big.ToNegativeInf, operator), v.operation(x, y, big.ToPositiveInf, operator)
			if low == nil || a.Cmp(low) < 0 {
				low = a
			}
			if high == nil || b.Cmp(high) > 0 {
				high = b
			}
		}
	}
	return strokeMiterWide{low, high, v.precision}
}

// mul 计算高精度区间积
// 入参: w 乘数
// 返回: strokeMiterWide 结果区间
func (v strokeMiterWide) mul(w strokeMiterWide) strokeMiterWide {
	return v.binary(w, '*')
}

// quo 计算正除数的高精度区间商
// 入参: w 除数
// 返回: strokeMiterWide 结果区间
func (v strokeMiterWide) quo(w strokeMiterWide) strokeMiterWide {
	return v.binary(w, '/')
}

// square 计算非负高精度平方区间
// 返回: strokeMiterWide 平方区间
func (v strokeMiterWide) square() strokeMiterWide {
	w := v.mul(v)
	if w.low != nil && w.low.Sign() < 0 {
		w.low = new(big.Float).SetPrec(v.precision)
	}
	return w
}

// sqrt 计算向外舍入的高精度平方根区间
// 返回: strokeMiterWide 平方根区间
func (v strokeMiterWide) sqrt() strokeMiterWide {
	if v.low == nil {
		return v
	}
	return strokeMiterWide{v.operation(v.low, nil, big.ToNegativeInf, 's'), v.operation(v.high, nil, big.ToPositiveInf, 's'), v.precision}
}

// minimum 包围高精度区间的最小值，避免裁切阈值附近的不稳定分支
// 入参: w 另一长度区间
// 返回: strokeMiterWide 最小值区间
func (v strokeMiterWide) minimum(w strokeMiterWide) strokeMiterWide {
	if v.low == nil || w.low == nil {
		return strokeMiterWide{precision: v.precision}
	}
	lo, hi := v.low, v.high
	if w.low.Cmp(lo) < 0 {
		lo = w.low
	}
	if w.high.Cmp(hi) < 0 {
		hi = w.high
	}
	return strokeMiterWide{lo, hi, v.precision}
}

// coordinate 验证最终float64坐标相对高精度区间两端的最大误差
// 入参: tolerance 坐标轴误差预算
// 返回: float64 坐标, bool 是否满足有限表示及绝对误差
func (v strokeMiterWide) coordinate(tolerance float64) (float64, bool) {
	if v.low == nil {
		return 0, false
	}
	mid := new(big.Float).SetPrec(v.precision).Add(v.low, v.high)
	mid.Quo(mid, new(big.Float).SetInt64(2))
	value, _ := mid.Float64()
	if !geometryFinite(value) {
		return 0, false
	}
	x := new(big.Float).SetFloat64(value)
	e0 := v.operation(x, new(big.Float).Neg(v.low), big.ToPositiveInf, '+')
	e1 := v.operation(v.high, new(big.Float).Neg(x), big.ToPositiveInf, '+')
	budget := new(big.Float).SetFloat64(tolerance)
	return value, e0.Cmp(budget) <= 0 && e1.Cmp(budget) <= 0
}

// strokeMiterCoordinates 由精确浮点射线方向归一化后计算裁切尖角，并在最终设备空间认证误差
// 入参: number 数值区间原型, center 连接点, incoming 入射方向, outgoing 出射方向, radius 半宽, limit 尖角限制, transform 设备矩阵, tolerance 坐标轴误差, turn 精确转向符号
// 返回: [5]Point 同一尖角的顶点, bool 是否获得全部坐标的误差证书
func strokeMiterCoordinates[T strokeMiterNumber[T]](number T, center, incoming, outgoing Point, radius, limit float64, transform Matrix, tolerance float64, turn int) ([5]Point, bool) {
	z, one, half := number.constant(0), number.constant(1), number.constant(0.5)
	ux, uy := number.constant(incoming.X), number.constant(incoming.Y)
	vx, vy := number.constant(outgoing.X), number.constant(outgoing.Y)
	un, vn := ux.square().add(uy.square()).sqrt(), vx.square().add(vy.square()).sqrt()
	ux, uy, vx, vy = ux.quo(un), uy.quo(un), vx.quo(vn), vy.quo(vn)
	h := number.constant(radius)
	side := one
	if turn < 0 {
		side = number.constant(-1)
	}
	ax, ay := uy.mul(side).mul(h), z.sub(ux).mul(side).mul(h)
	cx, cy := vy.mul(side).mul(h), z.sub(vx).mul(side).mul(h)
	var length T
	if turn == 0 {
		length = h.mul(number.constant(limit))
	} else {
		cosine := ux.add(vx).square().add(uy.add(vy).square()).sqrt().mul(half)
		sine := ux.sub(vx).square().add(uy.sub(vy).square()).sqrt().mul(half)
		clipped := number.constant(limit).sub(one).quo(sine).add(sine.quo(one.add(cosine))).mul(h)
		length = h.mul(sine).quo(cosine).minimum(clipped)
	}
	local := [5][2]T{{z, z}, {ax, ay}, {ax.add(ux.mul(length)), ay.add(uy.mul(length))}, {cx.sub(vx.mul(length)), cy.sub(vy.mul(length))}, {cx, cy}}
	var result [5]Point
	for i, p := range local {
		x, y := number.constant(center.X).add(p[0]), number.constant(center.Y).add(p[1])
		dx := x.mul(number.constant(transform.A)).add(y.mul(number.constant(transform.C))).add(number.constant(transform.E))
		dy := x.mul(number.constant(transform.B)).add(y.mul(number.constant(transform.D))).add(number.constant(transform.F))
		var okX, okY bool
		result[i].X, okX = dx.coordinate(tolerance)
		result[i].Y, okY = dy.coordinate(tolerance)
		if !okX || !okY {
			return [5]Point{}, false
		}
	}
	return result, true
}

// miter 以浮点区间作为常规路径，必要时有限次提升精度，裁切及设备舍入均不得静默超差
// 入参: p 连接点, incoming 入射方向, outgoing 出射方向, limit 有效尖角限制
// 返回: error 无法证明设备误差或边数预算不足的错误
func (b *strokeOutlineBuilder) miter(p, incoming, outgoing Point, limit float64) error {
	if !geometryFinite(p.X, p.Y, incoming.X, incoming.Y, outgoing.X, outgoing.Y, limit, b.radius) || incoming == (Point{}) || outgoing == (Point{}) || limit < 1 || b.radius < 0 {
		return fmt.Errorf("%w: stroke miter parameters", ErrInvalid)
	}
	turn := strokeOutlineTriangleSign([3]Point{{}, incoming, outgoing})
	if turn == 0 && (incoming.X != 0 && math.Signbit(incoming.X) == math.Signbit(outgoing.X) || incoming.X == 0 && math.Signbit(incoming.Y) == math.Signbit(outgoing.Y)) {
		return nil
	}
	tolerance := b.fill.tolerance / 4
	points, ok := strokeMiterCoordinates(strokeMiterInterval{}, p, incoming, outgoing, b.radius, limit, b.transform, tolerance, turn)
	for precision := uint(128); !ok && precision <= 4096; precision *= 2 {
		points, ok = strokeMiterCoordinates(strokeMiterWide{precision: precision}, p, incoming, outgoing, b.radius, limit, b.transform, tolerance, turn)
	}
	if !ok {
		return fmt.Errorf("%w: stroke miter coordinate precision exceeds tolerance", ErrLimit)
	}
	return b.devicePolygon(points[:])
}

// pathStrokeEdges 按路径段、虚线与闭合语义生成设备空间非零规则描边边集
// 入参: path 已填入规范默认值的路径, transform 有效设备变换, tolerance 正的设备误差容限, maxEdges 非负几何输出及中心线预算
// 返回: []geometryEdge 供非零规则统一覆盖的描边边集, error 参数、能力、数值或资源限制错误，失败时无部分结果
func pathStrokeEdges(path *Path, transform Matrix, tolerance float64, maxEdges int) ([]geometryEdge, error) {
	if path == nil || path.Data == nil || !geometryFillMatrixFinite(transform) || !geometryFinite(tolerance) || tolerance <= 0 || maxEdges < 0 {
		return nil, fmt.Errorf("%w: stroke path parameters", ErrInvalid)
	}
	if maxEdges > int(^uint(0)>>1)/4 {
		return nil, fmt.Errorf("%w: stroke max edges", ErrLimit)
	}
	style := strokeOutlineStyle{path.StrokeThickness, path.StrokeStartLineCap, path.StrokeEndLineCap, path.StrokeLineJoin, path.StrokeMiterLimit}
	if !geometryFinite(style.thickness, style.miter, path.StrokeDashOffset) || style.thickness < 0 || style.miter < 1 || !strokeOutlineCapValid(style.startCap) || !strokeOutlineCapValid(style.endCap) || !strokeOutlineCapValid(path.StrokeDashCap) || style.join != LineJoinMiter && style.join != LineJoinBevel && style.join != LineJoinRound {
		return nil, fmt.Errorf("%w: stroke path style", ErrInvalid)
	}
	dashed, nominal, err := strokePathDashMode(path.StrokeDashArray, path.StrokeDashOffset)
	if err != nil {
		return nil, err
	}
	geometry := IdentityMatrix()
	if path.Data.Transform != nil {
		geometry = *path.Data.Transform
	}
	if !geometryFillMatrixFinite(geometry) {
		return nil, fmt.Errorf("%w: stroke geometry transform", ErrInvalid)
	}
	segments, segmentLimit := 0, max(rasterMaxEdges, maxEdges)
	for _, figure := range path.Data.Figures {
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return nil, fmt.Errorf("%w: stroke figure start", ErrInvalid)
		}
		if segments >= segmentLimit || len(figure.Segments) > segmentLimit-1-segments {
			return nil, fmt.Errorf("%w: stroke segment budget", ErrLimit)
		}
		segments += len(figure.Segments) + 1
		for _, segment := range figure.Segments {
			if err := geometryFillValidateSegment(segment); err != nil {
				return nil, err
			}
		}
	}
	if path.Stroke == nil || geometryMatrixSingular(transform) {
		return nil, nil
	}
	transform.E = geometryLinearCombination(transform.E, transform.A, geometry.E, transform.C, geometry.F)
	transform.F = geometryLinearCombination(transform.F, transform.B, geometry.E, transform.D, geometry.F)
	geometry.E, geometry.F = 0, 0
	if !geometryFillMatrixFinite(transform) {
		return nil, fmt.Errorf("%w: stroke translation composition", ErrLimit)
	}
	if style.thickness == 0 && !nominal {
		return nil, nil
	}
	scale := math.Hypot(math.Hypot(transform.A, transform.B), math.Hypot(transform.C, transform.D))
	lengthTolerance := tolerance / max(1, scale) / float64(max(1, segments)) / 8
	if lengthTolerance == 0 || !geometryFinite(scale) {
		return nil, fmt.Errorf("%w: stroke metric tolerance", ErrLimit)
	}
	builder := strokeOutlineBuilder{fill: geometryFillBuilder{tolerance: tolerance / 4, maxEdges: maxEdges}, transform: transform, radius: style.thickness / 2}
	if builder.radius == 0 && !nominal {
		return nil, fmt.Errorf("%w: stroke radius underflow", ErrLimit)
	}
	curveGeometry, curveDevice := geometry, transform
	planningPath := *path
	deviceSpace := nominal && style.thickness == 0
	if deviceSpace {
		geometrySingular := geometryMatrixSingular(geometry)
		geometryZero := geometry.A == 0 && geometry.B == 0 && geometry.C == 0 && geometry.D == 0
		curveGeometry = strokePathCompose(transform, geometry)
		curveDevice = IdentityMatrix()
		planningPath.StrokeThickness = 1
		lengthTolerance = tolerance / float64(max(1, segments)) / 8
		if !geometryFillMatrixFinite(curveGeometry) || !geometrySingular && geometryMatrixSingular(curveGeometry) || !geometryZero && curveGeometry.A == 0 && curveGeometry.B == 0 && curveGeometry.C == 0 && curveGeometry.D == 0 {
			return nil, fmt.Errorf("%w: nominal stroke transform precision", ErrLimit)
		}
	}
	angularTolerance, err := strokePathAngleBudget(builder.radius, transform, tolerance, nominal, deviceSpace)
	if err != nil {
		return nil, err
	}
	remaining := maxEdges
	dashWork := max(strokeDashMaxWork, maxEdges)
	metric := curveDevice
	curveAngle := angularTolerance
	if dashed {
		norm := strokeCurveUp(math.Hypot(math.Hypot(metric.A, metric.B), math.Hypot(metric.C, metric.D)) * (1 + 0x1p-45))
		if !geometryFinite(norm) {
			return nil, fmt.Errorf("%w: stroke dash metric range", ErrLimit)
		}
		metric = Matrix{A: norm, D: norm}
		curveAngle /= 2
	}
	for _, figure := range path.Data.Figures {
		var pieces []strokePathPiece
		precision := lengthTolerance
		for attempt := 0; ; attempt++ {
			runs, runErr := strokePathRuns(figure, curveGeometry, metric, tolerance/4, precision, curveAngle, &remaining)
			if runErr != nil {
				return nil, runErr
			}
			pieces, err = strokePathPieces(runs, figure.IsClosed, &planningPath, dashed, angularTolerance, lengthTolerance*float64(max(1, segments)), maxEdges-len(builder.fill.edges), &dashWork)
			if err != errStrokePathRefine || attempt == 11 {
				break
			}
			precision /= 4
			if precision == 0 {
				return nil, errStrokePathRefine
			}
		}
		if err != nil {
			return nil, err
		}
		for _, piece := range pieces {
			if builder.radius != 0 {
				if err := builder.pathPiece(piece, style); err != nil {
					return nil, err
				}
			}
			if nominal {
				devicePiece := piece
				if !deviceSpace {
					devicePiece, err = strokePathDevicePiece(piece, transform)
					if err != nil {
						return nil, err
					}
				}
				firstEdge := len(builder.fill.edges)
				hairline := strokeOutlineBuilder{fill: builder.fill, transform: IdentityMatrix(), radius: 0.5}
				if err := hairline.pathPiece(devicePiece, style); err != nil {
					return nil, err
				}
				if geometryMatrixOrientation(transform) < 0 {
					for i := firstEdge; i < len(hairline.fill.edges); i++ {
						hairline.fill.edges[i].start, hairline.fill.edges[i].end = hairline.fill.edges[i].end, hairline.fill.edges[i].start
					}
				}
				builder.fill = hairline.fill
			}
		}
	}
	return builder.fill.edges, nil
}

// strokePathAngleBudget 按笔画半宽与设备误差容限分配局部切线角度预算
// 入参: radius 描边半宽, transform 有效设备变换, tolerance 设备误差预算, nominal 是否有标称轮廓, deviceSpace 是否已在设备空间展开
// 返回: float64 正的弧度上限, error 角度或变换精度超出表示范围错误
func strokePathAngleBudget(radius float64, transform Matrix, tolerance float64, nominal, deviceSpace bool) (float64, error) {
	angle := math.Pi / 8
	if deviceSpace {
		angle = strokePathRadiusAngle(tolerance, 0.5, 1)
	} else {
		scale := math.Hypot(math.Hypot(transform.A, transform.B), math.Hypot(transform.C, transform.D))
		if radius > 0 {
			angle = strokePathRadiusAngle(tolerance, radius, scale)
		}
		if nominal {
			linear := transform
			linear.E, linear.F = 0, 0
			inverse, err := linear.Inverse()
			if err != nil {
				return 0, fmt.Errorf("%w: nominal stroke direction conditioning", ErrLimit)
			}
			inverseScale := math.Hypot(math.Hypot(inverse.A, inverse.B), math.Hypot(inverse.C, inverse.D))
			condition := scale * inverseScale
			if !geometryFinite(condition) || condition == 0 {
				return 0, fmt.Errorf("%w: nominal stroke direction range", ErrLimit)
			}
			angle = min(angle, strokePathRadiusAngle(tolerance, 1, condition))
			angle = min(angle, 2*math.Asin(math.Sin(math.Pi/16)/condition/2))
		}
	}
	if angle <= 0 || !geometryFinite(angle) {
		return 0, fmt.Errorf("%w: stroke angular precision", ErrLimit)
	}
	return angle, nil
}

// strokePathRadiusAngle 按半宽与设备放大率分配法向角度，指数拆分避免中间乘除溢出
// 入参: tolerance 正的设备误差预算, radius 正的描边半宽, scale 正的设备放大率上界
// 返回: float64 弧度上限，无法表示时为零
func strokePathRadiusAngle(tolerance, radius, scale float64) float64 {
	t, et := math.Frexp(tolerance)
	r, er := math.Frexp(radius)
	s, es := math.Frexp(scale)
	ratio := math.Ldexp(t/r/s, et-er-es-4)
	return 2 * math.Asin(min(math.Sin(math.Pi/16), ratio))
}

// geometryMatrixSingular 精确区分奇异矩阵，不因逆矩阵超出浮点范围而误判
// 入参: m 系数均为有限值的仿射矩阵
// 返回: bool 线性部分是否不可逆
func geometryMatrixSingular(m Matrix) bool {
	return geometryMatrixOrientation(m) == 0
}

// geometryMatrixOrientation 精确判定线性变换的方向，乘积溢出或接近相消时使用有理数
// 入参: m 系数均为有限值的仿射矩阵
// 返回: int 保向为1，反向为负1，奇异为0
func geometryMatrixOrientation(m Matrix) int {
	p, q := m.A*m.D, m.B*m.C
	bound := (math.Abs(p) + math.Abs(q)) * 8 * (math.Nextafter(1, 2) - 1)
	if geometryFinite(p, q, bound) && math.Abs(p-q) > bound {
		if p > q {
			return 1
		}
		return -1
	}
	a, b := new(big.Rat).SetFloat64(m.A), new(big.Rat).SetFloat64(m.B)
	c, d := new(big.Rat).SetFloat64(m.C), new(big.Rat).SetFloat64(m.D)
	return new(big.Rat).Mul(a, d).Cmp(new(big.Rat).Mul(b, c))
}

// strokePathCompose 组合中心线变换，使用稳定线性组合避免中间乘积溢出
// 入参: outer 后应用的变换, inner 先应用的变换
// 返回: Matrix 组合变换，结果仍由调用方检查有限性及精度
func strokePathCompose(outer, inner Matrix) Matrix {
	return Matrix{
		A: geometryLinearCombination(0, outer.A, inner.A, outer.C, inner.B),
		B: geometryLinearCombination(0, outer.B, inner.A, outer.D, inner.B),
		C: geometryLinearCombination(0, outer.A, inner.C, outer.C, inner.D),
		D: geometryLinearCombination(0, outer.B, inner.C, outer.D, inner.D),
		E: geometryLinearCombination(outer.E, outer.A, inner.E, outer.C, inner.F),
		F: geometryLinearCombination(outer.F, outer.B, inner.E, outer.D, inner.F),
	}
}

// strokePathDevicePiece 将已完成虚线切分的片段转换为设备坐标，不改变原始虚线相位
// 入参: piece 描边空间片段, transform 有效设备变换
// 返回: strokePathPiece 独立设备中心线, error 坐标或方向表示范围错误
func strokePathDevicePiece(piece strokePathPiece, transform Matrix) (strokePathPiece, error) {
	result := piece
	result.points = make([]Point, len(piece.points))
	result.directions = make([]strokePathDirection, len(piece.directions))
	for i, point := range piece.points {
		value, err := geometryFillPoint(transform, point)
		if err != nil {
			return strokePathPiece{}, err
		}
		result.points[i] = value
	}
	for i, direction := range piece.directions {
		var err error
		result.directions[i].incoming, err = strokePathDeviceDirection(direction.incoming, transform)
		if err != nil {
			return strokePathPiece{}, err
		}
		result.directions[i].outgoing, err = strokePathDeviceDirection(direction.outgoing, transform)
		if err != nil {
			return strokePathPiece{}, err
		}
	}
	for _, entry := range []struct {
		source Point
		target *Point
	}{{piece.startDir, &result.startDir}, {piece.endDir, &result.endDir}} {
		value, err := strokePathDeviceDirection(entry.source, transform)
		if err != nil {
			return strokePathPiece{}, err
		}
		*entry.target = value
	}
	return result, nil
}

// strokePathDeviceDirection 将非零单位切线转换为设备方向，保留表示未指定切线的零值
// 入参: direction 描边空间方向, transform 有效设备变换
// 返回: Point 设备空间单位方向, error 切线超出表示范围错误
func strokePathDeviceDirection(direction Point, transform Matrix) (Point, error) {
	if direction == (Point{}) {
		return Point{}, nil
	}
	x := geometryLinearCombination(0, transform.A, direction.X, transform.C, direction.Y)
	y := geometryLinearCombination(0, transform.B, direction.X, transform.D, direction.Y)
	if !geometryFinite(x, y) || x == 0 && y == 0 {
		return Point{}, fmt.Errorf("%w: nominal stroke tangent precision", ErrLimit)
	}
	return strokeOutlineDirection(Point{}, Point{x, y}), nil
}

// strokePathDashMode 在相位归一化前精确判定虚线间隙与标称线宽模式
// 入参: pattern 原始虚线数组, offset 原始偏移
// 返回: bool 是否存在非零间隙, bool 是否使用标称线宽约定, error 数组或资源限制错误
func strokePathDashMode(pattern []float64, offset float64) (bool, bool, error) {
	if len(pattern)%2 != 0 || !geometryFinite(offset) {
		return false, false, fmt.Errorf("%w: stroke dash mode", ErrInvalid)
	}
	if len(pattern) > strokeDashMaxPattern {
		return false, false, fmt.Errorf("%w: stroke dash pattern size", ErrLimit)
	}
	period := new(big.Rat)
	dashed := false
	for i, value := range pattern {
		if !geometryFinite(value) || value < 0 {
			return false, false, fmt.Errorf("%w: stroke dash entry", ErrInvalid)
		}
		period.Add(period, new(big.Rat).SetFloat64(value))
		dashed = dashed || i%2 != 0 && value > 0
	}
	nominal := len(pattern) != 0 && new(big.Rat).SetFloat64(offset).Cmp(period.Neg(period)) < 0
	return dashed, nominal, nil
}

// strokePathRuns 展开原始段并在未描边段处分组，显式保留闭合附加段及退化连接
// 入参: figure 原始子路径, geometry 几何变换, device 设备误差度量变换, tolerance 设备展开误差, lengthTolerance 单段弧长误差, angularTolerance 切线角度上限, remaining 剩余中心线点数
// 返回: []strokePathRun 按原始顺序排列的描边连续段, error 展开或数值限制错误
func strokePathRuns(figure GeometryFigure, geometry, device Matrix, tolerance, lengthTolerance, angularTolerance float64, remaining *int) ([]strokePathRun, error) {
	var runs []strokePathRun
	var run strokePathRun
	current := figure.StartPoint
	count := len(figure.Segments)
	if figure.IsClosed {
		count++
	}
	if count == 0 {
		if *remaining < 2 {
			return nil, fmt.Errorf("%w: stroke centerline budget", ErrLimit)
		}
		point, err := geometryFillPoint(geometry, current)
		if err != nil {
			return nil, err
		}
		*remaining -= 2
		return []strokePathRun{{points: []Point{point, point}, joins: []bool{false, false}, distance: []float64{0, 0}, lengthBounds: make([]strokeDistanceRange, 2), start: true, end: true}}, nil
	}
	for i := range count {
		segment := GeometrySegment{Kind: GeometryLine, Point: figure.StartPoint, IsStroked: true}
		if i < len(figure.Segments) {
			segment = figure.Segments[i]
		}
		if !segment.IsStroked {
			if len(run.points) != 0 {
				runs = append(runs, run)
				run = strokePathRun{}
			}
			current = segment.Point
			continue
		}
		curve, err := strokeFlattenSegmentAngle(current, segment, geometry, device, tolerance, lengthTolerance, angularTolerance, *remaining)
		if err != nil {
			return nil, err
		}
		*remaining -= len(curve.points)
		if len(run.points) == 0 {
			run.points = append(run.points, curve.points[0])
			run.joins = append(run.joins, false)
			run.directions = append(run.directions, strokePathDirection{})
			run.lengthErrors = append(run.lengthErrors, 0)
			run.start = i == 0
		} else {
			run.joins[len(run.joins)-1] = true
		}
		prefixError := run.lengthErrors[len(run.lengthErrors)-1]
		for j := 1; j < len(curve.points); j++ {
			run.lengthErrors = append(run.lengthErrors, strokeCurveUp(prefixError+curve.lengthErrors[j]))
		}
		run.directions[len(run.directions)-1].outgoing = curve.startTangent
		run.points = append(run.points, curve.points[1:]...)
		run.joins = append(run.joins, make([]bool, len(curve.points)-1)...)
		run.directions = append(run.directions, make([]strokePathDirection, len(curve.points)-1)...)
		run.directions[len(run.directions)-1].incoming = curve.endTangent
		run.end = i == count-1
		current = segment.Point
	}
	if len(run.points) != 0 {
		runs = append(runs, run)
	}
	for i := range runs {
		if err := strokePathMeasure(&runs[i]); err != nil {
			return nil, err
		}
	}
	return runs, nil
}

// strokePathPieces 按连续段独立重启虚线相位，并区分真实端点与内部断口的端帽
// 入参: runs 有弧长定位的描边连续段, closed 原始子路径是否闭合, path 原始描边样式, dashed 是否需要虚线切分, angle 切线角预算, tolerance 弧长定位预算, maxPieces 非负片段数量上限, work 剩余虚线定位工作量
// 返回: []strokePathPiece 描边片段, error 虚线或资源限制错误
func strokePathPieces(runs []strokePathRun, closed bool, path *Path, dashed bool, angle, tolerance float64, maxPieces int, work *int) ([]strokePathPiece, error) {
	var pieces []strokePathPiece
	firstRunEnd := 0
	remaining := maxPieces
	for i, run := range runs {
		length := run.distance[len(run.distance)-1]
		spans := []strokeDashSpan{{0, length}}
		if dashed {
			var err error
			spans, err = strokePathDashSpans(run, path, angle, tolerance, maxPieces-len(pieces), work)
			if err != nil {
				return nil, err
			}
		}
		if len(spans) > maxPieces-len(pieces) {
			return nil, fmt.Errorf("%w: stroke piece budget", ErrLimit)
		}
		for _, span := range spans {
			piece, err := strokePathSlice(run, span, remaining)
			if err != nil {
				return nil, err
			}
			remaining -= len(piece.points)
			piece.figureStart = span.start == 0 && run.start
			piece.figureEnd = span.end == length && run.end
			piece.positive = span.end > span.start
			piece.startCap, piece.endCap = LineCapFlat, LineCapFlat
			if dashed {
				piece.startCap, piece.endCap = path.StrokeDashCap, path.StrokeDashCap
			}
			if !closed && span.start == 0 && run.start {
				piece.startCap = path.StrokeStartLineCap
			}
			if !closed && span.end == length && run.end {
				piece.endCap = path.StrokeEndLineCap
			}
			pieces = append(pieces, piece)
		}
		if i == 0 {
			firstRunEnd = len(pieces)
		}
	}
	if closed && len(pieces) > 0 && firstRunEnd > 0 && runs[0].start && runs[len(runs)-1].end {
		pieces = strokePathClosePieces(pieces, firstRunEnd)
	}
	return pieces, nil
}

// strokePathClosePieces 按连续描边邻域连接闭合缝，独立零长虚线仍保留端帽
// 入参: pieces 已切分的描边片段, firstRunEnd 首个连续段的片段结束索引
// 返回: []strokePathPiece 完成闭合连接后的片段
func strokePathClosePieces(pieces []strokePathPiece, firstRunEnd int) []strokePathPiece {
	if len(pieces) == 1 && pieces[0].figureStart && pieces[0].figureEnd {
		pieces[0].closed = true
		pieces[0].startCap, pieces[0].endCap = LineCapFlat, LineCapFlat
		return pieces
	}
	firstIndex, lastIndex := -1, -1
	for i := 0; i < firstRunEnd; i++ {
		if pieces[i].figureStart && pieces[i].positive {
			firstIndex = i
			break
		}
	}
	for i := len(pieces) - 1; i >= 0; i-- {
		if pieces[i].figureEnd && pieces[i].positive {
			lastIndex = i
			break
		}
	}
	if firstIndex < 0 || lastIndex < 0 {
		return pieces
	}
	first, last := &pieces[firstIndex], &pieces[lastIndex]
	if firstIndex == lastIndex {
		first.closed = true
		first.startCap, first.endCap = LineCapFlat, LineCapFlat
		return pieces
	}
	last.joins[len(last.joins)-1] = true
	last.directions[len(last.directions)-1].outgoing = first.directions[0].outgoing
	last.points = append(last.points, first.points[1:]...)
	last.joins = append(last.joins, first.joins[1:]...)
	last.directions = append(last.directions, first.directions[1:]...)
	last.endDir, last.endCap = first.endDir, first.endCap
	last.figureStart, last.figureEnd = false, false
	copy(pieces[firstIndex:], pieces[firstIndex+1:])
	pieces[len(pieces)-1] = strokePathPiece{}
	return pieces[:len(pieces)-1]
}

// strokePathSlice 用累计距离截取折线，原始连接点及零长度段保留在片段内
// 入参: run 描边连续段, span 已限制到连续段距离范围的闭区间, maxPoints 片段点数上限
// 返回: strokePathPiece 独立的中心线片段, error 点数超出预算错误
func strokePathSlice(run strokePathRun, span strokeDashSpan, maxPoints int) (strokePathPiece, error) {
	n := len(run.points)
	begin := sort.Search(n, func(i int) bool { return run.distance[i] > span.start })
	finish := sort.Search(n, func(i int) bool { return run.distance[i] >= span.end })
	if span.start == 0 {
		begin = 1
	}
	if span.end == run.distance[n-1] {
		finish = n - 1
	}
	begin, finish = max(1, begin), min(n-1, finish)
	count := max(0, finish-begin) + 2
	if count > maxPoints {
		return strokePathPiece{}, fmt.Errorf("%w: stroke piece point budget", ErrLimit)
	}
	start, startDir := strokePathPosition(run, span.start, true)
	end, endDir := strokePathPosition(run, span.end, false)
	piece := strokePathPiece{points: make([]Point, 1, count), joins: make([]bool, 1, count), directions: make([]strokePathDirection, 1, count), startDir: startDir, endDir: endDir}
	piece.points[0] = start
	piece.directions[0].outgoing = startDir
	for i := begin; i < finish; i++ {
		piece.points = append(piece.points, run.points[i])
		piece.joins = append(piece.joins, run.joins[i])
		direction := strokePathDirection{}
		if len(run.directions) != 0 {
			direction = run.directions[i]
		}
		piece.directions = append(piece.directions, direction)
	}
	piece.points = append(piece.points, end)
	piece.joins = append(piece.joins, false)
	piece.directions = append(piece.directions, strokePathDirection{incoming: endDir})
	return piece, nil
}

// strokePathPosition 在累计距离中定位坐标和单侧方向，完全退化时采用正横轴
// 入参: run 描边连续段, distance 距离坐标, outgoing 是否选择出射侧
// 返回: Point 中心线坐标, Point 正向单位方向
func strokePathPosition(run strokePathRun, distance float64, outgoing bool) (Point, Point) {
	i := strokePathPositionIndex(run, distance, outgoing)
	a, b := run.points[i-1], run.points[i]
	if a == b {
		return a, Point{1, 0}
	}
	fraction := (distance - run.distance[i-1]) / (run.distance[i] - run.distance[i-1])
	point := Point{geometryLinearCombination(0, a.X, 1-fraction, b.X, fraction), geometryLinearCombination(0, a.Y, 1-fraction, b.Y, fraction)}
	if distance == run.distance[i-1] {
		point = a
	} else if distance == run.distance[i] {
		point = b
	}
	direction := strokeOutlineDirection(a, b)
	if len(run.directions) != 0 {
		if distance == run.distance[i-1] && run.directions[i-1].outgoing != (Point{}) {
			direction = run.directions[i-1].outgoing
		} else if distance == run.distance[i] && run.directions[i].incoming != (Point{}) {
			direction = run.directions[i].incoming
		}
	}
	return point, direction
}

// strokePathPositionIndex 通过累计距离二分定位单侧弦，跳过任意数量的连续零长段
// 入参: run 至少含两个顶点的连续段, distance 段内距离, outgoing 是否采用出射侧
// 返回: int 弦终点索引，完全退化时为1
func strokePathPositionIndex(run strokePathRun, distance float64, outgoing bool) int {
	n := len(run.distance)
	i := sort.Search(n, func(i int) bool {
		if outgoing {
			return run.distance[i] > distance
		}
		return run.distance[i] >= distance
	})
	if i == 0 {
		i = sort.Search(n, func(i int) bool { return run.distance[i] > run.distance[0] })
	}
	if i == n {
		i = sort.Search(n, func(i int) bool { return run.distance[i] >= run.distance[n-1] })
	}
	return max(1, i)
}

// pathPiece 扩展描边片段，原始连接使用指定样式，平滑细分点使用圆连接，内部回折不加连接
// 入参: piece 中心线片段及端帽, style 原始描边参数
// 返回: error 数值或资源限制错误
func (b *strokeOutlineBuilder) pathPiece(piece strokePathPiece, style strokeOutlineStyle) error {
	first, previous := -1, -1
	var firstDirection, previousDirection Point
	for i := 1; i < len(piece.points); i++ {
		p, q := piece.points[i-1], piece.points[i]
		if p == q {
			continue
		}
		direction := strokeOutlineDirection(p, q)
		startDirection, endDirection := direction, direction
		if len(piece.directions) != 0 {
			if piece.directions[i-1].outgoing != (Point{}) {
				startDirection = piece.directions[i-1].outgoing
			}
			if piece.directions[i].incoming != (Point{}) {
				endDirection = piece.directions[i].incoming
			}
		}
		if previous >= 0 {
			join, limit := LineJoinRound, style.miter
			if piece.joins[i-1] {
				join = style.join
			}
			if i-previous > 1 {
				join, limit = style.join, 1
			}
			reversal := false
			if !piece.joins[i-1] && i-previous == 1 {
				dot := previousDirection.X*startDirection.X + previousDirection.Y*startDirection.Y
				if math.Abs(dot) < 0.5 {
					return fmt.Errorf("%w: stroke subdivision direction continuity", ErrLimit)
				}
				reversal = dot < 0
			}
			if !reversal {
				if err := b.join(p, previousDirection, startDirection, join, limit); err != nil {
					return err
				}
			}
		} else {
			first, firstDirection = i, startDirection
		}
		if err := b.segmentDirections(p, q, startDirection, endDirection); err != nil {
			return err
		}
		previous, previousDirection = i, endDirection
	}
	if piece.closed {
		if first == -1 {
			if err := b.round(piece.points[0], Point{1, 0}, Point{-1, 0}); err != nil {
				return err
			}
			return b.round(piece.points[0], Point{-1, 0}, Point{1, 0})
		}
		limit := style.miter
		if first > 1 || previous < len(piece.points)-1 {
			limit = 1
		}
		return b.join(piece.points[0], previousDirection, firstDirection, style.join, limit)
	}
	if err := b.cap(piece.points[0], Point{-piece.startDir.X, -piece.startDir.Y}, piece.startCap); err != nil {
		return err
	}
	return b.cap(piece.points[len(piece.points)-1], piece.endDir, piece.endCap)
}
