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
	"cmp"
	"fmt"
	"image"
	"math"
	"math/big"
	"math/bits"
	"slices"
)

// rasterMaxDimension 等常量定义光栅化默认资源上限与几何容差
const (
	rasterMaxDimension = 1 << 20
	rasterMaxPixels    = 1 << 24
	rasterMaxEdges     = 1 << 20
	rasterMaxWork      = 1 << 27
	rasterMaxExact     = 1 << 16
	rasterMaxRegions   = 1 << 10
	rasterAtOrRightEps = 0x1p-49
)

// rasterFullMaskRow 保存用于快速填充的满覆盖率掩模行模板
var rasterFullMaskRow = makeRasterFullMaskRow()

// rasterRegion 保存设备空间闭合边集及其独立填充规则
type rasterRegion struct {
	edges []geometryEdge
	rule  GeometryFillRule
}

// rasterEdge 保存按纵坐标递增排列的端点、有效扫描范围及原始方向
type rasterEdge struct {
	start, end  Point
	first, last int
	direction   int
	region      int
}

// rasterAliasedCrossing 保存像素中心扫描线的整数列交点及方向
type rasterAliasedCrossing struct {
	col       int
	direction int
	region    int
}

// rasterScratch 保存单工作Goroutine独占的可复用扫描线缓冲，减少重复堆分配
type rasterScratch struct {
	prepared   []rasterEdge
	active     []rasterEdge
	aliased    []rasterAliasedCrossing
	band       []rasterBandEdge
	divisions  []float64
	difference []float64
	winding    []int
}

// rasterAreaBoundary 保存横向线性边界的精确积分参数，端点按横坐标排序
type rasterAreaBoundary struct {
	low   big.Rat
	high  big.Rat
	width big.Rat
}

// rasterAreaInterval 保存包含精确结果的向外舍入区间，不用于修改几何拓扑
type rasterAreaInterval struct {
	low  float64
	high float64
}

// rasterBandEdge 保存扫描带两端的交点及原始有向边
type rasterBandEdge struct {
	edge rasterEdge
	lo   float64
	hi   float64
}

// rasterBandPosition 保留交叉事件的精确纵坐标，普通顶点直接使用原始浮点值
type rasterBandPosition struct {
	value float64
	exact *big.Rat
}

// makeRasterFullMaskRow 预构建全满覆盖字节块，用于快速填充整段二值掩模
// 返回: [256]byte 全为255的常量填充块
func makeRasterFullMaskRow() [256]byte {
	var row [256]byte
	for i := range row {
		row[i] = 255
	}
	return row
}

// rasterFillOnes 将目标掩模切片全部置为满覆盖255
// 入参: dst 待填充的连续字节区间
func rasterFillOnes(dst []byte) {
	if len(dst) <= 16 {
		for i := range dst {
			dst[i] = 255
		}
		return
	}
	for offset := 0; offset < len(dst); offset += len(rasterFullMaskRow) {
		copy(dst[offset:], rasterFullMaskRow[:])
	}
}

// rasterRegionsCoverageBudget 按调用方预算与整数溢出防线执行区域扫描，允许显式提高像素和边数上限
// 入参: regions 非空独立区域列表, bounds 输出像素范围, aliased 是否禁用抗锯齿, required 所需命中区域数, maxPixels 最大像素预算, maxEdges 最大边数预算, maxWork 最大扫描工作量, dst 可选复用输出掩模, scratch 可选复用工作区
// 返回: *image.Alpha 覆盖率图像, error 参数、闭合性或资源限制错误，失败时不返回部分图像
func rasterRegionsCoverageBudget(regions []rasterRegion, bounds image.Rectangle, aliased bool, required int, maxPixels uint64, maxEdges int, maxWork uint64, dst *image.Alpha, scratch *rasterScratch) (*image.Alpha, error) {
	if len(regions) == 0 || bounds.Min.X > bounds.Max.X || bounds.Min.Y > bounds.Max.Y || maxEdges < 0 {
		return nil, fmt.Errorf("%w: raster regions or bounds", ErrInvalid)
	}
	if len(regions) > rasterMaxRegions {
		return nil, fmt.Errorf("%w: raster region count", ErrLimit)
	}
	edgeCount := 0
	for _, region := range regions {
		if region.rule != GeometryEvenOdd && region.rule != GeometryNonZero {
			return nil, fmt.Errorf("%w: raster fill rule", ErrInvalid)
		}
		if len(region.edges) > maxEdges-edgeCount {
			return nil, fmt.Errorf("%w: raster edge count", ErrLimit)
		}
		edgeCount += len(region.edges)
	}
	if bounds.Min.X < -(1<<30) || bounds.Min.Y < -(1<<30) || bounds.Max.X > 1<<30 || bounds.Max.Y > 1<<30 {
		return nil, fmt.Errorf("%w: raster coordinate range", ErrLimit)
	}
	width64, height64 := int64(bounds.Max.X)-int64(bounds.Min.X), int64(bounds.Max.Y)-int64(bounds.Min.Y)
	if width64 > rasterMaxDimension || height64 > rasterMaxDimension || width64 > 0 && (uint64(height64) > maxPixels/uint64(width64) || uint64(height64) > uint64(^uint(0)>>1)/uint64(width64)) {
		return nil, fmt.Errorf("%w: raster dimensions", ErrLimit)
	}
	width, height := int(width64), int(height64)
	rows := height
	var prepared []rasterEdge
	if scratch != nil && cap(scratch.prepared) >= edgeCount {
		prepared = scratch.prepared[:0]
	} else {
		prepared = make([]rasterEdge, 0, edgeCount)
	}
	empty := false
	minYFloat, maxYFloat := float64(bounds.Min.Y), float64(bounds.Max.Y)
	for index, region := range regions {
		before := len(prepared)
		for _, edge := range region.edges {
			a, b, direction := edge.start, edge.end, 1
			if !geometryFinite(a.X, a.Y, b.X, b.Y) {
				return nil, fmt.Errorf("%w: non-finite raster edge", ErrInvalid)
			}
			if a.Y == b.Y {
				continue
			}
			if a.Y > b.Y {
				a, b, direction = b, a, -1
			}
			lo := max(a.Y, minYFloat)
			hi := min(b.Y, maxYFloat)
			if lo >= hi {
				continue
			}
			first, last := 0, 0
			if aliased {
				first = rasterFirstSample(lo, bounds.Min.Y, rows)
				last = rasterFirstSample(hi, bounds.Min.Y, rows)
			} else {
				lower := math.Nextafter(lo-minYFloat, math.Inf(-1))
				upper := math.Nextafter(hi-minYFloat, math.Inf(1))
				first = max(0, int(math.Floor(lower)))
				last = min(rows, int(math.Ceil(upper)))
			}
			if first < last {
				prepared = append(prepared, rasterEdge{a, b, first, last, direction, index})
			}
		}
		empty = empty || len(prepared) == before
	}
	if scratch != nil {
		scratch.prepared = prepared[:0]
	}
	pixelCount := width * height
	var mask *image.Alpha
	if dst != nil {
		if cap(dst.Pix) < pixelCount {
			dst.Pix = make([]byte, pixelCount)
		} else {
			dst.Pix = dst.Pix[:pixelCount]
			clear(dst.Pix)
		}
		dst.Stride = width
		dst.Rect = bounds
		mask = dst
	} else {
		mask = image.NewAlpha(bounds)
	}
	if width == 0 || height == 0 || len(prepared) == 0 || empty && required == len(regions) {
		return mask, nil
	}
	if len(prepared) <= 16 {
		for i := 1; i < len(prepared); i++ {
			item := prepared[i]
			j := i - 1
			for j >= 0 && prepared[j].first > item.first {
				prepared[j+1] = prepared[j]
				j--
			}
			prepared[j+1] = item
		}
	} else {
		slices.SortFunc(prepared, func(a, b rasterEdge) int { return cmp.Compare(a.first, b.first) })
	}
	var active []rasterEdge
	if scratch != nil && cap(scratch.active) >= len(prepared) {
		active = scratch.active[:0]
	} else {
		active = make([]rasterEdge, 0, len(prepared))
	}
	var winding []int
	if scratch != nil && cap(scratch.winding) >= len(regions) {
		winding = scratch.winding[:len(regions)]
	} else {
		winding = make([]int, len(regions))
	}
	work, next, exact := uint64(width)*uint64(height), 0, rasterMaxExact
	if aliased {
		var aliasedCrossings []rasterAliasedCrossing
		if scratch != nil && cap(scratch.aliased) >= len(prepared) {
			aliasedCrossings = scratch.aliased[:0]
		} else {
			aliasedCrossings = make([]rasterAliasedCrossing, 0, len(prepared))
		}
		work += uint64(edgeCount) * uint64(2+2*bits.Len(uint(rows)))
		widthBits := bits.Len(uint(width))
		for row := 0; row < rows; row++ {
			retained := active[:0]
			for _, edge := range active {
				if edge.last > row {
					retained = append(retained, edge)
				}
			}
			active = retained
			for next < len(prepared) && prepared[next].first <= row {
				active = append(active, prepared[next])
				next++
			}
			if len(active) == 0 {
				jump := rows
				if next < len(prepared) {
					jump = min(rows, prepared[next].first)
				}
				skip := uint64(jump - row)
				work += skip * uint64(len(regions)) * 2
				if work > maxWork {
					return nil, fmt.Errorf("%w: raster scan work", ErrLimit)
				}
				row = jump - 1
				continue
			}
			cost := 3 + bits.Len(uint(len(active))) + widthBits
			work += (uint64(len(active))*uint64(cost) + uint64(len(regions))) * 2
			if work > maxWork {
				return nil, fmt.Errorf("%w: raster scan work", ErrLimit)
			}
			y := float64(bounds.Min.Y+row) + 0.5
			offset := row * mask.Stride
			if err := rasterAliasedRow(active, aliasedCrossings[:0], mask.Pix[offset:offset+width], bounds.Min.X, width, y, regions, required, winding, &exact); err != nil {
				return nil, err
			}
		}
		if scratch != nil {
			scratch.active = active[:0]
			scratch.aliased = aliasedCrossings[:0]
			scratch.winding = winding
		}
		return mask, nil
	}
	var band []rasterBandEdge
	if scratch != nil && cap(scratch.band) >= len(prepared) {
		band = scratch.band[:0]
	} else {
		band = make([]rasterBandEdge, 0, len(prepared))
	}
	var divisions []float64
	if scratch != nil && cap(scratch.divisions) >= 2*len(prepared)+2 {
		divisions = scratch.divisions[:0]
	} else {
		divisions = make([]float64, 0, 2*len(prepared)+2)
	}
	var difference []float64
	if scratch != nil && cap(scratch.difference) >= width+1 {
		difference = scratch.difference[:width+1]
		clear(difference)
	} else {
		difference = make([]float64, width+1)
	}
	work += uint64(edgeCount) * 3
	for row := 0; row < rows; row++ {
		retained := active[:0]
		for _, edge := range active {
			if edge.last > row {
				retained = append(retained, edge)
			}
		}
		active = retained
		for next < len(prepared) && prepared[next].first <= row {
			active = append(active, prepared[next])
			next++
		}
		if len(active) == 0 {
			jump := rows
			if next < len(prepared) {
				jump = min(rows, prepared[next].first)
			}
			skip := uint64(jump - row)
			work += skip * uint64(len(regions)) * 2
			if work > maxWork {
				return nil, fmt.Errorf("%w: raster scan work", ErrLimit)
			}
			row = jump - 1
			continue
		}
		lo := float64(bounds.Min.Y + row)
		hi := float64(bounds.Min.Y + row + 1)
		divisions = append(divisions[:0], lo, hi)
		for _, edge := range active {
			if edge.start.Y > lo && edge.start.Y < hi {
				divisions = append(divisions, edge.start.Y)
			}
			if edge.end.Y > lo && edge.end.Y < hi {
				divisions = append(divisions, edge.end.Y)
			}
		}
		if len(divisions) > 2 {
			slices.Sort(divisions)
			divisions = slices.Compact(divisions)
		}
		cost := 3 + bits.Len(uint(len(active)))
		work += (uint64(len(active))*uint64(cost) + uint64(len(regions))) * uint64(len(divisions))
		if work > maxWork {
			return nil, fmt.Errorf("%w: raster scan work", ErrLimit)
		}
		for i := 1; i < len(divisions); i++ {
			if err := rasterBandSpans(active, band, divisions[i-1], divisions[i], regions, required, winding, &work, maxWork, &exact, func(lower, upper rasterBandPosition, left, right rasterBandEdge) error {
				return rasterAreaSpan(difference, bounds.Min.X, left.lo, left.hi, right.lo, right.hi, upper.distance(lower), &work, maxWork)
			}); err != nil {
				return nil, err
			}
		}
		coverage := 0.0
		rowPix := mask.Pix[row*mask.Stride : row*mask.Stride+width]
		for x := range width {
			coverage += difference[x]
			rowPix[x] = uint8(math.Floor(min(1, max(0, coverage))*255 + 0.5))
		}
		clear(difference)
	}
	if scratch != nil {
		scratch.active = active[:0]
		scratch.band = band[:0]
		scratch.divisions = divisions[:0]
		scratch.difference = difference
		scratch.winding = winding
	}
	return mask, nil
}

// rasterFirstSample 在设备空间查找不小于端点的首个像素中心，避免相对原点换算丢失半像素边界
// 入参: y 端点纵坐标, origin 输出起始行, rows 输出行数
// 返回: int 首个符合条件的行下标，没有时为rows
func rasterFirstSample(y float64, origin, rows int) int {
	if rows <= 0 || float64(origin)+0.5 >= y {
		return 0
	}
	if float64(origin+rows-1)+0.5 < y {
		return rows
	}
	idx := int(math.Ceil(y - 0.5 - float64(origin)))
	idx = max(0, min(rows, idx))
	for idx > 0 && float64(origin+idx-1)+0.5 >= y {
		idx--
	}
	for idx < rows && float64(origin+idx)+0.5 < y {
		idx++
	}
	return idx
}

// rasterAliasedEdgeCol 求单条非水平边在扫描行上首个满足像素中心归属右侧的列下标，结果与二分搜索等价
// 入参: edge 纵向递增边, origin 行起点横坐标, width 行宽, y 扫描纵坐标, exact 剩余精确计算次数
// 返回: int 列下标[0, width], error 精确计算预算不足错误
func rasterAliasedEdgeCol(edge rasterEdge, origin, width int, y float64, exact *int) (int, error) {
	if edge.start.X == edge.end.X {
		return rasterFirstSample(edge.start.X, origin, width), nil
	}
	if width <= 0 {
		return 0, nil
	}
	firstCenter := float64(origin) + 0.5
	if firstCenter >= max(edge.start.X, edge.end.X) {
		return 0, nil
	}
	lastCenter := float64(origin+width-1) + 0.5
	if lastCenter < min(edge.start.X, edge.end.X) {
		return width, nil
	}
	dx, dy := edge.end.X-edge.start.X, edge.end.Y-edge.start.Y
	lo, hi := 0, width
	if dy > 0 && geometryFinite(dx, dy) {
		xEst := edge.start.X + (y-edge.start.Y)*(dx/dy)
		if geometryFinite(xEst) {
			cand := int(math.Ceil(xEst - 0.5 - float64(origin)))
			if cand >= 0 && cand <= width {
				atCand := true
				if cand < width {
					var err error
					atCand, err = rasterAtOrRight(edge.start, edge.end, Point{float64(origin+cand) + 0.5, y}, exact)
					if err != nil {
						return 0, err
					}
				}
				if atCand {
					if cand == 0 {
						return 0, nil
					}
					prev, err := rasterAtOrRight(edge.start, edge.end, Point{float64(origin+cand-1) + 0.5, y}, exact)
					if err != nil {
						return 0, err
					}
					if !prev {
						return cand, nil
					}
					hi = cand - 1
				} else {
					if cand+1 == width {
						return width, nil
					}
					next, err := rasterAtOrRight(edge.start, edge.end, Point{float64(origin+cand+1) + 0.5, y}, exact)
					if err != nil {
						return 0, err
					}
					if next {
						return cand + 1, nil
					}
					lo = cand + 2
				}
			}
		}
	}
	for lo < hi {
		mid := lo + (hi-lo)/2
		right, err := rasterAtOrRight(edge.start, edge.end, Point{float64(origin+mid) + 0.5, y}, exact)
		if err != nil {
			return 0, err
		}
		if right {
			hi = mid
		} else {
			lo = mid + 1
		}
	}
	return lo, nil
}

// rasterAliasedRow 按像素中心归属直接填充二值覆盖行，避免经由差分数组与浮点量化往返
// 入参: active 当前扫描行候选边, crossings 可复用整数交点缓冲, rowPix 目标行字节切片, origin 行起点横坐标, width 行宽, y 扫描纵坐标, regions 独立区域, required 所需命中区域数, winding 区域绕数缓冲, exact 剩余精确计算次数
// 返回: error 资源上限或边集不闭合错误
func rasterAliasedRow(active []rasterEdge, crossings []rasterAliasedCrossing, rowPix []byte, origin, width int, y float64, regions []rasterRegion, required int, winding []int, exact *int) error {
	for _, edge := range active {
		if y < edge.start.Y || y >= edge.end.Y {
			continue
		}
		col, err := rasterAliasedEdgeCol(edge, origin, width, y, exact)
		if err != nil {
			return err
		}
		crossings = append(crossings, rasterAliasedCrossing{col, edge.direction, edge.region})
	}
	n := len(crossings)
	if n == 0 {
		return nil
	}
	if n == 2 {
		if crossings[0].col > crossings[1].col {
			crossings[0], crossings[1] = crossings[1], crossings[0]
		}
	} else if n <= 16 {
		for i := 1; i < n; i++ {
			item := crossings[i]
			j := i - 1
			for j >= 0 && crossings[j].col > item.col {
				crossings[j+1] = crossings[j]
				j--
			}
			crossings[j+1] = item
		}
	} else {
		slices.SortFunc(crossings, func(a, b rasterAliasedCrossing) int { return cmp.Compare(a.col, b.col) })
	}
	if len(regions) == 1 {
		evenOdd := regions[0].rule == GeometryEvenOdd
		w, previous := 0, 0
		for i := 0; i < n; {
			col := crossings[i].col
			if w != 0 && previous < col {
				rasterFillOnes(rowPix[previous:col])
			}
			for i < n && crossings[i].col == col {
				if evenOdd {
					w ^= 1
				} else {
					w += crossings[i].direction
				}
				i++
			}
			previous = col
		}
		if w != 0 {
			return fmt.Errorf("%w: raster edges are not closed", ErrInvalid)
		}
		return nil
	}
	clear(winding)
	covered, previous := 0, 0
	for i := 0; i < n; {
		col := crossings[i].col
		if covered >= required && previous < col {
			rasterFillOnes(rowPix[previous:col])
		}
		for i < n && crossings[i].col == col {
			crossing := crossings[i]
			before := winding[crossing.region] != 0
			if regions[crossing.region].rule == GeometryEvenOdd {
				winding[crossing.region] ^= 1
			} else {
				winding[crossing.region] += crossing.direction
			}
			after := winding[crossing.region] != 0
			if before != after {
				if after {
					covered++
				} else {
					covered--
				}
			}
			i++
		}
		previous = col
	}
	if covered != 0 {
		return fmt.Errorf("%w: raster edges are not closed", ErrInvalid)
	}
	return nil
}

// rasterIntersection 以向外舍入区间求扫描交点横坐标，区间过宽时回退精确有理数
// 入参: a 下纵坐标端点, b 上纵坐标端点, y 位于半开纵区间的扫描位置, exact 剩余精确计算次数
// 返回: float64 交点横坐标, error 精确计算预算不足错误
func rasterIntersection(a, b Point, y float64, exact *int) (float64, error) {
	if a.X == b.X || y == a.Y {
		return a.X, nil
	}
	negative, positive := math.Inf(-1), math.Inf(1)
	n, d, dx := y-a.Y, b.Y-a.Y, b.X-a.X
	dlo, dhi := math.Nextafter(d, negative), math.Nextafter(d, positive)
	if geometryFinite(n, d, dx, dlo, dhi) && dlo > 0 {
		tlo := max(0, math.Nextafter(max(0, math.Nextafter(n, negative))/dhi, negative))
		thi := min(1, math.Nextafter(math.Nextafter(n, positive)/dlo, positive))
		dxlo, dxhi := math.Nextafter(dx, negative), math.Nextafter(dx, positive)
		p0, p1, p2, p3 := tlo*dxlo, tlo*dxhi, thi*dxlo, thi*dxhi
		lo := math.Nextafter(a.X+math.Nextafter(min(p0, p1, p2, p3), negative), negative)
		hi := math.Nextafter(a.X+math.Nextafter(max(p0, p1, p2, p3), positive), positive)
		spacing := max(math.Abs(math.Nextafter(lo, positive)-lo), math.Abs(math.Nextafter(hi, positive)-hi))
		if geometryFinite(lo, hi, spacing) && hi-lo <= max(1e-9, 16*spacing) {
			return lo + (hi-lo)/2, nil
		}
	}
	x, err := rasterExactIntersection(a, b, y, exact)
	if err != nil {
		return 0, err
	}
	result, _ := x.Float64()
	return result, nil
}

// rasterExactIntersection 以精确有理数计算非水平边在给定纵坐标处的横坐标
// 入参: a 下纵坐标端点, b 上纵坐标端点, y 位于闭区间的纵坐标, exact 剩余精确计算次数
// 返回: *big.Rat 精确交点横坐标, error 精确计算预算不足错误
func rasterExactIntersection(a, b Point, y float64, exact *int) (*big.Rat, error) {
	if err := rasterExactCharge(exact); err != nil {
		return nil, err
	}
	return rasterRationalIntersection(a, b, new(big.Rat).SetFloat64(y)), nil
}

// rasterRationalIntersection 在调用方已计入预算后计算精确纵坐标处的直线交点
// 入参: a 下纵坐标端点, b 上纵坐标端点, y 精确纵坐标
// 返回: *big.Rat 精确交点横坐标
func rasterRationalIntersection(a, b Point, y *big.Rat) *big.Rat {
	ax, ay := new(big.Rat).SetFloat64(a.X), new(big.Rat).SetFloat64(a.Y)
	x := new(big.Rat).Sub(new(big.Rat).SetFloat64(b.X), ax)
	x.Mul(x, new(big.Rat).Sub(y, ay))
	x.Quo(x, new(big.Rat).Sub(new(big.Rat).SetFloat64(b.Y), ay))
	x.Add(x, ax)
	return x
}

// rasterAtOrRight 判断像素中心是否位于纵向递增边的右侧或边上，近共线及溢出时使用精确有理数
// 入参: a 下纵坐标端点, b 上纵坐标端点, p 待测像素中心, exact 剩余精确计算次数
// 返回: bool 是否位于边上或右侧, error 精确计算预算不足错误
func rasterAtOrRight(a, b, p Point, exact *int) (bool, error) {
	if p.X >= max(a.X, b.X) {
		return true, nil
	}
	if p.X < min(a.X, b.X) {
		return false, nil
	}
	left, right := (b.X-a.X)*(p.Y-a.Y), (p.X-a.X)*(b.Y-a.Y)
	errorBound := (math.Abs(left)+math.Abs(right))*rasterAtOrRightEps + 16*math.SmallestNonzeroFloat64
	difference := left - right
	if geometryFinite(left, right, errorBound, difference) && math.Abs(difference) > errorBound {
		return difference < 0, nil
	}
	if err := rasterExactCharge(exact); err != nil {
		return false, err
	}
	ax, ay := new(big.Rat).SetFloat64(a.X), new(big.Rat).SetFloat64(a.Y)
	bx, by := new(big.Rat).SetFloat64(b.X), new(big.Rat).SetFloat64(b.Y)
	px, py := new(big.Rat).SetFloat64(p.X), new(big.Rat).SetFloat64(p.Y)
	l := new(big.Rat).Mul(new(big.Rat).Sub(bx, ax), new(big.Rat).Sub(py, ay))
	r := new(big.Rat).Mul(new(big.Rat).Sub(px, ax), new(big.Rat).Sub(by, ay))
	return l.Cmp(r) <= 0, nil
}

// rasterExactCharge 在分配高精度数值前扣减共享预算
// 入参: remaining 剩余精确计算次数
// 返回: error 预算耗尽错误
func rasterExactCharge(remaining *int) error {
	if *remaining <= 0 {
		return fmt.Errorf("%w: raster exact arithmetic work", ErrLimit)
	}
	*remaining--
	return nil
}

// rasterAreaSpan 在指定扫描工作上限内将非交叉梯形与单位像素的精确相交面积累加到差分行
// 入参: difference 带末尾哨兵的差分行, origin 行起点, left0 上端左边界, left1 下端左边界, right0 上端右边界, right1 下端右边界, height 正且不超过1的扫描带高度, work 累计工作量, maxWork 扫描工作预算上限
// 返回: error 参数、数值表示或工作预算错误
func rasterAreaSpan(difference []float64, origin int, left0, left1, right0, right1, height float64, work *uint64, maxWork uint64) error {
	if work == nil {
		return fmt.Errorf("%w: nil raster area work counter", ErrInvalid)
	}
	if err := rasterSweepCharge(work, 16, maxWork); err != nil {
		return err
	}
	if len(difference) == 0 || !geometryFinite(left0, left1, right0, right1, height) || height <= 0 || height > 1 || left0 > right0 || left1 > right1 {
		return fmt.Errorf("%w: raster area span parameters", ErrInvalid)
	}
	width := len(difference) - 1
	if width > rasterMaxDimension || origin < -(1<<30) || origin > 1<<30 || int64(origin)+int64(width) > 1<<30 {
		return fmt.Errorf("%w: raster area row range", ErrLimit)
	}
	if width == 0 || left0 == right0 && left1 == right1 {
		return nil
	}
	low, high := float64(origin), float64(origin+width)
	leftMin, leftMax := min(left0, left1), max(left0, left1)
	rightMin, rightMax := min(right0, right1), max(right0, right1)
	if leftMin >= high || rightMax <= low {
		return nil
	}
	leftStart := int(math.Floor(max(low, min(high, leftMin))) - low)
	leftEnd := int(math.Ceil(max(low, min(high, leftMax))) - low)
	rightStart := int(math.Floor(max(low, min(high, rightMin))) - low)
	rightEnd := int(math.Ceil(max(low, min(high, rightMax))) - low)
	if leftEnd < rightStart {
		if err := rasterSweepCharge(work, 2, maxWork); err != nil {
			return err
		}
		if err := rasterAreaAdd(difference, leftEnd, rightStart, height); err != nil {
			return err
		}
	}
	if rightStart <= leftEnd {
		leftEnd, rightStart = max(leftEnd, rightEnd), rightEnd
	}
	var left, right rasterAreaBoundary
	var bandHeight, a, l, r big.Rat
	ready := false
	intervals := [2][2]int{{leftStart, leftEnd}, {rightStart, rightEnd}}
	for _, interval := range intervals {
		for i := interval[0]; i < interval[1]; i++ {
			if err := rasterSweepCharge(work, 8, maxWork); err != nil {
				return err
			}
			x := float64(origin + i)
			area := 0.0
			if rasterAreaLinear(leftMin, leftMax, x) && rasterAreaLinear(rightMin, rightMax, x) {
				w0 := max(x, min(x+1, right0)) - max(x, min(x+1, left0))
				w1 := max(x, min(x+1, right1)) - max(x, min(x+1, left1))
				sum := w0 + w1
				if sum >= 0x1p-500 && height >= 0x1p-500 {
					area = (sum * height) * 0.5
				} else if sum != 0 {
					m, e := math.Frexp(sum)
					h, he := math.Frexp(height)
					area = math.Ldexp(m*h, e+he-1)
				}
			} else {
				if err := rasterSweepCharge(work, 32, maxWork); err != nil {
					return err
				}
				var accepted bool
				area, accepted = rasterAreaFast(leftMin, leftMax, rightMin, rightMax, x, height)
				if accepted {
					if err := rasterAreaAdd(difference, i, i+1, area); err != nil {
						return err
					}
					continue
				}
				if err := rasterSweepCharge(work, 128, maxWork); err != nil {
					return err
				}
				if !ready {
					if err := rasterSweepCharge(work, 32, maxWork); err != nil {
						return err
					}
					left.init(leftMin, leftMax)
					right.init(rightMin, rightMax)
					bandHeight.SetFloat64(height)
					ready = true
				}
				left.integral(&l, int64(origin+i))
				right.integral(&r, int64(origin+i))
				a.Sub(&r, &l)
				a.Mul(&a, &bandHeight)
				area, _ = a.Float64()
			}
			if !geometryFinite(area) || area < 0 || area > height {
				return fmt.Errorf("%w: raster area numerical range", ErrLimit)
			}
			if err := rasterAreaAdd(difference, i, i+1, area); err != nil {
				return err
			}
		}
	}
	return nil
}

// rasterAreaLinear 判断截断到像素范围的边界在整个扫描带内是否为单个线性函数
// 入参: low 横坐标最小值, high 横坐标最大值, x 像素左边界
// 返回: bool 是否无需分段积分
func rasterAreaLinear(low, high, x float64) bool {
	return high <= x || low >= x+1 || low >= x && high <= x+1
}

// rasterAreaFast 在严格正面积且绝对与相对误差均满足容差界时执行浮点解析积分
// 入参: leftMin 左边界最小值, leftMax 左边界最大值, rightMin 右边界最小值, rightMax 右边界最大值, x 像素左边界, height 带高度
// 返回: float64 面积近似值, bool 是否满足误差界
func rasterAreaFast(leftMin, leftMax, rightMin, rightMax, x, height float64) (float64, bool) {
	left := rasterAreaFloatIntegral(leftMin, leftMax, x)
	right := rasterAreaFloatIntegral(rightMin, rightMax, x)
	area := right.sub(left).mul(rasterAreaInterval{height, height})
	if !geometryFinite(area.low, area.high) || area.low <= 0 {
		return 0, false
	}
	area.high = min(area.high, height)
	if area.high < area.low {
		return 0, false
	}
	width := math.Nextafter(area.high-area.low, math.Inf(1))
	relative := math.Nextafter(area.low*0x1p-30, math.Inf(-1))
	if width < 0 || width > 0x1p-46 || width > relative {
		return 0, false
	}
	return area.low + (area.high-area.low)/2, true
}

// rasterAreaFloatIntegral 用向外舍入区间包围截断线性边界的解析积分
// 入参: low 边界最小横坐标, high 边界最大横坐标, x 像素左边界
// 返回: rasterAreaInterval 积分区间，非有限区间由调用者回退精确运算
func rasterAreaFloatIntegral(low, high, x float64) rasterAreaInterval {
	if high <= x {
		return rasterAreaInterval{}
	}
	if low >= x+1 {
		return rasterAreaInterval{1, 1}
	}
	start := rasterAreaInterval{x, x}
	if low == high {
		return (rasterAreaInterval{low, low}).sub(start)
	}
	lo, hi := max(low, x), min(high, x+1)
	a, b := rasterAreaInterval{lo, lo}, rasterAreaInterval{hi, hi}
	numerator := b.sub(a).mul(a.sub(start).add(b.sub(start))).mul(rasterAreaInterval{0.5, 0.5})
	upper, lower := rasterAreaInterval{high, high}, rasterAreaInterval{low, low}
	if high > x+1 {
		numerator = numerator.add(upper.sub(rasterAreaInterval{x + 1, x + 1}))
	}
	return numerator.quo(upper.sub(lower))
}

// add 包围两个区间的和
// 入参: other 加数区间
// 返回: rasterAreaInterval 向外舍入的结果
func (v rasterAreaInterval) add(other rasterAreaInterval) rasterAreaInterval {
	return rasterAreaInterval{math.Nextafter(v.low+other.low, math.Inf(-1)), math.Nextafter(v.high+other.high, math.Inf(1))}
}

// sub 包围两个区间的差
// 入参: other 减数区间
// 返回: rasterAreaInterval 向外舍入的结果
func (v rasterAreaInterval) sub(other rasterAreaInterval) rasterAreaInterval {
	return rasterAreaInterval{math.Nextafter(v.low-other.high, math.Inf(-1)), math.Nextafter(v.high-other.low, math.Inf(1))}
}

// mul 包围已知非负量的乘积，区间与非负域相交不丢失精确结果
// 入参: other 已知非负乘数的区间
// 返回: rasterAreaInterval 向外舍入的结果
func (v rasterAreaInterval) mul(other rasterAreaInterval) rasterAreaInterval {
	return rasterAreaInterval{max(0, math.Nextafter(max(0, v.low)*max(0, other.low), math.Inf(-1))), math.Nextafter(v.high*other.high, math.Inf(1))}
}

// quo 包围已知非负分子的商，无法证明除数严格为正时标记为不可用区间
// 入参: other 正除数的区间
// 返回: rasterAreaInterval 向外舍入的结果，非法除数区间返回非有限值
func (v rasterAreaInterval) quo(other rasterAreaInterval) rasterAreaInterval {
	if other.low <= 0 || !geometryFinite(other.low, other.high) {
		return rasterAreaInterval{math.NaN(), math.NaN()}
	}
	return rasterAreaInterval{max(0, math.Nextafter(max(0, v.low)/other.high, math.Inf(-1))), math.Nextafter(v.high/other.low, math.Inf(1))}
}

// rasterAreaAdd 更新差分区间两端，仅读取待改元素，不扫描整行
// 入参: difference 差分行, start 起始索引, end 结束索引, area 单位像素覆盖面积
// 返回: error 原值非法或累加溢出错误
func rasterAreaAdd(difference []float64, start, end int, area float64) error {
	if area == 0 || start == end {
		return nil
	}
	if !geometryFinite(difference[start], difference[end]) {
		return fmt.Errorf("%w: non-finite raster difference entry", ErrInvalid)
	}
	a, b := difference[start]+area, difference[end]-area
	if !geometryFinite(a, b) {
		return fmt.Errorf("%w: raster difference accumulation overflow", ErrLimit)
	}
	difference[start], difference[end] = a, b
	return nil
}

// init 以浮点输入的精确有理数值初始化边界，允许端点差超过浮点上限
// 入参: low 横坐标最小值, high 横坐标最大值
func (b *rasterAreaBoundary) init(low, high float64) {
	b.low.SetFloat64(low)
	b.high.SetFloat64(high)
	b.width.Sub(&b.high, &b.low)
}

// integral 精确计算整个单位参数带内clamp(edge(t)-x,0,1)的积分
// 入参: result 结果接收值, x 像素左边界
func (b *rasterAreaBoundary) integral(result *big.Rat, x int64) {
	var start, end, low, high, value, term big.Rat
	start.SetInt64(x)
	end.SetInt64(x + 1)
	result.SetInt64(0)
	if b.high.Cmp(&start) <= 0 {
		return
	}
	if b.low.Cmp(&end) >= 0 {
		result.SetInt64(1)
		return
	}
	if b.width.Sign() == 0 {
		result.Sub(&b.low, &start)
		return
	}
	low.Set(&b.low)
	if low.Cmp(&start) < 0 {
		low.Set(&start)
	}
	high.Set(&b.high)
	if high.Cmp(&end) > 0 {
		high.Set(&end)
	}
	if high.Cmp(&low) > 0 {
		value.Sub(&high, &low)
		term.Sub(&low, &start)
		high.Sub(&high, &start)
		term.Add(&term, &high)
		value.Mul(&value, &term)
		term.SetInt64(2)
		result.Quo(&value, &term)
	}
	if b.high.Cmp(&end) > 0 {
		value.Sub(&b.high, &end)
		result.Add(result, &value)
	}
	result.Quo(result, &b.width)
}

// rasterBandSpans 在指定扫描工作上限内按精确交叉事件划分扫描带，输出满足填充规则的非交叉梯形
// 入参: active 候选边, band 可复用缓冲区, lo 起始纵坐标, hi 结束纵坐标, regions 独立区域, required 所需命中区域数, winding 绕数缓冲区, work 累计工作量, maxWork 扫描工作预算上限, exact 精确计算预算, emit 梯形接收函数
// 返回: error 边集、数值、预算或接收函数错误
func rasterBandSpans(active []rasterEdge, band []rasterBandEdge, lo, hi float64, regions []rasterRegion, required int, winding []int, work *uint64, maxWork uint64, exact *int, emit func(rasterBandPosition, rasterBandPosition, rasterBandEdge, rasterBandEdge) error) error {
	lower, upper := rasterBandPosition{value: lo}, rasterBandPosition{value: hi}
	for lower.compare(upper) < 0 {
		cost := uint64(len(active))*uint64(6+bits.Len(uint(len(active)))) + uint64(len(regions))
		if err := rasterSweepCharge(work, cost, maxWork); err != nil {
			return err
		}
		band = band[:0]
		for _, edge := range active {
			if edge.start.Y >= hi || edge.end.Y <= lo {
				continue
			}
			if edge.start.X == edge.end.X {
				band = append(band, rasterBandEdge{edge, edge.start.X, edge.start.X})
				continue
			}
			x0, err := rasterBandIntersection(edge, lower, exact)
			if err != nil {
				return err
			}
			x1, err := rasterBandIntersection(edge, upper, exact)
			if err != nil {
				return err
			}
			band = append(band, rasterBandEdge{edge, x0, x1})
		}
		if len(band) == 2 {
			order, err := rasterBandCompare(band[0], band[1], lower, upper, exact)
			if err != nil {
				return err
			}
			if order > 0 {
				band[0], band[1] = band[1], band[0]
			}
		} else if len(band) > 2 {
			var sortErr error
			slices.SortFunc(band, func(a, b rasterBandEdge) int {
				if sortErr != nil {
					return cmp.Compare(a.lo, b.lo)
				}
				order, err := rasterBandCompare(a, b, lower, upper, exact)
				sortErr = err
				return order
			})
			if sortErr != nil {
				return sortErr
			}
		}
		next := upper
		for i := 1; i < len(band); i++ {
			a, b := band[i-1], band[i]
			order, err := rasterBandCompareAt(a.edge, b.edge, upper, a.hi, b.hi, exact)
			if err != nil {
				return err
			}
			if order <= 0 {
				continue
			}
			y, err := rasterCrossingY(a.edge, b.edge, exact)
			if err != nil {
				return err
			}
			if y != nil {
				position := rasterBandPosition{exact: y}
				if position.compare(lower) > 0 && position.compare(next) < 0 {
					next = position
				}
			}
		}
		if next.exact != nil {
			for i := range band {
				x, err := rasterBandIntersection(band[i].edge, next, exact)
				if err != nil {
					return err
				}
				band[i].hi = x
			}
		}
		height := next.distance(lower)
		clear(winding)
		covered := 0
		for i, edge := range band {
			if covered >= required && i != 0 && height > 0 {
				left, right := band[i-1], edge
				if left.lo > right.lo || left.hi > right.hi {
					var err error
					left.lo, err = rasterBandExactFloat(left.edge, lower, exact)
					if err != nil {
						return err
					}
					right.lo, err = rasterBandExactFloat(right.edge, lower, exact)
					if err != nil {
						return err
					}
					left.hi, err = rasterBandExactFloat(left.edge, next, exact)
					if err != nil {
						return err
					}
					right.hi, err = rasterBandExactFloat(right.edge, next, exact)
					if err != nil {
						return err
					}
				}
				if err := emit(lower, next, left, right); err != nil {
					return err
				}
			}
			index := edge.edge.region
			before := winding[index] != 0
			if regions[index].rule == GeometryEvenOdd {
				winding[index] ^= 1
			} else {
				winding[index] += edge.edge.direction
			}
			after := winding[index] != 0
			if before != after {
				if after {
					covered++
				} else {
					covered--
				}
			}
		}
		if covered != 0 {
			return fmt.Errorf("%w: raster edges are not closed", ErrInvalid)
		}
		lower = next
	}
	return nil
}

// rasterBandIntersection 求扫描带端点与边的交点，保留边端点的原始坐标
// 入参: edge 纵向递增边, y 扫描带端点, exact 剩余精确计算次数
// 返回: float64 交点横坐标, error 精确计算预算不足错误
func rasterBandIntersection(edge rasterEdge, y rasterBandPosition, exact *int) (float64, error) {
	if edge.start.X == edge.end.X {
		return edge.start.X, nil
	}
	if y.exact != nil {
		return rasterBandExactFloat(edge, y, exact)
	}
	if y.value == edge.end.Y {
		return edge.end.X, nil
	}
	return rasterIntersection(edge.start, edge.end, y.value, exact)
}

// rational 返回纵坐标的只读精确值，普通顶点按需转换
// 返回: *big.Rat 不可由调用方修改的纵坐标
func (p rasterBandPosition) rational() *big.Rat {
	if p.exact != nil {
		return p.exact
	}
	return new(big.Rat).SetFloat64(p.value)
}

// compare 精确比较扫描带纵坐标，不把交叉事件舍入到邻近顶点
// 入参: other 待比较纵坐标
// 返回: int 比较结果
func (p rasterBandPosition) compare(other rasterBandPosition) int {
	if p.exact == nil && other.exact == nil {
		return cmp.Compare(p.value, other.value)
	}
	return p.rational().Cmp(other.rational())
}

// distance 将两个精确纵坐标的差舍入为面积积分所需的高度
// 入参: lower 扫描带起点
// 返回: float64 非负扫描带高度
func (p rasterBandPosition) distance(lower rasterBandPosition) float64 {
	if p.exact == nil && lower.exact == nil {
		return p.value - lower.value
	}
	value, _ := new(big.Rat).Sub(p.rational(), lower.rational()).Float64()
	return value
}

// rasterBandExactFloat 在精确扫描带纵坐标处计算交点，最后才舍入横坐标
// 入参: edge 纵向递增边, position 扫描带纵坐标, exact 剩余精确计算次数
// 返回: float64 交点横坐标, error 精确计算预算不足错误
func rasterBandExactFloat(edge rasterEdge, position rasterBandPosition, exact *int) (float64, error) {
	if err := rasterExactCharge(exact); err != nil {
		return 0, err
	}
	x, _ := rasterRationalIntersection(edge.start, edge.end, position.rational()).Float64()
	return x, nil
}

// rasterBandCompareAt 比较两条边在指定纵坐标处的横坐标，近重合时改用精确运算
// 入参: a 第一条边, b 第二条边, position 指定纵坐标, ax 第一条边的近似横坐标, bx 第二条边的近似横坐标, exact 剩余精确计算次数
// 返回: int 横坐标比较结果, error 精确计算预算不足错误
func rasterBandCompareAt(a, b rasterEdge, position rasterBandPosition, ax, bx float64, exact *int) (int, error) {
	if a.start == b.start && a.end == b.end {
		return 0, nil
	}
	av := a.start.X == a.end.X || position.exact == nil && (position.value == a.start.Y || position.value == a.end.Y)
	bv := b.start.X == b.end.X || position.exact == nil && (position.value == b.start.Y || position.value == b.end.Y)
	if av && bv {
		return cmp.Compare(ax, bx), nil
	}
	spacing := max(math.Abs(math.Nextafter(ax, math.Inf(1))-ax), math.Abs(math.Nextafter(bx, math.Inf(1))-bx))
	if math.Abs(ax-bx) > max(2e-9, 64*spacing) {
		return cmp.Compare(ax, bx), nil
	}
	if err := rasterExactCharge(exact); err != nil {
		return 0, err
	}
	x := rasterRationalIntersection(a.start, a.end, position.rational())
	if err := rasterExactCharge(exact); err != nil {
		return 0, err
	}
	y := rasterRationalIntersection(b.start, b.end, position.rational())
	return x.Cmp(y), nil
}

// rasterBandCompare 比较扫描带起点处的边顺序，近重合时用原始端点精确判定并以终点顺序消除歧义
// 入参: a 第一条扫描带边, b 第二条扫描带边, lo 扫描带起点, hi 扫描带终点, exact 剩余精确计算次数
// 返回: int 从左到右的比较结果, error 精确计算预算不足错误
func rasterBandCompare(a, b rasterBandEdge, lo, hi rasterBandPosition, exact *int) (int, error) {
	if a.edge.start == b.edge.start && a.edge.end == b.edge.end {
		return 0, nil
	}
	order, err := rasterBandCompareAt(a.edge, b.edge, lo, a.lo, b.lo, exact)
	if err != nil || order != 0 {
		return order, err
	}
	order, err = rasterBandCompareAt(a.edge, b.edge, hi, a.hi, b.hi, exact)
	if err != nil || order != 0 {
		return order, err
	}
	if order := cmp.Compare(a.edge.start.X, b.edge.start.X); order != 0 {
		return order, nil
	}
	if order := cmp.Compare(a.edge.start.Y, b.edge.start.Y); order != 0 {
		return order, nil
	}
	if order := cmp.Compare(a.edge.end.X, b.edge.end.X); order != 0 {
		return order, nil
	}
	return cmp.Compare(a.edge.end.Y, b.edge.end.Y), nil
}

// rasterCrossingY 用原始端点精确求两条非水平直线的交叉纵坐标，避免大坐标下斜率相减失真
// 入参: a 第一条纵向递增边, b 第二条纵向递增边, exact 剩余精确计算次数
// 返回: *big.Rat 精确交叉纵坐标，平行时为nil, error 精确计算预算不足错误
func rasterCrossingY(a, b rasterEdge, exact *int) (*big.Rat, error) {
	if err := rasterExactCharge(exact); err != nil {
		return nil, err
	}
	ax, ay := new(big.Rat).SetFloat64(a.start.X), new(big.Rat).SetFloat64(a.start.Y)
	bx, by := new(big.Rat).SetFloat64(b.start.X), new(big.Rat).SetFloat64(b.start.Y)
	ad := new(big.Rat).Sub(new(big.Rat).SetFloat64(a.end.Y), ay)
	bd := new(big.Rat).Sub(new(big.Rat).SetFloat64(b.end.Y), by)
	as := new(big.Rat).Quo(new(big.Rat).Sub(new(big.Rat).SetFloat64(a.end.X), ax), ad)
	bs := new(big.Rat).Quo(new(big.Rat).Sub(new(big.Rat).SetFloat64(b.end.X), bx), bd)
	denominator := new(big.Rat).Sub(as, bs)
	if denominator.Sign() == 0 {
		return nil, nil
	}
	numerator := new(big.Rat).Sub(bx, ax)
	numerator.Add(numerator, new(big.Rat).Mul(as, ay))
	numerator.Sub(numerator, new(big.Rat).Mul(bs, by))
	return numerator.Quo(numerator, denominator), nil
}

// rasterSweepCharge 在执行扫描带或面积积分前按指定上限检查并累计计算量
// 入参: work 已使用计算量, cost 待执行计算量, maxWork 扫描工作预算上限
// 返回: error 计算量超过预算上限错误
func rasterSweepCharge(work *uint64, cost, maxWork uint64) error {
	if *work > maxWork || cost > maxWork-*work {
		return fmt.Errorf("%w: raster scan work", ErrLimit)
	}
	*work += cost
	return nil
}
