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
	"math/bits"
	"slices"
	"sort"
)

// sceneBitmapGlyph 保存位图字形的设备空间逆变换、源覆盖与重采样度量
type sceneBitmapGlyph struct {
	mask    *image.Alpha
	inverse Matrix
	width   int
	height  int
	radiusX float64
	radiusY float64
	bounds  image.Rectangle
}

// sceneBitmapNode 保存平衡包围盒树节点，叶节点以负子节点标识单个字形
type sceneBitmapNode struct {
	bounds image.Rectangle
	left   int
	right  int
	glyph  int
}

// sceneBitmapIndex 保存仅与字形数量成比例的空间索引，不按设备面积或图块数量分配
type sceneBitmapIndex struct {
	glyphs []sceneBitmapGlyph
	nodes  []sceneBitmapNode
}

// boldBoundary 汇总实心梯形的有向边，消除内部共边及水平边的部分重合
type boldBoundary struct {
	lines      map[geometryEdge][]boldBoundaryEvent
	horizontal map[float64][]boldBoundaryEvent
	count      int
	limit      int
}

// boldBoundaryEvent 保存有向区间的排序坐标、几何端点及变化量
type boldBoundaryEvent struct {
	value float64
	point Point
	delta int
}

// glyphPaint 定位字形并按独立填充规则合并为单次文字绘制，含OpenXPS粗体平移偏移
// 入参: glyphs 字形元素, transform 有效设备变换, aliased 是否按输出像素中心判断归属, depth 当前元素深度
// 返回: []scenePaint 字形并集及画刷, error 字体、几何或能力错误
func (r *sceneRenderer) glyphPaint(glyphs *Glyphs, transform Matrix, aliased bool, depth int) ([]scenePaint, error) {
	if glyphs.Fill == nil || glyphs.FontRenderingEmSize == 0 {
		return nil, nil
	}
	count, err := glyphRunCount(glyphs, r.glyphs)
	if err != nil {
		return nil, err
	}
	if err := r.charge(uint64(count)); err != nil {
		return nil, err
	}
	if r.options.font == nil {
		return nil, fmt.Errorf("%w: scene font source is unavailable", ErrUnsupported)
	}
	source, err := r.options.font(glyphs)
	if err != nil {
		return nil, err
	}
	if source == nil || source.metrics == nil || source.face == nil {
		return nil, fmt.Errorf("%w: missing scene font", ErrInvalid)
	}
	selection, bitmap, err := r.glyphBitmapStrike(source, glyphs, transform)
	if err != nil {
		return nil, err
	}
	if bitmap {
		return r.glyphBitmapPaint(source, glyphs, selection, transform, aliased, depth, count)
	}
	run, err := resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, source.glyphYMax, r.glyphs, func() error { return r.charge(1) })
	if err != nil {
		return nil, err
	}
	r.glyphs -= count
	sample, err := r.brush(glyphs.Fill, transform, aliased, depth)
	if err != nil {
		return nil, err
	}
	meta := r.brushMeta
	paint := scenePaint{sample: sample, sampleCached: meta.sampleCached, aliased: aliased, native: r.nativeSample, solid: meta.solid, solidColor: meta.solidColor, gradient: meta.gradient, image: meta.image, visual: meta.visual}
	for _, glyph := range run.glyphs {
		if err := r.charge(0); err != nil {
			return nil, err
		}
		geometry, err := source.glyphOutline(glyph.gid)
		if err != nil {
			return nil, err
		}
		local := glyph.matrix
		if run.bold && r.options.format == FormatOpenXPS {
			shift := glyphs.FontRenderingEmSize / 100
			local.E += shift
			local.F -= shift
		}
		matrix := strokePathCompose(transform, local)
		if !geometryFillMatrixFinite(matrix) {
			return nil, fmt.Errorf("%w: scene glyph transform range", ErrLimit)
		}
		var region rasterRegion
		if run.bold {
			region, err = r.bold(&geometry, run.boldRadius, matrix, aliased)
		} else {
			region, err = r.fill(&geometry, matrix, aliased)
		}
		if err != nil {
			return nil, err
		}
		if len(region.edges) != 0 {
			paint.regions = append(paint.regions, region)
		}
	}
	if len(paint.regions) == 0 {
		return nil, nil
	}
	return []scenePaint{paint}, nil
}

// glyphBitmapStrike 为纯位图字体优先选择精确或EBSC代用strike，无匹配时按欧氏距离选取最近strike
// 入参: source 已加载字体, glyphs 字形元素, transform 元素到设备的有效变换
// 返回: fontBitmapSelection 选中的strike与比例, bool 是否使用位图, error 尺寸、字体、预算或取消错误
func (r *sceneRenderer) glyphBitmapStrike(source *fontSource, glyphs *Glyphs, transform Matrix) (fontBitmapSelection, bool, error) {
	if !fontIsBitmapOnly(source.face) {
		return fontBitmapSelection{}, false, nil
	}
	if r.options.bitmapDensity != nil {
		transform = strokePathCompose(*r.options.bitmapDensity, transform)
	}
	x, y := math.Hypot(transform.A, transform.B), math.Hypot(transform.C, transform.D)
	if glyphs.IsSideways {
		x, y = y, x
	}
	x, y = x*glyphs.FontRenderingEmSize, y*glyphs.FontRenderingEmSize
	if !geometryFinite(x, y) || x <= 0 || y <= 0 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: bitmap glyph requires positive finite device ppem", ErrUnsupported)
	}
	if err := r.charge(uint64(source.face.tables["EBLC"].length) + uint64(source.face.tables["EBSC"].length) + 1); err != nil {
		return fontBitmapSelection{}, false, err
	}
	px, py := math.Round(x), math.Round(y)
	if px >= 1 && py >= 1 && px <= 255 && py <= 255 && math.Abs(x-px) <= 1e-9 && math.Abs(y-py) <= 1e-9 {
		selection, present, err := source.selectBitmapStrikeWithWork(uint16(px), uint16(py), glyphs.IsSideways, r.charge)
		if err != nil || present {
			return selection, present, err
		}
	}
	if err := source.loadBitmaps(r.charge); err != nil {
		return fontBitmapSelection{}, false, err
	}
	if source.bitmaps == nil || len(source.bitmaps.strikes) == 0 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: no matching page bitmap strike", ErrUnsupported)
	}
	if err := r.charge(uint64(len(source.bitmaps.strikes))); err != nil {
		return fontBitmapSelection{}, false, err
	}
	wantFlag := uint8(fontBitmapFlagHorizontal)
	if glyphs.IsSideways {
		wantFlag = fontBitmapFlagVertical
	}
	best, bestDist := -1, math.Inf(1)
	for _, matchDirection := range []bool{true, false} {
		for i, candidate := range source.bitmaps.strikes {
			if candidate.ppemX == 0 || candidate.ppemY == 0 {
				continue
			}
			if matchDirection && candidate.flags&wantFlag == 0 {
				continue
			}
			dist := math.Hypot(float64(candidate.ppemX)-x, float64(candidate.ppemY)-y)
			if best < 0 || dist < bestDist {
				best, bestDist = i, dist
			}
		}
		if best >= 0 {
			break
		}
	}
	if best < 0 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: no matching page bitmap strike", ErrUnsupported)
	}
	strike := source.bitmaps.strikes[best]
	return fontBitmapSelection{strike: best, ppemX: strike.ppemX, ppemY: strike.ppemY, scaleX: 1, scaleY: 1}, true, nil
}

// glyphBitmapPaint 解码位图字形并合并覆盖索引，按单次覆盖结果采样画刷
// 入参: source 字体, glyphs 字形元素, selection 所选strike, transform 设备变换, aliased 像素中心模式, depth 元素深度, count 字形数量
// 返回: []scenePaint 单次覆盖绘制或空白结果, error 定位、解码、画刷、预算或取消错误
func (r *sceneRenderer) glyphBitmapPaint(source *fontSource, glyphs *Glyphs, selection fontBitmapSelection, transform Matrix, aliased bool, depth, count int) ([]scenePaint, error) {
	capacity := min(fontBitmapMaxPixels, max(0, r.options.pixels-r.live), int(min(r.work/2, uint64(^uint(0)>>1))))
	components := min(fontBitmapMaxComponents, int(min(r.work/2, uint64(^uint(0)>>1))))
	decoder := fontBitmapDecode{font: source.bitmaps, strike: &source.bitmaps.strikes[selection.strike], path: make(map[uint16]bool), cache: make(map[uint16]fontBitmapDecoded), components: components, pixels: capacity}
	bitmapLive := 0
	committed := false
	defer func() {
		if !committed && bitmapLive != 0 {
			r.releaseLive(bitmapLive)
		}
	}()
	decode := func(gid uint16) (fontBitmapDecoded, error) {
		if err := r.charge(0); err != nil {
			return fontBitmapDecoded{}, err
		}
		allowance := int(min(r.work/2, uint64(^uint(0)>>1)))
		decoder.components = min(decoder.components, allowance)
		decoder.pixels = min(decoder.pixels, allowance, max(0, r.options.pixels-r.live))
		beforeComponents, beforePixels := decoder.components, decoder.pixels
		decoded, present, err := decoder.decode(gid)
		consumed := beforePixels - decoder.pixels
		r.live += consumed
		bitmapLive += consumed
		if charged := r.charge(uint64(beforeComponents-decoder.components) + uint64(consumed)); charged != nil {
			return fontBitmapDecoded{}, charged
		}
		if err != nil {
			return fontBitmapDecoded{}, err
		}
		if !present {
			return fontBitmapDecoded{}, fmt.Errorf("%w: selected page bitmap glyph %d is absent", ErrUnsupported, gid)
		}
		return decoded, nil
	}
	yMax := func(gid uint16) (float64, error) {
		decoded, err := decode(gid)
		if err != nil {
			return 0, err
		}
		if decoded.metrics.hasVertical {
			return 0, nil
		}
		if !decoded.metrics.hasHorizontal {
			return 0, fmt.Errorf("%w: bitmap glyph has no positioning metrics", ErrUnsupported)
		}
		return math.Round(float64(decoded.metrics.horizontal.bearingY)*selection.scaleY) * float64(source.metrics.unitsPerEm) / float64(selection.ppemY), nil
	}
	run, err := resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, yMax, r.glyphs, func() error { return r.charge(1) })
	if err != nil {
		return nil, err
	}
	r.glyphs -= count
	brush, err := r.brush(glyphs.Fill, transform, aliased, depth)
	if err != nil {
		return nil, err
	}
	brushMeta := r.brushMeta
	paint := scenePaint{aliased: aliased, visual: brushMeta.visual}
	native := r.nativeSample
	var bitmaps []sceneBitmapGlyph
	for _, glyph := range run.glyphs {
		decoded, err := decode(glyph.gid)
		if err != nil {
			return nil, err
		}
		metrics := decoded.metrics
		axis := metrics.horizontal
		local := glyph.matrix
		vertical := run.sideways && metrics.hasVertical
		if vertical {
			axis = metrics.vertical
			local.E, local.F = glyph.origin.X, glyph.origin.Y
		} else if !metrics.hasHorizontal {
			return nil, fmt.Errorf("%w: bitmap glyph has no horizontal bearing", ErrUnsupported)
		}
		if run.bold && r.options.format == FormatOpenXPS {
			local.E += glyphs.FontRenderingEmSize / 100
			local.F -= glyphs.FontRenderingEmSize / 100
		}
		width := int(math.Round(float64(metrics.width) * selection.scaleX))
		height := int(math.Round(float64(metrics.height) * selection.scaleY))
		if width == 0 || height == 0 {
			continue
		}
		unitsX := float64(source.metrics.unitsPerEm) / float64(selection.ppemX)
		unitsY := float64(source.metrics.unitsPerEm) / float64(selection.ppemY)
		bearingY := math.Round(float64(axis.bearingY) * selection.scaleY)
		if vertical {
			bearingY = -bearingY
		}
		pixels := Matrix{A: unitsX, D: -unitsY, E: math.Round(float64(axis.bearingX)*selection.scaleX) * unitsX, F: bearingY * unitsY}
		matrix := strokePathCompose(transform, strokePathCompose(local, pixels))
		if !geometryFillMatrixFinite(matrix) {
			return nil, fmt.Errorf("%w: page bitmap transform range", ErrLimit)
		}
		inverse, err := matrix.Inverse()
		if err != nil {
			return nil, err
		}
		bitmap := sceneBitmapGlyph{mask: decoded.mask, inverse: inverse, width: width, height: height}
		if run.bold {
			bitmap.radiusX, bitmap.radiusY = float64(selection.ppemX)/100, float64(selection.ppemY)/100
		}
		box := Rect{X: -bitmap.radiusX, Y: -bitmap.radiusY, Width: float64(width) + 2*bitmap.radiusX, Height: float64(height) + 2*bitmap.radiusY}
		region, err := r.fill(renderBoxGeometry(box), matrix, aliased)
		if err != nil {
			return nil, err
		}
		bitmap.bounds = r.regionBounds(region, aliased)
		paint.regions = append(paint.regions, region)
		bitmaps = append(bitmaps, bitmap)
	}
	if len(bitmaps) == 0 {
		return nil, nil
	}
	if len(bitmaps) > int(^uint(0)>>1)/2 {
		return nil, fmt.Errorf("%w: bitmap index node count", ErrLimit)
	}
	levels := uint64(bits.Len(uint(len(bitmaps))) + 1)
	if uint64(len(bitmaps)) > r.work/(levels*(levels+1)) {
		return nil, fmt.Errorf("%w: bitmap index build work", ErrLimit)
	}
	if err := r.charge(2 * uint64(len(bitmaps))); err != nil {
		return nil, err
	}
	index := sceneBitmapIndex{glyphs: bitmaps, nodes: make([]sceneBitmapNode, 0, 2*len(bitmaps)-1)}
	if _, err := index.build(r, 0, len(bitmaps)); err != nil {
		return nil, err
	}
	paint.sample = func(point, center Point) (renderColor, error) {
		position := point
		if aliased {
			position = center
		}
		alpha, err := index.coverage(r, 0, position)
		if err != nil {
			return renderColor{}, err
		}
		if alpha == 0 {
			return renderColor{}, nil
		}
		color, err := brush(point, center)
		if err != nil {
			return renderColor{}, err
		}
		return renderColorModulate(color, 1, float64(alpha)/255)
	}
	if brushMeta.sampleCached != nil {
		brushCached := brushMeta.sampleCached
		paint.sampleCached = func(point, center Point, cache *imageSampleCache) (renderColor, error) {
			position := point
			if aliased {
				position = center
			}
			alpha, err := index.coverage(r, 0, position)
			if err != nil {
				return renderColor{}, err
			}
			if alpha == 0 {
				return renderColor{}, nil
			}
			color, err := brushCached(point, center, cache)
			if err != nil {
				return renderColor{}, err
			}
			return renderColorModulate(color, 1, float64(alpha)/255)
		}
	}
	if native != nil {
		paint.native = func(point, center Point) (printNativeColor, error) {
			position := point
			if aliased {
				position = center
			}
			alpha, err := index.coverage(r, 0, position)
			if err != nil || alpha == 0 {
				return printNativeColor{}, err
			}
			value, err := native(point, center)
			value.alpha *= float64(alpha) / 255
			return value, err
		}
	}
	committed = true
	if bitmapLive != 0 {
		reserved := bitmapLive
		r.registerCleanup(func() { r.releaseLive(reserved) })
	}
	return []scenePaint{paint}, nil
}

// build 按当前最长轴的中位数建立平衡树，排序和包围盒工作在执行前预留预算
// 入参: r 当前绘制器, start 字形起始位置, end 字形结束位置，不包含该位置
// 返回: int 当前节点位置, error 工作预算或取消错误
func (s *sceneBitmapIndex) build(r *sceneRenderer, start, end int) (int, error) {
	count := end - start
	if err := r.charge(uint64(count) * uint64(1+2*bits.Len(uint(count)))); err != nil {
		return 0, err
	}
	bounds := s.glyphs[start].bounds
	for i := start + 1; i < end; i++ {
		bounds = bounds.Union(s.glyphs[i].bounds)
	}
	node := len(s.nodes)
	s.nodes = append(s.nodes, sceneBitmapNode{bounds: bounds, left: -1, right: -1, glyph: start})
	if count == 1 {
		return node, nil
	}
	glyphs := s.glyphs[start:end]
	sort.Slice(glyphs, func(i, j int) bool {
		a, b := glyphs[i].bounds, glyphs[j].bounds
		if bounds.Dx() >= bounds.Dy() {
			return int64(a.Min.X)+int64(a.Max.X) < int64(b.Min.X)+int64(b.Max.X)
		}
		return int64(a.Min.Y)+int64(a.Max.Y) < int64(b.Min.Y)+int64(b.Max.Y)
	})
	middle := start + count/2
	left, err := s.build(r, start, middle)
	if err != nil {
		return 0, err
	}
	right, err := s.build(r, middle, end)
	if err != nil {
		return 0, err
	}
	s.nodes[node].left, s.nodes[node].right = left, right
	return node, nil
}

// coverage 查询命中当前包围盒的候选字形并合并覆盖，完全不透明时提前结束
// 入参: r 当前绘制器, node 索引节点位置, point 已选定采样模式的设备位置
// 返回: uint8 候选覆盖的最大等级, error 工作预算或取消错误
func (s *sceneBitmapIndex) coverage(r *sceneRenderer, node int, point Point) (uint8, error) {
	if err := r.charge(1); err != nil {
		return 0, err
	}
	n := s.nodes[node]
	if point.X < float64(n.bounds.Min.X) || point.Y < float64(n.bounds.Min.Y) || point.X >= float64(n.bounds.Max.X) || point.Y >= float64(n.bounds.Max.Y) {
		return 0, nil
	}
	if n.left < 0 {
		return s.glyphs[n.glyph].coverage(r, point)
	}
	left, err := s.coverage(r, n.left, point)
	if err != nil || left == 255 {
		return left, err
	}
	right, err := s.coverage(r, n.right, point)
	return max(left, right), err
}

// coverage 在设备采样点查询位图字形覆盖等级，粗体模式下按设计空间半径扩张采样
// 入参: r 当前场景绘制器, point 设备空间覆盖采样位置
// 返回: uint8 当前覆盖等级, error 变换、工作预算或取消错误
func (b sceneBitmapGlyph) coverage(r *sceneRenderer, point Point) (uint8, error) {
	if err := r.charge(1); err != nil {
		return 0, err
	}
	p := b.inverse.Transform(point)
	if !geometryFinite(p.X, p.Y) {
		return 0, fmt.Errorf("%w: bitmap sample coordinates", ErrLimit)
	}
	if p.X < -b.radiusX || p.Y < -b.radiusY || p.X >= float64(b.width)+b.radiusX || p.Y >= float64(b.height)+b.radiusY {
		return 0, nil
	}
	if b.radiusX == 0 {
		x, y := int(math.Floor(p.X)), int(math.Floor(p.Y))
		return b.mask.AlphaAt((2*x+1)*b.mask.Rect.Dx()/(2*b.width), (2*y+1)*b.mask.Rect.Dy()/(2*b.height)).A, nil
	}
	alpha := uint8(0)
	for y := max(0, int(math.Floor(p.Y-b.radiusY))); y < min(b.height, int(math.Ceil(p.Y+b.radiusY))); y++ {
		for x := max(0, int(math.Floor(p.X-b.radiusX))); x < min(b.width, int(math.Ceil(p.X+b.radiusX))); x++ {
			if err := r.charge(1); err != nil {
				return 0, err
			}
			dx := max(float64(x)-p.X, 0, p.X-float64(x+1)) / b.radiusX
			dy := max(float64(y)-p.Y, 0, p.Y-float64(y+1)) / b.radiusY
			if dx*dx+dy*dy <= 1 {
				alpha = max(alpha, b.mask.AlphaAt((2*x+1)*b.mask.Rect.Dx()/(2*b.width), (2*y+1)*b.mask.Rect.Dy()/(2*b.height)).A)
			}
		}
	}
	return alpha, nil
}

// bold 消除原填充区域内部共边后向外扩张粗体边界并应用斜体与设备变换
// 入参: geometry 字体设计单位轮廓, radius 设计单位扩张半径, transform 有效设备变换, aliased 是否保留设备像素坐标
// 返回: rasterRegion 独立粗体区域, error 几何、数值或资源错误
func (r *sceneRenderer) bold(geometry *Geometry, radius float64, transform Matrix, aliased bool) (rasterRegion, error) {
	if !geometryFinite(radius) || radius <= 0 || !geometryFillMatrixFinite(transform) {
		return rasterRegion{}, fmt.Errorf("%w: bold geometry parameters", ErrInvalid)
	}
	if err := r.geometryWork(geometry); err != nil {
		return rasterRegion{}, err
	}
	scale := math.Hypot(math.Hypot(transform.A, transform.B), math.Hypot(transform.C, transform.D))
	if !geometryFinite(scale) || scale == 0 {
		return rasterRegion{}, fmt.Errorf("%w: bold geometry scale", ErrLimit)
	}
	tolerance := r.options.tolerance / scale / 2
	if !geometryFinite(tolerance) || tolerance <= 0 {
		return rasterRegion{}, fmt.Errorf("%w: bold geometry tolerance", ErrLimit)
	}
	edges, err := geometryFillEdges(geometry, IdentityMatrix(), tolerance, r.edges)
	if err != nil {
		return rasterRegion{}, err
	}
	if len(edges) > rasterMaxEdges {
		return rasterRegion{}, fmt.Errorf("%w: bold source edge count", ErrLimit)
	}
	if err := r.charge(uint64(len(edges)) * 4); err != nil {
		return rasterRegion{}, err
	}
	prepared := make([]rasterEdge, 0, len(edges))
	vertices := make([]float64, 0, 2*len(edges))
	for _, edge := range edges {
		a, b, direction := edge.start, edge.end, 1
		if a.Y == b.Y {
			continue
		}
		if a.Y > b.Y {
			a, b, direction = b, a, -1
		}
		prepared = append(prepared, rasterEdge{start: a, end: b, direction: direction})
		vertices = append(vertices, a.Y, b.Y)
	}
	slices.Sort(vertices)
	vertices = slices.Compact(vertices)
	boundary := boldBoundary{lines: make(map[geometryEdge][]boldBoundaryEvent), horizontal: make(map[float64][]boldBoundaryEvent), limit: rasterMaxEdges}
	active := make([]rasterEdge, 0, len(prepared))
	band := make([]rasterBandEdge, 0, len(prepared))
	regions := []rasterRegion{{rule: geometry.FillRule}}
	winding := []int{0}
	work, charged := uint64(0), uint64(0)
	emit := func(lower, upper rasterBandPosition, left, right rasterBandEdge) error {
		if err := r.charge(work - charged); err != nil {
			return err
		}
		charged = work
		if left.lo == right.lo && left.hi == right.hi {
			return nil
		}
		lo, hi := lower.value, upper.value
		if lower.exact != nil {
			lo, _ = lower.exact.Float64()
		}
		if upper.exact != nil {
			hi, _ = upper.exact.Float64()
		}
		if !geometryFinite(lo, hi) || hi <= lo || left.lo > right.lo || left.hi > right.hi {
			return fmt.Errorf("%w: bold span numerical range", ErrLimit)
		}
		return boundary.add(lo, hi, left, right)
	}
	for i := 1; i < len(vertices); i++ {
		if err := r.charge(uint64(len(prepared))); err != nil {
			return rasterRegion{}, err
		}
		lo, hi := vertices[i-1], vertices[i]
		active = active[:0]
		for _, edge := range prepared {
			if edge.start.Y <= lo && edge.end.Y >= hi {
				active = append(active, edge)
			}
		}
		if err := rasterBandSpans(active, band, lo, hi, regions, 1, winding, &work, rasterMaxWork, &r.exact, emit); err != nil {
			return rasterRegion{}, err
		}
		if err := r.charge(work - charged); err != nil {
			return rasterRegion{}, err
		}
		charged = work
	}
	contours, err := boundary.contours(r.charge)
	if err != nil {
		return rasterRegion{}, err
	}
	builder := strokeOutlineBuilder{fill: geometryFillBuilder{tolerance: r.options.tolerance / 2, maxEdges: rasterMaxEdges}, transform: transform, radius: radius}
	for _, points := range contours {
		before := len(builder.fill.edges)
		if err := builder.boldOutline(points); err != nil {
			return rasterRegion{}, err
		}
		if err := r.charge(uint64(len(builder.fill.edges) - before)); err != nil {
			return rasterRegion{}, err
		}
	}
	expanded, err := boldCancelEdges(builder.fill.edges, r.charge)
	if err != nil {
		return rasterRegion{}, err
	}
	if len(expanded) > r.edges {
		return rasterRegion{}, fmt.Errorf("%w: bold output edge budget", ErrLimit)
	}
	r.edges -= len(expanded)
	return r.region(expanded, GeometryNonZero, aliased)
}

// boldOutline 沿闭合填充轮廓向外生成半笔宽条带与凸角圆弧并加入粗体区域
// 入参: points 实心区域位于左侧的闭合轮廓，不重复首点
// 返回: error 坐标、圆弧或预算错误
func (b *strokeOutlineBuilder) boldOutline(points []Point) error {
	if len(points) < 3 {
		return fmt.Errorf("%w: bold boundary contour", ErrInvalid)
	}
	previous := strokeOutlineDirection(points[len(points)-1], points[0])
	for i, p := range points {
		q := points[(i+1)%len(points)]
		direction := strokeOutlineDirection(p, q)
		normal := Point{direction.Y, -direction.X}
		center, err := b.outlinePoint(p, Point{}, 1)
		if err != nil {
			return err
		}
		end, err := b.outlinePoint(q, Point{}, 1)
		if err != nil {
			return err
		}
		outer, err := b.outlinePoint(p, normal, b.radius)
		if err != nil {
			return err
		}
		outerEnd, err := b.outlinePoint(q, normal, b.radius)
		if err != nil {
			return err
		}
		if err := b.fill.edge(center, end); err != nil {
			return err
		}
		if err := b.devicePolygon([]Point{center, outer, outerEnd, end}); err != nil {
			return err
		}
		if strokeOutlineTriangleSign([3]Point{{}, previous, direction}) > 0 {
			if err := b.round(p, Point{previous.Y, -previous.X}, normal); err != nil {
				return err
			}
		}
		previous = direction
	}
	return nil
}

// boldCancelEdges 抵消完全重合的反向边，保留绕数及稳定的输出顺序，不焊接近似坐标
// 入参: edges 有限有向边, charge 工作量及取消检查函数
// 返回: []geometryEdge 复用原缓冲区的边, error 预算或取消错误
func boldCancelEdges(edges []geometryEdge, charge func(uint64) error) ([]geometryEdge, error) {
	if err := charge(uint64(len(edges)) * 2); err != nil {
		return nil, err
	}
	counts := make(map[geometryEdge]int, len(edges))
	for i, edge := range edges {
		if i%1024 == 0 {
			if err := charge(0); err != nil {
				return nil, err
			}
		}
		direction := 1
		if edge.start.X > edge.end.X || edge.start.X == edge.end.X && edge.start.Y > edge.end.Y {
			edge.start, edge.end, direction = edge.end, edge.start, -1
		}
		counts[edge] += direction
	}
	result := edges[:0]
	for i, edge := range edges {
		if i%1024 == 0 {
			if err := charge(0); err != nil {
				return nil, err
			}
		}
		if edge.start.X > edge.end.X || edge.start.X == edge.end.X && edge.start.Y > edge.end.Y {
			edge.start, edge.end = edge.end, edge.start
		}
		count := counts[edge]
		if count == 0 {
			continue
		}
		if count < 0 {
			counts[edge] = count + 1
			edge.start, edge.end = edge.end, edge.start
		} else {
			counts[edge] = count - 1
		}
		result = append(result, edge)
	}
	return result, nil
}

// add 加入实心梯形边界，沿同一原始直线保留端点事件，避免扫描带引入额外转角
// 入参: lo 上端纵坐标, hi 下端纵坐标, left 左侧有向原边及交点, right 右侧有向原边及交点
// 返回: error 中间边数超限错误
func (b *boldBoundary) add(lo, hi float64, left, right rasterBandEdge) error {
	if b.count > b.limit-4 {
		return fmt.Errorf("%w: bold boundary edge budget", ErrLimit)
	}
	b.count += 4
	b.horizontal[lo] = append(b.horizontal[lo], boldBoundaryEvent{left.lo, Point{left.lo, lo}, 1}, boldBoundaryEvent{right.lo, Point{right.lo, lo}, -1})
	b.horizontal[hi] = append(b.horizontal[hi], boldBoundaryEvent{left.hi, Point{left.hi, hi}, -1}, boldBoundaryEvent{right.hi, Point{right.hi, hi}, 1})
	for i, edge := range []rasterBandEdge{left, right} {
		direction := 2*i - 1
		line := geometryEdge{edge.edge.start, edge.edge.end}
		b.lines[line] = append(b.lines[line], boldBoundaryEvent{lo, Point{edge.lo, lo}, direction}, boldBoundaryEvent{hi, Point{edge.hi, hi}, -direction})
	}
	return nil
}

// contours 将消除内部边后的有向边连接为闭合轮廓，分支按左侧实心区域选取转向
// 入参: charge 工作量及取消检查函数
// 返回: [][]Point 闭合轮廓，不重复末尾首点, error 边界、预算或取消错误
func (b *boldBoundary) contours(charge func(uint64) error) ([][]Point, error) {
	outgoing := make(map[Point][]Point)
	add := func(a, c Point, direction int) {
		if direction < 0 {
			a, c = c, a
		}
		outgoing[a] = append(outgoing[a], c)
	}
	collect := func(events []boldBoundaryEvent) error {
		if err := charge(uint64(len(events)) * uint64(1+bits.Len(uint(len(events))))); err != nil {
			return err
		}
		slices.SortFunc(events, func(a, c boldBoundaryEvent) int { return cmp.Compare(a.value, c.value) })
		winding := 0
		var start Point
		for i := 0; i < len(events); {
			value, point, before := events[i].value, events[i].point, winding
			for i < len(events) && events[i].value == value {
				winding += events[i].delta
				i++
			}
			if winding != before {
				if before != 0 {
					add(start, point, before)
				}
				start = point
			}
		}
		if winding != 0 {
			return fmt.Errorf("%w: open bold boundary interval", ErrInvalid)
		}
		return nil
	}
	for _, events := range b.lines {
		if err := collect(events); err != nil {
			return nil, err
		}
	}
	for _, events := range b.horizontal {
		if err := collect(events); err != nil {
			return nil, err
		}
	}
	var contours [][]Point
	for start, next := range outgoing {
		for len(next) != 0 {
			if err := charge(1); err != nil {
				return nil, err
			}
			previous, current := start, next[len(next)-1]
			outgoing[start] = next[:len(next)-1]
			points := []Point{start}
			for current != start {
				points = append(points, current)
				candidates := outgoing[current]
				if err := charge(uint64(len(candidates) + 1)); err != nil {
					return nil, err
				}
				if len(candidates) == 0 {
					return nil, fmt.Errorf("%w: open bold boundary", ErrInvalid)
				}
				chosen, angle := 0, math.Inf(-1)
				incoming := strokeOutlineDirection(previous, current)
				for i, candidate := range candidates {
					direction := strokeOutlineDirection(current, candidate)
					turn := math.Atan2(incoming.X*direction.Y-incoming.Y*direction.X, incoming.X*direction.X+incoming.Y*direction.Y)
					if turn > angle {
						chosen, angle = i, turn
					}
				}
				following := candidates[chosen]
				candidates[chosen] = candidates[len(candidates)-1]
				outgoing[current] = candidates[:len(candidates)-1]
				previous, current = current, following
			}
			if len(points) >= 3 {
				contours = append(contours, points)
			}
			next = outgoing[start]
		}
	}
	return contours, nil
}
