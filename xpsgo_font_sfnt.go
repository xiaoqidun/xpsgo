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
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"image"
	"math"
	"math/bits"
	"sort"
	"sync"
)

// trueTypeMaxDepth 等常量限制TrueType字形解析资源上限
const (
	trueTypeMaxDepth      = 64
	trueTypeMaxPoints     = 1 << 18
	trueTypeMaxContours   = 1 << 16
	trueTypeMaxComponents = 4096
)

// fontBitmapMaxStrikes 等常量限制字体位图解析资源上限
const (
	fontBitmapMaxStrikes    = 256
	fontBitmapMaxSubtables  = 65536
	fontBitmapMaxRecords    = 1 << 20
	fontBitmapMaxDepth      = 64
	fontBitmapMaxComponents = 65536
	fontBitmapMaxPixels     = 16 << 20
)

// fontBitmapMaxScaleRecords 限制位图缩放记录的解析数量上限
const fontBitmapMaxScaleRecords = 65536

// cffFontDict 保存字体字典、私有参数及显式矩阵，缺省矩阵由坐标转换层解释
type cffFontDict struct {
	dict    cffDict
	private cffPrivate
	matrix  *Matrix
}

// cffFont 保存字体集中一个字体的字形程序及字典选择关系，不将CFF字体序号作为TTC索引
type cffFont struct {
	set            *cffSet
	top            cffFontDict
	charstrings    [][]byte
	charset        *cffCharset
	fontDict       []cffFontDict
	fdSelect       []uint8
	cid            bool
	charstringType float64
	paintType      float64
}

// cffFontParser 在字体字典间共享解析预算及相同私有字典的只读结果
type cffFontParser struct {
	set     *cffSet
	entries int
	subrs   int
	private map[[2]uint32]cffPrivate
}

// fontSource 持有共享的只读字体数据，字符映射、轮廓和位图索引分别按需解析
type fontSource struct {
	face         *fontFace
	metrics      *fontMetrics
	cmapOnce     sync.Once
	cmap         *fontCmap
	cmapErr      error
	outlineOnce  sync.Once
	trueType     *trueTypeFont
	cff          *cffFont
	outlineErr   error
	bitmapMutex  sync.Mutex
	bitmapLoaded bool
	bitmaps      *fontBitmaps
	bitmapErr    error
	bitmapScale  fontSourceBitmapScale
}

// fontSourceBitmapScale 保存单个字体访问器独立的EBSC懒加载状态
type fontSourceBitmapScale struct {
	mutex  sync.Mutex
	loaded bool
	scales *fontBitmapScales
	err    error
}

// trueTypeFont 保存只读TrueType轮廓表及已经校验的字形位置
type trueTypeFont struct {
	face      *fontFace
	glyf      []byte
	locations []uint32
	numGlyphs uint16
}

// trueTypeGlyph 保存未hint的闭合轮廓、glyf头部声明边界及最终度量来源
type trueTypeGlyph struct {
	geometry             Geometry
	bounds               Rect
	metricsGlyph         uint16
	metricsBounds        Rect
	metricsPositionKnown bool
	points               []trueTypePoint
	endPoints            []int
	components           []trueTypeComponent
	instructions         []byte
}

// trueTypePoint 保存原始编号对应的控制点，不包含隐含中点
type trueTypePoint struct {
	point   Point
	onCurve bool
}

// trueTypeComponent 保存直接组件的原始参数、标志及设计单位定位矩阵
type trueTypeComponent struct {
	flags     uint16
	glyph     uint16
	argument1 int
	argument2 int
	transform Matrix
}

// trueTypeBudget 限制单次字形展开的累计工作量及活动引用路径
type trueTypeBudget struct {
	metrics    *fontMetrics
	points     int
	contours   int
	components int
	path       []uint16
	context    context.Context
	work       int
	workLimit  int
}

// trueTypeCursor 以错误状态记录字形数据的有界读取位置
type trueTypeCursor struct {
	data []byte
	pos  int
	err  error
}

// fontBitmapAxisMetrics 保存未经缩放或轴交换的原始字形轴度量
type fontBitmapAxisMetrics struct {
	bearingX int8
	bearingY int8
	advance  uint8
}

// fontBitmapMetrics 保存位图字形声明的像素尺寸及实际提供的横竖度量
type fontBitmapMetrics struct {
	width         uint8
	height        uint8
	horizontal    fontBitmapAxisMetrics
	vertical      fontBitmapAxisMetrics
	hasHorizontal bool
	hasVertical   bool
}

// fontBitmapLineMetrics 保存位图strike的核心行度量字段
type fontBitmapLineMetrics struct {
	ascender  int8
	descender int8
	widthMax  uint8
}

// fontBitmapEntry 保存已验证的数据区间及索引提供的固定度量
type fontBitmapEntry struct {
	gid         uint16
	imageFormat uint16
	start       uint64
	end         uint64
	fixed       bool
	metrics     fontBitmapMetrics
}

// fontBitmapStrike 保存原序strike的元数据及按字形编号排序的只读目录
type fontBitmapStrike struct {
	ppemX      uint8
	ppemY      uint8
	bitDepth   uint8
	flags      uint8
	startGlyph uint16
	endGlyph   uint16
	entries    []fontBitmapEntry
}

// fontBitmaps 保存独立于glyf的只读嵌入位图索引
type fontBitmaps struct {
	data    []byte
	strikes []fontBitmapStrike
}

// fontBitmapDecoded 保存单次解码内可复用的完成结果，不向其他请求共享像素
type fontBitmapDecoded struct {
	mask    *image.Alpha
	metrics fontBitmapMetrics
}

// fontBitmapDecode 保存单次组件展开的路径、缓存及总工作量预算
type fontBitmapDecode struct {
	font       *fontBitmaps
	strike     *fontBitmapStrike
	path       map[uint16]bool
	cache      map[uint16]fontBitmapDecoded
	components int
	pixels     int
}

// fontBitmapScale 保存EBSC表的位图缩放原始记录及目标行度量
type fontBitmapScale struct {
	horizontal      fontBitmapLineMetrics
	vertical        fontBitmapLineMetrics
	ppemX           uint8
	ppemY           uint8
	substitutePpemX uint8
	substitutePpemY uint8
}

// fontBitmapScaleTarget 保存首条记录位置及相同目标下的内容冲突状态
type fontBitmapScaleTarget struct {
	record    int
	ambiguous bool
}

// fontBitmapScales 保存原序EBSC记录及只读目标尺寸索引
type fontBitmapScales struct {
	records []fontBitmapScale
	targets map[[2]uint8]fontBitmapScaleTarget
}

// fontBitmapSelection 保存选中的源strike位置、请求尺寸及双轴缩放比例
type fontBitmapSelection struct {
	strike int
	ppemX  uint8
	ppemY  uint8
	scaleX float64
	scaleY float64
}

// parseCFFFont 连接指定字体的字符集、编码、字典及Type2执行Context，保留绘制参数而不执行绘制
// 入参: set 已解析的字体集, index 字体集中的零基序号
// 返回: *cffFont 字体程序, error 结构、能力或资源限制错误
func parseCFFFont(set *cffSet, index int) (*cffFont, error) {
	if set == nil || index < 0 || index >= len(set.top) || index >= len(set.names) {
		return nil, fmt.Errorf("%w: CFF font index", ErrInvalid)
	}
	if len(set.names[index]) == 0 || set.names[index][0] == 0 {
		return nil, fmt.Errorf("%w: CFF font is unnamed or deleted", ErrInvalid)
	}
	dict := set.top[index]
	encodings := 0
	for _, entry := range dict {
		if entry.operator == 16 {
			encodings++
		}
	}
	if encodings > 1 {
		return nil, fmt.Errorf("%w: repeated CFF Encoding operator", ErrInvalid)
	}
	if _, present := dict.value(0x0c14); present {
		return nil, fmt.Errorf("%w: CFF SyntheticBase", ErrUnsupported)
	}
	font := &cffFont{set: set, charstringType: 2}
	for _, item := range []struct {
		operator uint16
		target   *float64
	}{{0x0c06, &font.charstringType}, {0x0c05, &font.paintType}, {0x0c08, nil}} {
		if operands, present := dict.value(item.operator); present {
			if len(operands) != 1 || !geometryFinite(operands[0].value) {
				return nil, fmt.Errorf("%w: CFF font parameter %d", ErrInvalid, item.operator)
			}
			if item.target != nil {
				*item.target = operands[0].value
			}
		}
	}
	if operands, present := dict.value(0x0c1e); present {
		if len(dict) == 0 || dict[0].operator != 0x0c1e || len(operands) != 3 {
			return nil, fmt.Errorf("%w: CFF ROS order or operands", ErrInvalid)
		}
		for i := range 2 {
			sid, err := cffInteger(operands[i:i+1], 0, 64999)
			if err != nil || sid >= 391+int64(len(set.strings)) {
				return nil, fmt.Errorf("%w: CFF ROS string reference", ErrInvalid)
			}
		}
		font.cid = true
	}
	parser := cffFontParser{set: set, entries: cffMaxDictEntries, subrs: 1 << 20, private: make(map[[2]uint32]cffPrivate)}
	var err error
	font.top, err = parser.fontDict(dict, !font.cid)
	if err != nil {
		return nil, err
	}
	offset, err := cffRequiredOffset(dict, 17)
	if err != nil {
		return nil, err
	}
	font.charstrings, _, err = parseCFFIndex(set.data, offset)
	if err != nil {
		return nil, err
	}
	if len(font.charstrings) == 0 {
		return nil, fmt.Errorf("%w: CFF CharStrings lacks notdef", ErrInvalid)
	}
	offset, err = cffOptionalOffset(dict, 15)
	if err != nil {
		return nil, err
	}
	font.charset, err = parseCFFCharset(set.data, offset, len(font.charstrings), len(set.strings), font.cid)
	if err != nil {
		return nil, err
	}
	if !font.cid {
		offset, err = cffOptionalOffset(dict, 16)
		if err != nil {
			return nil, err
		}
		if _, err = parseCFFEncoding(set.data, offset, font.charset); err != nil {
			return nil, err
		}
		return font, nil
	}
	if _, present := dict.value(16); present {
		return nil, fmt.Errorf("%w: CID CFF must not declare Encoding", ErrInvalid)
	}
	offset, err = cffRequiredOffset(dict, 0x0c24)
	if err != nil {
		return nil, err
	}
	dictionaries, _, err := parseCFFIndex(set.data, offset)
	if err != nil {
		return nil, err
	}
	if len(dictionaries) == 0 {
		return nil, fmt.Errorf("%w: empty CFF FDArray", ErrInvalid)
	}
	font.fontDict = make([]cffFontDict, len(dictionaries))
	for i, data := range dictionaries {
		fd, err := parseCFFDictLimit(data, parser.entries)
		if err != nil {
			return nil, fmt.Errorf("CFF Font DICT %d: %w", i, err)
		}
		parser.entries -= len(fd)
		font.fontDict[i], err = parser.fontDict(fd, true)
		if err != nil {
			return nil, fmt.Errorf("CFF Font DICT %d: %w", i, err)
		}
	}
	offset, err = cffRequiredOffset(dict, 0x0c25)
	if err != nil {
		return nil, err
	}
	font.fdSelect, err = parseCFFFDSelect(set.data, offset, len(font.charstrings), len(font.fontDict))
	if err != nil {
		return nil, err
	}
	return font, nil
}

// cffRequiredOffset 读取必需的非负整数偏移，保留零值与缺失之间的区别
// 入参: dict 字典, operator 偏移操作符
// 返回: uint32 偏移, error 缺失或类型错误
func cffRequiredOffset(dict cffDict, operator uint16) (uint32, error) {
	operands, present := dict.value(operator)
	if !present {
		return 0, fmt.Errorf("%w: missing CFF operator %d", ErrInvalid, operator)
	}
	value, err := cffInteger(operands, 0, math.MaxUint32)
	return uint32(value), err
}

// cffOptionalOffset 读取缺省为零的字符集或编码偏移
// 入参: dict 字典, operator 偏移操作符
// 返回: uint32 偏移或预定义编号, error 类型错误
func cffOptionalOffset(dict cffDict, operator uint16) (uint32, error) {
	if _, present := dict.value(operator); !present {
		return 0, nil
	}
	return cffRequiredOffset(dict, operator)
}

// fontDict 解析显式FontMatrix并按需连接必需的Private字典，复用相同范围的解析结果
// 入参: dict 字体字典, private 是否要求私有字典
// 返回: cffFontDict 字体字典配置, error 参数、范围或累计资源错误
func (p *cffFontParser) fontDict(dict cffDict, private bool) (cffFontDict, error) {
	result := cffFontDict{dict: dict}
	if operands, present := dict.value(0x0c07); present {
		if len(operands) != 6 {
			return result, fmt.Errorf("%w: CFF FontMatrix operand count", ErrInvalid)
		}
		var v [6]float64
		for i := range v {
			v[i] = operands[i].value
		}
		if !geometryFinite(v[:]...) {
			return result, fmt.Errorf("%w: non-finite CFF FontMatrix", ErrInvalid)
		}
		result.matrix = &Matrix{v[0], v[1], v[2], v[3], v[4], v[5]}
	}
	if !private {
		return result, nil
	}
	operands, present := dict.value(18)
	if !present || len(operands) != 2 {
		return result, fmt.Errorf("%w: missing or invalid CFF Private range", ErrInvalid)
	}
	var key [2]uint32
	for i := range key {
		value, err := cffInteger(operands[i:i+1], 0, math.MaxUint32)
		if err != nil {
			return result, err
		}
		key[i] = uint32(value)
	}
	if cached, present := p.private[key]; present {
		result.private = cached
		return result, nil
	}
	parsed, err := parseCFFPrivate(p.set.data, key[1], key[0])
	if err != nil {
		return result, err
	}
	if len(parsed.dict) > p.entries || len(parsed.localSubr) > p.subrs {
		return result, fmt.Errorf("%w: CFF font dictionary expansion", ErrLimit)
	}
	p.entries -= len(parsed.dict)
	p.subrs -= len(parsed.localSubr)
	p.private[key] = parsed
	result.private = parsed
	return result, nil
}

// rawGlyph 执行单个Type2程序，按FDSelect选择局部子程序，不展开组合字符或应用矩阵
// 入参: gid 字形索引
// 返回: *type2Glyph 原始字形, error 索引、能力或程序错误
func (f *cffFont) rawGlyph(gid uint16) (*type2Glyph, error) {
	if int(gid) >= len(f.charstrings) {
		return nil, fmt.Errorf("%w: CFF glyph index %d", ErrInvalid, gid)
	}
	if f.charstringType != 2 {
		return nil, fmt.Errorf("%w: CFF CharstringType %g", ErrUnsupported, f.charstringType)
	}
	private := f.top.private
	if f.cid {
		private = f.fontDict[f.fdSelect[gid]].private
	}
	return parseType2(f.charstrings[gid], type2Context{
		globalSubr: f.set.globalSubr, localSubr: private.localSubr,
		defaultWidth: private.defaultWidth, nominalWidth: private.nominalWidth,
		randomSeed: private.randomSeed,
	})
}

// glyph 展开Type2的非嵌套组合字符，结果保留charstring坐标与宽度，未应用字体矩阵或绘制样式
// 入参: gid 字形索引
// 返回: *type2Glyph 独立可修改的完整原始轮廓, error 字形、字符引用或组合结构错误
func (f *cffFont) glyph(gid uint16) (*type2Glyph, error) {
	glyph, err := f.rawGlyph(gid)
	if err != nil || glyph.seac == nil {
		return glyph, err
	}
	if f.cid {
		return nil, fmt.Errorf("%w: CID CFF cannot use named seac components", ErrInvalid)
	}
	for i, code := range []byte{glyph.seac.base, glyph.seac.accent} {
		sid := cffStandardSID(code)
		component, present := f.charset.glyph(sid)
		if sid == 0 || !present {
			return nil, fmt.Errorf("%w: missing CFF seac component %d", ErrInvalid, code)
		}
		part, err := f.rawGlyph(component)
		if err != nil {
			return nil, err
		}
		if part.seac != nil {
			return nil, fmt.Errorf("%w: nested CFF seac", ErrInvalid)
		}
		if i == 1 {
			if err := cffTranslateGlyph(&part.geometry, glyph.seac.offset); err != nil {
				return nil, err
			}
		}
		glyph.geometry.Figures = append(glyph.geometry.Figures, part.geometry.Figures...)
	}
	glyph.seac = nil
	return glyph, nil
}

// cffTranslateGlyph 平移新解码轮廓的起点、端点和曲线控制点，不修改字体程序
// 入参: geometry 独立字形轮廓, offset 平移量
// 返回: error 坐标超出有限范围错误
func cffTranslateGlyph(geometry *Geometry, offset Point) error {
	for i := range geometry.Figures {
		figure := &geometry.Figures[i]
		figure.StartPoint.X += offset.X
		figure.StartPoint.Y += offset.Y
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return fmt.Errorf("%w: CFF component translation overflow", ErrLimit)
		}
		for j := range figure.Segments {
			segment := &figure.Segments[j]
			points := []*Point{&segment.Point}
			if segment.Kind == GeometryCubic {
				points = append(points, &segment.Control1, &segment.Control2)
			}
			for _, point := range points {
				point.X += offset.X
				point.Y += offset.Y
				if !geometryFinite(point.X, point.Y) {
					return fmt.Errorf("%w: CFF component translation overflow", ErrLimit)
				}
			}
		}
	}
	return nil
}

// newFontSource 解析共用字体度量，不因尚未使用的字符映射或轮廓表而阻止显式字形定位
// 入参: face 已校验封装范围的字体面，使用期间不得修改其数据
// 返回: *fontSource 字体访问器, error 度量表错误
func newFontSource(face *fontFace) (*fontSource, error) {
	metrics, err := parseFontMetrics(face)
	if err != nil {
		return nil, err
	}
	return &fontSource{face: face, metrics: metrics}, nil
}

// loadCmap 初始化选定字符映射，结果及错误由一次性初始化机制保护
func (f *fontSource) loadCmap() {
	data, err := f.face.table("cmap")
	if err == nil {
		f.cmap, err = parseFontCmap(data, uint32(f.metrics.numGlyphs))
	}
	f.cmapErr = err
}

// glyphIndex 将Unicode字符映射到当前字体的字形，不回退到其他字体或低优先级编码表
// 入参: char Unicode字符
// 返回: uint16 字形编号，缺字返回零, error 映射表或编码转换错误
func (f *fontSource) glyphIndex(char rune) (uint16, error) {
	f.cmapOnce.Do(f.loadCmap)
	if f.cmapErr != nil {
		return 0, f.cmapErr
	}
	return f.cmap.unicodeGlyph(char)
}

// loadBitmaps 初始化嵌入位图目录，只缓存完整结果及确定性错误
// 入参: charge 可选预算及取消回调
// 返回: error 目录解析、预算或取消错误
func (f *fontSource) loadBitmaps(charge func(uint64) error) error {
	if err := fontBitmapWork(charge, 0); err != nil {
		return err
	}
	f.bitmapMutex.Lock()
	if f.bitmapLoaded {
		err := f.bitmapErr
		f.bitmapMutex.Unlock()
		return err
	}
	f.bitmapMutex.Unlock()
	value, err := parseFontBitmapsWithWork(f.face, uint32(f.metrics.numGlyphs), charge)
	if fontBitmapRetry(err) {
		return err
	}
	if canceled := fontBitmapWork(charge, 0); canceled != nil {
		return canceled
	}
	f.bitmapMutex.Lock()
	if !f.bitmapLoaded {
		f.bitmaps, f.bitmapErr, f.bitmapLoaded = value, err, true
	}
	err = f.bitmapErr
	f.bitmapMutex.Unlock()
	return err
}

// loadOutline 初始化轮廓访问器并检查CFF与SFNT的字形数量，不选择未知字体集中的任意字体
func (f *fontSource) loadOutline() {
	if !f.face.cff {
		_, hasGlyf := f.face.tables["glyf"]
		_, hasLoca := f.face.tables["loca"]
		_, hasBitmap := f.face.tables["EBLC"]
		if !hasGlyf && !hasLoca && hasBitmap {
			f.outlineErr = fmt.Errorf("%w: bitmap-only font has no scalable outline", ErrUnsupported)
			return
		}
		f.trueType, f.outlineErr = parseTrueType(f.face)
		return
	}
	data, err := f.face.table("CFF ")
	if err != nil {
		f.outlineErr = err
		return
	}
	set, err := parseCFFSet(data)
	if err != nil {
		f.outlineErr = err
		return
	}
	if len(set.top) != 1 {
		f.outlineErr = fmt.Errorf("%w: selecting a font from a multi-font CFF table", ErrUnsupported)
		return
	}
	f.cff, err = parseCFFFont(set, 0)
	if err == nil && len(f.cff.charstrings) != int(f.metrics.numGlyphs) {
		err = fmt.Errorf("%w: CFF CharStrings count does not match maxp", ErrInvalid)
	}
	f.outlineErr = err
}

// glyphOutline 返回以水平字符原点为基准的独立设计单位轮廓，纵轴向上且不应用页面变换或样式模拟
// 入参: gid 当前物理字体面的字形编号
// 返回: Geometry 未hint的非零填充轮廓, error 轮廓、矩阵或尚未支持的绘制方式错误
func (f *fontSource) glyphOutline(gid uint16) (Geometry, error) {
	if gid >= f.metrics.numGlyphs {
		return Geometry{}, fmt.Errorf("%w: font glyph index %d", ErrInvalid, gid)
	}
	f.outlineOnce.Do(f.loadOutline)
	if f.outlineErr != nil {
		return Geometry{}, f.outlineErr
	}
	if f.trueType != nil {
		glyph, err := f.trueType.glyph(gid)
		if err != nil {
			return Geometry{}, err
		}
		_, bearing, err := f.metrics.horizontal(glyph.metricsGlyph)
		if err != nil {
			return Geometry{}, err
		}
		x := float64(bearing) - glyph.metricsBounds.X
		if x != 0 {
			if err := fontTransformOutline(&glyph.geometry, Matrix{A: 1, D: 1, E: x}); err != nil {
				return Geometry{}, err
			}
		}
		return glyph.geometry, nil
	}
	if f.cff.paintType != 0 {
		return Geometry{}, fmt.Errorf("%w: CFF PaintType %g outline painting", ErrUnsupported, f.cff.paintType)
	}
	glyph, err := f.cff.glyph(gid)
	if err != nil {
		return Geometry{}, err
	}
	matrix, err := f.cff.designMatrix(gid, f.metrics.unitsPerEm)
	if err != nil {
		return Geometry{}, err
	}
	if err := fontTransformOutline(&glyph.geometry, matrix); err != nil {
		return Geometry{}, err
	}
	return glyph.geometry, nil
}

// glyphYMax 读取TrueType声明上边界或计算CFF曲线的实际设计单位上边界
// 入参: gid 字形编号
// 返回: float64 纵轴向上的最大坐标，空字形返回零, error 轮廓或范围错误
func (f *fontSource) glyphYMax(gid uint16) (float64, error) {
	if gid >= f.metrics.numGlyphs {
		return 0, fmt.Errorf("%w: font glyph index %d", ErrInvalid, gid)
	}
	f.outlineOnce.Do(f.loadOutline)
	if f.outlineErr != nil {
		return 0, f.outlineErr
	}
	if f.trueType != nil {
		start, end := f.trueType.locations[gid], f.trueType.locations[int(gid)+1]
		if start == end {
			return 0, nil
		}
		if end-start < 10 {
			return 0, fmt.Errorf("%w: truncated TrueType glyph header", ErrInvalid)
		}
		return float64(int16(binary.BigEndian.Uint16(f.trueType.glyf[start+8:]))), nil
	}
	geometry, err := f.glyphOutline(gid)
	if err != nil {
		return 0, err
	}
	figures := geometry.Figures[:0]
	for _, figure := range geometry.Figures {
		if len(figure.Segments) != 0 {
			figures = append(figures, figure)
		}
	}
	geometry.Figures = figures
	bounds, err := geometry.Bounds()
	return bounds.Y + bounds.Height, err
}

// designMatrix 计算CFF字形坐标到SFNT设计单位的变换矩阵，CID字体按先FD后Top组合
// 入参: gid 字形编号, unitsPerEm SFNT每em设计单位数
// 返回: Matrix 字形到设计单位的变换, error 索引或溢出错误
func (f *cffFont) designMatrix(gid uint16, unitsPerEm uint16) (Matrix, error) {
	if int(gid) >= len(f.charstrings) || unitsPerEm < 16 || unitsPerEm > 16384 {
		return Matrix{}, fmt.Errorf("%w: CFF design matrix glyph or unitsPerEm", ErrInvalid)
	}
	var matrix Matrix
	if f.top.matrix != nil {
		matrix = *f.top.matrix
	} else {
		matrix = Matrix{A: 0.001, D: 0.001}
	}
	if f.cid {
		fd := f.fontDict[f.fdSelect[gid]].matrix
		if fd != nil {
			if f.top.matrix == nil {
				matrix = *fd
			} else {
				matrix = matrix.Mul(*fd)
			}
		}
	}
	u := float64(unitsPerEm)
	matrix = (Matrix{A: u, D: u}).Mul(matrix)
	if !geometryFinite(matrix.A, matrix.B, matrix.C, matrix.D, matrix.E, matrix.F) {
		return Matrix{}, fmt.Errorf("%w: CFF design matrix overflow", ErrLimit)
	}
	return matrix, nil
}

// fontTransformOutline 原地变换新解码字体轮廓的端点及有效控制点，不对度量表再施加字体矩阵
// 入参: geometry 独立的字体轮廓, matrix 设计单位变换
// 返回: error 非字体曲线类型或非有限坐标错误
func fontTransformOutline(geometry *Geometry, matrix Matrix) error {
	for i := range geometry.Figures {
		figure := &geometry.Figures[i]
		figure.StartPoint = matrix.Transform(figure.StartPoint)
		if !geometryFinite(figure.StartPoint.X, figure.StartPoint.Y) {
			return fmt.Errorf("%w: transformed font contour overflow", ErrLimit)
		}
		for j := range figure.Segments {
			segment := &figure.Segments[j]
			points := [3]*Point{&segment.Point, &segment.Control1, &segment.Control2}
			count := 1
			switch segment.Kind {
			case GeometryQuadratic:
				count = 2
			case GeometryCubic:
				count = 3
			case GeometryLine:
			default:
				return fmt.Errorf("%w: invalid font outline segment", ErrInvalid)
			}
			for _, point := range points[:count] {
				*point = matrix.Transform(*point)
				if !geometryFinite(point.X, point.Y) {
					return fmt.Errorf("%w: transformed font curve overflow", ErrLimit)
				}
			}
		}
	}
	return nil
}

// fontBitmapRetry 判断初始化是否因当前请求预算或取消而失败，不将该状态缓存为字体缺陷
// 入参: err 初始化错误
// 返回: bool 是否应允许后续请求重试
func fontBitmapRetry(err error) bool {
	return errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded)
}

// load 有界初始化EBSC，完整结果和确定性错误由互斥锁保护
// 入参: face 只读字体面, charge 可选预算及取消回调
// 返回: *fontBitmapScales 缩放目录或nil, error 目录、预算或取消错误
func (s *fontSourceBitmapScale) load(face *fontFace, charge func(uint64) error) (*fontBitmapScales, error) {
	if err := fontBitmapWork(charge, 0); err != nil {
		return nil, err
	}
	s.mutex.Lock()
	if s.loaded {
		value, err := s.scales, s.err
		s.mutex.Unlock()
		return value, err
	}
	s.mutex.Unlock()
	value, err := parseFontBitmapScalesWithWork(face, charge)
	if fontBitmapRetry(err) {
		return nil, err
	}
	if canceled := fontBitmapWork(charge, 0); canceled != nil {
		return nil, canceled
	}
	s.mutex.Lock()
	if !s.loaded {
		s.scales, s.err, s.loaded = value, err, true
	}
	value, err = s.scales, s.err
	s.mutex.Unlock()
	return value, err
}

// selectBitmapStrikeWithWork 在索引和缩放目录初始化时执行预算及取消检查
// 入参: ppemX 横轴请求尺寸, ppemY 竖轴请求尺寸, charge 可选预算及取消回调
// 返回: fontBitmapSelection 原始选择结果, bool 是否匹配, error 请求、目录、预算或取消错误
func (f *fontSource) selectBitmapStrikeWithWork(ppemX, ppemY uint16, charge func(uint64) error) (fontBitmapSelection, bool, error) {
	if f == nil || f.metrics == nil || ppemX == 0 || ppemY == 0 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: bitmap source or request size", ErrInvalid)
	}
	if ppemX > 255 || ppemY > 255 {
		return fontBitmapSelection{}, false, nil
	}
	if err := f.loadBitmaps(charge); err != nil {
		return fontBitmapSelection{}, false, err
	}
	var work uint64
	if f.bitmaps != nil {
		work = uint64(len(f.bitmaps.strikes))
	}
	if err := fontBitmapWork(charge, work); err != nil {
		return fontBitmapSelection{}, false, err
	}
	selection, present, err := f.bitmaps.selectStrike(nil, ppemX, ppemY)
	if err != nil || present {
		return selection, present, err
	}
	scales, err := f.bitmapScale.load(f.face, charge)
	if err != nil {
		return fontBitmapSelection{}, false, err
	}
	if err := fontBitmapWork(charge, work*2); err != nil {
		return fontBitmapSelection{}, false, err
	}
	return f.bitmaps.selectStrike(scales, ppemX, ppemY)
}

// parseTrueType 解析TrueType的head、maxp、loca及glyf索引，不执行字体指令
// 入参: face 字体面，其底层数据在使用期间不得修改
// 返回: *trueTypeFont 只读轮廓访问器, error 缺表、版本或索引范围错误
func parseTrueType(face *fontFace) (*trueTypeFont, error) {
	if face == nil || face.cff {
		return nil, fmt.Errorf("%w: TrueType outlines require a TrueType face", ErrInvalid)
	}
	head, err := fontMetricsTable(face, "head", 54)
	if err != nil {
		return nil, err
	}
	if binary.BigEndian.Uint32(head)>>16 != 1 {
		return nil, fmt.Errorf("%w: TrueType head version", ErrUnsupported)
	}
	if binary.BigEndian.Uint16(head[52:]) != 0 {
		return nil, fmt.Errorf("%w: TrueType glyphDataFormat", ErrUnsupported)
	}
	format := binary.BigEndian.Uint16(head[50:])
	if format > 1 {
		return nil, fmt.Errorf("%w: TrueType indexToLocFormat", ErrInvalid)
	}
	maxp, err := fontMetricsTable(face, "maxp", 32)
	if err != nil {
		return nil, err
	}
	if binary.BigEndian.Uint32(maxp)>>16 != 1 {
		return nil, fmt.Errorf("%w: TrueType maxp version", ErrUnsupported)
	}
	count := binary.BigEndian.Uint16(maxp[4:])
	if count == 0 {
		return nil, fmt.Errorf("%w: TrueType font has no glyphs", ErrInvalid)
	}
	loca, err := fontMetricsTable(face, "loca", (int(count)+1)*(2+2*int(format)))
	if err != nil {
		return nil, err
	}
	glyf, err := face.table("glyf")
	if err != nil {
		return nil, err
	}
	f := &trueTypeFont{face: face, glyf: glyf, numGlyphs: count, locations: make([]uint32, int(count)+1)}
	for i := range f.locations {
		var offset uint32
		if format == 0 {
			offset = uint32(binary.BigEndian.Uint16(loca[2*i:])) * 2
		} else {
			offset = binary.BigEndian.Uint32(loca[4*i:])
		}
		if uint64(offset) > uint64(len(glyf)) || i > 0 && offset < f.locations[i-1] {
			return nil, fmt.Errorf("%w: invalid loca offset at index %d", ErrInvalid, i)
		}
		f.locations[i] = offset
	}
	return f, nil
}

// glyph 展开TrueType简单或复合字形，返回独立设计单位轮廓及原始声明边界
// 入参: gid 字形索引
// 返回: *trueTypeGlyph y向上的NonZero轮廓, error 结构错误或资源上限错误
func (f *trueTypeFont) glyph(gid uint16) (*trueTypeGlyph, error) {
	if f == nil || gid >= f.numGlyphs {
		return nil, fmt.Errorf("%w: TrueType glyph index %d", ErrInvalid, gid)
	}
	g, err := f.load(gid, &trueTypeBudget{})
	if err != nil {
		return nil, err
	}
	g.geometry = trueTypeGeometry(g.points, g.endPoints)
	g.instructions = append([]byte(nil), g.instructions...)
	return g, nil
}

// load 递归读取字形并保留控制点编号，所有展开过程共享资源预算
// 入参: gid 字形索引, budget 本次调用的资源预算
// 返回: *trueTypeGlyph 尚未转换几何的字形, error 结构或资源错误
func (f *trueTypeFont) load(gid uint16, budget *trueTypeBudget) (*trueTypeGlyph, error) {
	if err := budget.charge(1); err != nil {
		return nil, err
	}
	if gid >= f.numGlyphs {
		return nil, fmt.Errorf("%w: component glyph index %d", ErrInvalid, gid)
	}
	for _, ancestor := range budget.path {
		if ancestor == gid {
			return nil, fmt.Errorf("%w: cyclic TrueType component %d", ErrInvalid, gid)
		}
	}
	if len(budget.path) > trueTypeMaxDepth {
		return nil, fmt.Errorf("%w: TrueType component depth exceeds %d", ErrLimit, trueTypeMaxDepth)
	}
	budget.path = append(budget.path, gid)
	defer func() { budget.path = budget.path[:len(budget.path)-1] }()
	start, end := f.locations[int(gid)], f.locations[int(gid)+1]
	g := &trueTypeGlyph{metricsGlyph: gid, metricsPositionKnown: true}
	if start == end {
		return g, nil
	}
	r := &trueTypeCursor{data: f.glyf[start:end]}
	contours := int(int16(r.word()))
	xMin, yMin := int16(r.word()), int16(r.word())
	xMax, yMax := int16(r.word()), int16(r.word())
	if r.err != nil {
		return nil, r.err
	}
	if xMin > xMax || yMin > yMax {
		return nil, fmt.Errorf("%w: inverted glyf bounds for glyph %d", ErrInvalid, gid)
	}
	g.bounds = Rect{X: float64(xMin), Y: float64(yMin), Width: float64(int32(xMax) - int32(xMin)), Height: float64(int32(yMax) - int32(yMin))}
	g.metricsBounds = g.bounds
	var err error
	if contours >= 0 {
		err = g.readSimple(r, contours, budget)
	} else {
		err = f.readComposite(g, r, budget)
	}
	if err != nil {
		return nil, fmt.Errorf("TrueType glyph %d: %w", gid, err)
	}
	return g, nil
}

// readSimple 解码轮廓端点、重复标志及先横后竖的坐标差分
// 入参: r 字形数据读取器, contours 轮廓数, budget 资源预算
// 返回: error 结构或资源错误
func (g *trueTypeGlyph) readSimple(r *trueTypeCursor, contours int, budget *trueTypeBudget) error {
	if contours == 0 && r.pos == len(r.data) {
		return nil
	}
	endData := r.take(2 * contours)
	if r.err != nil {
		return r.err
	}
	count := 0
	for i := 0; i < contours; i++ {
		end := int(binary.BigEndian.Uint16(endData[2*i:]))
		if end < count {
			return fmt.Errorf("%w: non-increasing contour endpoints", ErrInvalid)
		}
		count = end + 1
	}
	length := int(r.word())
	g.instructions = r.take(length)
	if r.err != nil {
		return r.err
	}
	if err := budget.reserve(count, contours); err != nil {
		return err
	}
	g.endPoints = make([]int, contours)
	for i := range g.endPoints {
		g.endPoints[i] = int(binary.BigEndian.Uint16(endData[2*i:]))
	}
	flags := make([]byte, count)
	for i := 0; i < count; {
		flag := r.byte()
		repeat := 1
		if flag&8 != 0 {
			repeat += int(r.byte())
		}
		if r.err != nil {
			return r.err
		}
		if repeat > count-i {
			return fmt.Errorf("%w: repeated flags exceed point count", ErrInvalid)
		}
		for j := 0; j < repeat; j++ {
			flags[i+j] = flag
		}
		i += repeat
	}
	g.points = make([]trueTypePoint, count)
	for axis := 0; axis < 2; axis++ {
		var coordinate int64
		short, same := byte(2<<axis), byte(16<<axis)
		for i, flag := range flags {
			var delta int64
			if flag&short != 0 {
				delta = int64(r.byte())
				if flag&same == 0 {
					delta = -delta
				}
			} else if flag&same == 0 {
				delta = int64(int16(r.word()))
			}
			if r.err != nil {
				return r.err
			}
			coordinate += delta
			if axis == 0 {
				g.points[i].point.X = float64(coordinate)
			} else {
				g.points[i].point.Y = float64(coordinate)
			}
			g.points[i].onCurve = flag&1 != 0
		}
	}
	return nil
}

// readComposite 展开组件、应用线性变换并按偏移或原始编号控制点定位
// 入参: g 正在构造的父字形, r 字形数据读取器, budget 资源预算
// 返回: error 结构或资源错误
func (f *trueTypeFont) readComposite(g *trueTypeGlyph, r *trueTypeCursor, budget *trueTypeBudget) error {
	hasInstructions := false
	for {
		component := trueTypeComponent{flags: r.word(), glyph: r.word(), transform: IdentityMatrix()}
		flags := component.flags
		if flags&1 != 0 {
			component.argument1, component.argument2 = int(r.word()), int(r.word())
			if flags&2 != 0 {
				component.argument1, component.argument2 = int(int16(component.argument1)), int(int16(component.argument2))
			}
		} else {
			component.argument1, component.argument2 = int(r.byte()), int(r.byte())
			if flags&2 != 0 {
				component.argument1, component.argument2 = int(int8(component.argument1)), int(int8(component.argument2))
			}
		}
		transformFlags := flags & (8 | 64 | 128)
		if transformFlags != 0 && transformFlags&(transformFlags-1) != 0 {
			return fmt.Errorf("%w: conflicting component transform flags", ErrInvalid)
		}
		m := &component.transform
		switch transformFlags {
		case 8:
			m.A = float64(int16(r.word())) / 16384
			m.D = m.A
		case 64:
			m.A, m.D = float64(int16(r.word()))/16384, float64(int16(r.word()))/16384
		case 128:
			m.A, m.B = float64(int16(r.word()))/16384, float64(int16(r.word()))/16384
			m.C, m.D = float64(int16(r.word()))/16384, float64(int16(r.word()))/16384
		}
		if r.err != nil {
			return r.err
		}
		budget.components++
		if err := budget.charge(1); err != nil {
			return err
		}
		if budget.components > trueTypeMaxComponents {
			return fmt.Errorf("%w: TrueType component expansion exceeds %d", ErrLimit, trueTypeMaxComponents)
		}
		child, err := f.load(component.glyph, budget)
		if err != nil {
			return err
		}
		if flags&2 != 0 {
			offset := Point{X: float64(component.argument1), Y: float64(component.argument2)}
			if flags&0x1800 == 0x0800 {
				offset = m.Transform(offset)
			}
			m.E, m.F = offset.X, offset.Y
		} else {
			if len(g.components) == 0 {
				return fmt.Errorf("%w: first component requires XY placement", ErrInvalid)
			}
			if component.argument1 >= len(g.points)+4 || component.argument2 >= len(child.points)+4 {
				return fmt.Errorf("%w: component attachment point out of range", ErrInvalid)
			}
			parentPoint, err := f.attachmentPoint(g, component.argument1, budget)
			if err != nil {
				return err
			}
			childPoint, err := f.attachmentPoint(child, component.argument2, budget)
			if err != nil {
				return err
			}
			childPoint = m.Transform(childPoint)
			m.E, m.F = parentPoint.X-childPoint.X, parentPoint.Y-childPoint.Y
		}
		if err := budget.reserve(len(child.points), len(child.endPoints)); err != nil {
			return err
		}
		base := len(g.points)
		for _, point := range child.points {
			point.point = m.Transform(point.point)
			if !geometryFinite(point.point.X, point.point.Y) {
				return fmt.Errorf("%w: non-finite composite point", ErrLimit)
			}
			g.points = append(g.points, point)
		}
		for _, end := range child.endPoints {
			g.endPoints = append(g.endPoints, base+end)
		}
		if flags&0x200 != 0 {
			g.metricsGlyph = child.metricsGlyph
			g.metricsBounds = child.metricsBounds
			g.metricsPositionKnown = child.metricsPositionKnown && *m == IdentityMatrix()
		}
		g.components = append(g.components, component)
		hasInstructions = hasInstructions || flags&0x100 != 0
		if flags&0x20 == 0 {
			break
		}
	}
	if hasInstructions {
		length := int(r.word())
		g.instructions = r.take(length)
	}
	return r.err
}

// attachmentPoint 返回原始控制点编号对应的轮廓点或未hint的水平phantom附着点
// 入参: g 当前字形或部分构造的父字形, index 点号, budget 本次调用的度量解析缓存
// 返回: Point 设计单位附着点, error 结构错误或尚未支持的phantom定位
func (f *trueTypeFont) attachmentPoint(g *trueTypeGlyph, index int, budget *trueTypeBudget) (Point, error) {
	if index < 0 || index >= len(g.points)+4 {
		return Point{}, fmt.Errorf("%w: component attachment point out of range", ErrInvalid)
	}
	if index < len(g.points) {
		return g.points[index].point, nil
	}
	phantom := index - len(g.points)
	if phantom >= 2 {
		return Point{}, fmt.Errorf("%w: vertical phantom attachment position is not established", ErrUnsupported)
	}
	if !g.metricsPositionKnown {
		return Point{}, fmt.Errorf("%w: phantom attachment after transformed USE_MY_METRICS", ErrUnsupported)
	}
	if budget.metrics == nil {
		h, data, err := parseFontMetricAxis(f.face, "hhea", "hmtx", f.numGlyphs)
		if err != nil {
			return Point{}, err
		}
		budget.metrics = &fontMetrics{numGlyphs: f.numGlyphs, hhea: h, hmtx: data}
	}
	advance, bearing, err := budget.metrics.horizontal(g.metricsGlyph)
	if err != nil {
		return Point{}, err
	}
	p := Point{X: g.metricsBounds.X - float64(bearing)}
	if phantom == 1 {
		p.X += float64(advance)
	}
	return p, nil
}

// reserve 在分配及复制控制点之前扣除累计展开预算
// 入参: points 新增点处理数, contours 新增轮廓处理数
// 返回: error 实现资源上限错误
func (b *trueTypeBudget) reserve(points, contours int) error {
	if points > trueTypeMaxPoints-b.points || contours > trueTypeMaxContours-b.contours {
		return fmt.Errorf("%w: TrueType point or contour expansion budget", ErrLimit)
	}
	if err := b.charge(points + contours); err != nil {
		return err
	}
	b.points += points
	b.contours += contours
	return nil
}

// charge 在分配或展开字形数据前检查取消及可选累计工作上限，不改变原有单字形安全限制
// 入参: count 本步骤的工作单元数量
// 返回: error 取消、数量或累计预算错误
func (b *trueTypeBudget) charge(count int) error {
	if err := checkContext(b.context); err != nil {
		return err
	}
	if count < 0 {
		return fmt.Errorf("%w: negative TrueType work", ErrInvalid)
	}
	if b.workLimit != 0 {
		if count > b.workLimit-b.work {
			return fmt.Errorf("%w: TrueType cumulative glyph work", ErrLimit)
		}
		b.work += count
	}
	return nil
}

// take 返回指定长度的字形数据片段，截断时记录结构错误
// 入参: count 需要的字节数
// 返回: []byte 只读片段，错误时为nil
func (r *trueTypeCursor) take(count int) []byte {
	if r.err != nil {
		return nil
	}
	if count < 0 || count > len(r.data)-r.pos {
		r.err = fmt.Errorf("%w: truncated glyf data at byte %d", ErrInvalid, r.pos)
		return nil
	}
	data := r.data[r.pos : r.pos+count]
	r.pos += count
	return data
}

// word 读取大端无符号字，不越过当前字形边界
// 返回: uint16 数据或错误状态下的零值
func (r *trueTypeCursor) word() uint16 {
	data := r.take(2)
	if data == nil {
		return 0
	}
	return binary.BigEndian.Uint16(data)
}

// byte 读取单字节，不越过当前字形边界
// 返回: byte 数据或错误状态下的零值
func (r *trueTypeCursor) byte() byte {
	data := r.take(1)
	if data == nil {
		return 0
	}
	return data[0]
}

// trueTypeGeometry 将原始控制点转换为闭合NonZero二次路径，保留轮廓方向
// 入参: points 已定位的控制点, ends 各轮廓末点编号
// 返回: Geometry y向上的设计单位几何
func trueTypeGeometry(points []trueTypePoint, ends []int) Geometry {
	geometry, _ := trueTypeGeometryWithStep(points, ends, nil)
	return geometry
}

// trueTypeGeometryWithStep 在追加子路径和语义段前检查预算，不预先分配完整轮廓
// 入参: points 已解码控制点, ends 轮廓结束索引, step 构建检查，子路径传零、线段传一，nil不附加检查
// 返回: Geometry 完整几何，失败为零值, error 预算或取消错误
func trueTypeGeometryWithStep(points []trueTypePoint, ends []int, step func(int) error) (Geometry, error) {
	g := Geometry{FillRule: GeometryNonZero}
	begin := 0
	for _, end := range ends {
		if step != nil {
			if err := step(0); err != nil {
				return Geometry{}, err
			}
		}
		contour := points[begin : end+1]
		begin = end + 1
		first, last := contour[0], contour[len(contour)-1]
		figure := GeometryFigure{IsClosed: true, IsFilled: true}
		switch {
		case first.onCurve:
			figure.StartPoint = first.point
			contour = contour[1:]
		case last.onCurve:
			figure.StartPoint = last.point
			contour = contour[:len(contour)-1]
		default:
			figure.StartPoint = Point{X: (first.point.X + last.point.X) / 2, Y: (first.point.Y + last.point.Y) / 2}
		}
		for i := 0; i < len(contour); i++ {
			if step != nil {
				if err := step(1); err != nil {
					return Geometry{}, err
				}
			}
			p := contour[i]
			segment := GeometrySegment{Kind: GeometryLine, Point: p.point, IsStroked: true}
			if !p.onCurve {
				segment.Kind, segment.Control1 = GeometryQuadratic, p.point
				segment.Point = figure.StartPoint
				if i+1 < len(contour) {
					next := contour[i+1]
					if next.onCurve {
						segment.Point = next.point
						i++
					} else {
						segment.Point = Point{X: (p.point.X + next.point.X) / 2, Y: (p.point.Y + next.point.Y) / 2}
					}
				}
			}
			figure.Segments = append(figure.Segments, segment)
		}
		g.Figures = append(g.Figures, figure)
	}
	return g, nil
}

// fontBitmapWork 预留位图目录工作量，amount为零时仅检查取消
// 入参: charge 可选工作量回调, amount 预留工作量
// 返回: error 预算或取消错误
func fontBitmapWork(charge func(uint64) error, amount uint64) error {
	if charge != nil {
		return charge(amount)
	}
	return nil
}

// parseFontBitmapsWithWork 在目录和连续索引展开前预留工作量，不按压缩表长度估计记录数量
// 入参: face 只读字体面, numGlyphs 字形数量, charge 可选预算及取消回调
// 返回: *fontBitmaps 完整位图目录或nil, error 结构、能力、预算或取消错误
func parseFontBitmapsWithWork(face *fontFace, numGlyphs uint32, charge func(uint64) error) (*fontBitmaps, error) {
	if err := fontBitmapWork(charge, 0); err != nil {
		return nil, err
	}
	if face == nil {
		return nil, fmt.Errorf("%w: missing bitmap font face", ErrInvalid)
	}
	_, hasLocation := face.tables["EBLC"]
	_, hasData := face.tables["EBDT"]
	if !hasLocation && !hasData {
		return nil, nil
	}
	if hasLocation != hasData || numGlyphs == 0 || numGlyphs > 65536 {
		return nil, fmt.Errorf("%w: bitmap table pair or glyph count", ErrInvalid)
	}
	location, err := face.table("EBLC")
	if err != nil {
		return nil, err
	}
	data, err := face.table("EBDT")
	if err != nil {
		return nil, err
	}
	if len(location) < 8 || len(data) < 4 {
		return nil, fmt.Errorf("%w: truncated bitmap header", ErrInvalid)
	}
	if binary.BigEndian.Uint32(location) != 0x00020000 || binary.BigEndian.Uint32(data) != 0x00020000 {
		return nil, fmt.Errorf("%w: bitmap table version", ErrUnsupported)
	}
	count := uint64(binary.BigEndian.Uint32(location[4:]))
	if count > fontBitmapMaxStrikes {
		return nil, fmt.Errorf("%w: bitmap strike count", ErrLimit)
	}
	headerEnd := 8 + count*48
	if headerEnd > uint64(len(location)) {
		return nil, fmt.Errorf("%w: truncated bitmap strikes", ErrInvalid)
	}
	if err := fontBitmapWork(charge, count); err != nil {
		return nil, err
	}
	b := &fontBitmaps{data: data, strikes: make([]fontBitmapStrike, int(count))}
	remaining, subtables := fontBitmapMaxRecords, fontBitmapMaxSubtables
	for i := range b.strikes {
		if err := fontBitmapWork(charge, 0); err != nil {
			return nil, err
		}
		raw := location[8+i*48 : 8+(i+1)*48]
		s := &b.strikes[i]
		s.ppemX, s.ppemY, s.bitDepth, s.flags = raw[44], raw[45], raw[46], raw[47]
		s.startGlyph, s.endGlyph = binary.BigEndian.Uint16(raw[40:]), binary.BigEndian.Uint16(raw[42:])
		if s.startGlyph > s.endGlyph || uint32(s.endGlyph) >= numGlyphs || s.ppemX == 0 || s.ppemY == 0 || s.flags&0xfc != 0 || binary.BigEndian.Uint32(raw[12:]) != 0 {
			return nil, fmt.Errorf("%w: bitmap strike %d metadata", ErrInvalid, i)
		}
		if s.bitDepth != 1 && s.bitDepth != 2 && s.bitDepth != 4 && s.bitDepth != 8 {
			return nil, fmt.Errorf("%w: bitmap bit depth %d", ErrUnsupported, s.bitDepth)
		}
		base, size := uint64(binary.BigEndian.Uint32(raw)), uint64(binary.BigEndian.Uint32(raw[4:]))
		n := uint64(binary.BigEndian.Uint32(raw[8:]))
		if n > uint64(subtables) {
			return nil, fmt.Errorf("%w: bitmap subtable count", ErrLimit)
		}
		subtables -= int(n)
		if base < headerEnd || base%4 != 0 || base+size > uint64(len(location)) || n*8 > size {
			return nil, fmt.Errorf("%w: bitmap strike %d index range", ErrInvalid, i)
		}
		area := location[base : base+size]
		if err := fontBitmapWork(charge, n); err != nil {
			return nil, err
		}
		for j := uint64(0); j < n; j++ {
			if err := fontBitmapWork(charge, 0); err != nil {
				return nil, err
			}
			record := area[j*8 : j*8+8]
			first, last := binary.BigEndian.Uint16(record), binary.BigEndian.Uint16(record[2:])
			offset := uint64(binary.BigEndian.Uint32(record[4:]))
			if first > last || first < s.startGlyph || last > s.endGlyph || offset < n*8 || offset%4 != 0 || offset+8 > size {
				return nil, fmt.Errorf("%w: bitmap strike %d subtable range", ErrInvalid, i)
			}
			if err := s.parseIndex(area[offset:], first, last, uint64(len(data)), &remaining, charge); err != nil {
				return nil, fmt.Errorf("bitmap strike %d subtable %d: %w", i, j, err)
			}
		}
		if err := fontBitmapWork(charge, uint64(len(s.entries))*uint64(1+bits.Len(uint(len(s.entries))))); err != nil {
			return nil, err
		}
		sort.Slice(s.entries, func(a, c int) bool { return s.entries[a].gid < s.entries[c].gid })
		for j := 1; j < len(s.entries); j++ {
			if err := fontBitmapWork(charge, 0); err != nil {
				return nil, err
			}
			if s.entries[j-1].gid == s.entries[j].gid {
				return nil, fmt.Errorf("%w: duplicate bitmap glyph %d", ErrInvalid, s.entries[j].gid)
			}
		}
	}
	if err := fontBitmapWork(charge, 0); err != nil {
		return nil, err
	}
	return b, nil
}

// parseBitmapLineMetrics 读取已验证长度的十二字节行度量核心字段并跳过保留字节
// 入参: data 行度量记录
// 返回: fontBitmapLineMetrics 核心行度量
func parseBitmapLineMetrics(data []byte) fontBitmapLineMetrics {
	return fontBitmapLineMetrics{ascender: int8(data[0]), descender: int8(data[1]), widthMax: data[2]}
}

// parseBitmapBigMetrics 读取已验证长度的八字节横竖字形度量
// 入参: data 大度量记录
// 返回: fontBitmapMetrics 同时含横竖轴的原始度量
func parseBitmapBigMetrics(data []byte) fontBitmapMetrics {
	return fontBitmapMetrics{
		height: data[0], width: data[1], hasHorizontal: true, hasVertical: true,
		horizontal: fontBitmapAxisMetrics{int8(data[2]), int8(data[3]), data[4]},
		vertical:   fontBitmapAxisMetrics{int8(data[5]), int8(data[6]), data[7]},
	}
}

// parseIndex 将EBLC索引子表展开为有界位图字形记录
// 入参: data 当前strike范围内的子表数据, first 最小编号, last 最大编号, dataSize EBDT长度, remaining 剩余解析记录预算, charge 可选预算及取消回调
// 返回: error 索引结构或资源上限错误
func (s *fontBitmapStrike) parseIndex(data []byte, first, last uint16, dataSize uint64, remaining *int, charge func(uint64) error) error {
	format, imageFormat := binary.BigEndian.Uint16(data), binary.BigEndian.Uint16(data[2:])
	base := uint64(binary.BigEndian.Uint32(data[4:]))
	n := uint64(last) - uint64(first) + 1
	var stride, pos, imageSize uint64
	var fixed bool
	var metrics fontBitmapMetrics
	switch format {
	case 1:
		stride, pos = 4, 8
	case 3:
		stride, pos = 2, 8
	case 4:
		if len(data) < 12 {
			return fmt.Errorf("%w: truncated bitmap sparse index", ErrInvalid)
		}
		n, stride, pos = uint64(binary.BigEndian.Uint32(data[8:])), 4, 12
	case 2, 5:
		if len(data) < 20 {
			return fmt.Errorf("%w: truncated bitmap fixed metrics", ErrInvalid)
		}
		imageSize, fixed = uint64(binary.BigEndian.Uint32(data[8:])), true
		metrics = parseBitmapBigMetrics(data[12:20])
		pos = 20
		if format == 5 {
			if len(data) < 24 {
				return fmt.Errorf("%w: truncated bitmap fixed sparse index", ErrInvalid)
			}
			n, stride, pos = uint64(binary.BigEndian.Uint32(data[20:])), 2, 24
		}
	default:
		return fmt.Errorf("%w: bitmap index format %d", ErrUnsupported, format)
	}
	if n > uint64(*remaining) {
		return fmt.Errorf("%w: bitmap index record budget", ErrLimit)
	}
	*remaining -= int(n)
	required := pos + n*stride
	if !fixed {
		required += stride
	}
	if (required+3)&^uint64(3) > uint64(len(data)) || base < 4 || base > dataSize {
		return fmt.Errorf("%w: bitmap index or image base range", ErrInvalid)
	}
	if imageFormat == 5 && !fixed {
		return fmt.Errorf("%w: bitmap format 5 requires fixed metrics", ErrInvalid)
	}
	if err := fontBitmapWork(charge, n); err != nil {
		return err
	}
	var previous uint16
	for i := uint64(0); i < n; i++ {
		if err := fontBitmapWork(charge, 0); err != nil {
			return err
		}
		gid := uint16(uint64(first) + i)
		start, end := i*imageSize, (i+1)*imageSize
		switch format {
		case 1:
			start, end = uint64(binary.BigEndian.Uint32(data[pos+i*4:])), uint64(binary.BigEndian.Uint32(data[pos+(i+1)*4:]))
		case 3:
			start, end = uint64(binary.BigEndian.Uint16(data[pos+i*2:])), uint64(binary.BigEndian.Uint16(data[pos+(i+1)*2:]))
		case 4:
			gid = binary.BigEndian.Uint16(data[pos+i*4:])
			start, end = uint64(binary.BigEndian.Uint16(data[pos+i*4+2:])), uint64(binary.BigEndian.Uint16(data[pos+(i+1)*4+2:]))
		case 5:
			gid = binary.BigEndian.Uint16(data[pos+i*2:])
		}
		if gid < first || gid > last || i != 0 && gid <= previous || start > end || base+end > dataSize {
			return fmt.Errorf("%w: bitmap glyph %d index range or order", ErrInvalid, gid)
		}
		previous = gid
		if start == end && (format == 1 || format == 3) {
			continue
		}
		s.entries = append(s.entries, fontBitmapEntry{gid: gid, imageFormat: imageFormat, start: base + start, end: base + end, fixed: fixed, metrics: metrics})
	}
	return nil
}

// decode 展开单个字形，缓存仅包含已完成结果，循环路径不会因缓存而隐藏
// 入参: gid 字形编号
// 返回: fontBitmapDecoded 位图及度量, bool 是否存在, error 解码或资源错误
func (d *fontBitmapDecode) decode(gid uint16) (fontBitmapDecoded, bool, error) {
	if d.components == 0 || len(d.path) >= fontBitmapMaxDepth {
		return fontBitmapDecoded{}, false, fmt.Errorf("%w: bitmap component work or depth", ErrLimit)
	}
	d.components--
	if d.path[gid] {
		return fontBitmapDecoded{}, false, fmt.Errorf("%w: cyclic bitmap component %d", ErrInvalid, gid)
	}
	if cached, ok := d.cache[gid]; ok {
		return cached, true, nil
	}
	i := sort.Search(len(d.strike.entries), func(i int) bool { return d.strike.entries[i].gid >= gid })
	if i == len(d.strike.entries) || d.strike.entries[i].gid != gid {
		return fontBitmapDecoded{}, false, nil
	}
	entry := d.strike.entries[i]
	data := d.font.data[entry.start:entry.end]
	metrics, skip, err := d.strike.imageMetrics(entry, data)
	if err != nil {
		return fontBitmapDecoded{}, true, err
	}
	w, h := int(metrics.width), int(metrics.height)
	if w*h > d.pixels {
		return fontBitmapDecoded{}, true, fmt.Errorf("%w: bitmap pixel expansion", ErrLimit)
	}
	d.pixels -= w * h
	result := fontBitmapDecoded{mask: image.NewAlpha(image.Rect(0, 0, w, h)), metrics: metrics}
	d.path[gid] = true
	defer delete(d.path, gid)
	switch entry.imageFormat {
	case 1, 2, 5, 6, 7:
		err = decodeBitmapPixels(result.mask, data[skip:], d.strike.bitDepth, entry.imageFormat == 1 || entry.imageFormat == 6)
	case 8, 9:
		if len(data)-skip < 2 {
			err = fmt.Errorf("%w: truncated bitmap component count", ErrInvalid)
			break
		}
		n := int(binary.BigEndian.Uint16(data[skip:]))
		skip += 2
		if n > (len(data)-skip)/4 {
			err = fmt.Errorf("%w: truncated bitmap components", ErrInvalid)
			break
		}
		if n > d.components {
			err = fmt.Errorf("%w: bitmap component expansion", ErrLimit)
			break
		}
		for j := 0; j < n; j++ {
			raw := data[skip+j*4 : skip+j*4+4]
			child, present, childErr := d.decode(binary.BigEndian.Uint16(raw))
			if childErr != nil {
				err = childErr
				break
			}
			if !present {
				err = fmt.Errorf("%w: missing bitmap component %d", ErrInvalid, binary.BigEndian.Uint16(raw))
				break
			}
			err = d.place(result.mask, child.mask, int(int8(raw[2])), int(int8(raw[3])))
			if err != nil {
				break
			}
		}
	}
	if err != nil {
		return fontBitmapDecoded{}, true, err
	}
	d.cache[gid] = result
	return result, true, nil
}

// imageMetrics 读取位图字形图像格式的原始度量及后续数据偏移
// 入参: entry 已验证索引项, data 对应EBDT区间
// 返回: fontBitmapMetrics 原始度量, int 后续数据偏移, error 截断或能力错误
func (s *fontBitmapStrike) imageMetrics(entry fontBitmapEntry, data []byte) (fontBitmapMetrics, int, error) {
	switch entry.imageFormat {
	case 1, 2, 8:
		skip := 5
		if entry.imageFormat == 8 {
			skip = 6
		}
		if len(data) < skip {
			return fontBitmapMetrics{}, 0, fmt.Errorf("%w: truncated bitmap small metrics", ErrInvalid)
		}
		m := fontBitmapMetrics{height: data[0], width: data[1]}
		axis := fontBitmapAxisMetrics{int8(data[2]), int8(data[3]), data[4]}
		switch s.flags & 3 {
		case 1:
			m.horizontal, m.hasHorizontal = axis, true
		case 2:
			m.vertical, m.hasVertical = axis, true
		default:
			return fontBitmapMetrics{}, 0, fmt.Errorf("%w: ambiguous bitmap small-metrics direction", ErrUnsupported)
		}
		return m, skip, nil
	case 5:
		if !entry.fixed {
			return fontBitmapMetrics{}, 0, fmt.Errorf("%w: missing bitmap fixed metrics", ErrInvalid)
		}
		return entry.metrics, 0, nil
	case 6, 7, 9:
		if len(data) < 8 {
			return fontBitmapMetrics{}, 0, fmt.Errorf("%w: truncated bitmap big metrics", ErrInvalid)
		}
		return parseBitmapBigMetrics(data), 8, nil
	default:
		return fontBitmapMetrics{}, 0, fmt.Errorf("%w: bitmap image format %d", ErrUnsupported, entry.imageFormat)
	}
}

// decodeBitmapPixels 以最高有效位优先解码灰度，并按位深线性映射到Alpha覆盖值
// 入参: dst 已分配掩码, data 图像字节, depth 位深, byteAligned 是否逐行字节对齐
// 返回: error 图像截断错误
func decodeBitmapPixels(dst *image.Alpha, data []byte, depth uint8, byteAligned bool) error {
	w, h := dst.Rect.Dx(), dst.Rect.Dy()
	rowBits := w * int(depth)
	if byteAligned {
		rowBits = (rowBits + 7) &^ 7
	}
	if (rowBits*h+7)/8 > len(data) {
		return fmt.Errorf("%w: truncated bitmap pixels", ErrInvalid)
	}
	maximum := uint8((1 << depth) - 1)
	for y := 0; y < h; y++ {
		for x := 0; x < w; x++ {
			bit := y*rowBits + x*int(depth)
			value := (data[bit/8] >> uint(8-int(depth)-bit%8)) & maximum
			dst.Pix[y*dst.Stride+x] = uint8(uint16(value) * 255 / uint16(maximum))
		}
	}
	return nil
}

// place 按组件左上角偏移写入主字形掩码并裁剪越界像素，拒绝未定义的部分灰度重叠
// 入参: dst 主字形掩码, src 组件掩码, x 水平偏移, y 向下为正的竖向偏移
// 返回: error 像素工作量或灰度重叠能力错误
func (d *fontBitmapDecode) place(dst, src *image.Alpha, x, y int) error {
	r := src.Rect.Add(image.Pt(x, y)).Intersect(dst.Rect)
	if r.Dx()*r.Dy() > d.pixels {
		return fmt.Errorf("%w: bitmap component pixel work", ErrLimit)
	}
	d.pixels -= r.Dx() * r.Dy()
	for row := r.Min.Y; row < r.Max.Y; row++ {
		for col := r.Min.X; col < r.Max.X; col++ {
			a := &dst.Pix[row*dst.Stride+col]
			b := src.Pix[(row-y)*src.Stride+col-x]
			if *a != 0 && b != 0 && *a != 255 && b != 255 {
				return fmt.Errorf("%w: overlapping grayscale bitmap components", ErrUnsupported)
			}
			*a = max(*a, b)
		}
	}
	return nil
}

// parseFontBitmapScalesWithWork 在缩放目录分配前预留工作量，并在记录之间检查取消
// 入参: face 只读字体面, charge 可选预算及取消回调
// 返回: *fontBitmapScales 完整缩放目录或nil, error 结构、能力、预算或取消错误
func parseFontBitmapScalesWithWork(face *fontFace, charge func(uint64) error) (*fontBitmapScales, error) {
	if err := fontBitmapWork(charge, 0); err != nil {
		return nil, err
	}
	if face == nil {
		return nil, fmt.Errorf("%w: missing bitmap scale font face", ErrInvalid)
	}
	if _, ok := face.tables["EBSC"]; !ok {
		return nil, nil
	}
	data, err := face.table("EBSC")
	if err != nil {
		return nil, err
	}
	if len(data) < 8 {
		return nil, fmt.Errorf("%w: truncated EBSC header", ErrInvalid)
	}
	if binary.BigEndian.Uint32(data) != 0x00020000 {
		return nil, fmt.Errorf("%w: EBSC version", ErrUnsupported)
	}
	count := uint64(binary.BigEndian.Uint32(data[4:]))
	if count > fontBitmapMaxScaleRecords {
		return nil, fmt.Errorf("%w: EBSC record count", ErrLimit)
	}
	if 8+count*28 > uint64(len(data)) {
		return nil, fmt.Errorf("%w: truncated EBSC records", ErrInvalid)
	}
	if err := fontBitmapWork(charge, count); err != nil {
		return nil, err
	}
	s := &fontBitmapScales{
		records: make([]fontBitmapScale, int(count)),
		targets: make(map[[2]uint8]fontBitmapScaleTarget, int(count)),
	}
	for i := range s.records {
		if err := fontBitmapWork(charge, 0); err != nil {
			return nil, err
		}
		raw := data[8+i*28 : 8+(i+1)*28]
		r := fontBitmapScale{
			horizontal: parseBitmapLineMetrics(raw[:12]), vertical: parseBitmapLineMetrics(raw[12:24]),
			ppemX: raw[24], ppemY: raw[25], substitutePpemX: raw[26], substitutePpemY: raw[27],
		}
		if r.ppemX == 0 || r.ppemY == 0 || r.substitutePpemX == 0 || r.substitutePpemY == 0 {
			return nil, fmt.Errorf("%w: EBSC record %d zero ppem", ErrInvalid, i)
		}
		s.records[i] = r
		key := [2]uint8{r.ppemX, r.ppemY}
		if target, ok := s.targets[key]; ok {
			target.ambiguous = target.ambiguous || r != s.records[target.record]
			s.targets[key] = target
		} else {
			s.targets[key] = fontBitmapScaleTarget{record: i}
		}
	}
	return s, nil
}

// findStrike 按双轴ppem查找原序EBLC位置，不依据位深或字形覆盖率猜测优先级
// 入参: x 横轴尺寸, y 竖轴尺寸
// 返回: int 首个匹配位置或负一, int 匹配数量
func (b *fontBitmaps) findStrike(x, y uint8) (int, int) {
	index, count := -1, 0
	if b != nil {
		for i, s := range b.strikes {
			if s.ppemX == x && s.ppemY == y {
				if count == 0 {
					index = i
				}
				count++
			}
		}
	}
	return index, count
}

// selectStrike 按精确EBLC优先、精确目标EBSC次之的顺序选择位图strike，冲突时返回ErrUnsupported
// 入参: scales 已解析的EBSC或nil, ppemX 正横轴请求尺寸, ppemY 正竖轴请求尺寸
// 返回: fontBitmapSelection 选择结果, bool 是否存在匹配, error 请求、引用或选择能力错误
func (b *fontBitmaps) selectStrike(scales *fontBitmapScales, ppemX, ppemY uint16) (fontBitmapSelection, bool, error) {
	if ppemX == 0 || ppemY == 0 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: bitmap request requires positive ppem", ErrInvalid)
	}
	if ppemX > 255 || ppemY > 255 {
		return fontBitmapSelection{}, false, nil
	}
	x, y := uint8(ppemX), uint8(ppemY)
	index, count := b.findStrike(x, y)
	if count == 0 {
		if scales == nil {
			return fontBitmapSelection{}, false, nil
		}
		target, ok := scales.targets[[2]uint8{x, y}]
		if !ok {
			return fontBitmapSelection{}, false, nil
		}
		if target.ambiguous {
			return fontBitmapSelection{}, false, fmt.Errorf("%w: conflicting EBSC target %dx%d", ErrUnsupported, x, y)
		}
		record := target.record
		r := scales.records[record]
		index, count = b.findStrike(r.substitutePpemX, r.substitutePpemY)
		if count == 0 {
			return fontBitmapSelection{}, false, fmt.Errorf("%w: EBSC record %d source strike %dx%d is missing", ErrInvalid, record, r.substitutePpemX, r.substitutePpemY)
		}
	}
	if count > 1 {
		return fontBitmapSelection{}, false, fmt.Errorf("%w: bitmap request %dx%d matches %d source strikes", ErrUnsupported, x, y, count)
	}
	source := b.strikes[index]
	selection := fontBitmapSelection{
		strike: index, ppemX: x, ppemY: y,
		scaleX: float64(x) / float64(source.ppemX), scaleY: float64(y) / float64(source.ppemY),
	}
	return selection, true, nil
}
