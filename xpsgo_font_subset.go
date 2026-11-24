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
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"maps"
	"math"
	"math/bits"
	"slices"
	"strings"
)

// FontSubsetOptions 设置集合字体面索引、输入输出字节上限及字形解析工作上限
// MaxWork累计TrueType轮廓展开、CFF程序执行及替换程序字节，零值采用1048576个工作单元
type FontSubsetOptions struct {
	CollectionIndex uint32
	MaxBytes        int64
	MaxWork         int
}

// subsetCFFPrivate 保存重定位后的私有字典与未重编号的局部子程序索引
type subsetCFFPrivate struct {
	size int
	data []byte
}

// fontSubsetFaceKey 区分原始字体目录和保留编号，重复字体面复用已重定位的候选目录
type fontSubsetFaceKey struct {
	directory string
	glyphs    string
}

// fontCollectionTableKey 用表标识及摘要查找共享候选，共享前仍比较完整字节
type fontCollectionTableKey struct {
	tag    [4]byte
	digest [32]byte
	length uint32
}

// fontCollectionBuilder 逐面构造TTC1.0并共享相同表，仅持有输出数据和目录索引
type fontCollectionBuilder struct {
	data    []byte
	tables  map[fontCollectionTableKey][]uint32
	maximum int64
	count   uint32
	context context.Context
}

// subsetFontAxis 累计有轮廓字形的侧承和最大延伸量，不改变各字形的步进
type subsetFontAxis struct {
	leading  int
	trailing int
	extent   int
	present  bool
}

// subsetFontProfile 累计裁剪后全局边界和字形存储需求，保留原编号以记录组件深度
type subsetFontProfile struct {
	bounds       [4]int
	present      bool
	horizontal   subsetFontAxis
	vertical     subsetFontAxis
	simple       [2]int
	composite    [2]int
	instructions int
	elements     int
	children     map[uint16][]uint16
}

// DefaultFontSubsetOptions 返回默认字体裁剪选项
// 返回: FontSubsetOptions 默认单字体裁剪配置
func DefaultFontSubsetOptions() FontSubsetOptions {
	return FontSubsetOptions{MaxBytes: DefaultLimits().MaxPartBytes, MaxWork: 1 << 20}
}

// SubsetFont 裁剪已解混淆的TrueType或CFF1字体，保留原字形编号、.notdef、复合依赖与排版度量并返回独立SFNT
// 集合输入仅输出指定字体面并移除失效的DSIG，受嵌入或子集化限制时返回ErrRestricted
// 入参: ctx 取消Context，nil采用Background, data 原始字体数据，调用期间不得修改, glyphs 保留的原字形编号, options 资源上限参数
// 返回: []byte 独立字体数据，失败为nil, error 封装、许可、能力、字形、资源或取消错误
func SubsetFont(ctx context.Context, data []byte, glyphs []uint16, options *FontSubsetOptions) ([]byte, error) {
	return subsetFont(normalizeContext(ctx), data, glyphs, options, nil)
}

// subsetFontConfig 规范化字体裁剪预算参数并结合累计剩余工作上限约束单次上限
// 入参: options 单字体选项, remaining 可选累计剩余工作量
// 返回: FontSubsetOptions 规范化配置, error 参数或累计工作预算错误
func subsetFontConfig(options *FontSubsetOptions, remaining *int) (FontSubsetOptions, error) {
	configuration := DefaultFontSubsetOptions()
	if options != nil {
		configuration.CollectionIndex = options.CollectionIndex
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxWork != 0 {
			configuration.MaxWork = options.MaxWork
		}
	}
	if configuration.MaxBytes < 1 || configuration.MaxWork < 1 {
		return configuration, fmt.Errorf("%w: font subset limits", ErrInvalid)
	}
	if remaining != nil {
		if *remaining < 1 {
			return configuration, fmt.Errorf("%w: font subset cumulative work budget", ErrLimit)
		}
		configuration.MaxWork = min(configuration.MaxWork, *remaining)
	}
	return configuration, nil
}

// subsetFont 共用单字体裁剪入口，可将执行工作计入包级累计预算
// 入参: ctx 已规范化取消Context, data 字体数据, glyphs 保留编号, options 单字体选项, remaining 可选累计剩余工作量
// 返回: []byte 独立字体数据, error 字体、资源或取消错误
func subsetFont(ctx context.Context, data []byte, glyphs []uint16, options *FontSubsetOptions, remaining *int) ([]byte, error) {
	configuration, err := subsetFontConfig(options, remaining)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
		return nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
	}
	face, err := parseFontFace(data, configuration.CollectionIndex)
	if err != nil {
		return nil, err
	}
	if issues := face.validateDirectory(); len(issues) != 0 {
		return nil, fmt.Errorf("%w: font subset directory %s: %s", ErrInvalid, issues[0].table, issues[0].message)
	}
	return subsetFontFace(ctx, face, glyphs, configuration, remaining)
}

// subsetFontFace 对已完成目录与校验和验证的字体面执行权限检查、元数据校验与轮廓子集化
// 入参: ctx 已规范化取消Context, face 已校验字体面, glyphs 保留编号, configuration 已规范化选项, remaining 累计工作预算
// 返回: []byte 独立字体数据, error 字体、许可、预算或取消错误
func subsetFontFace(ctx context.Context, face *fontFace, glyphs []uint16, configuration FontSubsetOptions, remaining *int) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	os2, err := parseFontOS2Metrics(face)
	if err != nil {
		return nil, err
	}
	rights, err := fontEmbeddingRights(os2)
	if err != nil {
		return nil, err
	}
	if rights&0x302 != 0 {
		return nil, fmt.Errorf("%w: font embedding or subsetting restriction", ErrRestricted)
	}
	for _, tag := range []string{"fvar", "COLR", "SVG "} {
		if _, present := face.tables[tag]; present {
			return nil, fmt.Errorf("%w: font subset dependencies in %s", ErrUnsupported, tag)
		}
	}
	fontMetrics, err := validateCreatedFontMetrics(face, os2)
	if err != nil {
		return nil, err
	}
	if face.cff {
		return subsetCFFFont(ctx, face, fontMetrics, glyphs, configuration, remaining)
	}
	if _, present := face.tables["gvar"]; present {
		return nil, fmt.Errorf("%w: variable TrueType font subsetting", ErrUnsupported)
	}
	font, err := parseTrueType(face)
	if err != nil {
		return nil, err
	}
	needed := make([]bool, int(font.numGlyphs))
	queue := make([]uint16, 0, min(int(font.numGlyphs), len(glyphs)+1))
	needed[0] = true
	queue = append(queue, 0)
	for _, gid := range glyphs {
		if gid >= font.numGlyphs {
			return nil, fmt.Errorf("%w: subset glyph index %d", ErrInvalid, gid)
		}
		if !needed[gid] {
			needed[gid] = true
			queue = append(queue, gid)
		}
	}
	budget := &trueTypeBudget{context: ctx, workLimit: configuration.MaxWork}
	if remaining != nil {
		defer func() { *remaining -= budget.work }()
	}
	profile := subsetFontProfile{}
	for index := 0; index < len(queue); index++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		gid := queue[index]
		glyph, err := font.load(gid, budget)
		if err != nil {
			return nil, err
		}
		budget.points, budget.contours, budget.components = 0, 0, 0
		start, end := font.locations[gid], font.locations[int(gid)+1]
		composite := start != end && int16(binary.BigEndian.Uint16(font.glyf[start:])) < 0
		if err := profile.add(gid, glyph, fontMetrics, composite); err != nil {
			return nil, err
		}
		for _, component := range glyph.components {
			if !needed[component.glyph] {
				needed[component.glyph] = true
				queue = append(queue, component.glyph)
			}
		}
	}
	head, _ := face.table("head")
	short := binary.BigEndian.Uint16(head[50:]) == 0
	offsets := make([]uint32, int(font.numGlyphs)+1)
	var glyf []byte
	for index := 0; index <= int(font.numGlyphs); index++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		offsets[index] = uint32(len(glyf))
		if index == int(font.numGlyphs) || !needed[index] {
			continue
		}
		start, end := font.locations[index], font.locations[index+1]
		length := uint64(end-start) + uint64((int(end-start))&1)
		if uint64(len(glyf))+length > uint64(configuration.MaxBytes) || uint64(len(glyf))+length > math.MaxUint32 {
			return nil, fmt.Errorf("%w: subset glyph byte budget", ErrLimit)
		}
		glyf = append(glyf, font.glyf[start:end]...)
		if len(glyf)&1 != 0 {
			glyf = append(glyf, 0)
		}
	}
	if short {
		for _, offset := range offsets {
			if offset&1 != 0 || offset > 131070 {
				short = false
				break
			}
		}
	}
	stride := 4
	if short {
		stride = 2
	}
	if uint64(len(offsets))*uint64(stride) > uint64(configuration.MaxBytes) {
		return nil, fmt.Errorf("%w: subset loca byte budget", ErrLimit)
	}
	loca := make([]byte, len(offsets)*stride)
	for index, offset := range offsets {
		if short {
			binary.BigEndian.PutUint16(loca[index*stride:], uint16(offset/2))
		} else {
			binary.BigEndian.PutUint32(loca[index*stride:], offset)
		}
	}
	tables := map[string][]byte{"glyf": glyf, "loca": loca}
	if err := profile.apply(face, fontMetrics, tables, ctx); err != nil {
		return nil, err
	}
	if !short {
		binary.BigEndian.PutUint16(tables["head"][50:], 1)
	}
	return encodeSubsetFont(ctx, face, tables, slices.Contains(needed, false), configuration)
}

// encodeSubsetFont 重建独立SFNT目录及四字节表填充，剔除失效签名及与被置空字形不一致的衍生表
// 入参: ctx 取消Context, face 原字体面, replacements 替换的字体表, pruned 是否置空了未用轮廓字形, options 字节上限
// 返回: []byte 独立字体数据, error 表、字节、目录或取消错误
func encodeSubsetFont(ctx context.Context, face *fontFace, replacements map[string][]byte, pruned bool, options FontSubsetOptions) ([]byte, error) {
	tags := slices.Sorted(maps.Keys(face.tables))
	tags = slices.DeleteFunc(tags, func(tag string) bool {
		if tag == "DSIG" {
			return true
		}
		if !pruned {
			return false
		}
		switch tag {
		case "hdmx", "LTSH", "VDMX", "EBLC", "EBDT", "EBSC", "CBDT", "CBLC", "sbix":
			return true
		}
		return false
	})
	count := len(tags)
	if count == 0 || count > 4095 {
		return nil, fmt.Errorf("%w: subset table directory range", ErrLimit)
	}
	total := uint64(12 + count*16)
	for _, tag := range tags {
		length := uint64(face.tables[tag].length)
		if replacement, present := replacements[tag]; present {
			length = uint64(len(replacement))
		}
		total += (length + 3) &^ uint64(3)
		if total > uint64(options.MaxBytes) || total > uint64(int(^uint(0)>>1)) || total > uint64(^uint32(0)) {
			return nil, fmt.Errorf("%w: subset font output budget", ErrLimit)
		}
	}
	output := make([]byte, int(total))
	binary.BigEndian.PutUint32(output, binary.BigEndian.Uint32(face.data[face.offset:]))
	binary.BigEndian.PutUint16(output[4:], uint16(count))
	selector := bits.Len(uint(count)) - 1
	search := 16 << selector
	binary.BigEndian.PutUint16(output[6:], uint16(search))
	binary.BigEndian.PutUint16(output[8:], uint16(selector))
	binary.BigEndian.PutUint16(output[10:], uint16(count*16-search))
	position, headOffset := 12+count*16, -1
	for index, tag := range tags {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		data, present := replacements[tag]
		if !present {
			var err error
			data, err = face.table(tag)
			if err != nil {
				return nil, err
			}
		}
		copy(output[position:], data)
		if tag == "head" {
			if len(data) < 54 {
				return nil, fmt.Errorf("%w: subset head table", ErrInvalid)
			}
			headOffset = position
			clear(output[position+8 : position+12])
		}
		record := output[12+index*16 : 12+(index+1)*16]
		copy(record, tag)
		binary.BigEndian.PutUint32(record[4:], fontChecksum(output[position:position+len(data)]))
		binary.BigEndian.PutUint32(record[8:], uint32(position))
		binary.BigEndian.PutUint32(record[12:], uint32(len(data)))
		position += (len(data) + 3) &^ 3
	}
	if headOffset < 0 {
		return nil, fmt.Errorf("%w: missing subset head", ErrInvalid)
	}
	binary.BigEndian.PutUint32(output[headOffset+8:], 0xb1b0afba-fontChecksum(output))
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return output, nil
}

// subsetCFFFont 保留原GID与子程序编号并重建CFF1字体子集表，未用字形按原度量生成空程序
// 入参: ctx 已规范化取消Context, face 原SFNT字体面, metrics 已校验字体度量, glyphs 保留字形编号, options 资源上限, work 可选包级剩余工作量
// 返回: []byte 独立SFNT, error 字形、结构、矩阵、预算或取消错误
func subsetCFFFont(ctx context.Context, face *fontFace, metrics *fontMetrics, glyphs []uint16, options FontSubsetOptions, work *int) ([]byte, error) {
	data, err := face.table("CFF ")
	if err != nil {
		if _, exists := face.tables["CFF2"]; exists {
			return nil, fmt.Errorf("%w: CFF2 font subsetting", ErrUnsupported)
		}
		return nil, err
	}
	set, err := parseCFFSet(data)
	if err != nil {
		return nil, err
	}
	if len(set.names) != 1 {
		return nil, fmt.Errorf("%w: OpenType CFF FontSet count", ErrInvalid)
	}
	font, err := parseCFFFont(set, 0)
	if err != nil {
		return nil, err
	}
	if font.charstringType != 2 || font.paintType != 0 {
		return nil, fmt.Errorf("%w: subset CFF outline representation", ErrUnsupported)
	}
	if len(font.charstrings) != int(metrics.numGlyphs) {
		return nil, fmt.Errorf("%w: subset CFF and maxp glyph count", ErrInvalid)
	}
	needed := make([]bool, len(font.charstrings))
	needed[0] = true
	queue := []uint16{0}
	for _, gid := range glyphs {
		if int(gid) >= len(needed) {
			return nil, fmt.Errorf("%w: subset CFF glyph index", ErrInvalid)
		}
		if !needed[gid] {
			needed[gid] = true
			queue = append(queue, gid)
		}
	}
	remaining := options.MaxWork
	if work != nil {
		defer func() { *work -= options.MaxWork - remaining }()
	}
	selected := make(map[uint16]*type2Glyph)
	for index := 0; index < len(queue); index++ {
		gid := queue[index]
		glyph, err := subsetCFFGlyph(ctx, font, gid, &remaining)
		if err != nil {
			return nil, err
		}
		selected[gid] = glyph
		if glyph.seac != nil {
			if font.cid {
				return nil, fmt.Errorf("%w: CID subset CFF seac", ErrInvalid)
			}
			for _, code := range []byte{glyph.seac.base, glyph.seac.accent} {
				sid := cffStandardSID(code)
				component, present := font.charset.glyph(sid)
				if sid == 0 || !present {
					return nil, fmt.Errorf("%w: missing subset CFF seac component", ErrInvalid)
				}
				if !needed[component] {
					needed[component] = true
					queue = append(queue, component)
				}
			}
		}
	}
	programs := make([][]byte, len(font.charstrings))
	for index, original := range font.charstrings {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if needed[index] {
			programs[index] = original
			continue
		}
		if remaining == 0 {
			return nil, fmt.Errorf("%w: CFF subset replacement work", ErrLimit)
		}
		width, _, err := metrics.horizontal(uint16(index))
		if err != nil {
			return nil, err
		}
		charWidth, hasWidth := subsetCFFEmptyWidth(font, uint16(index), width, metrics.unitsPerEm)
		programs[index] = subsetCFFEmptyGlyph(charWidth, hasWidth, subsetCFFGlyphPrivate(font, uint16(index)))
		if len(programs[index]) > remaining {
			return nil, fmt.Errorf("%w: CFF subset replacement work", ErrLimit)
		}
		remaining -= len(programs[index])
	}
	profile := subsetFontProfile{}
	var cffBounds [4]int64
	hasCFFBounds := false
	for _, gid := range queue {
		geometry := subsetCFFCloneGeometry(selected[gid].geometry)
		if seac := selected[gid].seac; seac != nil {
			for index, code := range []byte{seac.base, seac.accent} {
				component, _ := font.charset.glyph(cffStandardSID(code))
				child := selected[component]
				if child.seac != nil {
					return nil, fmt.Errorf("%w: nested subset CFF seac", ErrInvalid)
				}
				part := subsetCFFCloneGeometry(child.geometry)
				if index == 1 {
					if err := cffTranslateGlyph(&part, seac.offset); err != nil {
						return nil, err
					}
				}
				geometry.Figures = append(geometry.Figures, part.Figures...)
			}
		}
		geometry.Figures = slices.DeleteFunc(geometry.Figures, func(figure GeometryFigure) bool { return len(figure.Segments) == 0 })
		hasOutline := len(geometry.Figures) != 0
		if hasOutline && !font.cid {
			cb, err := geometry.Bounds()
			if err != nil {
				return nil, err
			}
			cxMin, cyMin := math.Floor(cb.X), math.Floor(cb.Y)
			cxMax, cyMax := math.Ceil(cb.X+cb.Width), math.Ceil(cb.Y+cb.Height)
			if cxMin < math.MinInt32 || cyMin < math.MinInt32 || cxMax > math.MaxInt32 || cyMax > math.MaxInt32 {
				return nil, fmt.Errorf("%w: subset CFF FontBBox range", ErrLimit)
			}
			box := [4]int64{int64(cxMin), int64(cyMin), int64(cxMax), int64(cyMax)}
			if !hasCFFBounds {
				cffBounds, hasCFFBounds = box, true
			} else {
				cffBounds[0], cffBounds[1] = min(cffBounds[0], box[0]), min(cffBounds[1], box[1])
				cffBounds[2], cffBounds[3] = max(cffBounds[2], box[2]), max(cffBounds[3], box[3])
			}
		}
		matrix, err := font.designMatrix(gid, metrics.unitsPerEm)
		if err != nil {
			return nil, err
		}
		if err := fontTransformOutline(&geometry, matrix); err != nil {
			return nil, err
		}
		bounds, err := geometry.Bounds()
		if err != nil {
			return nil, err
		}
		xMin, yMin := math.Floor(bounds.X), math.Floor(bounds.Y)
		xMax, yMax := math.Ceil(bounds.X+bounds.Width), math.Ceil(bounds.Y+bounds.Height)
		if xMin < -32768 || yMin < -32768 || xMax > 32767 || yMax > 32767 {
			return nil, fmt.Errorf("%w: subset CFF bounds outside FWORD", ErrInvalid)
		}
		if hasOutline && font.cid {
			box := [4]int64{int64(xMin), int64(yMin), int64(xMax), int64(yMax)}
			if !hasCFFBounds {
				cffBounds, hasCFFBounds = box, true
			} else {
				cffBounds[0], cffBounds[1] = min(cffBounds[0], box[0]), min(cffBounds[1], box[1])
				cffBounds[2], cffBounds[3] = max(cffBounds[2], box[2]), max(cffBounds[3], box[3])
			}
		}
		bounds = Rect{X: xMin, Y: yMin, Width: xMax - xMin, Height: yMax - yMin}
		if err := profile.addBounds(gid, bounds, hasOutline, metrics); err != nil {
			return nil, err
		}
	}
	encoded, err := encodeSubsetCFFWithBBox(ctx, font, programs, cffBounds[:], options)
	if err != nil {
		return nil, err
	}
	tables := map[string][]byte{"CFF ": encoded}
	if err := profile.apply(face, metrics, tables, ctx); err != nil {
		return nil, err
	}
	return encodeSubsetFont(ctx, face, tables, slices.Contains(needed, false), options)
}

// subsetCFFGlyph 按原字体字典执行单个字形，共用累计操作预算和取消Context
// 入参: ctx 取消Context, font 原CFF字体, gid 原GID, remaining 剩余工作预算
// 返回: *type2Glyph 原始字形及宽度, error 程序、预算或取消错误
func subsetCFFGlyph(ctx context.Context, font *cffFont, gid uint16, remaining *int) (*type2Glyph, error) {
	private := subsetCFFGlyphPrivate(font, gid)
	return parseType2(font.charstrings[gid], type2Context{globalSubr: font.set.globalSubr, localSubr: private.localSubr, defaultWidth: private.defaultWidth, nominalWidth: private.nominalWidth, randomSeed: private.randomSeed, context: ctx, work: remaining})
}

// subsetCFFGlyphPrivate 按原FDSelect选择宽度及局部子程序，不把FD索引改写为字体集合索引
// 入参: font 原CFF字体, gid 已验证的原GID
// 返回: cffPrivate 字形私有字典
func subsetCFFGlyphPrivate(font *cffFont, gid uint16) cffPrivate {
	if font.cid {
		return font.fontDict[font.fdSelect[gid]].private
	}
	return font.top.private
}

// subsetCFFCloneGeometry 复制字形曲线，矩阵和组合平移不会修改其他字形共享的轮廓
// 入参: source 字形几何
// 返回: Geometry 独立曲线数据
func subsetCFFCloneGeometry(source Geometry) Geometry {
	result := source
	result.Figures = slices.Clone(source.Figures)
	for index := range result.Figures {
		result.Figures[index].Segments = slices.Clone(result.Figures[index].Segments)
	}
	return result
}

// subsetCFFEmptyWidth 按字体矩阵将hmtx水平步进宽换算为CFF字形空间宽度
// 入参: font 原CFF字体, gid 字形编号, advance hmtx水平步进宽, unitsPerEm SFNT每em设计单位数
// 返回: float64 字形空间宽度, bool 是否可逆换算
func subsetCFFEmptyWidth(font *cffFont, gid, advance, unitsPerEm uint16) (float64, bool) {
	if font.top.matrix == nil && (!font.cid || font.fontDict[font.fdSelect[gid]].matrix == nil) {
		if unitsPerEm == 1000 {
			return float64(advance), true
		}
		width := float64(advance) * 1000 / float64(unitsPerEm)
		return width, geometryFinite(width)
	}
	matrix, err := font.designMatrix(gid, unitsPerEm)
	if err != nil || matrix.A == 0 || matrix.B != 0 {
		return 0, false
	}
	width := float64(advance) / matrix.A
	return width, geometryFinite(width)
}

// subsetCFFEmptyGlyph 生成无轮廓Type2程序，无法简洁表达宽度时省略宽度以依赖hmtx
// 入参: width 字形空间宽度, hasWidth 是否具备有效换算宽度, private 原私有字典的宽度参数
// 返回: []byte 空字形程序
func subsetCFFEmptyGlyph(width float64, hasWidth bool, private cffPrivate) []byte {
	if !hasWidth || width == private.defaultWidth {
		return []byte{14}
	}
	delta := width - private.nominalWidth
	if !geometryFinite(delta) || delta+private.nominalWidth != width {
		return []byte{14}
	}
	if delta == math.Trunc(delta) && delta >= -32768 && delta <= 32767 {
		return append(subsetType2Integer(int(delta)), 14)
	}
	fixed := delta * 65536
	if fixed == math.Trunc(fixed) && fixed >= math.MinInt32 && fixed <= math.MaxInt32 {
		return append(binary.BigEndian.AppendUint32([]byte{255}, uint32(int32(fixed))), 14)
	}
	return []byte{14}
}

// subsetType2Integer 编码已限定为有符号十六位的Type2整数
// 入参: value 范围已验证的整数
// 返回: []byte Type2操作数
func subsetType2Integer(value int) []byte {
	switch {
	case value >= -107 && value <= 107:
		return []byte{byte(value + 139)}
	case value >= 108 && value <= 1131:
		value -= 108
		return []byte{byte(value/256 + 247), byte(value)}
	case value <= -108 && value >= -1131:
		value = -value - 108
		return []byte{byte(value/256 + 251), byte(value)}
	default:
		return binary.BigEndian.AppendUint16([]byte{28}, uint16(int16(value)))
	}
}

// encodeSubsetCFFIndex 编码CFF1索引，按最大偏移选择宽度，不改写对象内容或编号
// 入参: objects 对象字节, maximum 输出字节上限
// 返回: []byte 索引数据, error 数量、偏移或字节预算错误
func encodeSubsetCFFIndex(objects [][]byte, maximum int64) ([]byte, error) {
	if len(objects) > 65535 {
		return nil, fmt.Errorf("%w: subset CFF INDEX count", ErrLimit)
	}
	if len(objects) == 0 {
		if maximum < 2 {
			return nil, fmt.Errorf("%w: subset CFF INDEX budget", ErrLimit)
		}
		return []byte{0, 0}, nil
	}
	length := uint64(1)
	for _, object := range objects {
		length += uint64(len(object))
		if length > math.MaxUint32 {
			return nil, fmt.Errorf("%w: subset CFF INDEX offset", ErrLimit)
		}
	}
	width := 1
	for width < 4 && length >= uint64(1)<<uint(width*8) {
		width++
	}
	total := uint64(3+(len(objects)+1)*width) + length - 1
	if maximum < 0 || total > uint64(maximum) || total > uint64(int(^uint(0)>>1)) {
		return nil, fmt.Errorf("%w: subset CFF INDEX byte budget", ErrLimit)
	}
	data := make([]byte, int(total))
	binary.BigEndian.PutUint16(data, uint16(len(objects)))
	data[2] = byte(width)
	position, offset := 3+(len(objects)+1)*width, uint32(1)
	for index := 0; index <= len(objects); index++ {
		for byteIndex := 0; byteIndex < width; byteIndex++ {
			data[3+index*width+byteIndex] = byte(offset >> uint(8*(width-byteIndex-1)))
		}
		if index < len(objects) {
			copy(data[position:], objects[index])
			position += len(objects[index])
			offset += uint32(len(objects[index]))
		}
	}
	return data, nil
}

// patchSubsetCFFDict 按固定宽度整数替换指定CFF字典条目并保持其余条目原字节不变
// 入参: original 原字典, values 替换或补入的整数条目, maximum 输出字节上限
// 返回: []byte 字典数据, error 原字典、整数范围或字节预算错误
func patchSubsetCFFDict(original []byte, values map[uint16][]int64, maximum int64) ([]byte, error) {
	if _, err := parseCFFDict(original); err != nil {
		return nil, err
	}
	var output []byte
	seen := make(map[uint16]bool)
	start := 0
	for position := 0; position < len(original); {
		code := original[position]
		if code > 21 {
			_, next, err := cffNumber(original, position)
			if err != nil {
				return nil, err
			}
			position = next
			continue
		}
		operator := uint16(code)
		position++
		if code == 12 {
			operator = 0x0c00 | uint16(original[position])
			position++
		}
		entry := original[start:position]
		if operands, replace := values[operator]; replace {
			var err error
			entry, err = subsetCFFEntry(operator, operands)
			if err != nil {
				return nil, err
			}
			seen[operator] = true
		}
		if int64(len(entry)) > maximum-int64(len(output)) {
			return nil, fmt.Errorf("%w: subset CFF DICT budget", ErrLimit)
		}
		output = append(output, entry...)
		start = position
	}
	var missing []uint16
	for operator := range values {
		if !seen[operator] {
			missing = append(missing, operator)
		}
	}
	slices.Sort(missing)
	for _, operator := range missing {
		entry, err := subsetCFFEntry(operator, values[operator])
		if err != nil {
			return nil, err
		}
		if int64(len(entry)) > maximum-int64(len(output)) {
			return nil, fmt.Errorf("%w: subset CFF DICT budget", ErrLimit)
		}
		output = append(output, entry...)
	}
	return output, nil
}

// subsetCFFEntry 编码一个固定宽度整数字典条目，不把DICT整数编码用于Type2字形
// 入参: operator 字典操作符, values 有符号整数操作数
// 返回: []byte 字典条目, error 操作数范围错误
func subsetCFFEntry(operator uint16, values []int64) ([]byte, error) {
	var data []byte
	for _, value := range values {
		if value < math.MinInt32 || value > math.MaxInt32 {
			return nil, fmt.Errorf("%w: subset CFF DICT integer range", ErrLimit)
		}
		data = append(data, 29)
		data = binary.BigEndian.AppendUint32(data, uint32(int32(value)))
	}
	if operator > 255 {
		data = append(data, byte(operator>>8))
	}
	return append(data, byte(operator)), nil
}

// encodeSubsetCFFWithBBox 重建CFF1表并在提供字符空间包围盒时同步更新Top DICT的FontBBox
// 入参: ctx 取消Context, font 原CFF字体, programs 按原GID排列的新字形程序, fontBBox 可选四元组FontBBox, options 字节上限
// 返回: []byte 独立CFF表, error 字典、布局、范围或取消错误
func encodeSubsetCFFWithBBox(ctx context.Context, font *cffFont, programs [][]byte, fontBBox []int64, options FontSubsetOptions) ([]byte, error) {
	maximum := min(options.MaxBytes, int64(math.MaxInt32))
	set := font.set
	_, afterName, err := parseCFFIndex(set.data, uint32(set.data[2]))
	if err != nil {
		return nil, err
	}
	topObjects, _, err := parseCFFIndex(set.data, afterName)
	if err != nil || len(topObjects) != 1 {
		return nil, fmt.Errorf("%w: OpenType CFF must have one Top DICT", ErrInvalid)
	}
	privateFonts := []cffFontDict{font.top}
	var dictionaries [][]byte
	if font.cid {
		privateFonts = font.fontDict
		offset, err := cffRequiredOffset(font.top.dict, 0x0c24)
		if err != nil {
			return nil, err
		}
		dictionaries, _, err = parseCFFIndex(set.data, offset)
		if err != nil {
			return nil, err
		}
	}
	privates := make([]subsetCFFPrivate, len(privateFonts))
	privateKeys := make([][2]uint32, len(privateFonts))
	privateCache := make(map[[2]uint32]subsetCFFPrivate)
	privateBytes := int64(0)
	for index, fd := range privateFonts {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		values, _ := fd.dict.value(18)
		for field := range privateKeys[index] {
			value, err := cffInteger(values[field:field+1], 0, math.MaxInt32)
			if err != nil {
				return nil, err
			}
			privateKeys[index][field] = uint32(value)
		}
		if cached, present := privateCache[privateKeys[index]]; present {
			privates[index] = cached
			continue
		}
		privates[index], err = buildSubsetCFFPrivate(set.data, fd, maximum-privateBytes)
		if err != nil {
			return nil, err
		}
		privateBytes += int64(len(privates[index].data))
		privateCache[privateKeys[index]] = privates[index]
	}
	encoding, customEncoding, err := subsetCFFEncoding(font)
	if err != nil {
		return nil, err
	}
	values := map[uint16][]int64{15: {0}, 17: {0}}
	if len(fontBBox) == 4 {
		values[5] = fontBBox
	}
	if font.cid {
		values[0x0c24], values[0x0c25] = []int64{0}, []int64{0}
	} else {
		values[18] = []int64{int64(privates[0].size), 0}
		if customEncoding {
			values[16] = []int64{0}
		}
	}
	top, err := patchSubsetCFFDict(topObjects[0], values, maximum)
	if err != nil {
		return nil, err
	}
	coreObjects := [][][]byte{set.names, {top}, set.strings, set.globalSubr}
	output := bytes.Clone(set.data[:set.data[2]])
	output[3] = 4
	put := func(data []byte) (int64, error) {
		if err := checkContext(ctx); err != nil {
			return 0, err
		}
		if int64(len(data)) > maximum-int64(len(output)) {
			return 0, fmt.Errorf("%w: subset CFF table byte budget", ErrLimit)
		}
		position := int64(len(output))
		output = append(output, data...)
		return position, nil
	}
	var topPosition, topLength int
	for index, objects := range coreObjects {
		data, err := encodeSubsetCFFIndex(objects, maximum)
		if err != nil {
			return nil, err
		}
		position, err := put(data)
		if err != nil {
			return nil, err
		}
		if index == 1 {
			topPosition, topLength = int(position), len(data)
		}
	}
	var charset []byte
	if font.cid {
		charset = encodeSubsetCFFCharsetFormat2(font.charset.values)
	} else {
		charset = make([]byte, 1, 1+2*(len(font.charset.values)-1))
		for _, value := range font.charset.values[1:] {
			charset = binary.BigEndian.AppendUint16(charset, value)
		}
	}
	position, err := put(charset)
	if err != nil {
		return nil, err
	}
	values[15][0] = position
	if customEncoding {
		position, err := put(encoding)
		if err != nil {
			return nil, err
		}
		values[16][0] = position
	}
	chars, err := encodeSubsetCFFIndex(programs, maximum)
	if err != nil {
		return nil, err
	}
	position, err = put(chars)
	if err != nil {
		return nil, err
	}
	values[17][0] = position
	var fdPosition, fdLength int
	if font.cid {
		position, err := put(encodeSubsetCFFFDSelectFormat3(font.fdSelect))
		if err != nil {
			return nil, err
		}
		values[0x0c25][0] = position
		for index, dictionary := range dictionaries {
			dictionaries[index], err = patchSubsetCFFDict(dictionary, map[uint16][]int64{18: {int64(privates[index].size), 0}}, maximum)
			if err != nil {
				return nil, err
			}
		}
		data, err := encodeSubsetCFFIndex(dictionaries, maximum)
		if err != nil {
			return nil, err
		}
		position, err = put(data)
		if err != nil {
			return nil, err
		}
		values[0x0c24][0] = position
		fdPosition, fdLength = int(position), len(data)
	}
	privatePositions := make(map[[2]uint32]int64)
	for index, private := range privates {
		position, present := privatePositions[privateKeys[index]]
		if !present {
			var err error
			position, err = put(private.data)
			if err != nil {
				return nil, err
			}
			privatePositions[privateKeys[index]] = position
		}
		if font.cid {
			dictionaries[index], err = patchSubsetCFFDict(dictionaries[index], map[uint16][]int64{18: {int64(private.size), position}}, maximum)
			if err != nil {
				return nil, err
			}
		} else {
			values[18][1] = position
		}
	}
	if font.cid {
		data, err := encodeSubsetCFFIndex(dictionaries, maximum)
		if err != nil {
			return nil, err
		}
		if len(data) != fdLength {
			return nil, fmt.Errorf("%w: unstable subset CFF FDArray layout", ErrInvalid)
		}
		copy(output[fdPosition:fdPosition+fdLength], data)
	}
	top, err = patchSubsetCFFDict(topObjects[0], values, maximum)
	if err != nil {
		return nil, err
	}
	data, err := encodeSubsetCFFIndex([][]byte{top}, maximum)
	if err != nil {
		return nil, err
	}
	if len(data) != topLength {
		return nil, fmt.Errorf("%w: unstable subset CFF Top DICT layout", ErrInvalid)
	}
	copy(output[topPosition:topPosition+topLength], data)
	return output, checkContext(ctx)
}

// encodeSubsetCFFCharsetFormat2 按连续区间编码紧凑的CFF Format 2字符集表
// 入参: values 包含隐式.notdef在内的GID到CID或SID映射
// 返回: []byte Format 2字符集字节
func encodeSubsetCFFCharsetFormat2(values []uint16) []byte {
	out := []byte{2}
	for i := 1; i < len(values); {
		first := values[i]
		nLeft := 0
		for i+1+nLeft < len(values) && nLeft < 65535 && uint32(values[i+1+nLeft]) == uint32(first)+uint32(nLeft)+1 {
			nLeft++
		}
		out = binary.BigEndian.AppendUint16(out, first)
		out = binary.BigEndian.AppendUint16(out, uint16(nLeft))
		i += nLeft + 1
	}
	return out
}

// encodeSubsetCFFFDSelectFormat3 按连续相同字典索引编码紧凑的CFF Format 3选择表
// 入参: fdSelect 按GID排列的字体字典索引
// 返回: []byte Format 3选择表字节
func encodeSubsetCFFFDSelectFormat3(fdSelect []uint8) []byte {
	out := []byte{3, 0, 0}
	ranges := 0
	for gid := 0; gid < len(fdSelect); {
		fd := fdSelect[gid]
		start := gid
		for gid < len(fdSelect) && fdSelect[gid] == fd {
			gid++
		}
		out = binary.BigEndian.AppendUint16(out, uint16(start))
		out = append(out, fd)
		ranges++
	}
	binary.BigEndian.PutUint16(out[1:], uint16(ranges))
	return binary.BigEndian.AppendUint16(out, uint16(len(fdSelect)))
}

// buildSubsetCFFPrivate 重建局部Subrs相对偏移，子程序内容与编号不变，不复制原布局中的无关间隔
// 入参: source 原CFF表, fd 原字体字典, maximum 字节上限
// 返回: subsetCFFPrivate 私有字典及子程序, error 范围或字节预算错误
func buildSubsetCFFPrivate(source []byte, fd cffFontDict, maximum int64) (subsetCFFPrivate, error) {
	values, present := fd.dict.value(18)
	if !present || len(values) != 2 {
		return subsetCFFPrivate{}, fmt.Errorf("%w: subset CFF Private range", ErrInvalid)
	}
	size, err := cffInteger(values[:1], 0, math.MaxInt32)
	if err != nil {
		return subsetCFFPrivate{}, err
	}
	offset, err := cffInteger(values[1:], 0, math.MaxInt32)
	if err != nil || offset+size > int64(len(source)) {
		return subsetCFFPrivate{}, fmt.Errorf("%w: subset CFF Private bounds", ErrInvalid)
	}
	original := source[offset : offset+size]
	if int64(len(original)) > maximum {
		return subsetCFFPrivate{}, fmt.Errorf("%w: subset CFF Private byte budget", ErrLimit)
	}
	if _, present := fd.private.dict.value(19); !present {
		return subsetCFFPrivate{size: len(original), data: original}, nil
	}
	dict, err := patchSubsetCFFDict(original, map[uint16][]int64{19: {0}}, maximum)
	if err != nil {
		return subsetCFFPrivate{}, err
	}
	dict, err = patchSubsetCFFDict(original, map[uint16][]int64{19: {int64(len(dict))}}, maximum)
	if err != nil {
		return subsetCFFPrivate{}, err
	}
	subrs, err := encodeSubsetCFFIndex(fd.private.localSubr, maximum-int64(len(dict)))
	if err != nil {
		return subsetCFFPrivate{}, err
	}
	return subsetCFFPrivate{size: len(dict), data: append(dict, subrs...)}, nil
}

// subsetCFFEncoding 保留预定义编码编号或已验证的显式编码数据，不重排主映射及补充映射
// 入参: font 原CFF字体
// 返回: []byte 显式编码数据, bool 是否需要重定位, error 编码或映射错误
func subsetCFFEncoding(font *cffFont) ([]byte, bool, error) {
	if font.cid {
		return nil, false, nil
	}
	offset, err := cffOptionalOffset(font.top.dict, 16)
	if err != nil || offset <= 1 {
		return nil, false, err
	}
	_, data, err := parseCFFEncodingRecord(font.set.data, offset, font.charset)
	return data, true, err
}

// subsetFontResourceFace 复用已解析首字体面裁剪单字体或集合资源，避免重复解析字体面及校验和
// 入参: ctx 已规范化取消Context, firstFace 已解析的零号字体面, usage 各字体面使用编号, options 字节上限参数, work 包级剩余工作预算
// 返回: []byte 独立字体资源, error 字体、集合、预算或取消错误
func subsetFontResourceFace(ctx context.Context, firstFace *fontFace, usage map[uint32][]uint16, options FontSubsetOptions, work *int) ([]byte, error) {
	data := firstFace.data
	if !firstFace.collection {
		configuration, err := subsetFontConfig(&options, work)
		if err != nil {
			return nil, err
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		glyphs := usage[0]
		if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
			return nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
		}
		if issues := firstFace.validateDirectory(); len(issues) != 0 {
			return nil, fmt.Errorf("%w: font subset directory %s: %s", ErrInvalid, issues[0].table, issues[0].message)
		}
		return subsetFontFace(ctx, firstFace, glyphs, configuration, work)
	}
	if int64(len(data)) > options.MaxBytes {
		return nil, fmt.Errorf("%w: collection subset input byte budget", ErrLimit)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	count := binary.BigEndian.Uint32(data[8:])
	builder, err := newFontCollectionBuilder(count, options.MaxBytes, ctx)
	if err != nil {
		return nil, err
	}
	checksums := newFontChecksums(data, 3*uint64(len(data)))
	cached := make(map[fontSubsetFaceKey][]byte)
	remaining := options.MaxWork
	if work == nil {
		work = &remaining
	}
	for index := uint32(0); index < count; index++ {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		face := firstFace
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return nil, err
			}
		}
		if issues := face.validateDirectoryChecksums(checksums); len(issues) != 0 {
			return nil, fmt.Errorf("%w: collection source face %d %s: %s", ErrInvalid, index, issues[0].table, issues[0].message)
		}
		glyphs := usage[index]
		charge := 1 + len(face.tables) + len(glyphs)
		if charge > *work {
			return nil, fmt.Errorf("%w: collection subset directory budget", ErrLimit)
		}
		*work -= charge
		glyphs = slices.Clone(glyphs)
		slices.Sort(glyphs)
		glyphs = slices.Compact(glyphs)
		if len(glyphs) != 0 && glyphs[0] == 0 {
			glyphs = glyphs[1:]
		}
		encodedGlyphs := make([]byte, 2*len(glyphs))
		for i, gid := range glyphs {
			binary.BigEndian.PutUint16(encodedGlyphs[i*2:], gid)
		}
		key := fontSubsetFaceKey{directory: string(data[face.offset : uint64(face.offset)+uint64(12+len(face.tables)*16)]), glyphs: string(encodedGlyphs)}
		if header, present := cached[key]; present {
			if err := builder.directory(index, header); err != nil {
				return nil, err
			}
			continue
		}
		options.CollectionIndex = index
		configuration, err := subsetFontConfig(&options, work)
		if err != nil {
			return nil, err
		}
		if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
			return nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
		}
		font, err := subsetFontFace(ctx, face, glyphs, configuration, work)
		if err != nil {
			return nil, err
		}
		header, err := builder.face(index, font)
		if err != nil {
			return nil, err
		}
		cached[key] = header
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return builder.data, nil
}

// newFontCollectionBuilder 在字节和地址上限内建立集合头，不复制字体数据
// 入参: count 字体面数量, maximum 字节上限, ctx 取消Context
// 返回: *fontCollectionBuilder 集合构造器, error 数量、预算或取消错误
func newFontCollectionBuilder(count uint32, maximum int64, ctx context.Context) (*fontCollectionBuilder, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if count == 0 {
		return nil, fmt.Errorf("%w: empty font collection", ErrInvalid)
	}
	maximum = min(maximum, int64(math.MaxUint32), int64(int(^uint(0)>>1)))
	header := uint64(12) + uint64(count)*4
	if maximum < 0 || header > uint64(maximum) {
		return nil, fmt.Errorf("%w: collection header byte budget", ErrLimit)
	}
	b := &fontCollectionBuilder{data: make([]byte, int(header)), tables: make(map[fontCollectionTableKey][]uint32), maximum: maximum, count: count, context: ctx}
	copy(b.data, "ttcf")
	binary.BigEndian.PutUint32(b.data[4:], 0x10000)
	binary.BigEndian.PutUint32(b.data[8:], count)
	return b, nil
}

// put 写入一个四字节对齐的数据块，预算不足时不扩张缓冲
// 入参: data 数据块
// 返回: uint32 集合内地址, error 字节预算或取消错误
func (b *fontCollectionBuilder) put(data []byte) (uint32, error) {
	if err := checkContext(b.context); err != nil {
		return 0, err
	}
	size := (uint64(len(data)) + 3) &^ uint64(3)
	if size > uint64(b.maximum-int64(len(b.data))) {
		return 0, fmt.Errorf("%w: collection table byte budget", ErrLimit)
	}
	position := uint32(len(b.data))
	b.data = append(b.data, data...)
	for padding := size - uint64(len(data)); padding != 0; padding-- {
		b.data = append(b.data, 0)
	}
	return position, nil
}

// table 写入或复用内容完全相同的表，head的校验调整值按集合规则归零
// 入参: tag 表标识, data 原表数据
// 返回: uint32 表地址, uint32 表校验和, error 结构、预算或取消错误
func (b *fontCollectionBuilder) table(tag string, data []byte) (uint32, uint32, error) {
	if err := checkContext(b.context); err != nil {
		return 0, 0, err
	}
	if uint64(len(data)) > math.MaxUint32 || int64(len(data)) > b.maximum {
		return 0, 0, fmt.Errorf("%w: collection table size", ErrLimit)
	}
	if tag == "head" {
		if len(data) < 54 {
			return 0, 0, fmt.Errorf("%w: collection head table", ErrInvalid)
		}
		data = bytes.Clone(data)
		clear(data[8:12])
	}
	key := fontCollectionTableKey{digest: sha256.Sum256(data), length: uint32(len(data))}
	copy(key.tag[:], tag)
	for _, offset := range b.tables[key] {
		if bytes.Equal(data, b.data[uint64(offset):uint64(offset)+uint64(len(data))]) {
			return offset, fontChecksum(data), nil
		}
	}
	position, err := b.put(data)
	if err != nil {
		return 0, 0, err
	}
	b.tables[key] = append(b.tables[key], position)
	return position, fontChecksum(data), nil
}

// directory 写入已重定位的独立目录副本，供相同字体面和字形集合复用
// 入参: index 原字体面序号, header 已重定位的目录
// 返回: error 序号、预算或取消错误
func (b *fontCollectionBuilder) directory(index uint32, header []byte) error {
	if index >= b.count {
		return fmt.Errorf("%w: collection directory index", ErrInvalid)
	}
	position, err := b.put(header)
	if err != nil {
		return err
	}
	binary.BigEndian.PutUint32(b.data[12+index*4:], position)
	return nil
}

// face 校验独立SFNT并重定位全部表记录，不保留修改后失效的字体签名
// 入参: index 原字体面序号, font 已裁剪的独立字体
// 返回: []byte 可复用的重定位目录, error 字体、序号、预算或取消错误
func (b *fontCollectionBuilder) face(index uint32, font []byte) ([]byte, error) {
	if err := checkContext(b.context); err != nil {
		return nil, err
	}
	face, err := parseFontFace(font, 0)
	if err != nil {
		return nil, err
	}
	if face.collection || index >= b.count {
		return nil, fmt.Errorf("%w: collection source or face index", ErrInvalid)
	}
	if issues := face.validateDirectory(); len(issues) != 0 {
		return nil, fmt.Errorf("%w: collection source %s: %s", ErrInvalid, issues[0].table, issues[0].message)
	}
	if _, present := face.tables["DSIG"]; present {
		return nil, fmt.Errorf("%w: collection source retains font signature", ErrInvalid)
	}
	headerLength := 12 + 16*len(face.tables)
	position, err := b.put(font[:headerLength])
	if err != nil {
		return nil, err
	}
	binary.BigEndian.PutUint32(b.data[12+index*4:], position)
	for record := 12; record < headerLength; record += 16 {
		tag := string(font[record : record+4])
		data, err := face.table(tag)
		if err != nil {
			return nil, err
		}
		offset, checksum, err := b.table(tag, data)
		if err != nil {
			return nil, err
		}
		binary.BigEndian.PutUint32(b.data[int(position)+record+4:], checksum)
		binary.BigEndian.PutUint32(b.data[int(position)+record+8:], offset)
	}
	return bytes.Clone(b.data[int(position) : int(position)+headerLength]), nil
}

// add 按保留轮廓及原度量更新全局字形信息，不用未保留字形扩大边界
// 入参: gid 原字形编号, glyph 已验证的展开字形, metrics 原度量, composite 是否为复合记录
// 返回: error 度量读取错误
func (p *subsetFontProfile) add(gid uint16, glyph *trueTypeGlyph, metrics *fontMetrics, composite bool) error {
	points, contours := len(glyph.points), len(glyph.endPoints)
	maximum := &p.simple
	if composite {
		maximum = &p.composite
	}
	maximum[0], maximum[1] = max(maximum[0], points), max(maximum[1], contours)
	p.instructions = max(p.instructions, len(glyph.instructions))
	p.elements = max(p.elements, len(glyph.components))
	if p.children == nil {
		p.children = make(map[uint16][]uint16)
	}
	for _, component := range glyph.components {
		p.children[gid] = append(p.children[gid], component.glyph)
	}
	return p.addBounds(gid, glyph.bounds, contours != 0, metrics)
}

// addBounds 汇总有轮廓字形的设计单位边界及横竖度量，用于两类轮廓共享的全局统计
// 入参: gid 原字形编号, box 字形设计单位边界, nonempty 是否有轮廓, metrics 原度量
// 返回: error 度量读取错误
func (p *subsetFontProfile) addBounds(gid uint16, box Rect, nonempty bool, metrics *fontMetrics) error {
	if !nonempty {
		return nil
	}
	bounds := [4]int{int(box.X), int(box.Y), int(box.X + box.Width), int(box.Y + box.Height)}
	if !p.present {
		p.bounds, p.present = bounds, true
	} else {
		p.bounds[0], p.bounds[1] = min(p.bounds[0], bounds[0]), min(p.bounds[1], bounds[1])
		p.bounds[2], p.bounds[3] = max(p.bounds[2], bounds[2]), max(p.bounds[3], bounds[3])
	}
	advance, bearing, err := metrics.horizontal(gid)
	if err != nil {
		return err
	}
	p.horizontal.add(int(advance), int(bearing), int(box.Width))
	if metrics.vhea != nil {
		advance, bearing, err := metrics.vertical(gid)
		if err != nil {
			return err
		}
		p.vertical.add(int(advance), int(bearing), int(box.Height))
	}
	return nil
}

// add 累计非空轮廓的前后侧承及延伸量
// 入参: advance 步进, bearing 前侧承, span 轮廓跨度
func (a *subsetFontAxis) add(advance, bearing, span int) {
	trailing, extent := advance-bearing-span, bearing+span
	if !a.present {
		a.leading, a.trailing, a.extent, a.present = bearing, trailing, extent, true
		return
	}
	a.leading, a.trailing, a.extent = min(a.leading, bearing), min(a.trailing, trailing), max(a.extent, extent)
}

// apply 写入裁剪后的全局边界、轮廓需求和度量极值，不改写排版基线或时间元数据
// 入参: face 原字体面, metrics 保留的字形度量, tables 替换表集合, ctx 取消Context
// 返回: error 表读取或字段范围错误
func (p *subsetFontProfile) apply(face *fontFace, metrics *fontMetrics, tables map[string][]byte, ctx context.Context) error {
	for _, tag := range []string{"head", "maxp", "hhea", "vhea"} {
		if tag == "vhea" {
			if _, present := face.tables[tag]; !present {
				continue
			}
		}
		data, err := face.table(tag)
		if err != nil {
			return err
		}
		tables[tag] = bytes.Clone(data)
	}
	for _, axis := range []struct {
		tag     string
		data    []byte
		records uint16
	}{{"hhea", metrics.hmtx, metrics.hhea.longMetrics}, {"vhea", metrics.vmtx, 0}} {
		table := tables[axis.tag]
		if table == nil {
			continue
		}
		if axis.tag == "vhea" {
			axis.records = metrics.vhea.longMetrics
		}
		var maximum uint16
		for index := 0; index < int(axis.records); index++ {
			if err := checkContext(ctx); err != nil {
				return err
			}
			maximum = max(maximum, binary.BigEndian.Uint16(axis.data[index*4:]))
		}
		binary.BigEndian.PutUint16(table[10:], maximum)
	}
	for index, value := range p.bounds {
		binary.BigEndian.PutUint16(tables["head"][36+index*2:], uint16(int16(value)))
	}
	depths := make(map[uint16]int)
	var depth func(uint16) int
	depth = func(gid uint16) int {
		if value, present := depths[gid]; present {
			return value
		}
		maximum := 0
		for _, child := range p.children[gid] {
			maximum = max(maximum, 1+depth(child))
		}
		depths[gid] = maximum
		return maximum
	}
	maximumDepth := 0
	for gid := range p.children {
		maximumDepth = max(maximumDepth, depth(gid))
	}
	for _, field := range []struct{ offset, value int }{{6, p.simple[0]}, {8, p.simple[1]}, {10, p.composite[0]}, {12, p.composite[1]}, {26, p.instructions}, {28, p.elements}, {30, maximumDepth}} {
		if face.cff {
			break
		}
		if field.value > 65535 {
			return fmt.Errorf("%w: subset maxp field", ErrLimit)
		}
		binary.BigEndian.PutUint16(tables["maxp"][field.offset:], uint16(field.value))
	}
	if err := p.horizontal.apply(tables["hhea"]); err != nil {
		return err
	}
	if table := tables["vhea"]; table != nil {
		return p.vertical.apply(table)
	}
	return nil
}

// apply 写入有符号侧承和延伸字段，拒绝溢出而不截断或钳位字体度量
// 入参: table 已验证的hhea或vhea副本
// 返回: error 字段不能由FWORD表示
func (a *subsetFontAxis) apply(table []byte) error {
	for index, value := range []int{a.leading, a.trailing, a.extent} {
		if value < -32768 || value > 32767 {
			return fmt.Errorf("%w: subset metric extent outside FWORD", ErrInvalid)
		}
		binary.BigEndian.PutUint16(table[12+index*2:], uint16(int16(value)))
	}
	return nil
}

// SubsetFonts 汇总包内字体使用并裁剪资源，保持URI、集合索引、混淆密钥、GID与度量不变且仅提交更小候选
// 不绕过字体许可且不自动重签，失败不修改包；不支持或X3D关联字体原样保留并以ErrUnsupported记入结果
// 入参: ctx 取消Context，nil采用Background, options 字节及累计工作参数，nil采用默认值
// 返回: []ResourceOptimization 按部件名排列的资源结果，失败为nil, error 使用汇总、字体、预算或取消错误
func (p *Package) SubsetFonts(ctx context.Context, options *OptimizationOptions) ([]ResourceOptimization, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	configuration := OptimizationOptions{MaxBytes: p.limits.MaxPartBytes, MaxWork: 1 << 20}
	if options != nil {
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxWork != 0 {
			configuration.MaxWork = options.MaxWork
		}
	}
	if configuration.MaxBytes < 1 || configuration.MaxWork < 1 {
		return nil, fmt.Errorf("%w: package font optimization limits", ErrInvalid)
	}
	reader, err := p.reader(ctx)
	if err != nil {
		return nil, err
	}
	defer reader.Close()
	budget := resourceMergeBudget{bytes: reader.limits.MaxPackageBytes, work: reader.limits.MaxXMLNodes, seen: make(map[string]bool), context: ctx}
	models, err := reader.hasResourceModels(&budget)
	if err != nil {
		return nil, err
	}
	if models {
		if _, err := reader.resourceReferenceGraph(&budget); err != nil {
			return nil, err
		}
		if err := budget.charge(len(p.parts)); err != nil {
			return nil, err
		}
		var result []ResourceOptimization
		for _, key := range slices.Sorted(maps.Keys(p.parts)) {
			if err := budget.charge(1); err != nil {
				return nil, err
			}
			part := p.parts[key]
			if requiredResourceMedia(requiredFont, part.media) {
				size := int64(len(part.data))
				result = append(result, ResourceOptimization{Part: part.name, OriginalBytes: size, Bytes: size, Err: fmt.Errorf("%w: font usage depends on opaque X3D content", ErrUnsupported)})
			}
		}
		return result, checkContext(ctx)
	}
	usage, err := reader.FontUsage(ctx, nil)
	if err != nil {
		return nil, err
	}
	groups := make(map[string]map[uint32][]uint16)
	for _, font := range usage {
		key := strings.ToLower(font.Part)
		if groups[key] == nil {
			groups[key] = make(map[uint32][]uint16)
		}
		groups[key][font.CollectionIndex] = font.Glyphs
	}
	pending := make(map[string]packagePart)
	var result []ResourceOptimization
	remaining := configuration.MaxWork
	for _, key := range slices.Sorted(maps.Keys(groups)) {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		part := p.parts[key]
		entry := ResourceOptimization{Part: part.name, OriginalBytes: int64(len(part.data)), Bytes: int64(len(part.data))}
		if err := p.editable(part.name); err != nil {
			entry.Err = err
			result = append(result, entry)
			continue
		}
		face, err := reader.pkg.readFontFaceLimit(part.name, 0, configuration.MaxBytes)
		if err != nil {
			return nil, err
		}
		encoded, err := subsetFontResourceFace(ctx, face, groups[key], FontSubsetOptions{MaxBytes: configuration.MaxBytes, MaxWork: configuration.MaxWork}, &remaining)
		if err != nil {
			if !errors.Is(err, ErrUnsupported) && !errors.Is(err, ErrRestricted) {
				return nil, &PartError{Part: part.name, Err: err}
			}
			entry.Err = err
			result = append(result, entry)
			continue
		}
		if int64(len(encoded)) < entry.OriginalBytes {
			if strings.EqualFold(part.media, "application/vnd.ms-package.obfuscated-opentype") {
				encoded, err = ObfuscateFont(part.name, encoded)
				if err != nil {
					return nil, err
				}
			}
			entry.Bytes, entry.Changed = int64(len(encoded)), true
			pending[key] = packagePart{name: part.name, media: part.media, data: encoded}
		}
		result = append(result, entry)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	for key, value := range pending {
		p.total -= int64(len(p.parts[key].data)) - int64(len(value.data))
		p.parts[key], p.dirty[key] = value, true
	}
	return result, nil
}
