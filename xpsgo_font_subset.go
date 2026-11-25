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
	"encoding/xml"
	"errors"
	"fmt"
	"maps"
	"math"
	"math/bits"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

// FontSubsetOptions 设置集合字体面索引、输入输出字节上限、字形解析工作上限、紧凑重映射与合成cmap配置
// MaxWork累计TrueType轮廓展开、CFF程序执行及替换程序字节，零值采用1048576个工作单元
type FontSubsetOptions struct {
	CollectionIndex  uint32
	MaxBytes         int64
	MaxWork          int
	AllowMissingCmap bool
	CompactGIDs      bool
	SynthesizeCmap   map[rune]uint16
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

// SubsetFont 裁剪已解混淆的TrueType或CFF1字体，保留.notdef、复合依赖与排版度量并返回独立SFNT
// 集合输入仅输出指定字体面并移除失效的DSIG，受嵌入或子集化限制时返回ErrRestricted
// 入参: ctx 取消Context，nil采用Background, data 原始字体数据，调用期间不得修改, glyphs 保留的原字形编号, options 资源上限参数
// 返回: []byte 独立字体数据，失败为nil, error 封装、许可、能力、字形、资源或取消错误
func SubsetFont(ctx context.Context, data []byte, glyphs []uint16, options *FontSubsetOptions) ([]byte, error) {
	return subsetFont(normalizeContext(ctx), data, glyphs, options, nil)
}

// SubsetFontMapped 裁剪已解混淆的TrueType或CFF1字体并返回旧GID到新GID的映射表
// 启用CompactGIDs时将保留字形按升序紧凑重编号为0至N-1并重写轮廓、度量与cmap表，否则返回恒等映射
// 入参: ctx 取消Context，nil采用Background, data 原始字体数据，调用期间不得修改, collectionIndex 集合字体面索引, glyphIDs 保留的原字形编号, options 裁剪选项
// 返回: []byte 独立字体数据, map[uint16]uint16 旧GID到新GID映射表, error 封装、许可、能力、字形、资源或取消错误
func SubsetFontMapped(ctx context.Context, data []byte, collectionIndex int, glyphIDs []uint16, options FontSubsetOptions) (encoded []byte, gidMap map[uint16]uint16, err error) {
	if collectionIndex < 0 || uint64(collectionIndex) > math.MaxUint32 {
		return nil, nil, fmt.Errorf("%w: negative or overflowing collection index", ErrInvalid)
	}
	options.CollectionIndex = uint32(collectionIndex)
	return subsetFontMapped(normalizeContext(ctx), data, glyphIDs, &options, nil)
}

// subsetFontConfig 规范化字体裁剪预算参数并结合累计剩余工作上限约束单次上限
// 入参: options 单字体选项, remaining 可选累计剩余工作量
// 返回: FontSubsetOptions 规范化配置, error 参数或累计工作预算错误
func subsetFontConfig(options *FontSubsetOptions, remaining *int) (FontSubsetOptions, error) {
	configuration := DefaultFontSubsetOptions()
	if options != nil {
		configuration.CollectionIndex = options.CollectionIndex
		configuration.AllowMissingCmap = options.AllowMissingCmap
		configuration.CompactGIDs = options.CompactGIDs
		configuration.SynthesizeCmap = options.SynthesizeCmap
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
	encoded, _, err := subsetFontMapped(ctx, data, glyphs, options, remaining)
	return encoded, err
}

// subsetFontMapped 共用单字体裁剪入口，可将执行工作计入包级累计预算并返回旧GID到新GID映射
// 入参: ctx 已规范化取消Context, data 字体数据, glyphs 保留编号, options 单字体选项, remaining 可选累计剩余工作量
// 返回: []byte 独立字体数据, map[uint16]uint16 旧GID到新GID映射表, error 字体、资源或取消错误
func subsetFontMapped(ctx context.Context, data []byte, glyphs []uint16, options *FontSubsetOptions, remaining *int) ([]byte, map[uint16]uint16, error) {
	configuration, err := subsetFontConfig(options, remaining)
	if err != nil {
		return nil, nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
		return nil, nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
	}
	face, err := parseFontFace(data, configuration.CollectionIndex)
	if err != nil {
		return nil, nil, err
	}
	if issues := face.validateDirectory(); len(issues) != 0 {
		return nil, nil, fmt.Errorf("%w: font subset directory %s: %s", ErrInvalid, issues[0].table, issues[0].message)
	}
	return subsetFontFace(ctx, face, glyphs, configuration, remaining)
}

// subsetFontFace 对已完成目录与校验和验证的字体面执行权限检查、元数据校验与轮廓子集化
// 入参: ctx 已规范化取消Context, face 已校验字体面, glyphs 保留编号, configuration 已规范化选项, remaining 累计工作预算
// 返回: []byte 独立字体数据, map[uint16]uint16 旧GID到新GID映射表, error 字体、许可、预算或取消错误
func subsetFontFace(ctx context.Context, face *fontFace, glyphs []uint16, configuration FontSubsetOptions, remaining *int) ([]byte, map[uint16]uint16, error) {
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	var os2 *fontOS2Metrics
	if _, hasOS2 := face.tables["OS/2"]; hasOS2 || !fontIsBitmapOnly(face) && !configuration.AllowMissingCmap {
		var err error
		os2, err = parseFontOS2Metrics(face)
		if err != nil {
			return nil, nil, err
		}
		rights, err := fontEmbeddingRights(os2)
		if err != nil {
			return nil, nil, err
		}
		if rights&0x302 != 0 {
			return nil, nil, fmt.Errorf("%w: font embedding or subsetting restriction", ErrRestricted)
		}
	}
	if fontIsBitmapOnly(face) {
		return nil, nil, fmt.Errorf("%w: bitmap-only font subsetting", ErrUnsupported)
	}
	for _, tag := range []string{"fvar", "COLR", "SVG "} {
		if _, present := face.tables[tag]; present {
			return nil, nil, fmt.Errorf("%w: font subset dependencies in %s", ErrUnsupported, tag)
		}
	}
	fontMetrics, err := validateFontSubsetMetrics(face, os2, configuration.AllowMissingCmap)
	if err != nil {
		return nil, nil, err
	}
	if face.cff {
		return subsetCFFFont(ctx, face, fontMetrics, glyphs, configuration, remaining)
	}
	if _, present := face.tables["gvar"]; present {
		return nil, nil, fmt.Errorf("%w: variable TrueType font subsetting", ErrUnsupported)
	}
	font, err := parseTrueType(face)
	if err != nil {
		return nil, nil, err
	}
	needed := make([]bool, int(font.numGlyphs))
	queue := make([]uint16, 0, min(int(font.numGlyphs), len(glyphs)+1))
	needed[0] = true
	queue = append(queue, 0)
	for _, gid := range glyphs {
		if gid >= font.numGlyphs {
			return nil, nil, fmt.Errorf("%w: subset glyph index %d", ErrInvalid, gid)
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
			return nil, nil, err
		}
		gid := queue[index]
		glyph, err := font.load(gid, budget)
		if err != nil {
			return nil, nil, err
		}
		budget.points, budget.contours, budget.components = 0, 0, 0
		start, end := font.locations[gid], font.locations[int(gid)+1]
		composite := start != end && int16(binary.BigEndian.Uint16(font.glyf[start:])) < 0
		if err := profile.add(gid, glyph, fontMetrics, composite); err != nil {
			return nil, nil, err
		}
		for _, component := range glyph.components {
			if !needed[component.glyph] {
				needed[component.glyph] = true
				queue = append(queue, component.glyph)
			}
		}
	}
	oldToNew, newToOld := buildSubsetGIDMap(needed, configuration.CompactGIDs)
	head, _ := face.table("head")
	short := binary.BigEndian.Uint16(head[50:]) == 0
	var offsets []uint32
	var glyf []byte
	if configuration.CompactGIDs {
		offsets = make([]uint32, len(newToOld)+1)
		for newGID, oldGID := range newToOld {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			offsets[newGID] = uint32(len(glyf))
			start, end := font.locations[oldGID], font.locations[int(oldGID)+1]
			if start == end {
				continue
			}
			length := uint64(end-start) + uint64((int(end-start))&1)
			if uint64(len(glyf))+length > uint64(configuration.MaxBytes) || uint64(len(glyf))+length > math.MaxUint32 {
				return nil, nil, fmt.Errorf("%w: subset glyph byte budget", ErrLimit)
			}
			raw := bytes.Clone(font.glyf[start:end])
			if len(raw) >= 10 && int16(binary.BigEndian.Uint16(raw)) < 0 {
				if err := rewriteCompositeGlyphIDs(raw, oldToNew); err != nil {
					return nil, nil, err
				}
			}
			glyf = append(glyf, raw...)
			if len(glyf)&1 != 0 {
				glyf = append(glyf, 0)
			}
		}
		offsets[len(newToOld)] = uint32(len(glyf))
	} else {
		offsets = make([]uint32, int(font.numGlyphs)+1)
		for index := 0; index <= int(font.numGlyphs); index++ {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			offsets[index] = uint32(len(glyf))
			if index == int(font.numGlyphs) || !needed[index] {
				continue
			}
			start, end := font.locations[index], font.locations[index+1]
			length := uint64(end-start) + uint64((int(end-start))&1)
			if uint64(len(glyf))+length > uint64(configuration.MaxBytes) || uint64(len(glyf))+length > math.MaxUint32 {
				return nil, nil, fmt.Errorf("%w: subset glyph byte budget", ErrLimit)
			}
			glyf = append(glyf, font.glyf[start:end]...)
			if len(glyf)&1 != 0 {
				glyf = append(glyf, 0)
			}
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
		return nil, nil, fmt.Errorf("%w: subset loca byte budget", ErrLimit)
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
		return nil, nil, err
	}
	if configuration.CompactGIDs {
		if err := applyCompactSubsetTables(face, fontMetrics, newToOld, oldToNew, tables); err != nil {
			return nil, nil, err
		}
	}
	if cmapTable, err := buildSubsetCmapTable(face, uint32(font.numGlyphs), oldToNew, configuration); err != nil {
		return nil, nil, err
	} else if cmapTable != nil {
		tables["cmap"] = cmapTable
	}
	if short {
		binary.BigEndian.PutUint16(tables["head"][50:], 0)
	} else {
		binary.BigEndian.PutUint16(tables["head"][50:], 1)
	}
	encoded, err := encodeSubsetFont(ctx, face, tables, slices.Contains(needed, false), configuration.CompactGIDs, configuration)
	if err != nil {
		return nil, nil, err
	}
	return encoded, oldToNew, nil
}

// encodeSubsetFont 重建独立SFNT目录及四字节表填充，剔除失效签名及与被置空或重排字形不一致的衍生表
// 入参: ctx 取消Context, face 原字体面, replacements 替换或新增的字体表, pruned 是否置空了未用轮廓字形, compact 是否启用紧凑GID重编号, options 字节上限
// 返回: []byte 独立字体数据, error 表、字节、目录或取消错误
func encodeSubsetFont(ctx context.Context, face *fontFace, replacements map[string][]byte, pruned, compact bool, options FontSubsetOptions) ([]byte, error) {
	tagSet := make(map[string]bool, len(face.tables)+len(replacements))
	for tag := range face.tables {
		tagSet[tag] = true
	}
	for tag := range replacements {
		tagSet[tag] = true
	}
	tags := slices.Sorted(maps.Keys(tagSet))
	tags = slices.DeleteFunc(tags, func(tag string) bool {
		if tag == "DSIG" {
			return true
		}
		if _, replaced := replacements[tag]; replaced {
			return false
		}
		if compact {
			switch tag {
			case "kern", "GPOS", "GSUB", "GDEF", "JSTF", "BASE", "VORG", "hdmx", "LTSH", "VDMX", "EBLC", "EBDT", "EBSC", "CBDT", "CBLC", "sbix":
				return true
			}
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

// subsetCFFFont 裁剪CFF1字体子集表，支持原GID保号或紧凑重编号与合成cmap
// 入参: ctx 已规范化取消Context, face 原SFNT字体面, metrics 已校验字体度量, glyphs 保留字形编号, options 资源上限与重映射配置, work 可选包级剩余工作量
// 返回: []byte 独立SFNT, map[uint16]uint16 旧GID到新GID映射表, error 字形、结构、矩阵、预算或取消错误
func subsetCFFFont(ctx context.Context, face *fontFace, metrics *fontMetrics, glyphs []uint16, options FontSubsetOptions, work *int) ([]byte, map[uint16]uint16, error) {
	data, err := face.table("CFF ")
	if err != nil {
		if _, exists := face.tables["CFF2"]; exists {
			return nil, nil, fmt.Errorf("%w: CFF2 font subsetting", ErrUnsupported)
		}
		return nil, nil, err
	}
	set, err := parseCFFSet(data)
	if err != nil {
		return nil, nil, err
	}
	if len(set.names) != 1 {
		return nil, nil, fmt.Errorf("%w: OpenType CFF FontSet count", ErrInvalid)
	}
	font, err := parseCFFFont(set, 0)
	if err != nil {
		return nil, nil, err
	}
	if font.charstringType != 2 || font.paintType != 0 {
		return nil, nil, fmt.Errorf("%w: subset CFF outline representation", ErrUnsupported)
	}
	if len(font.charstrings) != int(metrics.numGlyphs) {
		return nil, nil, fmt.Errorf("%w: subset CFF and maxp glyph count", ErrInvalid)
	}
	needed := make([]bool, len(font.charstrings))
	needed[0] = true
	queue := []uint16{0}
	for _, gid := range glyphs {
		if int(gid) >= len(needed) {
			return nil, nil, fmt.Errorf("%w: subset CFF glyph index", ErrInvalid)
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
			return nil, nil, err
		}
		selected[gid] = glyph
		if glyph.seac != nil {
			if font.cid {
				return nil, nil, fmt.Errorf("%w: CID subset CFF seac", ErrInvalid)
			}
			for _, code := range []byte{glyph.seac.base, glyph.seac.accent} {
				sid := cffStandardSID(code)
				component, present := font.charset.glyph(sid)
				if sid == 0 || !present {
					return nil, nil, fmt.Errorf("%w: missing subset CFF seac component", ErrInvalid)
				}
				if !needed[component] {
					needed[component] = true
					queue = append(queue, component)
				}
			}
		}
	}
	oldToNew, newToOld := buildSubsetGIDMap(needed, options.CompactGIDs)
	var programs [][]byte
	var charsetValues []uint16
	var fdSelect []uint8
	if options.CompactGIDs {
		programs = make([][]byte, len(newToOld))
		charsetValues = make([]uint16, len(newToOld))
		if font.cid {
			fdSelect = make([]uint8, len(newToOld))
		}
		for newGID, oldGID := range newToOld {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			programs[newGID] = font.charstrings[oldGID]
			charsetValues[newGID] = font.charset.values[oldGID]
			if font.cid {
				fdSelect[newGID] = font.fdSelect[oldGID]
			}
		}
	} else {
		programs = make([][]byte, len(font.charstrings))
		charsetValues = font.charset.values
		fdSelect = font.fdSelect
		for index, original := range font.charstrings {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			if needed[index] {
				programs[index] = original
				continue
			}
			if remaining == 0 {
				return nil, nil, fmt.Errorf("%w: CFF subset replacement work", ErrLimit)
			}
			width, _, err := metrics.horizontal(uint16(index))
			if err != nil {
				return nil, nil, err
			}
			charWidth, hasWidth := subsetCFFEmptyWidth(font, uint16(index), width, metrics.unitsPerEm)
			programs[index] = subsetCFFEmptyGlyph(charWidth, hasWidth, subsetCFFGlyphPrivate(font, uint16(index)))
			if len(programs[index]) > remaining {
				return nil, nil, fmt.Errorf("%w: CFF subset replacement work", ErrLimit)
			}
			remaining -= len(programs[index])
		}
	}
	profile := subsetFontProfile{}
	var cffBounds [4]float64
	hasCFFBounds := false
	for _, gid := range queue {
		geometry := subsetCFFCloneGeometry(selected[gid].geometry)
		if seac := selected[gid].seac; seac != nil {
			for index, code := range []byte{seac.base, seac.accent} {
				component, _ := font.charset.glyph(cffStandardSID(code))
				child := selected[component]
				if child.seac != nil {
					return nil, nil, fmt.Errorf("%w: nested subset CFF seac", ErrInvalid)
				}
				part := subsetCFFCloneGeometry(child.geometry)
				if index == 1 {
					if err := cffTranslateGlyph(&part, seac.offset); err != nil {
						return nil, nil, err
					}
				}
				geometry.Figures = append(geometry.Figures, part.Figures...)
			}
		}
		geometry.Figures = slices.DeleteFunc(geometry.Figures, func(figure GeometryFigure) bool { return len(figure.Segments) == 0 })
		hasOutline := len(geometry.Figures) != 0
		if hasOutline {
			bboxGeometry := geometry
			if font.cid {
				if fdMatrix := font.fontDict[font.fdSelect[gid]].matrix; fdMatrix != nil {
					bboxMatrix := *fdMatrix
					if font.top.matrix == nil {
						bboxMatrix = (Matrix{A: 1000, D: 1000}).Mul(bboxMatrix)
					}
					if !geometryFinite(bboxMatrix.A, bboxMatrix.B, bboxMatrix.C, bboxMatrix.D, bboxMatrix.E, bboxMatrix.F) {
						return nil, nil, fmt.Errorf("%w: subset CFF FontBBox matrix", ErrLimit)
					}
					bboxGeometry = subsetCFFCloneGeometry(geometry)
					if err := fontTransformOutline(&bboxGeometry, bboxMatrix); err != nil {
						return nil, nil, err
					}
				}
			}
			cb, err := bboxGeometry.Bounds()
			if err != nil {
				return nil, nil, err
			}
			box := [4]float64{cb.X, cb.Y, cb.X + cb.Width, cb.Y + cb.Height}
			if !geometryFinite(box[0], box[1], box[2], box[3]) {
				return nil, nil, fmt.Errorf("%w: subset CFF FontBBox range", ErrLimit)
			}
			if !hasCFFBounds {
				cffBounds, hasCFFBounds = box, true
			} else {
				cffBounds[0], cffBounds[1] = min(cffBounds[0], box[0]), min(cffBounds[1], box[1])
				cffBounds[2], cffBounds[3] = max(cffBounds[2], box[2]), max(cffBounds[3], box[3])
			}
		}
		matrix, err := font.designMatrix(gid, metrics.unitsPerEm)
		if err != nil {
			return nil, nil, err
		}
		if err := fontTransformOutline(&geometry, matrix); err != nil {
			return nil, nil, err
		}
		bounds, err := geometry.Bounds()
		if err != nil {
			return nil, nil, err
		}
		xMin, yMin := math.Floor(bounds.X), math.Floor(bounds.Y)
		xMax, yMax := math.Ceil(bounds.X+bounds.Width), math.Ceil(bounds.Y+bounds.Height)
		if xMin < -32768 || yMin < -32768 || xMax > 32767 || yMax > 32767 {
			return nil, nil, fmt.Errorf("%w: subset CFF bounds outside FWORD", ErrInvalid)
		}
		bounds = Rect{X: xMin, Y: yMin, Width: xMax - xMin, Height: yMax - yMin}
		if err := profile.addBounds(gid, bounds, hasOutline, metrics); err != nil {
			return nil, nil, err
		}
	}
	encoded, err := encodeSubsetCFFTable(ctx, font, programs, charsetValues, fdSelect, cffBounds[:], options.CompactGIDs, options)
	if err != nil {
		return nil, nil, err
	}
	tables := map[string][]byte{"CFF ": encoded}
	if err := profile.apply(face, metrics, tables, ctx); err != nil {
		return nil, nil, err
	}
	if options.CompactGIDs {
		if err := applyCompactSubsetTables(face, metrics, newToOld, oldToNew, tables); err != nil {
			return nil, nil, err
		}
	}
	if cmapTable, err := buildSubsetCmapTable(face, uint32(len(font.charstrings)), oldToNew, options); err != nil {
		return nil, nil, err
	} else if cmapTable != nil {
		tables["cmap"] = cmapTable
	}
	out, err := encodeSubsetFont(ctx, face, tables, slices.Contains(needed, false), options.CompactGIDs, options)
	if err != nil {
		return nil, nil, err
	}
	return out, oldToNew, nil
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

// patchSubsetCFFDictReal 按固定宽度整数及浮点数替换指定CFF字典条目并保持其余条目原字节不变
// 入参: original 原字典, values 替换或补入的固定宽度整数条目, reals 替换或补入的浮点或紧凑整数条目, maximum 输出字节上限
// 返回: []byte 字典数据, error 原字典、数值范围或字节预算错误
func patchSubsetCFFDictReal(original []byte, values map[uint16][]int64, reals map[uint16][]float64, maximum int64) ([]byte, error) {
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
		} else if operands, replace := reals[operator]; replace {
			var err error
			entry, err = subsetCFFFloatEntry(operator, operands)
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
	for operator := range reals {
		if !seen[operator] {
			missing = append(missing, operator)
		}
	}
	slices.Sort(missing)
	for _, operator := range missing {
		var entry []byte
		var err error
		if operands, ok := values[operator]; ok {
			entry, err = subsetCFFEntry(operator, operands)
		} else {
			entry, err = subsetCFFFloatEntry(operator, reals[operator])
		}
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

// subsetCFFFloatEntry 编码支持紧凑整数及标准CFF Real浮点操作数的字典条目
// 入参: operator 字典操作符, values 有限浮点操作数
// 返回: []byte 字典条目, error 非有限值或编码超限错误
func subsetCFFFloatEntry(operator uint16, values []float64) ([]byte, error) {
	var data []byte
	for _, value := range values {
		encoded, err := subsetCFFNumberOperand(value)
		if err != nil {
			return nil, err
		}
		data = append(data, encoded...)
	}
	if operator > 255 {
		data = append(data, byte(operator>>8))
	}
	return append(data, byte(operator)), nil
}

// subsetCFFNumberOperand 按Adobe TN #5176编码单个CFF DICT数值，精确int32整数紧凑写出，其余用byte 30实数编码
// 入参: value 有限浮点数值
// 返回: []byte 操作数字节, error 非有限值或长度超限错误
func subsetCFFNumberOperand(value float64) ([]byte, error) {
	if !geometryFinite(value) {
		return nil, fmt.Errorf("%w: subset CFF DICT non-finite number", ErrInvalid)
	}
	if value == 0 {
		return []byte{139}, nil
	}
	if math.Trunc(value) == value && value >= math.MinInt32 && value <= math.MaxInt32 {
		n := int64(value)
		switch {
		case n >= -107 && n <= 107:
			return []byte{byte(n + 139)}, nil
		case n >= 108 && n <= 1131:
			v := n - 108
			return []byte{byte(247 + v/256), byte(v % 256)}, nil
		case n >= -1131 && n <= -108:
			v := -n - 108
			return []byte{byte(251 + v/256), byte(v % 256)}, nil
		case n >= -32768 && n <= 32767:
			return []byte{28, byte(n >> 8), byte(n)}, nil
		default:
			return binary.BigEndian.AppendUint32([]byte{29}, uint32(int32(n))), nil
		}
	}
	text := strconv.FormatFloat(value, 'g', -1, 64)
	var nibbles []byte
	for i := 0; i < len(text); i++ {
		switch text[i] {
		case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9':
			nibbles = append(nibbles, text[i]-'0')
		case '.':
			nibbles = append(nibbles, 10)
		case '-':
			nibbles = append(nibbles, 14)
		case 'e', 'E':
			if i+1 < len(text) && text[i+1] == '-' {
				nibbles = append(nibbles, 12)
				i++
			} else {
				nibbles = append(nibbles, 11)
				if i+1 < len(text) && text[i+1] == '+' {
					i++
				}
			}
		default:
			return nil, fmt.Errorf("%w: subset CFF DICT real syntax", ErrInvalid)
		}
	}
	nibbles = append(nibbles, 15)
	if len(nibbles)%2 != 0 {
		nibbles = append(nibbles, 15)
	}
	if len(nibbles)/2 >= cffMaxRealBytes {
		return nil, fmt.Errorf("%w: subset CFF DICT real length", ErrLimit)
	}
	data := make([]byte, 1+len(nibbles)/2)
	data[0] = 30
	for i := 0; i < len(nibbles); i += 2 {
		data[1+i/2] = nibbles[i]<<4 | nibbles[i+1]
	}
	return data, nil
}

// encodeSubsetCFFTable 重建CFF1表，支持自定义字符集、FDSelect、FontBBox更新与紧凑模式标准编码重置
// 入参: ctx 取消Context, font 原CFF字体, programs 新字形程序, charsetValues GID到SID或CID映射, fdSelect CID字体字典选择数组, fontBBox 可选四元组FontBBox, resetEncoding 紧凑模式下是否重置自定义编码, options 字节上限
// 返回: []byte 独立CFF表, error 字典、布局、范围或取消错误
func encodeSubsetCFFTable(ctx context.Context, font *cffFont, programs [][]byte, charsetValues []uint16, fdSelect []uint8, fontBBox []float64, resetEncoding bool, options FontSubsetOptions) ([]byte, error) {
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
	var reals map[uint16][]float64
	if len(fontBBox) == 4 {
		reals = map[uint16][]float64{5: fontBBox}
	}
	if font.cid {
		values[0x0c24], values[0x0c25] = []int64{0}, []int64{0}
	} else {
		values[18] = []int64{int64(privates[0].size), 0}
		if resetEncoding {
			customEncoding = false
			if _, hasEnc := font.top.dict.value(16); hasEnc {
				values[16] = []int64{0}
			}
		} else if customEncoding {
			values[16] = []int64{0}
		}
	}
	top, err := patchSubsetCFFDictReal(topObjects[0], values, reals, maximum)
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
		charset = encodeSubsetCFFCharsetFormat2(charsetValues)
	} else {
		charset = make([]byte, 1, 1+2*max(0, len(charsetValues)-1))
		for _, value := range charsetValues[1:] {
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
		position, err := put(encodeSubsetCFFFDSelectFormat3(fdSelect))
		if err != nil {
			return nil, err
		}
		values[0x0c25][0] = position
		for index, dictionary := range dictionaries {
			dictionaries[index], err = patchSubsetCFFDictReal(dictionary, map[uint16][]int64{18: {int64(privates[index].size), 0}}, nil, maximum)
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
			dictionaries[index], err = patchSubsetCFFDictReal(dictionaries[index], map[uint16][]int64{18: {int64(private.size), position}}, nil, maximum)
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
	top, err = patchSubsetCFFDictReal(topObjects[0], values, reals, maximum)
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
	dict, err := patchSubsetCFFDictReal(original, map[uint16][]int64{19: {0}}, nil, maximum)
	if err != nil {
		return subsetCFFPrivate{}, err
	}
	dict, err = patchSubsetCFFDictReal(original, map[uint16][]int64{19: {int64(len(dict))}}, nil, maximum)
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

// subsetFontResourceFaceMapped 复用已解析首字体面裁剪单字体或集合资源，并返回各字体面的旧GID到新GID映射表
// 入参: ctx 已规范化取消Context, firstFace 已解析的零号字体面, usage 各字体面使用编号, options 字节上限与紧凑重映射参数, work 包级剩余工作预算
// 返回: []byte 独立字体资源, map[uint32]map[uint16]uint16 各字体面的旧GID到新GID映射, error 字体、集合、预算或取消错误
func subsetFontResourceFaceMapped(ctx context.Context, firstFace *fontFace, usage map[uint32][]uint16, options FontSubsetOptions, work *int) ([]byte, map[uint32]map[uint16]uint16, error) {
	data := firstFace.data
	if !firstFace.collection {
		configuration, err := subsetFontConfig(&options, work)
		if err != nil {
			return nil, nil, err
		}
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		glyphs := usage[0]
		if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
			return nil, nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
		}
		if issues := firstFace.validateDirectory(); len(issues) != 0 {
			return nil, nil, fmt.Errorf("%w: font subset directory %s: %s", ErrInvalid, issues[0].table, issues[0].message)
		}
		encoded, gidMap, err := subsetFontFace(ctx, firstFace, glyphs, configuration, work)
		if err != nil {
			return nil, nil, err
		}
		return encoded, map[uint32]map[uint16]uint16{0: gidMap}, nil
	}
	if int64(len(data)) > options.MaxBytes {
		return nil, nil, fmt.Errorf("%w: collection subset input byte budget", ErrLimit)
	}
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	count := binary.BigEndian.Uint32(data[8:])
	builder, err := newFontCollectionBuilder(count, options.MaxBytes, ctx)
	if err != nil {
		return nil, nil, err
	}
	checksums := newFontChecksums(data, 3*uint64(len(data)))
	type cachedCollectionFace struct {
		header []byte
		gidMap map[uint16]uint16
	}
	cached := make(map[fontSubsetFaceKey]cachedCollectionFace)
	gidMaps := make(map[uint32]map[uint16]uint16, count)
	remaining := options.MaxWork
	if work == nil {
		work = &remaining
	}
	for index := uint32(0); index < count; index++ {
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		face := firstFace
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return nil, nil, err
			}
		}
		if issues := face.validateDirectoryChecksums(checksums); len(issues) != 0 {
			return nil, nil, fmt.Errorf("%w: collection source face %d %s: %s", ErrInvalid, index, issues[0].table, issues[0].message)
		}
		glyphs := usage[index]
		charge := 1 + len(face.tables) + len(glyphs)
		if charge > *work {
			return nil, nil, fmt.Errorf("%w: collection subset directory budget", ErrLimit)
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
		if entry, present := cached[key]; present {
			if err := builder.directory(index, entry.header); err != nil {
				return nil, nil, err
			}
			gidMaps[index] = entry.gidMap
			continue
		}
		options.CollectionIndex = index
		configuration, err := subsetFontConfig(&options, work)
		if err != nil {
			return nil, nil, err
		}
		if int64(len(data)) > configuration.MaxBytes || len(glyphs) > configuration.MaxWork {
			return nil, nil, fmt.Errorf("%w: font subset input budget", ErrLimit)
		}
		font, gidMap, err := subsetFontFace(ctx, face, glyphs, configuration, work)
		if err != nil {
			return nil, nil, err
		}
		header, err := builder.face(index, font)
		if err != nil {
			return nil, nil, err
		}
		cached[key] = cachedCollectionFace{header: header, gidMap: gidMap}
		gidMaps[index] = gidMap
	}
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	return builder.data, gidMaps, nil
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

// SubsetFonts 汇总包内字体使用并裁剪资源，默认保持GID不变；启用CompactGIDs时按升序紧凑重编号并同步重写所有引用页面与资源字典的Glyphs.Indices
// 不绕过字体许可且不自动重签，失败不修改包；不支持或X3D关联字体原样保留并以ErrUnsupported记入结果
// 入参: ctx 取消Context，nil采用Background, options 字节、累计工作及CompactGIDs参数，nil采用默认值
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
		configuration.CompactGIDs = options.CompactGIDs
	}
	return p.subsetFontsLocked(ctx, FontSubsetOptions{MaxBytes: configuration.MaxBytes, MaxWork: configuration.MaxWork, CompactGIDs: configuration.CompactGIDs})
}

// SubsetFontsWithOptions 按FontSubsetOptions裁剪包内字体资源，支持CompactGIDs紧凑重编号并同步重写引用页面与字典中的Glyphs.Indices
// 入参: ctx 取消Context，nil采用Background, options 字体子集化选项，nil采用默认值
// 返回: []ResourceOptimization 按部件名排列的资源结果，失败为nil, error 使用汇总、字体、预算或取消错误
func (p *Package) SubsetFontsWithOptions(ctx context.Context, options *FontSubsetOptions) ([]ResourceOptimization, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	cfg := FontSubsetOptions{MaxBytes: p.limits.MaxPartBytes, MaxWork: 1 << 20}
	if options != nil {
		cfg = *options
		if cfg.MaxBytes == 0 {
			cfg.MaxBytes = p.limits.MaxPartBytes
		}
		if cfg.MaxWork == 0 {
			cfg.MaxWork = 1 << 20
		}
	}
	return p.subsetFontsLocked(ctx, cfg)
}

// subsetFontsLocked 在持有包写锁时执行包级字体裁剪，并在启用CompactGIDs时同步重映射所有引用页面的Glyphs.Indices
// 入参: ctx 已规范化取消Context, options 字体裁剪配置
// 返回: []ResourceOptimization 优化结果列表, error 裁剪、重写或校验错误
func (p *Package) subsetFontsLocked(ctx context.Context, options FontSubsetOptions) ([]ResourceOptimization, error) {
	if options.MaxBytes < 1 || options.MaxWork < 1 {
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
	remaps := make(map[string]map[uint32]map[uint16]uint16)
	var result []ResourceOptimization
	remaining := options.MaxWork
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
		face, err := reader.pkg.readFontFaceLimit(part.name, 0, options.MaxBytes)
		if err != nil {
			return nil, err
		}
		faceOpts := FontSubsetOptions{MaxBytes: options.MaxBytes, MaxWork: options.MaxWork, AllowMissingCmap: options.AllowMissingCmap, CompactGIDs: options.CompactGIDs}
		encoded, gidMaps, err := subsetFontResourceFaceMapped(ctx, face, groups[key], faceOpts, &remaining)
		if err != nil {
			if !errors.Is(err, ErrUnsupported) && !errors.Is(err, ErrRestricted) {
				return nil, &PartError{Part: part.name, Err: err}
			}
			entry.Err = err
			result = append(result, entry)
			continue
		}
		if int64(len(encoded)) < entry.OriginalBytes {
			if matchStandardContentType(p.format, part.media, "application/vnd.ms-package.obfuscated-opentype") {
				encoded, err = ObfuscateFont(part.name, encoded)
				if err != nil {
					return nil, err
				}
			}
			entry.Bytes, entry.Changed = int64(len(encoded)), true
			pending[key] = packagePart{name: part.name, media: part.media, data: encoded}
			if options.CompactGIDs && fontSubsetHasNonIdentityRemap(gidMaps) {
				remaps[key] = gidMaps
			}
		}
		result = append(result, entry)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if len(remaps) == 0 {
		for key, value := range pending {
			p.total -= int64(len(p.parts[key].data)) - int64(len(value.data))
			p.parts[key], p.dirty[key] = value, true
		}
		return result, nil
	}
	q := p.storyCopy()
	for key, value := range pending {
		q.total -= int64(len(q.parts[key].data)) - int64(len(value.data))
		q.parts[key], q.dirty[key] = value, true
	}
	for _, key := range slices.Sorted(maps.Keys(q.parts)) {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		part := q.parts[key]
		if !strings.EqualFold(part.media, fixedContentType("fixedpage")) && !strings.EqualFold(part.media, resourceDictionaryContentType) {
			continue
		}
		rewritten, changed, err := rewriteSubsetFontGlyphIndices(part.name, part.data, q.format, q.limits, remaps, ctx)
		if err != nil {
			return nil, &PartError{Part: part.name, Err: err}
		}
		if !changed {
			continue
		}
		if err := q.editable(part.name); err != nil {
			return nil, err
		}
		if int64(len(rewritten)) > q.limits.MaxPartBytes {
			return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: rewritten glyph indices exceed part budget", ErrLimit)}
		}
		nextTotal := q.total - int64(len(part.data)) + int64(len(rewritten))
		if nextTotal > q.limits.MaxPackageBytes {
			return nil, fmt.Errorf("%w: rewritten glyph indices exceed package budget", ErrLimit)
		}
		q.total = nextTotal
		q.parts[key] = packagePart{name: part.name, media: part.media, data: rewritten}
		q.dirty[key] = true
	}
	verified, err := q.reader(ctx)
	if err != nil {
		return nil, err
	}
	verified.Close()
	p.commitStory(q)
	return result, nil
}

// fontSubsetHasNonIdentityRemap 判断字体各面的GID映射是否存在实际变化
// 入参: gidMaps 字体面索引到旧新GID映射表的集合
// 返回: bool 是否至少有一个字形编号发生改变
func fontSubsetHasNonIdentityRemap(gidMaps map[uint32]map[uint16]uint16) bool {
	for _, faceMap := range gidMaps {
		for oldGID, newGID := range faceMap {
			if oldGID != newGID {
				return true
			}
		}
	}
	return false
}

// rewriteSubsetFontGlyphIndices 重写FixedPage或ResourceDictionary中引用紧凑重映射字体的Glyphs.Indices属性
// 入参: partName 当前标记部件URI, original 原始XML字节, format 文档方言, limits 资源上限, remaps 字体部件及面索引对应的旧新GID映射, ctx 取消Context
// 返回: []byte 重写后XML字节, bool 是否发生修改, error XML、解析或映射缺失错误
func rewriteSubsetFontGlyphIndices(partName string, original []byte, format Format, limits Limits, remaps map[string]map[uint32]map[uint16]uint16, ctx context.Context) ([]byte, bool, error) {
	namespace := formatNamespace(format)
	tracker := newResourceMarkupIgnoreTracker(format, false, ctx)
	filter := func(token xml.Token, node *xmlElement) (bool, error) {
		skip, _, err := tracker.visit(token, node)
		return skip, err
	}
	encoder := pageEncoder{format: format, ns: namespace, part: partName, limits: limits, ctx: ctx}
	return rewriteXMLAttributes(original, limits, ctx, nil, filter, func(node *xmlElement, attr xml.Attr) (string, bool, error) {
		if node.Name != (xml.Name{Space: namespace, Local: "Glyphs"}) || attr.Name != (xml.Name{Local: "Indices"}) {
			return attr.Value, false, nil
		}
		fontAttr, ok := node.attribute("FontUri")
		if !ok {
			return attr.Value, false, nil
		}
		uri, faceIndex, _, err := ParseFontURI(strings.Trim(fontAttr, " \t\r\n"))
		if err != nil {
			return "", false, err
		}
		fontPart, err := resolvePart(partName, uri)
		if err != nil {
			return "", false, err
		}
		faceMaps, present := remaps[strings.ToLower(fontPart)]
		if !present {
			return attr.Value, false, nil
		}
		gidMap, present := faceMaps[faceIndex]
		if !present {
			return attr.Value, false, nil
		}
		clusters, err := ParseGlyphIndices(attr.Value)
		if err != nil {
			return "", false, err
		}
		modified := false
		for ci := range clusters {
			for gi := range clusters[ci].Glyphs {
				entry := &clusters[ci].Glyphs[gi]
				if !entry.HasIndex {
					continue
				}
				newGID, ok := gidMap[entry.Index]
				if !ok {
					return "", false, fmt.Errorf("%w: missing remapped glyph %d for %s", ErrInvalid, entry.Index, fontPart)
				}
				if newGID != entry.Index {
					entry.Index = newGID
					modified = true
				}
			}
		}
		if !modified {
			return attr.Value, false, nil
		}
		encoder.work, encoder.bytes = 0, 0
		encoded, err := encoder.glyphIndices(clusters, 1)
		if err != nil {
			return "", false, err
		}
		return encoded, true, nil
	})
}

// buildSubsetGIDMap 按保留字形集合生成旧GID到新GID映射表及按新GID排序的旧GID切片
// 入参: needed 源字体各GID保留标记, compact 是否启用紧凑升序重编号
// 返回: map[uint16]uint16 旧GID到新GID映射表, []uint16 新GID到旧GID反查表
func buildSubsetGIDMap(needed []bool, compact bool) (map[uint16]uint16, []uint16) {
	oldToNew := make(map[uint16]uint16)
	var newToOld []uint16
	for oldGID, keep := range needed {
		if !keep {
			continue
		}
		if compact {
			newGID := uint16(len(newToOld))
			oldToNew[uint16(oldGID)] = newGID
			newToOld = append(newToOld, uint16(oldGID))
		} else {
			oldToNew[uint16(oldGID)] = uint16(oldGID)
			newToOld = append(newToOld, uint16(oldGID))
		}
	}
	return oldToNew, newToOld
}

// rewriteCompositeGlyphIDs 按紧凑重映射表原地替换TrueType复合字形记录中的所有组件GID
// 入参: raw 单个复合字形的glyf字节副本, oldToNew 旧GID到新GID映射表
// 返回: error 复合记录截断或组件缺失错误
func rewriteCompositeGlyphIDs(raw []byte, oldToNew map[uint16]uint16) error {
	for pos := 10; ; {
		if pos+4 > len(raw) {
			return fmt.Errorf("%w: truncated composite glyph during GID remap", ErrInvalid)
		}
		flags := binary.BigEndian.Uint16(raw[pos:])
		oldGID := binary.BigEndian.Uint16(raw[pos+2:])
		newGID, ok := oldToNew[oldGID]
		if !ok {
			return fmt.Errorf("%w: missing remapped composite component %d", ErrInvalid, oldGID)
		}
		binary.BigEndian.PutUint16(raw[pos+2:], newGID)
		pos += 4
		if flags&0x0001 != 0 {
			pos += 4
		} else {
			pos += 2
		}
		switch {
		case flags&0x0008 != 0:
			pos += 2
		case flags&0x0040 != 0:
			pos += 4
		case flags&0x0080 != 0:
			pos += 8
		}
		if pos > len(raw) {
			return fmt.Errorf("%w: truncated composite glyph transform during GID remap", ErrInvalid)
		}
		if flags&0x0020 == 0 {
			break
		}
	}
	return nil
}

// applyCompactSubsetTables 按紧凑GID顺序重建hmtx、vmtx、maxp、post与可选VORG并同步hhea和vhea记录数与最大步进
// 入参: face 原字体面, metrics 原字体度量, newToOld 新GID到旧GID表, oldToNew 旧GID到新GID表, tables 替换表集合
// 返回: error 度量读取或表数据错误
func applyCompactSubsetTables(face *fontFace, metrics *fontMetrics, newToOld []uint16, oldToNew map[uint16]uint16, tables map[string][]byte) error {
	count := len(newToOld)
	if count == 0 || count > 65535 {
		return fmt.Errorf("%w: compact subset glyph count", ErrLimit)
	}
	hmtx := make([]byte, count*4)
	var maxHAdv uint16
	for newGID, oldGID := range newToOld {
		adv, lsb, err := metrics.horizontal(oldGID)
		if err != nil {
			return err
		}
		binary.BigEndian.PutUint16(hmtx[newGID*4:], adv)
		binary.BigEndian.PutUint16(hmtx[newGID*4+2:], uint16(lsb))
		maxHAdv = max(maxHAdv, adv)
	}
	tables["hmtx"] = hmtx
	binary.BigEndian.PutUint16(tables["hhea"][10:], maxHAdv)
	binary.BigEndian.PutUint16(tables["hhea"][34:], uint16(count))
	binary.BigEndian.PutUint16(tables["maxp"][4:], uint16(count))
	if metrics.vhea != nil && tables["vhea"] != nil {
		vmtx := make([]byte, count*4)
		var maxVAdv uint16
		for newGID, oldGID := range newToOld {
			adv, tsb, err := metrics.vertical(oldGID)
			if err != nil {
				return err
			}
			binary.BigEndian.PutUint16(vmtx[newGID*4:], adv)
			binary.BigEndian.PutUint16(vmtx[newGID*4+2:], uint16(tsb))
			maxVAdv = max(maxVAdv, adv)
		}
		tables["vmtx"] = vmtx
		binary.BigEndian.PutUint16(tables["vhea"][10:], maxVAdv)
		binary.BigEndian.PutUint16(tables["vhea"][34:], uint16(count))
	}
	if _, hasPost := face.tables["post"]; hasPost {
		postData, err := face.table("post")
		if err != nil {
			return err
		}
		if len(postData) >= 32 && binary.BigEndian.Uint32(postData) != 0x00030000 {
			post3 := bytes.Clone(postData[:32])
			binary.BigEndian.PutUint32(post3, 0x00030000)
			tables["post"] = post3
		}
	}
	if len(metrics.vorg) >= 8 {
		type vorgEntry struct {
			gid uint16
			y   uint16
		}
		origCount := int(binary.BigEndian.Uint16(metrics.vorg[6:]))
		var entries []vorgEntry
		for i := range origCount {
			oldGID := binary.BigEndian.Uint16(metrics.vorg[8+4*i:])
			if newGID, ok := oldToNew[oldGID]; ok {
				entries = append(entries, vorgEntry{gid: newGID, y: binary.BigEndian.Uint16(metrics.vorg[10+4*i:])})
			}
		}
		slices.SortFunc(entries, func(a, b vorgEntry) int {
			if a.gid < b.gid {
				return -1
			}
			if a.gid > b.gid {
				return 1
			}
			return 0
		})
		vorg := make([]byte, 8+4*len(entries))
		copy(vorg[:6], metrics.vorg[:6])
		binary.BigEndian.PutUint16(vorg[6:], uint16(len(entries)))
		for i, entry := range entries {
			binary.BigEndian.PutUint16(vorg[8+4*i:], entry.gid)
			binary.BigEndian.PutUint16(vorg[10+4*i:], entry.y)
		}
		tables["VORG"] = vorg
	}
	return nil
}

// buildSubsetCmapTable 按SynthesizeCmap或CompactGIDs生成标准OpenType Format 4与Format 12 cmap表
// 入参: face 原字体面, numGlyphs 原字形总数, oldToNew 旧GID到新GID映射表, options 子集配置
// 返回: []byte 新cmap表字节，无需重写时为nil, error 映射越界或解析错误
func buildSubsetCmapTable(face *fontFace, numGlyphs uint32, oldToNew map[uint16]uint16, options FontSubsetOptions) ([]byte, error) {
	if len(options.SynthesizeCmap) > 0 {
		mapping := make(map[rune]uint16, len(options.SynthesizeCmap))
		for r, oldGID := range options.SynthesizeCmap {
			if !utf8.ValidRune(r) || uint32(oldGID) >= numGlyphs {
				return nil, fmt.Errorf("%w: invalid SynthesizeCmap rune %U or glyph %d", ErrInvalid, r, oldGID)
			}
			if oldGID == 0 {
				continue
			}
			newGID, ok := oldToNew[oldGID]
			if !ok {
				continue
			}
			if newGID != 0 {
				mapping[r] = newGID
			}
		}
		return encodeOpenTypeCmap(mapping)
	}
	if !options.CompactGIDs {
		return nil, nil
	}
	if _, hasCmap := face.tables["cmap"]; !hasCmap {
		return nil, nil
	}
	cmapData, err := face.table("cmap")
	if err != nil {
		return nil, err
	}
	parsed, err := parseFontCmap(cmapData, numGlyphs)
	if err != nil {
		return nil, err
	}
	mapping := make(map[rune]uint16, len(oldToNew))
	for oldGID, newGID := range oldToNew {
		if oldGID == 0 || newGID == 0 {
			continue
		}
		for _, r := range parsed.runesForGlyph(oldGID, fontGlyphRunesLimit) {
			if _, exists := mapping[r]; !exists {
				mapping[r] = newGID
			}
		}
	}
	return encodeOpenTypeCmap(mapping)
}

// encodeOpenTypeCmap 合成标准OpenType cmap表，BMP优先使用Format 4，超限或含增补平面码点时写出Format 12
// 入参: mapping Unicode标量到非零字形编号映射
// 返回: []byte 符合OpenType规范的完整cmap表字节, error 超出格式限制错误
func encodeOpenTypeCmap(mapping map[rune]uint16) ([]byte, error) {
	type pair struct {
		code uint32
		gid  uint16
	}
	var all []pair
	var bmp []pair
	hasNonBMP := false
	for r, gid := range mapping {
		if gid == 0 || !utf8.ValidRune(r) {
			continue
		}
		code := uint32(r)
		all = append(all, pair{code: code, gid: gid})
		if code <= 0xfffe {
			bmp = append(bmp, pair{code: code, gid: gid})
		} else if code > 0xffff {
			hasNonBMP = true
		}
	}
	slices.SortFunc(all, func(a, b pair) int {
		if a.code < b.code {
			return -1
		}
		if a.code > b.code {
			return 1
		}
		return 0
	})
	slices.SortFunc(bmp, func(a, b pair) int {
		if a.code < b.code {
			return -1
		}
		if a.code > b.code {
			return 1
		}
		return 0
	})
	type format4Seg struct {
		start uint16
		end   uint16
		delta uint16
		gids  []uint16
	}
	buildFormat4 := func(mergeGap uint32) []byte {
		var segs []format4Seg
		for i := 0; i < len(bmp); {
			startCode := bmp[i].code
			startGID := bmp[i].gid
			endIdx := i
			if mergeGap == 0 {
				for endIdx+1 < len(bmp) && bmp[endIdx+1].code == bmp[endIdx].code+1 && uint32(bmp[endIdx+1].gid) == uint32(bmp[endIdx].gid)+1 {
					endIdx++
				}
				segs = append(segs, format4Seg{start: uint16(startCode), end: uint16(bmp[endIdx].code), delta: startGID - uint16(startCode)})
			} else {
				for endIdx+1 < len(bmp) && bmp[endIdx+1].code-bmp[endIdx].code <= mergeGap {
					endIdx++
				}
				endCode := bmp[endIdx].code
				gids := make([]uint16, endCode-startCode+1)
				for j := i; j <= endIdx; j++ {
					gids[bmp[j].code-startCode] = bmp[j].gid
				}
				segs = append(segs, format4Seg{start: uint16(startCode), end: uint16(endCode), gids: gids})
			}
			i = endIdx + 1
		}
		segs = append(segs, format4Seg{start: 0xffff, end: 0xffff, delta: 1})
		segCount := len(segs)
		arrayLen := 0
		for _, seg := range segs {
			arrayLen += len(seg.gids)
		}
		totalLen := 16 + 8*segCount + 2*arrayLen
		if totalLen > 65535 {
			return nil
		}
		segCountX2 := uint16(segCount * 2)
		entrySelector := uint16(bits.Len(uint(segCount)) - 1)
		searchRange := uint16(2 << entrySelector)
		rangeShift := segCountX2 - searchRange
		out := make([]byte, totalLen)
		binary.BigEndian.PutUint16(out[0:], 4)
		binary.BigEndian.PutUint16(out[2:], uint16(totalLen))
		binary.BigEndian.PutUint16(out[6:], segCountX2)
		binary.BigEndian.PutUint16(out[8:], searchRange)
		binary.BigEndian.PutUint16(out[10:], entrySelector)
		binary.BigEndian.PutUint16(out[12:], rangeShift)
		arrayPos := 16 + 8*segCount
		for idx, seg := range segs {
			binary.BigEndian.PutUint16(out[14+2*idx:], seg.end)
			binary.BigEndian.PutUint16(out[16+2*segCount+2*idx:], seg.start)
			binary.BigEndian.PutUint16(out[16+4*segCount+2*idx:], seg.delta)
			wordPos := 16 + 6*segCount + 2*idx
			if len(seg.gids) > 0 {
				binary.BigEndian.PutUint16(out[wordPos:], uint16(arrayPos-wordPos))
				for _, gid := range seg.gids {
					binary.BigEndian.PutUint16(out[arrayPos:], gid)
					arrayPos += 2
				}
			}
		}
		return out
	}
	sub4 := buildFormat4(0)
	if sub4 == nil {
		sub4 = buildFormat4(8)
	}
	if sub4 == nil {
		sub4 = buildFormat4(65535)
	}
	if sub4 != nil && !hasNonBMP {
		headerLen := uint32(4 + 2*8)
		out := make([]byte, int(headerLen)+len(sub4))
		binary.BigEndian.PutUint16(out[2:], 2)
		binary.BigEndian.PutUint16(out[4:], 0)
		binary.BigEndian.PutUint16(out[6:], 3)
		binary.BigEndian.PutUint32(out[8:], headerLen)
		binary.BigEndian.PutUint16(out[12:], 3)
		binary.BigEndian.PutUint16(out[14:], 1)
		binary.BigEndian.PutUint32(out[16:], headerLen)
		copy(out[headerLen:], sub4)
		return out, nil
	}
	type format12Group struct {
		start uint32
		end   uint32
		gid   uint32
	}
	var groups []format12Group
	for i := 0; i < len(all); {
		j := i
		for j+1 < len(all) && all[j+1].code == all[j].code+1 && uint32(all[j+1].gid) == uint32(all[j].gid)+1 {
			j++
		}
		groups = append(groups, format12Group{start: all[i].code, end: all[j].code, gid: uint32(all[i].gid)})
		i = j + 1
	}
	sub12Len := uint64(16) + 12*uint64(len(groups))
	if sub12Len > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded cmap format 12 exceeds uint32 range", ErrLimit)
	}
	sub12 := make([]byte, int(sub12Len))
	binary.BigEndian.PutUint16(sub12[0:], 12)
	binary.BigEndian.PutUint32(sub12[4:], uint32(sub12Len))
	binary.BigEndian.PutUint32(sub12[12:], uint32(len(groups)))
	for i, group := range groups {
		pos := 16 + 12*i
		binary.BigEndian.PutUint32(sub12[pos:], group.start)
		binary.BigEndian.PutUint32(sub12[pos+4:], group.end)
		binary.BigEndian.PutUint32(sub12[pos+8:], group.gid)
	}
	if sub4 == nil {
		headerLen := uint32(4 + 2*8)
		if uint64(headerLen)+sub12Len > math.MaxUint32 {
			return nil, fmt.Errorf("%w: encoded cmap exceeds uint32 range", ErrLimit)
		}
		out := make([]byte, int(headerLen)+len(sub12))
		binary.BigEndian.PutUint16(out[2:], 2)
		records := [2][3]uint32{{0, 4, headerLen}, {3, 10, headerLen}}
		for i, rec := range records {
			pos := 4 + 8*i
			binary.BigEndian.PutUint16(out[pos:], uint16(rec[0]))
			binary.BigEndian.PutUint16(out[pos+2:], uint16(rec[1]))
			binary.BigEndian.PutUint32(out[pos+4:], rec[2])
		}
		copy(out[headerLen:], sub12)
		return out, nil
	}
	headerLen := uint32(4 + 4*8)
	off4 := headerLen
	off12 := uint64(off4) + uint64((len(sub4)+3)&^3)
	if off12+sub12Len > math.MaxUint32 {
		return nil, fmt.Errorf("%w: encoded cmap exceeds uint32 range", ErrLimit)
	}
	out := make([]byte, int(off12)+len(sub12))
	binary.BigEndian.PutUint16(out[2:], 4)
	records := [4][3]uint32{{0, 3, off4}, {0, 4, uint32(off12)}, {3, 1, off4}, {3, 10, uint32(off12)}}
	for i, rec := range records {
		pos := 4 + 8*i
		binary.BigEndian.PutUint16(out[pos:], uint16(rec[0]))
		binary.BigEndian.PutUint16(out[pos+2:], uint16(rec[1]))
		binary.BigEndian.PutUint32(out[pos+4:], rec[2])
	}
	copy(out[off4:], sub4)
	copy(out[int(off12):], sub12)
	return out, nil
}
