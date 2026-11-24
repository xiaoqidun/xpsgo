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
	"encoding/hex"
	"encoding/xml"
	"fmt"
	"maps"
	"math"
	"math/bits"
	"net/url"
	"path"
	"slices"
	"sort"
	"strconv"
	"strings"
	"unicode/utf16"
	"unicode/utf8"
)

// fontChecksumBlock 限定每次区间查询的边缘扫描量，必须是四的倍数
const fontChecksumBlock = 256

const (
	// FontEmbeddingUnknown 表示未知字体嵌入许可
	FontEmbeddingUnknown FontEmbeddingPermission = iota
	// FontEmbeddingInstallable 表示可安装嵌入许可
	FontEmbeddingInstallable
	// FontEmbeddingRestricted 表示受限禁止嵌入与编辑许可
	FontEmbeddingRestricted
	// FontEmbeddingPreviewPrint 表示仅允许预览与打印嵌入许可
	FontEmbeddingPreviewPrint
	// FontEmbeddingEditable 表示允许可编辑嵌入许可
	FontEmbeddingEditable
)

// fontTable 保存字体表相对于完整字体部件的范围及校验和
type fontTable struct {
	offset   uint32
	length   uint32
	checksum uint32
}

// fontIssue 记录可安全读取但不符合字体封装规范的问题
type fontIssue struct {
	table   string
	message string
}

// fontFace 保存单个字体面的只读表视图，不接管输入数据
type fontFace struct {
	data       []byte
	offset     uint32
	tables     map[string]fontTable
	cff        bool
	collection bool
	issues     []fontIssue
}

// fontChecksums 保存按字节位置模四分块累加的只读字体校验和前缀
type fontChecksums struct {
	data   []byte
	prefix [][4]uint32
}

// fontCacheKey 区分包内字体部件及集合索引，部件键按OPC规则忽略大小写
type fontCacheKey struct {
	part  string
	index uint32
}

// fontCache 保存单次处理的字体数据及字体面，不跨阅读器或请求共享可变缓存
type fontCache struct {
	pkg       *packageReader
	data      map[string][]byte
	faces     map[fontCacheKey]*fontSource
	remaining int64
	maxFaces  int
	created   map[fontCacheKey]bool
	checksums map[string]fontChecksums
}

// FontEmbeddingPermission 表示OpenType字体OS/2表声明的嵌入许可级别
type FontEmbeddingPermission uint8

// FontResource 保存已解混淆的只读字体程序、名称、格式、度量及嵌入权限元数据
// Data为独立字节副本，与内部解析状态隔离；Ascender与Descender采用hhea设计单位
// EmbeddingPermission保留OS/2原始fsType位掩码，Permission表示许可级别，受限状态由IsRestricted提供
type FontResource struct {
	Part                string
	CollectionIndex     uint32
	HasCollectionIndex  bool
	Obfuscated          bool
	IsCollection        bool
	IsCFF               bool
	FamilyName          string
	PostScriptName      string
	Data                []byte
	UnitsPerEm          uint16
	Ascender            int16
	Descender           int16
	GlyphCount          int
	EmbeddingPermission uint16
	Permission          FontEmbeddingPermission
	source              *fontSource
}

// fontMetrics 保存未缩放的字体设计度量及原始权限信息，不执行嵌入权限策略
type fontMetrics struct {
	unitsPerEm uint16
	numGlyphs  uint16
	hhea       fontMetricHeader
	vhea       *fontMetricHeader
	hmtx       []byte
	vmtx       []byte
	os2        *fontOS2Metrics
	vorg       []byte
}

// fontMetricHeader 保存横向或竖向度量头的公共字段
type fontMetricHeader struct {
	ascender    int16
	descender   int16
	longMetrics uint16
}

// fontOS2Metrics 保存OS/2版本、原始权限标志及排版度量
type fontOS2Metrics struct {
	version       uint16
	fsType        uint16
	typoAscender  int16
	typoDescender int16
}

// glyphRun 保存未重排的字形定位结果及设计单位粗体扩张半径
type glyphRun struct {
	glyphs     []positionedGlyph
	rtl        bool
	sideways   bool
	bold       bool
	italic     bool
	boldRadius float64
}

// positionedGlyph 保存字形编号、UTF-16簇范围、局部原点及设计单位到局部坐标的变换矩阵
type positionedGlyph struct {
	gid             uint16
	cluster         int
	clusterStart    int
	clusterEnd      int
	explicitIndex   bool
	explicitAdvance bool
	nominal         Point
	origin          Point
	advance         float64
	matrix          Matrix
}

// FontUsage 保存一个字体面的实际字形编号，包含.notdef，列表按编号递增且无重复
// 不展开复合字形依赖，依赖闭包由裁剪后端处理；Part保持包内原始部件名
type FontUsage struct {
	Part            string
	CollectionIndex uint32
	Glyphs          []uint16
}

// fontUsageCollector 汇总全部原始固定布局标记，包括未选兼容分支和未引用字典
type fontUsageCollector struct {
	reader  *Reader
	fonts   fontCache
	usage   map[fontCacheKey]map[uint16]bool
	work    int
	context context.Context
}

// readFontFaceLimit 按实际解压数据限制字体读取，不仅依赖ZIP声明的部件长度
// 入参: part 字体部件URI, index 字体面索引, maximum 本次读取上限
// 返回: *fontFace 已解除混淆的字体面, error 字体、封装或预算错误
func (p *packageReader) readFontFaceLimit(part string, index uint32, maximum int64) (*fontFace, error) {
	face, _, err := p.readFontFaceInfo(part, index, maximum)
	return face, err
}

// readFontFaceInfo 合并内容类型与部件规范化查表，按实际解压上限读取并解除混淆字体面
// 入参: part 字体部件URI, index 字体面索引, maximum 本次读取上限
// 返回: *fontFace 已解除混淆的字体面, bool 原部件是否为ODTTF混淆字体, error 字体、封装或预算错误
func (p *packageReader) readFontFaceInfo(part string, index uint32, maximum int64) (*fontFace, bool, error) {
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	media, err := p.contentType(canonical)
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	if !requiredResourceMedia(requiredFont, media) {
		return nil, false, &PartError{Part: part, Err: fmt.Errorf("%w: unexpected font content type %q", ErrInvalid, media)}
	}
	data, err := p.readItems(strings.ToLower(canonical), min(maximum, p.limits.MaxPartBytes))
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	obfuscated := strings.EqualFold(media, "application/vnd.ms-package.obfuscated-opentype")
	if obfuscated {
		if len(data) < 32 {
			return nil, false, &PartError{Part: part, Err: fmt.Errorf("%w: truncated obfuscated font", ErrInvalid)}
		}
		key, err := FontObfuscationKey(part)
		if err != nil {
			return nil, false, &PartError{Part: part, Err: err}
		}
		for i := range 32 {
			data[i] ^= key[i%len(key)]
		}
	}
	face, err := parseFontFace(data, index)
	if err != nil {
		return nil, false, &PartError{Part: part, Err: err}
	}
	return face, obfuscated, nil
}

// parseFontFace 解析OpenType字体面及TTC集合中的指定字体面目录，不解码表内容
// 入参: data 完整字体部件数据, index 从零开始的字体面索引
// 返回: *fontFace 字体面, error 封装或范围错误
func parseFontFace(data []byte, index uint32) (*fontFace, error) {
	offset, headerEnd, collection, err := fontFaceOffset(data, index)
	if err != nil {
		return nil, err
	}
	header := data[offset : uint64(offset)+12]
	version := binary.BigEndian.Uint32(header)
	if version != 0x00010000 && version != 0x4f54544f {
		return nil, fmt.Errorf("%w: font outline format %#x", ErrUnsupported, version)
	}
	count := uint64(binary.BigEndian.Uint16(header[4:]))
	directoryEnd := uint64(offset) + 12 + count*16
	if count == 0 || directoryEnd > uint64(len(data)) {
		return nil, fmt.Errorf("%w: truncated or empty font table directory", ErrInvalid)
	}
	face := &fontFace{data: data, offset: offset, tables: make(map[string]fontTable, count), cff: version == 0x4f54544f, collection: collection}
	selector := bits.Len64(count) - 1
	search := uint64(16) << selector
	if search > 65535 || count*16-search > 65535 || uint64(binary.BigEndian.Uint16(header[6:])) != search || int(binary.BigEndian.Uint16(header[8:])) != selector || uint64(binary.BigEndian.Uint16(header[10:])) != count*16-search {
		face.issues = append(face.issues, fontIssue{message: "incorrect table directory search fields"})
	}
	if offset%4 != 0 {
		face.issues = append(face.issues, fontIssue{message: "font directory is not four-byte aligned"})
	}
	previous := ""
	for i := uint64(0); i < count; i++ {
		position := uint64(offset) + 12 + i*16
		record := data[position : position+16]
		tag := string(record[:4])
		for _, c := range record[:4] {
			if c < 32 || c > 126 {
				return nil, fmt.Errorf("%w: invalid font table tag %q", ErrInvalid, tag)
			}
		}
		if _, exists := face.tables[tag]; exists {
			return nil, fmt.Errorf("%w: duplicate font table %q", ErrInvalid, tag)
		}
		table := fontTable{checksum: binary.BigEndian.Uint32(record[4:]), offset: binary.BigEndian.Uint32(record[8:]), length: binary.BigEndian.Uint32(record[12:])}
		start, end := uint64(table.offset), uint64(table.offset)+uint64(table.length)
		if end > uint64(len(data)) || table.length != 0 && (start < headerEnd || start < directoryEnd && end > uint64(offset)) {
			return nil, fmt.Errorf("%w: invalid range for font table %q", ErrInvalid, tag)
		}
		if tag < previous {
			face.issues = append(face.issues, fontIssue{table: tag, message: "table directory is not sorted by tag"})
		}
		previous = tag
		if table.offset%4 != 0 {
			face.issues = append(face.issues, fontIssue{table: tag, message: "table is not four-byte aligned"})
		}
		face.tables[tag] = table
	}
	return face, nil
}

// fontFaceOffset 校验字体封装头并定位指定字体面的目录
// 入参: data 完整字体部件数据, index 字体面索引
// 返回: uint32 字体面偏移, uint64 集合头结束位置, bool 是否为集合, error 封装错误
func fontFaceOffset(data []byte, index uint32) (uint32, uint64, bool, error) {
	if len(data) < 12 {
		return 0, 0, false, fmt.Errorf("%w: truncated font header", ErrInvalid)
	}
	if string(data[:4]) != "ttcf" {
		if index != 0 {
			return 0, 0, false, fmt.Errorf("%w: face index %d in a standalone font", ErrInvalid, index)
		}
		return 0, 0, false, nil
	}
	version := binary.BigEndian.Uint32(data[4:])
	if version != 0x00010000 && version != 0x00020000 {
		return 0, 0, false, fmt.Errorf("%w: font collection version %#x", ErrUnsupported, version)
	}
	count := uint64(binary.BigEndian.Uint32(data[8:]))
	end := uint64(12) + count*4
	if version == 0x00020000 {
		end += 12
	}
	if count == 0 || uint64(index) >= count || end > uint64(len(data)) {
		return 0, 0, false, fmt.Errorf("%w: invalid font collection count or face index", ErrInvalid)
	}
	if version == 0x00020000 {
		dsig := data[end-12 : end]
		tag := binary.BigEndian.Uint32(dsig)
		length := uint64(binary.BigEndian.Uint32(dsig[4:]))
		position := uint64(binary.BigEndian.Uint32(dsig[8:]))
		if tag == 0 && (length != 0 || position != 0) || tag != 0 && (tag != 0x44534947 || length == 0 || position < end || position+length > uint64(len(data))) {
			return 0, 0, false, fmt.Errorf("%w: invalid font collection signature range", ErrInvalid)
		}
	}
	position := uint64(12) + uint64(index)*4
	offset := binary.BigEndian.Uint32(data[position:])
	if uint64(offset) < end || uint64(offset)+12 > uint64(len(data)) {
		return 0, 0, false, fmt.Errorf("%w: invalid font face offset", ErrInvalid)
	}
	return offset, end, true, nil
}

// table 返回指定字体表的只读数据，缺表或越界时返回错误
// 入参: tag 四字节字体表标识
// 返回: []byte 字体表视图, error 表范围或缺失错误
func (f *fontFace) table(tag string) ([]byte, error) {
	if f == nil {
		return nil, fmt.Errorf("%w: missing font face", ErrInvalid)
	}
	table, ok := f.tables[tag]
	if !ok {
		return nil, fmt.Errorf("%w: missing font table %q", ErrInvalid, tag)
	}
	end := uint64(table.offset) + uint64(table.length)
	if end > uint64(len(f.data)) {
		return nil, fmt.Errorf("%w: font table %q exceeds input", ErrInvalid, tag)
	}
	return f.data[table.offset:end], nil
}

// validateDirectory 核对目录、表校验和、尾部填充及表范围重叠，不验证表内容或数字签名
// 返回: []fontIssue 按表标识稳定排序的封装问题
func (f *fontFace) validateDirectory() []fontIssue {
	var work uint64
	if !f.collection {
		work = uint64(len(f.data))
	}
	for _, table := range f.tables {
		if uint64(table.offset)+uint64(table.length) <= uint64(len(f.data)) {
			work += uint64(table.length)
		}
	}
	return f.validateDirectoryChecksums(newFontChecksums(f.data, work))
}

// validateDirectoryChecksums 共用同一字体资源的校验和索引，目录、范围和填充仍逐字体面核对
// 入参: checksums 当前字体资源的只读求和视图
// 返回: []fontIssue 按表标识排序的封装问题
func (f *fontFace) validateDirectoryChecksums(checksums fontChecksums) []fontIssue {
	issues := append([]fontIssue(nil), f.issues...)
	tags := make([]string, 0, len(f.tables))
	for tag := range f.tables {
		tags = append(tags, tag)
	}
	slices.Sort(tags)
	for _, tag := range tags {
		table := f.tables[tag]
		data, err := f.table(tag)
		if err != nil {
			issues = append(issues, fontIssue{table: tag, message: err.Error()})
			continue
		}
		checksum := checksums.rangeSum(int(table.offset), int(uint64(table.offset)+uint64(table.length)))
		if tag == "head" && len(data) >= 12 {
			checksum -= binary.BigEndian.Uint32(data[8:])
		}
		if checksum != table.checksum {
			issues = append(issues, fontIssue{table: tag, message: "table checksum mismatch"})
		}
		end := uint64(table.offset) + uint64(table.length)
		padded := (end + 3) &^ uint64(3)
		if padded > uint64(len(f.data)) {
			issues = append(issues, fontIssue{table: tag, message: "missing table padding"})
		} else {
			for _, value := range f.data[end:padded] {
				if value != 0 {
					issues = append(issues, fontIssue{table: tag, message: "nonzero table padding"})
					break
				}
			}
		}
	}
	slices.SortFunc(tags, func(a, b string) int {
		left, right := f.tables[a].offset, f.tables[b].offset
		if left < right {
			return -1
		}
		if left > right {
			return 1
		}
		return cmp.Compare(a, b)
	})
	end := uint64(0)
	for _, tag := range tags {
		table := f.tables[tag]
		if table.length == 0 {
			continue
		}
		if uint64(table.offset) < end {
			issues = append(issues, fontIssue{table: tag, message: "overlapping font tables"})
		}
		end = max(end, uint64(table.offset)+uint64(table.length))
	}
	if !f.collection && checksums.rangeSum(0, len(f.data)) != 0xb1b0afba {
		issues = append(issues, fontIssue{message: "font checksum adjustment mismatch"})
	}
	slices.SortStableFunc(issues, func(a, b fontIssue) int {
		if a.table < b.table {
			return -1
		}
		if a.table > b.table {
			return 1
		}
		return 0
	})
	return issues
}

// newFontChecksums 按预计扫描量按需构建分块校验和前缀索引
// 入参: data 只读字体数据, work 所有有效表及独立字体整文件校验的总字节数
// 返回: fontChecksums 本次校验专用的求和视图
func newFontChecksums(data []byte, work uint64) fontChecksums {
	s := fontChecksums{data: data}
	if work <= 2*uint64(len(data)) {
		return s
	}
	s.prefix = make([][4]uint32, len(data)/fontChecksumBlock+1)
	var sum [4]uint32
	for block := 1; block < len(s.prefix); block++ {
		for i := (block - 1) * fontChecksumBlock; i < block*fontChecksumBlock; i += 4 {
			sum[0] += uint32(data[i])
			sum[1] += uint32(data[i+1])
			sum[2] += uint32(data[i+2])
			sum[3] += uint32(data[i+3])
		}
		s.prefix[block] = sum
	}
	return s
}

// lanes 返回结束位置之前按绝对字节位置模四累加的前缀值
// 入参: end 已校验且不超过输入长度的结束位置
// 返回: [4]uint32 四路模二的三十二次方字节和
func (s fontChecksums) lanes(end int) [4]uint32 {
	block := end / fontChecksumBlock
	sum := s.prefix[block]
	for i := block * fontChecksumBlock; i < end; i++ {
		sum[i&3] += uint32(s.data[i])
	}
	return sum
}

// rangeSum 计算已校验半开区间的校验和，尾部只作逻辑补零
// 入参: start 相对完整字体部件的区间起点, end 相对完整字体部件的区间终点
// 返回: uint32 以区间起点为四字节边界的校验和
func (s fontChecksums) rangeSum(start, end int) uint32 {
	if len(s.prefix) == 0 || start/fontChecksumBlock == end/fontChecksumBlock {
		return fontChecksum(s.data[start:end])
	}
	left, right := s.lanes(start), s.lanes(end)
	var sum uint32
	for i := range 4 {
		lane := (start + i) & 3
		sum += (right[lane] - left[lane]) << uint(24-8*i)
	}
	return sum
}

// fontChecksum 按大端四字节求和，最后不足四字节时补零
// 入参: data 待计算数据
// 返回: uint32 模二的三十二次方校验和
func fontChecksum(data []byte) uint32 {
	var sum uint32
	for len(data) >= 4 {
		sum += binary.BigEndian.Uint32(data)
		data = data[4:]
	}
	for i, value := range data {
		sum += uint32(value) << (24 - uint(i)*8)
	}
	return sum
}

// fontEmbeddingRights 按OS/2版本校验并解析生效的字体嵌入许可与限制位
// 入参: metrics 已解析的OS/2表
// 返回: uint16 生效的嵌入许可和限制位, error 保留位或互斥规则错误
func fontEmbeddingRights(metrics *fontOS2Metrics) (uint16, error) {
	rights := metrics.fsType
	if metrics.version <= 1 {
		rights &= 0xf
	}
	if rights&0xfcf1 != 0 {
		return 0, fmt.Errorf("%w: reserved font embedding flags", ErrInvalid)
	}
	permission := rights & 0xe
	if metrics.version >= 3 && bits.OnesCount16(permission) > 1 {
		return 0, fmt.Errorf("%w: mutually exclusive font embedding levels", ErrInvalid)
	}
	if permission&8 != 0 {
		permission = 8
	} else if permission&4 != 0 {
		permission = 4
	}
	return rights&0x300 | permission, nil
}

// validateCreated 校验生产者字体封装和元数据，共享集合校验索引，每个字体面仅检查一次
// 入参: key 字体部件及集合索引, face 本次缓存中的只读字体面
// 返回: error 封装、元数据或格式能力错误
func (c *fontCache) validateCreated(key fontCacheKey, face *fontFace) error {
	if c.created[key] {
		return nil
	}
	if err := validateCreatedFontMetadata(face); err != nil {
		return err
	}
	checksums, reused := c.checksums[key.part]
	if !reused {
		checksums = fontChecksums{data: face.data}
	} else if face.collection && len(checksums.prefix) == 0 {
		checksums = newFontChecksums(face.data, 2*uint64(len(face.data))+1)
	}
	if issues := face.validateDirectoryChecksums(checksums); len(issues) != 0 {
		return fmt.Errorf("%w: producer font directory %s: %s", ErrInvalid, issues[0].table, issues[0].message)
	}
	if c.checksums == nil {
		c.checksums = make(map[string]fontChecksums)
	}
	if c.created == nil {
		c.created = make(map[fontCacheKey]bool)
	}
	c.checksums[key.part], c.created[key] = checksums, true
	return nil
}

// load 按字体预算加载并缓存解混淆后的只读字体访问器，同集合字体面共享底层数据
// 入参: glyphs 已解析并绑定字体部件的字形元素
// 返回: *fontSource 只读字体访问器, error 字体或资源预算错误
func (c *fontCache) load(glyphs *Glyphs) (*fontSource, error) {
	part, err := opcPartName(glyphs.FontPart)
	if err != nil {
		return nil, err
	}
	key := fontCacheKey{strings.ToLower(part), glyphs.CollectionIndex}
	if face := c.faces[key]; face != nil {
		return face, nil
	}
	if len(c.faces) >= c.maxFaces {
		return nil, fmt.Errorf("%w: font face budget", ErrLimit)
	}
	var face *fontFace
	if data, ok := c.data[key.part]; ok {
		face, err = parseFontFace(data, key.index)
	} else {
		var size uint64
		size, err = c.pkg.partSize(key.part)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if c.remaining < 0 || size > uint64(c.remaining) {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: font byte budget", ErrLimit)}
		}
		face, err = c.pkg.readFontFaceLimit(part, key.index, c.remaining)
		if err == nil {
			c.remaining -= int64(len(face.data))
			c.data[key.part] = face.data
		}
	}
	if err != nil {
		if problem, ok := err.(*PartError); ok && strings.EqualFold(problem.Part, part) {
			return nil, err
		}
		return nil, &PartError{Part: part, Err: err}
	}
	source, err := newFontSource(face)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	c.faces[key] = source
	return source, nil
}

// String 返回字体嵌入许可级别的文本表示
// 返回: string 嵌入许可名称
func (p FontEmbeddingPermission) String() string {
	switch p {
	case FontEmbeddingUnknown:
		return "Unknown"
	case FontEmbeddingInstallable:
		return "Installable"
	case FontEmbeddingRestricted:
		return "Restricted"
	case FontEmbeddingPreviewPrint:
		return "PreviewPrint"
	case FontEmbeddingEditable:
		return "Editable"
	default:
		return fmt.Sprintf("FontEmbeddingPermission(%d)", p)
	}
}

// Font 按包内字体URI读取并解析字体资源，支持ODTTF自动解混淆及TTC集合索引片段
// 入参: ctx 取消Context，nil采用Background, fontURI 相对或包根字体URI，可附#index集合索引
// 返回: *FontResource 独立只读字体资源, error URI、读取、格式、权限或取消错误
func (r *Reader) Font(ctx context.Context, fontURI string) (*FontResource, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	partURI, collectionIndex, hasCollectionIndex, err := ParseFontURI(strings.Trim(fontURI, " \t\r\n"))
	if err != nil {
		return nil, err
	}
	part, err := resolvePart("/", partURI)
	if err != nil {
		return nil, err
	}
	face, obfuscated, err := r.pkg.readFontFaceInfo(part, collectionIndex, r.pkg.limits.MaxPartBytes)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	source, err := newFontSource(face)
	if err != nil {
		return nil, &PartError{Part: part, Err: err}
	}
	fsType, permission, _ := fontResourceEmbedding(source.metrics.os2)
	familyName, postScriptName := fontResourceNames(face)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return &FontResource{
		Part:                part,
		CollectionIndex:     collectionIndex,
		HasCollectionIndex:  hasCollectionIndex,
		Obfuscated:          obfuscated,
		IsCollection:        face.collection,
		IsCFF:               face.cff,
		FamilyName:          familyName,
		PostScriptName:      postScriptName,
		Data:                bytes.Clone(face.data),
		UnitsPerEm:          source.metrics.unitsPerEm,
		Ascender:            source.metrics.hhea.ascender,
		Descender:           source.metrics.hhea.descender,
		GlyphCount:          int(source.metrics.numGlyphs),
		EmbeddingPermission: fsType,
		Permission:          permission,
		source:              source,
	}, nil
}

// IsRestricted 报告字体是否禁止编辑、禁止子集化或禁止矢量轮廓嵌入
// 返回: bool 是否受限，nil资源返回false
func (f *FontResource) IsRestricted() bool {
	if f == nil {
		return false
	}
	if f.source != nil && f.source.metrics != nil {
		_, _, restricted := fontResourceEmbedding(f.source.metrics.os2)
		return restricted
	}
	if f.Permission == FontEmbeddingRestricted || f.Permission == FontEmbeddingPreviewPrint {
		return true
	}
	return f.EmbeddingPermission&0x302 != 0
}

// GlyphOutline 提取指定字形在设计单位下的矢量轮廓几何，纵轴向上且已按水平原点归一化
// 入参: glyph 字形编号
// 返回: *Geometry 独立轮廓几何, error 索引、格式或不支持的轮廓类型错误
func (f *FontResource) GlyphOutline(glyph uint16) (*Geometry, error) {
	if f == nil || f.source == nil {
		return nil, fmt.Errorf("%w: empty font resource", ErrInvalid)
	}
	outline, err := f.source.glyphOutline(glyph)
	if err != nil {
		return nil, err
	}
	return &outline, nil
}

// GlyphAdvance 返回指定字形以em为单位归一化的水平步进宽度
// 入参: glyph 字形编号
// 返回: float64 归一化水平步进宽度，即原始设计步进除以UnitsPerEm, error 空资源或字形越界错误
func (f *FontResource) GlyphAdvance(glyph uint16) (float64, error) {
	if f == nil || f.source == nil || f.source.metrics == nil || f.UnitsPerEm == 0 {
		return 0, fmt.Errorf("%w: empty font resource", ErrInvalid)
	}
	advance, _, err := f.source.metrics.horizontal(glyph)
	if err != nil {
		return 0, err
	}
	return float64(advance) / float64(f.UnitsPerEm), nil
}

// GlyphVerticalAdvance 返回指定字形以em为单位归一化的竖向步进高度，缺vmtx表时回落至OS/2或hhea升降部之和
// 入参: glyph 字形编号
// 返回: float64 归一化竖向步进高度，即原始设计步进除以UnitsPerEm, error 空资源、字形越界或无效度量错误
func (f *FontResource) GlyphVerticalAdvance(glyph uint16) (float64, error) {
	if f == nil || f.source == nil || f.source.metrics == nil || f.UnitsPerEm == 0 {
		return 0, fmt.Errorf("%w: empty font resource", ErrInvalid)
	}
	advance, err := f.source.metrics.verticalAdvance(glyph)
	if err != nil {
		return 0, err
	}
	return float64(advance) / float64(f.UnitsPerEm), nil
}

// RuneGlyph 按字体选定的cmap表查找Unicode码点对应的非零字形编号
// 入参: r Unicode码点
// 返回: uint16 字形编号, bool 是否命中有效非零字形
func (f *FontResource) RuneGlyph(r rune) (uint16, bool) {
	if f == nil || f.source == nil {
		return 0, false
	}
	gid, err := f.source.glyphIndex(r)
	if err != nil || gid == 0 {
		return 0, false
	}
	return gid, true
}

// fontResourceEmbedding 提取OS/2原始fsType标志并归类嵌入许可级别及受限状态
// 入参: os2 已解析的OS/2度量，无OS/2表时为nil
// 返回: uint16 原始fsType标志, FontEmbeddingPermission 许可级别, bool 是否禁止编辑、子集化或矢量轮廓嵌入
func fontResourceEmbedding(os2 *fontOS2Metrics) (uint16, FontEmbeddingPermission, bool) {
	if os2 == nil {
		return 0, FontEmbeddingInstallable, false
	}
	rights, err := fontEmbeddingRights(os2)
	if err != nil || rights&0x202 != 0 {
		return os2.fsType, FontEmbeddingRestricted, true
	}
	switch rights & 0xe {
	case 4:
		return os2.fsType, FontEmbeddingPreviewPrint, true
	case 8:
		return os2.fsType, FontEmbeddingEditable, rights&0x100 != 0
	default:
		return os2.fsType, FontEmbeddingInstallable, rights&0x100 != 0
	}
}

// fontIsBitmapOnly 判断字体面是否为含位图表且不含可缩放轮廓表的纯位图字体
// 入参: face 已解析的字体面
// 返回: bool 是否为纯位图字体
func fontIsBitmapOnly(face *fontFace) bool {
	if face == nil || face.cff {
		return false
	}
	_, hasGlyf := face.tables["glyf"]
	_, hasLoca := face.tables["loca"]
	_, hasCFF := face.tables["CFF "]
	_, hasCFF2 := face.tables["CFF2"]
	if hasGlyf || hasLoca || hasCFF || hasCFF2 {
		return false
	}
	_, hasEBLC := face.tables["EBLC"]
	_, hasEBDT := face.tables["EBDT"]
	return hasEBLC || hasEBDT
}

// fontResourceNames 从SFNT名称表提取字体家族名与PostScript名称，表缺失或损坏时返回空字符串
// 入参: face 已解析的字体面
// 返回: string 字体家族名, string PostScript名称
func fontResourceNames(face *fontFace) (string, string) {
	if face == nil {
		return "", ""
	}
	data, err := face.table("name")
	if err != nil || len(data) < 6 {
		return "", ""
	}
	format := binary.BigEndian.Uint16(data)
	if format != 0 && format != 1 {
		return "", ""
	}
	count := int(binary.BigEndian.Uint16(data[2:]))
	storage := int(binary.BigEndian.Uint16(data[4:]))
	end := 6 + 12*count
	headerEnd := end
	if format == 1 {
		if end+2 > len(data) {
			return "", ""
		}
		headerEnd = end + 2 + 4*int(binary.BigEndian.Uint16(data[end:]))
	}
	if headerEnd > len(data) || storage < headerEnd || storage > len(data) {
		return "", ""
	}
	var family, typoFamily, postScript string
	familyRank, typoRank, psRank := 0, 0, 0
	for offset := 6; offset < end; offset += 12 {
		platform := binary.BigEndian.Uint16(data[offset:])
		encoding := binary.BigEndian.Uint16(data[offset+2:])
		language := binary.BigEndian.Uint16(data[offset+4:])
		nameID := binary.BigEndian.Uint16(data[offset+6:])
		if nameID != 1 && nameID != 6 && nameID != 16 {
			continue
		}
		length := int(binary.BigEndian.Uint16(data[offset+8:]))
		start := int(binary.BigEndian.Uint16(data[offset+10:]))
		if start > len(data)-storage || length > len(data)-storage-start {
			continue
		}
		text, rank := decodeFontNameRecord(platform, encoding, language, data[storage+start:storage+start+length])
		if rank == 0 || text == "" {
			continue
		}
		switch nameID {
		case 1:
			if rank > familyRank {
				family, familyRank = text, rank
			}
		case 16:
			if rank > typoRank {
				typoFamily, typoRank = text, rank
			}
		case 6:
			if rank > psRank {
				postScript, psRank = text, rank
			}
		}
	}
	if family == "" {
		family = typoFamily
	}
	return family, postScript
}

// decodeFontNameRecord 按平台与编码解码单条OpenType名称记录并返回匹配优先级
// 入参: platform 平台标识, encoding 编码标识, language 语言标识, raw 原始字节切片
// 返回: string 解码后的非空名称, int 优先级分值，不支持的编码返回0
func decodeFontNameRecord(platform, encoding, language uint16, raw []byte) (string, int) {
	if len(raw) == 0 {
		return "", 0
	}
	switch platform {
	case 3:
		if encoding != 0 && encoding != 1 && encoding != 10 || len(raw)%2 != 0 {
			return "", 0
		}
		rank := 3
		if language == 0x0409 {
			rank = 4
		}
		return decodeFontNameUTF16BE(raw), rank
	case 0:
		if len(raw)%2 != 0 {
			return "", 0
		}
		return decodeFontNameUTF16BE(raw), 2
	case 1:
		if encoding != 0 {
			return "", 0
		}
		var b strings.Builder
		b.Grow(len(raw))
		for _, c := range raw {
			if c == 0 {
				continue
			}
			if c < 0x80 {
				b.WriteByte(c)
			} else {
				b.WriteRune(fontCmapMacRoman[c-0x80])
			}
		}
		rank := 1
		if language == 0 {
			rank = 2
		}
		return strings.TrimSpace(b.String()), rank
	default:
		return "", 0
	}
}

// decodeFontNameUTF16BE 将大端UTF-16名称字节解码为清理空字符后的UTF-8字符串
// 入参: raw 偶数长度的UTF-16BE字节切片
// 返回: string 解码并去首尾空白后的字符串
func decodeFontNameUTF16BE(raw []byte) string {
	units := make([]uint16, len(raw)/2)
	for i := range units {
		units[i] = binary.BigEndian.Uint16(raw[2*i:])
	}
	var b strings.Builder
	for _, r := range utf16.Decode(units) {
		if r == 0 {
			continue
		}
		b.WriteRune(r)
	}
	return strings.TrimSpace(b.String())
}

// ParseFontURI 分离包内字体URI与TrueType Collection的零基字体索引，拒绝外部地址、查询与空片段
// 入参: fontURI XML解码后的相对URI或包内绝对路径
// 返回: string 保留转义的部件URI, uint32 集合索引，省略时为零, bool 是否显式指定索引, error 错误信息
func ParseFontURI(fontURI string) (partURI string, collectionIndex uint32, hasCollectionIndex bool, err error) {
	for _, r := range fontURI {
		if r <= ' ' || r == '\\' || r == 0x7f {
			return "", 0, false, fmt.Errorf("%w: invalid whitespace or character in font URI", ErrInvalid)
		}
	}
	u, err := url.Parse(fontURI)
	if err != nil {
		return "", 0, false, fmt.Errorf("%w: invalid font URI: %w", ErrInvalid, err)
	}
	if u.Scheme != "" || u.Host != "" || u.User != nil || u.Opaque != "" || u.RawQuery != "" || u.ForceQuery || u.Path == "" || strings.HasSuffix(u.Path, "/") {
		return "", 0, false, fmt.Errorf("%w: font URI must reference a package part", ErrInvalid)
	}
	partURI, _, hasCollectionIndex = strings.Cut(fontURI, "#")
	if !hasCollectionIndex {
		return partURI, 0, false, nil
	}
	if !glyphDecimalDigits(u.Fragment) {
		return "", 0, false, fmt.Errorf("%w: font collection index must be a nonnegative decimal integer", ErrInvalid)
	}
	index, err := strconv.ParseUint(u.Fragment, 10, 32)
	if err != nil {
		return "", 0, false, fmt.Errorf("%w: font collection index out of range: %w", ErrInvalid, err)
	}
	return partURI, uint32(index), true, nil
}

// FontObfuscationKey 从字体部件GUID名称生成16字节混淆XOR密钥，不限制GUID版本
// 入参: fontURI 末段为8-4-4-4-12十六进制GUID的字体URI，可附扩展名及集合索引
// 返回: [16]byte 规范字节顺序的XOR密钥, error 错误信息
func FontObfuscationKey(fontURI string) ([16]byte, error) {
	var key [16]byte
	partURI, _, _, err := ParseFontURI(fontURI)
	if err != nil {
		return key, err
	}
	u, err := url.Parse(partURI)
	if err != nil {
		return key, fmt.Errorf("%w: invalid font part URI: %w", ErrInvalid, err)
	}
	name := path.Base(u.Path)
	if len(name) > 36 {
		if name[36] != '.' || len(name) == 37 {
			return key, fmt.Errorf("%w: invalid GUID font extension", ErrInvalid)
		}
		name = name[:36]
	}
	if len(name) != 36 || name[8] != '-' || name[13] != '-' || name[18] != '-' || name[23] != '-' {
		return key, fmt.Errorf("%w: font part name must contain an 8-4-4-4-12 GUID", ErrInvalid)
	}
	var bytes [16]byte
	compact := name[:8] + name[9:13] + name[14:18] + name[19:23] + name[24:]
	if _, err := hex.Decode(bytes[:], []byte(compact)); err != nil {
		return key, fmt.Errorf("%w: invalid font GUID: %w", ErrInvalid, err)
	}
	for i := range key {
		key[i] = bytes[len(bytes)-1-i]
	}
	return key, nil
}

// ObfuscateFont 混淆字体数据的前32字节并返回独立副本，不修改输入数据
// 入参: fontURI 含GUID名称的字体URI, data 至少包含32字节的字体数据
// 返回: []byte 独立的混淆数据副本, error 错误信息
func ObfuscateFont(fontURI string, data []byte) ([]byte, error) {
	return xorFontHeader(fontURI, data)
}

// DeobfuscateFont 解除字体数据前32字节的混淆并返回独立副本，不修改输入数据
// 入参: fontURI 含GUID名称的字体URI, data 至少包含32字节的混淆字体数据
// 返回: []byte 独立的解混淆数据副本, error 错误信息
func DeobfuscateFont(fontURI string, data []byte) ([]byte, error) {
	return xorFontHeader(fontURI, data)
}

// xorFontHeader 实现两次相同密钥的字体头部XOR运算
// 入参: fontURI 字体URI, data 原始数据
// 返回: []byte 转换后的独立副本, error 错误信息
func xorFontHeader(fontURI string, data []byte) ([]byte, error) {
	if len(data) < 32 {
		return nil, fmt.Errorf("%w: font data must contain at least 32 bytes", ErrInvalid)
	}
	key, err := FontObfuscationKey(fontURI)
	if err != nil {
		return nil, err
	}
	result := make([]byte, len(data))
	copy(result, data)
	for i := 0; i < 32; i++ {
		result[i] ^= key[i%len(key)]
	}
	return result, nil
}

// validateCreatedFontMetadata 校验生产者字体的必需表、基础度量及名称表结构，不解码轮廓或字符映射
// 入参: face 已定位的只读字体面
// 返回: error 缺表、结构错误或尚未支持的元数据格式
func validateCreatedFontMetadata(face *fontFace) error {
	_, err := validateCreatedFontMetrics(face, nil)
	return err
}

// validateCreatedFontMetrics 校验生产者字体必需表与元数据并返回基础度量，可复用已解析的OS/2避免重复解析
// 入参: face 已定位的只读字体面, os2 可选已解析OS/2度量，nil时内部解析
// 返回: *fontMetrics 已校验基础字体度量, error 缺表、结构错误或尚未支持的元数据格式
func validateCreatedFontMetrics(face *fontFace, os2 *fontOS2Metrics) (*fontMetrics, error) {
	for _, table := range []struct {
		tag     string
		minimum int
	}{{"cmap", 4}, {"head", 54}, {"hhea", 36}, {"hmtx", 4}, {"maxp", 6}, {"name", 6}, {"OS/2", 2}, {"post", 32}} {
		if _, err := fontMetricsTable(face, table.tag, table.minimum); err != nil {
			return nil, err
		}
	}
	cmap, _ := face.table("cmap")
	if binary.BigEndian.Uint16(cmap) != 0 {
		return nil, fmt.Errorf("%w: cmap metadata version", ErrUnsupported)
	}
	count := int(binary.BigEndian.Uint16(cmap[2:]))
	end := 4 + 8*count
	if count == 0 || end > len(cmap) {
		return nil, fmt.Errorf("%w: cmap encoding records", ErrInvalid)
	}
	for offset := 4; offset < end; offset += 8 {
		start := uint64(binary.BigEndian.Uint32(cmap[offset+4:]))
		if start < uint64(end) || start+2 > uint64(len(cmap)) {
			return nil, fmt.Errorf("%w: cmap encoding offset", ErrInvalid)
		}
	}
	metrics, err := parseFontMetricsWithOS2(face, os2)
	if err != nil {
		return nil, err
	}
	name, _ := face.table("name")
	if err := validateCreatedFontNames(name); err != nil {
		return nil, err
	}
	post, _ := face.table("post")
	if err := validateCreatedFontPost(post, metrics.numGlyphs, face.cff); err != nil {
		return nil, err
	}
	return metrics, nil
}

// validateCreatedFontNames 校验格式0或1名称记录的排序、语言标签表及字符串范围，允许记录共用字符串
// 入参: data 完整name表
// 返回: error 截断、排序、范围或格式错误
func validateCreatedFontNames(data []byte) error {
	if len(data) < 6 {
		return fmt.Errorf("%w: truncated name header", ErrInvalid)
	}
	format := binary.BigEndian.Uint16(data)
	if format != 0 && format != 1 {
		return fmt.Errorf("%w: name table format", ErrUnsupported)
	}
	end := 6 + 12*int(binary.BigEndian.Uint16(data[2:]))
	storage := int(binary.BigEndian.Uint16(data[4:]))
	headerEnd, langTags := end, 0
	if format == 1 {
		if end+2 > len(data) {
			return fmt.Errorf("%w: truncated name language tag count", ErrInvalid)
		}
		langTags = int(binary.BigEndian.Uint16(data[end:]))
		headerEnd = end + 2 + 4*langTags
	}
	if headerEnd > len(data) || storage < headerEnd || storage > len(data) {
		return fmt.Errorf("%w: name records or string storage", ErrInvalid)
	}
	for offset := 6; offset < end; offset += 12 {
		if offset > 6 && bytes.Compare(data[offset-12:offset-4], data[offset:offset+8]) > 0 {
			return fmt.Errorf("%w: name record ordering", ErrInvalid)
		}
		if format == 1 {
			if language := binary.BigEndian.Uint16(data[offset+4:]); language >= 0x8000 && int(language-0x8000) >= langTags {
				return fmt.Errorf("%w: name language tag index", ErrInvalid)
			}
		}
		length := int(binary.BigEndian.Uint16(data[offset+8:]))
		start := int(binary.BigEndian.Uint16(data[offset+10:]))
		if start > len(data)-storage || length > len(data)-storage-start {
			return fmt.Errorf("%w: name string range", ErrInvalid)
		}
	}
	if format == 1 {
		for offset := end + 2; offset < headerEnd; offset += 4 {
			length := int(binary.BigEndian.Uint16(data[offset:]))
			start := int(binary.BigEndian.Uint16(data[offset+2:]))
			if start > len(data)-storage || length > len(data)-storage-start {
				return fmt.Errorf("%w: name language tag string range", ErrInvalid)
			}
		}
	}
	return nil
}

// validateCreatedFontPost 校验post表的格式版本、字形数、名称索引及自定义名称范围
// 入参: data 完整post表, glyphs maxp声明的字形数, cff 是否使用CFF轮廓
// 返回: error 截断、索引、字形数量或格式错误
func validateCreatedFontPost(data []byte, glyphs uint16, cff bool) error {
	if len(data) < 32 {
		return fmt.Errorf("%w: truncated post header", ErrInvalid)
	}
	version := binary.BigEndian.Uint32(data)
	switch version {
	case 0x00010000, 0x00020000, 0x00025000, 0x00030000:
	default:
		return fmt.Errorf("%w: post table format %#x", ErrUnsupported, version)
	}
	if cff && version != 0x00030000 {
		return fmt.Errorf("%w: CFF requires post format 3", ErrInvalid)
	}
	if version == 0x00010000 || version == 0x00030000 {
		if len(data) != 32 || version == 0x00010000 && glyphs != 258 {
			return fmt.Errorf("%w: post header-only format or glyph count", ErrInvalid)
		}
		return nil
	}
	if len(data) < 34 || binary.BigEndian.Uint16(data[32:]) != glyphs {
		return fmt.Errorf("%w: post glyph count", ErrInvalid)
	}
	if version == 0x00025000 {
		if len(data) != 34+int(glyphs) {
			return fmt.Errorf("%w: post format 2.5 offsets", ErrInvalid)
		}
		for i, offset := range data[34:] {
			index := i + int(int8(offset))
			if index < 0 || index >= 258 {
				return fmt.Errorf("%w: post format 2.5 standard name index", ErrInvalid)
			}
		}
		return nil
	}
	end := 34 + 2*int(glyphs)
	if end > len(data) {
		return fmt.Errorf("%w: truncated post name indices", ErrInvalid)
	}
	required := 0
	for offset := 34; offset < end; offset += 2 {
		index := int(binary.BigEndian.Uint16(data[offset:]))
		if index >= 32768 {
			return fmt.Errorf("%w: reserved post name index", ErrInvalid)
		}
		required = max(required, index-257)
	}
	names := 0
	for offset := end; offset < len(data); names++ {
		length := int(data[offset])
		offset++
		if length > len(data)-offset {
			return fmt.Errorf("%w: truncated post custom name", ErrInvalid)
		}
		offset += length
	}
	if names < required {
		return fmt.Errorf("%w: post custom name index exceeds string array", ErrInvalid)
	}
	return nil
}

// parseFontMetrics 解析字体共用度量及兼容版本扩展，输入字体数据在使用期间不得修改
// 入参: face 已完成目录范围校验的字体面
// 返回: *fontMetrics 字体度量, error 表结构或版本错误
func parseFontMetrics(face *fontFace) (*fontMetrics, error) {
	return parseFontMetricsWithOS2(face, nil)
}

// parseFontMetricsWithOS2 解析字体共用度量，支持复用调用方已解析的OS/2度量避免重复解码
// 入参: face 已完成目录范围校验的字体面, os2 可选已解析OS/2度量，nil时按需解析
// 返回: *fontMetrics 字体度量, error 表结构或版本错误
func parseFontMetricsWithOS2(face *fontFace, os2 *fontOS2Metrics) (*fontMetrics, error) {
	head, err := fontMetricsTable(face, "head", 54)
	if err != nil {
		return nil, err
	}
	if binary.BigEndian.Uint32(head)>>16 != 1 {
		return nil, fmt.Errorf("%w: head version", ErrUnsupported)
	}
	if binary.BigEndian.Uint32(head[12:]) != 0x5f0f3cf5 {
		return nil, fmt.Errorf("%w: head magic number", ErrInvalid)
	}
	m := &fontMetrics{
		unitsPerEm: binary.BigEndian.Uint16(head[18:]),
	}
	if m.unitsPerEm < 16 || m.unitsPerEm > 16384 {
		return nil, fmt.Errorf("%w: head unitsPerEm %d", ErrInvalid, m.unitsPerEm)
	}
	maxp, err := fontMetricsTable(face, "maxp", 6)
	if err != nil {
		return nil, err
	}
	version := binary.BigEndian.Uint32(maxp)
	major := version >> 16
	if major > 1 || major == 0 && version < 0x00005000 {
		return nil, fmt.Errorf("%w: maxp version %#x", ErrUnsupported, version)
	}
	if face.cff != (major == 0) || major == 1 && len(maxp) < 32 {
		return nil, fmt.Errorf("%w: maxp format or length", ErrInvalid)
	}
	m.numGlyphs = binary.BigEndian.Uint16(maxp[4:])
	if m.numGlyphs == 0 {
		return nil, fmt.Errorf("%w: maxp has no glyphs", ErrInvalid)
	}
	m.hhea, m.hmtx, err = parseFontMetricAxis(face, "hhea", "hmtx", m.numGlyphs)
	if err != nil {
		return nil, err
	}
	_, hasVhea := face.tables["vhea"]
	_, hasVmtx := face.tables["vmtx"]
	if hasVhea != hasVmtx {
		return nil, fmt.Errorf("%w: vhea and vmtx must occur together", ErrInvalid)
	}
	if hasVhea {
		var header fontMetricHeader
		header, m.vmtx, err = parseFontMetricAxis(face, "vhea", "vmtx", m.numGlyphs)
		if err != nil {
			return nil, err
		}
		m.vhea = &header
	}
	if os2 != nil {
		m.os2 = os2
	} else if _, exists := face.tables["OS/2"]; exists {
		m.os2, err = parseFontOS2Metrics(face)
		if err != nil {
			return nil, err
		}
	}
	if _, exists := face.tables["VORG"]; face.cff && exists {
		m.vorg, err = parseFontVerticalOrigins(face, m.numGlyphs)
		if err != nil {
			return nil, err
		}
	}
	return m, nil
}

// fontMetricsTable 读取满足最小长度要求的度量表
// 入参: face 字体面, tag 表标识, minimum 最小字节数
// 返回: []byte 只读表数据, error 缺表或截断错误
func fontMetricsTable(face *fontFace, tag string, minimum int) ([]byte, error) {
	data, err := face.table(tag)
	if err != nil {
		return nil, err
	}
	if len(data) < minimum {
		return nil, fmt.Errorf("%w: truncated %s table", ErrInvalid, tag)
	}
	return data, nil
}

// parseFontMetricAxis 解析横竖度量头及压缩度量数组
// 入参: face 字体面, headerTag 度量头标识, metricsTag 度量数组标识, glyphs 字形总数
// 返回: fontMetricHeader 度量头, []byte 只读度量数组, error 表结构错误
func parseFontMetricAxis(face *fontFace, headerTag, metricsTag string, glyphs uint16) (fontMetricHeader, []byte, error) {
	var h fontMetricHeader
	data, err := fontMetricsTable(face, headerTag, 36)
	if err != nil {
		return h, nil, err
	}
	version := binary.BigEndian.Uint32(data)
	if version>>16 != 1 {
		return h, nil, fmt.Errorf("%w: %s version %#x", ErrUnsupported, headerTag, version)
	}
	if binary.BigEndian.Uint16(data[32:]) != 0 {
		return h, nil, fmt.Errorf("%w: %s metricDataFormat", ErrUnsupported, headerTag)
	}
	h.ascender = int16(binary.BigEndian.Uint16(data[4:]))
	h.descender = int16(binary.BigEndian.Uint16(data[6:]))
	h.longMetrics = binary.BigEndian.Uint16(data[34:])
	if h.longMetrics == 0 || h.longMetrics > glyphs {
		return h, nil, fmt.Errorf("%w: %s long metric count %d", ErrInvalid, headerTag, h.longMetrics)
	}
	minimum := 4*int(h.longMetrics) + 2*(int(glyphs)-int(h.longMetrics))
	metrics, err := fontMetricsTable(face, metricsTag, minimum)
	return h, metrics, err
}

// parseFontOS2Metrics 解析OS/2公共字段及兼容扩展，保留原始版本与全部fsType位且不裁决渲染权限
// 入参: face 字体面
// 返回: *fontOS2Metrics 权限与排版度量, error 版本或截断错误
func parseFontOS2Metrics(face *fontFace) (*fontOS2Metrics, error) {
	data, err := fontMetricsTable(face, "OS/2", 2)
	if err != nil {
		return nil, err
	}
	version := binary.BigEndian.Uint16(data)
	minimum := 96
	if version == 0 {
		minimum = 78
	} else if version == 1 {
		minimum = 86
	}
	if len(data) < minimum {
		return nil, fmt.Errorf("%w: truncated OS/2 version %d", ErrInvalid, version)
	}
	return &fontOS2Metrics{
		version:       version,
		fsType:        binary.BigEndian.Uint16(data[8:]),
		typoAscender:  int16(binary.BigEndian.Uint16(data[68:])),
		typoDescender: int16(binary.BigEndian.Uint16(data[70:])),
	}, nil
}

// parseFontVerticalOrigins 校验CFF垂直起点表的版本、范围及严格递增的字形索引
// 入参: face 字体面, glyphs 字形总数
// 返回: []byte 只读VORG数据, error 版本或表结构错误
func parseFontVerticalOrigins(face *fontFace, glyphs uint16) ([]byte, error) {
	data, err := fontMetricsTable(face, "VORG", 8)
	if err != nil {
		return nil, err
	}
	if binary.BigEndian.Uint16(data) != 1 {
		return nil, fmt.Errorf("%w: VORG version", ErrUnsupported)
	}
	count := int(binary.BigEndian.Uint16(data[6:]))
	if len(data) < 8+4*count {
		return nil, fmt.Errorf("%w: truncated VORG records", ErrInvalid)
	}
	var previous uint16
	for i := 0; i < count; i++ {
		gid := binary.BigEndian.Uint16(data[8+4*i:])
		if gid >= glyphs || i > 0 && gid <= previous {
			return nil, fmt.Errorf("%w: VORG glyph index %d", ErrInvalid, gid)
		}
		previous = gid
	}
	return data, nil
}

// horizontal 返回指定字形的原始横向步进宽度及左侧边距
// 入参: gid 字形索引
// 返回: uint16 横向步进宽度, int16 左侧边距, error 字形范围错误
func (m *fontMetrics) horizontal(gid uint16) (advance uint16, bearing int16, err error) {
	if m == nil || gid >= m.numGlyphs {
		return 0, 0, fmt.Errorf("%w: horizontal glyph index %d", ErrInvalid, gid)
	}
	advance, bearing = fontMetricAt(m.hmtx, m.hhea.longMetrics, gid)
	return advance, bearing, nil
}

// vertical 返回指定字形的原始竖向步进高度及顶部边距，不合成缺失的vmtx
// 入参: gid 字形索引
// 返回: uint16 竖向步进高度, int16 顶部边距, error 缺表或字形范围错误
func (m *fontMetrics) vertical(gid uint16) (advance uint16, bearing int16, err error) {
	if m == nil || gid >= m.numGlyphs || m.vhea == nil {
		return 0, 0, fmt.Errorf("%w: missing vertical metrics or invalid glyph index %d", ErrInvalid, gid)
	}
	advance, bearing = fontMetricAt(m.vmtx, m.vhea.longMetrics, gid)
	return advance, bearing, nil
}

// fontMetricAt 从长记录及尾部边距数组读取已校验的单个度量
// 入参: data 度量数组, count 长记录数, gid 字形索引
// 返回: uint16 步进距离, int16 边距
func fontMetricAt(data []byte, count, gid uint16) (uint16, int16) {
	i, n := int(gid), int(count)
	if i < n {
		return binary.BigEndian.Uint16(data[4*i:]), int16(binary.BigEndian.Uint16(data[4*i+2:]))
	}
	return binary.BigEndian.Uint16(data[4*(n-1):]), int16(binary.BigEndian.Uint16(data[4*n+2*(i-n):]))
}

// needsGlyphYMax 判断垂直起点是否需要调用方提供字形顶部，CFF需提供实际曲线极值
// 返回: bool 是否需要字形顶部
func (m *fontMetrics) needsGlyphYMax() bool {
	return m != nil && m.vhea != nil && m.vorg == nil
}

// verticalOrigin 计算未旋转字形的竖向顶部起点
// 入参: gid 字形索引, glyphYMax 字体设计单位的字形顶部，仅needsGlyphYMax为真时使用
// 返回: Point 未缩放且未旋转的顶部起点, error 字形范围或非有限坐标错误
func (m *fontMetrics) verticalOrigin(gid uint16, glyphYMax float64) (Point, error) {
	advance, _, err := m.horizontal(gid)
	if err != nil {
		return Point{}, err
	}
	origin := Point{X: float64(advance) / 2}
	switch {
	case m.vorg != nil:
		origin.Y = float64(int16(binary.BigEndian.Uint16(m.vorg[4:])))
		count := int(binary.BigEndian.Uint16(m.vorg[6:]))
		i := sort.Search(count, func(i int) bool { return binary.BigEndian.Uint16(m.vorg[8+4*i:]) >= gid })
		if i < count && binary.BigEndian.Uint16(m.vorg[8+4*i:]) == gid {
			origin.Y = float64(int16(binary.BigEndian.Uint16(m.vorg[10+4*i:])))
		}
	case m.vhea != nil:
		_, bearing, err := m.vertical(gid)
		if err != nil {
			return Point{}, err
		}
		origin.Y = glyphYMax + float64(bearing)
	case m.os2 != nil:
		origin.Y = float64(m.os2.typoAscender)
	default:
		origin.Y = float64(m.hhea.ascender)
	}
	if math.IsNaN(origin.Y) || math.IsInf(origin.Y, 0) {
		return Point{}, fmt.Errorf("%w: non-finite vertical origin", ErrInvalid)
	}
	return origin, nil
}

// verticalAdvance 计算默认竖向步进高度，优先采用vmtx，否则采用非零OS/2排版上下行高度，若OS/2缺失或sTypoAscender与sTypoDescender均为零则回落hhea且不计行间距
// 入参: gid 字形索引
// 返回: uint16 字体设计单位的步进高度, error 字形范围或负步进高度错误
func (m *fontMetrics) verticalAdvance(gid uint16) (uint16, error) {
	if m == nil || gid >= m.numGlyphs {
		return 0, fmt.Errorf("%w: vertical glyph index %d", ErrInvalid, gid)
	}
	if m.vhea != nil {
		advance, _, err := m.vertical(gid)
		return advance, err
	}
	ascender, descender := int32(m.hhea.ascender), int32(m.hhea.descender)
	if m.os2 != nil && (m.os2.typoAscender != 0 || m.os2.typoDescender != 0) {
		ascender, descender = int32(m.os2.typoAscender), int32(m.os2.typoDescender)
	}
	if descender < 0 {
		descender = -descender
	}
	advance := ascender + descender
	if advance < 0 {
		return 0, fmt.Errorf("%w: negative default vertical advance", ErrInvalid)
	}
	return uint16(advance), nil
}

// resolveGlyphRunWithStep 在每个字形定位前检查调用方预算或取消信号，不改变既有字形顺序与度量
// 入参: glyphs 字形元素, metrics 字体度量, lookup Unicode查询, yMax 字形顶部查询, maxGlyphs 字形上限, step 单步检查，nil不附加检查
// 返回: *glyphRun 完整定位结果, error 结构、回调、资源或取消错误
func resolveGlyphRunWithStep(glyphs *Glyphs, metrics *fontMetrics, lookup func(rune) (uint16, error), yMax func(uint16) (float64, error), maxGlyphs int, step func() error) (*glyphRun, error) {
	count, err := glyphRunCount(glyphs, maxGlyphs)
	if err != nil {
		return nil, err
	}
	if metrics == nil || metrics.unitsPerEm < 16 || metrics.unitsPerEm > 16384 || metrics.numGlyphs == 0 {
		return nil, fmt.Errorf("%w: invalid glyph run font metrics", ErrInvalid)
	}
	run := &glyphRun{rtl: glyphs.BidiLevel&1 != 0, sideways: glyphs.IsSideways}
	switch glyphs.StyleSimulations {
	case "", "None":
	case "BoldSimulation":
		run.bold = true
	case "ItalicSimulation":
		run.italic = true
	case "BoldItalicSimulation":
		run.bold, run.italic = true, true
	default:
		return nil, fmt.Errorf("%w: unknown glyph style simulation", ErrInvalid)
	}
	if run.bold {
		run.boldRadius = float64(metrics.unitsPerEm) / 100
	}
	run.glyphs = make([]positionedGlyph, 0, count)
	scale, metricScale := glyphs.FontRenderingEmSize/float64(metrics.unitsPerEm), glyphs.FontRenderingEmSize/100
	direction := 1.0
	if run.rtl {
		direction = -1
	}
	total, compensation := 0.0, 0.0
	appendGlyph := func(entry GlyphIndex, r rune, start, end, clusterIndex int) error {
		if step != nil {
			if err := step(); err != nil {
				return err
			}
		}
		gid, err := glyphRunIndex(entry, r, metrics.numGlyphs, lookup)
		if err != nil {
			return err
		}
		position := positionedGlyph{gid: gid, cluster: clusterIndex, clusterStart: start, clusterEnd: end, explicitIndex: entry.HasIndex, explicitAdvance: entry.HasAdvanceWidth}
		position.nominal = Point{X: glyphs.Origin.X + direction*total, Y: glyphs.Origin.Y}
		position.origin = position.nominal
		if entry.HasUOffset {
			position.origin.X += direction * entry.UOffset * metricScale
		}
		if entry.HasVOffset {
			position.origin.Y -= entry.VOffset * metricScale
		}
		if err := run.placeGlyph(&position, entry, metrics, scale, metricScale, yMax); err != nil {
			return err
		}
		adjusted := position.advance - compensation
		next := total + adjusted
		compensation = (next - total) - adjusted
		total = next
		endX := glyphs.Origin.X + direction*total
		if !geometryFinite(total, compensation, endX, position.nominal.X, position.origin.X, position.origin.Y) {
			return fmt.Errorf("%w: glyph run position overflow", ErrInvalid)
		}
		run.glyphs = append(run.glyphs, position)
		return nil
	}
	if err := walkGlyphRun(glyphs, appendGlyph); err != nil {
		return nil, err
	}
	return run, nil
}

// walkGlyphRun 遍历已校验的字形簇和剩余文本，统一渲染与字体使用汇总的UTF-16范围
// 入参: glyphs 已通过glyphRunCount的字形序列, visit 字形条目及字符、文本范围和簇序号的访问函数
// 返回: error 访问错误
func walkGlyphRun(glyphs *Glyphs, visit func(GlyphIndex, rune, int, int, int) error) error {
	text := glyphs.Text
	units, clusterIndex := 0, 0
	for _, cluster := range glyphs.Indices {
		start, end := -1, -1
		var first rune
		if glyphs.Text != "" {
			start = units
			first, _ = utf8.DecodeRuneInString(text)
			for remaining := cluster.CodeUnitCount; remaining > 0; {
				r, size := utf8.DecodeRuneInString(text)
				width := 1
				if r > 0xffff {
					width = 2
				}
				remaining -= width
				units += width
				text = text[size:]
			}
			end = units
		}
		for _, entry := range cluster.Glyphs {
			if err := visit(entry, first, start, end, clusterIndex); err != nil {
				return err
			}
		}
		clusterIndex++
	}
	for _, r := range text {
		if err := visit(GlyphIndex{}, r, units, units+1, clusterIndex); err != nil {
			return err
		}
		units++
		clusterIndex++
	}
	return nil
}

// glyphRunIndex 按显式编号或字体Unicode映射选择字形，不进行重塑形或系统字体替换
// 入参: entry 字形条目, character Unicode字符, glyphs 字体字形总数, lookup 字体字符查询
// 返回: uint16 字形编号, error 查询能力或字形范围错误
func glyphRunIndex(entry GlyphIndex, character rune, glyphs uint16, lookup func(rune) (uint16, error)) (uint16, error) {
	gid := entry.Index
	if !entry.HasIndex {
		if lookup == nil {
			return 0, fmt.Errorf("%w: Unicode glyph lookup is unavailable", ErrUnsupported)
		}
		var err error
		gid, err = lookup(character)
		if err != nil {
			return 0, fmt.Errorf("glyph lookup: %w", err)
		}
	}
	if gid >= glyphs {
		return 0, fmt.Errorf("%w: glyph index %d exceeds font glyph count", ErrInvalid, gid)
	}
	return gid, nil
}

// glyphRunCount 校验已解码文本及簇结构，在任何字体回调与输出分配之前确定字形数量
// 入参: glyphs 字形元素, limit 最大输出字形数
// 返回: int 输出字形数量, error 结构、代理对或资源错误
func glyphRunCount(glyphs *Glyphs, limit int) (int, error) {
	if limit <= 0 {
		return 0, fmt.Errorf("%w: glyph run limit must be positive", ErrLimit)
	}
	if glyphs == nil || !geometryFinite(glyphs.FontRenderingEmSize, glyphs.Origin.X, glyphs.Origin.Y) || glyphs.FontRenderingEmSize < 0 || glyphs.BidiLevel < 0 || glyphs.BidiLevel > 61 || glyphs.IsSideways && glyphs.BidiLevel&1 != 0 {
		return 0, fmt.Errorf("%w: invalid glyph run parameters", ErrInvalid)
	}
	if !utf8.ValidString(glyphs.Text) {
		return 0, fmt.Errorf("%w: glyph text is not UTF-8", ErrInvalid)
	}
	remaining, count := glyphs.Text, 0
	for _, cluster := range glyphs.Indices {
		if cluster.CodeUnitCount <= 0 || len(cluster.Glyphs) == 0 || !cluster.HasMapping && (cluster.CodeUnitCount != 1 || len(cluster.Glyphs) != 1 || cluster.HasGlyphCount) || !cluster.HasGlyphCount && len(cluster.Glyphs) != 1 {
			return 0, fmt.Errorf("%w: invalid glyph cluster structure", ErrInvalid)
		}
		if len(cluster.Glyphs) > limit-count {
			return 0, fmt.Errorf("%w: glyph run exceeds %d glyphs", ErrLimit, limit)
		}
		count += len(cluster.Glyphs)
		for _, entry := range cluster.Glyphs {
			if !entry.HasIndex && (glyphs.Text == "" || len(cluster.Glyphs) != 1) || entry.HasAdvanceWidth && (!geometryFinite(entry.AdvanceWidth) || entry.AdvanceWidth < 0) || entry.HasUOffset && !geometryFinite(entry.UOffset) || entry.HasVOffset && !geometryFinite(entry.VOffset) {
				return 0, fmt.Errorf("%w: invalid glyph entry", ErrInvalid)
			}
		}
		if glyphs.Text == "" {
			continue
		}
		scalars := 0
		for units := cluster.CodeUnitCount; units > 0; {
			if remaining == "" {
				return 0, fmt.Errorf("%w: glyph cluster exceeds UTF16 text", ErrInvalid)
			}
			r, size := utf8.DecodeRuneInString(remaining)
			width := 1
			if r > 0xffff {
				width = 2
				if !cluster.HasMapping || units < 2 {
					return 0, fmt.Errorf("%w: supplementary character requires an unsplit explicit cluster", ErrInvalid)
				}
			}
			units -= width
			remaining = remaining[size:]
			scalars++
		}
		if len(cluster.Glyphs) == 1 && !cluster.Glyphs[0].HasIndex && scalars != 1 {
			return 0, fmt.Errorf("%w: cluster glyph index requires a single Unicode scalar", ErrInvalid)
		}
	}
	for _, r := range remaining {
		if r > 0xffff {
			return 0, fmt.Errorf("%w: supplementary character lacks an explicit cluster", ErrInvalid)
		}
		if count == limit {
			return 0, fmt.Errorf("%w: glyph run exceeds %d glyphs", ErrLimit, limit)
		}
		count++
	}
	if count == 0 {
		return 0, fmt.Errorf("%w: glyph run has neither text nor glyph indices", ErrInvalid)
	}
	return count, nil
}

// placeGlyph 计算单字形的逻辑步进和仿射矩阵，不生成或修改字体轮廓
// 入参: p 待填充的定位记录, entry 原始字形条目, metrics 已校验的度量, scale 设计单位缩放, metricScale 百分之一em缩放, yMax 字形顶部查询
// 返回: error 度量、回调或数值溢出错误
func (run *glyphRun) placeGlyph(p *positionedGlyph, entry GlyphIndex, metrics *fontMetrics, scale, metricScale float64, yMax func(uint16) (float64, error)) error {
	var anchor Point
	if run.sideways {
		var top float64
		if metrics.needsGlyphYMax() {
			if yMax == nil {
				return fmt.Errorf("%w: sideways glyph bounds are unavailable", ErrUnsupported)
			}
			var err error
			top, err = yMax(p.gid)
			if err != nil {
				return fmt.Errorf("glyph bounds: %w", err)
			}
		}
		var err error
		anchor, err = metrics.verticalOrigin(p.gid, top)
		if err != nil {
			return err
		}
	} else if run.rtl {
		width, _, err := metrics.horizontal(p.gid)
		if err != nil {
			return err
		}
		anchor.X = float64(width)
	}
	if entry.HasAdvanceWidth {
		p.advance = entry.AdvanceWidth * metricScale
	} else {
		var advance uint16
		var err error
		if run.sideways {
			advance, err = metrics.verticalAdvance(p.gid)
		} else {
			advance, _, err = metrics.horizontal(p.gid)
		}
		if err != nil {
			return err
		}
		p.advance = float64(advance) * scale
		if run.bold {
			p.advance += 2 * metricScale
		}
	}
	shear := 0.0
	if run.italic {
		shear = math.Tan(math.Pi / 9)
	}
	m := Matrix{A: scale, C: scale * shear, D: -scale}
	if run.sideways {
		m = Matrix{B: -scale, C: -scale, D: -scale * shear}
	}
	m.E = p.origin.X - (m.A*anchor.X + m.C*anchor.Y)
	m.F = p.origin.Y - (m.B*anchor.X + m.D*anchor.Y)
	if !geometryFinite(p.advance, m.A, m.B, m.C, m.D, m.E, m.F) {
		return fmt.Errorf("%w: glyph transform or advance overflow", ErrInvalid)
	}
	p.matrix = m
	return nil
}

// FontUsage 汇总所有固定布局及资源字典中的字体与字形使用，遇到未支持保留标记或外部字体时返回错误
// 遍历期间检查ctx取消信号及options资源上限，返回按部件名和字体面索引排序的独立结果
// 入参: ctx 取消Context，nil采用Background, options 累计资源上限，nil采用阅读器上限
// 返回: []FontUsage 按部件名和字体面索引排列的独立结果，失败为nil, error 标记、字体、资源或取消错误
func (r *Reader) FontUsage(ctx context.Context, options *OptimizationOptions) ([]FontUsage, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	configuration := OptimizationOptions{MaxBytes: r.limits.MaxPackageBytes, MaxWork: r.limits.MaxXMLNodes}
	if options != nil {
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
		if options.MaxWork != 0 {
			configuration.MaxWork = options.MaxWork
		}
	}
	if configuration.MaxBytes < 1 || configuration.MaxWork < 1 {
		return nil, fmt.Errorf("%w: font usage limits", ErrInvalid)
	}
	c := fontUsageCollector{reader: r, fonts: fontCache{pkg: r.pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: configuration.MaxBytes, maxFaces: r.limits.MaxPartCount}, usage: make(map[fontCacheKey]map[uint16]bool), work: configuration.MaxWork, context: ctx}
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := c.charge(1); err != nil {
			return nil, err
		}
		part := r.pkg.names[key]
		if key == strings.ToLower(opcTypesName) || opcRelationshipName(part) {
			continue
		}
		media, err := r.pkg.contentType(part)
		if err != nil {
			return nil, err
		}
		model, err := resourceModelMedia(media)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if model {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: font usage in opaque X3D content", ErrUnsupported)}
		}
		markup, err := fontUsageMarkup(media)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if !markup {
			continue
		}
		limit := min(r.limits.MaxMetadataBytes, r.limits.MaxPartBytes, c.fonts.remaining)
		data, err := r.pkg.readItems(key, limit)
		if err != nil {
			return nil, err
		}
		c.fonts.remaining -= int64(len(data))
		root, err := decodeXMLVisit(data, r.limits, func(token xml.Token, node *xmlElement) error {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := c.charge(1); err != nil {
				return err
			}
			return c.element(part, node)
		})
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		namespace := formatNamespace(r.format)
		if _, err := preprocessXMLContext(root, []string{namespace, namespace + "/resourcedictionary-key", structureNamespace(r.format)}, ctx); err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
	}
	var result []FontUsage
	for key, indices := range c.usage {
		result = append(result, FontUsage{Part: r.pkg.names[key.part], CollectionIndex: key.index, Glyphs: slices.Sorted(maps.Keys(indices))})
	}
	slices.SortFunc(result, func(a, b FontUsage) int {
		if compared := strings.Compare(a.Part, b.Part); compared != 0 {
			return compared
		}
		if a.CollectionIndex < b.CollectionIndex {
			return -1
		}
		if a.CollectionIndex > b.CollectionIndex {
			return 1
		}
		return 0
	})
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// charge 在每个读取、节点或字形选择步骤前检查累计工作上限和取消信号
// 入参: count 本次工作量
// 返回: error 工作预算或取消错误
func (c *fontUsageCollector) charge(count int) error {
	if err := checkContext(c.context); err != nil {
		return err
	}
	if count > c.work {
		return fmt.Errorf("%w: font usage work budget", ErrLimit)
	}
	c.work -= count
	return nil
}

// element 校验原始标记的支持范围并汇总字形，不过滤兼容分支或不可见内容
// 入参: part 标记所属部件, node 原始节点
// 返回: error 未理解标记或字形选择错误
func (c *fontUsageCollector) element(part string, node *xmlElement) error {
	if err := validateResourceMarkupElement(node, c.reader.format); err != nil {
		return err
	}
	namespace := formatNamespace(c.reader.format)
	if node.Name != (xml.Name{Space: namespace, Local: "Glyphs"}) {
		return nil
	}
	value := *node
	value.Children = nil
	value.Attr = slices.DeleteFunc(slices.Clone(node.Attr), func(attr xml.Attr) bool { return attr.Name.Space == mcNamespace })
	attrs, err := visualAttributes(&value, c.reader.format)
	if err != nil {
		return err
	}
	if err := validateGlyphAttributes(attrs, c.reader.format); err != nil {
		return err
	}
	uri, face, present, err := ParseFontURI(strings.Trim(attrs["FontUri"], " \t\r\n"))
	if err != nil {
		return err
	}
	fontPart, err := resolvePart(part, uri)
	if err != nil {
		return err
	}
	glyphs := NewGlyphs("", 0, strings.TrimPrefix(attrs["UnicodeString"], "{}"))
	glyphs.FontPart, glyphs.CollectionIndex, glyphs.HasCollectionIndex = fontPart, face, present
	glyphs.FontRenderingEmSize, _ = xmlNumber(attrs["FontRenderingEmSize"])
	glyphs.Indices, _ = ParseGlyphIndices(attrs["Indices"])
	count, err := glyphRunCount(glyphs, c.work)
	if err != nil {
		return err
	}
	font, err := c.fonts.load(glyphs)
	if err != nil {
		return err
	}
	key := fontCacheKey{part: strings.ToLower(fontPart), index: face}
	indices := c.usage[key]
	if indices == nil {
		indices = map[uint16]bool{0: true}
		c.usage[key] = indices
	}
	if err := c.charge(count); err != nil {
		return err
	}
	return walkGlyphRun(glyphs, func(entry GlyphIndex, character rune, start, end, cluster int) error {
		if err := checkContext(c.context); err != nil {
			return err
		}
		gid, err := glyphRunIndex(entry, character, font.metrics.numGlyphs, font.glyphIndex)
		if err != nil {
			return err
		}
		indices[gid] = true
		return nil
	})
}

// fontUsageElement 判断已支持的固定布局元素，不因命名空间已知就忽略未知元素的字形依赖
// 入参: name 元素本地名称
// 返回: bool 是否理解元素类型
func fontUsageElement(name string) bool {
	if resourceKind(name) != "" {
		return true
	}
	if owner, property, present := strings.Cut(name, "."); present && resourcePropertyKind(owner, property) != "" {
		return true
	}
	switch name {
	case "FixedPage", "FixedDocument", "FixedDocumentSequence", "DocumentReference", "PageContent", "PageContent.LinkTargets", "LinkTarget", "FixedPage.Resources", "Canvas.Resources", "ResourceDictionary", "GradientStop", "LinearGradientBrush.GradientStops", "RadialGradientBrush.GradientStops", "PathFigure", "PolyLineSegment", "PolyBezierSegment", "PolyQuadraticBezierSegment", "ArcSegment":
		return true
	}
	return false
}

// fontUsageMarkup 区分字体标记和已知非布局元数据，拒绝猜测自定义XML的字体语义
// 入参: media 部件内容类型
// 返回: bool 是否含布局标记, error 未理解XML部件错误
func fontUsageMarkup(media string) (bool, error) {
	for _, kind := range []string{"fixedpage", "fixeddocument", "fixeddocumentsequence", "documentstructure", "storyfragments"} {
		if strings.EqualFold(media, fixedContentType(kind)) {
			return true, nil
		}
	}
	if strings.EqualFold(media, resourceDictionaryContentType) {
		return true, nil
	}
	for _, known := range []string{opcCoreType, opcSignatureType, printTicketType, "application/vnd.ms-printing.printcapabilities+xml", fixedContentType("signaturedefinitions"), fixedContentType("discard-control")} {
		if strings.EqualFold(media, known) {
			return false, nil
		}
	}
	media = strings.ToLower(media)
	if strings.HasSuffix(media, "+xml") || media == "application/xml" || media == "text/xml" {
		return false, fmt.Errorf("%w: font usage in custom XML content type %q", ErrUnsupported, media)
	}
	return false, nil
}
