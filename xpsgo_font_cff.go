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
	"fmt"
	"math"
	"strconv"
)

// cffMaxDictEntries 等常量限制CFF解析资源上限
const (
	cffMaxDictEntries = 1 << 16
	cffMaxRealBytes   = 4096
)

// cffStandardEncoding 保存CFF标准编码的字符码到SID映射表
var cffStandardEncoding = [256]uint16{
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
	17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
	33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
	49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
	65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
	81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110,
	0, 111, 112, 113, 114, 0, 115, 116, 117, 118, 119, 120, 121, 122, 0, 123,
	0, 124, 125, 126, 127, 128, 129, 130, 131, 0, 132, 133, 0, 134, 135, 136,
	137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 138, 0, 139, 0, 0, 0, 0, 140, 141, 142, 143, 0, 0, 0, 0,
	0, 144, 0, 0, 0, 145, 0, 0, 146, 147, 148, 149, 0, 0, 0, 0,
}

// cffExpertEncoding 保存CFF专家编码的字符码到SID映射表
var cffExpertEncoding = [256]uint16{
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	1, 229, 230, 0, 231, 232, 233, 234, 235, 236, 237, 238, 13, 14, 15, 99,
	239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 27, 28, 249, 250, 251, 252,
	0, 253, 254, 255, 256, 257, 0, 0, 0, 258, 0, 0, 259, 260, 261, 262,
	0, 0, 263, 264, 265, 0, 266, 109, 110, 267, 268, 269, 0, 270, 271, 272,
	273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
	289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 304, 305, 306, 0, 0, 307, 308, 309, 310, 311, 0, 312, 0, 0, 313,
	0, 0, 314, 315, 0, 0, 316, 317, 318, 0, 0, 0, 158, 155, 163, 319,
	320, 321, 322, 323, 324, 325, 0, 0, 326, 150, 164, 169, 327, 328, 329, 330,
	331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346,
	347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362,
	363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
}

// cffExpertCharset 保存CFF专家字符集按GID顺序排列的SID映射表
var cffExpertCharset = [...]uint16{
	0, 1, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 13, 14, 15, 99,
	239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 27, 28, 249, 250, 251, 252,
	253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 109, 110,
	267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282,
	283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298,
	299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314,
	315, 316, 317, 318, 158, 155, 163, 319, 320, 321, 322, 323, 324, 325, 326, 150,
	164, 169, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340,
	341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356,
	357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372,
	373, 374, 375, 376, 377, 378,
}

// cffExpertSubsetCharset 保存CFF专家子集字符集按GID顺序排列的SID映射表
var cffExpertSubsetCharset = [...]uint16{
	0, 1, 231, 232, 235, 236, 237, 238, 13, 14, 15, 99, 239, 240, 241, 242,
	243, 244, 245, 246, 247, 248, 27, 28, 249, 250, 251, 253, 254, 255, 256, 257,
	258, 259, 260, 261, 262, 263, 264, 265, 266, 109, 110, 267, 268, 269, 270, 272,
	300, 301, 302, 305, 314, 315, 158, 155, 163, 320, 321, 322, 323, 324, 325, 326,
	150, 164, 169, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339,
	340, 341, 342, 343, 344, 345, 346,
}

// cffOperand 保存CFF字典数值及其是否采用实数编码
type cffOperand struct {
	value float64
	real  bool
}

// cffEntry 保存字典操作符及按原顺序排列的操作数
type cffEntry struct {
	operator uint16
	operands []cffOperand
}

// cffDict 保留CFF字典的条目顺序，不在词法解析时忽略未知操作符
type cffDict []cffEntry

// cffSet 保存CFF1字体集的固定索引区及顶层字典，字节视图在使用期间不得修改
type cffSet struct {
	data       []byte
	names      [][]byte
	top        []cffDict
	strings    [][]byte
	globalSubr [][]byte
}

// cffPrivate 保存私有字典、局部子程序及字形宽度默认值
type cffPrivate struct {
	dict         cffDict
	localSubr    [][]byte
	defaultWidth float64
	nominalWidth float64
	randomSeed   int32
}

// cffCharset 保存包含隐式.notdef的GID到SID或CID映射及唯一反查表
type cffCharset struct {
	values  []uint16
	byValue map[uint16]uint16
	cid     bool
}

// type2Context 保存当前字体字典的只读子程序、宽度参数及执行与几何构建预算
type type2Context struct {
	globalSubr    [][]byte
	localSubr     [][]byte
	defaultWidth  float64
	nominalWidth  float64
	randomSeed    int32
	maxOperations int
	context       context.Context
	work          *int
	geometryStep  func(int) error
}

// type2Glyph 保存未应用FontMatrix且y向上的非零填充轮廓及字形宽度
type type2Glyph struct {
	geometry Geometry
	width    float64
	seac     *type2Seac
}

// type2Seac 保存StandardEncoding中的组合字符编号，不是当前字体编码或GID
type type2Seac struct {
	offset Point
	base   uint8
	accent uint8
}

// type2Interpreter 保存一个字形跨子程序共享的有界执行状态
type type2Interpreter struct {
	context     type2Context
	glyph       type2Glyph
	stack       [48]float64
	n           int
	transient   [32]float64
	initialized uint32
	point       Point
	widthSeen   bool
	stems       int
	stage       int
	plainStems  bool
	remaining   int
	randomState uint32
}

// parseCFFSet 读取CFF1文件头及按固定顺序排列的四个索引，兼容同一主版本的扩展头
// 入参: data 完整CFF数据
// 返回: *cffSet 字体集索引, error 版本、范围或顶层字典错误
func parseCFFSet(data []byte) (*cffSet, error) {
	if len(data) < 4 {
		return nil, fmt.Errorf("%w: truncated CFF header", ErrInvalid)
	}
	if data[0] != 1 {
		return nil, fmt.Errorf("%w: CFF major version %d", ErrUnsupported, data[0])
	}
	if data[2] < 4 || int(data[2]) > len(data) || data[3] < 1 || data[3] > 4 {
		return nil, fmt.Errorf("%w: invalid CFF header size or offset size", ErrInvalid)
	}
	set := &cffSet{data: data}
	var top [][]byte
	var err error
	position := uint32(data[2])
	for _, target := range []*[][]byte{&set.names, &top, &set.strings, &set.globalSubr} {
		*target, position, err = parseCFFIndex(data, position)
		if err != nil {
			return nil, err
		}
	}
	if len(set.names) == 0 || len(set.names) != len(top) {
		return nil, fmt.Errorf("%w: CFF Name and Top DICT counts must match and be nonzero", ErrInvalid)
	}
	set.top = make([]cffDict, len(top))
	remaining := cffMaxDictEntries
	for i, dict := range top {
		set.top[i], err = parseCFFDictLimit(dict, remaining)
		if err != nil {
			return nil, fmt.Errorf("CFF Top DICT %d: %w", i, err)
		}
		remaining -= len(set.top[i])
	}
	return set, nil
}

// parseCFFIndex 解析CFF1的变长对象索引，返回与输入共享存储的只读对象
// 入参: data 完整CFF数据, offset 索引相对于数据起点的偏移
// 返回: [][]byte 对象视图, uint32 索引结束偏移, error 索引范围或格式错误
func parseCFFIndex(data []byte, offset uint32) ([][]byte, uint32, error) {
	start := uint64(offset)
	if start+2 > uint64(len(data)) {
		return nil, 0, fmt.Errorf("%w: truncated CFF INDEX count", ErrInvalid)
	}
	count := uint64(binary.BigEndian.Uint16(data[start:]))
	if count == 0 {
		if start+2 > math.MaxUint32 {
			return nil, 0, fmt.Errorf("%w: CFF INDEX exceeds offset range", ErrLimit)
		}
		return nil, uint32(start + 2), nil
	}
	if start+3 > uint64(len(data)) {
		return nil, 0, fmt.Errorf("%w: truncated CFF INDEX offset size", ErrInvalid)
	}
	size := uint64(data[start+2])
	base := start + 3 + (count+1)*size
	if size < 1 || size > 4 || base > uint64(len(data)) {
		return nil, 0, fmt.Errorf("%w: invalid CFF INDEX offset array", ErrInvalid)
	}
	first := uint64(cffOffset(data[start+3 : start+3+size]))
	last := uint64(cffOffset(data[base-size : base]))
	if first != 1 || last < first || base+last-1 > uint64(len(data)) {
		return nil, 0, fmt.Errorf("%w: invalid CFF INDEX object range", ErrInvalid)
	}
	end := base + last - 1
	if end > math.MaxUint32 {
		return nil, 0, fmt.Errorf("%w: CFF INDEX exceeds offset range", ErrLimit)
	}
	objects := make([][]byte, int(count))
	previous := first
	for i := uint64(0); i < count; i++ {
		position := start + 3 + (i+1)*size
		next := uint64(cffOffset(data[position : position+size]))
		if next < previous || next > last {
			return nil, 0, fmt.Errorf("%w: unordered CFF INDEX offsets", ErrInvalid)
		}
		objects[i] = data[base+previous-1 : base+next-1]
		previous = next
	}
	return objects, uint32(end), nil
}

// cffOffset 读取已完成长度校验的一至四字节大端偏移
// 入参: data 偏移字节
// 返回: uint32 偏移值
func cffOffset(data []byte) uint32 {
	var value uint32
	for _, b := range data {
		value = value<<8 | uint32(b)
	}
	return value
}

// parseCFFDict 解析CFF1字典的操作符与数值，保留条目顺序及数值编码类型
// 入参: data 字典字节
// 返回: cffDict 字典条目, error 非法编码、截断或操作数过多错误
func parseCFFDict(data []byte) (cffDict, error) {
	return parseCFFDictLimit(data, cffMaxDictEntries)
}

// parseCFFDictLimit 在共享条目预算内解析字典，限制字体集的累计内存占用
// 入参: data 字典字节, limit 剩余条目数
// 返回: cffDict 字典条目, error 编码错误或资源上限错误
func parseCFFDictLimit(data []byte, limit int) (cffDict, error) {
	var dict cffDict
	var stack []cffOperand
	for position := 0; position < len(data); {
		b := data[position]
		if b <= 21 {
			if len(dict) >= limit {
				return nil, fmt.Errorf("%w: CFF DICT entry count", ErrLimit)
			}
			operator := uint16(b)
			position++
			if b == 12 {
				if position == len(data) {
					return nil, fmt.Errorf("%w: truncated CFF DICT operator", ErrInvalid)
				}
				operator = 0x0c00 | uint16(data[position])
				position++
			}
			dict = append(dict, cffEntry{operator: operator, operands: stack})
			stack = nil
			continue
		}
		operand, next, err := cffNumber(data, position)
		if err != nil {
			return nil, err
		}
		if len(stack) == 48 {
			return nil, fmt.Errorf("%w: CFF DICT operand stack exceeds 48", ErrInvalid)
		}
		stack = append(stack, operand)
		position = next
	}
	if len(stack) != 0 {
		return nil, fmt.Errorf("%w: CFF DICT operands without operator", ErrInvalid)
	}
	return dict, nil
}

// cffNumber 解析字典整数或实数，不接受Type2专用的定点数编码
// 入参: data 字典字节, position 数值起点
// 返回: cffOperand 数值, int 数值结束位置, error 编码或范围错误
func cffNumber(data []byte, position int) (cffOperand, int, error) {
	if position < 0 || position >= len(data) {
		return cffOperand{}, 0, fmt.Errorf("%w: truncated CFF DICT number", ErrInvalid)
	}
	b := data[position]
	position++
	size := 0
	switch {
	case b >= 32 && b <= 246:
		return cffOperand{value: float64(int(b) - 139)}, position, nil
	case b >= 247 && b <= 254:
		size = 1
	case b == 28:
		size = 2
	case b == 29:
		size = 4
	case b == 30:
		value, next, err := cffReal(data, position)
		return cffOperand{value: value, real: true}, next, err
	default:
		return cffOperand{}, 0, fmt.Errorf("%w: reserved CFF DICT byte %d", ErrInvalid, b)
	}
	if len(data)-position < size {
		return cffOperand{}, 0, fmt.Errorf("%w: truncated CFF DICT integer", ErrInvalid)
	}
	var value int32
	switch {
	case b >= 247 && b <= 250:
		value = (int32(b)-247)*256 + int32(data[position]) + 108
	case b >= 251 && b <= 254:
		value = -(int32(b)-251)*256 - int32(data[position]) - 108
	case b == 28:
		value = int32(int16(binary.BigEndian.Uint16(data[position:])))
	case b == 29:
		value = int32(binary.BigEndian.Uint32(data[position:]))
	}
	return cffOperand{value: float64(value)}, position + size, nil
}

// cffReal 解析最高有效半字节优先的十进制实数及指数
// 入参: data 字典字节, position 实数首个编码字节的位置
// 返回: float64 有限实数, int 数值结束位置, error 非法词法或截断错误
func cffReal(data []byte, position int) (float64, int, error) {
	var text []byte
	start := position
	for position < len(data) {
		if position-start >= cffMaxRealBytes {
			return 0, 0, fmt.Errorf("%w: CFF DICT real length", ErrLimit)
		}
		b := data[position]
		position++
		for i, nibble := range [2]byte{b >> 4, b & 15} {
			switch {
			case nibble < 10:
				text = append(text, '0'+nibble)
			case nibble == 10:
				text = append(text, '.')
			case nibble == 11:
				text = append(text, 'E')
			case nibble == 12:
				text = append(text, 'E', '-')
			case nibble == 14:
				text = append(text, '-')
			case nibble == 15:
				if i == 0 && b&15 != 15 {
					return 0, 0, fmt.Errorf("%w: invalid CFF DICT real padding", ErrInvalid)
				}
				value, err := strconv.ParseFloat(string(text), 64)
				if err != nil || math.IsInf(value, 0) || math.IsNaN(value) {
					return 0, 0, fmt.Errorf("%w: invalid CFF DICT real", ErrInvalid)
				}
				return value, position, nil
			default:
				return 0, 0, fmt.Errorf("%w: reserved CFF DICT real nibble", ErrInvalid)
			}
		}
	}
	return 0, 0, fmt.Errorf("%w: unterminated CFF DICT real", ErrInvalid)
}

// value 查找字典最后一次声明的指定操作符，不改变原始条目
// 入参: operator 操作符编码，双字节操作符以前缀0x0c00表示
// 返回: []cffOperand 操作数, bool 是否存在
func (d cffDict) value(operator uint16) ([]cffOperand, bool) {
	for i := len(d) - 1; i >= 0; i-- {
		if d[i].operator == operator {
			return d[i].operands, true
		}
	}
	return nil, false
}

// cffInteger 读取单个整数字典操作数并检查取值范围
// 入参: operands 操作数列表, minimum 最小值, maximum 最大值
// 返回: int64 整数, error 数量、类型或范围错误
func cffInteger(operands []cffOperand, minimum, maximum int64) (int64, error) {
	if len(operands) != 1 || operands[0].real || !geometryFinite(operands[0].value) || operands[0].value < float64(minimum) || operands[0].value > float64(maximum) || math.Trunc(operands[0].value) != operands[0].value {
		return 0, fmt.Errorf("%w: invalid CFF integer operand", ErrInvalid)
	}
	return int64(operands[0].value), nil
}

// parseCFFPrivate 读取私有字典及相对于字典起点定位的局部子程序
// 入参: data 完整CFF数据, offset 私有字典起点, size 私有字典字节数
// 返回: cffPrivate 私有字典信息, error 范围、类型或子程序索引错误
func parseCFFPrivate(data []byte, offset, size uint32) (cffPrivate, error) {
	var result cffPrivate
	end := uint64(offset) + uint64(size)
	if end > uint64(len(data)) {
		return result, fmt.Errorf("%w: CFF Private DICT exceeds input", ErrInvalid)
	}
	dict, err := parseCFFDict(data[offset:end])
	if err != nil {
		return result, err
	}
	result.dict = dict
	for _, field := range []struct {
		operator uint16
		target   *float64
	}{{20, &result.defaultWidth}, {21, &result.nominalWidth}} {
		if values, present := dict.value(field.operator); present {
			if len(values) != 1 {
				return result, fmt.Errorf("%w: CFF width operand count", ErrInvalid)
			}
			*field.target = values[0].value
		}
	}
	if values, present := dict.value(0x0c13); present {
		seed, err := cffInteger(values, math.MinInt32, math.MaxInt32)
		if err != nil {
			return result, err
		}
		result.randomSeed = int32(seed)
	}
	if values, present := dict.value(19); present {
		relative, err := cffInteger(values, 0, math.MaxUint32)
		if err != nil {
			return result, err
		}
		position := uint64(offset) + uint64(relative)
		if position > math.MaxUint32 {
			return result, fmt.Errorf("%w: CFF local subroutine offset overflow", ErrInvalid)
		}
		result.localSubr, _, err = parseCFFIndex(data, uint32(position))
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// parseCFFFDSelect 解析CID字体的格式0或格式3字体字典选择表
// 入参: data 完整CFF数据, offset 选择表偏移, glyphs 字形数量, fonts 字体字典数量
// 返回: []uint8 每个字形对应的字体字典索引, error 结构或范围错误
func parseCFFFDSelect(data []byte, offset uint32, glyphs, fonts int) ([]uint8, error) {
	if uint64(offset) >= uint64(len(data)) || glyphs <= 0 || glyphs > 65535 || fonts <= 0 || fonts > 65535 {
		return nil, fmt.Errorf("%w: invalid CFF FDSelect input", ErrInvalid)
	}
	d := data[offset:]
	switch d[0] {
	case 0:
		if len(d)-1 < glyphs {
			return nil, fmt.Errorf("%w: truncated CFF FDSelect format 0", ErrInvalid)
		}
		for _, fd := range d[1 : 1+glyphs] {
			if int(fd) >= fonts {
				return nil, fmt.Errorf("%w: CFF font dictionary index %d", ErrInvalid, fd)
			}
		}
		return d[1 : 1+glyphs], nil
	case 3:
		if len(d) < 5 {
			return nil, fmt.Errorf("%w: truncated CFF FDSelect format 3", ErrInvalid)
		}
		count := int(binary.BigEndian.Uint16(d[1:]))
		if count == 0 || count > glyphs || len(d) < 5+3*count || binary.BigEndian.Uint16(d[3:]) != 0 || int(binary.BigEndian.Uint16(d[3+3*count:])) != glyphs {
			return nil, fmt.Errorf("%w: invalid CFF FDSelect ranges", ErrInvalid)
		}
		result := make([]uint8, glyphs)
		for i := 0; i < count; i++ {
			position := 3 + 3*i
			first := int(binary.BigEndian.Uint16(d[position:]))
			fd := d[position+2]
			next := int(binary.BigEndian.Uint16(d[position+3:]))
			if first >= next || next > glyphs || int(fd) >= fonts {
				return nil, fmt.Errorf("%w: invalid CFF FDSelect range or dictionary index", ErrInvalid)
			}
			for gid := first; gid < next; gid++ {
				result[gid] = fd
			}
		}
		return result, nil
	default:
		return nil, fmt.Errorf("%w: CFF FDSelect format %d", ErrUnsupported, d[0])
	}
}

// parseCFFCharset 解析CFF1字符集并建立GID与SID或CID的双向映射
// 入参: data 完整CFF数据, offset 预定义字符集编号或数据偏移, glyphs 字形数量, strings 自定义字符串数量, cid 是否为CID字体
// 返回: *cffCharset 字符集映射, error 格式、数量、标识范围或重复错误
func parseCFFCharset(data []byte, offset uint32, glyphs int, strings int, cid bool) (*cffCharset, error) {
	if glyphs < 1 || glyphs > 65535 || strings < 0 || strings > 65535 {
		return nil, fmt.Errorf("%w: invalid CFF charset glyph or string count", ErrInvalid)
	}
	maxValue := min(64999, 390+strings)
	if cid {
		maxValue = 65535
	}
	if glyphs > maxValue+1 {
		return nil, fmt.Errorf("%w: CFF charset exceeds available identifiers", ErrInvalid)
	}
	var predefined []uint16
	if offset <= 2 {
		if cid {
			return nil, fmt.Errorf("%w: CID font cannot use a predefined charset", ErrInvalid)
		}
		switch offset {
		case 0:
			if glyphs > 229 {
				return nil, fmt.Errorf("%w: ISOAdobe charset has only 229 glyphs", ErrInvalid)
			}
		case 1:
			predefined = cffExpertCharset[:]
		case 2:
			predefined = cffExpertSubsetCharset[:]
		}
		if predefined != nil && glyphs > len(predefined) {
			return nil, fmt.Errorf("%w: CFF predefined charset is too short", ErrInvalid)
		}
	} else if uint64(offset) >= uint64(len(data)) {
		return nil, fmt.Errorf("%w: CFF charset offset is outside data", ErrInvalid)
	}
	var format byte
	position := uint64(offset)
	if offset > 2 {
		format = data[position]
		position++
		if format > 2 {
			return nil, fmt.Errorf("%w: CFF charset format %d", ErrUnsupported, format)
		}
		if format == 0 && uint64(glyphs-1)*2 > uint64(len(data))-position {
			return nil, fmt.Errorf("%w: truncated CFF charset", ErrInvalid)
		}
	}
	charset := &cffCharset{values: make([]uint16, glyphs), byValue: make(map[uint16]uint16, glyphs), cid: cid}
	charset.byValue[0] = 0
	for gid := 1; gid < glyphs; {
		first, count := gid, 1
		if offset <= 2 {
			if predefined != nil {
				first = int(predefined[gid])
			}
		} else {
			entrySize := uint64(2)
			if format != 0 {
				entrySize += uint64(format)
			}
			if entrySize > uint64(len(data))-position {
				return nil, fmt.Errorf("%w: truncated CFF charset range", ErrInvalid)
			}
			first = int(binary.BigEndian.Uint16(data[position:]))
			position += 2
			if format == 1 {
				count += int(data[position])
				position++
			} else if format == 2 {
				count += int(binary.BigEndian.Uint16(data[position:]))
				position += 2
			}
		}
		if count > glyphs-gid || first+count-1 > maxValue {
			return nil, fmt.Errorf("%w: CFF charset range exceeds glyph or identifier bounds", ErrInvalid)
		}
		for value := first; value < first+count; value++ {
			if _, exists := charset.byValue[uint16(value)]; exists {
				return nil, fmt.Errorf("%w: duplicate CFF charset identifier %d", ErrInvalid, value)
			}
			charset.values[gid] = uint16(value)
			charset.byValue[uint16(value)] = uint16(gid)
			gid++
		}
	}
	return charset, nil
}

// glyph 反查SID或CID对应的字形，标识零对应隐式.notdef
// 入参: value 字符串标识或CID
// 返回: uint16 字形编号, bool 标识是否存在
func (charset *cffCharset) glyph(value uint16) (uint16, bool) {
	if charset == nil {
		return 0, false
	}
	gid, ok := charset.byValue[value]
	return gid, ok
}

// parseCFFEncoding 解析CFF1单字节编码表，零值表示未编码字形
// 入参: data 完整CFF数据, offset 预定义编码编号或数据偏移, charset 已解析的具名字符集
// 返回: *[256]uint16 字符码到GID映射, error 格式、重复编码或字形引用错误
func parseCFFEncoding(data []byte, offset uint32, charset *cffCharset) (*[256]uint16, error) {
	encoding, _, err := parseCFFEncodingRecord(data, offset, charset)
	return encoding, err
}

// parseCFFEncodingRecord 验证编码映射并返回其原始数据，预定义编码不占用表内数据
// 入参: data 完整CFF数据, offset 编码偏移或预定义编号, charset 字符集
// 返回: *[256]uint16 字符码到字形编号, []byte 显式编码数据, error 编码或映射错误
func parseCFFEncodingRecord(data []byte, offset uint32, charset *cffCharset) (*[256]uint16, []byte, error) {
	if charset == nil || charset.cid || len(charset.values) == 0 || len(charset.values) > 65535 {
		return nil, nil, fmt.Errorf("%w: CFF encoding requires a name-keyed charset", ErrInvalid)
	}
	encoding := new([256]uint16)
	if offset <= 1 {
		sids := &cffStandardEncoding
		if offset == 1 {
			sids = &cffExpertEncoding
		}
		for code, sid := range sids {
			if sid != 0 {
				encoding[code], _ = charset.glyph(sid)
			}
		}
		return encoding, nil, nil
	}
	position := uint64(offset)
	if position+2 > uint64(len(data)) {
		return nil, nil, fmt.Errorf("%w: truncated CFF encoding header", ErrInvalid)
	}
	format, count := data[position], int(data[position+1])
	position += 2
	if format&0x7f > 1 {
		return nil, nil, fmt.Errorf("%w: CFF encoding format %d", ErrUnsupported, format&0x7f)
	}
	gid := 1
	for i := 0; i < count; i++ {
		entrySize := uint64(1 + (format & 1))
		if entrySize > uint64(len(data))-position {
			return nil, nil, fmt.Errorf("%w: truncated CFF encoding range", ErrInvalid)
		}
		first, length := int(data[position]), 1
		position++
		if format&1 != 0 {
			length += int(data[position])
			position++
		}
		if first+length > 256 || length > len(charset.values)-gid {
			return nil, nil, fmt.Errorf("%w: CFF encoding range exceeds code or glyph bounds", ErrInvalid)
		}
		for code := first; code < first+length; code++ {
			if encoding[code] != 0 {
				return nil, nil, fmt.Errorf("%w: duplicate CFF encoding code %d", ErrInvalid, code)
			}
			encoding[code] = uint16(gid)
			gid++
		}
	}
	if format&0x80 != 0 {
		if position >= uint64(len(data)) {
			return nil, nil, fmt.Errorf("%w: missing CFF encoding supplement count", ErrInvalid)
		}
		supplements := int(data[position])
		position++
		if uint64(supplements)*3 > uint64(len(data))-position {
			return nil, nil, fmt.Errorf("%w: truncated CFF encoding supplements", ErrInvalid)
		}
		for i := 0; i < supplements; i++ {
			code := data[position]
			sid := binary.BigEndian.Uint16(data[position+1:])
			position += 3
			mapped, ok := charset.glyph(sid)
			if !ok || mapped == 0 || int(mapped) >= gid || encoding[code] != 0 {
				return nil, nil, fmt.Errorf("%w: CFF supplement must add a code for a main-encoding glyph", ErrInvalid)
			}
			encoding[code] = mapped
		}
	}
	return encoding, data[offset:position], nil
}

// cffStandardSID 查找StandardEncoding中指定单字节字符码对应的SID
// 入参: code 单字节字符码
// 返回: uint16 字符串标识，未定义字符码返回零
func cffStandardSID(code byte) uint16 {
	return cffStandardEncoding[code]
}

// parseType2 执行CFF1的Type2字形程序并生成设计单位轮廓，不执行hint网格调整或FontMatrix变换
// 入参: data 字形charstring, context 当前字体字典Type2执行Context
// 返回: *type2Glyph 完整轮廓及待外部解析的seac, error 数据、能力或执行限制错误
func parseType2(data []byte, context type2Context) (*type2Glyph, error) {
	if context.maxOperations < 0 || !geometryFinite(context.defaultWidth, context.nominalWidth) {
		return nil, fmt.Errorf("%w: invalid Type2 context", ErrInvalid)
	}
	if len(context.globalSubr) > 65536 || len(context.localSubr) > 65536 {
		return nil, fmt.Errorf("%w: Type2 subroutine count", ErrLimit)
	}
	budget := context.maxOperations
	if budget == 0 {
		budget = 1 << 20
	}
	p := &type2Interpreter{context: context, remaining: budget, randomState: 0x6d2b79f5}
	if context.randomSeed != 0 {
		p.randomState = uint32(context.randomSeed)
	}
	p.glyph.width = context.defaultWidth
	p.glyph.geometry.FillRule = GeometryNonZero
	ended, err := p.execute(data, 0)
	if err != nil {
		return nil, err
	}
	if !ended {
		return nil, fmt.Errorf("%w: Type2 missing endchar", ErrInvalid)
	}
	return &p.glyph, nil
}

// spend 在执行或读取掩码前扣减共享预算
// 入参: count 执行单元数量
// 返回: error 预算耗尽错误
func (p *type2Interpreter) spend(count int) error {
	if err := checkContext(p.context.context); err != nil {
		return err
	}
	if count > p.remaining {
		return fmt.Errorf("%w: Type2 operation budget", ErrLimit)
	}
	if p.context.work != nil {
		if count > *p.context.work {
			return fmt.Errorf("%w: Type2 cumulative operation budget", ErrLimit)
		}
		*p.context.work -= count
	}
	p.remaining -= count
	return nil
}

// push 将有限数压入规范限定的48项参数栈
// 入参: value 数值
// 返回: error 栈或数值错误
func (p *type2Interpreter) push(value float64) error {
	if !geometryFinite(value) {
		return fmt.Errorf("%w: non-finite Type2 arithmetic", ErrInvalid)
	}
	if p.n == len(p.stack) {
		return fmt.Errorf("%w: Type2 operand stack", ErrLimit)
	}
	p.stack[p.n] = value
	p.n++
	return nil
}

// execute 执行一个charstring或子程序，endchar终止整个字形而return仅返回当前调用，不执行不可达尾部
// 入参: data 当前程序, depth 子程序嵌套层数
// 返回: bool 是否已执行endchar, error 执行错误
func (p *type2Interpreter) execute(data []byte, depth int) (bool, error) {
	if len(data) > 65535 || depth > 10 {
		return false, fmt.Errorf("%w: Type2 charstring length or subroutine depth", ErrLimit)
	}
	for pc := 0; pc < len(data); {
		if err := p.spend(1); err != nil {
			return false, err
		}
		op := data[pc]
		pc++
		if op >= 32 || op == 28 {
			value, consumed, err := type2Number(op, data[pc:])
			if err != nil {
				return false, err
			}
			pc += consumed
			if err := p.push(value); err != nil {
				return false, err
			}
			continue
		}
		switch op {
		case 10, 29:
			if p.n == 0 {
				return false, type2Arguments(op)
			}
			p.n--
			subr := p.context.localSubr
			if op == 29 {
				subr = p.context.globalSubr
			}
			bias := 107
			if len(subr) >= 33900 {
				bias = 32768
			} else if len(subr) >= 1240 {
				bias = 1131
			}
			operand := p.stack[p.n]
			index := operand + float64(bias)
			if math.Trunc(operand) != operand || !type2Integer(index, 0, len(subr)-1) {
				return false, fmt.Errorf("%w: Type2 subroutine index", ErrInvalid)
			}
			ended, err := p.execute(subr[int(index)], depth+1)
			if err != nil {
				return false, err
			}
			if ended {
				return true, nil
			}
		case 11:
			if depth == 0 {
				return false, fmt.Errorf("%w: Type2 misplaced return", ErrInvalid)
			}
			return false, nil
		case 12:
			if pc == len(data) {
				return false, fmt.Errorf("%w: truncated Type2 escape", ErrInvalid)
			}
			escape := data[pc]
			pc++
			if err := p.escape(escape); err != nil {
				return false, err
			}
		case 14:
			if err := p.width(op); err != nil {
				return false, err
			}
			if p.n != 0 && p.n != 4 {
				return false, type2Arguments(op)
			}
			if p.n == 4 {
				if !type2Integer(p.stack[2], 0, 255) || !type2Integer(p.stack[3], 0, 255) {
					return false, fmt.Errorf("%w: Type2 seac character code", ErrInvalid)
				}
				p.glyph.seac = &type2Seac{offset: Point{p.stack[0], p.stack[1]}, base: uint8(p.stack[2]), accent: uint8(p.stack[3])}
			}
			p.n = 0
			return true, nil
		case 1, 3, 18, 23, 19, 20:
			consumed, err := p.hint(op, data[pc:])
			if err != nil {
				return false, err
			}
			pc += consumed
		case 4, 5, 6, 7, 8, 21, 22, 24, 25, 26, 27, 30, 31:
			if err := p.path(op); err != nil {
				return false, err
			}
		default:
			return false, fmt.Errorf("%w: undefined Type2 operator %d", ErrUnsupported, op)
		}
	}
	return false, fmt.Errorf("%w: unterminated Type2 program", ErrInvalid)
}

// type2Number 解码Type2整数、shortint及有符号16.16定点数
// 入参: first 首字节, data 后续字节
// 返回: float64 数值, int 后续消耗字节数, error 截断错误
func type2Number(first byte, data []byte) (float64, int, error) {
	count := 0
	switch {
	case first == 28:
		count = 2
	case first == 255:
		count = 4
	case first >= 247:
		count = 1
	}
	if len(data) < count {
		return 0, 0, fmt.Errorf("%w: truncated Type2 number", ErrInvalid)
	}
	switch {
	case first == 28:
		return float64(int16(binary.BigEndian.Uint16(data))), count, nil
	case first == 255:
		return float64(int32(binary.BigEndian.Uint32(data))) / 65536, count, nil
	case first >= 251:
		return float64(-256*(int(first)-251) - int(data[0]) - 108), count, nil
	case first >= 247:
		return float64(256*(int(first)-247) + int(data[0]) + 108), count, nil
	default:
		return float64(int(first) - 139), 0, nil
	}
}

// type2Integer 检查可安全转换为有界int的整数值
// 入参: value 数值, minimum 下界, maximum 上界
// 返回: bool 是否为范围内的有限整数
func type2Integer(value float64, minimum, maximum int) bool {
	return geometryFinite(value) && value >= float64(minimum) && value <= float64(maximum) && math.Trunc(value) == value
}

// type2Arguments 生成操作数数量或位置错误
// 入参: op 操作符编号
// 返回: error 可识别的无效数据错误
func type2Arguments(op byte) error {
	return fmt.Errorf("%w: Type2 operator %d operands or placement", ErrInvalid, op)
}

// width 在第一个允许携带宽度的清栈操作处提取可选宽度
// 入参: op 操作符编号
// 返回: error 宽度计算错误
func (p *type2Interpreter) width(op byte) error {
	if p.widthSeen {
		return nil
	}
	p.widthSeen = true
	present := false
	switch op {
	case 1, 3, 18, 23, 19, 20:
		present = p.n%2 == 1
	case 4, 22:
		present = p.n == 2
	case 21:
		present = p.n == 3
	case 14:
		present = p.n == 1 || p.n == 5
	}
	if present {
		p.glyph.width = p.context.nominalWidth + p.stack[0]
		if !geometryFinite(p.glyph.width) {
			return fmt.Errorf("%w: non-finite Type2 width", ErrInvalid)
		}
		copy(p.stack[:], p.stack[1:p.n])
		p.n--
	}
	return nil
}

// hint 处理有序stem声明及掩码字节，但不执行像素网格调整
// 入参: op 提示操作符, data 紧随操作符的字节
// 返回: int 掩码字节数, error 提示结构或限制错误
func (p *type2Interpreter) hint(op byte, data []byte) (int, error) {
	if err := p.width(op); err != nil {
		return 0, err
	}
	stage := 0
	switch op {
	case 1:
		stage = 1
	case 18:
		stage = 2
	case 3:
		stage = 3
	case 23:
		stage = 4
	case 20:
		stage = 5
	case 19:
		stage = 6
	}
	mask := op == 19 || op == 20
	if p.n%2 != 0 || !mask && (p.n == 0 || p.stage > stage) || mask && p.n != 0 && p.stage >= 5 || op == 20 && p.stage > 5 {
		return 0, type2Arguments(op)
	}
	if op == 1 || op == 3 {
		p.plainStems = true
	}
	if (op == 19 || op == 20) && p.plainStems {
		return 0, fmt.Errorf("%w: Type2 mask requires hm stem declarations", ErrInvalid)
	}
	p.stems += p.n / 2
	p.n = 0
	if p.stems > 96 {
		return 0, fmt.Errorf("%w: Type2 stem count", ErrLimit)
	}
	p.stage = max(p.stage, stage)
	if !mask {
		return 0, nil
	}
	count := (p.stems + 7) / 8
	if count == 0 || len(data) < count {
		return 0, fmt.Errorf("%w: Type2 mask without stems or truncated mask", ErrInvalid)
	}
	if unused := (8 - p.stems%8) % 8; data[count-1]&byte((1<<unused)-1) != 0 {
		return 0, fmt.Errorf("%w: nonzero Type2 mask padding", ErrInvalid)
	}
	if err := p.spend(count); err != nil {
		return 0, err
	}
	return count, nil
}

// move 创建自动闭合的非零填充子路径，后续移动仍相对于上一实际终点
// 入参: dx 横向增量, dy 纵向增量
// 返回: error 坐标、预算或取消错误
func (p *type2Interpreter) move(dx, dy float64) error {
	p.point.X += dx
	p.point.Y += dy
	if !geometryFinite(p.point.X, p.point.Y) {
		return fmt.Errorf("%w: non-finite Type2 point", ErrInvalid)
	}
	if p.context.geometryStep != nil {
		if err := p.context.geometryStep(0); err != nil {
			return err
		}
	}
	p.glyph.geometry.Figures = append(p.glyph.geometry.Figures, GeometryFigure{StartPoint: p.point, IsClosed: true, IsFilled: true})
	return nil
}

// line 追加使用绝对终点保存的相对直线
// 入参: dx 横向增量, dy 纵向增量
// 返回: error 路径、坐标、预算或取消错误
func (p *type2Interpreter) line(dx, dy float64) error {
	if len(p.glyph.geometry.Figures) == 0 {
		return fmt.Errorf("%w: Type2 line before moveto", ErrInvalid)
	}
	p.point.X += dx
	p.point.Y += dy
	if !geometryFinite(p.point.X, p.point.Y) {
		return fmt.Errorf("%w: non-finite Type2 line", ErrInvalid)
	}
	if p.context.geometryStep != nil {
		if err := p.context.geometryStep(1); err != nil {
			return err
		}
	}
	f := &p.glyph.geometry.Figures[len(p.glyph.geometry.Figures)-1]
	f.Segments = append(f.Segments, GeometrySegment{Kind: GeometryLine, Point: p.point, IsStroked: true})
	return nil
}

// curve 将连续相对增量转换为绝对三次曲线控制点及终点
// 入参: dx1 第一横向增量, dy1 第一纵向增量, dx2 第二横向增量, dy2 第二纵向增量, dx3 终点横向增量, dy3 终点纵向增量
// 返回: error 路径、坐标、预算或取消错误
func (p *type2Interpreter) curve(dx1, dy1, dx2, dy2, dx3, dy3 float64) error {
	if len(p.glyph.geometry.Figures) == 0 {
		return fmt.Errorf("%w: Type2 curve before moveto", ErrInvalid)
	}
	a := Point{p.point.X + dx1, p.point.Y + dy1}
	b := Point{a.X + dx2, a.Y + dy2}
	p.point = Point{b.X + dx3, b.Y + dy3}
	if !geometryFinite(a.X, a.Y, b.X, b.Y, p.point.X, p.point.Y) {
		return fmt.Errorf("%w: non-finite Type2 curve", ErrInvalid)
	}
	if p.context.geometryStep != nil {
		if err := p.context.geometryStep(1); err != nil {
			return err
		}
	}
	f := &p.glyph.geometry.Figures[len(p.glyph.geometry.Figures)-1]
	f.Segments = append(f.Segments, GeometrySegment{Kind: GeometryCubic, Control1: a, Control2: b, Point: p.point, IsStroked: true})
	return nil
}

// path 执行全部单字节路径命令并消费完整参数栈
// 入参: op 路径操作符
// 返回: error 参数、路径或坐标错误
func (p *type2Interpreter) path(op byte) error {
	if op == 4 || op == 21 || op == 22 {
		if err := p.width(op); err != nil {
			return err
		}
	} else if !p.widthSeen || len(p.glyph.geometry.Figures) == 0 {
		return type2Arguments(op)
	}
	p.stage = 7
	a := p.stack[:p.n]
	p.n = 0
	n := len(a)
	switch op {
	case 4, 22:
		if n != 1 {
			return type2Arguments(op)
		}
		if op == 4 {
			return p.move(0, a[0])
		}
		return p.move(a[0], 0)
	case 21:
		if n != 2 {
			return type2Arguments(op)
		}
		return p.move(a[0], a[1])
	case 5:
		if n < 2 || n%2 != 0 {
			return type2Arguments(op)
		}
		for i := 0; i < n; i += 2 {
			if err := p.line(a[i], a[i+1]); err != nil {
				return err
			}
		}
	case 6, 7:
		if n == 0 {
			return type2Arguments(op)
		}
		for i, value := range a {
			dx, dy := value, 0.0
			if (i%2 == 0) == (op == 7) {
				dx, dy = 0, value
			}
			if err := p.line(dx, dy); err != nil {
				return err
			}
		}
	case 8, 24:
		curves := n
		if op == 24 {
			curves -= 2
		}
		if curves < 6 || curves%6 != 0 {
			return type2Arguments(op)
		}
		for i := 0; i < curves; i += 6 {
			if err := p.curve(a[i], a[i+1], a[i+2], a[i+3], a[i+4], a[i+5]); err != nil {
				return err
			}
		}
		if op == 24 {
			return p.line(a[n-2], a[n-1])
		}
	case 25:
		if n < 8 || (n-6)%2 != 0 {
			return type2Arguments(op)
		}
		for i := 0; i < n-6; i += 2 {
			if err := p.line(a[i], a[i+1]); err != nil {
				return err
			}
		}
		return p.curve(a[n-6], a[n-5], a[n-4], a[n-3], a[n-2], a[n-1])
	case 26, 27, 30, 31:
		if n < 4 || n%4 > 1 {
			return type2Arguments(op)
		}
		odd := 0.0
		if (op == 26 || op == 27) && n%4 == 1 {
			odd, a = a[0], a[1:]
		}
		horizontal := op == 27 || op == 31
		for len(a) >= 4 {
			var dx1, dy1, dx3, dy3 float64
			if op == 26 || op == 27 {
				dx1, dy1, dx3, dy3 = odd, a[0], 0, a[3]
				if horizontal {
					dx1, dy1, dx3, dy3 = a[0], odd, a[3], 0
				}
				odd = 0
			} else {
				if horizontal {
					dx1, dy3 = a[0], a[3]
					if len(a) == 5 {
						dx3 = a[4]
					}
				} else {
					dy1, dx3 = a[0], a[3]
					if len(a) == 5 {
						dy3 = a[4]
					}
				}
				horizontal = !horizontal
			}
			if err := p.curve(dx1, dy1, a[1], a[2], dx3, dy3); err != nil {
				return err
			}
			a = a[4:]
		}
	}
	return nil
}

// flex 将四种flex命令展开为两条原始三次曲线，不应用设备像素拉直提示
// 入参: op 转义操作符编号
// 返回: error 参数或路径错误
func (p *type2Interpreter) flex(op byte) error {
	a := p.stack[:p.n]
	var d [12]float64
	switch op {
	case 34:
		if len(a) != 7 {
			return type2Arguments(op)
		}
		d = [12]float64{a[0], 0, a[1], a[2], a[3], 0, a[4], 0, a[5], -a[2], a[6], 0}
	case 35:
		if len(a) != 13 {
			return type2Arguments(op)
		}
		copy(d[:], a[:12])
	case 36:
		if len(a) != 9 {
			return type2Arguments(op)
		}
		d = [12]float64{a[0], a[1], a[2], a[3], a[4], 0, a[5], 0, a[6], a[7], a[8], -(a[1] + a[3] + a[7])}
	case 37:
		if len(a) != 11 {
			return type2Arguments(op)
		}
		copy(d[:10], a[:10])
		dx, dy := a[0]+a[2]+a[4]+a[6]+a[8], a[1]+a[3]+a[5]+a[7]+a[9]
		if math.Abs(dx) > math.Abs(dy) {
			d[10], d[11] = a[10], -dy
		} else {
			d[10], d[11] = -dx, a[10]
		}
	}
	p.n = 0
	p.stage = 7
	if err := p.curve(d[0], d[1], d[2], d[3], d[4], d[5]); err != nil {
		return err
	}
	return p.curve(d[6], d[7], d[8], d[9], d[10], d[11])
}

// escape 执行Type2转义算术、逻辑、栈、存储及flex操作
// 入参: op 转义操作符编号
// 返回: error 操作数、能力或限制错误
func (p *type2Interpreter) escape(op byte) error {
	if op >= 34 && op <= 37 {
		return p.flex(op)
	}
	if op == 0 {
		if p.n != 0 {
			return type2Arguments(op)
		}
		return nil
	}
	if op == 23 {
		x := p.randomState
		x ^= x << 13
		x ^= x >> 17
		x ^= x << 5
		p.randomState = x
		return p.push((float64(x) + 1) / 4294967296)
	}
	need := 0
	switch op {
	case 5, 9, 14, 18, 21, 26, 27, 29:
		need = 1
	case 3, 4, 10, 11, 12, 15, 20, 24, 28, 30:
		need = 2
	case 22:
		need = 4
	default:
		return fmt.Errorf("%w: undefined Type2 escaped operator %d", ErrUnsupported, op)
	}
	if p.n < need {
		return type2Arguments(op)
	}
	a := p.stack[p.n-need : p.n]
	switch op {
	case 27:
		return p.push(a[0])
	case 28:
		a[0], a[1] = a[1], a[0]
		return nil
	case 29:
		index := a[0]
		p.n--
		if !geometryFinite(index) || math.Trunc(index) != index {
			return type2Arguments(op)
		}
		index = max(index, 0)
		if !type2Integer(index, 0, p.n-1) {
			return type2Arguments(op)
		}
		return p.push(p.stack[p.n-1-int(index)])
	case 30:
		count, shift := a[0], a[1]
		p.n -= 2
		if !type2Integer(count, 0, p.n) || math.Trunc(shift) != shift {
			return type2Arguments(op)
		}
		if count != 0 {
			n := int(count)
			j := int(math.Mod(shift, count))
			if j < 0 {
				j += n
			}
			var copyStack [48]float64
			copy(copyStack[:], p.stack[p.n-n:p.n])
			for i := 0; i < n; i++ {
				p.stack[p.n-n+(i+j)%n] = copyStack[i]
			}
		}
		return nil
	}
	p.n -= need
	value := 0.0
	switch op {
	case 3:
		if a[0] != 0 && a[1] != 0 {
			value = 1
		}
	case 4:
		if a[0] != 0 || a[1] != 0 {
			value = 1
		}
	case 5:
		if a[0] == 0 {
			value = 1
		}
	case 9:
		value = math.Abs(a[0])
	case 10:
		value = a[0] + a[1]
	case 11:
		value = a[0] - a[1]
	case 12:
		value = a[0] / a[1]
	case 14:
		value = -a[0]
	case 15:
		if a[0] == a[1] {
			value = 1
		}
	case 18:
		return nil
	case 20:
		if !type2Integer(a[1], 0, 31) {
			return type2Arguments(op)
		}
		index := uint32(a[1])
		p.transient[index] = a[0]
		p.initialized |= 1 << index
		return nil
	case 21:
		if !type2Integer(a[0], 0, 31) || p.initialized&(1<<uint32(a[0])) == 0 {
			return fmt.Errorf("%w: Type2 uninitialized or invalid transient index", ErrInvalid)
		}
		value = p.transient[uint32(a[0])]
	case 22:
		value = a[1]
		if a[2] <= a[3] {
			value = a[0]
		}
	case 24:
		value = a[0] * a[1]
	case 26:
		value = math.Sqrt(a[0])
	}
	return p.push(value)
}
