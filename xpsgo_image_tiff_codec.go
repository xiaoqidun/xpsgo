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
	"compress/zlib"
	"encoding/binary"
	"errors"
	"fmt"
	"image"
	"image/color"
	"image/jpeg"
	"io"
)

// tiffFaxVertical 等常量表示TIFF传真压缩编码模式
const (
	tiffFaxVertical = iota
	tiffFaxHorizontal
	tiffFaxPass
	tiffFaxUncompressed
	tiffFaxEnd
)

// tiffFaxWhite 保存ITU-T T.4白色游程霍夫曼解码前缀树
var tiffFaxWhite = newTIFFFaxTree([]string{
	"00110101", "000111", "0111", "1000", "1011", "1100", "1110", "1111",
	"10011", "10100", "00111", "01000", "001000", "000011", "110100", "110101",
	"101010", "101011", "0100111", "0001100", "0001000", "0010111", "0000011", "0000100",
	"0101000", "0101011", "0010011", "0100100", "0011000", "00000010", "00000011", "00011010",
	"00011011", "00010010", "00010011", "00010100", "00010101", "00010110", "00010111", "00101000",
	"00101001", "00101010", "00101011", "00101100", "00101101", "00000100", "00000101", "00001010",
	"00001011", "01010010", "01010011", "01010100", "01010101", "00100100", "00100101", "01011000",
	"01011001", "01011010", "01011011", "01001010", "01001011", "00110010", "00110011", "00110100",
	"11011", "10010", "010111", "0110111", "00110110", "00110111", "01100100", "01100101",
	"01101000", "01100111", "011001100", "011001101", "011010010", "011010011", "011010100", "011010101",
	"011010110", "011010111", "011011000", "011011001", "011011010", "011011011", "010011000", "010011001",
	"010011010", "011000", "010011011", "00000001000", "00000001100", "00000001101", "000000010010", "000000010011",
	"000000010100", "000000010101", "000000010110", "000000010111", "000000011100", "000000011101", "000000011110", "000000011111",
})

// tiffFaxBlack 保存ITU-T T.4黑色游程霍夫曼解码前缀树
var tiffFaxBlack = newTIFFFaxTree([]string{
	"0000110111", "010", "11", "10", "011", "0011", "0010", "00011",
	"000101", "000100", "0000100", "0000101", "0000111", "00000100", "00000111", "000011000",
	"0000010111", "0000011000", "0000001000", "00001100111", "00001101000", "00001101100", "00000110111", "00000101000",
	"00000010111", "00000011000", "000011001010", "000011001011", "000011001100", "000011001101", "000001101000", "000001101001",
	"000001101010", "000001101011", "000011010010", "000011010011", "000011010100", "000011010101", "000011010110", "000011010111",
	"000001101100", "000001101101", "000011011010", "000011011011", "000001010100", "000001010101", "000001010110", "000001010111",
	"000001100100", "000001100101", "000001010010", "000001010011", "000000100100", "000000110111", "000000111000", "000000100111",
	"000000101000", "000001011000", "000001011001", "000000101011", "000000101100", "000001011010", "000001100110", "000001100111",
	"0000001111", "000011001000", "000011001001", "000001011011", "000000110011", "000000110100", "000000110101", "0000001101100",
	"0000001101101", "0000001001010", "0000001001011", "0000001001100", "0000001001101", "0000001110010", "0000001110011", "0000001110100",
	"0000001110101", "0000001110110", "0000001110111", "0000001010010", "0000001010011", "0000001010100", "0000001010101", "0000001011010",
	"0000001011011", "0000001100100", "0000001100101", "00000001000", "00000001100", "00000001101", "000000010010", "000000010011",
	"000000010100", "000000010101", "000000010110", "000000010111", "000000011100", "000000011101", "000000011110", "000000011111",
})

// tiffFaxNode 保存T.4终止码和补充码的只读前缀树节点，value为游程加一
type tiffFaxNode struct {
	next  [2]uint16
	value uint16
}

// tiffFaxReader 保存单个条带的位位置、位顺序和工作预算，不跨条带保留参考行
type tiffFaxReader struct {
	data         []byte
	position     uint64
	fillOrder    uint32
	work         uint64
	allowLiteral bool
	literal      bool
	literalWhite uint8
	literalBlack bool
	literalExit  bool
	exitBlack    bool
}

// tiffJPEGEntropyWriter 保存单个DCT分量的熵编码位及字节填充状态
type tiffJPEGEntropyWriter struct {
	data  []byte
	word  uint32
	count uint
}

// tiffLegacyExtraJPEG 保存具有完整交换流的多扫描TIFF解码状态
type tiffLegacyExtraJPEG struct {
	stream  tiffJPEGTable
	entropy []byte
}

// tiffJPEGTable 保存JPEG码表、帧参数及已占用的码表槽位
type tiffJPEGTable struct {
	data       []byte
	quant      uint16
	huffman    uint16
	process    byte
	precision  byte
	width      uint16
	height     uint16
	components int
	sampling   [5]byte
	identities [5]byte
}

// newTIFFFaxTree 将标准表按终止码0至63及补充码64至2560建立不可变前缀树
// 入参: codes 标准表中的二进制码字
// 返回: []tiffFaxNode 前缀树
func newTIFFFaxTree(codes []string) []tiffFaxNode {
	tree := make([]tiffFaxNode, 1, 256)
	for index, code := range codes {
		node := 0
		for _, bit := range code {
			branch := int(bit - '0')
			next := tree[node].next[branch]
			if next == 0 {
				next = uint16(len(tree))
				tree = append(tree, tiffFaxNode{})
				tree[node].next[branch] = next
			}
			node = int(next)
		}
		value := index
		if index >= 64 {
			value = (index - 63) * 64
		}
		tree[node].value = uint16(value + 1)
	}
	return tree
}

// bits 读取高位或低位优先的位流，在输入不足或工作预算耗尽时停止
// 入参: count 位数量
// 返回: uint32 位值, error 输入或资源错误
func (f *tiffFaxReader) bits(count uint) (uint32, error) {
	if count > 32 || uint64(count) > f.work {
		return 0, fmt.Errorf("%w: TIFF fax bit budget", ErrLimit)
	}
	if f.position > uint64(len(f.data))*8 || uint64(count) > uint64(len(f.data))*8-f.position {
		return 0, fmt.Errorf("%w: truncated TIFF fax bits", ErrInvalid)
	}
	f.work -= uint64(count)
	var value uint32
	for range count {
		shift := uint(f.position & 7)
		if f.fillOrder == 1 {
			shift = 7 - shift
		}
		value = value<<1 | uint32(f.data[f.position>>3]>>shift&1)
		f.position++
	}
	return value, nil
}

// peek 在不改变条带位置的情况下检查扩展前缀，输入不足时不匹配
// 入参: count 前视位数, value 待匹配位值
// 返回: bool 是否匹配
func (f *tiffFaxReader) peek(count uint, value uint32) bool {
	copy := *f
	got, err := copy.bits(count)
	return err == nil && got == value
}

// literalWord 解码一个未压缩模式码字，跨行保留待输出像素而不丢失填充或退出状态
// 返回: error 码字、输入或资源错误
func (f *tiffFaxReader) literalWord() error {
	for zeros := 0; zeros <= 10; zeros++ {
		bit, err := f.bits(1)
		if err != nil {
			return err
		}
		if bit == 0 {
			continue
		}
		switch {
		case zeros < 5:
			f.literalWhite, f.literalBlack = uint8(zeros), true
		case zeros == 5:
			f.literalWhite = 5
		default:
			f.literalWhite, f.literalExit = uint8(zeros-6), true
			tag, err := f.bits(1)
			if err != nil {
				return err
			}
			f.exitBlack = tag == 1
		}
		return nil
	}
	return fmt.Errorf("%w: TIFF fax uncompressed code", ErrInvalid)
}

// tiffFaxToggleChange 在指定列切换颜色变化点并抵消同列零长游程，保证变化点严格递增
// 入参: changes 变色点缓冲区, position 当前列号
// 返回: []int 更新后的变色点切片
func tiffFaxToggleChange(changes []int, position int) []int {
	if len(changes) > 0 && changes[len(changes)-1] == position {
		return changes[:len(changes)-1]
	}
	return append(changes, position)
}

// literalLine 输出当前行的未压缩像素，T.6字面量可以跨行，退出色作用于恢复压缩的位置
// 入参: row 当前行, width 行宽, position 起始列, black 当前假定颜色, changes 变色点缓冲区
// 返回: int 结束列, bool 恢复颜色, []int 变色点, error 字面量或输入错误
func (f *tiffFaxReader) literalLine(row []byte, width, position int, black bool, changes []int) (int, bool, []int, error) {
	setColor := func(color bool) {
		if color != black {
			changes = tiffFaxToggleChange(changes, position)
			black = color
		}
	}
	for {
		if f.literalWhite > 0 && position < width {
			count := min(int(f.literalWhite), width-position)
			setColor(false)
			position += count
			f.literalWhite -= uint8(count)
		}
		if f.literalWhite == 0 && f.literalBlack && position < width {
			setColor(true)
			tiffFaxPaint(row, position, position+1, true)
			position++
			f.literalBlack = false
		}
		if f.literalWhite == 0 && !f.literalBlack && f.literalExit {
			f.literalExit, f.literal = false, false
			setColor(f.exitBlack)
			return position, black, changes, nil
		}
		if position == width {
			return position, black, changes, nil
		}
		if f.literalWhite == 0 && !f.literalBlack {
			if err := f.literalWord(); err != nil {
				return 0, false, nil, err
			}
		}
	}
}

// run 读取同色补充码及唯一终止码，不允许游程越过当前行
// 入参: black 是否读取黑色表, limit 剩余行宽
// 返回: int 游程长度, error 码字、长度或资源错误
func (f *tiffFaxReader) run(black bool, limit int) (int, error) {
	tree := tiffFaxWhite
	if black {
		tree = tiffFaxBlack
	}
	total := 0
	for {
		node := uint16(0)
		for depth := 0; depth < 13; depth++ {
			bit, err := f.bits(1)
			if err != nil {
				return 0, err
			}
			node = tree[node].next[bit]
			if node == 0 {
				return 0, fmt.Errorf("%w: TIFF fax run code", ErrInvalid)
			}
			if tree[node].value != 0 {
				break
			}
		}
		if tree[node].value == 0 {
			return 0, fmt.Errorf("%w: TIFF fax code length", ErrInvalid)
		}
		value := int(tree[node].value) - 1
		if value > limit-total {
			return 0, fmt.Errorf("%w: TIFF fax run width", ErrInvalid)
		}
		total += value
		if value < 64 {
			return total, nil
		}
	}
}

// eol 读取T.4行首标记及可变填充位，扫描受条带工作预算限制
// 返回: error 行首标记或输入错误
func (f *tiffFaxReader) eol() error {
	for zeros := 0; ; zeros++ {
		bit, err := f.bits(1)
		if err != nil {
			return err
		}
		if bit == 1 {
			if zeros < 11 {
				return fmt.Errorf("%w: TIFF fax EOL", ErrInvalid)
			}
			return nil
		}
	}
}

// mode 读取T.4或T.6二维模式，保留垂直偏移和未压缩扩展的区别
// 返回: int 模式, int 垂直偏移, error 模式或输入错误
func (f *tiffFaxReader) mode() (int, int, error) {
	code := uint32(0)
	for length := uint(1); length <= 7; length++ {
		bit, err := f.bits(1)
		if err != nil {
			return 0, 0, err
		}
		code = code<<1 | bit
		switch {
		case length == 1 && code == 1:
			return tiffFaxVertical, 0, nil
		case length == 3 && (code == 2 || code == 3):
			return tiffFaxVertical, int(code)*2 - 5, nil
		case length == 3 && code == 1:
			return tiffFaxHorizontal, 0, nil
		case length == 4 && code == 1:
			return tiffFaxPass, 0, nil
		case length == 6 && (code == 2 || code == 3):
			return tiffFaxVertical, int(code)*4 - 10, nil
		case length == 7 && (code == 2 || code == 3):
			return tiffFaxVertical, int(code)*6 - 15, nil
		case length == 7 && code == 1:
			extension, err := f.bits(3)
			if err != nil {
				return 0, 0, err
			}
			if extension != 7 {
				return 0, 0, fmt.Errorf("%w: TIFF fax extension %d", ErrUnsupported, extension)
			}
			return tiffFaxUncompressed, 0, nil
		}
	}
	if code == 0 {
		first, err := f.bits(5)
		if err != nil {
			return 0, 0, err
		}
		second, err := f.bits(12)
		if err != nil {
			return 0, 0, err
		}
		if first == 1 && second == 1 {
			return tiffFaxEnd, 0, nil
		}
	}
	return 0, 0, fmt.Errorf("%w: TIFF fax two-dimensional mode", ErrInvalid)
}

// tiffFaxPaint 将已检查的逻辑黑色游程写入高位优先位图，白色及行尾填充保持零
// 入参: row 目标行, start 起始列, end 结束列, black 是否为黑色
func tiffFaxPaint(row []byte, start, end int, black bool) {
	if !black {
		return
	}
	for start < end && start&7 != 0 {
		row[start/8] |= 1 << uint(7-start&7)
		start++
	}
	for end-start >= 8 {
		row[start/8] = 255
		start += 8
	}
	for start < end {
		row[start/8] |= 1 << uint(7-start&7)
		start++
	}
}

// line1 读取一维游程并记录变色点，防止无进展码流放大中间状态
// 入参: row 目标行, width 有效列数, changes 本行复用缓冲区
// 返回: []int 有序变色点, error 游程或资源错误
func (f *tiffFaxReader) line1(row []byte, width int, changes []int) ([]int, error) {
	position, black := 0, false
	for actions := 0; position < width; actions++ {
		if actions > width*4+32 {
			return nil, fmt.Errorf("%w: TIFF fax run count", ErrLimit)
		}
		if f.allowLiteral && f.peek(12, 15) {
			if _, err := f.bits(12); err != nil {
				return nil, err
			}
			f.literal = true
			var err error
			position, black, changes, err = f.literalLine(row, width, position, black, changes)
			if err != nil {
				return nil, err
			}
			if position == width && f.literal {
				if f.literalWhite != 0 || f.literalBlack {
					return nil, fmt.Errorf("%w: TIFF T.4 uncompressed line width", ErrInvalid)
				}
				if err := f.literalWord(); err != nil || !f.literalExit || f.literalWhite != 0 {
					return nil, fmt.Errorf("%w: TIFF T.4 uncompressed line boundary", ErrInvalid)
				}
				f.literal, f.literalExit = false, false
			}
			continue
		}
		length, err := f.run(black, width-position)
		if err != nil {
			return nil, err
		}
		tiffFaxPaint(row, position, position+length, black)
		position += length
		changes = tiffFaxToggleChange(changes, position)
		black = !black
	}
	return changes, nil
}

// line2 依据上一行的变色点读取二维模式，参考游标只向右移动
// 入参: row 目标行, width 有效列数, reference 上一行含哨兵的变色点, changes 本行复用缓冲区
// 返回: []int 本行变色点, bool 是否遇到行首EOFB, error 模式、长度或资源错误
func (f *tiffFaxReader) line2(row []byte, width int, reference, changes []int) ([]int, bool, error) {
	position, cursor, black := 0, 0, false
	started := false
	for actions := 0; position < width; actions++ {
		if actions > width*4+32 {
			return nil, false, fmt.Errorf("%w: TIFF fax mode count", ErrLimit)
		}
		if f.literal {
			before := position
			var err error
			position, black, changes, err = f.literalLine(row, width, position, black, changes)
			if err != nil {
				return nil, false, err
			}
			if position == width {
				break
			}
			started = started || position != before || black
			continue
		}
		for cursor < len(reference) && (reference[cursor] < position || started && reference[cursor] == position) {
			cursor++
		}
		index := cursor
		if (index&1 == 1) != black {
			index++
		}
		b1, b2 := width, width
		if index < len(reference) {
			b1 = reference[index]
		}
		if index+1 < len(reference) {
			b2 = reference[index+1]
		}
		mode, delta, err := f.mode()
		if err != nil {
			return nil, false, err
		}
		switch mode {
		case tiffFaxPass:
			started = true
			if b2 <= position || b2 > width {
				return nil, false, fmt.Errorf("%w: TIFF fax pass position", ErrInvalid)
			}
			tiffFaxPaint(row, position, b2, black)
			position = b2
		case tiffFaxHorizontal:
			started = true
			first, err := f.run(black, width-position)
			if err != nil {
				return nil, false, err
			}
			second, err := f.run(!black, width-position-first)
			if err != nil {
				return nil, false, err
			}
			if first+second == 0 {
				return nil, false, fmt.Errorf("%w: TIFF fax horizontal progress", ErrInvalid)
			}
			tiffFaxPaint(row, position, position+first, black)
			tiffFaxPaint(row, position+first, position+first+second, !black)
			position += first
			changes = tiffFaxToggleChange(changes, position)
			position += second
			changes = tiffFaxToggleChange(changes, position)
		case tiffFaxVertical:
			started = true
			end := b1 + delta
			if end < position || end > width {
				return nil, false, fmt.Errorf("%w: TIFF fax vertical position", ErrInvalid)
			}
			tiffFaxPaint(row, position, end, black)
			position = end
			changes = tiffFaxToggleChange(changes, position)
			black = !black
		case tiffFaxUncompressed:
			f.literal = true
		case tiffFaxEnd:
			if actions != 0 {
				return nil, false, fmt.Errorf("%w: TIFF fax EOFB inside row", ErrInvalid)
			}
			return changes, true, nil
		}
	}
	if len(changes) == 0 || changes[len(changes)-1] != width {
		changes = append(changes, width)
	}
	return changes, false, nil
}

// faxStrip 解码独立的MH、T.4或T.6条带，输出逻辑游程位图后由TIFF解释黑白极性
// 入参: dst 限定尺寸的位图, src 编码条带, width 有效列数, compression 压缩标识, fillOrder 编码位顺序, options T.4或T.6选项
// 返回: error 尺寸、码流、能力或资源错误
func faxStrip(dst, src []byte, width int, compression, fillOrder, options uint32) error {
	rowBytes := (width + 7) / 8
	if width <= 0 || width > rasterMaxDimension || len(dst)%rowBytes != 0 || fillOrder != 1 && fillOrder != 2 {
		return fmt.Errorf("%w: TIFF fax strip layout", ErrInvalid)
	}
	if compression < 2 || compression > 4 || compression == 2 && options != 0 || compression == 3 && options&^7 != 0 || compression == 4 && options&^2 != 0 {
		return fmt.Errorf("%w: TIFF fax options", ErrInvalid)
	}
	clear(dst)
	f := tiffFaxReader{data: src, fillOrder: fillOrder, work: min(rasterMaxWork, uint64(len(src))*8+uint64(len(dst))*16+1024), allowLiteral: compression != 2}
	reference, changes := make([]int, 2, width+3), make([]int, 0, width+3)
	reference[0], reference[1] = width, width
	for y := 0; y < len(dst)/rowBytes; y++ {
		oneDimensional := compression != 4
		if compression == 3 {
			if err := f.eol(); err != nil {
				return err
			}
			if options&4 != 0 && f.position&7 != 0 {
				return fmt.Errorf("%w: TIFF T.4 EOL byte alignment", ErrInvalid)
			}
			if options&1 != 0 {
				bit, err := f.bits(1)
				if err != nil {
					return err
				}
				oneDimensional = bit == 1
				if y == 0 && !oneDimensional {
					return fmt.Errorf("%w: TIFF T.4 first strip row", ErrInvalid)
				}
			}
		}
		row := dst[y*rowBytes : (y+1)*rowBytes]
		var err error
		if oneDimensional {
			changes, err = f.line1(row, width, changes[:0])
		} else {
			var end bool
			changes, end, err = f.line2(row, width, reference, changes[:0])
			if end {
				return fmt.Errorf("%w: TIFF fax premature EOFB", ErrInvalid)
			}
		}
		if err != nil {
			return err
		}
		if compression == 3 && f.literal {
			if f.literalWhite != 0 || f.literalBlack {
				return fmt.Errorf("%w: TIFF T.4 uncompressed line width", ErrInvalid)
			}
			if err := f.literalWord(); err != nil || !f.literalExit || f.literalWhite != 0 {
				return fmt.Errorf("%w: TIFF T.4 uncompressed line boundary", ErrInvalid)
			}
			f.literal, f.literalExit = false, false
		}
		for len(changes) > 0 && changes[len(changes)-1] == width {
			changes = changes[:len(changes)-1]
		}
		changes = append(changes, width, width, width)
		reference, changes = changes, reference[:0]
		if compression == 2 {
			f.position = (f.position + 7) &^ 7
		}
	}
	return nil
}

// decodeTIFFDeflate 按TIFF补充规范解压zlib流，拒绝截断、超长或尾部冗余字节
// 入参: dst 目标字节, src 压缩条带或图块字节
// 返回: error zlib解压、校验或长度错误
func decodeTIFFDeflate(dst, src []byte) error {
	input := bytes.NewReader(src)
	reader, err := zlib.NewReader(input)
	if err != nil {
		return fmt.Errorf("%w: TIFF deflate stream: %w", ErrInvalid, err)
	}
	if _, err := io.ReadFull(reader, dst); err != nil {
		_ = reader.Close()
		return fmt.Errorf("%w: TIFF deflate data: %w", ErrInvalid, err)
	}
	var extra [1]byte
	n, err := reader.Read(extra[:])
	if n != 0 || err != io.EOF {
		_ = reader.Close()
		return fmt.Errorf("%w: excessive TIFF deflate output", ErrInvalid)
	}
	if err := reader.Close(); err != nil {
		return fmt.Errorf("%w: TIFF deflate checksum: %w", ErrInvalid, err)
	}
	if input.Len() != 0 {
		return fmt.Errorf("%w: trailing TIFF deflate data", ErrInvalid)
	}
	return nil
}

// jpegColor 校验TIFF的YCbCr解释，非默认颜色参数留给专用颜色转换路径
// 返回: error 字段或颜色能力错误
func (d *tiffDirectory) jpegColor() error {
	if d.entry[532] == nil {
		return fmt.Errorf("%w: missing TIFF YCbCr ReferenceBlackWhite", ErrInvalid)
	}
	if err := d.rationalDefaults(529, [][2]uint32{{299, 1000}, {587, 1000}, {114, 1000}}); err != nil {
		return err
	}
	if err := d.rationalDefaults(532, [][2]uint32{{0, 1}, {255, 1}, {128, 1}, {255, 1}, {128, 1}, {255, 1}}); err != nil {
		return err
	}
	position, err := d.number(531, 1, false)
	if err != nil {
		return err
	}
	if position != 1 {
		return fmt.Errorf("%w: TIFF YCbCr positioning", ErrUnsupported)
	}
	return nil
}

// rationalDefaults 检查有理数字段及支持的默认解释，不将自定义参数静默替换
// 入参: tag 字段标识, expected 支持的分子分母列表
// 返回: error 字段或颜色能力错误
func (d *tiffDirectory) rationalDefaults(tag uint16, expected [][2]uint32) error {
	entry := d.entry[tag]
	if entry == nil {
		return nil
	}
	if d.order.Uint16(entry[2:]) != 5 || d.order.Uint32(entry[4:]) != uint32(len(expected)) {
		return fmt.Errorf("%w: TIFF rational tag %d", ErrInvalid, tag)
	}
	offset := uint64(d.order.Uint32(entry[8:]))
	size := uint64(len(expected)) * 8
	if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
		return fmt.Errorf("%w: TIFF rational tag %d offset", ErrInvalid, tag)
	}
	for i, want := range expected {
		n, q := d.order.Uint32(d.data[offset+uint64(i)*8:]), d.order.Uint32(d.data[offset+uint64(i)*8+4:])
		if q == 0 {
			return fmt.Errorf("%w: TIFF rational tag %d denominator", ErrInvalid, tag)
		}
		if uint64(n)*uint64(want[1]) != uint64(q)*uint64(want[0]) {
			return fmt.Errorf("%w: TIFF rational tag %d color interpretation", ErrUnsupported, tag)
		}
	}
	return nil
}

// jpegBlock 解码独立JPEG压缩块，按TIFF颜色解释读取原始分量并裁去边界填充
// 入参: out 目标图像, data JPEG压缩块, tables 共享码表, previous 前一块的帧参数, region 存储矩形, tiled 是否采用图块组织, photo TIFF颜色标识, bits 样本位数
// 返回: error 码流、布局或颜色能力错误
func (d *tiffDirectory) jpegBlock(out *rasterImage, data []byte, tables tiffJPEGTable, previous *tiffJPEGTable, region image.Rectangle, tiled bool, photo, bits uint32) error {
	stream, err := normalizeTIFFJPEG(data, false, tables)
	if err != nil {
		return err
	}
	if previous.process != 0 && (previous.process != stream.process || previous.precision != stream.precision || previous.components != stream.components || previous.identities != stream.identities) {
		return fmt.Errorf("%w: inconsistent TIFF JPEG frames", ErrInvalid)
	}
	channels, err := d.number(277, 1, false)
	if err != nil {
		return err
	}
	if uint32(stream.precision) != bits || int(stream.width) != region.Dx() || int(stream.height) != region.Dy() || stream.components != int(channels) {
		return fmt.Errorf("%w: TIFF JPEG frame layout", ErrInvalid)
	}
	*previous = stream
	previous.data = nil
	if len(tables.data) > 0 {
		merged := make([]byte, 0, len(stream.data)+len(tables.data))
		merged = append(merged, 0xff, 0xd8)
		merged = append(merged, tables.data...)
		merged = append(merged, stream.data[2:]...)
		stream.data = merged
	}
	if stream.components != out.channels {
		return d.jpegExtraBlock(out, stream, region, tiled, photo, bits)
	}
	if stream.process == 0xc3 {
		return decodeTIFFLosslessJPEG(out, stream, region, photo)
	}
	if photo == 5 {
		if stream.components != 4 || stream.sampling != [5]byte{0x11, 0x11, 0x11, 0x11} {
			return fmt.Errorf("%w: TIFF CMYK JPEG component layout", ErrInvalid)
		}
		hint := []byte{0xff, 0xd8, 0xff, 0xee, 0, 14, 'A', 'd', 'o', 'b', 'e', 0, 100, 0, 0, 0, 0, 0}
		stream.data = append(hint, stream.data[2:]...)
	}
	config, err := jpeg.DecodeConfig(bytes.NewReader(stream.data))
	if err != nil {
		return tiffJPEGDecodeError(err)
	}
	if config.Width != region.Dx() || config.Height != region.Dy() {
		return fmt.Errorf("%w: TIFF JPEG block dimensions", ErrInvalid)
	}
	if (config.ColorModel == color.CMYKModel) != (photo == 5) {
		return fmt.Errorf("%w: TIFF JPEG color component count", ErrInvalid)
	}
	decoded, err := jpeg.Decode(bytes.NewReader(stream.data))
	if err != nil {
		return tiffJPEGDecodeError(err)
	}
	gray, grayImage := decoded.(*image.Gray)
	cmyk, cmykImage := decoded.(*image.CMYK)
	ycbcr, ycbcrImage := decoded.(*image.YCbCr)
	if photo <= 1 && !grayImage || photo >= 2 && grayImage {
		return fmt.Errorf("%w: TIFF JPEG component count", ErrInvalid)
	}
	if ycbcrImage && photo == 2 && ycbcr.SubsampleRatio != image.YCbCrSubsampleRatio444 {
		return fmt.Errorf("%w: subsampled TIFF RGB JPEG", ErrInvalid)
	}
	if photo == 6 {
		if !ycbcrImage {
			return fmt.Errorf("%w: TIFF YCbCr JPEG components", ErrInvalid)
		}
		if err := d.jpegSubsampling(ycbcr.SubsampleRatio); err != nil {
			return err
		}
	}
	vertical := uint32(1)
	if ycbcrImage && (ycbcr.SubsampleRatio == image.YCbCrSubsampleRatio420 || ycbcr.SubsampleRatio == image.YCbCrSubsampleRatio440 || ycbcr.SubsampleRatio == image.YCbCrSubsampleRatio410) {
		vertical = 2
	}
	if tiled {
		horizontal := 1
		if ycbcrImage {
			switch ycbcr.SubsampleRatio {
			case image.YCbCrSubsampleRatio422, image.YCbCrSubsampleRatio420:
				horizontal = 2
			case image.YCbCrSubsampleRatio411, image.YCbCrSubsampleRatio410:
				horizontal = 4
			}
		}
		if region.Dx()%(8*horizontal) != 0 || region.Dy()%int(8*vertical) != 0 {
			return fmt.Errorf("%w: TIFF JPEG tile MCU alignment", ErrInvalid)
		}
	} else {
		stripRows, err := d.number(278, ^uint32(0), true)
		if err != nil {
			return err
		}
		if stripRows < uint32(out.bounds().Dy()) && stripRows%(8*vertical) != 0 {
			return fmt.Errorf("%w: TIFF JPEG strip MCU alignment", ErrInvalid)
		}
	}
	visible := region.Intersect(out.bounds())
	for y := range visible.Dy() {
		for x := range visible.Dx() {
			if cmykImage {
				value := cmyk.CMYKAt(x, y)
				at := ((region.Min.Y+y)*out.bounds().Dx() + region.Min.X + x) * 4
				for channel, sample := range [4]uint8{value.C, value.M, value.Y, value.K} {
					out.native.values[at+channel] = 65535 - uint16(sample)*257
				}
				continue
			}
			var pixel color.NRGBA64
			if grayImage {
				value := uint16(gray.GrayAt(x, y).Y) * 257
				if photo == 0 {
					value = 65535 - value
				}
				pixel = color.NRGBA64{value, value, value, 65535}
			} else if ycbcrImage && photo == 2 {
				value := ycbcr.YCbCrAt(x, y)
				pixel = color.NRGBA64{uint16(value.Y) * 257, uint16(value.Cb) * 257, uint16(value.Cr) * 257, 65535}
			} else {
				pixel = imagePixel(decoded, x, y)
			}
			out.pixels.(*image.NRGBA64).SetNRGBA64(region.Min.X+x, region.Min.Y+y, pixel)
		}
	}
	return nil
}

// tiffJPEGDecodeError 区分无效码流与标准解码器尚未提供的JPEG能力
// 入参: err 标准解码器错误
// 返回: error 带能力或数据分类的错误
func tiffJPEGDecodeError(err error) error {
	var unsupported jpeg.UnsupportedError
	if errors.As(err, &unsupported) {
		return fmt.Errorf("%w: TIFF JPEG decode: %w", ErrUnsupported, err)
	}
	return fmt.Errorf("%w: TIFF JPEG decode: %w", ErrInvalid, err)
}

// jpegSubsampling 核对TIFF声明的色度抽样与条带码流，不依赖图像扩展名或JFIF提示
// 入参: ratio 已解码的JPEG抽样布局
// 返回: error 字段、布局或能力错误
func (d *tiffDirectory) jpegSubsampling(ratio image.YCbCrSubsampleRatio) error {
	x, y := uint32(2), uint32(2)
	if d.entry[530] != nil {
		field, _, err := d.field(530, 2, false)
		if err != nil {
			return err
		}
		x, y = uint32(d.order.Uint16(field)), uint32(d.order.Uint16(field[2:]))
	}
	var expected image.YCbCrSubsampleRatio
	switch {
	case x == 1 && y == 1:
		expected = image.YCbCrSubsampleRatio444
	case x == 2 && y == 1:
		expected = image.YCbCrSubsampleRatio422
	case x == 2 && y == 2:
		expected = image.YCbCrSubsampleRatio420
	case x == 1 && y == 2:
		expected = image.YCbCrSubsampleRatio440
	case x == 4 && y == 1:
		expected = image.YCbCrSubsampleRatio411
	case x == 4 && y == 2:
		expected = image.YCbCrSubsampleRatio410
	default:
		return fmt.Errorf("%w: TIFF YCbCr subsampling", ErrUnsupported)
	}
	if expected != ratio {
		return fmt.Errorf("%w: TIFF JPEG subsampling mismatch", ErrInvalid)
	}
	return nil
}

// tiffJPEGSampleBuffer 为独立JPEG块分配有界原始样本，不提前解释颜色或透明度
// 入参: region 块存储矩形, channels 包含附加样本的分量数
// 返回: *rasterImage 块内原始分量, error 布局或容量错误
func tiffJPEGSampleBuffer(region image.Rectangle, channels int) (*rasterImage, error) {
	count := uint64(region.Dx()) * uint64(region.Dy())
	if region.Empty() || channels < 1 || channels > 5 {
		return nil, fmt.Errorf("%w: TIFF JPEG sample buffer layout", ErrInvalid)
	}
	if count > (64<<20)/uint64(2*channels) {
		return nil, fmt.Errorf("%w: TIFF JPEG sample buffer budget", ErrLimit)
	}
	native, err := newImageComponents(image.Rect(0, 0, region.Dx(), region.Dy()), channels, false, count*2)
	if err != nil {
		return nil, err
	}
	return &rasterImage{native: native, channels: channels}, nil
}

// jpegExtraBlock 解码附加样本，完成全部分量后统一应用TIFF透明度解释
// 入参: out 目标图像, stream 完整JPEG流, region 存储矩形, tiled 是否采用图块, photo TIFF颜色解释, bits 样本位数
// 返回: error 码流、布局或容量错误
func (d *tiffDirectory) jpegExtraBlock(out *rasterImage, stream tiffJPEGTable, region image.Rectangle, tiled bool, photo, bits uint32) error {
	for c := range stream.components {
		if stream.sampling[c] != 0x11 {
			return fmt.Errorf("%w: TIFF JPEG extra sample sampling", ErrInvalid)
		}
	}
	if stream.process != 0xc3 {
		if tiled && (region.Dx()%8 != 0 || region.Dy()%8 != 0) {
			return fmt.Errorf("%w: TIFF JPEG tile MCU alignment", ErrInvalid)
		}
		rows, err := d.number(278, ^uint32(0), true)
		if err != nil {
			return err
		}
		if !tiled && rows < uint32(out.bounds().Dy()) && rows%8 != 0 {
			return fmt.Errorf("%w: TIFF JPEG strip MCU alignment", ErrInvalid)
		}
	}
	raw, err := tiffJPEGSampleBuffer(region, stream.components)
	if err != nil {
		return err
	}
	if stream.process == 0xc3 {
		err = decodeTIFFLosslessJPEG(raw, stream, raw.bounds(), photo)
	} else {
		err = decodeTIFFJPEGPlanes(raw.native, stream)
	}
	if err != nil {
		return err
	}
	alpha, err := d.number(338, 0, false)
	if err != nil {
		return err
	}
	format := tiffPixelFormat{photo: photo, bits: bits, channels: uint32(stream.components), alpha: alpha}
	format.writeJPEGSamples(out, raw.native, region)
	return nil
}

// writeJPEGSamples 写入十六位原始样本，透明度和ICC颜色分量保持分离
// 入参: out 目标图像, raw 块内分量, region 块在目标图像中的位置
func (f *tiffPixelFormat) writeJPEGSamples(out *rasterImage, raw *imageComponents, region image.Rectangle) {
	visible := region.Intersect(out.bounds())
	row := make([]byte, visible.Dx()*raw.channels*2)
	format := *f
	format.order, format.bits = binary.BigEndian, 16
	for y := range visible.Dy() {
		start := y * raw.bounds.Dx() * raw.channels
		for i := range len(row) / 2 {
			binary.BigEndian.PutUint16(row[i*2:], raw.values[start+i])
		}
		if out.native != nil {
			format.writeComponentRange(out.native, visible.Min.X, visible.Min.Y+y, visible.Dx(), row)
		} else {
			format.writeRowRange(out.pixels.(*image.NRGBA64), visible.Min.X, visible.Min.Y+y, visible.Dx(), row)
		}
	}
}

// decodeTIFFJPEGPlanes 将顺序DCT扫描拆为独立灰度码流，复用标准库的反量化和IDCT
// 入参: out 原始分量缓冲, stream 已规范化的JPEG流
// 返回: error 帧、扫描、熵编码或容量错误
func decodeTIFFJPEGPlanes(out *imageComponents, stream tiffJPEGTable) error {
	if stream.process != 0xc0 && stream.process != 0xc1 {
		return fmt.Errorf("%w: TIFF JPEG extra sample process", ErrUnsupported)
	}
	if stream.precision != 8 {
		return fmt.Errorf("%w: TIFF JPEG extra sample precision", ErrInvalid)
	}
	blocks := uint64((out.bounds.Dx()+7)/8) * uint64((out.bounds.Dy()+7)/8)
	if blocks*uint64(out.channels)*64 > rasterMaxWork || uint64(len(stream.data))*uint64(out.channels) > rasterMaxWork {
		return fmt.Errorf("%w: TIFF JPEG component work", ErrLimit)
	}
	var identities [256]bool
	for c := range stream.components {
		id := stream.identities[c]
		if identities[id] {
			return fmt.Errorf("%w: duplicate TIFF JPEG frame component", ErrInvalid)
		}
		identities[id] = true
	}
	var huffman [8]losslessHuffman
	var quant [5]byte
	var seen [5]bool
	var restart uint16
	header := []byte{255, 216}
	for pos := 2; pos < len(stream.data); {
		start := pos
		for stream.data[pos] == 255 {
			pos++
		}
		marker := stream.data[pos]
		pos++
		if marker == 0xd9 {
			for c := range stream.components {
				if !seen[c] {
					return fmt.Errorf("%w: incomplete TIFF JPEG components", ErrInvalid)
				}
			}
			return nil
		}
		size := int(binary.BigEndian.Uint16(stream.data[pos:]))
		payload := stream.data[pos+2 : pos+size]
		pos += size
		switch marker {
		case 0xc0, 0xc1:
			for c := range stream.components {
				quant[c] = payload[8+c*3]
			}
		case 0xc4:
			for len(payload) != 0 {
				selector := payload[0]
				var h losslessHuffman
				code, index := uint32(0), 0
				for i, count := range payload[1:17] {
					h.first[i], h.count[i], h.index[i] = code, uint32(count), index
					code = (code + uint32(count)) << 1
					index += int(count)
				}
				h.symbols = payload[17 : 17+index]
				huffman[int(selector&15)+4*int(selector>>4)] = h
				payload = payload[17+index:]
			}
			header = append(header, stream.data[start:pos]...)
		case 0xdb:
			header = append(header, stream.data[start:pos]...)
		case 0xdd:
			if len(payload) != 2 {
				return fmt.Errorf("%w: TIFF JPEG restart header", ErrInvalid)
			}
			restart = binary.BigEndian.Uint16(payload)
			header = append(header, stream.data[start:pos]...)
		case 0xda:
			if len(payload) < 6 || payload[0] < 1 || payload[0] > 4 || len(payload) != 4+2*int(payload[0]) || !bytes.Equal(payload[len(payload)-3:], []byte{0, 63, 0}) {
				return fmt.Errorf("%w: TIFF sequential JPEG scan", ErrInvalid)
			}
			var components [4]int
			for i := range int(payload[0]) {
				component := -1
				for c := range stream.components {
					if stream.identities[c] == payload[1+i*2] {
						component = c
					}
				}
				if component < 0 || seen[component] {
					return fmt.Errorf("%w: TIFF sequential JPEG component coverage", ErrInvalid)
				}
				seen[component] = true
				components[i] = component
			}
			end, err := losslessJPEGEntropyEnd(stream.data, pos)
			if err != nil {
				return err
			}
			planes, err := tiffJPEGScanPlanes(stream.data[pos:end], payload, huffman, restart, int(blocks), stream.process)
			if err != nil {
				return err
			}
			for i := range int(payload[0]) {
				c := components[i]
				frame := []byte{8, byte(stream.height >> 8), byte(stream.height), byte(stream.width >> 8), byte(stream.width), 1, 1, 0x11, quant[c]}
				data := appendTIFFJPEGMarker(bytes.Clone(header), stream.process, frame)
				data = appendTIFFJPEGMarker(data, 0xda, []byte{1, 1, payload[2+i*2], 0, 63, 0})
				data = append(data, planes[i]...)
				data = append(data, 255, 217)
				decoded, err := jpeg.Decode(bytes.NewReader(data))
				if err != nil {
					return tiffJPEGDecodeError(err)
				}
				gray, ok := decoded.(*image.Gray)
				if !ok || gray.Bounds() != out.bounds {
					return fmt.Errorf("%w: TIFF JPEG component dimensions", ErrInvalid)
				}
				for y := range out.bounds.Dy() {
					for x := range out.bounds.Dx() {
						out.values[(y*out.bounds.Dx()+x)*out.channels+c] = uint16(gray.GrayAt(x, y).Y) * 257
					}
				}
			}
			pos = end
		}
	}
	return fmt.Errorf("%w: missing TIFF JPEG end marker", ErrInvalid)
}

// tiffJPEGScanPlanes 按MCU顺序分离等抽样DCT分量，保留原始霍夫曼码和重启边界
// 入参: data 扫描熵编码, scan 扫描头, tables 当前霍夫曼表, restart 重启间隔, blocks MCU数量, process JPEG过程
// 返回: [4][]byte 独立分量熵编码, error 编码或扫描错误
func tiffJPEGScanPlanes(data, scan []byte, tables [8]losslessHuffman, restart uint16, blocks int, process byte) ([4][]byte, error) {
	var result [4][]byte
	var writers [4]tiffJPEGEntropyWriter
	b := losslessBits{data: data}
	last := -1
	for block := range blocks {
		if block != 0 && restart != 0 && block%int(restart) == 0 {
			var err error
			last, err = b.restart(last)
			if err != nil || last != (block/int(restart)-1)&7 {
				return result, fmt.Errorf("%w: TIFF JPEG scan restart", ErrInvalid)
			}
			for c := range int(scan[0]) {
				writers[c].finish()
				writers[c].data = append(writers[c].data, 255, byte(0xd0+last))
			}
		}
		for c := range int(scan[0]) {
			selector := scan[2+c*2]
			if selector>>4 > 3 || selector&15 > 3 || process == 0xc0 && (selector>>4 > 1 || selector&15 > 1) {
				return result, fmt.Errorf("%w: TIFF JPEG Huffman selector", ErrInvalid)
			}
			w := &writers[c]
			symbol, err := w.symbol(&b, &tables[selector>>4])
			if err != nil || symbol > 11 {
				return result, fmt.Errorf("%w: TIFF JPEG DC category", ErrInvalid)
			}
			if err := w.copy(&b, uint(symbol)); err != nil {
				return result, err
			}
			for k := 1; k < 64; {
				symbol, err := w.symbol(&b, &tables[4+int(selector&15)])
				if err != nil {
					return result, err
				}
				if symbol == 0 {
					break
				}
				size, run := symbol&15, int(symbol>>4)
				if size == 0 {
					if run != 15 || k+16 > 64 {
						return result, fmt.Errorf("%w: TIFF JPEG AC zero run", ErrInvalid)
					}
					k += 16
					continue
				}
				k += run
				if size > 10 || k >= 64 {
					return result, fmt.Errorf("%w: TIFF JPEG AC coefficient", ErrInvalid)
				}
				if err := w.copy(&b, uint(size)); err != nil {
					return result, err
				}
				k++
			}
		}
	}
	if err := b.align(); err != nil {
		return result, err
	}
	if b.pos != len(data) {
		return result, fmt.Errorf("%w: TIFF JPEG trailing scan entropy", ErrInvalid)
	}
	for c := range int(scan[0]) {
		writers[c].finish()
		result[c] = writers[c].data
	}
	return result, nil
}

// symbol 读取并转写规范霍夫曼码，不改变系数或预测差值
// 入参: b 源位流, h 当前码表
// 返回: byte 符号, error 截断或码字错误
func (w *tiffJPEGEntropyWriter) symbol(b *losslessBits, h *losslessHuffman) (byte, error) {
	code := uint32(0)
	for n := range 16 {
		bit, err := b.bits(1)
		if err != nil {
			return 0, err
		}
		w.put(bit, 1)
		code = code<<1 | bit
		if code >= h.first[n] && code-h.first[n] < h.count[n] {
			return h.symbols[h.index[n]+int(code-h.first[n])], nil
		}
	}
	return 0, fmt.Errorf("%w: TIFF JPEG Huffman code", ErrInvalid)
}

// copy 转写指定数量的系数附加位
// 入参: b 源位流, count 位数
// 返回: error 截断或填充错误
func (w *tiffJPEGEntropyWriter) copy(b *losslessBits, count uint) error {
	value, err := b.bits(count)
	if err == nil {
		w.put(value, count)
	}
	return err
}

// put 写入高位优先的熵编码位，并对FF字节填充零
// 入参: value 位值, count 位数
func (w *tiffJPEGEntropyWriter) put(value uint32, count uint) {
	w.word = w.word<<count | value
	w.count += count
	for w.count >= 8 {
		w.count -= 8
		value := byte(w.word >> w.count)
		w.data = append(w.data, value)
		if value == 255 {
			w.data = append(w.data, 0)
		}
	}
}

// finish 用全一填充位结束当前熵编码段
func (w *tiffJPEGEntropyWriter) finish() {
	if w.count != 0 {
		count := 8 - w.count
		w.put(1<<count-1, count)
	}
}

// legacyExtraJPEG 校验多扫描交换流与TIFF逐分量定义，避免将五分量重建为非法单扫描
// 入参: width 宽度, height 高度, channels 分量数, bits 样本精度
// 返回: tiffLegacyExtraJPEG 完整交换流解码状态, error 字段、扫描或能力错误
func (d *tiffDirectory) legacyExtraJPEG(width, height, channels, bits uint32) (tiffLegacyExtraJPEG, error) {
	var result tiffLegacyExtraJPEG
	process, err := d.number(512, 0, false)
	if err != nil {
		return result, err
	}
	if d.entry[512] == nil || process != 1 && process != 14 || process == 1 && bits != 8 || channels != 5 {
		return result, fmt.Errorf("%w: TIFF multiscan JPEG process", ErrInvalid)
	}
	source, err := d.legacyInterchange()
	if err != nil {
		return result, err
	}
	if source == nil {
		return result, fmt.Errorf("%w: TIFF multiscan JPEG requires interchange scan definitions", ErrUnsupported)
	}
	if uint64(len(source)) > rasterMaxWork/5 {
		return result, fmt.Errorf("%w: TIFF multiscan interchange work", ErrLimit)
	}
	stream, err := normalizeTIFFJPEG(source, false, tiffJPEGTable{})
	if err != nil {
		return result, err
	}
	want := byte(0xc0)
	if process == 14 {
		want = 0xc3
	}
	if stream.process != want || stream.components != int(channels) || uint32(stream.precision) != bits || uint32(stream.width) != width || uint32(stream.height) != height {
		return result, fmt.Errorf("%w: TIFF multiscan JPEG interchange frame", ErrInvalid)
	}
	var definitions [3][5][]byte
	var predictors, points [5]uint32
	for kind, tag := range []uint16{519, 520, 521} {
		if process == 14 && tag != 520 {
			continue
		}
		if d.entry[tag] == nil || d.order.Uint16(d.entry[tag][2:]) != 4 {
			return result, fmt.Errorf("%w: TIFF multiscan JPEG table offsets", ErrInvalid)
		}
		field, _, err := d.field(tag, 5, true)
		if err != nil {
			return result, err
		}
		for c := range 5 {
			offset := uint64(d.order.Uint32(field[c*4:]))
			size := uint64(64)
			if tag != 519 {
				if offset > uint64(len(d.data)) || uint64(len(d.data))-offset < 16 {
					return result, fmt.Errorf("%w: TIFF multiscan Huffman offset", ErrInvalid)
				}
				size = 16
				for _, n := range d.data[offset : offset+16] {
					size += uint64(n)
				}
			}
			if offset > uint64(len(d.data)) || size > uint64(len(d.data))-offset {
				return result, fmt.Errorf("%w: TIFF multiscan JPEG table range", ErrInvalid)
			}
			definitions[kind][c] = d.data[offset : offset+size]
		}
	}
	if process == 14 {
		field, _, err := d.field(517, 5, false)
		if err != nil {
			return result, err
		}
		for c := range 5 {
			predictors[c] = uint32(d.order.Uint16(field[c*2:]))
		}
		if d.entry[518] != nil {
			field, _, err = d.field(518, 5, false)
			if err != nil {
				return result, err
			}
			for c := range 5 {
				points[c] = uint32(d.order.Uint16(field[c*2:]))
			}
		}
	}
	restart, err := d.number(515, 0, false)
	if err != nil {
		return result, err
	}
	if err := validateTIFFLegacyExtraScans(stream, definitions, predictors, points, uint16(restart)); err != nil {
		return result, err
	}
	for pos := 2; pos < len(source); {
		for source[pos] == 255 {
			pos++
		}
		marker := source[pos]
		pos++
		size := int(binary.BigEndian.Uint16(source[pos:]))
		pos += size
		if marker == 0xda {
			end := len(source) - 2
			for end > pos && source[end-1] == 0xff {
				end--
			}
			result.entropy = source[pos:end]
			break
		}
	}
	result.stream = stream
	return result, nil
}

// validateTIFFLegacyExtraScans 按扫描时的码表及分量身份核对交换流，不假定全部分量共享一个扫描
// 入参: stream 规范化交换流, definitions TIFF分量码表, predictors 预测器, points 点变换, interval TIFF重启间隔
// 返回: error 码表、覆盖或参数冲突
func validateTIFFLegacyExtraScans(stream tiffJPEGTable, definitions [3][5][]byte, predictors, points [5]uint32, interval uint16) error {
	var quant [5]byte
	var seen [5]bool
	var restart uint16
	tables := []byte{255, 216}
	for pos := 2; pos < len(stream.data); {
		start := pos
		for stream.data[pos] == 255 {
			pos++
		}
		marker := stream.data[pos]
		pos++
		if marker == 0xd9 {
			for _, covered := range seen {
				if !covered {
					return fmt.Errorf("%w: incomplete TIFF multiscan interchange", ErrInvalid)
				}
			}
			return nil
		}
		size := int(binary.BigEndian.Uint16(stream.data[pos:]))
		payload := stream.data[pos+2 : pos+size]
		pos += size
		switch marker {
		case 0xc0, 0xc3:
			for c := range 5 {
				quant[c] = payload[8+c*3]
			}
		case 0xc4, 0xdb:
			tables = append(tables, stream.data[start:pos]...)
		case 0xdd:
			if len(payload) != 2 {
				return fmt.Errorf("%w: TIFF multiscan restart header", ErrInvalid)
			}
			restart = binary.BigEndian.Uint16(payload)
		case 0xda:
			if len(payload) < 6 || payload[0] < 1 || payload[0] > 4 || len(payload) != 4+2*int(payload[0]) || restart != interval {
				return fmt.Errorf("%w: TIFF multiscan interchange scan", ErrInvalid)
			}
			header, err := readTIFFLegacyHeader(tables)
			if err != nil {
				return err
			}
			for i := range int(payload[0]) {
				c := -1
				for index := range 5 {
					if stream.identities[index] == payload[1+i*2] {
						c = index
					}
				}
				selector := payload[2+i*2]
				if c < 0 || seen[c] || selector>>4 > 3 || selector&15 > 3 {
					return fmt.Errorf("%w: TIFF multiscan interchange component", ErrInvalid)
				}
				seen[c] = true
				if !bytes.Equal(header.huffman[selector>>4], definitions[1][c]) {
					return fmt.Errorf("%w: conflicting TIFF multiscan DC table", ErrInvalid)
				}
				if stream.process == 0xc3 {
					if selector&15 != 0 || quant[c] != 0 || uint32(payload[len(payload)-3]) != predictors[c] || payload[len(payload)-2] != 0 || uint32(payload[len(payload)-1]) != points[c] {
						return fmt.Errorf("%w: conflicting TIFF multiscan prediction", ErrInvalid)
					}
				} else {
					if selector>>4 > 1 || selector&15 > 1 || quant[c] > 3 || !bytes.Equal(payload[len(payload)-3:], []byte{0, 63, 0}) || !bytes.Equal(header.quant[quant[c]], definitions[0][c]) || !bytes.Equal(header.huffman[4+int(selector&15)], definitions[2][c]) {
						return fmt.Errorf("%w: conflicting TIFF multiscan DCT definitions", ErrInvalid)
					}
				}
			}
			end, err := losslessJPEGEntropyEnd(stream.data, pos)
			if err != nil {
				return err
			}
			pos = end
		}
	}
	return fmt.Errorf("%w: missing TIFF multiscan interchange end", ErrInvalid)
}

// jpegTables 读取可选共享码表，不将TIFF字段的字节序应用到JPEG数据
// 返回: tiffJPEGTable 共享码表, error 字段或码流错误
func (d *tiffDirectory) jpegTables() (tiffJPEGTable, error) {
	data, err := d.byteField(347, rasterMaxWork)
	if err != nil {
		return tiffJPEGTable{}, err
	}
	if data == nil {
		return tiffJPEGTable{}, nil
	}
	value, err := normalizeTIFFJPEG(data, true, tiffJPEGTable{})
	if err != nil {
		return tiffJPEGTable{}, err
	}
	value.data = value.data[2 : len(value.data)-2]
	return value, nil
}

// normalizeTIFFJPEG 校验JPEG标记，忽略TIFF不采用的APP和注释，并检查共享码表不能被条带重定义
// 入参: data JPEG数据, tables 是否为仅含码表的流, global 预加载的共享槽位
// 返回: tiffJPEGTable 规范化码流及其槽位, error 数据或能力错误
func normalizeTIFFJPEG(data []byte, tables bool, global tiffJPEGTable) (tiffJPEGTable, error) {
	if len(data) < 4 || data[0] != 0xff || data[1] != 0xd8 {
		return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG start marker", ErrInvalid)
	}
	value := tiffJPEGTable{data: make([]byte, 0, len(data))}
	value.data = append(value.data, 0xff, 0xd8)
	pos, sawScan := 2, false
	for pos < len(data) {
		start := pos
		if data[pos] != 0xff {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG marker prefix", ErrInvalid)
		}
		for pos < len(data) && data[pos] == 0xff {
			pos++
		}
		if pos == len(data) {
			return tiffJPEGTable{}, fmt.Errorf("%w: truncated TIFF JPEG marker", ErrInvalid)
		}
		marker := data[pos]
		pos++
		if marker == 0xd9 {
			if pos != len(data) || !tables && !sawScan {
				return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG end marker", ErrInvalid)
			}
			value.data = append(value.data, 0xff, 0xd9)
			return value, nil
		}
		if marker == 0xd8 || marker == 0 || marker == 1 || marker >= 0xd0 && marker <= 0xd7 {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG standalone marker", ErrInvalid)
		}
		if pos+2 > len(data) {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG marker size", ErrInvalid)
		}
		size := int(binary.BigEndian.Uint16(data[pos:]))
		if size < 2 || size > len(data)-pos {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG marker length", ErrInvalid)
		}
		payload := data[pos+2 : pos+size]
		pos += size
		if marker >= 0xe0 && marker <= 0xef || marker == 0xfe {
			continue
		}
		if tables && (marker == 0xcc || marker == 0xdd) {
			continue
		}
		if tables && marker != 0xdb && marker != 0xc4 {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG table stream marker", ErrInvalid)
		}
		if marker == 0xdb || marker == 0xc4 {
			quant, huffman, err := tiffJPEGSlots(payload, marker)
			if err != nil {
				return tiffJPEGTable{}, err
			}
			if quant&global.quant != 0 || huffman&global.huffman != 0 {
				return tiffJPEGTable{}, fmt.Errorf("%w: redefined TIFF JPEG global table", ErrInvalid)
			}
			value.quant |= quant
			value.huffman |= huffman
		}
		if marker == 0xc0 || marker == 0xc1 || marker == 0xc2 || marker == 0xc3 {
			if value.process != 0 {
				return tiffJPEGTable{}, fmt.Errorf("%w: multiple TIFF JPEG frames", ErrInvalid)
			}
			value.process = marker
			if len(payload) < 6 || payload[5] == 0 || len(payload) != 6+3*int(payload[5]) {
				return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG frame components", ErrInvalid)
			}
			value.components = int(payload[5])
			value.precision = payload[0]
			value.height = binary.BigEndian.Uint16(payload[1:])
			value.width = binary.BigEndian.Uint16(payload[3:])
			for component := range min(value.components, len(value.sampling)) {
				value.sampling[component] = payload[7+3*component]
				value.identities[component] = payload[6+3*component]
			}
		}
		if marker == 0xdc {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG DNL marker", ErrInvalid)
		}
		if marker != 0xdb && marker != 0xc4 && marker != 0xda && marker != 0xdd && marker != 0xc0 && marker != 0xc1 && marker != 0xc2 && marker != 0xc3 {
			return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG process marker %x", ErrUnsupported, marker)
		}
		value.data = append(value.data, data[start:pos]...)
		if marker == 0xda {
			if value.process == 0 {
				return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG scan before frame", ErrInvalid)
			}
			sawScan = true
			start = pos
			for pos < len(data) {
				if data[pos] != 0xff {
					pos++
					continue
				}
				mark := pos
				for pos < len(data) && data[pos] == 0xff {
					pos++
				}
				if pos == len(data) {
					return tiffJPEGTable{}, fmt.Errorf("%w: TIFF JPEG entropy end", ErrInvalid)
				}
				code := data[pos]
				if code == 0 || code >= 0xd0 && code <= 0xd7 {
					pos++
					continue
				}
				pos = mark
				break
			}
			value.data = append(value.data, data[start:pos]...)
		}
	}
	return tiffJPEGTable{}, fmt.Errorf("%w: missing TIFF JPEG end marker", ErrInvalid)
}

// tiffJPEGSlots 校验量化与霍夫曼定义并取得码表槽位，条带本地码表允许按扫描重定义
// 入参: data 标记负载, marker DQT或DHT标记
// 返回: uint16 量化槽位, uint16 霍夫曼槽位, error 定义错误
func tiffJPEGSlots(data []byte, marker byte) (uint16, uint16, error) {
	if len(data) == 0 {
		return 0, 0, fmt.Errorf("%w: empty JPEG table definition", ErrInvalid)
	}
	var quant, huffman uint16
	for len(data) > 0 {
		code := data[0]
		data = data[1:]
		kind, id := code>>4, code&15
		if id > 3 || kind > 1 {
			return 0, 0, fmt.Errorf("%w: TIFF JPEG table selector", ErrInvalid)
		}
		if marker == 0xdb {
			size := 64 * (1 + int(kind))
			if len(data) < size {
				return 0, 0, fmt.Errorf("%w: TIFF JPEG quantization size", ErrInvalid)
			}
			for i := 0; i < size; i += 1 + int(kind) {
				if kind == 0 && data[i] == 0 || kind == 1 && binary.BigEndian.Uint16(data[i:]) == 0 {
					return 0, 0, fmt.Errorf("%w: zero TIFF JPEG quantization value", ErrInvalid)
				}
			}
			quant |= 1 << id
			data = data[size:]
		} else {
			if len(data) < 16 {
				return 0, 0, fmt.Errorf("%w: TIFF JPEG Huffman counts", ErrInvalid)
			}
			size, available := 0, 1
			for _, count := range data[:16] {
				size += int(count)
				available = available*2 - int(count)
				if available < 0 {
					return 0, 0, fmt.Errorf("%w: oversubscribed TIFF JPEG Huffman table", ErrInvalid)
				}
			}
			if size == 0 || size > 256 || available == 0 || len(data)-16 < size {
				return 0, 0, fmt.Errorf("%w: TIFF JPEG Huffman values", ErrInvalid)
			}
			huffman |= 1 << (id + 4*kind)
			data = data[16+size:]
		}
	}
	return quant, huffman, nil
}

// decodeTIFFLosslessJPEG 解码压缩7的独立SOF3块，按扫描应用当前码表与预测参数并遵循TIFF颜色顺序
// 入参: out 目标图像, stream 已校验并载入共享码表的JPEG流, region 存储矩形, photo TIFF颜色解释
// 返回: error 帧、扫描、熵编码或能力错误
func decodeTIFFLosslessJPEG(out *rasterImage, stream tiffJPEGTable, region image.Rectangle, photo uint32) error {
	if stream.components < 1 || stream.components > 5 || stream.precision < 2 || stream.precision > 16 {
		return fmt.Errorf("%w: TIFF lossless JPEG frame", ErrInvalid)
	}
	if photo == 6 {
		return fmt.Errorf("%w: TIFF lossless JPEG YCbCr sampling", ErrUnsupported)
	}
	var identities [256]bool
	for c := range stream.components {
		id := stream.identities[c]
		if identities[id] {
			return fmt.Errorf("%w: duplicate TIFF lossless JPEG component", ErrInvalid)
		}
		identities[id] = true
		if stream.sampling[c] != 0x11 {
			return fmt.Errorf("%w: TIFF lossless JPEG component sampling", ErrInvalid)
		}
	}
	var huffman [4]losslessHuffman
	var restart uint16
	covered, frameSeen := 0, false
	for pos := 2; pos < len(stream.data); {
		for pos < len(stream.data) && stream.data[pos] == 0xff {
			pos++
		}
		if pos == len(stream.data) {
			return fmt.Errorf("%w: TIFF lossless JPEG marker", ErrInvalid)
		}
		marker := stream.data[pos]
		pos++
		if marker == 0xd9 {
			if covered != stream.components || pos != len(stream.data) {
				return fmt.Errorf("%w: incomplete TIFF lossless JPEG components", ErrInvalid)
			}
			return nil
		}
		size := int(binary.BigEndian.Uint16(stream.data[pos:]))
		payload := stream.data[pos+2 : pos+size]
		pos += size
		switch marker {
		case 0xc3:
			frameSeen = true
			for c := range stream.components {
				if payload[8+c*3] != 0 {
					return fmt.Errorf("%w: TIFF lossless JPEG quantization selector", ErrInvalid)
				}
			}
		case 0xc4:
			for len(payload) != 0 {
				selector := payload[0]
				payload = payload[1:]
				length := 16
				for _, count := range payload[:16] {
					length += int(count)
				}
				if selector>>4 == 0 {
					var err error
					huffman[selector&15], err = readLosslessHuffman(payload[:length])
					if err != nil {
						return err
					}
				}
				payload = payload[length:]
			}
		case 0xdd:
			if len(payload) != 2 {
				return fmt.Errorf("%w: TIFF lossless JPEG restart header", ErrInvalid)
			}
			restart = binary.BigEndian.Uint16(payload)
		case 0xda:
			if !frameSeen || len(payload) < 4 || payload[0] == 0 || payload[0] > 4 || int(payload[0]) > stream.components-covered || len(payload) != 4+2*int(payload[0]) {
				return fmt.Errorf("%w: TIFF lossless JPEG scan", ErrInvalid)
			}
			predictor, point := uint32(payload[len(payload)-3]), uint32(payload[len(payload)-1])
			if predictor < 1 || predictor > 7 || payload[len(payload)-2] != 0 || point >= uint32(stream.precision) {
				return fmt.Errorf("%w: TIFF lossless JPEG scan parameters", ErrInvalid)
			}
			l := tiffLegacyJPEG{channels: int(payload[0]), lossless: true, bits: uint32(stream.precision), restart: restart, strictRestart: true}
			var components [4]int
			for c := range l.channels {
				id, selector := payload[1+c*2], payload[2+c*2]
				if id != stream.identities[covered+c] || selector&15 != 0 || selector>>4 > 3 || huffman[selector>>4].symbols == nil {
					return fmt.Errorf("%w: TIFF lossless JPEG scan component", ErrInvalid)
				}
				l.scanOrder[c] = byte(c)
				l.huffman[c] = huffman[selector>>4]
				l.predictor[c], l.point[c] = predictor, point
				components[c] = covered + c
			}
			end, err := losslessJPEGEntropyEnd(stream.data, pos)
			if err != nil {
				return err
			}
			if err := l.losslessBlockDecode(out, stream.data[pos:end], region, photo, components[:l.channels]); err != nil {
				return err
			}
			covered += l.channels
			pos = end
		}
	}
	return fmt.Errorf("%w: missing TIFF lossless JPEG end marker", ErrInvalid)
}

// legacyLosslessJPEG 校验无损JPEG的逐分量预测、点变换和霍夫曼表，不采用DCT码表
// 入参: width 图像宽度, height 图像高度, photo TIFF颜色解释, channels 分量数, bits 样本精度
// 返回: tiffLegacyJPEG 解码参数, error 字段或能力错误
func (d *tiffDirectory) legacyLosslessJPEG(width, height, photo, channels, bits uint32) (tiffLegacyJPEG, error) {
	l := tiffLegacyJPEG{channels: int(channels), lossless: true, bits: bits, tables: []byte{0xff, 0xd8}}
	if channels < 1 || channels > 4 || bits < 2 || bits > 16 {
		return l, fmt.Errorf("%w: TIFF lossless JPEG sample layout", ErrInvalid)
	}
	if photo == 6 {
		return l, fmt.Errorf("%w: TIFF lossless JPEG YCbCr sampling", ErrUnsupported)
	}
	restart, err := d.number(515, 0, false)
	if err != nil {
		return l, err
	}
	l.restart = uint16(restart)
	predictors, _, err := d.field(517, l.channels, false)
	if err != nil {
		return l, err
	}
	var points []byte
	if d.entry[518] != nil {
		points, _, err = d.field(518, l.channels, false)
		if err != nil {
			return l, err
		}
	}
	if d.entry[520] == nil || d.order.Uint16(d.entry[520][2:]) != 4 {
		return l, fmt.Errorf("%w: TIFF lossless JPEG Huffman offset field", ErrInvalid)
	}
	offsets, _, err := d.field(520, l.channels, true)
	if err != nil {
		return l, err
	}
	var definitions [4][]byte
	for c := range l.channels {
		l.sampling[c], l.scanOrder[c], l.dc[c] = 0x11, byte(c), byte(c)
		l.predictor[c] = uint32(d.order.Uint16(predictors[c*2:]))
		if points != nil {
			l.point[c] = uint32(d.order.Uint16(points[c*2:]))
		}
		if l.predictor[c] < 1 || l.predictor[c] > 7 || l.point[c] >= bits {
			return l, fmt.Errorf("%w: TIFF lossless JPEG prediction parameters", ErrInvalid)
		}
		offset := uint64(d.order.Uint32(offsets[c*4:]))
		if offset > uint64(len(d.data)) || uint64(len(d.data))-offset < 16 {
			return l, fmt.Errorf("%w: TIFF lossless JPEG Huffman offset", ErrInvalid)
		}
		size := uint64(16)
		for _, count := range d.data[offset : offset+16] {
			size += uint64(count)
		}
		if size > 33 || size > uint64(len(d.data))-offset {
			return l, fmt.Errorf("%w: TIFF lossless JPEG Huffman range", ErrInvalid)
		}
		definitions[c] = d.data[offset : offset+size]
		l.huffman[c], err = readLosslessHuffman(definitions[c])
		if err != nil {
			return l, err
		}
		payload := append([]byte{byte(c)}, definitions[c]...)
		l.tables = appendTIFFJPEGMarker(l.tables, 0xc4, payload)
	}
	interchange, err := d.legacyInterchange()
	if err != nil || interchange == nil {
		return l, err
	}
	stream, err := normalizeTIFFJPEG(interchange, false, tiffJPEGTable{})
	if err != nil {
		return l, err
	}
	if stream.process != 0xc3 || stream.components != l.channels || !bytes.Equal(stream.sampling[:l.channels], l.sampling[:l.channels]) {
		return l, fmt.Errorf("%w: TIFF lossless JPEG interchange frame", ErrInvalid)
	}
	h, err := readTIFFLegacyHeader(stream.data)
	if err != nil {
		return l, err
	}
	if len(h.frame) != 6+3*l.channels || uint32(h.frame[0]) != bits || uint32(binary.BigEndian.Uint16(h.frame[1:])) != height || uint32(binary.BigEndian.Uint16(h.frame[3:])) != width || len(h.scan) != 4+2*l.channels || int(h.scan[0]) != l.channels || h.scan[len(h.scan)-2] != 0 || h.scan[len(h.scan)-1]>>4 != 0 || h.restart != l.restart {
		return l, fmt.Errorf("%w: TIFF lossless JPEG interchange dimensions or scan", ErrInvalid)
	}
	var seen [4]bool
	for scanIndex := range l.channels {
		identity := h.scan[1+scanIndex*2]
		component := -1
		for c := range l.channels {
			if h.frame[6+c*3] == identity {
				component = c
				break
			}
		}
		selector := h.scan[2+scanIndex*2]
		if component < 0 || seen[component] || selector&15 != 0 || selector>>4 > 3 {
			return l, fmt.Errorf("%w: TIFF lossless JPEG interchange component", ErrInvalid)
		}
		seen[component] = true
		if h.frame[8+component*3] != 0 || uint32(h.scan[len(h.scan)-3]) != l.predictor[component] || uint32(h.scan[len(h.scan)-1]) != l.point[component] || !bytes.Equal(h.huffman[selector>>4], definitions[component]) {
			return l, fmt.Errorf("%w: conflicting TIFF lossless JPEG interchange definitions", ErrInvalid)
		}
		l.scanOrder[scanIndex] = byte(component)
	}
	l.interchange = true
	return l, nil
}

// losslessBlockDecode 复用两行样本解码TIFF独立块或JPEG分量扫描
// 入参: out 目标图像, data 熵编码字节, region 存储矩形, photo TIFF颜色解释, components JPEG目标通道，nil表示TIFF块
// 返回: error 熵编码、样本或资源错误
func (l *tiffLegacyJPEG) losslessBlockDecode(out *rasterImage, data []byte, region image.Rectangle, photo uint32, components []int) error {
	width, height := region.Dx(), region.Dy()
	if width < 1 || height < 1 || width > 65535 || height > 65535 {
		return fmt.Errorf("%w: lossless JPEG dimensions", ErrLimit)
	}
	if uint64(width)*uint64(height)*uint64(l.channels) > rasterMaxWork || uint64(len(data)) > rasterMaxWork {
		return fmt.Errorf("%w: lossless JPEG decoding budget", ErrLimit)
	}
	rows := make([]uint16, width*l.channels*2)
	previous, current := rows[:width*l.channels], rows[width*l.channels:]
	b := losslessBits{data: data}
	restartMCU, lastRestart := 0, -1
	visible := region.Intersect(out.bounds())
	maximum := uint32((1 << l.bits) - 1)
	scale := uint32(65535) / maximum
	if scale*maximum != 65535 {
		scale = 0
	}
	for y := range height {
		for x := range width {
			mcu := y*width + x
			if mcu != 0 && l.restart != 0 && mcu%int(l.restart) == 0 {
				var err error
				lastRestart, err = b.restart(lastRestart)
				if err != nil {
					return err
				}
				if l.strictRestart && lastRestart != (mcu/int(l.restart)-1)&7 {
					return fmt.Errorf("%w: TIFF lossless JPEG initial restart", ErrInvalid)
				}
				restartMCU = mcu
			}
			since := mcu - restartMCU
			var sample [4]uint16
			for scanIndex := range l.channels {
				c := int(l.scanOrder[scanIndex])
				at := x*l.channels + c
				prediction := 1 << (l.bits - l.point[c] - 1)
				if since > 0 && since < width {
					if x != 0 {
						prediction = int(current[at-l.channels])
					}
				} else if since >= width {
					prediction = int(previous[at])
					if x != 0 && since > width {
						prediction = losslessPrediction(l.predictor[c], int(current[at-l.channels]), int(previous[at]), int(previous[at-l.channels]))
					}
				}
				difference, err := b.difference(&l.huffman[c])
				if err != nil {
					return err
				}
				value := uint16(prediction + difference)
				if uint32(value) > (1<<(l.bits-l.point[c]))-1 {
					return fmt.Errorf("%w: lossless JPEG sample range", ErrInvalid)
				}
				current[at] = value
				expanded := uint32(value) << l.point[c]
				if scale == 0 {
					sample[c] = uint16(expanded * 65535 / maximum)
				} else {
					sample[c] = uint16(expanded * scale)
				}
			}
			if x >= visible.Dx() || y >= visible.Dy() {
				continue
			}
			targetX, targetY := region.Min.X+x, region.Min.Y+y
			if components != nil {
				if out.native != nil {
					at := (targetY*out.bounds().Dx() + targetX) * out.native.channels
					for c, component := range components {
						out.native.values[at+component] = sample[c]
					}
					continue
				}
				pixels := out.pixels.(*image.NRGBA64)
				at := pixels.PixOffset(targetX, targetY)
				if out.channels == 1 {
					if photo == 0 {
						sample[0] = 65535 - sample[0]
					}
					for c := range 3 {
						binary.BigEndian.PutUint16(pixels.Pix[at+c*2:], sample[0])
					}
				} else {
					for c, component := range components {
						binary.BigEndian.PutUint16(pixels.Pix[at+component*2:], sample[c])
					}
				}
				pixels.Pix[at+6], pixels.Pix[at+7] = 255, 255
			} else if out.native != nil {
				at := (targetY*out.bounds().Dx() + targetX) * l.channels
				copy(out.native.values[at:at+l.channels], sample[:l.channels])
			} else {
				if photo == 0 {
					sample[0] = 65535 - sample[0]
				}
				if photo <= 1 {
					sample[1], sample[2] = sample[0], sample[0]
				}
				out.pixels.(*image.NRGBA64).SetNRGBA64(targetX, targetY, color.NRGBA64{sample[0], sample[1], sample[2], 65535})
			}
		}
		previous, current = current, previous
	}
	if err := b.align(); err != nil {
		return err
	}
	if b.pos != len(data) {
		return fmt.Errorf("%w: lossless JPEG trailing entropy", ErrInvalid)
	}
	return nil
}
