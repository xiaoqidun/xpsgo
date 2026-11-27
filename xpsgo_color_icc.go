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
	"crypto/md5"
	"encoding/binary"
	"fmt"
	"image/color"
	"maps"
	"math"
	"math/big"
	"slices"
	"time"
)

// iccMaxTags 与 iccMaxCurveSamples 限制ICC配置标签数量与曲线采样数上限
const (
	iccMaxTags         = 4096
	iccMaxCurveSamples = 1 << 20
)

// iccMetadataCacheEntries 定义ICC配置元数据缓存容量上限
const iccMetadataCacheEntries = 4096

// iccPCSFromLinearRGB 保存线性RGB到D50连接空间的转换矩阵
var iccPCSFromLinearRGB, _ = iccInverseMatrix(iccPCSDisplayMatrix)

// iccPCSWhite 保存ICC标准D50连接空间白点XYZ坐标
var iccPCSWhite = [3]float64{0.9642, 1, 0.8249}

// iccXYZD65ToLinearRGB 保存D65参考白XYZ到线性sRGB的直接显示矩阵
var iccXYZD65ToLinearRGB = iccDisplayD65Matrix()

// iccPCSDisplayMatrix 保存D50连接空间到线性sRGB显示空间的转换矩阵
var iccPCSDisplayMatrix = iccDisplayMatrix()

// ICCNamedColor 保存ICC命名色条目的名称、前后缀、连接空间坐标、显示近似sRGB及可选设备坐标
type ICCNamedColor struct {
	Name   string
	Prefix string
	Suffix string
	PCS    [3]float64
	SRGB   color.NRGBA
	Device []float64
}

// ICCColorant 保存ICC色料表（clrt/clot）单个通道的色料名称、连接空间坐标及显示近似sRGB，DeviceLink配置的PCS与SRGB为零值
type ICCColorant struct {
	Name string
	PCS  [3]float64
	SRGB color.NRGBA
}

// ICCProfileInfo 保存ICC配置文件的头部属性、默认渲染意图、可选命名色表及可选输入与输出色料表与色料顺序信息
type ICCProfileInfo struct {
	Version          uint32
	Class            string
	ColorSpace       string
	PCS              string
	Channels         int
	DefaultIntent    RenderingIntent
	NamedColors      []ICCNamedColor
	Colorants        []ICCColorant
	ColorantOrder    []uint8
	OrderedColorants []string
	OutputColorants  []ICCColorant
}

// iccTag 保存标签的数据范围，多个标签可以共享完全相同的数据
type iccTag struct {
	offset uint32
	size   uint32
}

// iccProfile 保存ICC头和只读标签，不丢弃未知私有标签
type iccProfile struct {
	data     []byte
	tags     map[string]iccTag
	version  uint32
	class    string
	space    string
	pcs      string
	intent   uint32
	channels int
}

// iccMetadataValidator 限制元数据检查的累计工作量，不复制配置文件或改写私有标签
type iccMetadataValidator struct {
	ctx       context.Context
	remaining uint64
}

// iccTargetTransform 将D50连接空间转换为目标设备分量，不承担源颜色解释或页面合成
type iccTargetTransform struct {
	profile     *iccProfile
	pipeline    *iccPipeline
	inverse     [3]iccInverseCurve
	matrix      [9]float64
	white       [3]float64
	absolutePCS bool
	gray        bool
	intent      uint32
}

// iccTransform 保存已选渲染意图的源配置文件转换，输出D50参考条件的XYZ
type iccTransform struct {
	profile     *iccProfile
	pipeline    *iccPipeline
	curves      [3]iccCurve
	matrix      [9]float64
	white       [3]float64
	absolutePCS bool
	gray        bool
	intent      uint32
	named       []iccNamedColor
}

// InspectICCProfile 探测ICC配置文件头部、空间通道、默认渲染意图、可选ncl2命名专色表及可选clrt/clot/clro色料表与铺墨顺序
// 入参: data ICC配置文件完整字节
// 返回: *ICCProfileInfo 只读配置元数据, error 头部、标签、版本、命名色或色料表错误
func InspectICCProfile(data []byte) (*ICCProfileInfo, error) {
	profile, err := parseICCProfile(data)
	if err != nil {
		return nil, err
	}
	info := &ICCProfileInfo{
		Version:       profile.version,
		Class:         profile.class,
		ColorSpace:    profile.space,
		PCS:           profile.pcs,
		Channels:      profile.channels,
		DefaultIntent: RenderingIntent(profile.intent + 1),
	}
	if profile.class == "nmcl" || profile.tag("ncl2") != nil && (profile.pcs == "XYZ " || profile.pcs == "Lab ") {
		named, err := parseICCNamedColor(profile)
		if err != nil {
			return nil, err
		}
		info.NamedColors = make([]ICCNamedColor, len(named))
		for i, entry := range named {
			linear := iccMatrixColor(iccPCSDisplayMatrix, entry.xyz)
			info.NamedColors[i] = ICCNamedColor{
				Name:   entry.name,
				Prefix: entry.prefix,
				Suffix: entry.suffix,
				PCS:    entry.pcs,
				SRGB: color.NRGBA{
					R: colorQuantize8(renderLinearToSRGB(colorClamp(linear[0]))),
					G: colorQuantize8(renderLinearToSRGB(colorClamp(linear[1]))),
					B: colorQuantize8(renderLinearToSRGB(colorClamp(linear[2]))),
					A: 255,
				},
				Device: slices.Clone(entry.device),
			}
		}
	}
	colorants, err := parseICCColorantTable(profile, false)
	if err != nil {
		return nil, err
	}
	outputColorants, err := parseICCColorantTable(profile, true)
	if err != nil {
		return nil, err
	}
	order, err := parseICCColorantOrder(profile)
	if err != nil {
		return nil, err
	}
	info.Colorants = colorants
	info.OutputColorants = outputColorants
	info.ColorantOrder = order
	if len(colorants) > 0 {
		info.OrderedColorants = make([]string, len(colorants))
		if len(order) > 0 {
			for i, idx := range order {
				info.OrderedColorants[i] = colorants[idx].Name
			}
		} else {
			for i, entry := range colorants {
				info.OrderedColorants[i] = entry.Name
			}
		}
	}
	return info, nil
}

// parseICCColorantTable 解析ICC规范clrt输入色料表或DeviceLink的clot输出色料表标签
// 入参: profile 已解析ICC配置, output 是否解析clot输出色料表
// 返回: []ICCColorant 按声明顺序排列的色料条目，缺失目标标签时返回nil, error 结构、编码或通道数错误
func parseICCColorantTable(profile *iccProfile, output bool) ([]ICCColorant, error) {
	tag := "clrt"
	if output {
		tag = "clot"
	}
	data := profile.tag(tag)
	if data == nil {
		return nil, nil
	}
	return parseICCColorantTableData(data, profile, output, false, nil)
}

// parseICCColorantTableData 统一校验并解析clrt/clot色料表二进制载荷，供读写两侧复用
// 严格拒绝空色料名、重复色料名及NUL后非零填充；DeviceLink配置按ICC.1规范跳过PCS与SRGB转换
// 入参: data 色料表原始标签字节, p 已解析ICC配置, output 是否为DeviceLink输出色料表, strictSize 是否禁止尾随对齐填充字节, step 可选工作量及取消回调
// 返回: []ICCColorant 解析后的色料条目列表, error 结构、类型、编码、通道数、重复名或取消错误
func parseICCColorantTableData(data []byte, p *iccProfile, output, strictSize bool, step func(uint64) error) ([]ICCColorant, error) {
	if err := iccMetadataType(data, "clrt"); err != nil {
		return nil, err
	}
	if len(data) < 12 {
		return nil, fmt.Errorf("%w: ICC colorant table header", ErrInvalid)
	}
	channels := p.channels
	if output {
		if p.class != "link" {
			return nil, fmt.Errorf("%w: ICC output colorant profile class", ErrInvalid)
		}
		channels = iccColorChannels(p.pcs)
	}
	if channels == 0 {
		return nil, fmt.Errorf("%w: ICC colorant channels", ErrUnsupported)
	}
	count := uint64(binary.BigEndian.Uint32(data[8:]))
	if count == 0 || count > iccMaxChannels || count != uint64(channels) {
		return nil, fmt.Errorf("%w: ICC colorant table count", ErrInvalid)
	}
	const stride = 38
	expected := uint64(12) + count*stride
	if strictSize {
		if uint64(len(data)) != expected {
			return nil, fmt.Errorf("%w: ICC colorant table size", ErrInvalid)
		}
	} else {
		if uint64(len(data)) < expected || uint64(len(data))-expected > 3 {
			return nil, fmt.Errorf("%w: ICC colorant table size", ErrInvalid)
		}
		for _, value := range data[expected:] {
			if value != 0 {
				return nil, fmt.Errorf("%w: ICC colorant table padding", ErrInvalid)
			}
		}
	}
	names := make(map[string]bool, int(count))
	entries := make([]ICCColorant, int(count))
	for i := range count {
		if step != nil {
			if err := step(stride); err != nil {
				return nil, err
			}
		}
		row := data[12+i*stride : 12+(i+1)*stride]
		name, err := iccNamedASCIIText(row[:32])
		if err != nil {
			return nil, err
		}
		if name == "" {
			return nil, fmt.Errorf("%w: ICC empty colorant name", ErrInvalid)
		}
		if names[name] {
			return nil, fmt.Errorf("%w: ICC duplicate colorant name", ErrInvalid)
		}
		names[name] = true
		var pcsCoord [3]float64
		var srgb color.NRGBA
		if p.class != "link" {
			var raw [3]uint16
			for axis := range 3 {
				raw[axis] = binary.BigEndian.Uint16(row[32+axis*2:])
			}
			var xyz [3]float64
			hasXYZ := false
			if p.pcs == "XYZ " {
				for axis := range 3 {
					xyz[axis] = float64(raw[axis]) / 32768
				}
				pcsCoord, hasXYZ = xyz, true
			} else if p.pcs == "Lab " {
				if p.version >= 0x04000000 {
					pcsCoord = [3]float64{float64(raw[0]) * 100 / 65535, float64(raw[1])*255/65535 - 128, float64(raw[2])*255/65535 - 128}
				} else {
					pcsCoord = [3]float64{min(100, float64(raw[0])*100/65280), float64(raw[1])/256 - 128, float64(raw[2])/256 - 128}
				}
				xyz, hasXYZ = iccLabToXYZ(pcsCoord), true
			} else {
				for axis := range 3 {
					pcsCoord[axis] = float64(raw[axis]) / 65535
				}
			}
			if hasXYZ {
				linear := iccMatrixColor(iccPCSDisplayMatrix, xyz)
				srgb = color.NRGBA{
					R: colorQuantize8(renderLinearToSRGB(colorClamp(linear[0]))),
					G: colorQuantize8(renderLinearToSRGB(colorClamp(linear[1]))),
					B: colorQuantize8(renderLinearToSRGB(colorClamp(linear[2]))),
					A: 255,
				}
			}
		}
		entries[i] = ICCColorant{Name: name, PCS: pcsCoord, SRGB: srgb}
	}
	return entries, nil
}

// parseICCColorantOrder 解析ICC规范clro色料顺序标签，校验长度为设备通道数的完整无重复置换
// 入参: profile 已解析ICC配置
// 返回: []uint8 零基色料通道顺序索引，缺失clro时返回nil, error 结构、通道数或索引置换错误
func parseICCColorantOrder(profile *iccProfile) ([]uint8, error) {
	data := profile.tag("clro")
	if data == nil {
		return nil, nil
	}
	if len(data) < 12 || string(data[:4]) != "clro" || binary.BigEndian.Uint32(data[4:]) != 0 {
		return nil, fmt.Errorf("%w: ICC colorant order header", ErrInvalid)
	}
	count := uint64(binary.BigEndian.Uint32(data[8:]))
	if count == 0 || count > iccMaxChannels || int(count) != profile.channels {
		return nil, fmt.Errorf("%w: ICC colorant order count", ErrInvalid)
	}
	expected := uint64(12) + count
	if uint64(len(data)) < expected || uint64(len(data))-expected > 3 {
		return nil, fmt.Errorf("%w: ICC colorant order size", ErrInvalid)
	}
	for _, value := range data[expected:] {
		if value != 0 {
			return nil, fmt.Errorf("%w: ICC colorant order padding", ErrInvalid)
		}
	}
	var seen [iccMaxChannels]bool
	order := make([]uint8, int(count))
	for i := range int(count) {
		idx := data[12+i]
		if uint64(idx) >= count || seen[idx] {
			return nil, fmt.Errorf("%w: ICC colorant order index", ErrInvalid)
		}
		seen[idx] = true
		order[i] = idx
	}
	return order, nil
}

// parseICCProfile 校验ICC封装和标签范围，输入在配置文件使用期间不得修改
// 入参: data 配置文件字节
// 返回: *iccProfile 只读配置文件, error 数据、版本或资源错误
func parseICCProfile(data []byte) (*iccProfile, error) {
	if len(data) < 132 || string(data[36:40]) != "acsp" {
		return nil, fmt.Errorf("%w: ICC profile header", ErrInvalid)
	}
	size := uint64(binary.BigEndian.Uint32(data))
	if size < 132 || size > uint64(len(data)) {
		return nil, fmt.Errorf("%w: ICC profile length", ErrInvalid)
	}
	data = data[:size]
	version := binary.BigEndian.Uint32(data[8:])
	if version>>24 != 2 && version>>24 != 4 {
		return nil, fmt.Errorf("%w: ICC profile version", ErrUnsupported)
	}
	intent := binary.BigEndian.Uint32(data[64:])
	if intent > 3 {
		return nil, fmt.Errorf("%w: ICC rendering intent", ErrInvalid)
	}
	p := &iccProfile{data: data, tags: make(map[string]iccTag), version: version, class: string(data[12:16]), space: string(data[16:20]), pcs: string(data[20:24]), intent: intent}
	switch p.class {
	case "scnr", "mntr", "prtr", "link", "spac", "abst", "nmcl":
	default:
		return nil, fmt.Errorf("%w: ICC profile class %q", ErrUnsupported, p.class)
	}
	p.channels = iccColorChannels(p.space)
	if p.channels == 0 {
		return nil, fmt.Errorf("%w: ICC data color space %q", ErrUnsupported, p.space)
	}
	if p.class != "link" && p.pcs != "XYZ " && p.pcs != "Lab " {
		return nil, fmt.Errorf("%w: ICC connection space %q", ErrInvalid, p.pcs)
	}
	count := uint64(binary.BigEndian.Uint32(data[128:]))
	if count > iccMaxTags {
		return nil, fmt.Errorf("%w: ICC tag count", ErrLimit)
	}
	end := uint64(132) + 12*count
	if end > size {
		return nil, fmt.Errorf("%w: ICC tag directory", ErrInvalid)
	}
	ranges := make([]iccTag, 0, int(count))
	for i := range count {
		entry := data[132+i*12 : 132+(i+1)*12]
		name := string(entry[:4])
		if _, exists := p.tags[name]; exists {
			return nil, fmt.Errorf("%w: duplicate ICC tag %q", ErrInvalid, name)
		}
		tag := iccTag{binary.BigEndian.Uint32(entry[4:]), binary.BigEndian.Uint32(entry[8:])}
		if uint64(tag.offset) < end || tag.offset%4 != 0 || tag.size < 8 || uint64(tag.offset)+uint64(tag.size) > size {
			return nil, fmt.Errorf("%w: ICC tag %q range", ErrInvalid, name)
		}
		p.tags[name] = tag
		ranges = append(ranges, tag)
	}
	slices.SortFunc(ranges, func(a, b iccTag) int {
		if value := cmp.Compare(a.offset, b.offset); value != 0 {
			return value
		}
		return cmp.Compare(a.size, b.size)
	})
	for i := 1; i < len(ranges); i++ {
		previous, current := ranges[i-1], ranges[i]
		if uint64(current.offset) < uint64(previous.offset)+uint64(previous.size) && current != previous {
			return nil, fmt.Errorf("%w: overlapping ICC tag data", ErrInvalid)
		}
	}
	return p, nil
}

// iccColorChannels 取得ICC定义的通道数，保留合法的多通道空间供转换能力单独判断
// 入参: signature 四字节色彩空间标识
// 返回: int 通道数，未知空间为零
func iccColorChannels(signature string) int {
	switch signature {
	case "GRAY":
		return 1
	case "RGB ", "XYZ ", "Lab ", "Luv ", "YCbr", "Yxy ", "HSV ", "HLS ", "CMY ":
		return 3
	case "CMYK":
		return 4
	}
	if len(signature) != 4 || signature[1:] != "CLR" {
		return 0
	}
	if signature[0] >= '2' && signature[0] <= '9' {
		return int(signature[0] - '0')
	}
	if signature[0] >= 'A' && signature[0] <= 'F' {
		return int(signature[0]-'A') + 10
	}
	return 0
}

// tag 取得标签的原始只读字节，未定义时返回nil
// 入参: name 四字节标签标识
// 返回: []byte 原始标签
func (p *iccProfile) tag(name string) []byte {
	tag, ok := p.tags[name]
	if !ok {
		return nil
	}
	return p.data[uint64(tag.offset) : uint64(tag.offset)+uint64(tag.size)]
}

// inputChannels 返回ICC配置用于颜色分量校验的输入通道数，命名专色配置取ncl2命名色数量
// 返回: int 输入通道数
func (p *iccProfile) inputChannels() int {
	if p == nil {
		return 0
	}
	if p.class == "nmcl" {
		if ncl2 := p.tag("ncl2"); len(ncl2) >= 16 {
			return int(binary.BigEndian.Uint32(ncl2[12:16]))
		}
	}
	return p.channels
}

// iccFixed 解码ICC有符号15.16定点数
// 入参: data 已检查长度的四字节数值
// 返回: float64 精确表示的定点值
func iccFixed(data []byte) float64 {
	return float64(int32(binary.BigEndian.Uint32(data))) / 65536
}

// iccXYZ 读取单个XYZ标签值，不提前裁剪配置文件的色彩空间参数
// 入参: data 标签字节
// 返回: [3]float64 XYZ三分量, error 标签错误
func iccXYZ(data []byte) ([3]float64, error) {
	if len(data) != 20 || string(data[:4]) != "XYZ " || binary.BigEndian.Uint32(data[4:]) != 0 {
		return [3]float64{}, fmt.Errorf("%w: ICC XYZ tag", ErrInvalid)
	}
	return [3]float64{iccFixed(data[8:]), iccFixed(data[12:]), iccFixed(data[16:])}, nil
}

// validateCreatedICCHeader 按ICC版本校验新写入配置文件的头部、白点、标识及外层数据布局
// 入参: p 已解析且保持不变的配置文件, ctx 可选取消Context
// 返回: error 头部、数据布局、标识校验或取消错误
func validateCreatedICCHeader(p *iccProfile, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if p == nil || len(p.data) < 132 {
		return fmt.Errorf("%w: ICC profile header", ErrInvalid)
	}
	data := p.data
	if uint64(binary.BigEndian.Uint32(data)) != uint64(len(data)) || string(data[36:40]) != "acsp" {
		return fmt.Errorf("%w: ICC profile size or signature", ErrInvalid)
	}
	if data[8]>>4 > 9 || data[8]&15 > 9 || data[9]>>4 > 9 || data[9]&15 > 9 || binary.BigEndian.Uint16(data[10:]) != 0 {
		return fmt.Errorf("%w: ICC profile version encoding", ErrInvalid)
	}
	if data[8] != 2 && data[8] != 4 {
		return fmt.Errorf("%w: ICC profile major version", ErrUnsupported)
	}
	if err := validateCreatedICCSpaces(data); err != nil {
		return err
	}
	if err := validateCreatedICCDate(data[24:36]); err != nil {
		return err
	}
	switch platform := string(data[40:44]); platform {
	case "\x00\x00\x00\x00", "APPL", "MSFT", "SGI ", "SUNW":
	case "TGNT":
		if data[8] != 2 {
			return fmt.Errorf("%w: ICC primary platform %q", ErrUnsupported, platform)
		}
	default:
		return fmt.Errorf("%w: ICC primary platform %q", ErrUnsupported, platform)
	}
	if binary.BigEndian.Uint32(data[64:]) > 3 {
		return fmt.Errorf("%w: ICC rendering intent", ErrInvalid)
	}
	white := [3]float64{iccFixed(data[68:]), iccFixed(data[72:]), iccFixed(data[76:])}
	if !iccD50White(binary.BigEndian.Uint32(data[8:]), white) {
		return fmt.Errorf("%w: ICC PCS illuminant must be D50", ErrInvalid)
	}
	if data[8] == 4 && data[9]>>4 == 4 && binary.BigEndian.Uint32(data[60:])&^uint32(15) != 0 {
		return fmt.Errorf("%w: ICC reserved device attributes", ErrInvalid)
	}
	var reserved [28]byte
	if data[8] == 4 && !bytes.Equal(data[100:128], reserved[:]) {
		return fmt.Errorf("%w: ICC reserved profile header", ErrInvalid)
	}
	if err := validateCreatedICCLayout(p, ctx); err != nil {
		return err
	}
	if data[8] == 4 {
		return validateCreatedICCIdentity(data, ctx)
	}
	return checkContext(ctx)
}

// iccDisplayWhite 判断v4显示类白点是否符合D50约束，不对其他版本或类别施加显示类限制
// 入参: p 已解析的配置文件, white 从XYZType解码的白点
// 返回: bool 是否满足显示类白点约束，配置文件为nil时为false
func iccDisplayWhite(p *iccProfile, white [3]float64) bool {
	if p == nil {
		return false
	}
	if p.version>>24 != 4 || p.class != "mntr" {
		return true
	}
	return iccD50White(p.version, white)
}

// iccReadDisplayWhite 校验读取路径的显示类白点，放宽ICCv4.0至v4.2非D50白点而对v4.3及以上保持D50约束
// 入参: p 已解析的配置文件, white 从XYZType解码的白点
// 返回: bool 是否满足读取路径显示类白点约束
func iccReadDisplayWhite(p *iccProfile, white [3]float64) bool {
	if p.version>>24 != 4 || p.class != "mntr" || p.version>>20&15 < 3 {
		return true
	}
	return iccD50White(p.version, white)
}

// iccSelectTransformTag 按ICC.1:2010优先级选择源或目标转换标签，v4优先采用浮点管线并排除抽象配置的D2B3路由
// 入参: profile 已解析配置文件, intent ICC渲染意图, forward 是否为设备到PCS方向
// 返回: string 选中标签名, []byte 标签字节，未找到为空
func iccSelectTransformTag(profile *iccProfile, intent uint32, forward bool) (string, []byte) {
	if profile.class == "abst" {
		if !forward {
			return "", nil
		}
		if profile.version>>24 == 4 {
			if data := profile.tag("D2B0"); data != nil {
				return "D2B0", data
			}
		}
		if data := profile.tag("A2B0"); data != nil {
			return "A2B0", data
		}
		return "", nil
	}
	var candidates []string
	if profile.version>>24 == 4 {
		if forward {
			candidates = [4][]string{
				{"D2B0", "A2B0"},
				{"D2B1", "A2B1", "D2B0", "A2B0"},
				{"D2B2", "A2B2", "D2B0", "A2B0"},
				{"D2B3", "D2B1", "A2B1", "D2B0", "A2B0"},
			}[intent]
		} else {
			candidates = [4][]string{
				{"B2D0", "B2A0"},
				{"B2D1", "B2A1", "B2D0", "B2A0"},
				{"B2D2", "B2A2", "B2D0", "B2A0"},
				{"B2D3", "B2D1", "B2A1", "B2D0", "B2A0"},
			}[intent]
		}
	} else if forward {
		candidates = [4][]string{{"A2B0"}, {"A2B1", "A2B0"}, {"A2B2", "A2B0"}, {"A2B1", "A2B0"}}[intent]
	} else {
		candidates = [4][]string{{"B2A0"}, {"B2A1", "B2A0"}, {"B2A2", "B2A0"}, {"B2A1", "B2A0"}}[intent]
	}
	for _, name := range candidates {
		if data := profile.tag(name); data != nil {
			return name, data
		}
	}
	return "", nil
}

// iccD50White 按ICC版本校验s15Fixed16编码的D50标准白点
// 入参: version 配置文件版本, white 从XYZNumber解码的白点
// 返回: bool 是否符合当前版本的D50判定规则
func iccD50White(version uint32, white [3]float64) bool {
	for i, component := range []int64{9642, 10000, 8249} {
		scaled := white[i] * 65536
		if !(scaled >= -2147483648 && scaled <= 2147483647) || scaled != float64(int32(scaled)) {
			return false
		}
		value := int64(scaled)
		if version>>24 == 4 && version>>20&15 >= 4 {
			difference := value*10000 - component*65536
			if difference <= -32768 || difference >= 32768 {
				return false
			}
		} else if value != (component*65536+5000)/10000 {
			return false
		}
	}
	return true
}

// validateCreatedICCSpaces 校验设备空间、连接空间及抽象配置文件的PCS输入约束
// 入参: data 已检查长度的配置文件头
// 返回: error 配置文件类别或色彩空间错误
func validateCreatedICCSpaces(data []byte) error {
	class, space, pcs := string(data[12:16]), string(data[16:20]), string(data[20:24])
	switch class {
	case "scnr", "mntr", "prtr", "link", "spac", "abst", "nmcl":
	default:
		return fmt.Errorf("%w: ICC profile class %q", ErrUnsupported, class)
	}
	if iccColorChannels(space) == 0 {
		return fmt.Errorf("%w: ICC data color space %q", ErrUnsupported, space)
	}
	if class == "link" {
		if iccColorChannels(pcs) == 0 {
			return fmt.Errorf("%w: ICC DeviceLink output color space %q", ErrUnsupported, pcs)
		}
	} else if pcs != "XYZ " && pcs != "Lab " {
		return fmt.Errorf("%w: ICC connection space %q", ErrInvalid, pcs)
	}
	if class == "abst" && space != "XYZ " && space != "Lab " {
		return fmt.Errorf("%w: ICC abstract profile input must be PCS", ErrInvalid)
	}
	return nil
}

// validateCreatedICCDate 校验创建时间的公历日期及时分秒，不推测时区或限制年份为四位
// 入参: data 十二字节dateTimeNumber
// 返回: error 日期或时间分量错误
func validateCreatedICCDate(data []byte) error {
	year, month, day := int(binary.BigEndian.Uint16(data)), int(binary.BigEndian.Uint16(data[2:])), int(binary.BigEndian.Uint16(data[4:]))
	hour, minute, second := int(binary.BigEndian.Uint16(data[6:])), int(binary.BigEndian.Uint16(data[8:])), int(binary.BigEndian.Uint16(data[10:]))
	if month < 1 || month > 12 || day < 1 || day > 31 || hour > 23 || minute > 59 || second > 59 {
		return fmt.Errorf("%w: ICC profile creation time", ErrInvalid)
	}
	date := time.Date(year, time.Month(month), day, hour, minute, second, 0, time.UTC)
	if date.Day() != day {
		return fmt.Errorf("%w: ICC profile creation date", ErrInvalid)
	}
	return nil
}

// validateCreatedICCLayout 校验共享标签及对齐填充，仅对v4.4要求所有唯一数据连续排列
// 入参: p 已解析的配置文件, ctx 可选取消Context
// 返回: error 标签共用头、范围、对齐或取消错误
func validateCreatedICCLayout(p *iccProfile, ctx context.Context) error {
	data := p.data
	count := uint64(binary.BigEndian.Uint32(data[128:]))
	if count > iccMaxTags {
		return fmt.Errorf("%w: ICC tag count", ErrLimit)
	}
	end := uint64(132) + 12*count
	if end > uint64(len(data)) || count != uint64(len(p.tags)) {
		return fmt.Errorf("%w: ICC tag directory", ErrInvalid)
	}
	ranges := make([]iccTag, 0, len(p.tags))
	for _, tag := range p.tags {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if uint64(tag.offset) < end || tag.offset%4 != 0 || tag.size < 8 || uint64(tag.offset)+uint64(tag.size) > uint64(len(data)) {
			return fmt.Errorf("%w: ICC tag data range", ErrInvalid)
		}
		ranges = append(ranges, tag)
	}
	slices.SortFunc(ranges, func(a, b iccTag) int {
		if result := cmp.Compare(a.offset, b.offset); result != 0 {
			return result
		}
		return cmp.Compare(a.size, b.size)
	})
	var previous iccTag
	for _, tag := range ranges {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if tag == previous {
			continue
		}
		if uint64(tag.offset) < end {
			return fmt.Errorf("%w: overlapping ICC tag data", ErrInvalid)
		}
		if data[8] == 4 && (previous.size == 0 || data[9]>>4 == 4) && uint64(tag.offset) != end {
			return fmt.Errorf("%w: ICC tag data gap", ErrInvalid)
		}
		start := uint64(tag.offset)
		if binary.BigEndian.Uint32(data[start+4:]) != 0 {
			return fmt.Errorf("%w: ICC reserved tag header", ErrInvalid)
		}
		end = start + uint64(tag.size)
		if data[8] == 4 {
			aligned := (end + 3) &^ uint64(3)
			if aligned > uint64(len(data)) {
				return fmt.Errorf("%w: ICC truncated tag padding", ErrInvalid)
			}
			for _, value := range data[end:aligned] {
				if value != 0 {
					return fmt.Errorf("%w: ICC nonzero tag padding", ErrInvalid)
				}
			}
			end = aligned
		}
		previous = tag
	}
	if data[8] == 4 && end != uint64(len(data)) {
		return fmt.Errorf("%w: ICC trailing profile data", ErrInvalid)
	}
	return checkContext(ctx)
}

// validateCreatedICCIdentity 分段计算并核验ICCv4非零ProfileID的MD5标识
// 入参: data 完整配置文件, ctx 可选取消Context
// 返回: error 标识不匹配或取消错误
func validateCreatedICCIdentity(data []byte, ctx context.Context) error {
	var zero [16]byte
	if bytes.Equal(data[84:100], zero[:]) {
		return checkContext(ctx)
	}
	digest := md5.New()
	for _, span := range []struct{ start, end int }{{0, 44}, {48, 64}, {68, 84}, {100, len(data)}} {
		for offset := span.start; offset < span.end; {
			if err := checkContext(ctx); err != nil {
				return err
			}
			end := offset + min(span.end-offset, 64<<10)
			_, _ = digest.Write(data[offset:end])
			offset = end
		}
		if span.end == 44 || span.end == 64 {
			_, _ = digest.Write(zero[:4])
		} else if span.end == 84 {
			_, _ = digest.Write(zero[:])
		}
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	if !bytes.Equal(digest.Sum(nil), data[84:100]) {
		return fmt.Errorf("%w: ICC profile ID mismatch", ErrInvalid)
	}
	return nil
}

// validateCreatedICCMetadata 按ICC版本校验描述、序列、色料及色度适应矩阵标签
// 入参: p 已解析的配置文件, ctx 可选取消Context
// 返回: error 标签格式、能力、资源或取消错误
func validateCreatedICCMetadata(p *iccProfile, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if p == nil {
		return fmt.Errorf("%w: ICC metadata profile", ErrInvalid)
	}
	major := p.version >> 24
	if major != 2 && major != 4 {
		return fmt.Errorf("%w: ICC metadata version", ErrUnsupported)
	}
	v := iccMetadataValidator{ctx: ctx, remaining: uint64(len(p.data))*16 + 4096}
	for _, name := range [...]string{"desc", "cprt", "dmnd", "dmdd", "vued", "pseq", "clrt", "clot", "chad"} {
		tag, exists := p.tags[name]
		if !exists {
			continue
		}
		if err := v.step(1); err != nil {
			return err
		}
		end := uint64(tag.offset) + uint64(tag.size)
		if tag.size < 8 || end > uint64(len(p.data)) {
			return fmt.Errorf("%w: ICC metadata %s range", ErrInvalid, name)
		}
		data := p.data[uint64(tag.offset):end]
		var err error
		switch name {
		case "desc", "cprt", "dmnd", "dmdd", "vued":
			if major == 4 {
				_, err = v.localized(data)
			} else if name == "cprt" {
				err = iccMetadataType(data, "text")
				if err == nil {
					err = v.ascii(data[8:])
				}
			} else {
				var used uint64
				used, err = v.description(data)
				if err == nil && used != uint64(len(data)) {
					err = fmt.Errorf("%w: ICC description size", ErrInvalid)
				}
			}
		case "pseq":
			err = v.sequence(data, major)
		case "clrt", "clot":
			minor := p.version >> 20 & 15
			defined := major == 4 && (name == "clrt" || name == "clot" && minor >= 2)
			if !defined {
				if binary.BigEndian.Uint32(data[4:]) != 0 {
					err = fmt.Errorf("%w: ICC extension type header", ErrInvalid)
				}
			} else {
				_, err = parseICCColorantTableData(data, p, name == "clot", true, v.step)
			}
		case "chad":
			err = iccMetadataAdaptation(data, major == 4)
		}
		if err != nil {
			return fmt.Errorf("ICC metadata %s: %w", name, err)
		}
	}
	return checkContext(ctx)
}

// step 检查取消状态并扣除本次检查的工作量
// 入参: n 本次访问的字节或记录数
// 返回: error 取消或资源错误
func (v *iccMetadataValidator) step(n uint64) error {
	if err := checkContext(v.ctx); err != nil {
		return err
	}
	if n > v.remaining {
		return fmt.Errorf("%w: ICC metadata work", ErrLimit)
	}
	v.remaining -= n
	return nil
}

// iccMetadataType 区分错误的标准类型与尚未解释的扩展类型
// 入参: data 标签字节, expected 允许的类型标识
// 返回: error 格式或能力错误
func iccMetadataType(data []byte, expected string) error {
	if len(data) < 8 || binary.BigEndian.Uint32(data[4:]) != 0 {
		return fmt.Errorf("%w: ICC metadata type header", ErrInvalid)
	}
	typeName := string(data[:4])
	if typeName == expected {
		return nil
	}
	switch typeName {
	case "desc", "text", "mluc", "pseq", "clrt", "sf32", "chrm", "clro", "curv", "data", "dtim", "mft1", "mft2", "mAB ", "mBA ", "meas", "ncl2", "ncol", "para", "rcs2", "scrn", "sig ", "uf32", "bfd ", "ui16", "ui32", "ui64", "ui08", "view", "XYZ ", "crdi", "devs", "dict", "mpet", "psid", "cicp":
		return fmt.Errorf("%w: ICC metadata type %q, expected %q", ErrInvalid, typeName, expected)
	default:
		return fmt.Errorf("%w: ICC metadata type %q", ErrUnsupported, typeName)
	}
}

// ascii 检查计入长度的7位ASCII字符串及其末尾终止符
// 入参: data 字符串字节
// 返回: error 编码、终止、资源或取消错误
func (v *iccMetadataValidator) ascii(data []byte) error {
	if len(data) == 0 || data[len(data)-1] != 0 {
		return fmt.Errorf("%w: ICC ASCII termination", ErrInvalid)
	}
	for i, value := range data[:len(data)-1] {
		if i%1024 == 0 {
			if err := v.step(uint64(min(1024, len(data)-1-i))); err != nil {
				return err
			}
		}
		if value > 127 || value == 0 {
			return fmt.Errorf("%w: ICC ASCII string", ErrInvalid)
		}
	}
	return nil
}

// description 校验ICCv2描述标签的ASCII、UTF-16BE及ScriptCode字段并返回占用字节数
// 入参: data 从描述类型起始处开始的字节
// 返回: uint64 描述占用字节数, error 格式、能力、资源或取消错误
func (v *iccMetadataValidator) description(data []byte) (uint64, error) {
	if err := iccMetadataType(data, "desc"); err != nil {
		return 0, err
	}
	if len(data) < 12 {
		return 0, fmt.Errorf("%w: ICC description count", ErrInvalid)
	}
	end := 12 + uint64(binary.BigEndian.Uint32(data[8:]))
	if end+8 > uint64(len(data)) {
		return 0, fmt.Errorf("%w: ICC description ASCII range", ErrInvalid)
	}
	if err := v.ascii(data[12:end]); err != nil {
		return 0, err
	}
	count := uint64(binary.BigEndian.Uint32(data[end+4:]))
	start := end + 8
	end = start + 2*count
	if end+70 > uint64(len(data)) {
		return 0, fmt.Errorf("%w: ICC description Unicode range", ErrInvalid)
	}
	if count != 0 {
		if binary.BigEndian.Uint16(data[end-2:]) != 0 {
			return 0, fmt.Errorf("%w: ICC description Unicode termination", ErrInvalid)
		}
		if err := v.utf16(data[start:end-2], true); err != nil {
			return 0, err
		}
	}
	scriptCount := int(data[end+2])
	if scriptCount > 67 || scriptCount != 0 && data[end+3+uint64(scriptCount)-1] != 0 {
		return 0, fmt.Errorf("%w: ICC ScriptCode description", ErrInvalid)
	}
	return end + 70, nil
}

// localized 检查mluc记录和UTF-16BE存储，允许记录共享字符串及扩展记录步长
// 入参: data 从mluc类型起始处开始的字节
// 返回: uint64 已引用数据的结束位置, error 格式、资源或取消错误
func (v *iccMetadataValidator) localized(data []byte) (uint64, error) {
	if err := iccMetadataType(data, "mluc"); err != nil {
		return 0, err
	}
	if len(data) < 16 {
		return 0, fmt.Errorf("%w: ICC localized header", ErrInvalid)
	}
	count, stride := uint64(binary.BigEndian.Uint32(data[8:])), uint64(binary.BigEndian.Uint32(data[12:]))
	if count == 0 {
		return 16, nil
	}
	if stride < 12 || 16+count*stride > uint64(len(data)) {
		return 0, fmt.Errorf("%w: ICC localized records", ErrInvalid)
	}
	end := 16 + count*stride
	used := end
	checked := make(map[iccTag]bool)
	for i := uint64(0); i < count; i++ {
		if err := v.step(1); err != nil {
			return 0, err
		}
		row := data[16+i*stride:]
		if row[0] < 'a' || row[0] > 'z' || row[1] < 'a' || row[1] > 'z' || (row[2] != 0 || row[3] != 0) && (row[2] < 'A' || row[2] > 'Z' || row[3] < 'A' || row[3] > 'Z') {
			return 0, fmt.Errorf("%w: ICC localized language or region", ErrInvalid)
		}
		rangeKey := iccTag{offset: binary.BigEndian.Uint32(row[8:]), size: binary.BigEndian.Uint32(row[4:])}
		start, size := uint64(rangeKey.offset), uint64(rangeKey.size)
		if size%2 != 0 || start < end || start+size > uint64(len(data)) {
			return 0, fmt.Errorf("%w: ICC localized string range", ErrInvalid)
		}
		used = max(used, start+size)
		if checked[rangeKey] {
			continue
		}
		if err := v.utf16(data[start:start+size], false); err != nil {
			return 0, err
		}
		if len(checked) < iccMetadataCacheEntries {
			checked[rangeKey] = true
		}
	}
	return used, nil
}

// utf16 按码元长度检查UTF-16BE及代理对，不分配解码副本
// 入参: data 字符串字节，不含v2描述的终止符, nonzero 是否禁止字段内部出现零码元
// 返回: error 编码、资源或取消错误
func (v *iccMetadataValidator) utf16(data []byte, nonzero bool) error {
	if len(data)%2 != 0 {
		return fmt.Errorf("%w: ICC Unicode byte length", ErrInvalid)
	}
	checkpoint := 0
	for i := 0; i < len(data); i += 2 {
		if i >= checkpoint {
			if err := v.step(uint64(min(1024, len(data)-i))); err != nil {
				return err
			}
			checkpoint = i + 1024
		}
		value := binary.BigEndian.Uint16(data[i:])
		if nonzero && value == 0 {
			return fmt.Errorf("%w: ICC embedded Unicode terminator", ErrInvalid)
		}
		if value >= 0xd800 && value <= 0xdbff {
			if i+4 > len(data) {
				return fmt.Errorf("%w: ICC Unicode surrogate", ErrInvalid)
			}
			next := binary.BigEndian.Uint16(data[i+2:])
			if next < 0xdc00 || next > 0xdfff {
				return fmt.Errorf("%w: ICC Unicode surrogate", ErrInvalid)
			}
			i += 2
		} else if value >= 0xdc00 && value <= 0xdfff {
			return fmt.Errorf("%w: ICC Unicode surrogate", ErrInvalid)
		}
	}
	return nil
}

// sequence 检查配置文件序列及逐项内嵌的制造商、型号描述
// 入参: data 序列标签, major ICC主版本
// 返回: error 格式、能力、资源或取消错误
func (v *iccMetadataValidator) sequence(data []byte, major uint32) error {
	if err := iccMetadataType(data, "pseq"); err != nil {
		return err
	}
	if len(data) < 12 {
		return fmt.Errorf("%w: ICC sequence header", ErrInvalid)
	}
	count := uint64(binary.BigEndian.Uint32(data[8:]))
	minimum := uint64(52)
	if major == 2 {
		minimum = 202
	}
	if count > uint64(len(data)-12)/minimum {
		return fmt.Errorf("%w: ICC sequence count", ErrInvalid)
	}
	position := uint64(12)
	for range count {
		if err := v.step(1); err != nil {
			return err
		}
		if position+20 > uint64(len(data)) {
			return fmt.Errorf("%w: ICC sequence entry", ErrInvalid)
		}
		position += 20
		for range 2 {
			var used uint64
			var err error
			if major == 2 {
				used, err = v.description(data[position:])
			} else {
				used, err = v.localized(data[position:])
			}
			if err != nil {
				return err
			}
			position += used
		}
	}
	if position != uint64(len(data)) {
		return fmt.Errorf("%w: ICC sequence size", ErrInvalid)
	}
	return nil
}

// iccMetadataAdaptation 检查九元素定点矩阵，并按v4要求精确判定其可逆性
// 入参: data 适应矩阵标签, invertible 是否要求可逆
// 返回: error 类型、长度或奇异矩阵错误
func iccMetadataAdaptation(data []byte, invertible bool) error {
	if err := iccMetadataType(data, "sf32"); err != nil {
		return err
	}
	if len(data) != 44 {
		return fmt.Errorf("%w: ICC adaptation matrix size", ErrInvalid)
	}
	if !invertible {
		return nil
	}
	var values [9]int64
	for i := range values {
		values[i] = int64(int32(binary.BigEndian.Uint32(data[8+4*i:])))
	}
	var determinant, term, factor big.Int
	for i := range 3 {
		term.SetInt64(values[i])
		factor.SetInt64(values[3+(i+1)%3])
		term.Mul(&term, &factor)
		factor.SetInt64(values[6+(i+2)%3])
		term.Mul(&term, &factor)
		determinant.Add(&determinant, &term)
		term.SetInt64(values[i])
		factor.SetInt64(values[3+(i+2)%3])
		term.Mul(&term, &factor)
		factor.SetInt64(values[6+(i+1)%3])
		term.Mul(&term, &factor)
		determinant.Sub(&determinant, &term)
	}
	if determinant.Sign() == 0 {
		return fmt.Errorf("%w: ICC singular adaptation matrix", ErrInvalid)
	}
	return nil
}

// validateCreatedICCProfile 校验新写入ICC配置文件的头部、必需标签及颜色转换表
// 入参: data 完整配置文件字节, ctx 取消Context
// 返回: *iccProfile 只读配置文件，失败为nil, error 结构、类型、能力、资源或取消错误
func validateCreatedICCProfile(data []byte, ctx context.Context) (*iccProfile, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p, err := parseICCProfile(data)
	if err != nil {
		return nil, err
	}
	if len(p.data) != len(data) {
		return nil, fmt.Errorf("%w: produced ICC profile has trailing data", ErrInvalid)
	}
	if err := validateCreatedICCHeader(p, ctx); err != nil {
		return nil, err
	}
	if err := requiredICCTags(p); err != nil {
		return nil, err
	}
	if err := validateCreatedICCMetadata(p, ctx); err != nil {
		return nil, err
	}
	if err := validateCreatedICCTransforms(p, ctx); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return p, nil
}

// requiredICCTags 按配置文件类别、版本与颜色模型校验必需标签集合
// 入参: p 已解析的配置文件
// 返回: error 缺少标签或模型声明错误
func requiredICCTags(p *iccProfile) error {
	required := []string{"desc", "cprt"}
	if p.class != "link" {
		required = append(required, "wtpt")
	}
	switch p.class {
	case "scnr", "mntr":
		matrix := []string{"rXYZ", "gXYZ", "bXYZ", "rTRC", "gTRC", "bTRC"}
		completeMatrix := p.channels == 3 && p.pcs == "XYZ "
		for _, name := range matrix {
			completeMatrix = completeMatrix && p.tag(name) != nil
		}
		if p.space == "GRAY" {
			required = append(required, "kTRC")
		} else if p.class == "mntr" && p.version>>24 == 2 && p.space == "RGB " && p.pcs == "XYZ " {
			required = append(required, matrix...)
		} else if !completeMatrix {
			required = append(required, "A2B0")
			if p.class == "mntr" && p.version>>24 == 4 {
				required = append(required, "B2A0")
			}
		}
	case "prtr":
		if p.space == "GRAY" {
			required = append(required, "kTRC")
		} else {
			required = append(required, "A2B0", "A2B1", "A2B2", "B2A0", "B2A1", "B2A2", "gamt")
			if p.version>>24 == 4 && p.version >= 0x04100000 && iccMultiColorSpace(p.space) {
				required = append(required, "clrt")
			}
		}
	case "link":
		required = append(required, "A2B0", "pseq")
		if p.version>>24 == 4 {
			if p.version >= 0x04100000 && iccMultiColorSpace(p.space) {
				required = append(required, "clrt")
			}
			if p.version >= 0x04200000 && iccMultiColorSpace(p.pcs) {
				required = append(required, "clot")
			}
		}
	case "spac":
		required = append(required, "A2B0", "B2A0")
	case "abst":
		if p.space != "XYZ " && p.space != "Lab " {
			return fmt.Errorf("%w: ICC abstract profile input is not a PCS", ErrInvalid)
		}
		required = append(required, "A2B0")
	case "nmcl":
		required = append(required, "ncl2")
	}
	for _, name := range required {
		if p.tag(name) == nil {
			return fmt.Errorf("%w: ICC %s profile needs %s", ErrInvalid, p.class, name)
		}
	}
	return nil
}

// iccMultiColorSpace 判断ICC的多色分量标识，不把RGB或CMYK误当作自定义色料列表
// 入参: space 已解析的颜色空间标识
// 返回: bool 是否采用xCLR标识
func iccMultiColorSpace(space string) bool {
	return len(space) == 4 && space[1:] == "CLR" && iccColorChannels(space) != 0
}

// validateCreatedICCTransforms 校验配置文件中全部曲线、矩阵、命名色及正反向查找表标签
// 入参: p 已解析的配置文件, ctx 取消Context
// 返回: error 标签、模型、能力、资源或取消错误
func validateCreatedICCTransforms(p *iccProfile, ctx context.Context) error {
	luts := make(map[iccTag]*iccPipeline)
	curves := make(map[iccTag]bool)
	for _, name := range slices.Sorted(maps.Keys(p.tags)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		data := p.tag(name)
		tag := p.tags[name]
		switch name {
		case "rTRC", "gTRC", "bTRC", "kTRC":
			if p.version>>24 == 2 && string(data[:4]) == "para" {
				return fmt.Errorf("%w: ICC v2 curve type", ErrInvalid)
			}
			if !curves[tag] {
				_, size, err := parseICCCurve(data)
				if err != nil {
					return err
				}
				if size != len(data) {
					return fmt.Errorf("%w: ICC standalone curve length", ErrInvalid)
				}
				curves[tag] = true
			}
		case "wtpt", "bkpt", "lumi", "rXYZ", "gXYZ", "bXYZ":
			value, err := iccXYZ(data)
			if err != nil {
				return err
			}
			if name == "wtpt" && (value[0] <= 0 || value[1] <= 0 || value[2] <= 0) {
				return fmt.Errorf("%w: ICC media white point", ErrInvalid)
			}
			if name == "wtpt" && !iccDisplayWhite(p, value) {
				return fmt.Errorf("%w: ICC display media white point", ErrInvalid)
			}
			if name == "bkpt" || name == "lumi" {
				for _, component := range value {
					if component < 0 {
						return fmt.Errorf("%w: ICC XYZ tristimulus value", ErrInvalid)
					}
				}
			}
		case "A2B0", "A2B1", "A2B2", "B2A0", "B2A1", "B2A2", "gamt", "D2B0", "D2B1", "D2B2", "D2B3", "B2D0", "B2D1", "B2D2", "B2D3":
			inputs, outputs, inputXYZ := p.channels, 3, p.space == "XYZ "
			if p.class == "link" {
				outputs = iccColorChannels(p.pcs)
			}
			forward := name[0] == 'A' || name[0] == 'D'
			if !forward {
				inputs, outputs, inputXYZ = 3, p.channels, p.pcs == "XYZ "
				if name == "gamt" {
					outputs = 1
				}
			}
			if err := validateCreatedICCLUT(p, name, forward, inputs, outputs, inputXYZ, luts); err != nil {
				return err
			}
		case "ncl2":
			if err := validateCreatedICCNamed(p, ctx); err != nil {
				return err
			}
		}
	}
	return checkContext(ctx)
}

// validateCreatedICCLUT 校验标签允许的转换类型及通道约定，缓存不改变类型和方向检查
// 入参: p 配置文件, name 标签标识, forward 是否为设备到PCS方向, inputs 输入通道数, outputs 输出通道数, inputXYZ 输入是否为XYZ, cache 已解析查找表
// 返回: error 类型、方向、通道、结构或能力错误
func validateCreatedICCLUT(p *iccProfile, name string, forward bool, inputs, outputs int, inputXYZ bool, cache map[iccTag]*iccPipeline) error {
	data := p.tag(name)
	kind := string(data[:4])
	floatingTag := name[0] == 'D' || len(name) >= 3 && name[2] == 'D'
	if floatingTag {
		if p.version>>24 != 4 || kind != "mpet" {
			return fmt.Errorf("%w: ICC %s transform type %q", ErrInvalid, name, kind)
		}
	} else if kind == "mAB " && !forward || kind == "mBA " && forward || p.version>>24 == 2 && (kind == "mAB " || kind == "mBA ") {
		return fmt.Errorf("%w: ICC %s transform type %q", ErrInvalid, name, kind)
	}
	tag := p.tags[name]
	pipeline := cache[tag]
	if pipeline == nil {
		var err error
		switch kind {
		case "mft1", "mft2":
			pipeline, err = parseICCLUT(data, inputXYZ)
		case "mAB ", "mBA ":
			pipeline, err = parseICCMultiLUT(data)
		case "mpet":
			if !floatingTag {
				return fmt.Errorf("%w: ICC %s transform type %q", ErrInvalid, name, kind)
			}
			pipeline, err = parseICCMultiProcess(data)
		default:
			return fmt.Errorf("%w: ICC %s transform type %q", ErrUnsupported, name, kind)
		}
		if err != nil {
			return err
		}
		cache[tag] = pipeline
	}
	if pipeline.inputs != inputs || pipeline.outputs != outputs {
		return fmt.Errorf("%w: ICC %s transform channels", ErrInvalid, name)
	}
	if kind == "mft1" || kind == "mft2" {
		if !inputXYZ {
			for axis := range 9 {
				want := int32(0)
				if axis%4 == 0 {
					want = 65536
				}
				if int32(binary.BigEndian.Uint32(data[12+axis*4:])) != want {
					return fmt.Errorf("%w: ICC LUT matrix requires XYZ input", ErrInvalid)
				}
			}
		}
		size := 48
		if kind == "mft2" {
			size = 52
		}
		for _, stage := range pipeline.stages {
			switch stage.kind {
			case iccStageCLUT:
				size += len(stage.data)
			case iccStageCurves:
				for _, curve := range stage.curves {
					size += len(curve.values)
				}
			}
		}
		if size != len(data) {
			return fmt.Errorf("%w: ICC LUT length", ErrInvalid)
		}
	}
	return nil
}

// walkICCNamedColor 统一校验并遍历ncl2命名色表全部记录，供读写两侧复用
// 入参: p 配置文件, ctx 可选取消Context, requireNonEmpty 是否拒绝零条记录, maxCount 可选记录数上限，零表示不限, visit 可选条目消费回调
// 返回: error 头部、通道、长度、编码、上限或取消错误
func walkICCNamedColor(p *iccProfile, ctx context.Context, requireNonEmpty bool, maxCount uint64, visit func(count int, prefix, suffix, name string, pcs [3]uint16, devBytes []byte) error) error {
	data := p.tag("ncl2")
	if len(data) < 84 || string(data[:4]) != "ncl2" || binary.BigEndian.Uint32(data[4:]) != 0 {
		return fmt.Errorf("%w: ICC named color header", ErrInvalid)
	}
	count, device := uint64(binary.BigEndian.Uint32(data[12:])), uint64(binary.BigEndian.Uint32(data[16:]))
	if device != 0 && device != uint64(p.channels) {
		return fmt.Errorf("%w: ICC named color device coordinates", ErrInvalid)
	}
	stride := uint64(38) + 2*device
	if requireNonEmpty && count == 0 || count > (uint64(len(data))-84)/stride {
		return fmt.Errorf("%w: ICC named color length", ErrInvalid)
	}
	expected := uint64(84) + count*stride
	if uint64(len(data))-expected > 3 {
		return fmt.Errorf("%w: ICC named color length", ErrInvalid)
	}
	for _, value := range data[expected:] {
		if value != 0 {
			return fmt.Errorf("%w: ICC named color padding", ErrInvalid)
		}
	}
	if maxCount > 0 && count > maxCount {
		return fmt.Errorf("%w: ICC named color count", ErrLimit)
	}
	prefix, err := iccNamedASCIIText(data[20:52])
	if err != nil {
		return err
	}
	suffix, err := iccNamedASCIIText(data[52:84])
	if err != nil {
		return err
	}
	for i := range count {
		if err := checkContext(ctx); err != nil {
			return err
		}
		row := data[84+i*stride : 84+(i+1)*stride]
		name, err := iccNamedASCIIText(row[:32])
		if err != nil {
			return err
		}
		if visit != nil {
			pcs := [3]uint16{
				binary.BigEndian.Uint16(row[32:]),
				binary.BigEndian.Uint16(row[34:]),
				binary.BigEndian.Uint16(row[36:]),
			}
			var devBytes []byte
			if device != 0 {
				devBytes = row[38:]
			}
			if err := visit(int(count), prefix, suffix, name, pcs, devBytes); err != nil {
				return err
			}
		}
	}
	return checkContext(ctx)
}

// validateCreatedICCNamed 校验命名色表的完整记录，不将OpenXPS绘制时的色调数量限制套用于ICC封装
// 入参: p 配置文件, ctx 取消Context
// 返回: error 记录、通道、字符串或取消错误
func validateCreatedICCNamed(p *iccProfile, ctx context.Context) error {
	return walkICCNamedColor(p, ctx, false, 0, nil)
}

// prepareICCTarget 按目标意图选择B2A，缺省表不存在时使用允许的矩阵或灰阶模型
// 入参: profile 目标配置文件, intent ICC目标渲染意图, ctx 取消Context
// 返回: *iccTargetTransform 只读目标转换, error 配置、能力、数值或取消错误
func prepareICCTarget(profile *iccProfile, intent uint32, ctx context.Context) (*iccTargetTransform, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	t, err := newICCTarget(profile, intent)
	if err != nil {
		return nil, err
	}
	return prepareICCTargetDirection(t, ctx)
}

// newICCTarget 校验目标ICC的公共属性，不提前要求未使用的转换方向
// 入参: profile 目标配置文件, intent ICC目标渲染意图
// 返回: *iccTargetTransform 未准备方向的目标, error 类别、通道或白点错误
func newICCTarget(profile *iccProfile, intent uint32) (*iccTargetTransform, error) {
	if profile == nil || intent > 3 {
		return nil, fmt.Errorf("%w: ICC target configuration", ErrInvalid)
	}
	switch profile.class {
	case "scnr", "mntr", "prtr", "spac":
	default:
		return nil, fmt.Errorf("%w: ICC target class %q", ErrUnsupported, profile.class)
	}
	if profile.channels < 1 || profile.channels > iccMaxChannels {
		return nil, fmt.Errorf("%w: ICC target channels", ErrUnsupported)
	}
	white, err := iccXYZ(profile.tag("wtpt"))
	if err != nil {
		return nil, err
	}
	for _, value := range white {
		if value <= 0 {
			return nil, fmt.Errorf("%w: ICC target white point", ErrInvalid)
		}
	}
	if !iccReadDisplayWhite(profile, white) {
		return nil, fmt.Errorf("%w: ICC target display white", ErrInvalid)
	}
	if profile.class == "mntr" {
		white = iccPCSWhite
	}
	return &iccTargetTransform{profile: profile, white: white, intent: intent}, nil
}

// prepareICCTargetDirection 为已校验的目标准备实际使用的反向转换，v4优先采用B2D浮点管线
// 入参: t 已校验目标, ctx 取消Context
// 返回: *iccTargetTransform 可用转换, error 表、曲线或预算错误
func prepareICCTargetDirection(t *iccTargetTransform, ctx context.Context) (*iccTargetTransform, error) {
	profile, intent := t.profile, t.intent
	var err error
	name, data := iccSelectTransformTag(profile, intent, false)
	if data != nil {
		if len(name) >= 3 && name[2] == 'D' {
			if string(data[:4]) != "mpet" {
				return nil, fmt.Errorf("%w: ICC target float LUT type %q", ErrInvalid, string(data[:4]))
			}
			t.pipeline, err = parseICCMultiProcess(data)
			t.absolutePCS = name == "B2D3"
		} else {
			switch string(data[:4]) {
			case "mft1", "mft2":
				t.pipeline, err = parseICCLUT(data, profile.pcs == "XYZ ")
			case "mBA ":
				if profile.version>>24 != 4 {
					return nil, fmt.Errorf("%w: ICC v2 target LUT type", ErrInvalid)
				}
				t.pipeline, err = parseICCMultiLUT(data)
			default:
				return nil, fmt.Errorf("%w: ICC target LUT type %q", ErrUnsupported, string(data[:4]))
			}
		}
		if err != nil {
			return nil, err
		}
		if t.pipeline.inputs != 3 || t.pipeline.outputs != profile.channels {
			return nil, fmt.Errorf("%w: ICC target LUT channels", ErrInvalid)
		}
		return t, checkContext(ctx)
	}
	var curves [3]iccCurve
	if profile.space == "GRAY" {
		t.gray = true
		curves[0], _, err = parseICCCurve(profile.tag("kTRC"))
	} else if profile.space == "RGB " && profile.pcs == "XYZ " {
		for column, pair := range [][2]string{{"rXYZ", "rTRC"}, {"gXYZ", "gTRC"}, {"bXYZ", "bTRC"}} {
			values, e := iccXYZ(profile.tag(pair[0]))
			if e != nil {
				return nil, e
			}
			for row := range 3 {
				t.matrix[row*3+column] = values[row]
			}
			curves[column], _, err = parseICCCurve(profile.tag(pair[1]))
			if err != nil {
				return nil, err
			}
		}
		t.matrix, err = iccInverseMatrix(t.matrix)
	} else {
		return nil, fmt.Errorf("%w: missing ICC target transform", ErrUnsupported)
	}
	if err != nil {
		return nil, err
	}
	count := 3
	if t.gray {
		count = 1
	}
	for i, curve := range curves[:count] {
		t.inverse[i], err = prepareICCInverseCurve(curve, ctx)
		if err != nil {
			return nil, err
		}
	}
	return t, checkContext(ctx)
}

// fromXYZ 将物理XYZ编码为目标设备分量，支持最多十五通道、绝对色度及浮点B2D管线
// 入参: xyz D50连接空间值，绝对意图时为绝对色度
// 返回: [iccMaxChannels]float64 前profile.channels项有效, error 非有限输入或转换错误
func (t *iccTargetTransform) fromXYZ(xyz [3]float64) ([iccMaxChannels]float64, error) {
	if !geometryFinite(xyz[0], xyz[1], xyz[2]) {
		return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC target PCS value", ErrInvalid)
	}
	if t.intent == 3 && !t.absolutePCS && t.white != iccPCSWhite {
		for axis := range 3 {
			xyz[axis] *= iccPCSWhite[axis] / t.white[axis]
		}
	}
	if !geometryFinite(xyz[0], xyz[1], xyz[2]) {
		return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC target white adaptation", ErrLimit)
	}
	if t.pipeline != nil {
		input := xyz
		if t.pipeline.floating {
			if t.profile.pcs == "Lab " {
				input = iccXYZToLab(xyz)
			}
		} else if t.profile.pcs == "XYZ " {
			for axis := range 3 {
				input[axis] *= 32768.0 / 65535
			}
		} else {
			lab := iccXYZToLab(xyz)
			input = [3]float64{lab[0] / 100, (lab[1] + 128) / 255, (lab[2] + 128) / 255}
			if t.pipeline.legacyLab {
				input = [3]float64{lab[0] * 65280 / (100 * 65535), (lab[1] + 128) * 256 / 65535, (lab[2] + 128) * 256 / 65535}
			}
		}
		if !geometryFinite(input[0], input[1], input[2]) {
			return [iccMaxChannels]float64{}, fmt.Errorf("%w: ICC target PCS encoding range", ErrLimit)
		}
		return t.pipeline.evaluate(input[:])
	}
	var result [iccMaxChannels]float64
	if t.gray {
		value := xyz[1] / iccPCSWhite[1]
		if t.profile.pcs == "Lab " {
			value = iccXYZToLab(xyz)[0] / 100
		}
		result[0] = inverseICCCurve(t.inverse[0], value)
	} else {
		linear := iccMatrixColor(t.matrix, xyz)
		if !geometryFinite(linear[0], linear[1], linear[2]) {
			return result, fmt.Errorf("%w: ICC inverse matrix range", ErrLimit)
		}
		for axis := range 3 {
			result[axis] = inverseICCCurve(t.inverse[axis], linear[axis])
		}
	}
	return result, nil
}

// iccXYZToLab 按D50参考白点计算物理CIELAB，不提前裁剪连接空间
// 入参: xyz 有限物理XYZ
// 返回: [3]float64 物理L、a、b分量
func iccXYZToLab(xyz [3]float64) [3]float64 {
	var f [3]float64
	for axis, value := range xyz {
		value /= iccPCSWhite[axis]
		if value > 216.0/24389 {
			f[axis] = math.Cbrt(value)
		} else {
			f[axis] = value*841/108 + 4.0/29
		}
	}
	return [3]float64{116*f[1] - 16, 500 * (f[0] - f[1]), 200 * (f[1] - f[2])}
}

// iccInverseMatrix 计算三分量颜色矩阵的逆，拒绝奇异矩阵及非有限结果
// 入参: m 行优先矩阵
// 返回: [9]float64 逆矩阵, error 奇异或数值范围错误
func iccInverseMatrix(m [9]float64) ([9]float64, error) {
	r := [9]float64{m[4]*m[8] - m[5]*m[7], m[2]*m[7] - m[1]*m[8], m[1]*m[5] - m[2]*m[4], m[5]*m[6] - m[3]*m[8], m[0]*m[8] - m[2]*m[6], m[2]*m[3] - m[0]*m[5], m[3]*m[7] - m[4]*m[6], m[1]*m[6] - m[0]*m[7], m[0]*m[4] - m[1]*m[3]}
	d := m[0]*r[0] + m[1]*r[3] + m[2]*r[6]
	if d == 0 {
		return [9]float64{}, fmt.Errorf("%w: singular ICC target matrix", ErrUnsupported)
	}
	for i := range r {
		r[i] /= d
		if !geometryFinite(r[i]) {
			return [9]float64{}, fmt.Errorf("%w: ICC inverse matrix range", ErrLimit)
		}
	}
	return r, nil
}

// prepareICCTransform 选择源设备至PCS的查找表，v4优先采用D2B浮点管线，缺省时使用规定的RGB或灰阶模型
// 入参: profile 已解析配置文件, intent ICC渲染意图
// 返回: *iccTransform 只读转换, error 配置文件、能力或结构错误
func prepareICCTransform(profile *iccProfile, intent uint32) (*iccTransform, error) {
	if profile == nil || intent > 3 {
		return nil, fmt.Errorf("%w: ICC transform configuration", ErrInvalid)
	}
	switch profile.class {
	case "scnr", "mntr", "prtr", "spac", "nmcl":
	default:
		return nil, fmt.Errorf("%w: ICC source profile class %q", ErrUnsupported, profile.class)
	}
	if profile.class != "nmcl" && profile.channels > iccMaxChannels {
		return nil, fmt.Errorf("%w: ICC transform channel count", ErrUnsupported)
	}
	white, err := iccXYZ(profile.tag("wtpt"))
	if err != nil {
		return nil, err
	}
	for _, value := range white {
		if value <= 0 {
			return nil, fmt.Errorf("%w: ICC media white point", ErrInvalid)
		}
	}
	if !iccReadDisplayWhite(profile, white) {
		return nil, fmt.Errorf("%w: ICC display media white point", ErrInvalid)
	}
	if profile.class == "mntr" || profile.class == "abst" {
		white = iccPCSWhite
	}
	t := &iccTransform{profile: profile, white: white, intent: intent}
	if profile.class == "nmcl" {
		t.named, err = parseICCNamedColor(profile)
		if err != nil {
			return nil, err
		}
		return t, nil
	}
	name, data := iccSelectTransformTag(profile, intent, true)
	if data != nil {
		if name[0] == 'D' {
			if string(data[:4]) != "mpet" {
				return nil, fmt.Errorf("%w: ICC source float transform type %q", ErrInvalid, string(data[:4]))
			}
			t.pipeline, err = parseICCMultiProcess(data)
			t.absolutePCS = name == "D2B3"
		} else {
			switch string(data[:4]) {
			case "mft1", "mft2":
				t.pipeline, err = parseICCLUT(data, profile.space == "XYZ ")
			case "mAB ":
				if profile.version>>24 != 4 {
					return nil, fmt.Errorf("%w: ICC v2 source LUT type", ErrInvalid)
				}
				t.pipeline, err = parseICCMultiLUT(data)
			default:
				return nil, fmt.Errorf("%w: ICC source transform type %q", ErrUnsupported, string(data[:4]))
			}
		}
		if err != nil {
			return nil, err
		}
		if t.pipeline.inputs != profile.channels || t.pipeline.outputs != 3 {
			return nil, fmt.Errorf("%w: ICC source transform channels", ErrInvalid)
		}
		return t, nil
	}
	if profile.space == "GRAY" {
		t.gray = true
		t.curves[0], _, err = parseICCCurve(profile.tag("kTRC"))
		if err != nil {
			return nil, err
		}
		return t, nil
	}
	if profile.space != "RGB " {
		return nil, fmt.Errorf("%w: missing ICC source LUT", ErrInvalid)
	}
	if profile.pcs != "XYZ " {
		return nil, fmt.Errorf("%w: ICC RGB matrix requires XYZ PCS", ErrInvalid)
	}
	for column, names := range [][2]string{{"rXYZ", "rTRC"}, {"gXYZ", "gTRC"}, {"bXYZ", "bTRC"}} {
		values, err := iccXYZ(profile.tag(names[0]))
		if err != nil {
			return nil, err
		}
		for row := range 3 {
			t.matrix[row*3+column] = values[row]
		}
		t.curves[column], _, err = parseICCCurve(profile.tag(names[1]))
		if err != nil {
			return nil, err
		}
	}
	return t, nil
}

// toXYZ 将源分量转换为物理XYZ，区分现代和传统Lab编码及绝对色度白点，可选对矩阵及灰阶TRC启用无裁剪扩展外推
// 入参: input 源设备的颜色分量, extended 是否对TRC启用扩展范围外推
// 返回: [3]float64 D50条件XYZ, error 输入、计算或能力错误
func (t *iccTransform) toXYZ(input []float64, extended bool) ([3]float64, error) {
	if t == nil || t.profile == nil || len(input) != t.inputChannels() {
		return [3]float64{}, fmt.Errorf("%w: ICC source color channels", ErrInvalid)
	}
	for _, value := range input {
		if !geometryFinite(value) {
			return [3]float64{}, fmt.Errorf("%w: ICC source color value", ErrInvalid)
		}
	}
	var xyz [3]float64
	if len(t.named) != 0 {
		xyz = t.namedXYZ(input)
	} else if t.pipeline != nil {
		output, err := t.pipeline.evaluate(input)
		if err != nil {
			return [3]float64{}, err
		}
		if t.pipeline.floating {
			if t.profile.pcs == "XYZ " {
				xyz = [3]float64{output[0], output[1], output[2]}
			} else {
				xyz = iccLabToXYZ([3]float64{output[0], output[1], output[2]})
			}
		} else if t.profile.pcs == "XYZ " {
			for i := range 3 {
				xyz[i] = output[i] * (65535.0 / 32768)
			}
		} else {
			lab := [3]float64{output[0] * 100, output[1]*255 - 128, output[2]*255 - 128}
			if t.pipeline.legacyLab {
				lab = [3]float64{min(100, output[0]*65535*100/65280), output[1]*65535/256 - 128, output[2]*65535/256 - 128}
			}
			xyz = iccLabToXYZ(lab)
		}
	} else if t.gray {
		var value float64
		var err error
		if extended {
			value, err = t.curves[0].evaluateExtended(input[0])
		} else {
			value, err = t.curves[0].evaluate(input[0])
		}
		if err != nil {
			return [3]float64{}, err
		}
		if t.profile.pcs == "Lab " {
			xyz = iccLabToXYZ([3]float64{100 * value, 0, 0})
		} else {
			for i := range 3 {
				xyz[i] = iccPCSWhite[i] * value
			}
		}
	} else {
		var linear [3]float64
		for i := range 3 {
			var value float64
			var err error
			if extended {
				value, err = t.curves[i].evaluateExtended(input[i])
			} else {
				value, err = t.curves[i].evaluate(input[i])
			}
			if err != nil {
				return [3]float64{}, err
			}
			linear[i] = value
		}
		xyz = iccMatrixColor(t.matrix, linear)
	}
	if t.intent == 3 && !t.absolutePCS && t.white != iccPCSWhite {
		for i := range 3 {
			xyz[i] *= t.white[i] / iccPCSWhite[i]
		}
	}
	if !geometryFinite(xyz[0], xyz[1], xyz[2]) {
		return [3]float64{}, fmt.Errorf("%w: ICC connection color range", ErrLimit)
	}
	return xyz, nil
}

// linearRGB 将源设备颜色经PCS转换为线性sRGB，支持TRC扩展外推
// 入参: input 源设备颜色分量, extended 是否对TRC启用扩展范围外推
// 返回: [3]float64 线性sRGB分量, error 源转换错误
func (t *iccTransform) linearRGB(input []float64, extended bool) ([3]float64, error) {
	xyz, err := t.toXYZ(input, extended)
	if err != nil {
		return [3]float64{}, err
	}
	return iccMatrixColor(iccPCSDisplayMatrix, xyz), nil
}

// iccLabToXYZ 按CIE有理数阈值还原D50参考白点的CIELAB，不提前裁剪a和b
// 入参: lab 物理L、a、b分量
// 返回: [3]float64 D50条件XYZ
func iccLabToXYZ(lab [3]float64) [3]float64 {
	y := (lab[0] + 16) / 116
	values := [3]float64{y + lab[1]/500, y, y - lab[2]/200}
	for i, value := range values {
		if value > 6.0/29 {
			values[i] = value * value * value
		} else {
			values[i] = (value - 4.0/29) * (108.0 / 841)
		}
		values[i] *= iccPCSWhite[i]
	}
	return values
}

// iccMatrixColor 计算三通道矩阵乘积，不裁剪色彩空间或量化中间分量
// 入参: matrix 行优先矩阵, color 三通道颜色
// 返回: [3]float64 矩阵结果
func iccMatrixColor(matrix [9]float64, color [3]float64) [3]float64 {
	return [3]float64{
		matrix[0]*color[0] + matrix[1]*color[1] + matrix[2]*color[2],
		matrix[3]*color[0] + matrix[4]*color[1] + matrix[5]*color[2],
		matrix[6]*color[0] + matrix[7]*color[1] + matrix[8]*color[2],
	}
}

// iccDisplayD65Matrix 计算D65参考白XYZ到线性sRGB的直接转换矩阵
// 返回: [9]float64 D65条件XYZ至线性sRGB的行优先矩阵
func iccDisplayD65Matrix() [9]float64 {
	white := [3]float64{0.3127 / 0.3290, 1, (1 - 0.3127 - 0.3290) / 0.3290}
	primaries := [9]float64{0.64 / 0.33, 0.30 / 0.60, 0.15 / 0.06, 1, 1, 1, (1 - 0.64 - 0.33) / 0.33, (1 - 0.30 - 0.60) / 0.60, (1 - 0.15 - 0.06) / 0.06}
	inversePrimaries, _ := iccInverseMatrix(primaries)
	scale := iccMatrixColor(inversePrimaries, white)
	for row := range 3 {
		for column := range 3 {
			primaries[row*3+column] *= scale[column]
		}
	}
	display, _ := iccInverseMatrix(primaries)
	return display
}

// iccDisplayMatrix 按Bradford色度适应计算D50连接空间到线性sRGB的显示矩阵
// 返回: [9]float64 D50条件XYZ至线性sRGB的行优先矩阵
func iccDisplayMatrix() [9]float64 {
	white := [3]float64{0.3127 / 0.3290, 1, (1 - 0.3127 - 0.3290) / 0.3290}
	display := iccDisplayD65Matrix()
	coneSource, coneTarget := iccMatrixColor(cicpBradford, iccPCSWhite), iccMatrixColor(cicpBradford, white)
	adapt := cicpBradford
	for row := range 3 {
		for column := range 3 {
			adapt[row*3+column] *= coneTarget[row] / coneSource[row]
		}
	}
	combined := cicpMulMatrix3(cicpBradfordInverse, adapt)
	return cicpMulMatrix3(display, combined)
}
