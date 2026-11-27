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
	"archive/zip"
	"bytes"
	"context"
	"encoding/binary"
	"encoding/xml"
	"fmt"
	"io"
	"io/fs"
	"mime"
	"slices"
	"sort"
	"strconv"
	"strings"
	"unicode/utf8"
)

const (
	// TargetModeInternal 表示OPC关系指向包内部件
	TargetModeInternal TargetMode = "Internal"
	// TargetModeExternal 表示OPC关系指向包外资源
	TargetModeExternal TargetMode = "External"
)

// opcTypesNS 等常量定义OPC包命名空间、内容类型与核心部件名
const (
	opcTypesNS   = "http://schemas.openxmlformats.org/package/2006/content-types"
	opcRelsNS    = "http://schemas.openxmlformats.org/package/2006/relationships"
	opcRelsType  = "application/vnd.openxmlformats-package.relationships+xml"
	opcTypesName = "/[Content_Types].xml"
)

// packageZIPMetadataLimit 等常量定义ZIP元数据上限与结构头签名
const (
	packageZIPMetadataLimit       = 65535
	packageZIPLocalSignature      = 0x04034b50
	packageZIPCentralSignature    = 0x02014b50
	packageZIPDescriptorSignature = 0x08074b50
	packageZIPEndSignature        = 0x06054b50
	packageZIP64EndSignature      = 0x06064b50
	packageZIP64LocatorSignature  = 0x07064b50
	packageZIPDigitalSignature    = 0x05054b50
)

// TargetMode 表示OPC关系的目标模式，合法取值为TargetModeInternal或TargetModeExternal
type TargetMode string

// Relationship 表示OPC关系，Target保留原始URI，TargetMode缺省时为TargetModeInternal
type Relationship struct {
	ID         string
	Type       string
	Target     string
	TargetMode TargetMode
}

// packageReader 持有只读OPC索引，不接管输入生命周期，可在底层ReaderAt支持时并发读取
type packageReader struct {
	files      []*zip.File
	comment    string
	parts      map[string][]*zip.File
	names      map[string]string
	data       map[string][]byte
	original   map[string]packagePart
	zipLayout  packageZIPLayout
	zipRecords []packageZIPLocal
	defaults   map[string]string
	overrides  map[string]string
	limits     Limits
	beforeRead func(string, uint64, int64) (int64, error)
	open       func(string) (io.ReadCloser, error)
	missing    func(string)
	relation   func(string) ([]Relationship, bool, error)
	cache      *streamResourceCache
}

// opcPiece 保存交错部件的分片编号及结束标记
type opcPiece struct {
	file  *zip.File
	index int
	last  bool
}

// packageReadError 保留底层读取故障，避免上层将封装错误归为内容验证结论
type packageReadError struct {
	err error
}

// PartInfo 描述OPC逻辑部件，Size为ZIP声明的解压字节数
type PartInfo struct {
	Name        string
	ContentType string
	Size        int64
}

// xmlPartLoader 提供调用私有的XML树读取策略，不修改阅读器或封装的配置
type xmlPartLoader func(string) (*xmlElement, error)

// packageZIPLayout 保存中央目录和结束记录的结构边界
type packageZIPLayout struct {
	base    int64
	central int64
	end     int64
	footer  int64
	count   uint64
}

// packageZIPLocal 保存中央目录指定的本地记录范围，供重叠及描述符校验使用
type packageZIPLocal struct {
	file         *zip.File
	start        int64
	data         int64
	end          int64
	finish       int64
	localVersion uint16
	zip64        bool
	cdSizeZIP64  bool
}

// zipHeaderFields 保存ZIP本地头或中央目录条目的安全校验关键字段
type zipHeaderFields struct {
	name         string
	version      uint16
	flags        uint16
	method       uint16
	crc32        uint32
	compressed   uint64
	uncompressed uint64
	zip64        bool
}

// newPackageReaderWithLimits 建立ZIP部件索引并解析内容类型，校验条目上限与声明解压字节上限
// 入参: ctx 取消Context, r 随机读取器, size ZIP数据长度, limits 包、部件及XML资源上限
// 返回: *packageReader 包读取器, error 错误信息
func newPackageReaderWithLimits(ctx context.Context, r io.ReaderAt, size int64, limits Limits) (*packageReader, error) {
	if r == nil || size < 0 {
		return nil, fmt.Errorf("%w: invalid package input", ErrInvalid)
	}
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	limit := limits.MaxPartBytes
	layout, err := readPackageZIPEnd(r, size, limits)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	zipInput, zipSize := r, size
	if layout.base != 0 {
		zipInput, zipSize = io.NewSectionReader(r, layout.base, size-layout.base), size-layout.base
	}
	z, err := zip.NewReader(zipInput, zipSize)
	if err != nil {
		return nil, fmt.Errorf("%w: ZIP: %w", ErrInvalid, err)
	}
	if len(z.File) > limits.MaxPartCount {
		return nil, fmt.Errorf("%w: ZIP has more than %d entries", ErrLimit, limits.MaxPartCount)
	}
	p := &packageReader{files: z.File, comment: z.Comment, parts: make(map[string][]*zip.File), names: make(map[string]string), defaults: make(map[string]string), overrides: make(map[string]string), limits: limits}
	pieces := make(map[string][]opcPiece)
	seen := make(map[string]bool)
	var total uint64
	for _, file := range z.File {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		key := strings.ToLower(file.Name)
		if seen[key] {
			return nil, fmt.Errorf("%w: duplicate ZIP entry %q", ErrInvalid, file.Name)
		}
		seen[key] = true
		if file.Flags&1 != 0 || file.Method != zip.Store && file.Method != zip.Deflate {
			return nil, fmt.Errorf("%w: encrypted or unsupported ZIP entry %q", ErrUnsupported, file.Name)
		}
		if file.UncompressedSize64 > uint64(limit) || file.UncompressedSize64 > uint64(limits.MaxPackageBytes)-total {
			return nil, fmt.Errorf("%w: ZIP entry %q exceeds decompression budget", ErrLimit, file.Name)
		}
		total += file.UncompressedSize64
		if file.FileInfo().IsDir() {
			if file.UncompressedSize64 != 0 {
				return nil, fmt.Errorf("%w: nonempty ZIP directory %q", ErrInvalid, file.Name)
			}
			dir := strings.TrimSuffix(file.Name, "/")
			if !strings.EqualFold(dir, strings.TrimPrefix(opcTypesName, "/")) {
				if _, err := opcPartName("/" + dir); err != nil {
					return nil, fmt.Errorf("directory: %w", err)
				}
			}
			continue
		}
		if !file.Mode().IsRegular() {
			return nil, fmt.Errorf("%w: nonregular ZIP entry %q", ErrUnsupported, file.Name)
		}
		name, index, last, err := opcPieceName(file.Name)
		if err != nil {
			return nil, err
		}
		if !strings.EqualFold(name, strings.TrimPrefix(opcTypesName, "/")) {
			name, err = opcPartName("/" + name)
			if err != nil {
				return nil, fmt.Errorf("ZIP entry: %w", err)
			}
		} else {
			name = opcTypesName
		}
		key = strings.ToLower(name)
		if p.names[key] == "" {
			p.names[key] = name
		}
		if index >= 0 {
			pieces[key] = append(pieces[key], opcPiece{file: file, index: index, last: last})
		} else {
			if _, exists := p.parts[key]; exists {
				return nil, fmt.Errorf("%w: duplicate part %q", ErrInvalid, name)
			}
			p.parts[key] = []*zip.File{file}
		}
	}
	for name, list := range pieces {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if _, exists := p.parts[name]; exists {
			return nil, fmt.Errorf("%w: both whole part and pieces for %q", ErrInvalid, name)
		}
		sort.Slice(list, func(i, j int) bool { return list[i].index < list[j].index })
		var size uint64
		for i, piece := range list {
			if piece.index != i || piece.last != (i == len(list)-1) {
				return nil, fmt.Errorf("%w: incomplete or duplicate piece sequence for %q", ErrInvalid, name)
			}
			if piece.file.UncompressedSize64 > uint64(limit)-size {
				return nil, fmt.Errorf("%w: assembled part %q exceeds limit", ErrLimit, name)
			}
			size += piece.file.UncompressedSize64
			p.parts[name] = append(p.parts[name], piece.file)
		}
	}
	for name := range p.parts {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		for i := strings.LastIndexByte(name, '/'); i > 0; i = strings.LastIndexByte(name[:i], '/') {
			if _, exists := p.parts[name[:i]]; exists {
				return nil, fmt.Errorf("%w: part %q derives from another part", ErrInvalid, name)
			}
		}
	}
	records, err := validatePackageZIP(ctx, r, layout, z.File)
	if err != nil {
		return nil, err
	}
	p.zipLayout, p.zipRecords = layout, records
	data, err := p.readItemsContext(ctx, strings.ToLower(opcTypesName), min(limit, limits.MaxMetadataBytes))
	if err != nil {
		return nil, fmt.Errorf("content types: %w", err)
	}
	if err := p.parseContentTypesContext(ctx, data); err != nil {
		return nil, err
	}
	for name := range p.parts {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if name == strings.ToLower(opcTypesName) {
			continue
		}
		if _, err := p.contentType(name); err != nil {
			return nil, err
		}
	}
	return p, nil
}

// opcPieceName 识别OPC分片后缀，拒绝前导零、溢出及不完整的分片名称
// 入参: name ZIP条目名称
// 返回: string 部件名称, int 分片编号，非分片为 -1, bool 是否末片, error 错误信息
func opcPieceName(name string) (string, int, bool, error) {
	slash := strings.LastIndexByte(name, '/')
	base := strings.ToLower(name[slash+1:])
	if !strings.HasPrefix(base, "[") {
		return name, -1, false, nil
	}
	if strings.EqualFold(name, strings.TrimPrefix(opcTypesName, "/")) {
		return name, -1, false, nil
	}
	end := strings.IndexByte(base, ']')
	if slash < 1 || end < 2 || base[end:] != "].piece" && base[end:] != "].last.piece" {
		return "", 0, false, fmt.Errorf("%w: invalid piece name %q", ErrInvalid, name)
	}
	digits := base[1:end]
	for _, c := range digits {
		if c < '0' || c > '9' {
			return "", 0, false, fmt.Errorf("%w: invalid piece number %q", ErrInvalid, name)
		}
	}
	index, err := strconv.ParseUint(digits, 10, 31)
	if err != nil || len(digits) > 1 && digits[0] == '0' {
		return "", 0, false, fmt.Errorf("%w: invalid piece number %q", ErrInvalid, name)
	}
	return name[:slash], int(index), base[end:] == "].last.piece", nil
}

// readPart 读取完整逻辑部件，逐片校验ZIP校验和并限制实际解压量
// 入参: name 部件的包根URI
// 返回: []byte 独立的部件数据, error 错误信息
func (p *packageReader) readPart(name string) ([]byte, error) {
	return p.readPartContext(nil, name)
}

// readPartContext 在取消检查下读取完整逻辑部件，逐片校验ZIP校验和并限制实际解压量
// 入参: ctx 取消Context, name 部件的包根URI
// 返回: []byte 独立的部件数据, error 错误信息
func (p *packageReader) readPartContext(ctx context.Context, name string) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	canonical, err := opcPartName(name)
	if err != nil {
		return nil, err
	}
	limit := p.limits.MaxPartBytes
	if opcRelationshipName(canonical) {
		limit = min(limit, p.limits.MaxMetadataBytes)
	}
	return p.readItemsContext(ctx, strings.ToLower(canonical), limit)
}

// readItems 按顺序读取底层条目，不信任中央目录中的解压尺寸
// 入参: key 已规范化的小写索引键, limit 本次读取的字节上限
// 返回: []byte 拼接数据, error 错误信息
func (p *packageReader) readItems(key string, limit int64) ([]byte, error) {
	return p.readItemsContext(nil, key, limit)
}

// readItemsContext 在取消检查下按顺序读取底层条目，不信任中央目录中的解压尺寸
// 入参: ctx 取消Context, key 已规范化的小写索引键, limit 本次读取的字节上限
// 返回: []byte 拼接数据, error 错误信息
func (p *packageReader) readItemsContext(ctx context.Context, key string, limit int64) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if p.open != nil || p.cache != nil {
		stream, err := p.openPartStream(ctx, key, PartReadOptions{MaxBytes: limit})
		if err != nil {
			return nil, err
		}
		data, err := io.ReadAll(stream)
		closeErr := stream.Close()
		if err != nil {
			return nil, err
		}
		if closeErr != nil {
			return nil, closeErr
		}
		if p.cache != nil {
			media, _ := p.contentType(p.names[key])
			p.cache.put(key, data, graphicResourceMedia(media))
		}
		return data, nil
	}
	files, ok := p.parts[key]
	if !ok {
		return nil, fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)
	}
	limit = min(limit, p.limits.MaxPackageBytes)
	if data, exists := p.data[key]; exists {
		if p.beforeRead != nil {
			allowed, err := p.beforeRead(key, uint64(len(data)), limit)
			if err != nil {
				return nil, err
			}
			if allowed < 0 {
				return nil, fmt.Errorf("%w: part read allowance", ErrLimit)
			}
			limit = min(limit, allowed)
		}
		if int64(len(data)) > limit {
			return nil, fmt.Errorf("%w: part %q exceeds byte limit", ErrLimit, key)
		}
		return append([]byte(nil), data...), nil
	}
	if p.beforeRead != nil {
		size, err := p.partSize(key)
		if err != nil {
			return nil, err
		}
		allowed, err := p.beforeRead(key, size, limit)
		if err != nil {
			return nil, err
		}
		if allowed < 0 {
			return nil, fmt.Errorf("%w: part read allowance", ErrLimit)
		}
		limit = min(limit, allowed)
	}
	var result []byte
	for _, file := range files {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		remaining := limit - int64(len(result))
		if file.UncompressedSize64 > uint64(remaining) {
			return nil, fmt.Errorf("%w: part %q exceeds byte limit", ErrLimit, key)
		}
		stream, err := file.Open()
		if err != nil {
			return nil, &packageReadError{err: fmt.Errorf("%w: open %q: %w", ErrInvalid, file.Name, err)}
		}
		data, readErr := io.ReadAll(io.LimitReader(stream, remaining))
		if readErr != nil {
			_ = stream.Close()
			return nil, &packageReadError{err: fmt.Errorf("%w: read %q: %w", ErrInvalid, file.Name, readErr)}
		}
		var n int
		var probeErr error
		if int64(len(data)) == remaining {
			var extra [1]byte
			n, probeErr = stream.Read(extra[:])
		}
		closeErr := stream.Close()
		if n != 0 {
			return nil, fmt.Errorf("%w: part %q exceeds byte limit", ErrLimit, key)
		}
		if probeErr != nil && probeErr != io.EOF {
			return nil, &packageReadError{err: fmt.Errorf("%w: read %q: %w", ErrInvalid, file.Name, probeErr)}
		}
		if closeErr != nil {
			return nil, &packageReadError{err: fmt.Errorf("%w: close %q: %w", ErrInvalid, file.Name, closeErr)}
		}
		if len(files) == 1 {
			return data, checkContext(ctx)
		}
		result = append(result, data...)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// partSize 返回内存部件或交错ZIP部件的解压尺寸，供读取前预算检查使用
// 入参: key 已规范化的小写索引键
// 返回: uint64 声明或实际数据长度, error 缺失或尺寸溢出错误
func (p *packageReader) partSize(key string) (uint64, error) {
	if data, exists := p.data[key]; exists {
		return uint64(len(data)), nil
	}
	files, exists := p.parts[key]
	if !exists {
		if p.missing != nil {
			p.missing(key)
		}
		return 0, fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)
	}
	var size uint64
	for _, file := range files {
		if file.UncompressedSize64 > ^uint64(0)-size {
			return 0, fmt.Errorf("%w: part size overflow", ErrLimit)
		}
		size += file.UncompressedSize64
	}
	return size, nil
}

// contentType 获取已存在部件的内容类型，Override优先于Default，名称按ASCII不区分大小写
// 入参: name 部件的包根URI
// 返回: string 内容类型, error 错误信息
func (p *packageReader) contentType(name string) (string, error) {
	canonical, err := opcPartName(name)
	if err != nil {
		return "", err
	}
	key := strings.ToLower(canonical)
	if _, ok := p.parts[key]; !ok {
		if p.missing != nil {
			p.missing(key)
		}
		return "", fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)
	}
	value := p.declaredContentType(canonical)
	if value == "" {
		return "", fmt.Errorf("%w: no content type for %q", ErrInvalid, name)
	}
	if opcRelationshipName(key) {
		if !strings.EqualFold(value, opcRelsType) {
			return "", fmt.Errorf("%w: incorrect relationship content type for %q", ErrInvalid, name)
		}
		return opcRelsType, nil
	}
	return value, nil
}

// declaredContentType 查询规范部件名的类型声明，未命中Override或Default时返回空字符串
// 入参: name 规范部件URI
// 返回: string 声明媒体类型，无声明时为空
func (p *packageReader) declaredContentType(name string) string {
	key := strings.ToLower(name)
	value := p.overrides[key]
	if value == "" {
		base := key[strings.LastIndexByte(key, '/')+1:]
		if dot := strings.LastIndexByte(base, '.'); dot >= 0 {
			value = p.defaults[base[dot+1:]]
		}
	}
	return value
}

// parseContentTypes 解析OPC内容类型索引，检查命名空间、属性及重复定义
// 入参: data 内容类型XML
// 返回: error 错误信息
func (p *packageReader) parseContentTypes(data []byte) error {
	return p.parseContentTypesContext(nil, data)
}

// parseContentTypesContext 在取消检查下解析OPC内容类型索引，检查命名空间、属性及重复定义
// 入参: ctx 取消Context, data 内容类型XML
// 返回: error 错误信息
func (p *packageReader) parseContentTypesContext(ctx context.Context, data []byte) error {
	count := 0
	err := opcMetadataContext(ctx, data, p.limits, opcTypesNS, "Types", func(element xml.StartElement, attrs map[string]string) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if _, _, err := p.registerContentTypeElement(element, attrs); err != nil {
			return err
		}
		count++
		return nil
	})
	if err == nil && count == 0 {
		return fmt.Errorf("%w: empty content types stream", ErrInvalid)
	}
	return err
}

// registerContentTypeElement 校验并登记单条Default或Override内容类型声明，供全量及交错流式解析共用
// 入参: element 已过滤元素, attrs 无命名空间属性映射
// 返回: string 命中的规范部件键（仅Override非空）, string 声明媒体类型, error 属性、MIME、扩展名或重复定义错误
func (p *packageReader) registerContentTypeElement(element xml.StartElement, attrs map[string]string) (string, string, error) {
	if err := opcAttributes(attrs, "ContentType", "Extension", "PartName"); err != nil {
		return "", "", err
	}
	value := attrs["ContentType"]
	mediaType, parameters, err := mime.ParseMediaType(value)
	if err != nil || !strings.Contains(mediaType, "/") || strings.ContainsAny(value, "\r\n\t") || strings.TrimSpace(value) != value {
		return "", "", fmt.Errorf("%w: invalid content type %q", ErrInvalid, value)
	}
	if len(parameters) != 0 && opcSpecificContentType(mediaType) {
		return "", "", fmt.Errorf("%w: parameters on package-specific content type %q", ErrInvalid, value)
	}
	switch element.Name.Local {
	case "Default":
		ext := attrs["Extension"]
		if len(attrs) != 2 || ext == "" {
			return "", "", fmt.Errorf("%w: invalid Default attributes", ErrInvalid)
		}
		normalized, ok := opcNormalizeExtension(ext)
		if !ok {
			return "", "", fmt.Errorf("%w: invalid extension %q", ErrInvalid, ext)
		}
		key := strings.ToLower(normalized)
		if _, exists := p.defaults[key]; exists {
			return "", "", fmt.Errorf("%w: duplicate content type default %q", ErrInvalid, ext)
		}
		p.defaults[key] = value
		return "", value, nil
	case "Override":
		name, err := opcPartName(attrs["PartName"])
		if err != nil || len(attrs) != 2 {
			return "", "", fmt.Errorf("%w: invalid Override part name or attributes", ErrInvalid)
		}
		key := strings.ToLower(name)
		if _, exists := p.overrides[key]; exists {
			return "", "", fmt.Errorf("%w: duplicate content type override %q", ErrInvalid, name)
		}
		p.overrides[key] = value
		return key, value, nil
	default:
		return "", "", fmt.Errorf("%w: unexpected content type element %q", ErrInvalid, element.Name.Local)
	}
}

// opcSpecificContentType 判断OPC自身定义且不允许参数的内容类型，不限制普通资源的MIME参数
// 入参: media 已解析并转为小写的MIME类型
// 返回: bool 是否为包专用内容类型
func opcSpecificContentType(media string) bool {
	switch media {
	case opcRelsType, opcCoreType, opcCertificateType, opcSignatureOriginType, opcSignatureType:
		return true
	}
	return false
}

// opcNormalizeExtension 按ECMA-376 Part 2 §A.3校验并规范化Default/@Extension，解码未保留字符并校验UTF-8百分号序列
// 入参: value 原始扩展名字符串
// 返回: string 规范化扩展名, bool 是否符合ST_Extension
func opcNormalizeExtension(value string) (string, bool) {
	if value == "" {
		return "", false
	}
	const hex = "0123456789ABCDEF"
	var b strings.Builder
	b.Grow(len(value))
	var pctBuf [16]byte
	for i := 0; i < len(value); i++ {
		c := value[i]
		if c == '%' {
			pct := pctBuf[:0]
			for i < len(value) && value[i] == '%' {
				if i+2 >= len(value) {
					return "", false
				}
				hi, lo := opcHex(value[i+1]), opcHex(value[i+2])
				if hi < 0 || lo < 0 {
					return "", false
				}
				decoded := byte(hi*16 + lo)
				if decoded == '.' || decoded == '/' || decoded == '\\' {
					return "", false
				}
				pct = append(pct, decoded)
				if opcUnreserved(decoded) {
					b.WriteByte(decoded)
				} else {
					b.WriteByte('%')
					b.WriteByte(hex[hi])
					b.WriteByte(hex[lo])
				}
				i += 3
			}
			if !utf8.Valid(pct) {
				return "", false
			}
			i--
		} else if c == '.' || !(opcUnreserved(c) || strings.ContainsRune("!$&'()*+,:=@", rune(c))) {
			return "", false
		} else {
			b.WriteByte(c)
		}
	}
	return b.String(), true
}

// relationships 获取指定源的OPC关系，外部目标仅保留元数据，不访问网络或文件系统
// 入参: source 源部件的包根URI，包级关系使用/
// 返回: []Relationship 关系列表，无关系部件时为空, error 错误信息
func (p *packageReader) relationships(source string) ([]Relationship, error) {
	return p.relationshipsContext(nil, source)
}

// relationshipsContext 在取消检查下获取指定源的OPC关系，外部目标仅保留元数据，不访问网络或文件系统
// 入参: ctx 取消Context, source 源部件的包根URI，包级关系使用/
// 返回: []Relationship 关系列表，无关系部件时为空, error 错误信息
func (p *packageReader) relationshipsContext(ctx context.Context, source string) ([]Relationship, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	name := "/_rels/.rels"
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return nil, err
		}
		if opcRelationshipName(canonical) {
			return nil, fmt.Errorf("%w: relationships cannot originate from a relationships part", ErrInvalid)
		}
		source = canonical
	}
	if p.relation != nil {
		if items, handled, err := p.relation(source); handled || err != nil {
			return items, err
		}
	}
	if source != "/" {
		canonical := source
		key := strings.ToLower(canonical)
		if _, ok := p.parts[key]; !ok {
			return nil, fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)
		}
		slash := strings.LastIndexByte(canonical, '/')
		name = canonical[:slash+1] + "_rels/" + canonical[slash+1:] + ".rels"
	}
	key := strings.ToLower(name)
	if _, ok := p.parts[key]; !ok {
		if p.missing != nil {
			p.missing(key)
		}
		return nil, nil
	}
	return p.readRelationshipsContext(ctx, source, name)
}

// readRelationships 共用完整关系部件解析，源存在性由普通读取器或临时关系后端验证
// 入参: source 已校验源URI, name 完整关系部件URI
// 返回: []Relationship 完整关系, error 读取、XML、结构或关系错误
func (p *packageReader) readRelationships(source, name string) ([]Relationship, error) {
	return p.readRelationshipsContext(nil, source, name)
}

// readRelationshipsContext 在取消检查下共用完整关系部件解析，源存在性由普通读取器或临时关系后端验证
// 入参: ctx 取消Context, source 已校验源URI, name 完整关系部件URI
// 返回: []Relationship 完整关系, error 读取、XML、结构或关系错误
func (p *packageReader) readRelationshipsContext(ctx context.Context, source, name string) ([]Relationship, error) {
	key := strings.ToLower(name)
	data, err := p.readItemsContext(ctx, key, min(p.limits.MaxPartBytes, p.limits.MaxMetadataBytes))
	if err != nil {
		return nil, err
	}
	var result []Relationship
	ids := make(map[string]bool)
	err = opcMetadataContext(ctx, data, p.limits, opcRelsNS, "Relationships", func(element xml.StartElement, attrs map[string]string) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		rel, err := parseRelationship(source, element, attrs, ids)
		if err != nil {
			return err
		}
		result = append(result, rel)
		return nil
	})
	if err != nil {
		return nil, fmt.Errorf("relationship part %q: %w", name, err)
	}
	return result, nil
}

// parseRelationship 共用关系属性、部件内ID及URI校验，不访问内部或外部目标
// 入参: source 关系源URI, element 已过滤元素, attrs 无限定属性, ids 本关系部件的已用ID
// 返回: Relationship 规范化关系，Target保留原值, error 结构、ID、URI或模式错误
func parseRelationship(source string, element xml.StartElement, attrs map[string]string, ids map[string]bool) (Relationship, error) {
	if element.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
		return Relationship{}, fmt.Errorf("%w: unexpected relationship element %q", ErrInvalid, element.Name.Local)
	}
	if err := opcAttributes(attrs, "Id", "Type", "Target", "TargetMode"); err != nil {
		return Relationship{}, err
	}
	rel := Relationship{ID: strings.Trim(attrs["Id"], " \t\r\n"), Type: attrs["Type"], Target: attrs["Target"], TargetMode: TargetMode(attrs["TargetMode"])}
	if !xmlNCName(rel.ID) || ids[rel.ID] {
		return Relationship{}, fmt.Errorf("%w: invalid or duplicate relationship ID %q", ErrInvalid, rel.ID)
	}
	ids[rel.ID] = true
	typeURI, err := opcURI(rel.Type)
	if err != nil || typeURI.Scheme == "" {
		return Relationship{}, fmt.Errorf("%w: relationship type must be an absolute URI", ErrInvalid)
	}
	if _, ok := attrs["TargetMode"]; !ok {
		rel.TargetMode = TargetModeInternal
	}
	if rel.Target == "" {
		return Relationship{}, fmt.Errorf("%w: empty relationship target", ErrInvalid)
	}
	switch rel.TargetMode {
	case TargetModeInternal:
		target, err := resolvePart(source, rel.Target)
		if err != nil {
			return Relationship{}, fmt.Errorf("%w: relationship %q: %w", ErrInvalid, rel.ID, err)
		}
		if opcRelationshipName(target) {
			return Relationship{}, fmt.Errorf("%w: relationship targets a relationships part", ErrInvalid)
		}
	case TargetModeExternal:
		if _, err := opcURI(rel.Target); err != nil {
			return Relationship{}, fmt.Errorf("%w: relationship %q: %w", ErrInvalid, rel.ID, err)
		}
	default:
		return Relationship{}, fmt.Errorf("%w: invalid TargetMode %q", ErrInvalid, rel.TargetMode)
	}
	return rel, nil
}

// opcMetadataContext 在取消检查下校验两层OPC元数据，对内容类型流与关系部件均执行兼容性预处理
// 入参: ctx 取消Context, data XML数据, limits 资源上限, namespace 预期命名空间, root 根元素名, visit 子元素处理函数
// 返回: error 错误信息
func opcMetadataContext(ctx context.Context, data []byte, limits Limits, namespace, root string, visit func(xml.StartElement, map[string]string) error) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	document, err := decodeXMLVisit(data, limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err != nil {
		return err
	}
	if namespace == opcRelsNS || namespace == opcTypesNS {
		document, err = preprocessXMLContext(document, []string{namespace}, ctx)
		if err != nil {
			return err
		}
	}
	return opcMetadataElements(document, namespace, root, visit)
}

// opcMetadataElements 校验已完成兼容处理的OPC元数据根及直接子元素，关系正文沿用正式模式的字符串类型
// 入参: document 已过滤根, namespace 预期命名空间, root 根名称, visit 子元素处理函数
// 返回: error 根、属性、子结构或处理错误
func opcMetadataElements(document *xmlElement, namespace, root string, visit func(xml.StartElement, map[string]string) error) error {
	if document.Name != (xml.Name{Space: namespace, Local: root}) {
		return fmt.Errorf("%w: invalid OPC XML root", ErrInvalid)
	}
	attrs, err := opcMetadataAttributes(document, namespace)
	if err != nil {
		return err
	}
	if len(attrs) != 0 || !xmlWhitespace(document.Text) {
		return fmt.Errorf("%w: attributes on OPC XML root", ErrInvalid)
	}
	for _, element := range document.Children {
		if namespace != opcRelsNS && !xmlWhitespace(element.Text) {
			return fmt.Errorf("%w: unexpected OPC XML text", ErrInvalid)
		}
		attrs, err := opcMetadataAttributes(element, namespace)
		if err != nil {
			return err
		}
		if len(element.Children) != 0 {
			return fmt.Errorf("%w: nested OPC metadata content", ErrInvalid)
		}
		if err := visit(xml.StartElement{Name: element.Name, Attr: element.Attr}, attrs); err != nil {
			return err
		}
	}
	return nil
}

// opcMetadataAttributes 校验OPC元素的命名空间及属性，文本约束由元素类型决定，忽略命名空间声明
// 入参: element 已解码的元素, namespace 预期命名空间
// 返回: map[string]string 无命名空间的属性, error 错误信息
func opcMetadataAttributes(element *xmlElement, namespace string) (map[string]string, error) {
	if element.Name.Space != namespace {
		return nil, fmt.Errorf("%w: unexpected OPC namespace %q", ErrUnsupported, element.Name.Space)
	}
	attrs := make(map[string]string)
	for _, attr := range element.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name.Space == "" && attr.Name.Local == "xmlns" {
			continue
		}
		if attr.Name.Space != "" {
			return nil, fmt.Errorf("%w: namespaced OPC attribute %q", ErrUnsupported, attr.Name.Local)
		}
		attrs[attr.Name.Local] = attr.Value
	}
	return attrs, nil
}

// opcAttributes 检查无命名空间的属性是否属于允许集合
// 入参: attrs 属性映射, allowed 允许的属性名
// 返回: error 错误信息
func opcAttributes(attrs map[string]string, allowed ...string) error {
	for name := range attrs {
		if !slices.Contains(allowed, name) {
			return fmt.Errorf("%w: unexpected OPC attribute %q", ErrInvalid, name)
		}
	}
	return nil
}

// Error 返回原读取错误的说明
// 返回: string 错误说明
func (e *packageReadError) Error() string { return e.err.Error() }

// Unwrap 保留底层错误及已有错误分类
// 返回: error 原读取错误
func (e *packageReadError) Unwrap() error { return e.err }

// Parts 返回按部件URI排列的独立索引，包含关系及未知部件，不包含目录、物理分片或内容类型流
// 大小写按包中首次出现的部件名称保留，百分号编码统一为大写
// 返回: []PartInfo 部件索引, error 阅读器关闭或索引错误
func (r *Reader) Parts() ([]PartInfo, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	keys := make([]string, 0, len(r.pkg.parts))
	for key := range r.pkg.parts {
		if key != strings.ToLower(opcTypesName) {
			keys = append(keys, key)
		}
	}
	slices.Sort(keys)
	result := make([]PartInfo, 0, len(keys))
	for _, key := range keys {
		name := r.pkg.names[key]
		media, err := r.pkg.contentType(name)
		if err != nil {
			return nil, err
		}
		size, err := r.pkg.partSize(key)
		if err != nil {
			return nil, err
		}
		result = append(result, PartInfo{Name: name, ContentType: media, Size: int64(size)})
	}
	return result, nil
}

// readXMLPart 从逻辑部件流解析XML树，远程字典复用有界缓存，调用方须保证包索引稳定
// 入参: name 部件URI, ctx 取消Context
// 返回: *xmlElement 完整根元素，失败为nil, error 部件、XML、CRC、预算或取消错误
func (p *packageReader) readXMLPart(name string, ctx context.Context) (*xmlElement, error) {
	canonical, err := opcPartName(name)
	if err != nil {
		return nil, err
	}
	key := strings.ToLower(canonical)
	if p.cache != nil {
		media, err := p.contentType(canonical)
		if err != nil {
			return nil, err
		}
		if strings.EqualFold(opcMediaTypeBase(media), resourceDictionaryContentType) {
			data, err := p.readItemsContext(ctx, key, p.limits.MaxPartBytes)
			if err != nil {
				return nil, err
			}
			return decodeXMLReader(bytes.NewReader(data), p.limits, ctx, nil)
		}
	}
	root, err := p.readXMLPartLimits(canonical, ctx, p.limits, nil)
	if err == nil && p.cache != nil {
		p.cache.mark(key)
	}
	return root, err
}

// readXMLPartLimits 通过独立流按调用方的只读上限解析XML，不填充共享字节缓存
// 入参: name 部件URI, ctx 取消Context, limits 本次解析上限, visit 可选词元访问器
// 返回: *xmlElement 完整根元素，失败为nil, error 部件、XML、CRC、预算或取消错误
func (p *packageReader) readXMLPartLimits(name string, ctx context.Context, limits Limits, visit xmlTokenSpanVisitor) (*xmlElement, error) {
	canonical, err := opcPartName(name)
	if err != nil {
		return nil, err
	}
	input, err := p.openPartStream(ctx, strings.ToLower(canonical), PartReadOptions{MaxBytes: limits.MaxPartBytes})
	if err != nil {
		return nil, err
	}
	root, err := decodeXMLReader(input, limits, ctx, visit)
	closeErr := input.Close()
	if err != nil {
		return nil, err
	}
	if closeErr != nil {
		return nil, closeErr
	}
	return root, nil
}

// validateZIPMetadata 校验单个ZIP物理头的名称、扩展字段与注释字节总长不超过上限
// 入参: nameBytes 名称字节数, extraBytes 扩展字段字节数, commentBytes 注释字节数，本地头为零
// 返回: error 非法长度或超过65535字节的格式错误
func validateZIPMetadata(nameBytes, extraBytes, commentBytes int) error {
	remaining := packageZIPMetadataLimit
	for _, size := range [...]int{nameBytes, extraBytes, commentBytes} {
		if size < 0 || size > remaining {
			return fmt.Errorf("%w: ZIP item name, extra and comment exceed 65535 bytes", ErrInvalid)
		}
		remaining -= size
	}
	return nil
}

// readPackageZIPAt 严格读取已确认范围内的结构字段，保留底层读取错误
// 入参: input 包输入, size 输入总长, offset 结构偏移, output 字段缓冲
// 返回: error 边界、短读或输入错误
func readPackageZIPAt(input io.ReaderAt, size, offset int64, output []byte) error {
	if offset < 0 || offset > size || int64(len(output)) > size-offset {
		return fmt.Errorf("%w: ZIP structural range", ErrInvalid)
	}
	n, err := input.ReadAt(output, offset)
	if n != len(output) {
		if err == nil {
			err = io.ErrUnexpectedEOF
		}
		return fmt.Errorf("%w: ZIP structural read: %w", ErrInvalid, err)
	}
	if err != nil && err != io.EOF {
		return err
	}
	return nil
}

// validatePackageZIP 校验中央目录、本地头与数据描述符的一致性，拒绝别名偏移及载荷重叠
// 入参: ctx 取消Context, input 包输入, layout 已解析结束记录, files 标准库索引
// 返回: []packageZIPLocal 已校验并按位置排列的物理记录, error 字段、范围、尺寸、描述符、取消或输入错误
func validatePackageZIP(ctx context.Context, input io.ReaderAt, layout packageZIPLayout, files []*zip.File) ([]packageZIPLocal, error) {
	if layout.count != uint64(len(files)) {
		return nil, fmt.Errorf("%w: ZIP central entry count", ErrInvalid)
	}
	position := layout.central
	var records []packageZIPLocal
	for _, file := range files {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		var fixed [46]byte
		if err := readPackageZIPAt(input, layout.end, position, fixed[:]); err != nil {
			return nil, err
		}
		if binary.LittleEndian.Uint32(fixed[:]) != packageZIPCentralSignature {
			return nil, fmt.Errorf("%w: ZIP central record signature", ErrInvalid)
		}
		nameBytes := int(binary.LittleEndian.Uint16(fixed[28:]))
		extraBytes := int(binary.LittleEndian.Uint16(fixed[30:]))
		commentBytes := int(binary.LittleEndian.Uint16(fixed[32:]))
		if err := validateZIPMetadata(nameBytes, extraBytes, commentBytes); err != nil {
			return nil, &PartError{Part: "/" + strings.TrimPrefix(file.Name, "/"), Err: err}
		}
		variable := make([]byte, nameBytes+extraBytes+commentBytes)
		if err := readPackageZIPAt(input, layout.end, position+46, variable); err != nil {
			return nil, err
		}
		if string(variable[:nameBytes]) != file.Name {
			return nil, fmt.Errorf("%w: ZIP central name index", ErrInvalid)
		}
		cdUncomp := binary.LittleEndian.Uint32(fixed[24:])
		cdComp := binary.LittleEndian.Uint32(fixed[20:])
		cdOffset := binary.LittleEndian.Uint32(fixed[42:])
		offset := uint64(cdOffset)
		disk := uint64(binary.LittleEndian.Uint16(fixed[34:]))
		_, _, offset, disk, _, err := packageZIP64Values(variable[nameBytes:nameBytes+extraBytes], uint64(cdUncomp), uint64(cdComp), offset, disk)
		if err != nil {
			return nil, err
		}
		if disk != 0 {
			return nil, fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
		}
		if offset > uint64(layout.central-layout.base) {
			return nil, fmt.Errorf("%w: ZIP local header offset", ErrInvalid)
		}
		record, err := readPackageZIPLocal(input, layout.central, layout.base+int64(offset), file, cdOffset == 0xffffffff, cdUncomp == 0xffffffff || cdComp == 0xffffffff)
		if err != nil {
			return nil, &PartError{Part: "/" + strings.TrimPrefix(file.Name, "/"), Err: err}
		}
		records = append(records, record)
		position += 46 + int64(len(variable))
	}
	if position != layout.end {
		var signature [6]byte
		if err := readPackageZIPAt(input, layout.end, position, signature[:]); err != nil {
			return nil, err
		}
		if binary.LittleEndian.Uint32(signature[:]) != packageZIPDigitalSignature || position+6+int64(binary.LittleEndian.Uint16(signature[4:])) != layout.end {
			return nil, fmt.Errorf("%w: ZIP central trailing record", ErrInvalid)
		}
	}
	slices.SortFunc(records, func(a, b packageZIPLocal) int {
		if a.start < b.start {
			return -1
		}
		if a.start > b.start {
			return 1
		}
		return 0
	})
	for index, record := range records {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		boundary := layout.central
		if index+1 < len(records) {
			boundary = records[index+1].start
		}
		if record.end > boundary || record.start >= boundary {
			return nil, &PartError{Part: "/" + strings.TrimPrefix(record.file.Name, "/"), Err: fmt.Errorf("%w: overlapping ZIP items", ErrInvalid)}
		}
		records[index].finish = record.end
		if record.file.Flags&8 != 0 {
			length, err := packageZIPDescriptorLength(input, boundary, record)
			if err != nil {
				return nil, &PartError{Part: "/" + strings.TrimPrefix(record.file.Name, "/"), Err: err}
			}
			records[index].finish += int64(length)
		}
	}
	return records, nil
}

// readPackageZIPLocal 对照中央目录读取并校验ZIP本地头，仅在数据描述符模式接受尺寸占位
// 入参: input 包输入, boundary 中央目录起点, offset 本地头偏移, file 中央索引, extendedOffset 中央偏移是否使用ZIP64, cdSizeZIP64 中央尺寸是否使用ZIP64
// 返回: packageZIPLocal 物理范围, error 共同字段、ZIP64、边界或输入错误
func readPackageZIPLocal(input io.ReaderAt, boundary, offset int64, file *zip.File, extendedOffset, cdSizeZIP64 bool) (packageZIPLocal, error) {
	var fixed [30]byte
	if err := readPackageZIPAt(input, boundary, offset, fixed[:]); err != nil {
		return packageZIPLocal{}, err
	}
	if binary.LittleEndian.Uint32(fixed[:]) != packageZIPLocalSignature {
		return packageZIPLocal{}, fmt.Errorf("%w: ZIP local record signature", ErrInvalid)
	}
	version := binary.LittleEndian.Uint16(fixed[4:])
	flags := binary.LittleEndian.Uint16(fixed[6:])
	method := binary.LittleEndian.Uint16(fixed[8:])
	nameBytes := int(binary.LittleEndian.Uint16(fixed[26:]))
	extraBytes := int(binary.LittleEndian.Uint16(fixed[28:]))
	if err := validateZIPMetadata(nameBytes, extraBytes, 0); err != nil {
		return packageZIPLocal{}, err
	}
	variable := make([]byte, nameBytes+extraBytes)
	if err := readPackageZIPAt(input, boundary, offset+30, variable); err != nil {
		return packageZIPLocal{}, err
	}
	uncompressed, compressed, zip64, err := packageZIPLocal64Values(variable[nameBytes:], uint64(binary.LittleEndian.Uint32(fixed[22:])), uint64(binary.LittleEndian.Uint32(fixed[18:])), file.Flags&8 != 0)
	if err != nil {
		return packageZIPLocal{}, err
	}
	localFields := zipHeaderFields{
		name:         string(variable[:nameBytes]),
		version:      version,
		flags:        flags,
		method:       method,
		crc32:        binary.LittleEndian.Uint32(fixed[14:]),
		compressed:   compressed,
		uncompressed: uncompressed,
		zip64:        zip64,
	}
	centralFields := zipHeaderFields{
		name:         file.Name,
		version:      file.ReaderVersion,
		flags:        file.Flags,
		method:       file.Method,
		crc32:        file.CRC32,
		compressed:   file.CompressedSize64,
		uncompressed: file.UncompressedSize64,
		zip64:        extendedOffset || cdSizeZIP64,
	}
	if err := validateZIPLocalCentralHeaders(localFields, centralFields, file.Flags&8 == 0); err != nil {
		return packageZIPLocal{}, err
	}
	data := offset + 30 + int64(len(variable))
	if file.CompressedSize64 > uint64(boundary-data) {
		return packageZIPLocal{}, fmt.Errorf("%w: ZIP data crosses central directory", ErrInvalid)
	}
	return packageZIPLocal{file: file, start: offset, data: data, end: data + int64(file.CompressedSize64), localVersion: version, zip64: zip64, cdSizeZIP64: cdSizeZIP64}, nil
}

// validZIPExtractVersion 判断ZIP提取版本号是否属于指定压缩方式与ZIP64条件下的合法APPNOTE标准版本集
// 入参: version 提取版本号, method 压缩方式, requireZIP64 是否要求支持ZIP64扩展
// 返回: bool 是否属于合法提取版本集
func validZIPExtractVersion(version, method uint16, requireZIP64 bool) bool {
	if requireZIP64 {
		return version == 45
	}
	switch version {
	case 10:
		return method == zip.Store
	case 20, 45:
		return true
	default:
		return false
	}
}

// validateZIPLocalCentralHeaders 统一校验ZIP本地头与中央目录的安全关键字段一致性，放宽时间戳、Deflate压缩提示位及合法版本集差异
// 入参: local 本地头字段, central 中央目录字段, exactSizes 是否严格核对CRC与尺寸
// 返回: error 名称、方法、标志、版本、CRC或尺寸冲突错误
func validateZIPLocalCentralHeaders(local, central zipHeaderFields, exactSizes bool) error {
	if local.name != central.name {
		return fmt.Errorf("%w: ZIP local/central names", ErrInvalid)
	}
	if local.method != central.method {
		return fmt.Errorf("%w: ZIP local/central common fields", ErrInvalid)
	}
	flagMask := uint16(0xffff)
	if central.method == zip.Deflate {
		flagMask &^= 0x0006
	}
	if local.flags&flagMask != central.flags&flagMask {
		return fmt.Errorf("%w: ZIP local/central common fields", ErrInvalid)
	}
	needCDZIP64 := central.zip64 || central.compressed >= 0xffffffff || central.uncompressed >= 0xffffffff
	if local.zip64 && local.version < 45 || needCDZIP64 && central.version < 45 || local.version >= 45 && central.version < 45 {
		return fmt.Errorf("%w: ZIP64 extraction version", ErrInvalid)
	}
	if local.version != central.version {
		if !validZIPExtractVersion(local.version, central.method, local.zip64) || !validZIPExtractVersion(central.version, central.method, needCDZIP64) {
			return fmt.Errorf("%w: ZIP local/central extraction version", ErrInvalid)
		}
	}
	if exactSizes {
		if local.crc32 != central.crc32 || local.uncompressed != central.uncompressed || local.compressed != central.compressed {
			return fmt.Errorf("%w: ZIP local/central CRC or sizes", ErrInvalid)
		}
	} else if local.crc32 != 0 && local.crc32 != central.crc32 || local.uncompressed != 0 && local.uncompressed != central.uncompressed || local.compressed != 0 && local.compressed != central.compressed {
		return fmt.Errorf("%w: ZIP descriptor local size placeholders", ErrInvalid)
	}
	if central.method == zip.Store && central.compressed != central.uncompressed {
		return fmt.Errorf("%w: stored ZIP item sizes", ErrInvalid)
	}
	return nil
}

// packageZIP64Extra 提取扩展字段中唯一的ZIP64载荷并校验全部扩展块边界
// 入参: extra 原始扩展字段字节
// 返回: []byte ZIP64扩展体, bool 是否存在0x0001扩展块, error 扩展边界或重复错误
func packageZIP64Extra(extra []byte) ([]byte, bool, error) {
	var extended []byte
	present := false
	for len(extra) != 0 {
		if len(extra) < 4 {
			return nil, false, fmt.Errorf("%w: ZIP extra field header", ErrInvalid)
		}
		size := int(binary.LittleEndian.Uint16(extra[2:]))
		if size > len(extra)-4 {
			return nil, false, fmt.Errorf("%w: ZIP extra field length", ErrInvalid)
		}
		if binary.LittleEndian.Uint16(extra) == 1 {
			if present {
				return nil, false, fmt.Errorf("%w: duplicate ZIP64 field", ErrInvalid)
			}
			present, extended = true, extra[4:4+size]
		}
		extra = extra[4+size:]
	}
	return extended, present, nil
}

// packageZIPLocal64Values 按APPNOTE§4.5.3解析本地头ZIP64扩展，要求包含大小时成对提供原始与压缩尺寸
// 入参: extra 本地头扩展字段, uncompressed, compressed 本地头32位尺寸字段, descriptor 是否启用数据描述符
// 返回: uint64 实际未压缩尺寸, uint64 实际压缩尺寸, bool 是否启用ZIP64扩展, error 扩展格式、长度或值冲突错误
func packageZIPLocal64Values(extra []byte, uncompressed, compressed uint64, descriptor bool) (uint64, uint64, bool, error) {
	extended, present, err := packageZIP64Extra(extra)
	if err != nil {
		return 0, 0, false, err
	}
	if uncompressed == 0xffffffff || compressed == 0xffffffff {
		if !present || len(extended) != 16 {
			return 0, 0, false, fmt.Errorf("%w: incomplete ZIP64 local field", ErrInvalid)
		}
		orig64 := binary.LittleEndian.Uint64(extended[:8])
		comp64 := binary.LittleEndian.Uint64(extended[8:16])
		if uncompressed != 0xffffffff && uncompressed != orig64 || compressed != 0xffffffff && compressed != comp64 {
			return 0, 0, false, fmt.Errorf("%w: mismatched ZIP64 local sizes", ErrInvalid)
		}
		return orig64, comp64, true, nil
	}
	if !present || !descriptor {
		return uncompressed, compressed, false, nil
	}
	if len(extended) == 0 {
		return uncompressed, compressed, true, nil
	}
	if len(extended) != 16 {
		return 0, 0, false, fmt.Errorf("%w: invalid ZIP64 local field length", ErrInvalid)
	}
	orig64 := binary.LittleEndian.Uint64(extended[:8])
	comp64 := binary.LittleEndian.Uint64(extended[8:16])
	if orig64 != uncompressed || comp64 != compressed {
		return 0, 0, false, fmt.Errorf("%w: mismatched ZIP64 local sizes", ErrInvalid)
	}
	return orig64, comp64, true, nil
}

// packageZIP64Values 按占位字段顺序读取中央目录ZIP64扩展，校验哨兵字段完整存在
// 入参: extra 扩展字段, uncompressed, compressed, offset, disk 传统字段
// 返回: uint64 实际未压缩尺寸, uint64 实际压缩尺寸, uint64 实际本地头偏移, uint64 实际起始磁盘号, bool 是否存在ZIP64字段, error 扩展或缺失字段错误
func packageZIP64Values(extra []byte, uncompressed, compressed, offset, disk uint64) (uint64, uint64, uint64, uint64, bool, error) {
	extended, present, err := packageZIP64Extra(extra)
	if err != nil {
		return 0, 0, 0, 0, false, err
	}
	values := []*uint64{&uncompressed, &compressed, &offset, &disk}
	for index, value := range values {
		marker, bytes := uint64(0xffffffff), 8
		if index == 3 {
			marker, bytes = 0xffff, 4
		}
		if *value != marker {
			continue
		}
		if !present || len(extended) < bytes {
			return 0, 0, 0, 0, false, fmt.Errorf("%w: incomplete ZIP64 field", ErrInvalid)
		}
		if bytes == 8 {
			*value = binary.LittleEndian.Uint64(extended)
		} else {
			*value = uint64(binary.LittleEndian.Uint32(extended))
		}
		extended = extended[bytes:]
	}
	if present && len(extended) != 0 {
		return 0, 0, 0, 0, false, fmt.Errorf("%w: trailing bytes in ZIP64 field", ErrInvalid)
	}
	return uncompressed, compressed, offset, disk, present, nil
}

// packageZIPDescriptorLength 校验描述符并返回实际结构长度，供前向输入与中央目录完整覆盖核对
// 入参: input 包输入, boundary 下一记录边界, record 当前物理条目
// 返回: int 描述符字节数, error 字段、边界或输入错误
func packageZIPDescriptorLength(input io.ReaderAt, boundary int64, record packageZIPLocal) (int, error) {
	widths := []int{4}
	if record.zip64 || record.cdSizeZIP64 || record.file.CompressedSize64 >= 0xffffffff || record.file.UncompressedSize64 >= 0xffffffff {
		widths = []int{8}
	} else if record.localVersion >= 45 || record.file.ReaderVersion >= 45 {
		widths = []int{8, 4}
	}
	var data [28]byte
	available := min(int64(len(data)), boundary-record.end)
	if available <= 0 {
		return 0, fmt.Errorf("%w: truncated ZIP data descriptor", ErrInvalid)
	}
	if err := readPackageZIPAt(input, boundary, record.end, data[:int(available)]); err != nil {
		return 0, err
	}
	checked := false
	for _, width := range widths {
		length := 4 + 2*width
		for _, start := range []int{0, 4} {
			if start != 0 && (int(available) < 4 || binary.LittleEndian.Uint32(data[:]) != packageZIPDescriptorSignature) {
				continue
			}
			if int(available) < start+length {
				continue
			}
			checked = true
			if binary.LittleEndian.Uint32(data[start:]) != record.file.CRC32 {
				continue
			}
			compressed, uncompressed := uint64(0), uint64(0)
			if width == 4 {
				compressed = uint64(binary.LittleEndian.Uint32(data[start+4:]))
				uncompressed = uint64(binary.LittleEndian.Uint32(data[start+8:]))
			} else {
				compressed = binary.LittleEndian.Uint64(data[start+4:])
				uncompressed = binary.LittleEndian.Uint64(data[start+12:])
			}
			if compressed != record.file.CompressedSize64 || uncompressed != record.file.UncompressedSize64 {
				continue
			}
			if len(widths) > 1 && width == 8 {
				endPos := record.end + int64(start+length)
				if endPos < boundary {
					if int(available) < start+length+4 {
						continue
					}
					sig := binary.LittleEndian.Uint32(data[start+length : start+length+4])
					if sig != packageZIPLocalSignature && sig != packageZIPCentralSignature && sig != packageZIPEndSignature && sig != packageZIP64EndSignature && sig != packageZIPDigitalSignature {
						continue
					}
				}
			}
			return start + length, nil
		}
	}
	if !checked {
		return 0, fmt.Errorf("%w: truncated ZIP data descriptor", ErrInvalid)
	}
	return 0, fmt.Errorf("%w: ZIP descriptor CRC or sizes", ErrInvalid)
}

// locatePackageZIP64End 结合无前缀与前缀基址规则定位紧接定位器之前的ZIP64结束记录
// 入参: input 包输入, locatorPos 定位器物理起点, relOffset 定位器声明的相对偏移, limits 预算上限
// 返回: int64 ZIP64结束记录物理起点, bool 是否找到合法结构, error 底层输入错误
func locatePackageZIP64End(input io.ReaderAt, locatorPos int64, relOffset uint64, limits Limits) (int64, bool, error) {
	if locatorPos < 56 || relOffset > uint64(locatorPos-56) {
		return 0, false, nil
	}
	check := func(pos int64) (bool, error) {
		var head [12]byte
		if err := readPackageZIPAt(input, locatorPos, pos, head[:]); err != nil {
			return false, err
		}
		return binary.LittleEndian.Uint32(head[:4]) == packageZIP64EndSignature && binary.LittleEndian.Uint64(head[4:12]) == uint64(locatorPos-pos-12), nil
	}
	if ok, err := check(int64(relOffset)); err != nil || ok {
		return int64(relOffset), ok, err
	}
	if ok, err := check(locatorPos - 56); err != nil || ok {
		return locatorPos - 56, ok, err
	}
	floor := int64(relOffset)
	if limits.MaxPackageBytes < locatorPos-floor-12 {
		floor = locatorPos - limits.MaxPackageBytes - 12
	}
	const chunkSize = 64 << 10
	buf := make([]byte, chunkSize+11)
	for high := locatorPos - 56; high >= floor; {
		low := max(floor, high-chunkSize+1)
		readLen := int(high - low + 12)
		if err := readPackageZIPAt(input, locatorPos, low, buf[:readLen]); err != nil {
			return 0, false, err
		}
		for i := int(high - low); i >= 0; i-- {
			pos := low + int64(i)
			if binary.LittleEndian.Uint32(buf[i:i+4]) == packageZIP64EndSignature && binary.LittleEndian.Uint64(buf[i+4:i+12]) == uint64(locatorPos-pos-12) {
				return pos, true, nil
			}
		}
		high = low - 1
	}
	return 0, false, nil
}

// readPackageZIPEnd 解析传统及ZIP64结束记录，支持ZIP64哨兵与归档前缀基址，在分配索引前检查数量和元数据预算
// 入参: input 包输入, size 输入总长, limits 读取上限
// 返回: packageZIPLayout 结构边界, error 结束记录、跨卷、ZIP64或资源错误
func readPackageZIPEnd(input io.ReaderAt, size int64, limits Limits) (packageZIPLayout, error) {
	if size < 22 {
		return packageZIPLayout{}, fmt.Errorf("%w: missing ZIP end record", ErrInvalid)
	}
	length := min(size, 65535+22)
	ending := make([]byte, int(length))
	if err := readPackageZIPAt(input, size, size-length, ending); err != nil {
		return packageZIPLayout{}, err
	}
	position := -1
	for index := len(ending) - 22; index >= 0; index-- {
		if binary.LittleEndian.Uint32(ending[index:]) == packageZIPEndSignature && index+22+int(binary.LittleEndian.Uint16(ending[index+20:])) == len(ending) {
			position = index
			break
		}
	}
	if position < 0 {
		return packageZIPLayout{}, fmt.Errorf("%w: ZIP end record length", ErrInvalid)
	}
	end := ending[position:]
	diskNumber := binary.LittleEndian.Uint16(end[4:])
	cdStartDisk := binary.LittleEndian.Uint16(end[6:])
	diskEntries := binary.LittleEndian.Uint16(end[8:])
	totalEntries := binary.LittleEndian.Uint16(end[10:])
	layout := packageZIPLayout{footer: size - length + int64(position), count: uint64(totalEntries)}
	directorySize := uint64(binary.LittleEndian.Uint32(end[12:]))
	directoryOffset := uint64(binary.LittleEndian.Uint32(end[16:]))
	boundary := layout.footer
	saturated := diskNumber == 0xffff || cdStartDisk == 0xffff || diskEntries == 0xffff || totalEntries == 0xffff || directorySize == 0xffffffff || directoryOffset == 0xffffffff
	var locator [20]byte
	present := layout.footer >= 20
	if present {
		if err := readPackageZIPAt(input, size, layout.footer-20, locator[:]); err != nil {
			return packageZIPLayout{}, err
		}
		present = binary.LittleEndian.Uint32(locator[:]) == packageZIP64LocatorSignature
	}
	hasZIP64Base := false
	if present {
		relEndOffset := binary.LittleEndian.Uint64(locator[8:])
		physEndOffset, found, err := locatePackageZIP64End(input, layout.footer-20, relEndOffset, limits)
		if err != nil {
			return packageZIPLayout{}, err
		}
		if !found && !saturated {
			present = false
		} else {
			if binary.LittleEndian.Uint32(locator[4:]) != 0 || binary.LittleEndian.Uint32(locator[16:]) != 1 {
				return packageZIPLayout{}, fmt.Errorf("%w: multiple ZIP64 disks", ErrUnsupported)
			}
			if !found {
				return packageZIPLayout{}, fmt.Errorf("%w: ZIP64 end offset", ErrInvalid)
			}
			if diskNumber != 0 && diskNumber != 0xffff || cdStartDisk != 0 && cdStartDisk != 0xffff {
				return packageZIPLayout{}, fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
			}
			count, bytes, start, err := readPackageZIP64End(input, layout.footer-20, physEndOffset, limits)
			if err != nil {
				return packageZIPLayout{}, err
			}
			if diskEntries != 0xffff && uint64(diskEntries) != count || totalEntries != 0xffff && uint64(totalEntries) != count || directorySize != 0xffffffff && directorySize != bytes || directoryOffset != 0xffffffff && directoryOffset != start {
				return packageZIPLayout{}, fmt.Errorf("%w: ZIP32/ZIP64 end fields", ErrInvalid)
			}
			layout.count, directorySize, directoryOffset, boundary = count, bytes, start, physEndOffset
			layout.base, hasZIP64Base = physEndOffset-int64(relEndOffset), true
		}
	}
	if !present {
		if diskNumber != 0 || cdStartDisk != 0 || diskEntries != totalEntries {
			return packageZIPLayout{}, fmt.Errorf("%w: multiple ZIP disks", ErrUnsupported)
		}
		if diskEntries == 0xffff || totalEntries == 0xffff || directorySize == 0xffffffff || directoryOffset == 0xffffffff {
			return packageZIPLayout{}, fmt.Errorf("%w: missing ZIP64 end locator", ErrInvalid)
		}
	}
	if layout.count > uint64(limits.MaxPartCount) || directorySize > uint64(limits.MaxPackageBytes) {
		return packageZIPLayout{}, fmt.Errorf("%w: ZIP central metadata budget", ErrLimit)
	}
	if hasZIP64Base {
		if layout.base < 0 || directorySize > uint64(boundary-layout.base) || directoryOffset > uint64(boundary-layout.base)-directorySize {
			return packageZIPLayout{}, fmt.Errorf("%w: ZIP central directory bounds", ErrInvalid)
		}
	} else {
		if directorySize > uint64(boundary) || directoryOffset > uint64(boundary)-directorySize {
			return packageZIPLayout{}, fmt.Errorf("%w: ZIP central directory bounds", ErrInvalid)
		}
		dirSize, dirOff := int64(directorySize), int64(directoryOffset)
		validCentralChain := func(start int64) (bool, error) {
			if dirSize == 0 {
				return layout.count == 0 && start >= 0 && start <= boundary, nil
			}
			if start < 0 || dirSize > boundary-start {
				return false, nil
			}
			pos, limit := start, start+dirSize
			for range layout.count {
				if limit-pos < 46 {
					return false, nil
				}
				var fixed [46]byte
				if err := readPackageZIPAt(input, limit, pos, fixed[:]); err != nil {
					return false, err
				}
				if binary.LittleEndian.Uint32(fixed[:]) != packageZIPCentralSignature {
					return false, nil
				}
				nameBytes := int(binary.LittleEndian.Uint16(fixed[28:]))
				extraBytes := int(binary.LittleEndian.Uint16(fixed[30:]))
				commentBytes := int(binary.LittleEndian.Uint16(fixed[32:]))
				if validateZIPMetadata(nameBytes, extraBytes, commentBytes) != nil {
					return false, nil
				}
				entryLen := 46 + int64(nameBytes) + int64(extraBytes) + int64(commentBytes)
				if entryLen > limit-pos {
					return false, nil
				}
				pos += entryLen
			}
			if pos == limit {
				return true, nil
			}
			if limit-pos < 6 {
				return false, nil
			}
			var digital [6]byte
			if err := readPackageZIPAt(input, limit, pos, digital[:]); err != nil {
				return false, err
			}
			return binary.LittleEndian.Uint32(digital[:]) == packageZIPDigitalSignature && pos+6+int64(binary.LittleEndian.Uint16(digital[4:])) == limit, nil
		}
		hasDigitalSig := func(pos int64) (bool, error) {
			if pos == boundary {
				return true, nil
			}
			if pos < 0 || boundary-pos < 6 {
				return false, nil
			}
			var digital [6]byte
			if err := readPackageZIPAt(input, boundary, pos, digital[:]); err != nil {
				return false, err
			}
			return binary.LittleEndian.Uint32(digital[:]) == packageZIPDigitalSignature && pos+6+int64(binary.LittleEndian.Uint16(digital[4:])) == boundary, nil
		}
		resolved := false
		if dirOff+dirSize == boundary {
			layout.base, resolved = 0, true
		} else {
			okCentral, err := validCentralChain(dirOff)
			if err != nil {
				return packageZIPLayout{}, err
			}
			if okCentral {
				okSig, err := hasDigitalSig(dirOff + dirSize)
				if err != nil {
					return packageZIPLayout{}, err
				}
				if okSig {
					layout.base, resolved = 0, true
				}
			}
		}
		if !resolved && dirSize > 0 {
			candBase := boundary - dirSize - dirOff
			okCentral, err := validCentralChain(candBase + dirOff)
			if err != nil {
				return packageZIPLayout{}, err
			}
			if okCentral {
				layout.base, resolved = candBase, true
			}
		}
		if !resolved && dirSize > 0 {
			minSigPos := max(dirOff+dirSize, boundary-(6+packageZIPMetadataLimit))
			maxSigPos := boundary - 6
			if minSigPos <= maxSigPos {
				scan := make([]byte, int(boundary-minSigPos))
				if err := readPackageZIPAt(input, boundary, minSigPos, scan); err != nil {
					return packageZIPLayout{}, err
				}
				for idx := int(maxSigPos - minSigPos); idx >= 0; idx-- {
					sigPos := minSigPos + int64(idx)
					if binary.LittleEndian.Uint32(scan[idx:idx+4]) != packageZIPDigitalSignature || sigPos+6+int64(binary.LittleEndian.Uint16(scan[idx+4:idx+6])) != boundary {
						continue
					}
					candBase := sigPos - dirSize - dirOff
					okCentral, err := validCentralChain(candBase + dirOff)
					if err != nil {
						return packageZIPLayout{}, err
					}
					if okCentral {
						layout.base, resolved = candBase, true
						break
					}
				}
			}
		}
		if !resolved {
			layout.base = 0
		}
	}
	layout.central = layout.base + int64(directoryOffset)
	layout.end = layout.central + int64(directorySize)
	if layout.end != boundary {
		var digital [6]byte
		if err := readPackageZIPAt(input, boundary, layout.end, digital[:]); err != nil {
			return packageZIPLayout{}, err
		}
		if binary.LittleEndian.Uint32(digital[:]) != packageZIPDigitalSignature || layout.end+6+int64(binary.LittleEndian.Uint16(digital[4:])) != boundary {
			return packageZIPLayout{}, fmt.Errorf("%w: ZIP central/end record gap", ErrInvalid)
		}
	}
	return layout, nil
}

// readPackageZIP64End 校验单卷ZIP64第一版记录和可传递的扩展区，不处理第二版中央目录加密
// 入参: input 包输入, boundary 定位器起点, offset ZIP64结束记录起点, limits 元数据上限
// 返回: uint64 条目数, uint64 中央目录长度, uint64 中央目录偏移, error 结构、版本、跨卷或资源错误
func readPackageZIP64End(input io.ReaderAt, boundary, offset int64, limits Limits) (uint64, uint64, uint64, error) {
	var record [56]byte
	if err := readPackageZIPAt(input, boundary, offset, record[:]); err != nil {
		return 0, 0, 0, err
	}
	if binary.LittleEndian.Uint32(record[:]) != packageZIP64EndSignature {
		return 0, 0, 0, fmt.Errorf("%w: ZIP64 end signature", ErrInvalid)
	}
	size := binary.LittleEndian.Uint64(record[4:])
	if size < 44 || size != uint64(boundary-offset-12) {
		return 0, 0, 0, fmt.Errorf("%w: ZIP64 end size", ErrInvalid)
	}
	if size > uint64(limits.MaxPackageBytes) {
		return 0, 0, 0, fmt.Errorf("%w: ZIP64 metadata budget", ErrLimit)
	}
	if binary.LittleEndian.Uint16(record[14:]) >= 62 {
		return 0, 0, 0, fmt.Errorf("%w: ZIP64 second-version end record", ErrUnsupported)
	}
	if binary.LittleEndian.Uint32(record[16:]) != 0 || binary.LittleEndian.Uint32(record[20:]) != 0 || binary.LittleEndian.Uint64(record[24:]) != binary.LittleEndian.Uint64(record[32:]) {
		return 0, 0, 0, fmt.Errorf("%w: multiple ZIP64 disks", ErrUnsupported)
	}
	return binary.LittleEndian.Uint64(record[32:]), binary.LittleEndian.Uint64(record[40:]), binary.LittleEndian.Uint64(record[48:]), nil
}
