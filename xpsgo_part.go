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
	"errors"
	"fmt"
	"io"
	"net/netip"
	"net/url"
	"strings"
	"sync"
	"unicode/utf8"
)

// uriSubDelimiters 定义RFC 3986 URI子分隔符集合
const uriSubDelimiters = "!$&'()*+,;="

// requiredFont 等常量表示固定页面所需的嵌入资源类别
const (
	requiredFont requiredResourceKind = iota + 1
	requiredImage
	requiredProfile
	requiredDictionary
	requiredModel
)

// PartReadOptions 设置逻辑部件流的解压字节上限，零值沿用阅读器上限
type PartReadOptions struct {
	MaxBytes int64
}

// partStream 顺序读取内存或ZIP分片，逐片校验尺寸及CRC，不分配完整逻辑部件
type partStream struct {
	mu        sync.Mutex
	owner     *Reader
	pkg       *packageReader
	key       string
	context   context.Context
	memory    *bytes.Reader
	input     io.ReadCloser
	logical   bool
	index     int
	partBytes uint64
	pieceRead uint64
	closed    bool
	terminal  error
}

// requiredResourceKind 标识包内渲染依赖的类型
type requiredResourceKind uint8

// requiredResource 保存依赖目标及首次声明它的部件和属性位置
type requiredResource struct {
	Part       string
	Kind       requiredResourceKind
	SourcePart string
	Element    string
	Attribute  string
}

// resolvePart 按源部件URI解析包内引用并规范化转义，拒绝外部URI、查询、片段及越界路径
// 入参: source 源部件的包根URI，包本身使用/, target 相对或包根URI
// 返回: string 规范化的包根URI, error 错误信息
func resolvePart(source, target string) (string, error) {
	if source != "/" {
		var err error
		source, err = opcPartName(source)
		if err != nil {
			return "", fmt.Errorf("invalid source: %w", err)
		}
	}
	u, err := opcURI(target)
	if err != nil {
		return "", err
	}
	if target == "" || u.Scheme != "" || u.Host != "" || u.User != nil || u.Opaque != "" || strings.HasPrefix(target, "//") {
		return "", fmt.Errorf("%w: target is not an internal part reference: %q", ErrInvalid, target)
	}
	if strings.ContainsAny(target, "?#") {
		return "", fmt.Errorf("%w: query or fragment in part reference: %q", ErrUnsupported, target)
	}
	escaped, err := opcNormalizePath(target, true)
	if err != nil {
		return "", err
	}
	var segments []string
	if !strings.HasPrefix(escaped, "/") && source != "/" {
		segments = strings.Split(source[1:], "/")
		segments = segments[:len(segments)-1]
	}
	for _, segment := range strings.Split(strings.TrimPrefix(escaped, "/"), "/") {
		switch segment {
		case ".":
		case "..":
			if len(segments) == 0 {
				return "", fmt.Errorf("%w: part reference escapes package root: %q", ErrInvalid, target)
			}
			segments = segments[:len(segments)-1]
		case "":
			return "", fmt.Errorf("%w: empty path segment in %q", ErrInvalid, target)
		default:
			segments = append(segments, segment)
		}
	}
	if strings.HasSuffix(escaped, "/.") || strings.HasSuffix(escaped, "/..") || escaped == "." || escaped == ".." {
		return "", fmt.Errorf("%w: part reference identifies a directory: %q", ErrInvalid, target)
	}
	return opcPartName("/" + strings.Join(segments, "/"))
}

// relativePart 将规范部件地址转换为相对于源部件的路径，保留转义及目标文件名
// 入参: source 源部件地址，包根使用/, target 目标部件地址
// 返回: string 不含方案、包根前缀或片段的相对引用, error 部件地址错误
func relativePart(source, target string) (string, error) {
	var err error
	if source != "/" {
		source, err = opcPartName(source)
		if err != nil {
			return "", err
		}
	}
	target, err = opcPartName(target)
	if err != nil {
		return "", err
	}
	var base []string
	if source != "/" {
		base = strings.Split(source[1:], "/")
		base = base[:len(base)-1]
	}
	parts := strings.Split(target[1:], "/")
	common := 0
	for common < len(base) && common < len(parts)-1 && base[common] == parts[common] {
		common++
	}
	result := strings.Repeat("../", len(base)-common) + strings.Join(parts[common:], "/")
	first, _, _ := strings.Cut(result, "/")
	if strings.ContainsRune(first, ':') {
		result = "./" + result
	}
	return result, nil
}

// opcPartName 校验严格的OPC部件URI，不执行可能掩盖非法名称的路径清理
// 入参: name 包根URI，非ASCII字符须使用UTF-8百分号编码
// 返回: string 转义十六进制大写的URI, error 错误信息
func opcPartName(name string) (string, error) {
	if !strings.HasPrefix(name, "/") || strings.HasPrefix(name, "//") || strings.ContainsAny(name, "?#") {
		return "", fmt.Errorf("%w: invalid part name %q", ErrInvalid, name)
	}
	canonical, err := opcNormalizePath(name, false)
	if err != nil {
		return "", err
	}
	for _, segment := range strings.Split(canonical[1:], "/") {
		if segment == "" || strings.HasSuffix(segment, ".") {
			return "", fmt.Errorf("%w: invalid part name segment in %q", ErrInvalid, name)
		}
	}
	return canonical, nil
}

// opcNormalizePath 共用OPC路径字符校验与百分号编码规范化，decodeUnreserved控制是否解码未保留字符
// 入参: value 原始路径, decodeUnreserved 是否按相对URI等价规则解码未保留ASCII字符
// 返回: string 规范化路径, error 错误信息
func opcNormalizePath(value string, decodeUnreserved bool) (string, error) {
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
					return "", fmt.Errorf("%w: invalid percent escape in %q", ErrInvalid, value)
				}
				hi, lo := opcHex(value[i+1]), opcHex(value[i+2])
				if hi < 0 || lo < 0 {
					return "", fmt.Errorf("%w: invalid percent escape in %q", ErrInvalid, value)
				}
				decoded := byte(hi*16 + lo)
				if decoded == '/' || decoded == '\\' {
					return "", fmt.Errorf("%w: forbidden percent escape in %q", ErrInvalid, value)
				}
				pct = append(pct, decoded)
				if opcUnreserved(decoded) {
					if !decodeUnreserved {
						return "", fmt.Errorf("%w: forbidden percent escape in %q", ErrInvalid, value)
					}
					b.WriteByte(decoded)
				} else {
					b.WriteByte('%')
					b.WriteByte(hex[hi])
					b.WriteByte(hex[lo])
				}
				i += 3
			}
			if !utf8.Valid(pct) {
				return "", fmt.Errorf("%w: invalid UTF-8 percent escape in %q", ErrInvalid, value)
			}
			i--
		} else if opcUnreserved(c) || strings.ContainsRune("/!$&'()*+,;=:@", rune(c)) {
			b.WriteByte(c)
		} else {
			return "", fmt.Errorf("%w: invalid URI path character in %q", ErrInvalid, value)
		}
	}
	return b.String(), nil
}

// opcURI 校验URI引用的通用语法并解析分量，禁止隐式修复文件系统路径
// 入参: value URI引用
// 返回: *url.URL 已解析引用, error 错误信息
func opcURI(value string) (*url.URL, error) {
	if !uriReference(value) {
		return nil, fmt.Errorf("%w: invalid URI %q", ErrInvalid, value)
	}
	u, err := url.Parse(value)
	if err != nil {
		return nil, fmt.Errorf("%w: invalid URI %q: %w", ErrInvalid, value, err)
	}
	return u, nil
}

// opcUnreserved 判断字符是否属于RFC 3986的未保留ASCII字符
// 入参: c 待检查字节
// 返回: bool 是否属于未保留字符
func opcUnreserved(c byte) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || strings.ContainsRune("-._~", rune(c))
}

// opcHex 将十六进制字符转换为数值
// 入参: c 待转换字节
// 返回: int 数值，非法字符返回 -1
func opcHex(c byte) int {
	switch {
	case c >= '0' && c <= '9':
		return int(c - '0')
	case c >= 'a' && c <= 'f':
		return int(c-'a') + 10
	case c >= 'A' && c <= 'F':
		return int(c-'A') + 10
	default:
		return -1
	}
}

// opcRelationshipName 判断部件名称是否符合OPC关系部件的保留命名规则
// 入参: name 已校验的包根URI
// 返回: bool 是否为关系部件
func opcRelationshipName(name string) bool {
	segments := strings.Split(strings.ToLower(name), "/")
	if len(segments) < 3 || segments[len(segments)-2] != "_rels" {
		return false
	}
	last := segments[len(segments)-1]
	if !strings.HasSuffix(last, ".rels") {
		return false
	}
	return len(last) > len(".rels") || len(segments) == 3 && segments[0] == ""
}

// opcMetadataPart 判断部件是否属于受MaxMetadataBytes约束的OPC元数据部件
// 入参: name 部件包根URI, media 部件内容类型
// 返回: bool 是否为关系部件、内容类型流或核心属性部件
func opcMetadataPart(name, media string) bool {
	return opcRelationshipName(name) || strings.EqualFold(name, opcTypesName) || strings.EqualFold(media, opcCoreType)
}

// OpenPart 打开独立逻辑部件读取流并按序拼接分片，使用后须关闭流，读取至EOF后完成全部CRC与尺寸校验
// 关闭流不影响阅读器，阅读器关闭后流不可读；同一流的Read和Close可并发调用
// 入参: ctx 取消Context，nil采用Background, name 部件URI, options 读取参数，nil采用默认值
// 返回: io.ReadCloser 部件流，失败为nil, error 部件、预算、关闭或取消错误
func (r *Reader) OpenPart(ctx context.Context, name string, options *PartReadOptions) (io.ReadCloser, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	part, err := opcPartName(name)
	if err != nil {
		return nil, err
	}
	configuration := PartReadOptions{MaxBytes: r.limits.MaxPartBytes}
	if options != nil && options.MaxBytes != 0 {
		configuration.MaxBytes = options.MaxBytes
	}
	stream, err := r.pkg.openPartStream(ctx, strings.ToLower(part), configuration)
	if err != nil {
		return nil, err
	}
	stream.owner = r
	return stream, nil
}

// openPartStream 校验声明尺寸及读取预算后建立惰性流，调用方须保证包索引不可变
// 入参: ctx 取消Context, key 规范化部件键, options 字节上限参数
// 返回: *partStream 独立流, error 部件、预算或取消错误
func (p *packageReader) openPartStream(ctx context.Context, key string, options PartReadOptions) (*partStream, error) {
	if options.MaxBytes < 1 {
		return nil, fmt.Errorf("%w: part stream byte limit", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	size, err := p.partSize(key)
	if err != nil {
		return nil, err
	}
	limit := min(options.MaxBytes, p.limits.MaxPartBytes, p.limits.MaxPackageBytes)
	if opcRelationshipName(p.names[key]) || key == strings.ToLower(opcTypesName) {
		limit = min(limit, p.limits.MaxMetadataBytes)
	}
	if p.beforeRead != nil {
		allowed, err := p.beforeRead(key, size, limit)
		if err != nil {
			return nil, err
		}
		if allowed < 0 {
			return nil, fmt.Errorf("%w: part stream read allowance", ErrLimit)
		}
		limit = min(limit, allowed)
	}
	if size > uint64(limit) {
		return nil, &PartError{Part: p.names[key], Err: fmt.Errorf("%w: part stream bytes", ErrLimit)}
	}
	stream := &partStream{pkg: p, key: key, context: ctx, partBytes: size}
	if data, present := p.data[key]; present {
		stream.memory = bytes.NewReader(data)
	} else if p.cache != nil {
		if data, present := p.cache.get(key); present {
			stream.memory = bytes.NewReader(data)
		}
	}
	if stream.memory == nil && p.open != nil {
		stream.input, err = p.open(key)
		if err != nil {
			return nil, &packageReadError{err: err}
		}
		stream.logical = true
	}
	return stream, nil
}

// Read 顺序读取当前分片，空分片不产生无进展读取，错误及EOF在后续读取中保持不变
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 封装、尺寸、CRC、关闭或取消错误
func (s *partStream) Read(output []byte) (int, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return 0, ErrClosed
	}
	if s.owner != nil {
		s.owner.mu.RLock()
		defer s.owner.mu.RUnlock()
		if s.owner.closed {
			return 0, s.finish(ErrClosed)
		}
	}
	if s.terminal != nil {
		return 0, s.terminal
	}
	if err := checkContext(s.context); err != nil {
		return 0, s.finish(err)
	}
	if len(output) == 0 {
		return 0, nil
	}
	if s.memory != nil {
		n, err := s.memory.Read(output)
		if err != nil {
			s.terminal = err
		}
		return n, err
	}
	if s.logical {
		return s.readLogical(output)
	}
	for {
		if err := checkContext(s.context); err != nil {
			return 0, s.finish(err)
		}
		if s.input == nil {
			if s.index == len(s.pkg.parts[s.key]) {
				if s.partBytes != 0 {
					return 0, s.finish(s.streamError(errors.New("part stream size")))
				}
				return 0, s.finish(io.EOF)
			}
			var err error
			s.input, err = s.pkg.parts[s.key][s.index].Open()
			if err != nil {
				return 0, s.finish(s.streamError(&packageReadError{err: err}))
			}
			s.pieceRead = 0
		}
		file := s.pkg.parts[s.key][s.index]
		remaining := min(s.partBytes, file.UncompressedSize64-s.pieceRead)
		target := output
		var probe [1]byte
		if remaining == 0 {
			target = probe[:]
		} else if uint64(len(target)) > remaining {
			target = target[:int(remaining)]
		}
		n, err := s.input.Read(target)
		if uint64(n) > s.partBytes || uint64(n) > file.UncompressedSize64-s.pieceRead {
			return 0, s.finish(s.streamError(errors.New("part stream declared size")))
		}
		s.partBytes -= uint64(n)
		s.pieceRead += uint64(n)
		if err != nil {
			if err != io.EOF {
				return n, s.finish(s.streamError(&packageReadError{err: err}))
			}
			closeErr := s.input.Close()
			s.input = nil
			if closeErr != nil {
				return n, s.finish(s.streamError(&packageReadError{err: closeErr}))
			}
			if s.pieceRead != file.UncompressedSize64 {
				return n, s.finish(s.streamError(errors.New("part stream piece size or close")))
			}
			s.index++
			if n != 0 {
				return n, nil
			}
			continue
		}
		if n == 0 {
			return 0, s.finish(s.streamError(&packageReadError{err: io.ErrNoProgress}))
		}
		return n, nil
	}
}

// Close 释放当前解压器，不接管包输入或阅读器的关闭责任，重复关闭无副作用
// 返回: error 当前分片关闭错误
func (s *partStream) Close() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return nil
	}
	s.closed = true
	s.memory, s.pkg, s.owner, s.context = nil, nil, nil, nil
	if s.input != nil {
		err := s.input.Close()
		s.input = nil
		return err
	}
	return nil
}

// finish 保留终止状态并释放当前解压器，调用方须持有流锁
// 入参: err EOF、读取或取消错误
// 返回: error 原终止状态
func (s *partStream) finish(err error) error {
	if s.input != nil {
		_ = s.input.Close()
		s.input = nil
	}
	s.terminal = err
	return err
}

// readLogical 校验前向存储后端返回的逻辑部件尺寸，保持与ZIP分片读取相同的预算及终止语义
// 入参: output 读取缓冲
// 返回: int 已读字节数, error 后端、尺寸或结束信息
func (s *partStream) readLogical(output []byte) (int, error) {
	var probe [1]byte
	target := output
	if s.partBytes == 0 {
		target = probe[:]
	} else if uint64(len(target)) > s.partBytes {
		target = target[:int(s.partBytes)]
	}
	n, err := s.input.Read(target)
	if uint64(n) > s.partBytes {
		return 0, s.finish(s.streamError(errors.New("logical stream declared size")))
	}
	s.partBytes -= uint64(n)
	if err != nil {
		if err != io.EOF {
			return n, s.finish(s.logicalError(err))
		}
		if s.partBytes != 0 {
			return n, s.finish(s.streamError(errors.New("logical stream truncated")))
		}
		closeErr := s.input.Close()
		s.input = nil
		if closeErr != nil {
			return n, s.finish(s.logicalError(closeErr))
		}
		return n, s.finish(io.EOF)
	}
	if n == 0 {
		return 0, s.finish(s.streamError(&packageReadError{err: io.ErrNoProgress}))
	}
	return n, nil
}

// logicalError 透传取消、限额及关闭错误，其余底层读取或关闭故障归类为部件流错误
// 入参: err 底层读取或关闭错误
// 返回: error 保留原分类或带部件信息的错误
func (s *partStream) logicalError(err error) error {
	if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) || errors.Is(err, ErrLimit) || errors.Is(err, ErrClosed) {
		return err
	}
	return s.streamError(&packageReadError{err: err})
}

// streamError 保留逻辑部件来源及原始ZIP错误分类
// 入参: err 原始错误
// 返回: error 带部件信息的错误
func (s *partStream) streamError(err error) error {
	return &PartError{Part: s.pkg.names[s.key], Err: fmt.Errorf("%w: part stream: %w", ErrInvalid, err)}
}

// uriReference 校验RFC3986通用引用语法，不规范化字符或执行协议专属校验和网络访问
// 入参: value URI引用，允许空值及相对引用
// 返回: bool 是否符合通用语法
func uriReference(value string) bool {
	body, fragment, present := strings.Cut(value, "#")
	if present && !uriCharacters(fragment, ":@/?", true) {
		return false
	}
	body, query, present := strings.Cut(body, "?")
	if present && !uriCharacters(query, ":@/?", true) {
		return false
	}
	colon, slash := strings.IndexByte(body, ':'), strings.IndexByte(body, '/')
	if colon >= 0 && (slash < 0 || colon < slash) {
		if !uriScheme(body[:colon]) {
			return false
		}
		body = body[colon+1:]
	}
	if strings.HasPrefix(body, "//") {
		authority := body[2:]
		body = ""
		if end := strings.IndexByte(authority, '/'); end >= 0 {
			body, authority = authority[end:], authority[:end]
		}
		if !uriAuthority(authority) {
			return false
		}
	}
	return uriCharacters(body, ":@/", true)
}

// uriScheme 校验由字母起始的协议名称，不限定可用协议集合
// 入参: value 协议名称
// 返回: bool 是否符合协议名称语法
func uriScheme(value string) bool {
	if value == "" || !(value[0] >= 'A' && value[0] <= 'Z' || value[0] >= 'a' && value[0] <= 'z') {
		return false
	}
	for index := 1; index < len(value); index++ {
		c := value[index]
		if !(c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z' || c >= '0' && c <= '9' || c == '+' || c == '-' || c == '.') {
			return false
		}
	}
	return true
}

// uriAuthority 校验用户信息、主机及端口，不查询主机或限制协议允许的端口范围
// 入参: value URI权威部分
// 返回: bool 是否符合权威部分语法
func uriAuthority(value string) bool {
	if before, after, present := strings.Cut(value, "@"); present {
		if !uriCharacters(before, ":", true) {
			return false
		}
		value = after
	}
	port := ""
	if strings.HasPrefix(value, "[") {
		end := strings.IndexByte(value, ']')
		if end < 0 || !uriIPLiteral(value[1:end]) {
			return false
		}
		tail := value[end+1:]
		if tail != "" {
			if tail[0] != ':' {
				return false
			}
			port = tail[1:]
		}
	} else {
		host := value
		if before, after, present := strings.Cut(value, ":"); present {
			host, port = before, after
		}
		if !uriCharacters(host, "", true) {
			return false
		}
	}
	for index := range len(port) {
		if port[index] < '0' || port[index] > '9' {
			return false
		}
	}
	return true
}

// uriIPLiteral 校验IPv6及IPvFuture字面量，不将作用域标识扩展混入RFC3986语法
// 入参: value 不含方括号的地址字面量
// 返回: bool 是否符合地址字面量语法
func uriIPLiteral(value string) bool {
	if value != "" && (value[0] == 'v' || value[0] == 'V') {
		version, address, present := strings.Cut(value[1:], ".")
		if !present || version == "" || address == "" {
			return false
		}
		for index := range len(version) {
			if opcHex(version[index]) < 0 {
				return false
			}
		}
		return uriCharacters(address, ":", false)
	}
	address, err := netip.ParseAddr(value)
	return err == nil && address.Is6() && address.Zone() == ""
}

// uriCharacters 校验未保留字符、子分隔符、指定分隔符及可选百分号编码，不解码标识内容
// 入参: value 待检查内容, extra 当前分量允许的额外分隔符, escapes 是否允许百分号编码
// 返回: bool 是否仅包含允许的字符
func uriCharacters(value, extra string, escapes bool) bool {
	for index := 0; index < len(value); index++ {
		c := value[index]
		if escapes && c == '%' {
			if index+2 >= len(value) || opcHex(value[index+1]) < 0 || opcHex(value[index+2]) < 0 {
				return false
			}
			index += 2
		} else if !opcUnreserved(c) && !strings.ContainsRune(uriSubDelimiters, rune(c)) && !strings.ContainsRune(extra, rune(c)) {
			return false
		}
	}
	return true
}

// validateRequiredResources 校验单页直接与间接资源的关系覆盖、存在性及媒体类型，调用方须持有阅读器读锁
// 入参: part 页面部件URI, graph 已完成MCE和资源绑定的完整单页资源图
// 返回: []requiredResource 按首次出现顺序去重的资源依赖, error 依赖或关系错误
func (r *Reader) validateRequiredResources(part string, graph *resourceGraph) ([]requiredResource, error) {
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	if graph == nil || !strings.EqualFold(canonical, graph.PagePart) || formatNamespace(r.format) == "" {
		return nil, fmt.Errorf("%w: required resources need the matching page resource graph", ErrInvalid)
	}
	resources, err := collectRequiredResources(graph, r.format)
	if err != nil {
		return nil, err
	}
	relations, err := r.pkg.relationships(canonical)
	if err != nil {
		return nil, &PartError{Part: canonical, Err: err}
	}
	typeURI := formatNamespace(r.format) + "/required-resource"
	targets := make(map[string]string)
	for _, relation := range relations {
		if relation.Type != typeURI {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return nil, &PartError{Part: canonical, Err: fmt.Errorf("%w: external Required Resource relationship %q", ErrInvalid, relation.ID)}
		}
		target, err := resolvePart(canonical, relation.Target)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: err}
		}
		media, err := r.pkg.contentType(target)
		if err != nil {
			return nil, &PartError{Part: canonical, Err: fmt.Errorf("Required Resource relationship %q target %s: %w", relation.ID, target, err)}
		}
		targets[strings.ToLower(target)] = media
	}
	for _, dependency := range resources {
		media, ok := targets[strings.ToLower(dependency.Part)]
		if !ok {
			return nil, requiredResourceError(dependency, fmt.Errorf("%w: missing Required Resource relationship from page %s to %s", ErrInvalid, canonical, dependency.Part))
		}
		if !requiredResourceMedia(dependency.Kind, media) {
			return nil, requiredResourceError(dependency, fmt.Errorf("%w: unexpected resource content type %q for %s", ErrInvalid, media, dependency.Part))
		}
	}
	checked := make(map[string]bool)
	for _, dependency := range resources {
		key := strings.ToLower(dependency.Part)
		if checked[key] {
			continue
		}
		checked[key] = true
		relations, err := r.pkg.relationships(dependency.Part)
		if err != nil {
			return nil, &PartError{Part: dependency.Part, Err: err}
		}
		for _, relation := range relations {
			if relation.Type == typeURI {
				return nil, &PartError{Part: dependency.Part, Err: fmt.Errorf("%w: Required Resource relationship %q must originate from FixedPage, not a resource part", ErrInvalid, relation.ID)}
			}
		}
	}
	return resources, nil
}

// collectRequiredResources 枚举预处理后页面及远程字典的全部包内部件引用，含字典中未使用的定义
// 入参: graph 完整资源图, format 文档格式
// 返回: []requiredResource 按类型及OPC等价部件名去重的依赖, error URI或引用语法错误
func collectRequiredResources(graph *resourceGraph, format Format) ([]requiredResource, error) {
	if graph == nil || len(graph.Nodes) == 0 || formatNamespace(format) == "" {
		return nil, fmt.Errorf("%w: incomplete required resource graph", ErrInvalid)
	}
	var result []requiredResource
	seen := make(map[string]bool)
	for _, node := range graph.Nodes {
		if node == nil || node.Name.Space != formatNamespace(format) || graph.Parts[node] == "" {
			return nil, fmt.Errorf("%w: missing resource definition provenance", ErrInvalid)
		}
		add := func(uri string, kind requiredResourceKind, attribute string) error {
			dependency := requiredResource{Kind: kind, SourcePart: graph.Parts[node], Element: node.Name.Local, Attribute: attribute}
			part, err := resolvePart(dependency.SourcePart, uri)
			if err != nil {
				return requiredResourceError(dependency, err)
			}
			dependency.Part = part
			key := fmt.Sprintf("%d:%s", kind, strings.ToLower(part))
			if !seen[key] {
				seen[key] = true
				result = append(result, dependency)
			}
			return nil
		}
		mandatory := ""
		switch node.Name.Local {
		case "Glyphs":
			mandatory = "FontUri"
		case "ImageBrush":
			mandatory = "ImageSource"
		}
		if mandatory != "" {
			if _, present := node.attribute(mandatory); !present {
				return nil, resourceError(graph.Parts[node], node, "missing "+mandatory)
			}
		}
		for _, attr := range node.Attr {
			if graph.Bindings[node][attr.Name.Local] != nil {
				continue
			}
			references, err := resourceAttributeReferences(node, attr)
			if err != nil {
				return nil, &PartError{Part: graph.Parts[node], Element: node.Name.Local, Err: fmt.Errorf("%s: %w", attr.Name.Local, err)}
			}
			for _, reference := range references {
				if err := add(reference.uri, reference.kind, attr.Name.Local); err != nil {
					return nil, err
				}
			}
		}
	}
	return result, nil
}

// requiredColorAttribute 判断属性是否直接承载颜色或画刷字面值
// 入参: element 元素本地名称, attribute 属性本地名称
// 返回: bool 是否需要从颜色中提取ICC引用
func requiredColorAttribute(element, attribute string) bool {
	return (element == "SolidColorBrush" || element == "GradientStop") && attribute == "Color" || (element == "Path" || element == "Glyphs") && attribute == "Fill" || element == "Path" && attribute == "Stroke"
}

// requiredResourceMedia 按双格式最终规范核对被访问资源的无参数媒体类型
// 入参: kind 资源种类, media 内容类型
// 返回: bool 类型是否符合用途
func requiredResourceMedia(kind requiredResourceKind, media string) bool {
	switch kind {
	case requiredFont:
		return strings.EqualFold(media, "application/vnd.ms-opentype") || strings.EqualFold(media, "application/vnd.ms-package.obfuscated-opentype")
	case requiredImage:
		return strings.EqualFold(media, "image/jpeg") || strings.EqualFold(media, "image/png") || strings.EqualFold(media, "image/tiff") || strings.EqualFold(media, "image/vnd.ms-photo")
	case requiredProfile:
		return strings.EqualFold(media, "application/vnd.ms-color.iccprofile")
	case requiredDictionary:
		return strings.EqualFold(media, resourceDictionaryContentType)
	case requiredModel:
		model, err := resourceModelMedia(media)
		return model && err == nil
	}
	return false
}

// graphicResourceMedia 判断媒体类型是否属于字体、图像、色彩配置或远程资源字典等图形资源
// 入参: media 无参数内容类型
// 返回: bool 是否为图形资源类型
func graphicResourceMedia(media string) bool {
	for _, kind := range [...]requiredResourceKind{requiredFont, requiredImage, requiredProfile, requiredDictionary} {
		if requiredResourceMedia(kind, media) {
			return true
		}
	}
	return false
}

// requiredResourceError 包装依赖声明位置及属性名
// 入参: resource 资源依赖, err 原始错误
// 返回: error 含部件与属性来源的错误
func requiredResourceError(resource requiredResource, err error) error {
	return &PartError{Part: resource.SourcePart, Element: resource.Element, Err: fmt.Errorf("%s: %w", resource.Attribute, err)}
}
