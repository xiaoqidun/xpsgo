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
	"compress/flate"
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"hash/crc32"
	"io"
	"maps"
	"slices"
	"strconv"
	"strings"
	"time"
)

const (
	// CompressionOriginal 表示写出时保留原有压缩载荷与方式
	CompressionOriginal Compression = iota
	// CompressionStore 表示写出时采用无压缩直接存储
	CompressionStore
	// CompressionDeflate 表示写出时统一使用Deflate重新压缩
	CompressionDeflate
	// CompressionOptimize 表示写出时尝试无损压缩并在体积更小时采用
	CompressionOptimize
)

// compressionBufferLimit 定义写出压缩候选缓冲的内存上限
const compressionBufferLimit = 8 << 20

// interleaveActiveParts 定义交错写出时同时活跃的逻辑部件并发窗口大小
const interleaveActiveParts = 16

// errCompressionBuffer 表示候选压缩载荷达到内存预算，调用方回退采用原始载荷
var errCompressionBuffer = errors.New("compression buffer limit exceeded")

// Compression 选择保留原压缩数据、直接存储、重新Deflate或无损优化，不改变逻辑部件内容
type Compression uint8

// WriteOptions 设置整包写出压缩方式、字体子集化、交错分片、普通部件顺序及输出字节上限
// 零值保留原压缩数据（内存包沿用导入方法或Deflate），Optimize仅在候选更小时替换，SubsetFonts仅作用于Package写出
// InterleaveBytes非零时按至多8MiB分片并按元数据优先与PartOrder轮转写出，MaxBytes零值沿用包上限
type WriteOptions struct {
	Compression     Compression
	SubsetFonts     bool
	InterleaveBytes int64
	PartOrder       []string
	MaxBytes        int64
}

// packageOutput 记录实际写出的字节并约束输出预算，不接管调用方的Writer生命周期
type packageOutput struct {
	writer  io.Writer
	context context.Context
	limit   int64
	count   int64
}

// compressionBuffer 按需增长候选载荷缓冲，不接收超出预算的部分，供一次写出的条目复用
type compressionBuffer struct {
	bytes.Buffer
	limit int
}

// interleavePart 保存逻辑部件的分片输出状态，输入流仅在开始输出该部件时打开
type interleavePart struct {
	key       string
	header    zip.FileHeader
	remaining uint64
	index     int
	priority  int
	input     *partStream
	done      bool
}

// zipEntryWriter 提供已有ZIP条目写出逻辑需要的两个创建入口
type zipEntryWriter interface {
	CreateHeader(*zip.FileHeader) (io.Writer, error)
	CreateRaw(*zip.FileHeader) (io.Writer, error)
}

// zipMetadataWriter 封装标准库ZIP写出器，在创建与关闭阶段检查含ZIP64扩展的头元数据长度
type zipMetadataWriter struct {
	*zip.Writer
	headers []*zip.FileHeader
	context context.Context
}

// String 返回压缩方式的可读名称
// 返回: string 压缩方式名称
func (c Compression) String() string {
	switch c {
	case CompressionOriginal:
		return "original"
	case CompressionStore:
		return "store"
	case CompressionDeflate:
		return "deflate"
	case CompressionOptimize:
		return "optimize"
	default:
		return "unknown"
	}
}

// DefaultWriteOptions 返回默认整包写出选项
// 返回: WriteOptions 写出选项
func DefaultWriteOptions() WriteOptions {
	return WriteOptions{Compression: CompressionOriginal, MaxBytes: DefaultLimits().MaxPackageBytes}
}

// WriteTo 将已打开文档写入输出流，保留原压缩数据与部件内容，不验证签名且不关闭输出流
// 入参: output 输出流
// 返回: int64 已写字节数, error 校验、读取或写出错误
func (r *Reader) WriteTo(output io.Writer) (int64, error) {
	return r.Write(context.Background(), output, nil)
}

// Write 校验全部物理条目的解压尺寸与CRC后写出整包，默认保留原顺序与未知部件，不验证内容或签名
// 指定InterleaveBytes时重新分片并移除目录条目，按OPC规则重建ZIP64记录，不关闭输出流
// 入参: ctx 取消Context，nil采用Background, output 输出流, options 写出参数，nil采用默认值
// 返回: int64 已写字节数，失败时可能已写入部分容器, error 校验、读取、资源、取消或写出错误
func (r *Reader) Write(ctx context.Context, output io.Writer, options *WriteOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return 0, err
	}
	defer r.mu.RUnlock()
	configuration := WriteOptions{Compression: CompressionOriginal, MaxBytes: r.limits.MaxPackageBytes}
	if options != nil {
		configuration.Compression = options.Compression
		configuration.InterleaveBytes, configuration.PartOrder = options.InterleaveBytes, options.PartOrder
		if options.MaxBytes != 0 {
			configuration.MaxBytes = options.MaxBytes
		}
	}
	if output == nil || configuration.MaxBytes < 1 || configuration.Compression > CompressionOptimize || configuration.InterleaveBytes < 0 || configuration.InterleaveBytes > compressionBufferLimit || configuration.InterleaveBytes == 0 && len(configuration.PartOrder) != 0 {
		return 0, fmt.Errorf("%w: package write parameters", ErrInvalid)
	}
	if err := checkContext(ctx); err != nil {
		return 0, err
	}
	if configuration.InterleaveBytes != 0 {
		return r.writeInterleaved(ctx, output, configuration)
	}
	if r.pkg.data != nil {
		return r.writeMemory(ctx, output, configuration)
	}
	buffer := make([]byte, 32<<10)
	for _, file := range r.pkg.files {
		if _, err := writeEntryHeader(file, configuration.Compression); err != nil {
			return 0, err
		}
		if err := validateWriteEntry(file, buffer, ctx); err != nil {
			return 0, err
		}
	}
	counted := packageOutput{writer: output, context: ctx, limit: configuration.MaxBytes}
	archive := newZIPMetadataWriter(&counted, ctx)
	if err := archive.SetComment(r.pkg.comment); err != nil {
		return 0, err
	}
	var optimizer *flate.Writer
	var candidate compressionBuffer
	if configuration.Compression == CompressionOptimize {
		var err error
		optimizer, err = flate.NewWriter(io.Discard, flate.BestCompression)
		if err != nil {
			return 0, err
		}
		defer optimizer.Close()
	}
	for _, file := range r.pkg.files {
		if err := checkContext(ctx); err != nil {
			return counted.count, err
		}
		if file.FileInfo().IsDir() {
			continue
		}
		var err error
		if configuration.Compression == CompressionOriginal {
			err = copyWriteEntry(archive, file, buffer)
		} else if configuration.Compression == CompressionOptimize {
			err = optimizeWriteEntry(archive, file, buffer, ctx, optimizer, &candidate)
		} else {
			err = rewriteEntry(archive, file, configuration.Compression, buffer, ctx)
		}
		if err != nil {
			return counted.count, err
		}
	}
	if err := archive.Close(); err != nil {
		return counted.count, err
	}
	if err := checkContext(ctx); err != nil {
		return counted.count, err
	}
	return counted.count, nil
}

// writeEntryHeader 保留可传递的条目元数据，移除旧ZIP64字段，重压缩时不追加时间戳或沿用压缩级别标志
// 入参: file 原始条目, compression 输出压缩方式
// 返回: zip.FileHeader 独立条目头, error 扩展字段结构错误
func writeEntryHeader(file *zip.File, compression Compression) (zip.FileHeader, error) {
	header := file.FileHeader
	if err := validateZIPMetadata(len(header.Name), len(header.Extra), len(header.Comment)); err != nil {
		return zip.FileHeader{}, &PartError{Part: file.Name, Err: err}
	}
	header.Extra = nil
	hasTimestamp := false
	for extra := file.Extra; len(extra) != 0; {
		if len(extra) < 4 {
			return zip.FileHeader{}, fmt.Errorf("%w: ZIP entry %s has truncated extra field", ErrInvalid, file.Name)
		}
		length := 4 + int(binary.LittleEndian.Uint16(extra[2:4]))
		if length > len(extra) {
			return zip.FileHeader{}, fmt.Errorf("%w: ZIP entry %s has truncated extra data", ErrInvalid, file.Name)
		}
		tag := binary.LittleEndian.Uint16(extra[:2])
		if tag == 0x5455 {
			hasTimestamp = true
		}
		if tag != 1 {
			header.Extra = append(header.Extra, extra[:length]...)
		}
		extra = extra[length:]
	}
	if compression == CompressionStore || compression == CompressionDeflate {
		header.Modified = time.Time{}
		header.Flags &^= 6
	} else if hasTimestamp {
		header.Modified = time.Time{}
	}
	return header, nil
}

// copyWriteEntry 保留原始压缩载荷，同时使ZIP64记录适应新的容器偏移
// 入参: archive 输出ZIP, file 输入条目, buffer 复用缓冲区
// 返回: error 读取或输出错误
func copyWriteEntry(archive zipEntryWriter, file *zip.File, buffer []byte) error {
	header, err := writeEntryHeader(file, CompressionOriginal)
	if err != nil {
		return err
	}
	input, err := file.OpenRaw()
	if err != nil {
		return err
	}
	output, err := archive.CreateRaw(&header)
	if err != nil {
		return err
	}
	_, err = io.CopyBuffer(output, input, buffer)
	return err
}

// Write 约束一次底层输出，保留短写和原始错误，计数始终反映调用方实际接收的字节
// 入参: data 待写数据
// 返回: int 已接收字节数, error 输出、取消或预算错误
func (w *packageOutput) Write(data []byte) (int, error) {
	if err := checkContext(w.context); err != nil {
		return 0, err
	}
	if int64(len(data)) > w.limit-w.count {
		return 0, fmt.Errorf("%w: package output byte budget", ErrLimit)
	}
	n, err := w.writer.Write(data)
	if n < 0 || n > len(data) {
		return 0, fmt.Errorf("%w: output writer returned invalid byte count", ErrInvalid)
	}
	w.count += int64(n)
	if n < len(data) && err == nil {
		err = io.ErrShortWrite
	}
	return n, err
}

// validateWriteEntry 在任何输出前完整检查物理条目，不依赖曾读取的固定布局页面或中央目录声明尺寸
// 入参: file ZIP条目, buffer 复用缓冲区, ctx 取消Context
// 返回: error 解压、CRC、尺寸或取消错误
func validateWriteEntry(file *zip.File, buffer []byte, ctx context.Context) error {
	reader, err := file.Open()
	if err != nil {
		return fmt.Errorf("%w: ZIP entry %s: %w", ErrInvalid, file.Name, err)
	}
	var count uint64
	for {
		if err := checkContext(ctx); err != nil {
			_ = reader.Close()
			return err
		}
		n, err := reader.Read(buffer)
		if uint64(n) > file.UncompressedSize64-count {
			_ = reader.Close()
			return fmt.Errorf("%w: ZIP entry %s exceeds declared size", ErrInvalid, file.Name)
		}
		count += uint64(n)
		if err != nil {
			closeErr := reader.Close()
			if err != io.EOF {
				return fmt.Errorf("%w: ZIP entry %s: %w", ErrInvalid, file.Name, err)
			}
			if closeErr != nil || count != file.UncompressedSize64 {
				return fmt.Errorf("%w: ZIP entry %s size or close", ErrInvalid, file.Name)
			}
			return nil
		}
		if n == 0 {
			_ = reader.Close()
			return fmt.Errorf("%w: ZIP entry %s: %w", ErrInvalid, file.Name, io.ErrNoProgress)
		}
	}
}

// rewriteEntry 重写单个物理条目的压缩封装，不拼接交错部件或修改内容字节
// 入参: archive 输出ZIP, file 输入条目, compression 压缩方式, buffer 复用缓冲区, ctx 取消Context
// 返回: error 读取、取消或输出错误
func rewriteEntry(archive zipEntryWriter, file *zip.File, compression Compression, buffer []byte, ctx context.Context) error {
	header, err := writeEntryHeader(file, compression)
	if err != nil {
		return err
	}
	header.Method = zip.Store
	if compression == CompressionDeflate {
		header.Method = zip.Deflate
	}
	writer, err := archive.CreateHeader(&header)
	if err != nil {
		return err
	}
	reader, err := file.Open()
	if err != nil {
		return err
	}
	readErr := writeCompressionInput(writer, reader, buffer, ctx)
	closeErr := reader.Close()
	if readErr != nil {
		return readErr
	}
	return closeErr
}

// interleavePriorities 计算交错写出优先级，将流式前置元数据、签名、票据及文档目录部件置于普通部件之前
// 入参: ctx 取消Context
// 返回: map[string]int 优先级, error 部件类型、票据引用或取消错误
func (r *Reader) interleavePriorities(ctx context.Context) (map[string]int, error) {
	priority := map[string]int{strings.ToLower(opcTypesName): 7, "/_rels/.rels": 6}
	discardMedia := fixedContentType("discard-control")
	for key := range r.pkg.parts {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := r.pkg.contentType(r.pkg.names[key])
		if err != nil {
			return nil, err
		}
		lower := strings.ToLower(media)
		if lower == discardMedia {
			priority[key] = max(priority[key], 5)
		} else if slices.Contains([]string{opcSignatureOriginType, opcSignatureType, opcCertificateType}, lower) {
			priority[key] = max(priority[key], 4)
			relKey := strings.ToLower(createdRelationshipPart(r.pkg.names[key]))
			priority[relKey] = max(priority[relKey], 4)
		}
	}
	if rootRels, err := r.pkg.relationships("/"); err == nil {
		if target, err := discardControlTarget(rootRels, r.format); err == nil && target != "" {
			key := strings.ToLower(target)
			priority[key] = max(priority[key], 5)
		}
	}
	seqKey := strings.ToLower(r.sequence)
	priority[seqKey] = max(priority[seqKey], 2)
	seqRelKey := strings.ToLower(createdRelationshipPart(r.sequence))
	priority[seqRelKey] = max(priority[seqRelKey], 2)
	owners := []string{r.sequence}
	for _, document := range r.documents {
		docKey := strings.ToLower(document.Part)
		priority[docKey] = max(priority[docKey], 1)
		docRelKey := strings.ToLower(createdRelationshipPart(document.Part))
		priority[docRelKey] = max(priority[docRelKey], 1)
		owners = append(owners, document.Part)
		for _, page := range document.Pages {
			owners = append(owners, page.Part)
		}
	}
	for _, owner := range owners {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		relations, err := r.pkg.relationships(owner)
		if err != nil {
			return nil, err
		}
		for _, relation := range relations {
			if relation.Type != formatNamespace(r.format)+"/printticket" {
				continue
			}
			if relation.TargetMode == TargetModeExternal {
				return nil, fmt.Errorf("%w: external interleaved PrintTicket", ErrInvalid)
			}
			target, err := resolvePart(owner, relation.Target)
			if err != nil {
				return nil, err
			}
			key := strings.ToLower(target)
			if _, exists := r.pkg.parts[key]; !exists {
				return nil, fmt.Errorf("%w: missing interleaved PrintTicket %s", ErrInvalid, target)
			}
			priority[key] = max(priority[key], 3)
		}
	}
	return priority, nil
}

// Write 将候选载荷写入有界缓冲，超过预算时保持已有数据并拒绝本次写入
// 入参: data 压缩数据
// 返回: int 接收字节数, error 缓冲预算错误
func (b *compressionBuffer) Write(data []byte) (int, error) {
	if len(data) > b.limit-b.Len() {
		return 0, errCompressionBuffer
	}
	if len(data) > b.Available() {
		needed := b.Len() + len(data)
		capacity := b.limit
		if b.Cap() <= b.limit/2 {
			capacity = max(needed, b.Cap()*2)
		}
		buffer := make([]byte, b.Len(), capacity)
		copy(buffer, b.Bytes())
		b.Buffer = *bytes.NewBuffer(buffer)
	}
	return b.Buffer.Write(data)
}

// reset 清空候选长度并更新载荷上限，保留本次写出已分配的缓冲容量
// 入参: limit 本条目的候选字节上限
func (b *compressionBuffer) reset(limit int) {
	b.Buffer.Reset()
	b.limit = limit
}

// optimizeWriteEntry 尝试最佳级别Deflate，仅在压缩载荷更小且未超缓冲上限时替换原载荷
// 入参: archive 输出ZIP, file 输入条目, buffer 读取缓冲区, ctx 取消Context, compressor 本次写出独占的压缩器, candidate 本次写出复用的候选缓冲
// 返回: error 读取、取消或写出错误
func optimizeWriteEntry(archive zipEntryWriter, file *zip.File, buffer []byte, ctx context.Context, compressor *flate.Writer, candidate *compressionBuffer) error {
	limit := compressionBufferLimit
	if file.CompressedSize64 < uint64(limit) {
		limit = int(file.CompressedSize64)
	}
	if limit == 0 {
		return copyWriteEntry(archive, file, buffer)
	}
	candidate.reset(limit)
	compressor.Reset(candidate)
	input, err := file.Open()
	if err != nil {
		_ = compressor.Close()
		return err
	}
	copyErr := writeCompressionInput(compressor, input, buffer, ctx)
	closeInputErr := input.Close()
	closeOutputErr := compressor.Close()
	if closeInputErr != nil {
		return closeInputErr
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	if copyErr != nil && !errors.Is(copyErr, errCompressionBuffer) {
		return copyErr
	}
	if closeOutputErr != nil && !errors.Is(closeOutputErr, errCompressionBuffer) {
		return closeOutputErr
	}
	if copyErr != nil || closeOutputErr != nil || uint64(candidate.Len()) >= file.CompressedSize64 {
		return copyWriteEntry(archive, file, buffer)
	}
	header, err := writeEntryHeader(file, CompressionOriginal)
	if err != nil {
		return err
	}
	header.Method = zip.Deflate
	header.Flags &^= 0xe
	header.ReaderVersion = 20
	header.CreatorVersion = header.CreatorVersion&0xff00 | 20
	header.CompressedSize, header.CompressedSize64 = uint32(candidate.Len()), uint64(candidate.Len())
	output, err := archive.CreateRaw(&header)
	if err != nil {
		return err
	}
	_, err = io.CopyBuffer(output, bytes.NewReader(candidate.Bytes()), buffer)
	return err
}

// writeCompressionInput 逐块读取部件并检查取消，不让压缩器接管输入或输出的生命周期
// 入参: output 压缩器, input 部件流, buffer 复用缓冲区, ctx 取消Context
// 返回: error 读取、短写、取消或压缩错误
func writeCompressionInput(output io.Writer, input io.Reader, buffer []byte, ctx context.Context) error {
	for {
		if err := checkContext(ctx); err != nil {
			return err
		}
		n, readErr := input.Read(buffer)
		if n != 0 {
			written, err := output.Write(buffer[:n])
			if err != nil {
				return err
			}
			if written != n {
				return io.ErrShortWrite
			}
		}
		if readErr != nil {
			if readErr == io.EOF {
				return nil
			}
			return readErr
		}
		if n == 0 {
			return io.ErrNoProgress
		}
	}
}

// writeInterleaved 校验输入与分片计划后按有界窗口交错写出分片，复用首条目元数据与首片增长提示
// 入参: ctx 取消Context, output 输出流, options 已校验分片参数
// 返回: int64 实际写出字节数, error 输入、计划、压缩、取消或输出错误
func (r *Reader) writeInterleaved(ctx context.Context, output io.Writer, options WriteOptions) (int64, error) {
	plan, err := r.interleavePlan(ctx, options)
	if err != nil {
		return 0, err
	}
	buffer := make([]byte, 32<<10)
	for _, file := range r.pkg.files {
		if _, err := writeEntryHeader(file, CompressionDeflate); err != nil {
			return 0, err
		}
		if err := validateWriteEntry(file, buffer, ctx); err != nil {
			return 0, err
		}
	}
	var maximum uint64
	for _, part := range plan {
		maximum = max(maximum, min(uint64(options.InterleaveBytes), part.remaining))
	}
	payload := make([]byte, int(maximum))
	counted := packageOutput{writer: output, context: ctx, limit: options.MaxBytes}
	archive := newZIPMetadataWriter(&counted, ctx)
	if err := archive.SetComment(r.pkg.comment); err != nil {
		return 0, err
	}
	var compressor *flate.Writer
	if options.Compression == CompressionOptimize {
		compressor, err = flate.NewWriter(io.Discard, flate.BestCompression)
		if err != nil {
			return 0, err
		}
		defer compressor.Close()
	}
	defer func() {
		for _, part := range plan {
			if part.input != nil {
				_ = part.input.Close()
			}
		}
	}()
	var candidate compressionBuffer
	for start := 0; start < len(plan); {
		end := min(len(plan), start+interleaveActiveParts)
		if plan[start].priority != 0 {
			end = start + 1
		}
		remaining := end - start
		for remaining > 0 {
			for _, part := range plan[start:end] {
				if part.done {
					continue
				}
				if err := checkContext(ctx); err != nil {
					return counted.count, err
				}
				if part.input == nil {
					part.input, err = r.pkg.openPartStream(ctx, part.key, PartReadOptions{MaxBytes: r.limits.MaxPartBytes})
					if err != nil {
						return counted.count, err
					}
				}
				count := int(min(uint64(options.InterleaveBytes), part.remaining))
				if _, err := io.ReadFull(part.input, payload[:count]); err != nil {
					return counted.count, err
				}
				part.remaining -= uint64(count)
				last := part.remaining == 0
				if last {
					var extra [1]byte
					if n, err := part.input.Read(extra[:]); n != 0 || err != io.EOF {
						if err != nil && err != io.EOF {
							return counted.count, err
						}
						return counted.count, &PartError{Part: r.pkg.names[part.key], Err: fmt.Errorf("%w: interleaved source ending", ErrInvalid)}
					}
					if err := part.input.Close(); err != nil {
						return counted.count, err
					}
					part.input = nil
				}
				if err := writeInterleavePiece(ctx, archive, part, last, payload[:count], options, compressor, &candidate, buffer); err != nil {
					return counted.count, err
				}
				part.index++
				if last {
					part.done = true
					remaining--
				}
			}
		}
		start = end
	}
	if err := archive.Close(); err != nil {
		return counted.count, err
	}
	return counted.count, checkContext(ctx)
}

// interleavePlan 检查完整输出分片数及名称，再安排元数据优先级和调用方指定的普通部件顺序
// 入参: ctx 取消Context, options 分片大小及部件顺序参数
// 返回: []*interleavePart 独立输出状态, error 部件、名称、数量或取消错误
func (r *Reader) interleavePlan(ctx context.Context, options WriteOptions) ([]*interleavePart, error) {
	priority, err := r.interleavePriorities(ctx)
	if err != nil {
		return nil, err
	}
	if len(options.PartOrder) > r.limits.MaxPartCount {
		return nil, fmt.Errorf("%w: interleaved part order count", ErrLimit)
	}
	order := make(map[string]int)
	for index, name := range options.PartOrder {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		part, err := opcPartName(name)
		if err != nil {
			return nil, err
		}
		key := strings.ToLower(part)
		if _, exists := r.pkg.parts[key]; !exists {
			return nil, fmt.Errorf("%w: interleaved order part %s missing", ErrInvalid, part)
		}
		if _, duplicate := order[key]; duplicate {
			return nil, fmt.Errorf("%w: interleaved order part %s repeated", ErrInvalid, part)
		}
		order[key] = index
	}
	var plan []*interleavePart
	var entries uint64
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		size, err := r.pkg.partSize(key)
		if err != nil {
			return nil, err
		}
		limit := min(r.limits.MaxPartBytes, r.limits.MaxPackageBytes)
		if opcRelationshipName(r.pkg.names[key]) || key == strings.ToLower(opcTypesName) {
			limit = min(limit, r.limits.MaxMetadataBytes)
		}
		if size > uint64(limit) {
			return nil, &PartError{Part: r.pkg.names[key], Err: fmt.Errorf("%w: interleaved logical part bytes", ErrLimit)}
		}
		count := uint64(1)
		if size != 0 {
			count += (size - 1) / uint64(options.InterleaveBytes)
		}
		if count > uint64(r.limits.MaxPartCount)-entries {
			return nil, fmt.Errorf("%w: interleaved ZIP entry count", ErrLimit)
		}
		entries += count
		var first zip.FileHeader
		if r.pkg.data != nil {
			first = r.pkg.memoryItems(key)[0].header
		} else {
			first = r.pkg.parts[key][0].FileHeader
		}
		header, err := writeEntryHeader(&zip.File{FileHeader: first}, CompressionDeflate)
		if err != nil {
			return nil, err
		}
		header.Name = strings.TrimPrefix(r.pkg.names[key], "/")
		part := &interleavePart{key: key, header: header, remaining: size, priority: priority[key]}
		last := interleavePieceHeader(part, int(count-1), true)
		firstPiece := interleavePieceHeader(part, 0, count == 1)
		if err := validateZIPMetadata(len(firstPiece.Name), len(firstPiece.Extra), len(firstPiece.Comment)); err != nil {
			return nil, err
		}
		if err := validateZIPMetadata(len(last.Name), len(last.Extra), len(last.Comment)); err != nil {
			return nil, err
		}
		plan = append(plan, part)
	}
	slices.SortStableFunc(plan, func(a, b *interleavePart) int {
		if a.priority != b.priority {
			return b.priority - a.priority
		}
		left, first := order[a.key]
		right, second := order[b.key]
		if first != second {
			if first {
				return -1
			}
			return 1
		}
		if first && left != right {
			return left - right
		}
		return strings.Compare(a.key, b.key)
	})
	return plan, checkContext(ctx)
}

// interleavePieceHeader 为新分片构造名称，增长提示只保留在首片，不沿用旧尺寸和压缩标志
// 入参: part 部件状态, index 分片编号, last 是否末片
// 返回: zip.FileHeader 独立分片头
func interleavePieceHeader(part *interleavePart, index int, last bool) zip.FileHeader {
	header := part.header
	header.Name += "/[" + strconv.Itoa(index) + "]"
	if last {
		header.Name += ".last"
	}
	header.Name += ".piece"
	if index != 0 {
		header.Extra = nil
		for extra := part.header.Extra; len(extra) != 0; {
			size := int(binary.LittleEndian.Uint16(extra[2:4])) + 4
			if binary.LittleEndian.Uint16(extra) != 0xa220 {
				header.Extra = append(header.Extra, extra[:size]...)
			}
			extra = extra[size:]
		}
	}
	header.Flags &^= 0xe
	header.ReaderVersion = 20
	header.CreatorVersion = header.CreatorVersion&0xff00 | 20
	header.CompressedSize, header.UncompressedSize = 0, 0
	header.CompressedSize64, header.UncompressedSize64, header.CRC32 = 0, 0, 0
	return header
}

// writeInterleavePiece 写出单个独立CRC分片，优化仅比较该片Deflate候选与直接存储
// 入参: ctx 取消Context, archive 输出ZIP, part 部件状态, last 是否末片, data 分片字节, options 压缩参数, compressor 复用压缩器, candidate 复用候选, buffer 输出缓冲
// 返回: error 压缩、取消或输出错误
func writeInterleavePiece(ctx context.Context, archive zipEntryWriter, part *interleavePart, last bool, data []byte, options WriteOptions, compressor *flate.Writer, candidate *compressionBuffer, buffer []byte) error {
	header := interleavePieceHeader(part, part.index, last)
	if options.Compression == CompressionStore {
		header.Method = zip.Store
	} else if options.Compression == CompressionDeflate {
		header.Method = zip.Deflate
	}
	if options.Compression != CompressionOptimize {
		if header.Method == zip.Store {
			header.CRC32 = crc32.ChecksumIEEE(data)
			header.CompressedSize64, header.UncompressedSize64 = uint64(len(data)), uint64(len(data))
			header.CompressedSize, header.UncompressedSize = uint32(len(data)), uint32(len(data))
			writer, err := archive.CreateRaw(&header)
			if err != nil {
				return err
			}
			return writeCompressionInput(writer, bytes.NewReader(data), buffer, ctx)
		}
		writer, err := archive.CreateHeader(&header)
		if err != nil {
			return err
		}
		return writeCompressionInput(writer, bytes.NewReader(data), buffer, ctx)
	}
	candidate.reset(len(data))
	compressor.Reset(candidate)
	copyErr := writeCompressionInput(compressor, bytes.NewReader(data), buffer, ctx)
	closeErr := compressor.Close()
	if err := checkContext(ctx); err != nil {
		return err
	}
	if copyErr != nil && !errors.Is(copyErr, errCompressionBuffer) {
		return copyErr
	}
	if closeErr != nil && !errors.Is(closeErr, errCompressionBuffer) {
		return closeErr
	}
	header.Method = zip.Store
	payload := data
	if copyErr == nil && closeErr == nil && candidate.Len() < len(data) {
		header.Method = zip.Deflate
		payload = candidate.Bytes()
	}
	header.CRC32 = crc32.ChecksumIEEE(data)
	header.UncompressedSize, header.UncompressedSize64 = uint32(len(data)), uint64(len(data))
	header.CompressedSize, header.CompressedSize64 = uint32(len(payload)), uint64(len(payload))
	writer, err := archive.CreateRaw(&header)
	if err != nil {
		return err
	}
	return writeCompressionInput(writer, bytes.NewReader(payload), buffer, ctx)
}

// writeMemory 写出内存包，保留未修改条目的元数据与分片，Original沿用导入压缩方法且新条目采用Deflate
// 入参: ctx 取消Context, output 输出流, options 已校验的写出选项
// 返回: int64 实际写出字节数, error 取消、压缩或输出错误
func (r *Reader) writeMemory(ctx context.Context, output io.Writer, options WriteOptions) (int64, error) {
	keys := make([]string, 0, len(r.pkg.data))
	for key := range r.pkg.data {
		keys = append(keys, key)
	}
	slices.Sort(keys)
	type memoryWriteItem struct {
		key    string
		header zip.FileHeader
		start  int
		end    int
	}
	planned := make([]memoryWriteItem, 0, len(keys))
	count := 0
	for _, key := range keys {
		if err := checkContext(ctx); err != nil {
			return 0, err
		}
		items := r.pkg.memoryItems(key)
		if len(items) > r.limits.MaxPartCount-count {
			return 0, fmt.Errorf("%w: output ZIP entry count", ErrLimit)
		}
		count += len(items)
		for _, item := range items {
			header, err := writeEntryHeader(&zip.File{FileHeader: item.header}, options.Compression)
			if err != nil {
				return 0, err
			}
			planned = append(planned, memoryWriteItem{key: key, header: header, start: item.start, end: item.end})
		}
	}
	counted := packageOutput{writer: output, context: ctx, limit: options.MaxBytes}
	archive := newZIPMetadataWriter(&counted, ctx)
	if err := archive.SetComment(r.pkg.comment); err != nil {
		return 0, err
	}
	buffer := make([]byte, 32<<10)
	var optimizer *flate.Writer
	var candidate compressionBuffer
	if options.Compression == CompressionOptimize {
		var err error
		optimizer, err = flate.NewWriter(io.Discard, flate.BestCompression)
		if err != nil {
			return 0, err
		}
		defer optimizer.Close()
	}
	for _, item := range planned {
		if err := checkContext(ctx); err != nil {
			return counted.count, err
		}
		data := r.pkg.data[item.key][item.start:item.end]
		header := item.header
		if options.Compression == CompressionStore {
			header.Method = zip.Store
		} else if options.Compression == CompressionDeflate {
			header.Method = zip.Deflate
		}
		if options.Compression == CompressionOptimize {
			limit := min(len(data), compressionBufferLimit)
			candidate.reset(limit)
			optimizer.Reset(&candidate)
			copyErr := writeCompressionInput(optimizer, bytes.NewReader(data), buffer, ctx)
			closeErr := optimizer.Close()
			if err := checkContext(ctx); err != nil {
				return counted.count, err
			}
			if copyErr != nil && !errors.Is(copyErr, errCompressionBuffer) {
				return counted.count, copyErr
			}
			if closeErr != nil && !errors.Is(closeErr, errCompressionBuffer) {
				return counted.count, closeErr
			}
			header.Method = zip.Store
			checksum := crc32.NewIEEE()
			for start := 0; start < len(data); start += len(buffer) {
				if err := checkContext(ctx); err != nil {
					return counted.count, err
				}
				_, _ = checksum.Write(data[start:min(start+len(buffer), len(data))])
			}
			header.CRC32 = checksum.Sum32()
			header.UncompressedSize64 = uint64(len(data))
			payload := data
			if copyErr == nil && closeErr == nil && candidate.Len() < len(data) {
				header.Method = zip.Deflate
				payload = candidate.Bytes()
			}
			header.CompressedSize64 = uint64(len(payload))
			header.Flags &^= 0xe
			header.ReaderVersion, header.CreatorVersion = 20, header.CreatorVersion&0xff00|20
			writer, err := archive.CreateRaw(&header)
			if err != nil {
				return counted.count, err
			}
			if err := writeCompressionInput(writer, bytes.NewReader(payload), buffer, ctx); err != nil {
				return counted.count, err
			}
			continue
		}
		writer, err := archive.CreateHeader(&header)
		if err != nil {
			return counted.count, err
		}
		if err := writeCompressionInput(writer, bytes.NewReader(data), buffer, ctx); err != nil {
			return counted.count, err
		}
	}
	if err := archive.Close(); err != nil {
		return counted.count, err
	}
	return counted.count, checkContext(ctx)
}

// memoryItems 为未修改部件沿用原物理条目，修改后的部件以完整条目写出
// 入参: key 内存部件索引
// 返回: []packageItem 输出条目及数据范围
func (p *packageReader) memoryItems(key string) []packageItem {
	data := p.data[key]
	old, exists := p.original[key]
	if exists && old.name == p.names[key] && len(old.items) != 0 && bytes.Equal(old.data, data) {
		return old.items
	}
	header := zip.FileHeader{Name: strings.TrimPrefix(p.names[key], "/"), Method: zip.Deflate}
	if exists && len(old.items) == 1 {
		header = old.items[0].header
		header.Name = strings.TrimPrefix(p.names[key], "/")
	}
	return []packageItem{{header: header, end: len(data)}}
}

// newZIPMetadataWriter 为包输出建立元数据校验入口，不接管输出流生命周期
// 入参: output 输出流, ctx 取消Context
// 返回: *zipMetadataWriter 使用标准库压缩和目录生成的写出器
func newZIPMetadataWriter(output io.Writer, ctx context.Context) *zipMetadataWriter {
	return &zipMetadataWriter{Writer: zip.NewWriter(output), context: ctx}
}

// CreateHeader 检查自动时间戳所占字节，再保留标准库实际创建的头供最终检查
// 入参: header 标准库接管的条目头，调用后不得修改
// 返回: io.Writer 未压缩载荷入口, error 元数据、取消或标准库错误
func (w *zipMetadataWriter) CreateHeader(header *zip.FileHeader) (io.Writer, error) {
	if err := checkContext(w.context); err != nil {
		return nil, err
	}
	extra := len(header.Extra)
	if !header.Modified.IsZero() {
		extra += 9
	}
	if err := validateZIPMetadata(len(header.Name), extra, len(header.Comment)); err != nil {
		return nil, err
	}
	output, err := w.Writer.CreateHeader(header)
	if err != nil {
		return nil, err
	}
	if err := validateZIPMetadata(len(header.Name), len(header.Extra), len(header.Comment)); err != nil {
		return nil, err
	}
	w.headers = append(w.headers, header)
	return output, nil
}

// CreateRaw 检查已知尺寸触发的本地和中央ZIP64字段，偏移扩展在关闭后按实际头检查
// 入参: header 标准库接管的条目头，调用后不得修改
// 返回: io.Writer 原始压缩载荷入口, error 元数据、取消或标准库错误
func (w *zipMetadataWriter) CreateRaw(header *zip.FileHeader) (io.Writer, error) {
	if err := checkContext(w.context); err != nil {
		return nil, err
	}
	extra := len(header.Extra)
	if header.Flags&8 == 0 && (header.CompressedSize64 >= 1<<32-1 || header.UncompressedSize64 >= 1<<32-1) {
		extra += 20
	}
	if err := validateZIPMetadata(len(header.Name), extra, 0); err != nil {
		return nil, err
	}
	extra = len(header.Extra)
	for _, size := range [...]uint64{header.UncompressedSize64, header.CompressedSize64} {
		if size >= 1<<32-1 {
			if extra == len(header.Extra) {
				extra += 4
			}
			extra += 8
		}
	}
	if err := validateZIPMetadata(len(header.Name), extra, len(header.Comment)); err != nil {
		return nil, err
	}
	output, err := w.Writer.CreateRaw(header)
	if err != nil {
		return nil, err
	}
	w.headers = append(w.headers, header)
	return output, nil
}

// Close 完成标准库目录写出并复核最终条目头元数据长度，越界时返回错误
// 返回: error 标准库、取消或最终元数据长度错误
func (w *zipMetadataWriter) Close() error {
	if err := checkContext(w.context); err != nil {
		return err
	}
	if err := w.Writer.Close(); err != nil {
		return err
	}
	for _, header := range w.headers {
		if err := checkContext(w.context); err != nil {
			return err
		}
		if err := validateZIPMetadata(len(header.Name), len(header.Extra), len(header.Comment)); err != nil {
			return err
		}
	}
	return checkContext(w.context)
}
