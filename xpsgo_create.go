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
	"crypto/rand"
	"encoding/binary"
	"encoding/xml"
	"fmt"
	"image/color"
	"io"
	"maps"
	"math"
	"mime"
	"net/url"
	"os"
	"slices"
	"strconv"
	"strings"
	"sync"
)

// createdNavigationOther 等常量表示固定布局部件的导航地址角色
const (
	createdNavigationOther createdNavigationKind = iota
	createdNavigationSequence
	createdNavigationDocument
	createdNavigationPage
)

// PackageOptions 设置可编辑包的资源上限，零值字段采用默认值
// MaxImagePixels按RGBA64等价存储容量计费，不只计算图像宽度与高度的乘积
type PackageOptions struct {
	Limits         Limits
	MaxImagePixels uint64
}

// Package 持有独立的文档、页面和资源数据，修改成功后才更新状态，支持并发读取及串行修改
type Package struct {
	mu             sync.RWMutex
	format         Format
	limits         Limits
	sequence       string
	documents      []Document
	pageCount      int
	parts          map[string]packagePart
	relations      map[string][]Relationship
	relationSizes  map[string]int64
	total          int64
	maxImagePixels uint64
	names          map[string]bool
	layout         map[string]bool
	parents        map[string]int
	allocated      map[string]int
	original       map[string]packagePart
	originalRels   map[string][]Relationship
	comment        string
	dirty          map[string]bool
	dirtyRels      map[string]bool
	deleted        map[string]bool
	protected      map[string]bool
}

// packagePart 保存不可修改的部件数据，来源参数在写入模型时复制
type packagePart struct {
	name  string
	media string
	data  []byte
	items []packageItem
}

// packageItem 保存原物理条目头和对应逻辑数据范围，不持有输入流
type packageItem struct {
	header zip.FileHeader
	start  int
	end    int
}

// createdNavigationKind 表示固定布局部件的导航地址角色
type createdNavigationKind uint8

// createdNavigation 保存当前固定布局的部件角色，供写出前检查内部链接地址
type createdNavigation struct {
	parts map[string]createdNavigationKind
}

// createdStoryGraph 保存单次关联校验的预算和私有索引，共享部件按各引用位置绑定
type createdStoryGraph struct {
	context    context.Context
	reader     *Reader
	backend    *packageReader
	remaining  int64
	work       int
	relations  map[string][]Relationship
	structures map[string]*DocumentStructure
	fragments  map[string]*StoryFragments
	names      map[string]map[string]bool
}

// DefaultPackageOptions 返回可编辑包的默认资源上限配置
// 返回: PackageOptions 包资源选项
func DefaultPackageOptions() PackageOptions {
	return PackageOptions{Limits: DefaultLimits(), MaxImagePixels: DefaultImageOptions().MaxPixels}
}

// NewPackage 创建空的可编辑包，方言未指定时采用OpenXPS，写出前必须具有文档和页面
// 入参: format 文档方言, options 资源选项，nil采用默认值
// 返回: *Package 可编辑包, error 方言或资源上限错误
func NewPackage(format Format, options *PackageOptions) (*Package, error) {
	if format == FormatUnknown {
		format = FormatOpenXPS
	}
	if formatNamespace(format) == "" {
		return nil, fmt.Errorf("%w: invalid package format", ErrInvalid)
	}
	defaults := DefaultPackageOptions()
	limits := defaults.Limits
	maxPixels := defaults.MaxImagePixels
	if options != nil {
		limits = mergeLimits(limits, options.Limits)
		if options.MaxImagePixels != 0 {
			maxPixels = options.MaxImagePixels
		}
	}
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	p := &Package{format: format, limits: limits, maxImagePixels: maxPixels, sequence: "/FixedDocSeq.fdseq", parts: make(map[string]packagePart), relations: make(map[string][]Relationship), relationSizes: make(map[string]int64), names: make(map[string]bool), layout: make(map[string]bool), parents: make(map[string]int), allocated: make(map[string]int), dirty: make(map[string]bool), dirtyRels: make(map[string]bool), protected: make(map[string]bool)}
	p.registerName(p.sequence)
	p.layout[strings.ToLower(p.sequence)] = true
	p.registerName("/_rels/.rels")
	return p, nil
}

// Format 返回可编辑包的方言
// 返回: Format 文档方言
func (p *Package) Format() Format {
	if p == nil {
		return FormatUnknown
	}
	return p.format
}

// DocumentCount 返回当前文档数量
// 返回: int 文档数量
func (p *Package) DocumentCount() int {
	if p == nil {
		return 0
	}
	p.mu.RLock()
	defer p.mu.RUnlock()
	return len(p.documents)
}

// PageCount 返回当前页面总数
// 返回: int 页面数量
func (p *Package) PageCount() int {
	if p == nil {
		return 0
	}
	p.mu.RLock()
	defer p.mu.RUnlock()
	return p.pageCount
}

// Document 返回独立的文档和页面索引
// 入参: docIndex 从零开始的文档序号
// 返回: Document 索引副本, error 序号错误
func (p *Package) Document(docIndex int) (Document, error) {
	if err := p.lock(); err != nil {
		return Document{}, err
	}
	defer p.mu.Unlock()
	if docIndex < 0 || docIndex >= len(p.documents) {
		return Document{}, fmt.Errorf("%w: document index", ErrInvalid)
	}
	value := p.documents[docIndex]
	value.Pages = slices.Clone(value.Pages)
	for index := range value.Pages {
		value.Pages[index].LinkTargets = slices.Clone(value.Pages[index].LinkTargets)
	}
	return value, nil
}

// AddDocument 新增固定文档，部件名为空时分配标准目录中的唯一名称，不创建空白页面
// 入参: part 文档部件URI，空值自动分配
// 返回: int 新文档序号, error 名称冲突或资源错误
func (p *Package) AddDocument(part string) (int, error) {
	if err := p.lock(); err != nil {
		return 0, err
	}
	defer p.mu.Unlock()
	return p.addDocumentLocked(part)
}

// addDocumentLocked 在调用方持有包写锁时新增固定文档
// 入参: part 文档部件URI，空值自动分配
// 返回: int 新文档序号, error 名称冲突、编辑许可或资源错误
func (p *Package) addDocumentLocked(part string) (int, error) {
	pattern := ""
	if part == "" {
		pattern = "/Documents/%d/FixedDoc.fdoc"
		var err error
		part, err = p.newName(pattern, nil)
		if err != nil {
			return 0, err
		}
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return 0, err
	}
	if err := p.available(canonical); err != nil {
		return 0, err
	}
	if err := p.editable(canonical, p.sequence); err != nil {
		return 0, err
	}
	if len(p.names) >= p.limits.MaxPartCount-1 {
		return 0, fmt.Errorf("%w: package part count", ErrLimit)
	}
	p.documents = append(p.documents, Document{Part: canonical})
	p.registerName(canonical)
	p.layout[strings.ToLower(canonical)] = true
	p.dirty[strings.ToLower(p.sequence)] = true
	p.commitName(pattern, canonical)
	return len(p.documents) - 1, nil
}

// AddPage 将类型化页面加入默认首文档，包尚无文档时自动创建首文档并在失败时回滚
// 入参: ctx 取消Context，nil采用Background, page 页面模型，Part为空时自动分配
// 返回: int 新页面在首文档内的序号, error 模型、名称、编码、取消或资源错误
func (p *Package) AddPage(ctx context.Context, page *Page) (int, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return 0, err
	}
	defer p.mu.Unlock()
	if err := checkContext(ctx); err != nil {
		return 0, err
	}
	if page == nil {
		return 0, fmt.Errorf("%w: document index or page", ErrInvalid)
	}
	if len(p.documents) != 0 {
		return p.addPageLocked(ctx, 0, page)
	}
	q := p.storyCopy()
	if _, err := q.addDocumentLocked(""); err != nil {
		return 0, err
	}
	index, err := q.addPageLocked(ctx, 0, page)
	if err != nil {
		return 0, err
	}
	p.commitStory(q)
	return index, nil
}

// AddPageTo 将类型化页面编码后加入指定文档，不修改调用方模型，资源可在写出前补齐
// 入参: ctx 取消Context，nil采用Background, docIndex 文档序号, page 页面模型，Part为空时自动分配
// 返回: int 新页面在文档内的序号, error 模型、名称、编码、取消或资源错误
func (p *Package) AddPageTo(ctx context.Context, docIndex int, page *Page) (int, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return 0, err
	}
	defer p.mu.Unlock()
	return p.addPageLocked(ctx, docIndex, page)
}

// addPageLocked 在调用方持有包写锁时编码并将页面加入指定文档
// 入参: ctx 取消Context, docIndex 文档序号, page 页面模型
// 返回: int 新页面在文档内的序号, error 模型、名称、编码、取消或资源错误
func (p *Package) addPageLocked(ctx context.Context, docIndex int, page *Page) (int, error) {
	if err := checkContext(ctx); err != nil {
		return 0, err
	}
	if docIndex < 0 || docIndex >= len(p.documents) || page == nil {
		return 0, fmt.Errorf("%w: document index or page", ErrInvalid)
	}
	if err := p.editable(p.documents[docIndex].Part); err != nil {
		return 0, err
	}
	if p.pageCount >= p.limits.MaxPageCount {
		return 0, fmt.Errorf("%w: page count", ErrLimit)
	}
	value := *page
	pattern := ""
	if value.Part == "" {
		base := p.documents[docIndex].Part
		base = base[:strings.LastIndexByte(base, '/')+1]
		pattern = base + "Pages/%d.fpage"
		var err error
		value.Part, err = p.newName(pattern, ctx)
		if err != nil {
			return 0, err
		}
	}
	part, err := opcPartName(value.Part)
	if err != nil {
		return 0, err
	}
	if err := p.available(part); err != nil {
		return 0, err
	}
	if err := p.editable(part); err != nil {
		return 0, err
	}
	value.Part = part
	targets, err := p.storePage(&value, ctx)
	if err != nil {
		return 0, err
	}
	p.layout[strings.ToLower(part)] = true
	p.documents[docIndex].Pages = append(p.documents[docIndex].Pages, PageReference{Part: part, LinkTargets: targets})
	p.pageCount++
	p.dirty[strings.ToLower(p.documents[docIndex].Part)] = true
	p.commitName(pattern, part)
	return len(p.documents[docIndex].Pages) - 1, nil
}

// AddFont 校验字体嵌入许可后按唯一GUID路径混淆存入包中，禁止嵌入的字体返回ErrRestricted
// 入参: data 原始OpenType或TrueType字体字节
// 返回: string 混淆字体的包根URI, error 字体格式、许可、名称或资源错误
func (p *Package) AddFont(data []byte) (string, error) {
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty font data", ErrInvalid)
	}
	if int64(len(data)) > p.limits.MaxPartBytes {
		return "", fmt.Errorf("%w: font byte budget", ErrLimit)
	}
	face, err := parseFontFace(data, 0)
	if err != nil {
		return "", err
	}
	count := uint32(1)
	if face.collection {
		count = binary.BigEndian.Uint32(data[8:12])
	}
	checked := make(map[uint32]bool)
	for index := uint32(0); index < count; index++ {
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return "", err
			}
		}
		if checked[face.offset] {
			continue
		}
		os2, err := parseFontOS2Metrics(face)
		if err != nil {
			return "", err
		}
		if os2 == nil {
			return "", fmt.Errorf("%w: producer font needs OS/2", ErrInvalid)
		}
		rights, err := fontEmbeddingRights(os2)
		if err != nil {
			return "", err
		}
		if rights&2 != 0 {
			return "", fmt.Errorf("%w: font prohibits embedding", ErrRestricted)
		}
		checked[face.offset] = true
	}
	part, err := p.newFontPart()
	if err != nil {
		return "", err
	}
	obfuscated, err := ObfuscateFont(part, data)
	if err != nil {
		return "", err
	}
	if err := p.editable(part); err != nil {
		return "", err
	}
	if err := p.storePart(part, "application/vnd.ms-package.obfuscated-opentype", obfuscated, false); err != nil {
		return "", err
	}
	return part, nil
}

// newFontPart 生成包内不冲突的UUIDv4混淆字体部件路径
// 返回: string 规范化字体部件URI, error 随机数或冲突错误
func (p *Package) newFontPart() (string, error) {
	var raw [16]byte
	for range 1024 {
		if _, err := rand.Read(raw[:]); err != nil {
			return "", err
		}
		raw[6] = raw[6]&0x0f | 0x40
		raw[8] = raw[8]&0x3f | 0x80
		part := fmt.Sprintf("/Resources/Fonts/%X-%X-%X-%X-%X.odttf", raw[0:4], raw[4:6], raw[6:8], raw[8:10], raw[10:16])
		if p.available(part) == nil {
			return part, nil
		}
	}
	return "", fmt.Errorf("%w: unable to allocate unique font part", ErrLimit)
}

// AddImage 按魔数识别PNG、JPEG、TIFF或JPEG XR图像并分配唯一路径存入包中
// 入参: data 原始图像字节
// 返回: string 图像部件的包根URI, error 格式、预算或名称冲突错误
func (p *Package) AddImage(data []byte) (string, error) {
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty image data", ErrInvalid)
	}
	media, ext, err := detectImageFormat(data)
	if err != nil {
		return "", err
	}
	pattern := "/Resources/Images/%d." + ext
	part, err := p.newName(pattern, nil)
	if err != nil {
		return "", err
	}
	if err := p.editable(part); err != nil {
		return "", err
	}
	if err := p.storePart(part, media, data, false); err != nil {
		return "", err
	}
	p.commitName(pattern, part)
	return part, nil
}

// AddColorProfile 校验ICC颜色配置文件并分配唯一路径存入包中
// 入参: data 原始ICC颜色配置文件字节
// 返回: string 配置文件部件的包根URI, error 格式、预算或名称冲突错误
func (p *Package) AddColorProfile(data []byte) (string, error) {
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	if len(data) == 0 {
		return "", fmt.Errorf("%w: empty color profile data", ErrInvalid)
	}
	if int64(len(data)) > p.limits.MaxPartBytes {
		return "", fmt.Errorf("%w: color profile byte budget", ErrLimit)
	}
	if _, err := validateCreatedICCProfile(data, nil); err != nil {
		return "", err
	}
	pattern := "/Resources/Profiles/%d.icc"
	part, err := p.newName(pattern, nil)
	if err != nil {
		return "", err
	}
	if err := p.editable(part); err != nil {
		return "", err
	}
	if err := p.storePart(part, "application/vnd.ms-color.iccprofile", data, false); err != nil {
		return "", err
	}
	p.commitName(pattern, part)
	return part, nil
}

// detectImageFormat 根据文件头魔数识别XPS支持的栅格图像媒体类型与扩展名
// 入参: data 图像原始字节
// 返回: string 媒体类型, string 扩展名, error 不支持的图像格式错误
func detectImageFormat(data []byte) (string, string, error) {
	if len(data) >= 8 && bytes.Equal(data[:8], []byte{0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n'}) {
		return "image/png", "png", nil
	}
	if len(data) >= 3 && data[0] == 0xff && data[1] == 0xd8 && data[2] == 0xff {
		return "image/jpeg", "jpg", nil
	}
	if len(data) >= 4 && data[0] == 'I' && data[1] == 'I' && data[2] == 0xbc && data[3] == 0x01 {
		return "image/vnd.ms-photo", "jxr", nil
	}
	if len(data) >= 4 && (data[0] == 'I' && data[1] == 'I' && data[2] == 0x2a && data[3] == 0x00 || data[0] == 'M' && data[1] == 'M' && data[2] == 0x00 && data[3] == 0x2a) {
		return "image/tiff", "tif", nil
	}
	return "", "", fmt.Errorf("%w: unsupported image format", ErrUnsupported)
}

// SetPart 新增或替换资源及扩展部件，名称与数据独立保存，不允许覆盖受文档模型管理的部件
// 入参: part 部件URI, media 内容类型, data 部件内容
// 返回: error 名称、媒体类型、冲突或预算错误
func (p *Package) SetPart(part, media string, data []byte) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return err
	}
	if p.managed(canonical) || opcRelationshipName(canonical) {
		return fmt.Errorf("%w: managed package part", ErrInvalid)
	}
	if err := p.editable(canonical); err != nil {
		return err
	}
	if err := p.store(canonical, media, data); err != nil {
		return err
	}
	delete(p.deleted, strings.ToLower(canonical))
	return nil
}

// ReadPart 返回已经存入模型的页面、资源或扩展部件副本，生成的索引与关系通过Reader读取
// 入参: part 部件URI
// 返回: []byte 独立数据, error 名称或部件不存在错误
func (p *Package) ReadPart(part string) ([]byte, error) {
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return nil, err
	}
	value, exists := p.parts[strings.ToLower(canonical)]
	if !exists {
		return nil, fmt.Errorf("%w: missing package part %s", ErrInvalid, canonical)
	}
	return bytes.Clone(value.data), nil
}

// Reader 生成独立只读快照并校验固定布局与资源关系，不压缩生成中间ZIP，不接管原模型生命周期
// 入参: ctx 取消Context，nil采用Background
// 返回: *Reader 独立快照, error 标准结构、资源或取消错误
func (p *Package) Reader(ctx context.Context) (*Reader, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := p.lock(); err != nil {
		return nil, err
	}
	snapshot := p.snapshot()
	p.mu.Unlock()
	return snapshot.reader(ctx)
}

// Write 校验完整只读快照后写出包，启用SubsetFonts时仅对临时副本子集化而不修改原包
// 入参: ctx 取消Context，nil采用Background, output 输出流, options 写出选项，nil采用默认值
// 返回: int64 已写字节数, error 校验、子集化、取消、压缩或输出错误
func (p *Package) Write(ctx context.Context, output io.Writer, options *WriteOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if output == nil || !validPackageWriteOptions(options) {
		return 0, fmt.Errorf("%w: package write parameters", ErrInvalid)
	}
	r, err := p.writeReader(ctx, options)
	if err != nil {
		return 0, err
	}
	defer r.Close()
	return r.Write(ctx, output, options)
}

// WriteFile 校验完整只读快照后写出到目标文件，写出或关闭失败时清理新建残缺文件
// 入参: ctx 取消Context，nil采用Background, path 目标文件路径, options 写出选项，nil采用默认值
// 返回: error 参数、校验、子集化、取消或文件写入错误
func (p *Package) WriteFile(ctx context.Context, path string, options *WriteOptions) error {
	ctx = normalizeContext(ctx)
	if path == "" || !validPackageWriteOptions(options) {
		return fmt.Errorf("%w: package write parameters", ErrInvalid)
	}
	r, err := p.writeReader(ctx, options)
	if err != nil {
		return err
	}
	defer r.Close()
	file, err := os.Create(path)
	if err != nil {
		return err
	}
	_, writeErr := r.Write(ctx, file, options)
	closeErr := file.Close()
	if writeErr != nil {
		_ = os.Remove(path)
		return writeErr
	}
	if closeErr != nil {
		_ = os.Remove(path)
		return closeErr
	}
	return nil
}

// validPackageWriteOptions 校验Package写出阶段接受的选项参数合法性
// 入参: options 写出选项，nil表示采用默认值
// 返回: bool 参数是否合法
func validPackageWriteOptions(options *WriteOptions) bool {
	if options == nil {
		return true
	}
	return options.Compression <= CompressionOptimize && options.MaxBytes >= 0 && options.InterleaveBytes >= 0 && options.InterleaveBytes <= compressionBufferLimit && (options.InterleaveBytes != 0 || len(options.PartOrder) == 0)
}

// writeReader 为包写出准备已校验只读快照，启用SubsetFonts时在独立副本上执行子集化
// 入参: ctx 取消Context, options 写出选项
// 返回: *Reader 独立只读快照, error 校验、子集化或取消错误
func (p *Package) writeReader(ctx context.Context, options *WriteOptions) (*Reader, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if options == nil || !options.SubsetFonts {
		return p.Reader(ctx)
	}
	if err := p.lock(); err != nil {
		return nil, err
	}
	clone := p.storyCopy()
	p.mu.Unlock()
	if _, err := clone.SubsetFonts(ctx, nil); err != nil {
		return nil, err
	}
	return clone.reader(ctx)
}

// WriteTo 将当前模型写入输出流，不关闭调用方输出流
// 入参: output 输出流
// 返回: int64 已写字节数, error 校验或写出错误
func (p *Package) WriteTo(output io.Writer) (int64, error) {
	return p.Write(context.Background(), output, nil)
}

// lock 校验可编辑包状态并获取写锁，成功后由调用方负责释放写锁
// 返回: error 空指针或未初始化包错误
func (p *Package) lock() error {
	if p == nil {
		return fmt.Errorf("%w: nil package", ErrInvalid)
	}
	p.mu.Lock()
	if p.parts == nil {
		p.mu.Unlock()
		return fmt.Errorf("%w: uninitialized package", ErrInvalid)
	}
	return nil
}

// snapshot 在调用方持有包锁时构造独立的浅拷贝快照，共享不可变部件字节
// 返回: *Package 独立快照
func (p *Package) snapshot() *Package {
	snapshot := &Package{format: p.format, limits: p.limits, sequence: p.sequence, maxImagePixels: p.maxImagePixels, parts: maps.Clone(p.parts), relations: maps.Clone(p.relations), documents: slices.Clone(p.documents), original: p.original, originalRels: p.originalRels, comment: p.comment, dirty: maps.Clone(p.dirty), dirtyRels: maps.Clone(p.dirtyRels)}
	for index := range snapshot.documents {
		snapshot.documents[index].Pages = slices.Clone(snapshot.documents[index].Pages)
	}
	return snapshot
}

// managed 通过固定布局索引判断部件是否受模型管理，按OPC等价名称比较
// 入参: part 部件名称
// 返回: bool 是否受模型管理
func (p *Package) managed(part string) bool {
	return p.layout[strings.ToLower(part)]
}

// storePage 完成页面编码及目标收集后原子替换部件，编码失败不改变已有内容
// 入参: page 带有目标部件名的模型, ctx 取消Context
// 返回: []string 页面链接目标, error 编码或预算错误
func (p *Package) storePage(page *Page, ctx context.Context) ([]string, error) {
	var output bytes.Buffer
	if _, err := EncodePage(ctx, &output, page, &EncodeOptions{Format: p.format, Limits: p.limits}); err != nil {
		return nil, err
	}
	root, err := decodeXML(output.Bytes(), p.limits)
	if err != nil {
		return nil, err
	}
	targets := createdPageTargets(root)
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := p.storePart(page.Part, fixedContentType("fixedpage"), output.Bytes(), false); err != nil {
		return nil, err
	}
	return targets, nil
}

// available 检查新名称不与既有部件相同或构成部件路径派生，不接受关系保留名称
// 入参: part 已规范化名称
// 返回: error 冲突错误
func (p *Package) available(part string) error {
	if opcRelationshipName(part) || p.managed(part) {
		return fmt.Errorf("%w: managed part name collision", ErrInvalid)
	}
	return p.availableName(part)
}

// availableName 检查部件名称及其祖先、后代是否已被占用，不限制部件用途
// 入参: part 已规范化名称
// 返回: error 名称冲突错误
func (p *Package) availableName(part string) error {
	key := strings.ToLower(part)
	if p.names[key] || p.parents[key] != 0 {
		return fmt.Errorf("%w: part name collision", ErrInvalid)
	}
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		if p.names[key[:slash]] {
			return fmt.Errorf("%w: derived part name", ErrInvalid)
		}
	}
	return nil
}

// store 校验资源类型和预算后提交独立字节，失败时保留之前的部件
// 入参: part 已规范化部件名, media 内容类型, data 部件内容
// 返回: error 类型或预算错误
func (p *Package) store(part, media string, data []byte) error {
	return p.storePart(part, media, data, true)
}

// storePart 校验媒体类型与预算后提交独立字节，可选跳过调用方已完成的名称冲突检查
// 入参: part 已规范化部件名, media 内容类型, data 部件内容, checkName 是否检查新部件名称冲突
// 返回: error 类型、冲突或预算错误
func (p *Package) storePart(part, media string, data []byte, checkName bool) error {
	if err := validatePackageMedia(media); err != nil {
		return err
	}
	if int64(len(data)) > p.limits.MaxPartBytes {
		return fmt.Errorf("%w: part byte budget", ErrLimit)
	}
	key := strings.ToLower(part)
	old, exists := p.parts[key]
	if !exists {
		if checkName {
			if err := p.availableName(part); err != nil {
				return err
			}
		}
		if len(p.names)+1 >= p.limits.MaxPartCount {
			return fmt.Errorf("%w: package part count", ErrLimit)
		}
	}
	size := p.total - int64(len(old.data))
	if int64(len(data)) > p.limits.MaxPackageBytes-size {
		return fmt.Errorf("%w: package byte budget", ErrLimit)
	}
	p.parts[key] = packagePart{name: part, media: media, data: bytes.Clone(data)}
	if !exists {
		p.registerName(part)
	}
	p.total = size + int64(len(data))
	p.dirty[key] = true
	return nil
}

// registerName 累计祖先名称的占用，部件派生冲突检查不反复扫描整个包
// 入参: part 已规范化的新部件名称
func (p *Package) registerName(part string) {
	key := strings.ToLower(part)
	p.names[key] = true
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		p.parents[key[:slash]]++
	}
}

// createdPageTargets 枚举直接页面内容的命名目标，不把视觉画刷源或字典定义暴露为可点击位置
// 入参: root 已编码并校验的页面根节点
// 返回: []string 按声明顺序排列的目标
func createdPageTargets(root *xmlElement) []string {
	var result []string
	var visit func(*xmlElement)
	visit = func(node *xmlElement) {
		if name, present := node.attribute("Name"); present {
			result = append(result, name)
		}
		for _, child := range node.Children {
			if child.Name.Local == "Canvas" || child.Name.Local == "Path" || child.Name.Local == "Glyphs" {
				visit(child)
			}
		}
	}
	visit(root)
	return result
}

// NewPage 创建页面模型，方言留空以继承目标包格式，尺寸与语言在编码时校验
// 入参: width 页面宽度, height 页面高度，均以1/96英寸计, language 页面语言
// 返回: *Page 页面模型
func NewPage(width, height float64, language string) *Page {
	box := Rect{Width: width, Height: height}
	return &Page{Width: width, Height: height, Language: language, ContentBox: box, BleedBox: box}
}

// NewCanvas 创建采用标准缺省属性的不透明画布
// 返回: *Canvas 画布模型
func NewCanvas() *Canvas {
	return &Canvas{ElementProperties: ElementProperties{Opacity: 1}}
}

// NewPath 创建采用标准缺省描边参数的不透明路径，不自动添加填充或描边画刷
// 入参: data 路径几何，nil表示未指定
// 返回: *Path 路径模型
func NewPath(data *Geometry) *Path {
	return &Path{ElementProperties: ElementProperties{Opacity: 1}, Data: data, StrokeThickness: 1, StrokeMiterLimit: 10, StrokeDashCap: LineCapFlat, StrokeStartLineCap: LineCapFlat, StrokeEndLineCap: LineCapFlat, StrokeLineJoin: LineJoinMiter}
}

// NewGlyphs 创建采用标准缺省属性的字形模型，不执行排版或字体查询
// 入参: fontURI 字体URI, size 字号，以1/96英寸计, text 文字，不含标记转义前缀
// 返回: *Glyphs 字形模型
func NewGlyphs(fontURI string, size float64, text string) *Glyphs {
	return &Glyphs{ElementProperties: ElementProperties{Opacity: 1}, FontURI: fontURI, FontRenderingEmSize: size, Text: text, StyleSimulations: StyleSimulationNone}
}

// NewBrush 创建不透明画刷模型，插值和延展方式采用标准缺省值，具体内容由调用方填充
// 入参: kind 画刷种类
// 返回: *Brush 画刷模型
func NewBrush(kind BrushKind) *Brush {
	return &Brush{Kind: kind, Opacity: 1}
}

// SolidBrush 将标准颜色转换为精确8位sRGB纯色画刷，nil返回全透明黑色画刷
// 入参: c 标准颜色值，nil表示全透明黑色
// 返回: *Brush 纯色画刷模型
func SolidBrush(c color.Color) *Brush {
	return &Brush{Kind: BrushSolidColor, Opacity: 1, Color: colorToSRGB(c)}
}

// colorToSRGB 将标准颜色转换为满足8位精确编码要求的非预乘sRGB颜色
// 入参: c 标准颜色值
// 返回: Color 精确8位sRGB颜色
func colorToSRGB(c color.Color) Color {
	if c == nil {
		return Color{Space: ColorSRGB, Alpha: 0, Components: []float64{0, 0, 0}}
	}
	switch value := c.(type) {
	case color.NRGBA:
		if value.A == 0 {
			return Color{Space: ColorSRGB, Alpha: 0, Components: []float64{0, 0, 0}}
		}
		return Color{Space: ColorSRGB, Alpha: float64(value.A) / 255, Components: []float64{float64(value.R) / 255, float64(value.G) / 255, float64(value.B) / 255}}
	case color.NRGBA64:
		if value.A == 0 {
			return Color{Space: ColorSRGB, Alpha: 0, Components: []float64{0, 0, 0}}
		}
		return Color{Space: ColorSRGB, Alpha: quantizeSRGB8(float64(value.A) / 65535), Components: []float64{quantizeSRGB8(float64(value.R) / 65535), quantizeSRGB8(float64(value.G) / 65535), quantizeSRGB8(float64(value.B) / 65535)}}
	}
	r, g, b, a := c.RGBA()
	if a == 0 {
		return Color{Space: ColorSRGB, Alpha: 0, Components: []float64{0, 0, 0}}
	}
	af := float64(a)
	return Color{Space: ColorSRGB, Alpha: quantizeSRGB8(af / 65535), Components: []float64{quantizeSRGB8(min(1, float64(r)/af)), quantizeSRGB8(min(1, float64(g)/af)), quantizeSRGB8(min(1, float64(b)/af))}}
}

// quantizeSRGB8 将归一化分量量化为可由8位无损表示的sRGB浮点值
// 入参: value 零到一之间的归一化分量
// 返回: float64 精确8位sRGB分量
func quantizeSRGB8(value float64) float64 {
	return math.Round(value*255) / 255
}

// ImageBrush 创建不透明非平铺图像画刷
// 入参: imageURI 图像部件URI, viewbox 源图像区域, viewport 目标绘制区域
// 返回: *Brush 图像画刷模型
func ImageBrush(imageURI string, viewbox, viewport Rect) *Brush {
	return &Brush{Kind: BrushImage, Opacity: 1, ImageSource: imageURI, Viewbox: viewbox, Viewport: viewport, TileMode: TileNone}
}

// AddText 向页面追加文字字形元素，fill为nil时默认使用纯黑画刷，页面为nil时返回nil
// 入参: fontURI 字体部件URI, origin 基线起点坐标, size 字号，以1/96英寸计, text 文字内容, fill 填充颜色
// 返回: *Glyphs 新建并已追加的字形元素
func (p *Page) AddText(fontURI string, origin Point, size float64, text string, fill color.Color) *Glyphs {
	if p == nil {
		return nil
	}
	if fill == nil {
		fill = color.Black
	}
	glyphs := NewGlyphs(fontURI, size, text)
	glyphs.Origin = origin
	glyphs.Fill = SolidBrush(fill)
	p.Elements = append(p.Elements, glyphs)
	return glyphs
}

// AddPath 向页面追加路径元素，页面为nil时返回nil
// 入参: data 路径几何，nil表示未指定, fill 填充画刷, stroke 描边画刷
// 返回: *Path 新建并已追加的路径元素
func (p *Page) AddPath(data *Geometry, fill, stroke *Brush) *Path {
	if p == nil {
		return nil
	}
	path := NewPath(data)
	path.Fill, path.Stroke = fill, stroke
	p.Elements = append(p.Elements, path)
	return path
}

// AddImage 向页面追加覆盖目标区域的矩形图像路径元素，页面为nil时返回nil
// 入参: imageURI 图像部件URI, viewbox 源图像裁切区域, viewport 目标页面矩形区域
// 返回: *Path 新建并已追加的图像路径元素
func (p *Page) AddImage(imageURI string, viewbox, viewport Rect) *Path {
	if p == nil {
		return nil
	}
	geometry := &Geometry{
		FillRule: GeometryEvenOdd,
		Figures: []GeometryFigure{{
			StartPoint: Point{X: viewport.X, Y: viewport.Y},
			IsClosed:   true,
			IsFilled:   true,
			Segments: []GeometrySegment{
				{Kind: GeometryLine, Point: Point{X: viewport.X + viewport.Width, Y: viewport.Y}, IsStroked: true},
				{Kind: GeometryLine, Point: Point{X: viewport.X + viewport.Width, Y: viewport.Y + viewport.Height}, IsStroked: true},
				{Kind: GeometryLine, Point: Point{X: viewport.X, Y: viewport.Y + viewport.Height}, IsStroked: true},
			},
		}},
	}
	return p.AddPath(geometry, ImageBrush(imageURI, viewbox, viewport), nil)
}

// validateRequiredResourceLinks 校验待写包全部关系分支的必要资源来源、内部目标及存在性，不解码额外资源
// 入参: ctx 取消Context，nil不取消
// 返回: error 关系位置、模式、缺失目标、预算或取消错误
func (r *Reader) validateRequiredResourceLinks(ctx context.Context) error {
	if err := r.readLock(); err != nil {
		return err
	}
	defer r.mu.RUnlock()
	remaining, work := r.limits.MaxPackageBytes, r.limits.MaxXMLNodes
	for _, key := range slices.Sorted(maps.Keys(r.pkg.parts)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if !opcRelationshipName(key) {
			continue
		}
		name := r.pkg.names[key]
		source := relationshipSource(name)
		data, err := r.pkg.readItems(key, min(r.limits.MaxPartBytes, r.limits.MaxMetadataBytes, remaining))
		if err != nil {
			return &PartError{Part: name, Err: err}
		}
		remaining -= int64(len(data))
		_, err = decodeXMLVisit(data, r.limits, func(token xml.Token, node *xmlElement) error {
			if err := checkContext(ctx); err != nil {
				return err
			}
			if work == 0 {
				return fmt.Errorf("%w: required resource relationship work budget", ErrLimit)
			}
			work--
			if _, start := token.(xml.StartElement); !start || node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
				return nil
			}
			kind, _ := node.attribute("Type")
			if kind != formatNamespace(r.format)+"/required-resource" {
				return nil
			}
			media, err := r.pkg.contentType(source)
			if source == "/" || err != nil || !strings.EqualFold(media, fixedContentType("fixedpage")) {
				return fmt.Errorf("%w: Required Resource relationship must originate from FixedPage", ErrInvalid)
			}
			mode, present := node.attribute("TargetMode")
			if present && TargetMode(mode) != TargetModeInternal {
				return fmt.Errorf("%w: external Required Resource relationship", ErrInvalid)
			}
			uri, present := node.attribute("Target")
			if !present {
				return fmt.Errorf("%w: missing Required Resource relationship target", ErrInvalid)
			}
			target, err := resolvePart(source, uri)
			if err != nil {
				return err
			}
			_, err = r.pkg.contentType(target)
			return err
		})
		if err != nil {
			return &PartError{Part: name, Err: err}
		}
	}
	return checkContext(ctx)
}

// newCreatedNavigation 按已校验的序列和文档索引建立导航角色映射，不读取页面内容
// 入参: r 当前包快照, ctx 取消Context
// 返回: *createdNavigation 只读角色索引, error 取消错误
func newCreatedNavigation(r *Reader, ctx context.Context) (*createdNavigation, error) {
	n := &createdNavigation{parts: make(map[string]createdNavigationKind, len(r.documents)+len(r.pages)+1)}
	n.parts[strings.ToLower(r.sequence)] = createdNavigationSequence
	for _, document := range r.documents {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		n.parts[strings.ToLower(document.Part)] = createdNavigationDocument
	}
	for _, page := range r.pages {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		n.parts[strings.ToLower(page.Part)] = createdNavigationPage
	}
	return n, nil
}

// validate 检查页面及资源定义中的内部链接，使用所属FixedPage而非远程字典作为相对地址基准
// 入参: page 页面部件URI, graph 完整资源图, ctx 取消Context
// 返回: error 导航地址、URI或取消错误
func (n *createdNavigation) validate(page string, graph *resourceGraph, ctx context.Context) error {
	for _, node := range graph.Nodes {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if node.Name.Local != "Canvas" && node.Name.Local != "Path" && node.Name.Local != "Glyphs" {
			continue
		}
		if target, present := node.attribute("FixedPage.NavigateUri"); present {
			if err := n.target(page, target); err != nil {
				return &PartError{Part: graph.Parts[node], Element: node.Name.Local, Err: fmt.Errorf("FixedPage.NavigateUri: %w", err)}
			}
		}
	}
	return nil
}

// target 校验内部导航链接的布局地址约束，不访问外部资源
// 入参: source 所属页面部件URI, value 原始链接声明
// 返回: error 导航地址或URI错误
func (n *createdNavigation) target(source, value string) error {
	value = structureURI(value)
	if linkExternal(value) {
		return nil
	}
	uri, err := url.Parse(value)
	if err != nil {
		return fmt.Errorf("%w: navigation URI: %w", ErrInvalid, err)
	}
	if uri.Fragment == "" {
		return nil
	}
	part := source
	if uri.Path != "" {
		part, err = resolvePart(source, uri.EscapedPath())
		if err != nil {
			return err
		}
	}
	kind := n.parts[strings.ToLower(part)]
	if kind == createdNavigationOther {
		return nil
	}
	if linkPageNumber(uri.Fragment) {
		if kind != createdNavigationSequence {
			return fmt.Errorf("%w: M9.8 page address must target the fixed document sequence", ErrInvalid)
		}
	} else if kind == createdNavigationPage {
		return fmt.Errorf("%w: M9.4 named address must target a fixed document or sequence", ErrInvalid)
	}
	return nil
}

// newName 有限查找模板内可用的部件URI，累计限制候选及祖先名称的检查字节，不修改编号或名称索引
// 入参: pattern 含唯一%d占位的URI模板，百分号转义保持原义, ctx 取消Context
// 返回: string 已规范化的可用名称, error 模板、冲突、预算、编号耗尽或取消错误
func (p *Package) newName(pattern string, ctx context.Context) (string, error) {
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	work := p.limits.MaxMetadataBytes
	if int64(len(pattern))-1 > min(work, p.limits.MaxPartBytes) || p.limits.MaxPartCount <= 1 || len(p.names) >= p.limits.MaxPartCount-1 {
		return "", fmt.Errorf("%w: part name allocation budget", ErrLimit)
	}
	prefix, suffix, err := packageNamePattern(pattern, ctx)
	if err != nil {
		return "", err
	}
	key := strings.ToLower(prefix)
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		if err := checkContext(ctx); err != nil {
			return "", err
		}
		if int64(slash) > work {
			return "", fmt.Errorf("%w: part name ancestor byte budget", ErrLimit)
		}
		work -= int64(slash)
		if p.names[key[:slash]] {
			return "", fmt.Errorf("%w: occupied part name directory", ErrInvalid)
		}
	}
	index := p.allocated[pattern]
	if index < 0 || index == math.MaxInt {
		return "", fmt.Errorf("%w: part name index exhausted", ErrLimit)
	}
	for remaining := min(p.limits.MaxPartCount, len(p.names)); remaining >= 0; remaining-- {
		if err := checkContext(ctx); err != nil {
			return "", err
		}
		if index == math.MaxInt {
			break
		}
		index++
		number := strconv.Itoa(index)
		if int64(len(number)) > min(work, p.limits.MaxPartBytes)-int64(len(prefix))-int64(len(suffix)) {
			return "", fmt.Errorf("%w: part name search byte budget", ErrLimit)
		}
		part := prefix + number + suffix
		work -= int64(len(part))
		key := strings.ToLower(part)
		if p.names[key] || p.parents[key] != 0 || p.managed(part) {
			continue
		}
		blocked := false
		for slash := strings.LastIndexByte(key, '/'); slash > len(prefix); slash = strings.LastIndexByte(key[:slash], '/') {
			if err := checkContext(ctx); err != nil {
				return "", err
			}
			if int64(slash) > work {
				return "", fmt.Errorf("%w: part name ancestor byte budget", ErrLimit)
			}
			work -= int64(slash)
			if p.names[key[:slash]] {
				blocked = true
				break
			}
		}
		if blocked {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return "", err
		}
		return part, nil
	}
	return "", fmt.Errorf("%w: part name search exhausted", ErrLimit)
}

// packageNamePattern 校验部件名模板并分离规范化后的前后缀，防止百分号规范化引发切片越界
// 入参: pattern 含唯一%d占位的URI模板, ctx 取消Context
// 返回: string 规范化前缀, string 规范化后缀, error 模板、关系保留名或取消错误
func packageNamePattern(pattern string, ctx context.Context) (string, string, error) {
	slot, err := packageNameSlot(pattern, ctx)
	if err != nil {
		return "", "", err
	}
	first, err := opcPartName(pattern[:slot] + "1" + pattern[slot+2:])
	if err != nil {
		return "", "", err
	}
	if opcRelationshipName(first) {
		return "", "", fmt.Errorf("%w: reserved relationship part name", ErrInvalid)
	}
	second, err := opcPartName(pattern[:slot] + "2" + pattern[slot+2:])
	if err != nil {
		return "", "", err
	}
	letter, err := opcPartName(pattern[:slot] + "a" + pattern[slot+2:])
	if err != nil {
		return "", "", err
	}
	if len(first) != len(second) || len(first) != len(letter) {
		return "", "", fmt.Errorf("%w: invalid part name placeholder", ErrInvalid)
	}
	diff := -1
	for index := 0; index < len(first); index++ {
		if first[index] != second[index] {
			if diff >= 0 {
				return "", "", fmt.Errorf("%w: invalid part name placeholder", ErrInvalid)
			}
			diff = index
		}
	}
	if diff < 0 || first[diff] != '1' || second[diff] != '2' || letter != first[:diff]+"a"+first[diff+1:] {
		return "", "", fmt.Errorf("%w: invalid part name placeholder", ErrInvalid)
	}
	return first[:diff], first[diff+1:], nil
}

// packageNameSlot 识别URI模板中的唯一占位，完整百分号转义不参与占位匹配
// 入参: pattern URI模板, ctx 取消Context
// 返回: int 占位起点, error 占位缺失、重复或取消错误
func packageNameSlot(pattern string, ctx context.Context) (int, error) {
	slot := -1
	checked := 0
	for index := 0; index < len(pattern); index++ {
		if index == 0 || index-checked >= 4096 {
			if err := checkContext(ctx); err != nil {
				return 0, err
			}
			checked = index
		}
		if pattern[index] != '%' {
			continue
		}
		if len(pattern)-index >= 3 && opcHex(pattern[index+1]) >= 0 && opcHex(pattern[index+2]) >= 0 {
			index += 2
			continue
		}
		if len(pattern)-index >= 2 && pattern[index+1] == 'd' {
			if slot >= 0 {
				return 0, fmt.Errorf("%w: repeated part name placeholder", ErrInvalid)
			}
			slot = index
			index++
		}
	}
	if slot < 0 {
		return 0, fmt.Errorf("%w: missing part name placeholder", ErrInvalid)
	}
	return slot, nil
}

// commitName 提交成功操作所用编号，空模板表示调用方指定名称
// 入参: pattern 已通过newName校验的模板, part 同次查找返回的部件URI
func (p *Package) commitName(pattern, part string) {
	if pattern == "" {
		return
	}
	prefix, suffix, err := packageNamePattern(pattern, nil)
	if err != nil || len(part) <= len(prefix)+len(suffix) || !strings.HasPrefix(part, prefix) || !strings.HasSuffix(part, suffix) {
		return
	}
	index, err := strconv.Atoi(part[len(prefix) : len(part)-len(suffix)])
	if err != nil {
		return
	}
	p.allocated[pattern] = index
}

// validateCreatedFonts 校验所有被引用字体面的封装、度量及嵌入许可规则
// 入参: cache 本次快照的字体缓存, graph 完整页面资源图, format 文档方言, ctx 取消Context
// 返回: []string 需要Restricted Font关系的字体部件, error 字体或嵌入规则错误
func validateCreatedFonts(cache *fontCache, graph *resourceGraph, format Format, ctx context.Context) ([]string, error) {
	var restricted []string
	seen := make(map[string]bool)
	parser := newSceneParser(format, graph)
	remaining := cache.pkg.limits.MaxXMLNodes
	checkedGlyphs := make(map[fontCacheKey]map[uint16]bool)
	for _, node := range graph.Nodes {
		if node.Name.Local != "Glyphs" {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		text, _ := node.attribute("FontUri")
		uri, index, present, err := ParseFontURI(strings.Trim(text, " \t\r\n"))
		if err != nil {
			return nil, err
		}
		part, err := resolvePart(graph.Parts[node], uri)
		if err != nil {
			return nil, err
		}
		source, err := cache.load(&Glyphs{FontPart: part, CollectionIndex: index, HasCollectionIndex: present})
		if err != nil {
			return nil, err
		}
		key := fontCacheKey{strings.ToLower(part), index}
		if err := cache.validateCreated(key, source.face); err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		glyphs, err := parser.glyphValue(node, ElementProperties{Part: graph.Parts[node], Opacity: 1})
		if err != nil {
			return nil, err
		}
		run, err := resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, source.glyphYMax, remaining, func() error { return checkContext(ctx) })
		if err != nil {
			return nil, &PartError{Part: graph.Parts[node], Element: "Glyphs", Err: err}
		}
		remaining -= len(run.glyphs)
		_, outlines := source.face.tables["glyf"]
		if outlines || source.face.cff {
			if checkedGlyphs[key] == nil {
				checkedGlyphs[key] = make(map[uint16]bool)
			}
			for _, glyph := range run.glyphs {
				if err := checkContext(ctx); err != nil {
					return nil, err
				}
				if !checkedGlyphs[key][glyph.gid] {
					if _, err := source.glyphOutline(glyph.gid); err != nil {
						return nil, &PartError{Part: part, Err: err}
					}
					checkedGlyphs[key][glyph.gid] = true
				}
			}
		}
		if source.metrics.os2 == nil {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: producer font needs OS/2", ErrInvalid)}
		}
		rights, err := fontEmbeddingRights(source.metrics.os2)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		if rights&2 != 0 {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: font prohibits embedding", ErrInvalid)}
		}
		if rights&0x30c != 0 {
			media, err := cache.pkg.contentType(part)
			if err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			if !strings.EqualFold(media, "application/vnd.ms-package.obfuscated-opentype") {
				return nil, &PartError{Part: part, Err: fmt.Errorf("%w: font requires obfuscation", ErrInvalid)}
			}
		}
		if rights&0x200 != 0 {
			if _, outline := source.face.tables["glyf"]; outline || source.face.cff {
				return nil, &PartError{Part: part, Err: fmt.Errorf("%w: bitmap-only embedding contains outlines", ErrInvalid)}
			}
			bitmap, err := parseFontBitmapsWithWork(source.face, uint32(source.metrics.numGlyphs), func(amount uint64) error {
				if err := checkContext(ctx); err != nil {
					return err
				}
				if remaining < 0 || amount > uint64(remaining) {
					return fmt.Errorf("%w: bitmap font work budget", ErrLimit)
				}
				remaining -= int(amount)
				return nil
			})
			if err != nil {
				return nil, &PartError{Part: part, Err: err}
			}
			hasBitmap := false
			if bitmap != nil {
				for strikeIndex := range bitmap.strikes {
					if len(bitmap.strikes[strikeIndex].entries) != 0 {
						hasBitmap = true
						break
					}
				}
			}
			if !hasBitmap {
				return nil, &PartError{Part: part, Err: fmt.Errorf("%w: bitmap-only font has no embedded bitmap", ErrInvalid)}
			}
		}
		if source.metrics.os2.fsType&4 != 0 && !seen[key.part] {
			seen[key.part] = true
			restricted = append(restricted, part)
		}
	}
	return restricted, nil
}

// validateCreatedResources 解码并校验页面引用的图像与ICC资源，单次快照内每个部件仅校验一次
// 入参: pkg 部件快照, graph 完整页面资源图, checked 已检查部件, channels 配置文件的输入分量数, ctx 取消Context
// 返回: error 资源、解码、预算或取消错误
func (p *Package) validateCreatedResources(pkg *packageReader, graph *resourceGraph, checked map[string]bool, channels map[string]uint32, ctx context.Context) error {
	resources, err := collectRequiredResources(graph, p.format)
	if err != nil {
		return err
	}
	for _, resource := range resources {
		if resource.Kind != requiredImage && resource.Kind != requiredProfile {
			continue
		}
		key := fmt.Sprintf("%d:%s", resource.Kind, strings.ToLower(resource.Part))
		if checked[key] {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return err
		}
		data, err := pkg.readPart(resource.Part)
		if err != nil {
			return err
		}
		if resource.Kind == requiredProfile {
			var profile *iccProfile
			profile, err = validateCreatedICCProfile(data, ctx)
			if err == nil {
				count := uint32(profile.channels)
				if profile.class == "nmcl" {
					count = binary.BigEndian.Uint32(profile.tag("ncl2")[12:])
				}
				channels[strings.ToLower(resource.Part)] = count
			}
		} else {
			media, mediaErr := pkg.contentType(resource.Part)
			if mediaErr != nil {
				return mediaErr
			}
			var image *rasterImage
			image, err = decodeRasterImageContext(ctx, data, media, p.maxImagePixels)
			if err == nil && len(image.profile) != 0 {
				profile := image.profile
				if image.profileCompressed {
					profile, err = inflatePNGProfile(profile, p.limits.MaxMetadataBytes)
				}
				if err == nil {
					var parsed *iccProfile
					parsed, err = validateCreatedICCProfile(profile, ctx)
					if err == nil && (parsed.class == "link" || parsed.class == "abst") {
						err = fmt.Errorf("%w: ICC profile class cannot be embedded in an image", ErrInvalid)
					}
				}
			}
		}
		if err != nil {
			return &PartError{Part: resource.Part, Err: err}
		}
		checked[key] = true
	}
	return validateCreatedContextColors(graph, channels, ctx)
}

// validateCreatedContextColors 检查颜色分量与ICC输入是否匹配，命名色使用色调数量而非设备坐标数量
// 入参: graph 包含远程字典的页面资源图, channels 已校验配置文件的输入分量数, ctx 取消Context
// 返回: error 颜色、引用、分量数量或取消错误
func validateCreatedContextColors(graph *resourceGraph, channels map[string]uint32, ctx context.Context) error {
	for _, node := range graph.Nodes {
		if err := checkContext(ctx); err != nil {
			return err
		}
		for _, attribute := range node.Attr {
			if attribute.Name.Space != "" || !requiredColorAttribute(node.Name.Local, attribute.Name.Local) || graph.Bindings[node][attribute.Name.Local] != nil {
				continue
			}
			if _, reference, err := parseResourceReference(attribute.Value); err != nil {
				return err
			} else if reference {
				continue
			}
			value, err := parseBrushColor(attribute.Value, node.Name.Space)
			if err != nil {
				return err
			}
			if value.Space != ColorContext {
				continue
			}
			part, err := resolvePart(graph.Parts[node], value.ProfileURI)
			if err != nil {
				return err
			}
			count, present := channels[strings.ToLower(part)]
			if !present || count != uint32(len(value.Components)) {
				return &PartError{Part: graph.Parts[node], Element: node.Name.Local, Err: fmt.Errorf("%w: %s color components do not match ICC profile %s", ErrInvalid, attribute.Name.Local, part)}
			}
		}
	}
	return checkContext(ctx)
}

// validateStoryLinks 校验实际关联的故事结构，不解析字体、几何或拼装文本，不改动源数据
// 入参: ctx 取消Context，nil不取消
// 返回: error 关闭、关联、模式、预算或取消错误
func (r *Reader) validateStoryLinks(ctx context.Context) error {
	if err := r.readLock(); err != nil {
		return err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return err
	}
	g := createdStoryGraph{context: ctx, remaining: r.limits.MaxPackageBytes, work: r.limits.MaxXMLNodes, relations: make(map[string][]Relationship), structures: make(map[string]*DocumentStructure), fragments: make(map[string]*StoryFragments), names: make(map[string]map[string]bool)}
	backend := *r.pkg
	previous := backend.beforeRead
	backend.beforeRead = func(key string, size uint64, limit int64) (int64, error) {
		if err := g.step(0); err != nil {
			return 0, err
		}
		if size > uint64(g.remaining) {
			return 0, fmt.Errorf("%w: story part %s exceeds byte budget", ErrLimit, key)
		}
		g.remaining -= int64(size)
		limit = min(limit, int64(size))
		if previous != nil {
			return previous(key, size, limit)
		}
		return limit, nil
	}
	g.backend = &backend
	pkg := backend
	pkg.relation = g.relationships
	g.reader = &Reader{pkg: &pkg, format: r.format, limits: r.limits, sequence: r.sequence, documents: r.documents, pages: r.pages}
	first := 0
	for index, document := range r.documents {
		if err := g.step(1); err != nil {
			return err
		}
		structure, err := g.document(index)
		if err != nil {
			return err
		}
		known := make(map[string]bool)
		if structure != nil {
			for _, story := range structure.Stories {
				if err := g.step(1); err != nil {
					return err
				}
				known[story.Name] = true
			}
		}
		locations := make(map[contentFragmentKey]int)
		fragmentNames := make(map[contentFragmentKey]bool)
		for local := range document.Pages {
			if err := g.step(1); err != nil {
				return err
			}
			fragments, err := g.pageFragments(first + local)
			if err != nil {
				return err
			}
			if fragments == nil {
				continue
			}
			for _, fragment := range fragments.Fragments {
				if err := g.step(1); err != nil {
					return err
				}
				if fragment.StoryName != nil {
					if !known[*fragment.StoryName] {
						return &PartError{Part: fragments.Part, Element: "StoryFragment", Err: fmt.Errorf("%w: story %q is not defined in its fixed document", ErrInvalid, *fragment.StoryName)}
					}
					key := contentFragmentKey{page: local, story: *fragment.StoryName}
					locations[key]++
					if fragment.FragmentName != nil {
						key.named, key.name = true, *fragment.FragmentName
						locations[key]++
						identity := contentFragmentKey{story: key.story, name: key.name, named: true}
						if fragmentNames[identity] {
							return &PartError{Part: fragments.Part, Element: "StoryFragment", Err: fmt.Errorf("%w: duplicate fragment name %q in story %q", ErrInvalid, key.name, key.story)}
						}
						fragmentNames[identity] = true
					}
				}
				if err := g.content(first+local, fragment.Content, 0); err != nil {
					return &PartError{Part: fragments.Part, Element: "StoryFragment", Err: err}
				}
			}
		}
		if structure != nil {
			for _, story := range structure.Stories {
				for _, reference := range story.Fragments {
					if err := g.step(1); err != nil {
						return err
					}
					key := contentFragmentKey{page: reference.PageNumber - 1, story: story.Name}
					if reference.FragmentName != nil {
						key.named, key.name = true, *reference.FragmentName
					}
					if reference.PageNumber < 1 || reference.PageNumber > len(document.Pages) || locations[key] != 1 {
						return &PartError{Part: structure.Part, Element: "StoryFragmentReference", Err: fmt.Errorf("%w: story %q page %d identifies %d fragments", ErrInvalid, story.Name, reference.PageNumber, locations[key])}
					}
				}
			}
		}
		first += len(document.Pages)
	}
	return g.step(0)
}

// step 检查取消并限制整次校验的关联和索引工作量
// 入参: count 本次处理数量
// 返回: error 取消或预算错误
func (g *createdStoryGraph) step(count int) error {
	if err := checkContext(g.context); err != nil {
		return err
	}
	if count > g.work {
		return fmt.Errorf("%w: story link work budget", ErrLimit)
	}
	g.work -= count
	return nil
}

// relationships 缓存源部件关系，避免结构解析器重复读取同一关系部件
// 入参: source 规范化源部件
// 返回: []Relationship 关系, bool 是否已处理, error 读取或预算错误
func (g *createdStoryGraph) relationships(source string) ([]Relationship, bool, error) {
	if err := g.step(0); err != nil {
		return nil, true, err
	}
	key := strings.ToLower(source)
	if relations, found := g.relations[key]; found {
		return relations, true, nil
	}
	relations, err := g.backend.relationships(source)
	if err != nil {
		return nil, true, err
	}
	if err := g.step(len(relations)); err != nil {
		return nil, true, err
	}
	g.relations[key] = relations
	return relations, true, nil
}

// target 仅按当前方言的明确关系定位结构，不根据内容类型猜测未关联部件
// 入参: source 源部件, kind 关系种类
// 返回: string 目标部件，未关联时为空, error 关联或取消错误
func (g *createdStoryGraph) target(source, kind string) (string, error) {
	relations, _, err := g.relationships(source)
	if err != nil {
		return "", err
	}
	part := ""
	for _, relation := range relations {
		if err := g.step(1); err != nil {
			return "", err
		}
		if relation.Type != formatNamespace(g.reader.format)+"/"+kind {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return "", &PartError{Part: source, Err: fmt.Errorf("%w: external %s part", ErrInvalid, kind)}
		}
		target, err := resolvePart(source, relation.Target)
		if err != nil {
			return "", &PartError{Part: source, Err: err}
		}
		if part != "" && !strings.EqualFold(part, target) {
			return "", &PartError{Part: source, Err: fmt.Errorf("%w: multiple distinct %s parts", ErrInvalid, kind)}
		}
		part = target
	}
	return part, nil
}

// document 复用标准结构解析，缓存共享部件，页码在每个所属文档中另行检查
// 入参: index 固定文档序号
// 返回: *DocumentStructure 结构，未关联时为nil, error 读取或模式错误
func (g *createdStoryGraph) document(index int) (*DocumentStructure, error) {
	part, err := g.target(g.reader.documents[index].Part, "documentstructure")
	if err != nil || part == "" {
		return nil, err
	}
	key := strings.ToLower(part)
	if structure, found := g.structures[key]; found {
		return structure, nil
	}
	structure, err := g.reader.readDocumentStructure(index)
	if err != nil {
		return nil, err
	}
	if structure.Outline != nil {
		if err := g.step(len(structure.Outline.Entries)); err != nil {
			return nil, err
		}
	}
	g.structures[key] = structure
	return structure, nil
}

// pageFragments 复用标准片段解析，共享部件只解码一次但不共享页面绑定结论
// 入参: index 全局页面序号
// 返回: *StoryFragments 片段，未关联时为nil, error 读取或模式错误
func (g *createdStoryGraph) pageFragments(index int) (*StoryFragments, error) {
	part, err := g.target(g.reader.pages[index].Part, "storyfragments")
	if err != nil || part == "" {
		return nil, err
	}
	key := strings.ToLower(part)
	if fragments, found := g.fragments[key]; found {
		return fragments, nil
	}
	fragments, err := g.reader.readStoryFragments(index)
	if err != nil {
		return nil, err
	}
	g.fragments[key] = fragments
	return fragments, nil
}

// content 绑定命名元素与列表标记，不要求LinkTarget声明或限制重复内容引用
// 入参: index 全局页号, content 语义节点, depth 当前深度
// 返回: error 名称、深度、预算或取消错误
func (g *createdStoryGraph) content(index int, content []ContentStructure, depth int) error {
	if depth >= g.reader.limits.MaxXMLDepth {
		return fmt.Errorf("%w: story link depth", ErrLimit)
	}
	for _, node := range content {
		if err := g.step(1); err != nil {
			return err
		}
		if node.Kind == StructureNamedElement || node.Marker != nil {
			names, err := g.pageNames(index)
			if err != nil {
				return err
			}
			name := node.NameReference
			if node.Marker != nil {
				name = *node.Marker
			}
			if !names[name] {
				return fmt.Errorf("%w: named element %q is absent from page %s", ErrInvalid, name, g.reader.pages[index].Part)
			}
		}
		if len(node.Children) != 0 {
			if err := g.content(index, node.Children, depth+1); err != nil {
				return err
			}
		}
	}
	return nil
}

// pageNames 从页内XML建立可供故事结构引用的元素名称索引
// 入参: index 全局页面序号
// 返回: map[string]bool 页内名称, error 页面、预算或取消错误
func (g *createdStoryGraph) pageNames(index int) (map[string]bool, error) {
	key := strings.ToLower(g.reader.pages[index].Part)
	if names, found := g.names[key]; found {
		return names, nil
	}
	page, err := g.reader.readPageHeader(index, nil, g.context)
	if err != nil {
		return nil, err
	}
	names := make(map[string]bool)
	var visit func(*xmlElement) error
	visit = func(node *xmlElement) error {
		if err := g.step(1); err != nil {
			return err
		}
		switch node.Name.Local {
		case "FixedPage", "Canvas", "Path", "Glyphs":
			if name, present := node.attribute("Name"); present {
				names[name] = true
			}
		}
		for _, child := range node.Children {
			if err := visit(child); err != nil {
				return err
			}
		}
		return nil
	}
	if err := visit(page.root); err != nil {
		return nil, err
	}
	g.names[key] = names
	return names, nil
}

// relationSourceName 还原关系源部件的原始大小写，依次查找当前快照、文档序列及包内部件
// 入参: pkg 内存快照索引, source 小写关系键或包根
// 返回: string 保留原始大小写的源部件名称
func (p *Package) relationSourceName(pkg *packageReader, source string) string {
	if source == "/" {
		return "/"
	}
	if name := pkg.names[source]; name != "" {
		return name
	}
	if strings.EqualFold(p.sequence, source) {
		return p.sequence
	}
	if part, exists := p.parts[source]; exists && part.name != "" {
		return part.name
	}
	for _, document := range p.documents {
		if strings.EqualFold(document.Part, source) {
			return document.Part
		}
		for _, page := range document.Pages {
			if strings.EqualFold(page.Part, source) {
				return page.Part
			}
		}
	}
	return source
}

// reader 构造独立部件索引，保留原标记并更新已修改的索引和关系，不创建中间ZIP
// 入参: ctx 取消Context
// 返回: *Reader 已校验快照, error 结构、资源或取消错误
func (p *Package) reader(ctx context.Context) (*Reader, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if len(p.documents) == 0 {
		return nil, fmt.Errorf("%w: package needs a document", ErrInvalid)
	}
	pkg := p.partReader()
	sequence := createdNode(formatNamespace(p.format), "FixedDocumentSequence")
	for _, document := range p.documents {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if len(document.Pages) == 0 {
			return nil, fmt.Errorf("%w: document %s needs a page", ErrInvalid, document.Part)
		}
		reference := createdNode(formatNamespace(p.format), "DocumentReference")
		documentSource, err := relativePart(p.sequence, document.Part)
		if err != nil {
			return nil, err
		}
		reference.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: documentSource}}
		sequence.Children = append(sequence.Children, reference)
		if _, present := p.original[strings.ToLower(document.Part)]; present && !p.dirty[strings.ToLower(document.Part)] {
			continue
		}
		root := createdNode(formatNamespace(p.format), "FixedDocument")
		for _, page := range document.Pages {
			child := createdNode(formatNamespace(p.format), "PageContent")
			pageSource, err := relativePart(document.Part, page.Part)
			if err != nil {
				return nil, err
			}
			child.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: pageSource}}
			if page.Width > 0 {
				child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "Width"}, Value: encodeNumber(page.Width)})
			}
			if page.Height > 0 {
				child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "Height"}, Value: encodeNumber(page.Height)})
			}
			if len(page.LinkTargets) != 0 {
				container := createdNode(formatNamespace(p.format), "PageContent.LinkTargets")
				for _, name := range page.LinkTargets {
					target := createdNode(formatNamespace(p.format), "LinkTarget")
					target.Attr = []xml.Attr{{Name: xml.Name{Local: "Name"}, Value: name}}
					container.Children = append(container.Children, target)
				}
				child.Children = []*xmlElement{container}
			}
			root.Children = append(root.Children, child)
		}
		data, err := createdMarkup(root, p.limits, ctx)
		if err != nil {
			return nil, err
		}
		createdPut(pkg, document.Part, fixedContentType("fixeddocument"), data)
	}
	if _, present := p.original[strings.ToLower(p.sequence)]; !present || p.dirty[strings.ToLower(p.sequence)] {
		data, err := createdMarkup(sequence, p.limits, ctx)
		if err != nil {
			return nil, err
		}
		createdPut(pkg, p.sequence, fixedContentType("fixeddocumentsequence"), data)
	}
	deferred := make(map[string]bool, len(p.documents)+1)
	deferred["/"] = true
	for _, document := range p.documents {
		deferred[strings.ToLower(document.Part)] = true
		for _, page := range document.Pages {
			deferred[strings.ToLower(page.Part)] = true
		}
	}
	for _, source := range slices.Sorted(maps.Keys(p.relations)) {
		if deferred[source] {
			continue
		}
		if err := p.composeRelationships(pkg, p.relationSourceName(pkg, source), nil, ctx); err != nil {
			return nil, err
		}
	}
	rootRelations := []Relationship{{Type: formatNamespace(p.format) + "/fixedrepresentation", Target: p.sequence, TargetMode: TargetModeInternal}}
	if err := p.composeRelationships(pkg, "/", rootRelations, ctx); err != nil {
		return nil, err
	}
	r := &Reader{pkg: pkg, format: p.format, limits: p.limits}
	if err := r.readSequence(); err != nil {
		return nil, err
	}
	if _, err := r.CoreProperties(ctx); err != nil {
		return nil, err
	}
	navigation, err := newCreatedNavigation(r, ctx)
	if err != nil {
		return nil, err
	}
	for _, page := range r.pages {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		root, err := r.readFixedPart(page.Part, "fixedpage", "FixedPage")
		if err != nil {
			return nil, err
		}
		graph, err := parseResourceGraphContext(page.Part, root, r.format, r.limits, func(part string) (*xmlElement, error) { return r.readResourceDictionaryLoader(part, nil, ctx) }, ctx)
		if err != nil {
			return nil, err
		}
		if err := navigation.validate(page.Part, graph, ctx); err != nil {
			return nil, err
		}
		dependencies, err := collectRequiredResources(graph, p.format)
		if err != nil {
			return nil, err
		}
		var relations []Relationship
		seen := make(map[string]bool)
		for _, dependency := range dependencies {
			key := strings.ToLower(dependency.Part)
			if seen[key] {
				continue
			}
			seen[key] = true
			relations = append(relations, Relationship{Type: formatNamespace(p.format) + "/required-resource", Target: dependency.Part, TargetMode: TargetModeInternal})
		}
		if err := p.composeRelationships(pkg, page.Part, relations, ctx); err != nil {
			return nil, err
		}
	}
	fonts := fontCache{pkg: pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: p.limits.MaxPackageBytes, maxFaces: p.limits.MaxPartCount}
	restricted := make(map[string][]Relationship)
	checkedResources := make(map[string]bool)
	profileChannels := make(map[string]uint32)
	owners := make(map[string]string)
	for _, document := range r.documents {
		for _, page := range document.Pages {
			owners[strings.ToLower(page.Part)] = strings.ToLower(document.Part)
		}
	}
	for index := range r.pages {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		page, err := r.readPage(index)
		if err != nil {
			return nil, err
		}
		changed, err := p.changedResources(page.resources)
		if err != nil {
			return nil, err
		}
		var parts []string
		if changed {
			parts, err = validateCreatedFonts(&fonts, page.resources, p.format, ctx)
			if err != nil {
				return nil, err
			}
			if err := p.validateCreatedResources(pkg, page.resources, checkedResources, profileChannels, ctx); err != nil {
				return nil, err
			}
		}
		key := owners[strings.ToLower(page.Part)]
		for _, part := range parts {
			duplicate := false
			for _, relation := range restricted[key] {
				duplicate = duplicate || strings.EqualFold(relation.Target, part)
			}
			if !duplicate {
				restricted[key] = append(restricted[key], Relationship{Type: formatNamespace(p.format) + "/restricted-font", Target: part, TargetMode: TargetModeInternal})
			}
		}
	}
	for _, document := range r.documents {
		if err := p.composeRelationships(pkg, document.Part, restricted[strings.ToLower(document.Part)], ctx); err != nil {
			return nil, err
		}
	}
	types := createdNode(opcTypesNS, "Types")
	for _, key := range slices.Sorted(maps.Keys(pkg.parts)) {
		child := createdNode(opcTypesNS, "Override")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "PartName"}, Value: pkg.names[key]}, {Name: xml.Name{Local: "ContentType"}, Value: pkg.overrides[key]}}
		types.Children = append(types.Children, child)
	}
	data := p.originalTypes(pkg)
	if data == nil {
		var err error
		data, err = createdMarkup(types, p.limits, ctx)
		if err != nil {
			return nil, err
		}
	}
	createdPut(pkg, opcTypesName, "", data)
	var total int64
	if len(pkg.parts) > p.limits.MaxPartCount {
		return nil, fmt.Errorf("%w: generated package part count", ErrLimit)
	}
	for key, data := range pkg.data {
		if int64(len(data)) > p.limits.MaxPartBytes || int64(len(data)) > p.limits.MaxPackageBytes-total {
			return nil, fmt.Errorf("%w: generated package byte budget", ErrLimit)
		}
		total += int64(len(data))
		for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
			if _, exists := pkg.parts[key[:slash]]; exists {
				return nil, fmt.Errorf("%w: derived generated part name", ErrInvalid)
			}
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := r.validateRequiredResourceLinks(ctx); err != nil {
		return nil, err
	}
	if err := r.validatePrintTicketLinks(ctx); err != nil {
		return nil, err
	}
	if err := r.validateSignatureDefinitionLinks(ctx); err != nil {
		return nil, err
	}
	if err := p.validateThumbnailLinks(r, ctx); err != nil {
		return nil, err
	}
	control, err := r.DiscardControl(ctx)
	if err != nil {
		return nil, err
	}
	if control != nil {
		if control.Ignored != 0 {
			return nil, fmt.Errorf("%w: invalid produced discard reference", ErrInvalid)
		}
		for _, hint := range control.Hints {
			if _, exists := pkg.parts[strings.ToLower(hint.Target)]; !exists {
				return nil, fmt.Errorf("%w: discard target is absent", ErrInvalid)
			}
			page := false
			for _, value := range r.pages {
				page = page || strings.EqualFold(value.Part, hint.SentinelPage)
			}
			if !page {
				return nil, fmt.Errorf("%w: discard sentinel is not a fixed page", ErrInvalid)
			}
		}
		if len(control.Hints) != 0 {
			if err := r.validateDiscardLifetime(control, ctx); err != nil {
				return nil, err
			}
		}
	}
	if err := r.validateStoryLinks(ctx); err != nil {
		return nil, err
	}
	return r, nil
}

// createdNode 创建标准命名空间中的结构节点
// 入参: namespace 命名空间, name 元素名称
// 返回: *xmlElement 结构节点
func createdNode(namespace, name string) *xmlElement {
	return &xmlElement{Name: xml.Name{Space: namespace, Local: name}, Namespaces: map[string]string{"": namespace, "xml": xmlNamespace}}
}

// createdMarkup 输出由标准结构生成的独立XML，保留元素上的MCE保留扩展及必要命名空间声明
// 入参: root 标准根节点, limits 资源上限, ctx 取消Context
// 返回: []byte XML数据, error 取消、字符、结构或预算错误
func createdMarkup(root *xmlElement, limits Limits, ctx context.Context) ([]byte, error) {
	return createdMarkupContent(root, nil, limits, ctx)
}

// createdMarkupContent 输出由标准结构及可选有序内容生成的独立XML，保留原始MCE保留元素、保留属性及相对顺序
// 入参: root 标准根节点, ordered 可选有序内容索引, limits 资源上限, ctx 取消Context
// 返回: []byte XML数据, error 取消、字符、结构或预算错误
func createdMarkupContent(root *xmlElement, ordered map[*xmlElement][]xmlContent, limits Limits, ctx context.Context) ([]byte, error) {
	if hasPreservedMarkup(root, root.Name.Space) {
		return createdPreservedMarkup(root, ordered, limits, ctx)
	}
	node := *root
	hasDefaultNS := false
	for _, attr := range root.Attr {
		if attr.Name == (xml.Name{Local: "xmlns"}) {
			hasDefaultNS = true
			break
		}
	}
	if !hasDefaultNS {
		node.Attr = append([]xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: root.Name.Space}}, root.Attr...)
	}
	root = &node
	count := 0
	var validate func(*xmlElement, int) error
	validate = func(node *xmlElement, depth int) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		count++
		if count > limits.MaxXMLNodes || depth > limits.MaxXMLDepth {
			return fmt.Errorf("%w: generated XML complexity", ErrLimit)
		}
		if !xmlTextValid(node.Text) || len(node.Children) != 0 && !xmlWhitespace(node.Text) {
			return fmt.Errorf("%w: invalid or ambiguous generated XML text", ErrInvalid)
		}
		for _, attr := range node.Attr {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
		}
		for _, child := range node.Children {
			if err := validate(child, depth+1); err != nil {
				return err
			}
		}
		return nil
	}
	if err := validate(root, 1); err != nil {
		return nil, err
	}
	limit := min(limits.MaxPartBytes, limits.MaxPackageBytes)
	if root.Name.Space == opcTypesNS || root.Name.Space == opcRelsNS {
		limit = min(limit, limits.MaxMetadataBytes)
	}
	var output bytes.Buffer
	counted := packageOutput{writer: &output, context: ctx, limit: limit}
	encoder := xml.NewEncoder(&counted)
	if err := encodePageNode(encoder, root, ctx); err != nil {
		return nil, err
	}
	if err := encoder.Flush(); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// hasPreservedMarkup 检查元素树是否包含需透传的MCE保留元素、保留属性或跨命名空间节点
// 入参: node 当前元素, defaultNS 根默认命名空间
// 返回: bool 是否需要走保留扩展序列化路径
func hasPreservedMarkup(node *xmlElement, defaultNS string) bool {
	if node == nil {
		return false
	}
	if len(node.PreservedElements) != 0 || len(node.PreservedAttributes) != 0 || node.Name.Space != defaultNS {
		return true
	}
	for _, child := range node.Children {
		if hasPreservedMarkup(child, defaultNS) {
			return true
		}
	}
	return false
}

// createdPreservedMarkup 构造带MCE保留元素、保留属性与命名空间声明的独立XML输出，不修改输入树
// 入参: root 根节点, ordered 可选有序内容索引, limits 资源上限, ctx 取消Context
// 返回: []byte 独立UTF-8 XML, error 字符、命名空间、预算或取消错误
func createdPreservedMarkup(root *xmlElement, ordered map[*xmlElement][]xmlContent, limits Limits, ctx context.Context) ([]byte, error) {
	defaultNS := root.Name.Space
	prefixes := make(map[string]string)
	used := map[string]bool{"xml": true, "xmlns": true}
	extSeq := 0
	bindPrefix := func(uri string, hints map[string]string) (string, error) {
		if uri == "" {
			return "", nil
		}
		if uri == xmlNamespace {
			return "xml", nil
		}
		if uri == xmlnsNamespace {
			return "", fmt.Errorf("%w: reserved XML namespace binding", ErrInvalid)
		}
		if existing, ok := prefixes[uri]; ok {
			return existing, nil
		}
		if uri == mcNamespace && !used["mc"] {
			prefixes[uri], used["mc"] = "mc", true
			return "mc", nil
		}
		if len(hints) != 0 {
			for _, prefix := range slices.Sorted(maps.Keys(hints)) {
				if prefix != "" && prefix != "xml" && prefix != "xmlns" && hints[prefix] == uri && xmlNCName(prefix) && !used[prefix] {
					prefixes[uri], used[prefix] = prefix, true
					return prefix, nil
				}
			}
		}
		for {
			extSeq++
			cand := "ext" + strconv.Itoa(extSeq)
			if !used[cand] {
				prefixes[uri], used[cand] = cand, true
				return cand, nil
			}
		}
	}
	ignorable := make(map[string]bool)
	preserveElems := make(map[string]bool)
	preserveAttrs := make(map[string]bool)
	count := 0
	var scanPreserved func(*xmlElement, map[string]string, int) error
	scanPreserved = func(node *xmlElement, fallbackNS map[string]string, depth int) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		count++
		if count > limits.MaxXMLNodes || depth > limits.MaxXMLDepth {
			return fmt.Errorf("%w: generated XML complexity", ErrLimit)
		}
		if !xmlTextValid(node.Text) {
			return fmt.Errorf("%w: invalid generated XML text", ErrInvalid)
		}
		hints := node.Namespaces
		if len(hints) == 0 {
			hints = fallbackNS
		}
		if node.Name.Space != "" && node.Name.Space != defaultNS {
			if _, err := bindPrefix(node.Name.Space, hints); err != nil {
				return err
			}
		}
		for _, attr := range node.Attr {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if attr.Name.Space == "" || attr.Name.Space == xmlnsNamespace || attr.Name.Space == xmlNamespace {
				continue
			}
			if _, err := bindPrefix(attr.Name.Space, hints); err != nil {
				return err
			}
		}
		for _, attr := range node.PreservedAttributes {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if attr.Name.Space != "" && attr.Name.Space != xmlNamespace {
				if _, err := bindPrefix(attr.Name.Space, hints); err != nil {
					return err
				}
			}
		}
		for _, child := range node.Children {
			if err := scanPreserved(child, hints, depth+1); err != nil {
				return err
			}
		}
		for _, item := range node.PreservedElements {
			if err := scanPreserved(item, hints, depth+1); err != nil {
				return err
			}
		}
		return nil
	}
	var scanConsumed func(*xmlElement, int) error
	scanConsumed = func(node *xmlElement, depth int) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		count++
		if count > limits.MaxXMLNodes || depth > limits.MaxXMLDepth {
			return fmt.Errorf("%w: generated XML complexity", ErrLimit)
		}
		if !xmlTextValid(node.Text) || len(node.Children) != 0 && !xmlWhitespace(node.Text) {
			return fmt.Errorf("%w: invalid or ambiguous generated XML text", ErrInvalid)
		}
		if node.Name.Space != "" && node.Name.Space != defaultNS {
			if _, err := bindPrefix(node.Name.Space, node.Namespaces); err != nil {
				return err
			}
		}
		for _, attr := range node.Attr {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if attr.Name.Space == "" || attr.Name.Space == xmlnsNamespace || attr.Name.Space == xmlNamespace || attr.Name.Space == node.Name.Space+"/resourcedictionary-key" {
				continue
			}
			if _, err := bindPrefix(attr.Name.Space, node.Namespaces); err != nil {
				return err
			}
		}
		for _, attr := range node.PreservedAttributes {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if attr.Name.Space != "" && attr.Name.Space != xmlNamespace {
				prefix, err := bindPrefix(attr.Name.Space, node.Namespaces)
				if err != nil {
					return err
				}
				ignorable[prefix] = true
				preserveAttrs[prefix+":"+attr.Name.Local] = true
			}
		}
		for _, item := range node.PreservedElements {
			hints := item.Namespaces
			if len(hints) == 0 {
				hints = node.Namespaces
			}
			if item.Name.Space != "" {
				prefix, err := bindPrefix(item.Name.Space, hints)
				if err != nil {
					return err
				}
				ignorable[prefix] = true
				preserveElems[prefix+":"+item.Name.Local] = true
			}
			if err := scanPreserved(item, node.Namespaces, depth+1); err != nil {
				return err
			}
		}
		for _, child := range node.Children {
			if err := scanConsumed(child, depth+1); err != nil {
				return err
			}
		}
		return nil
	}
	if err := scanConsumed(root, 1); err != nil {
		return nil, err
	}
	mcPrefix := ""
	if len(ignorable) != 0 {
		var err error
		mcPrefix, err = bindPrefix(mcNamespace, root.Namespaces)
		if err != nil {
			return nil, err
		}
	}
	limit := min(limits.MaxPartBytes, limits.MaxPackageBytes)
	if root.Name.Space == opcTypesNS || root.Name.Space == opcRelsNS {
		limit = min(limit, limits.MaxMetadataBytes)
	}
	var output bytes.Buffer
	counted := packageOutput{writer: &output, context: ctx, limit: limit}
	encoder := xml.NewEncoder(&counted)
	var encodeNode func(*xmlElement, bool, bool, bool) error
	encodeNode = func(node *xmlElement, isRoot, isPreserved, emptyDefault bool) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		localName := node.Name.Local
		needEmptyDefault := false
		if node.Name.Space == "" {
			if isPreserved && !emptyDefault {
				needEmptyDefault = true
			}
		} else if node.Name.Space != defaultNS || emptyDefault {
			if prefix := prefixes[node.Name.Space]; prefix != "" {
				localName = prefix + ":" + node.Name.Local
			}
		}
		start := xml.StartElement{Name: xml.Name{Local: localName}}
		if isRoot {
			if defaultNS != "" {
				if err := xmlNamespaceOutput("", defaultNS); err != nil {
					return err
				}
				start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: "xmlns"}, Value: defaultNS})
			}
			type nsEntry struct {
				prefix string
				uri    string
			}
			entries := make([]nsEntry, 0, len(prefixes))
			for uri, prefix := range prefixes {
				entries = append(entries, nsEntry{prefix: prefix, uri: uri})
			}
			slices.SortFunc(entries, func(a, b nsEntry) int { return strings.Compare(a.prefix, b.prefix) })
			for _, entry := range entries {
				if err := xmlNamespaceOutput(entry.prefix, entry.uri); err != nil {
					return err
				}
				start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: "xmlns:" + entry.prefix}, Value: entry.uri})
			}
			if len(ignorable) != 0 {
				start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: mcPrefix + ":Ignorable"}, Value: strings.Join(slices.Sorted(maps.Keys(ignorable)), " ")})
				if len(preserveElems) != 0 {
					start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: mcPrefix + ":PreserveElements"}, Value: strings.Join(slices.Sorted(maps.Keys(preserveElems)), " ")})
				}
				if len(preserveAttrs) != 0 {
					start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: mcPrefix + ":PreserveAttributes"}, Value: strings.Join(slices.Sorted(maps.Keys(preserveAttrs)), " ")})
				}
			}
		} else if needEmptyDefault {
			start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: "xmlns"}, Value: ""})
		}
		appendAttr := func(attr xml.Attr) {
			switch attr.Name.Space {
			case xmlnsNamespace:
				return
			case "":
				if attr.Name.Local == "xmlns" {
					return
				}
			case xmlNamespace:
				attr.Name = xml.Name{Local: "xml:" + attr.Name.Local}
			default:
				if attr.Name.Space == node.Name.Space+"/resourcedictionary-key" {
					attr.Name = xml.Name{Local: "r:" + attr.Name.Local}
				} else if prefix := prefixes[attr.Name.Space]; prefix != "" {
					attr.Name = xml.Name{Local: prefix + ":" + attr.Name.Local}
				}
			}
			start.Attr = append(start.Attr, attr)
		}
		for _, attr := range node.Attr {
			appendAttr(attr)
		}
		for _, attr := range node.PreservedAttributes {
			appendAttr(attr)
		}
		if err := encoder.EncodeToken(start); err != nil {
			return err
		}
		childEmptyDefault := emptyDefault || needEmptyDefault
		if ordered != nil {
			if items, ok := ordered[node]; ok {
				allowedChild := make(map[*xmlElement]bool, len(node.Children))
				for _, child := range node.Children {
					allowedChild[child] = true
				}
				allowedPreserved := make(map[*xmlElement]bool, len(node.PreservedElements))
				for _, item := range node.PreservedElements {
					allowedPreserved[item] = true
				}
				emitted := make(map[*xmlElement]bool, len(node.Children)+len(node.PreservedElements))
				for _, item := range items {
					if item.element != nil {
						if allowedChild[item.element] {
							emitted[item.element] = true
							if err := encodeNode(item.element, false, isPreserved, childEmptyDefault); err != nil {
								return err
							}
						} else if allowedPreserved[item.element] {
							emitted[item.element] = true
							if err := encodeNode(item.element, false, true, childEmptyDefault); err != nil {
								return err
							}
						}
						continue
					}
					if isPreserved {
						if data, ok := item.token.(xml.CharData); ok && !xmlTextValid(string(data)) {
							return fmt.Errorf("%w: invalid generated XML text", ErrInvalid)
						}
						if err := encoder.EncodeToken(item.token); err != nil {
							return err
						}
					}
				}
				for _, child := range node.Children {
					if !emitted[child] {
						if err := encodeNode(child, false, isPreserved, childEmptyDefault); err != nil {
							return err
						}
					}
				}
				for _, item := range node.PreservedElements {
					if !emitted[item] {
						if err := encodeNode(item, false, true, childEmptyDefault); err != nil {
							return err
						}
					}
				}
				return encoder.EncodeToken(start.End())
			}
		}
		if node.Text != "" {
			if err := encoder.EncodeToken(xml.CharData(node.Text)); err != nil {
				return err
			}
		}
		for _, child := range node.Children {
			if err := encodeNode(child, false, isPreserved, childEmptyDefault); err != nil {
				return err
			}
		}
		for _, item := range node.PreservedElements {
			if err := encodeNode(item, false, true, childEmptyDefault); err != nil {
				return err
			}
		}
		return encoder.EncodeToken(start.End())
	}
	if err := encodeNode(root, true, false, false); err != nil {
		return nil, err
	}
	if err := encoder.Flush(); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// createdPut 注册已经编码的不可变数据，不修改已有的调用方切片
// 入参: pkg 内存索引, part 部件名称, media 内容类型, data 独立或不可变数据
func createdPut(pkg *packageReader, part, media string, data []byte) {
	key := strings.ToLower(part)
	pkg.parts[key] = nil
	pkg.names[key], pkg.data[key] = part, data
	if media != "" {
		pkg.overrides[key] = media
	}
}

// createdPutRelations 根据明确关系生成标准XML，忽略内容不会从其他标记中复制进来
// 入参: pkg 内存索引, source 源部件或包根, relations 关系列表, limits 上限, ctx 取消Context
// 返回: []Relationship 已校验的消费分支关系, error 关系、字符或预算错误
func createdPutRelations(pkg *packageReader, source string, relations []Relationship, limits Limits, ctx context.Context) ([]Relationship, error) {
	data, err := createdRelationshipMarkup(relations, limits, ctx)
	if err != nil {
		return nil, err
	}
	name := createdRelationshipPart(source)
	createdPut(pkg, name, opcRelsType, data)
	return pkg.relationships(source)
}

// createdRelationshipMarkup 仅序列化当前关系列表，不复制原标记中的忽略内容
// 入参: relations 关系列表, limits 资源上限, ctx 取消Context
// 返回: []byte 标准关系XML, error 字符、资源或取消错误
func createdRelationshipMarkup(relations []Relationship, limits Limits, ctx context.Context) ([]byte, error) {
	if len(relations) >= limits.MaxXMLNodes {
		return nil, fmt.Errorf("%w: relationship XML complexity", ErrLimit)
	}
	root := createdNode(opcRelsNS, "Relationships")
	for _, relation := range relations {
		child := createdNode(opcRelsNS, "Relationship")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "Id"}, Value: relation.ID}, {Name: xml.Name{Local: "Type"}, Value: relation.Type}, {Name: xml.Name{Local: "Target"}, Value: relation.Target}}
		if relation.TargetMode != "" {
			child.Attr = append(child.Attr, xml.Attr{Name: xml.Name{Local: "TargetMode"}, Value: string(relation.TargetMode)})
		}
		root.Children = append(root.Children, child)
	}
	return createdMarkup(root, limits, ctx)
}

// createdRelationshipPart 返回源部件的关系部件名，包级关系使用根目录保留名称
// 入参: source 已规范化源部件或包根
// 返回: string 关系部件名
func createdRelationshipPart(source string) string {
	if source == "/" {
		return "/_rels/.rels"
	}
	slash := strings.LastIndexByte(source, '/')
	return source[:slash+1] + "_rels/" + source[slash+1:] + ".rels"
}

// createdRelationshipIDs 建立单次分配器，避免每新增一个依赖都重建整份关系ID索引
// 入参: relations 已有关系
// 返回: func() string 返回不同有效ID的分配函数
func createdRelationshipIDs(relations []Relationship) func() string {
	ids := make(map[string]bool, len(relations))
	for _, relation := range relations {
		ids[relation.ID] = true
	}
	index := 0
	return func() string {
		for {
			index++
			id := fmt.Sprintf("R%d", index)
			if !ids[id] {
				ids[id] = true
				return id
			}
		}
	}
}

// validatePackageMedia 校验内容类型的基本形式和OPC自身媒体类型的参数限制
// 入参: value 内容类型
// 返回: error 非法内容类型错误
func validatePackageMedia(value string) error {
	media, parameters, err := mime.ParseMediaType(value)
	if err != nil || !strings.Contains(media, "/") || strings.ContainsAny(value, "\r\n\t") || strings.TrimSpace(value) != value || !xmlTextValid(value) {
		return fmt.Errorf("%w: invalid content type", ErrInvalid)
	}
	if len(parameters) != 0 && opcSpecificContentType(media) {
		return fmt.Errorf("%w: parameters on package-specific content type", ErrInvalid)
	}
	return nil
}
