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
	"crypto/sha256"
	"encoding/binary"
	"encoding/xml"
	"fmt"
	"image"
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

	"github.com/xiaoqidun/jxrgo"
)

// createdNavigationOther 等常量表示固定布局部件的导航地址角色
const (
	createdNavigationOther createdNavigationKind = iota
	createdNavigationSequence
	createdNavigationDocument
	createdNavigationPage
)

// PackageOptions 设置可编辑包的资源上限与紧凑编码选项，零值字段采用默认值
// MaxImagePixels按RGBA64等价存储容量计费，不只计算图像宽度与高度的乘积；Compact启用后对新增或替换页面及资源字典启用紧凑属性编码
type PackageOptions struct {
	Limits         Limits
	MaxImagePixels uint64
	Compact        bool
}

// AddFontOptions 设置字体嵌入时的混淆策略、内容去重、TTC/OTC集合面索引与单面提取策略
// Obfuscate为nil时默认按ODTTF混淆嵌入，设为false时仅允许无限制字体按OpenType明文嵌入
// Deduplicate为true时按内容摘要与字节比对复用已嵌入部件；CollectionIndex指定TTC/OTC目标面索引；ExtractCollectionFace为true时仅校验并提取指定集合面为独立单面字体嵌入
type AddFontOptions struct {
	Obfuscate             *bool
	Deduplicate           bool
	CollectionIndex       int
	ExtractCollectionFace bool
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
	compact        bool
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
	partHashes     map[[32]byte][]string
	fontHashes     map[[32]byte][]string
	hashPartsCount int
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

// createdNavigation 保存当前固定布局的部件角色、页数与目标锚点索引，供写出前检查内部链接与大纲目标
type createdNavigation struct {
	parts         map[string]createdNavigationKind
	pageCount     int
	docTargets    map[string]map[string]bool
	allTargets    map[string]bool
	existingParts map[string]bool
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
	compact := false
	if options != nil {
		limits = mergeLimits(limits, options.Limits)
		if options.MaxImagePixels != 0 {
			maxPixels = options.MaxImagePixels
		}
		compact = options.Compact
	}
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	p := &Package{format: format, limits: limits, maxImagePixels: maxPixels, compact: compact, sequence: "/FixedDocSeq.fdseq", parts: make(map[string]packagePart), relations: make(map[string][]Relationship), relationSizes: make(map[string]int64), names: make(map[string]bool), layout: make(map[string]bool), parents: make(map[string]int), allocated: make(map[string]int), dirty: make(map[string]bool), dirtyRels: make(map[string]bool), protected: make(map[string]bool)}
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
	if err := p.mutateWithDiscardSync(func(target *Package) error {
		targets, err := target.storePage(&value, docIndex, -1, ctx)
		if err != nil {
			return err
		}
		target.layout[strings.ToLower(part)] = true
		target.documents[docIndex].Pages = append(target.documents[docIndex].Pages, PageReference{Part: part, Width: value.Width, Height: value.Height, LinkTargets: targets})
		target.pageCount++
		target.dirty[strings.ToLower(target.documents[docIndex].Part)] = true
		target.commitName(pattern, part)
		return nil
	}); err != nil {
		return 0, err
	}
	return len(p.documents[docIndex].Pages) - 1, nil
}

// AddFont 校验字体嵌入许可后按唯一GUID路径混淆存入包中，禁止嵌入的字体返回ErrRestricted
// 入参: data 原始OpenType或TrueType字体字节
// 返回: string 混淆字体的包根URI, error 字体格式、许可、名称或资源错误
func (p *Package) AddFont(data []byte) (string, error) {
	return p.AddFontWithOptions(context.Background(), data, nil)
}

// AddFontWithOptions 按指定选项校验许可、可选单面提取、去重与混淆嵌入字体，整份TTC/OTC集合返回带#index的FontUri
// 入参: ctx 取消Context，nil采用Background, data 原始OpenType/TrueType或TTC/OTC字体字节, options 嵌入选项，nil默认混淆
// 返回: string 字体部件URI，保留集合封装时附加#index片段, error 字体格式、许可、索引、取消或资源错误
func (p *Package) AddFontWithOptions(ctx context.Context, data []byte, options *AddFontOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	obfuscate := true
	deduplicate := false
	collectionIndex := 0
	extractFace := false
	if options != nil {
		if options.Obfuscate != nil {
			obfuscate = *options.Obfuscate
		}
		deduplicate = options.Deduplicate
		collectionIndex = options.CollectionIndex
		extractFace = options.ExtractCollectionFace
	}
	isCollection, isCFF, err := validateEmbeddedFontDataWithPolicy(ctx, data, p.limits.MaxPartBytes, obfuscate, collectionIndex, extractFace)
	if err != nil {
		return "", err
	}
	if isCollection && extractFace {
		extracted, faceCFF, extractErr := extractCollectionFaceSFNT(ctx, data, uint32(collectionIndex), p.limits.MaxPartBytes)
		if extractErr != nil {
			return "", extractErr
		}
		data = extracted
		isCollection = false
		isCFF = faceCFF
	}
	media, pattern := embeddedFontMediaAndPattern(obfuscate, isCollection, isCFF)
	if deduplicate {
		if existing, found := p.findDuplicateFontLocked(data, media, obfuscate); found {
			if isCollection {
				return fmt.Sprintf("%s#%d", existing, collectionIndex), nil
			}
			return existing, nil
		}
	}
	var part string
	if obfuscate {
		part, err = allocateObfuscatedFontPart(p.available)
	} else {
		part, err = p.newName(pattern, ctx)
	}
	if err != nil {
		return "", err
	}
	payload := data
	if obfuscate {
		payload, err = ObfuscateFont(part, data)
		if err != nil {
			return "", err
		}
	}
	if err := p.editable(part); err != nil {
		return "", err
	}
	if err := p.storePart(part, media, payload, false); err != nil {
		return "", err
	}
	p.commitName(pattern, part)
	if isCollection {
		return fmt.Sprintf("%s#%d", part, collectionIndex), nil
	}
	return part, nil
}

// fontFaceHasVectorOutline 判断OpenType或TrueType字体面是否包含矢量字形轮廓表
// 入参: face 已解析的SFNT字体面
// 返回: bool 包含glyf、CFF或CFF2矢量轮廓表时为true
func fontFaceHasVectorOutline(face *fontFace) bool {
	if face == nil {
		return false
	}
	if face.cff {
		return true
	}
	if _, hasGlyf := face.tables["glyf"]; hasGlyf {
		return true
	}
	if _, hasCFF2 := face.tables["CFF2"]; hasCFF2 {
		return true
	}
	return false
}

// validateEmbeddedFontFace 校验单个字体面的OS/2嵌入、混淆及纯位图嵌入许可规则
// 入参: face 已解析的SFNT字体面, obfuscate 是否执行混淆嵌入
// 返回: error 缺失OS/2表、非法fsType、禁止嵌入、需混淆或位图限制含矢量轮廓错误
func validateEmbeddedFontFace(face *fontFace, obfuscate bool) error {
	os2, err := parseFontOS2Metrics(face)
	if err != nil {
		return err
	}
	if os2 == nil {
		return fmt.Errorf("%w: producer font needs OS/2", ErrInvalid)
	}
	rights, err := fontEmbeddingRights(os2)
	if err != nil {
		return err
	}
	if rights&2 != 0 {
		return fmt.Errorf("%w: font prohibits embedding", ErrRestricted)
	}
	if rights&0x200 != 0 && fontFaceHasVectorOutline(face) {
		return fmt.Errorf("%w: bitmap-only font prohibits vector outline embedding", ErrRestricted)
	}
	if !obfuscate && rights&0x30c != 0 {
		return fmt.Errorf("%w: font requires obfuscation", ErrRestricted)
	}
	return nil
}

// validateEmbeddedFontDataWithPolicy 按单面提取或整集合策略校验待嵌入字体的格式、索引与OS/2许可规则
// 入参: ctx 取消Context, data 原始字体字节, maxBytes 字节上限, obfuscate 是否执行混淆嵌入, collectionIndex 目标字体面索引, targetOnly 集合字体是否仅校验目标面
// 返回: bool 是否为TTC/OTC集合, bool 目标或首面是否为CFF轮廓, error 格式、索引、许可、预算或取消错误
func validateEmbeddedFontDataWithPolicy(ctx context.Context, data []byte, maxBytes int64, obfuscate bool, collectionIndex int, targetOnly bool) (bool, bool, error) {
	if err := checkContext(ctx); err != nil {
		return false, false, err
	}
	if len(data) == 0 {
		return false, false, fmt.Errorf("%w: empty font data", ErrInvalid)
	}
	if int64(len(data)) > maxBytes {
		return false, false, fmt.Errorf("%w: font byte budget", ErrLimit)
	}
	if collectionIndex < 0 {
		return false, false, fmt.Errorf("%w: negative font collection index", ErrInvalid)
	}
	face, err := parseFontFace(data, 0)
	if err != nil {
		return false, false, err
	}
	isCollection, isCFF := face.collection, face.cff
	count := uint32(1)
	if isCollection {
		count = binary.BigEndian.Uint32(data[8:12])
		if uint64(collectionIndex) >= uint64(count) {
			return false, false, fmt.Errorf("%w: font collection index out of range", ErrInvalid)
		}
		if targetOnly {
			targetFace := face
			if collectionIndex != 0 {
				targetFace, err = parseFontFace(data, uint32(collectionIndex))
				if err != nil {
					return false, false, err
				}
			}
			if err := validateEmbeddedFontFace(targetFace, obfuscate); err != nil {
				return false, false, err
			}
			return true, targetFace.cff, nil
		}
	} else if collectionIndex != 0 {
		return false, false, fmt.Errorf("%w: collection index %d on standalone font", ErrInvalid, collectionIndex)
	}
	checked := make(map[uint32]bool)
	for index := uint32(0); index < count; index++ {
		if err := checkContext(ctx); err != nil {
			return false, false, err
		}
		if index != 0 {
			face, err = parseFontFace(data, index)
			if err != nil {
				return false, false, err
			}
		}
		if checked[face.offset] {
			continue
		}
		if err := validateEmbeddedFontFace(face, obfuscate); err != nil {
			return false, false, err
		}
		checked[face.offset] = true
	}
	return isCollection, isCFF, nil
}

// extractCollectionFaceSFNT 从TTC/OTC集合中提取指定索引的独立单面SFNT字体并移除已失效的集合签名表DSIG
// 入参: ctx 取消Context, data 原始集合字体字节, collectionIndex 目标字体面索引, maxBytes 输出字节上限
// 返回: []byte 独立单面SFNT字节, bool 是否为CFF轮廓, error 索引、封装、预算或取消错误
func extractCollectionFaceSFNT(ctx context.Context, data []byte, collectionIndex uint32, maxBytes int64) ([]byte, bool, error) {
	face, err := parseFontFace(data, collectionIndex)
	if err != nil {
		return nil, false, err
	}
	tags := slices.Sorted(maps.Keys(face.tables))
	tags = slices.DeleteFunc(tags, func(tag string) bool { return tag == "DSIG" })
	out, err := assembleSFNT(ctx, face, tags, nil, maxBytes, 54)
	if err != nil {
		return nil, false, err
	}
	return out, face.cff, nil
}

// embeddedFontMediaAndPattern 按混淆标志与字体容器类型返回标准媒体类型与默认路径模板
// 入参: obfuscate 是否混淆嵌入, isCollection 是否为TTC/OTC集合, isCFF 是否为CFF轮廓
// 返回: string 内容类型, string 非混淆时的路径模板（混淆时为空串）
func embeddedFontMediaAndPattern(obfuscate, isCollection, isCFF bool) (string, string) {
	if obfuscate {
		return "application/vnd.ms-package.obfuscated-opentype", ""
	}
	ext := "ttf"
	if isCollection {
		ext = "ttc"
	} else if isCFF {
		ext = "otf"
	}
	return "application/vnd.ms-opentype", "/Resources/Fonts/%d." + ext
}

// allocateObfuscatedFontPart 生成与当前名称表不冲突的UUIDv4混淆字体部件路径
// 入参: available 检查候选路径是否可用的回调，返回nil表示可用
// 返回: string 规范化混淆字体URI, error 随机数或冲突耗尽错误
func allocateObfuscatedFontPart(available func(string) error) (string, error) {
	var raw [16]byte
	for range 1024 {
		if _, err := rand.Read(raw[:]); err != nil {
			return "", err
		}
		raw[6] = raw[6]&0x0f | 0x40
		raw[8] = raw[8]&0x3f | 0x80
		part := fmt.Sprintf("/Resources/Fonts/%X-%X-%X-%X-%X.odttf", raw[0:4], raw[4:6], raw[6:8], raw[8:10], raw[10:16])
		if available(part) == nil {
			return part, nil
		}
	}
	return "", fmt.Errorf("%w: unable to allocate unique font part", ErrLimit)
}

// extractAllocatedPatternIndex 从已分配的部件路径中提取模板%d对应的正整数编号
// 入参: pattern 含唯一%d占位的路径模板, part 已分配部件路径
// 返回: int 提取到的编号, bool 是否匹配模板且为合法整数
func extractAllocatedPatternIndex(pattern, part string) (int, bool) {
	if pattern == "" {
		return 0, false
	}
	prefix, suffix, err := packageNamePattern(pattern, nil)
	if err != nil || len(part) <= len(prefix)+len(suffix) || !strings.HasPrefix(part, prefix) || !strings.HasSuffix(part, suffix) {
		return 0, false
	}
	index, err := strconv.Atoi(part[len(prefix) : len(part)-len(suffix)])
	if err != nil {
		return 0, false
	}
	return index, true
}

// layoutPartScope 根据固定文档序列与文档索引判定源部件对应的标准打印作用域
// 入参: sequence 主序列部件URI, documents 文档索引列表, source 待判定源部件URI
// 返回: PrintScope 作业、文档、页面或未知作用域
func layoutPartScope(sequence string, documents []Document, source string) PrintScope {
	if strings.EqualFold(source, sequence) {
		return PrintScopeJob
	}
	for _, document := range documents {
		if strings.EqualFold(source, document.Part) {
			return PrintScopeDocument
		}
		for _, page := range document.Pages {
			if strings.EqualFold(source, page.Part) {
				return PrintScopePage
			}
		}
	}
	return PrintScopeUnknown
}

// ensurePartHashIndexLocked 按需惰性构建包内普通资源与字体的SHA-256哈希去重索引，须持有写锁
func (p *Package) ensurePartHashIndexLocked() {
	if p.partHashes != nil && p.fontHashes != nil && p.hashPartsCount == len(p.parts) {
		return
	}
	p.partHashes = make(map[[32]byte][]string, len(p.parts))
	p.fontHashes = make(map[[32]byte][]string)
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		p.indexPartHashLocked(key, p.parts[key])
	}
	p.hashPartsCount = len(p.parts)
}

// indexPartHashLocked 将单个部件登记到SHA-256普通索引或字体明文摘要索引，须持有写锁
// 入参: key 部件小写键, part 部件数据
func (p *Package) indexPartHashLocked(key string, part packagePart) {
	digest := sha256.Sum256(part.data)
	if !slices.Contains(p.partHashes[digest], key) {
		p.partHashes[digest] = append(p.partHashes[digest], key)
	}
	if strings.EqualFold(part.media, "application/vnd.ms-package.obfuscated-opentype") {
		if len(part.data) >= 32 {
			if xorKey, err := FontObfuscationKey(part.name); err == nil {
				var prefix [32]byte
				copy(prefix[:], part.data[:32])
				for i := range 32 {
					prefix[i] ^= xorKey[i%len(xorKey)]
				}
				h := sha256.New()
				_, _ = h.Write(prefix[:])
				_, _ = h.Write(part.data[32:])
				var plainDigest [32]byte
				h.Sum(plainDigest[:0])
				if !slices.Contains(p.fontHashes[plainDigest], key) {
					p.fontHashes[plainDigest] = append(p.fontHashes[plainDigest], key)
				}
			}
		}
		return
	}
	if strings.EqualFold(part.media, "application/vnd.ms-opentype") {
		if !slices.Contains(p.fontHashes[digest], key) {
			p.fontHashes[digest] = append(p.fontHashes[digest], key)
		}
	}
}

// invalidatePartHashIndexLocked 清空包级哈希去重索引以在下次去重时按最新状态重建，须持有写锁
func (p *Package) invalidatePartHashIndexLocked() {
	p.partHashes = nil
	p.fontHashes = nil
	p.hashPartsCount = 0
}

// findDuplicateFontLocked 在已存入部件中按SHA-256索引、媒体类型与完整字节查找可复用的同类型字体部件
// 入参: raw 原始未混淆字体字节, media 目标媒体类型, obfuscated 是否混淆部件
// 返回: string 已存在的字体部件URI, bool 是否命中复用
func (p *Package) findDuplicateFontLocked(raw []byte, media string, obfuscated bool) (string, bool) {
	p.ensurePartHashIndexLocked()
	digest := sha256.Sum256(raw)
	candidates := p.fontHashes[digest]
	for _, key := range candidates {
		part, exists := p.parts[key]
		if !exists || !strings.EqualFold(part.media, media) || len(part.data) != len(raw) {
			continue
		}
		candidate := part.data
		if obfuscated {
			if len(candidate) < 32 {
				continue
			}
			xorKey, err := FontObfuscationKey(part.name)
			if err != nil {
				continue
			}
			var prefix [32]byte
			copy(prefix[:], candidate[:32])
			for i := range 32 {
				prefix[i] ^= xorKey[i%len(xorKey)]
			}
			if !bytes.Equal(prefix[:], raw[:32]) || !bytes.Equal(candidate[32:], raw[32:]) {
				continue
			}
			return part.name, true
		}
		if bytes.Equal(candidate, raw) {
			return part.name, true
		}
	}
	return "", false
}

// findDuplicatePartLocked 在已存入部件中按SHA-256索引、媒体类型与完整字节查找可复用的相同资源部件
// 入参: media 目标媒体类型, data 原始资源字节
// 返回: string 已存在的部件URI, bool 是否命中复用
func (p *Package) findDuplicatePartLocked(media string, data []byte) (string, bool) {
	p.ensurePartHashIndexLocked()
	digest := sha256.Sum256(data)
	for _, key := range p.partHashes[digest] {
		part, exists := p.parts[key]
		if !exists || !strings.EqualFold(part.media, media) || len(part.data) != len(data) {
			continue
		}
		if bytes.Equal(part.data, data) {
			return part.name, true
		}
	}
	return "", false
}

// AddImage 按魔数识别PNG、JPEG、TIFF或JPEG XR图像并分配唯一路径存入包中
// 入参: data 原始图像字节
// 返回: string 图像部件的包根URI, error 格式、预算或名称冲突错误
func (p *Package) AddImage(data []byte) (string, error) {
	return p.AddImageWithOptions(context.Background(), data, nil)
}

// AddImageWithOptions 按魔数识别图像并支持内容去重后存入包中
// 入参: ctx 取消Context，nil采用Background, data 原始图像字节, options 嵌入选项，nil禁用去重
// 返回: string 图像部件的包根URI, error 格式、预算、取消或名称冲突错误
func (p *Package) AddImageWithOptions(ctx context.Context, data []byte, options *AddImageOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
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
	return p.storeDeduplicatedResourceLocked(ctx, "/Resources/Images/%d."+ext, media, data, options != nil && options.Deduplicate)
}

// AddGoImage 将Go标准图像按指定格式、质量、分辨率与ICC配置编码并嵌入包中，支持内容去重
// 入参: ctx 取消Context，nil采用Background, img 标准Go图像, options 编码与去重选项，nil自动选择格式
// 返回: string 图像部件的包根URI, error 编码、许可、预算或取消错误
func (p *Package) AddGoImage(ctx context.Context, img image.Image, options *ImageEncodeOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	data, media, ext, err := encodeGoImageWithLimits(ctx, img, options, p.limits.MaxPartBytes, p.maxImagePixels)
	if err != nil {
		return "", err
	}
	return p.storeDeduplicatedResourceLocked(ctx, "/Resources/Images/%d."+ext, media, data, options != nil && options.Deduplicate)
}

// AddImageFromRows 通过逐行流式回调对接jxrgo.EncodeRows编码为JPEG XR图像并嵌入包中
// 入参: ctx 取消Context，nil采用Background, info JPEG XR图像头信息, read 按行读取回调, options JPEG XR编码选项，nil采用默认值
// 返回: string 图像部件的包根URI, error 编码、预算或取消错误
func (p *Package) AddImageFromRows(ctx context.Context, info jxrgo.Info, read jxrgo.RasterRowReader, options *jxrgo.EncodeOptions) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if read == nil {
		return "", fmt.Errorf("%w: missing row reader", ErrInvalid)
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	if err := validateImageRowsInfoLimits(info, p.maxImagePixels); err != nil {
		return "", err
	}
	var cfg jxrgo.EncodeOptions
	if options != nil {
		cfg = *options
	}
	if cfg.MaxOutputBytes == 0 || cfg.MaxOutputBytes > uint64(p.limits.MaxPartBytes) {
		cfg.MaxOutputBytes = uint64(p.limits.MaxPartBytes)
	}
	if cfg.Limits.MaxPixels == 0 || cfg.Limits.MaxPixels > p.maxImagePixels {
		cfg.Limits.MaxPixels = p.maxImagePixels
	}
	var buf bytes.Buffer
	counted := packageOutput{writer: &buf, context: ctx, limit: p.limits.MaxPartBytes}
	if err := jxrgo.EncodeRows(ctx, &counted, info, read, &cfg); err != nil {
		return "", err
	}
	return p.storeAllocatedResourceLocked(ctx, "/Resources/Images/%d.jxr", "image/vnd.ms-photo", buf.Bytes())
}

// AddPNGFromRows 通过逐行扫描回调流式编码标准PNG图像并嵌入包中
// 入参: ctx 取消Context，nil采用Background, options 图像尺寸、位深、色彩模型、分辨率与ICC配置, readRow 按零基行号填充原始扫描行的回调
// 返回: string 图像部件的包根URI, error 参数、回调、编码、预算或取消错误
func (p *Package) AddPNGFromRows(ctx context.Context, options StreamImageRowOptions, readRow func(y int, dst []byte) error) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if readRow == nil {
		return "", fmt.Errorf("%w: missing PNG row reader", ErrInvalid)
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	var buf bytes.Buffer
	counted := packageOutput{writer: &buf, context: ctx, limit: p.limits.MaxPartBytes}
	if err := encodePNGFromRowsTo(ctx, &counted, options, p.maxImagePixels, readRow); err != nil {
		return "", err
	}
	return p.storeAllocatedResourceLocked(ctx, "/Resources/Images/%d.png", "image/png", buf.Bytes())
}

// AddTIFFFromRows 通过逐行扫描回调按多Strip编码Little-Endian Baseline TIFF并嵌入包中
// 入参: ctx 取消Context，nil采用Background, options 图像尺寸、位深、色彩模型、压缩方式、分辨率与ICC配置, readRow 按零基行号填充原始像素的回调，16位样本按大端字节序
// 返回: string 图像部件的包根URI, error 参数、回调、编码、预算或取消错误
func (p *Package) AddTIFFFromRows(ctx context.Context, options StreamImageRowOptions, readRow func(y int, dst []byte) error) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if readRow == nil {
		return "", fmt.Errorf("%w: missing TIFF row reader", ErrInvalid)
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	var buf bytes.Buffer
	counted := packageOutput{writer: &buf, context: ctx, limit: p.limits.MaxPartBytes}
	if err := encodeTIFFFromRowsTo(ctx, &counted, options, p.limits.MaxPartBytes, p.maxImagePixels, readRow); err != nil {
		return "", err
	}
	return p.storeAllocatedResourceLocked(ctx, "/Resources/Images/%d.tif", "image/tiff", buf.Bytes())
}

// validateImageRowsInfoLimits 前置校验逐行流式编码图像头尺寸与像素预算上限
// 入参: info JPEG XR图像头信息, maxPixels 像素总数上限
// 返回: error 尺寸非法或像素超限错误
func validateImageRowsInfoLimits(info jxrgo.Info, maxPixels uint64) error {
	if info.Bounds.Empty() {
		return fmt.Errorf("%w: empty image bounds", ErrInvalid)
	}
	if maxPixels == 0 {
		maxPixels = DefaultImageOptions().MaxPixels
	}
	w, h := info.Bounds.Dx(), info.Bounds.Dy()
	if w > rasterMaxDimension || h > rasterMaxDimension || uint64(w) > maxPixels/uint64(h) {
		return fmt.Errorf("%w: image exceeds MaxImagePixels", ErrLimit)
	}
	return nil
}

// AddColorProfile 校验ICC颜色配置文件并分配唯一路径存入包中
// 入参: data 原始ICC颜色配置文件字节
// 返回: string 配置文件部件的包根URI, error 格式、预算或名称冲突错误
func (p *Package) AddColorProfile(data []byte) (string, error) {
	return p.AddColorProfileWithOptions(context.Background(), data, false)
}

// AddColorProfileWithOptions 校验ICC颜色配置文件并支持按内容去重后存入包中
// 入参: ctx 取消Context，nil采用Background, data 原始ICC颜色配置文件字节, deduplicate 是否按内容去重复用已有部件
// 返回: string 配置文件部件的包根URI, error 格式、预算、取消或名称冲突错误
func (p *Package) AddColorProfileWithOptions(ctx context.Context, data []byte, deduplicate bool) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
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
	if _, err := validateCreatedICCProfile(data, ctx); err != nil {
		return "", err
	}
	return p.storeDeduplicatedResourceLocked(ctx, "/Resources/Profiles/%d.icc", "application/vnd.ms-color.iccprofile", data, deduplicate)
}

// storeDeduplicatedResourceLocked 在持有写锁时按可选字节去重复用已有部件或分配路径原子存储
// 入参: ctx 已规范化取消Context, pattern 路径模板, media 内容类型, data 资源字节, deduplicate 是否启用内容去重
// 返回: string 资源部件URI, error 名称、预算、许可或取消错误
func (p *Package) storeDeduplicatedResourceLocked(ctx context.Context, pattern, media string, data []byte, deduplicate bool) (string, error) {
	if deduplicate {
		if existing, found := p.findDuplicatePartLocked(media, data); found {
			return existing, nil
		}
	}
	return p.storeAllocatedResourceLocked(ctx, pattern, media, data)
}

// AddResourceDictionary 编码共享远程资源字典并分配唯一部件路径存入包中
// 入参: ctx 取消Context，nil采用Background, dict 资源字典模型，Source必须为空
// 返回: string 资源字典部件的包根URI, error 模型、编码、预算或取消错误
func (p *Package) AddResourceDictionary(ctx context.Context, dict *ResourceDictionary) (string, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return "", err
	}
	if dict == nil {
		return "", fmt.Errorf("%w: nil resource dictionary", ErrInvalid)
	}
	if err := p.lock(); err != nil {
		return "", err
	}
	defer p.mu.Unlock()
	const pattern = "/Resources/Dictionaries/%d.dict"
	part, err := p.newName(pattern, ctx)
	if err != nil {
		return "", err
	}
	_, data, err := encodeResourceDictionaryTree(ctx, dict, &EncodeOptions{Format: p.format, Limits: p.limits, Part: part, Compact: p.compact})
	if err != nil {
		return "", err
	}
	if err := p.editable(part); err != nil {
		return "", err
	}
	if err := p.storePart(part, resourceDictionaryContentType, data, false); err != nil {
		return "", err
	}
	p.commitName(pattern, part)
	return part, nil
}

// storeAllocatedResourceLocked 在持有写锁时按模板分配资源部件路径并原子存储
// 入参: ctx 取消Context, pattern 含唯一%d占位符的部件路径模板, media 内容类型, data 部件字节
// 返回: string 分配后的部件URI, error 分配、许可或预算错误
func (p *Package) storeAllocatedResourceLocked(ctx context.Context, pattern, media string, data []byte) (string, error) {
	part, err := p.newName(pattern, ctx)
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

// writeReader 为包写出准备已校验只读快照，启用SubsetFonts时在独立副本上执行子集化并直接复用已校验快照
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
	cfg := FontSubsetOptions{MaxBytes: clone.limits.MaxPartBytes, MaxWork: 1 << 20, CompactGIDs: options.CompactFontGIDs}
	_, view, err := clone.subsetFontsWithReader(ctx, nil, cfg, true)
	if err != nil {
		return nil, err
	}
	return view, nil
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
	snapshot := &Package{format: p.format, limits: p.limits, sequence: p.sequence, maxImagePixels: p.maxImagePixels, compact: p.compact, parts: maps.Clone(p.parts), relations: maps.Clone(p.relations), documents: slices.Clone(p.documents), original: p.original, originalRels: p.originalRels, comment: p.comment, dirty: maps.Clone(p.dirty), dirtyRels: maps.Clone(p.dirtyRels)}
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

// storePage 完成页面编码及显式链接目标校验后原子替换部件，直接复用编码节点树消除写后二次解码
// 入参: page 带有目标部件名的模型, docIndex 所属文档序号, replacePageIndex 替换页面序号，新增页传-1, ctx 取消Context
// 返回: []string 经校验的显式页面链接目标, error 编码、链接目标或预算错误
func (p *Package) storePage(page *Page, docIndex, replacePageIndex int, ctx context.Context) ([]string, error) {
	root, data, err := encodePageTree(ctx, page, &EncodeOptions{Format: p.format, Limits: p.limits, Compact: p.compact})
	if err != nil {
		return nil, err
	}
	targets, err := validateExplicitLinkTargetsForPage(p.format, p.documents, page.LinkTargets, createdPageTargets(root), docIndex, replacePageIndex)
	if err != nil {
		return nil, err
	}
	if err := p.storePart(page.Part, fixedContentType("fixedpage"), data, false); err != nil {
		return nil, err
	}
	return targets, nil
}

// validateExplicitLinkTargetsForPage 校验显式LinkTargets名称均存在于当前页内且在XPS 1.0下不与同文档其它页重名
// 入参: format 文档格式, documents 文档列表, declared 调用方显式声明的链接目标列表, pageNames 页内可寻址元素名称列表, docIndex 所属文档序号, replacePageIndex 替换页面序号，新增页传-1
// 返回: []string 独立拷贝的链接目标列表，未声明时为nil, error 缺失、重复或命名冲突错误
func validateExplicitLinkTargetsForPage(format Format, documents []Document, declared, pageNames []string, docIndex, replacePageIndex int) ([]string, error) {
	if len(declared) == 0 {
		return nil, nil
	}
	present := make(map[string]bool, len(pageNames))
	for _, name := range pageNames {
		present[name] = true
	}
	var otherTargets map[string]bool
	if format == FormatXPS && docIndex >= 0 && docIndex < len(documents) {
		otherTargets = make(map[string]bool)
		for i, ref := range documents[docIndex].Pages {
			if i == replacePageIndex {
				continue
			}
			for _, name := range ref.LinkTargets {
				otherTargets[name] = true
			}
		}
	}
	seen := make(map[string]bool, len(declared))
	result := make([]string, 0, len(declared))
	for _, target := range declared {
		if target == "" || !present[target] {
			return nil, fmt.Errorf("%w: LinkTarget %q does not match any element Name on page", ErrInvalid, target)
		}
		if seen[target] {
			return nil, fmt.Errorf("%w: duplicate LinkTarget %q on page", ErrInvalid, target)
		}
		if format == FormatXPS {
			if !xmlNCName(target) {
				return nil, fmt.Errorf("%w: invalid XPS LinkTarget Name %q", ErrInvalid, target)
			}
			if otherTargets[target] {
				return nil, fmt.Errorf("%w: duplicate XPS LinkTarget %q across document pages", ErrInvalid, target)
			}
		}
		seen[target] = true
		result = append(result, target)
	}
	return result, nil
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
	registry := partNameRegistry{names: p.names, parents: p.parents}
	return registry.available(part)
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
	if err := validatePackageMediaForFormat(p.format, media); err != nil {
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
	stored := packagePart{name: part, media: media, data: bytes.Clone(data)}
	p.parts[key] = stored
	if !exists {
		p.registerName(part)
	}
	p.total = size + int64(len(data))
	p.dirty[key] = true
	delete(p.deleted, key)
	if exists {
		p.invalidatePartHashIndexLocked()
	} else if p.partHashes != nil && p.fontHashes != nil {
		p.indexPartHashLocked(key, stored)
		p.hashPartsCount = len(p.parts)
	}
	return nil
}

// registerName 累计祖先名称的占用，部件派生冲突检查不反复扫描整个包
// 入参: part 已规范化的新部件名称
func (p *Package) registerName(part string) {
	registry := partNameRegistry{names: p.names, parents: p.parents}
	registry.register(part)
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

// colorToSRGB 将标准颜色量化转换为8位非预乘sRGB颜色
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

// AddCanvas 向页面追加不透明画布容器元素，页面为nil时返回nil
// 返回: *Canvas 新建并已追加的画布元素
func (p *Page) AddCanvas() *Canvas {
	if p == nil {
		return nil
	}
	canvas := NewCanvas()
	p.Elements = append(p.Elements, canvas)
	return canvas
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

// newCreatedNavigation 按已校验的序列、文档、链接目标与现存部件建立导航索引，不读取页面内容
// 入参: r 当前包快照, ctx 取消Context
// 返回: *createdNavigation 只读角色与目标索引, error 取消错误
func newCreatedNavigation(r *Reader, ctx context.Context) (*createdNavigation, error) {
	n := &createdNavigation{
		parts:      make(map[string]createdNavigationKind, len(r.documents)+len(r.pages)+1),
		pageCount:  len(r.pages),
		docTargets: make(map[string]map[string]bool, len(r.documents)),
		allTargets: make(map[string]bool),
	}
	if r.pkg != nil {
		n.existingParts = make(map[string]bool, len(r.pkg.parts))
		for key := range r.pkg.parts {
			n.existingParts[key] = true
		}
	}
	n.parts[strings.ToLower(r.sequence)] = createdNavigationSequence
	for _, document := range r.documents {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		docKey := strings.ToLower(document.Part)
		n.parts[docKey] = createdNavigationDocument
		targets := make(map[string]bool)
		for _, page := range document.Pages {
			for _, target := range page.LinkTargets {
				targets[target] = true
				n.allTargets[target] = true
			}
		}
		n.docTargets[docKey] = targets
	}
	for _, page := range r.pages {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		n.parts[strings.ToLower(page.Part)] = createdNavigationPage
	}
	return n, nil
}

// validateCollect 检查页面及资源定义中的内部链接，onErr非nil时按节点非短路收集诊断
// 入参: page 页面部件URI, graph 完整资源图, ctx 取消Context, onErr 非短路错误收集回调，nil时遇错即返回
// 返回: error 导航地址、URI或取消错误
func (n *createdNavigation) validateCollect(page string, graph *resourceGraph, ctx context.Context, onErr func(part, element, attr string, err error) error) error {
	for _, node := range graph.Nodes {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if node.Name.Local != "Canvas" && node.Name.Local != "Path" && node.Name.Local != "Glyphs" {
			continue
		}
		if target, present := node.attribute("FixedPage.NavigateUri"); present {
			if err := n.target(page, target); err != nil {
				wrapped := &PartError{Part: graph.Parts[node], Element: node.Name.Local, Err: fmt.Errorf("FixedPage.NavigateUri: %w", err)}
				if onErr == nil {
					return wrapped
				}
				if cancelErr := onErr(graph.Parts[node], node.Name.Local, "FixedPage.NavigateUri", wrapped); cancelErr != nil {
					return cancelErr
				}
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

// outlineTarget 校验大纲书签OutlineEntry.Target的目标部件存在性、页码边界与LinkTarget锚点存在性
// 入参: source 文档结构部件URI, value 原始OutlineTarget声明
// 返回: error 空地址、URI语法、部件缺失、页码越界或锚点缺失错误
func (n *createdNavigation) outlineTarget(source, value string) error {
	value = structureURI(value)
	if value == "" {
		return fmt.Errorf("%w: empty outline target URI on %s", ErrInvalid, source)
	}
	if linkExternal(value) {
		return nil
	}
	uri, err := url.Parse(value)
	if err != nil {
		return fmt.Errorf("%w: outline target URI: %w", ErrInvalid, err)
	}
	part := source
	if uri.Path != "" {
		part, err = resolvePart(source, uri.EscapedPath())
		if err != nil {
			return err
		}
	}
	partKey := strings.ToLower(part)
	kind := n.parts[partKey]
	if kind == createdNavigationOther {
		if n.existingParts != nil && !n.existingParts[partKey] {
			return fmt.Errorf("%w: outline target part %s does not exist", ErrInvalid, part)
		}
		return nil
	}
	if uri.Fragment == "" {
		return nil
	}
	if linkPageNumber(uri.Fragment) {
		if kind != createdNavigationSequence {
			return fmt.Errorf("%w: M9.8 page address must target the fixed document sequence", ErrInvalid)
		}
		number, parseErr := strconv.ParseUint(uri.Fragment, 10, 64)
		if parseErr != nil || number < 1 || number > uint64(n.pageCount) {
			return fmt.Errorf("%w: outline page number #%s out of range (1..%d)", ErrInvalid, uri.Fragment, n.pageCount)
		}
		return nil
	}
	if kind == createdNavigationPage {
		return fmt.Errorf("%w: M9.4 named address must target a fixed document or sequence", ErrInvalid)
	}
	if kind == createdNavigationDocument {
		if !n.docTargets[partKey][uri.Fragment] {
			return fmt.Errorf("%w: outline LinkTarget %q does not exist in %s", ErrInvalid, uri.Fragment, part)
		}
	} else if kind == createdNavigationSequence {
		if !n.allTargets[uri.Fragment] {
			return fmt.Errorf("%w: outline LinkTarget %q does not exist in %s", ErrInvalid, uri.Fragment, part)
		}
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
	if index, ok := extractAllocatedPatternIndex(pattern, part); ok {
		p.allocated[pattern] = index
	}
}

// validateCreatedFontsCollect 校验页面资源图中所有被引用字体面的封装、度量及嵌入许可，onErr非nil时按节点非短路收集诊断
// 入参: cache 本次快照的字体缓存, graph 完整页面资源图, format 文档方言, ctx 取消Context, onErr 非短路错误收集回调，nil时遇错即返回
// 返回: []string 需要Restricted Font关系的字体部件, error 字体、嵌入规则或取消错误
func validateCreatedFontsCollect(cache *fontCache, graph *resourceGraph, format Format, ctx context.Context, onErr func(part, element, attr string, err error) error) ([]string, error) {
	var restricted []string
	seen := make(map[string]bool)
	parser := newSceneParser(format, graph)
	remaining := cache.pkg.limits.MaxXMLNodes
	checkedGlyphs := make(map[fontCacheKey]map[uint16]bool)
	report := func(part, element, attr string, err error) (bool, error) {
		if onErr == nil {
			return true, err
		}
		if cancelErr := onErr(part, element, attr, err); cancelErr != nil {
			return true, cancelErr
		}
		return false, nil
	}
	for _, node := range graph.Nodes {
		if node.Name.Local != "Glyphs" {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		nodePart := graph.Parts[node]
		text, _ := node.attribute("FontUri")
		uri, index, present, err := ParseFontURI(strings.Trim(text, " \t\r\n"))
		if err != nil {
			if stop, retErr := report(nodePart, "Glyphs", "FontUri", err); stop {
				return nil, retErr
			}
			continue
		}
		part, err := resolvePart(nodePart, uri)
		if err != nil {
			if stop, retErr := report(nodePart, "Glyphs", "FontUri", err); stop {
				return nil, retErr
			}
			continue
		}
		source, err := cache.load(&Glyphs{FontPart: part, CollectionIndex: index, HasCollectionIndex: present})
		if err != nil {
			if stop, retErr := report(part, "Glyphs", "FontUri", err); stop {
				return nil, retErr
			}
			continue
		}
		key := fontCacheKey{strings.ToLower(part), index}
		if err := cache.validateCreated(key, source.face); err != nil {
			if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: err}); stop {
				return nil, retErr
			}
			continue
		}
		glyphs, err := parser.glyphValue(node, ElementProperties{Part: nodePart, Opacity: 1})
		if err != nil {
			if stop, retErr := report(nodePart, "Glyphs", "FontUri", err); stop {
				return nil, retErr
			}
			continue
		}
		run, err := resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, source.glyphYMax, remaining, func() error { return checkContext(ctx) })
		if err != nil {
			if stop, retErr := report(nodePart, "Glyphs", "Indices", &PartError{Part: nodePart, Element: "Glyphs", Err: err}); stop {
				return nil, retErr
			}
			continue
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
					checkedGlyphs[key][glyph.gid] = true
					if _, err := source.glyphOutline(glyph.gid); err != nil {
						if stop, retErr := report(part, "Glyphs", "Indices", &PartError{Part: part, Err: err}); stop {
							return nil, retErr
						}
					}
				}
			}
		}
		if source.metrics.os2 == nil {
			if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: fmt.Errorf("%w: producer font needs OS/2", ErrInvalid)}); stop {
				return nil, retErr
			}
			continue
		}
		rights, err := fontEmbeddingRights(source.metrics.os2)
		if err != nil {
			if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: err}); stop {
				return nil, retErr
			}
			continue
		}
		if rights&2 != 0 {
			if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: fmt.Errorf("%w: font prohibits embedding", ErrInvalid)}); stop {
				return nil, retErr
			}
			continue
		}
		if rights&0x30c != 0 {
			media, err := cache.pkg.contentType(part)
			if err != nil {
				if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: err}); stop {
					return nil, retErr
				}
				continue
			}
			if !strings.EqualFold(media, "application/vnd.ms-package.obfuscated-opentype") {
				if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: fmt.Errorf("%w: font requires obfuscation", ErrInvalid)}); stop {
					return nil, retErr
				}
				continue
			}
		}
		if rights&0x200 != 0 {
			if fontFaceHasVectorOutline(source.face) {
				if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: fmt.Errorf("%w: bitmap-only embedding contains outlines", ErrInvalid)}); stop {
					return nil, retErr
				}
				continue
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
				if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: err}); stop {
					return nil, retErr
				}
				continue
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
				if stop, retErr := report(part, "Glyphs", "FontUri", &PartError{Part: part, Err: fmt.Errorf("%w: bitmap-only font has no embedded bitmap", ErrInvalid)}); stop {
					return nil, retErr
				}
				continue
			}
		}
		if rights&4 != 0 && !seen[key.part] {
			seen[key.part] = true
			restricted = append(restricted, part)
		}
	}
	return restricted, nil
}

// validateCreatedResourcesCollect 复用已提取依赖列表校验页面引用的图像与ICC资源，onErr非nil时按部件非短路收集诊断
// 入参: pkg 部件快照, graph 完整页面资源图, resources 已收集页面依赖列表, checked 已检查部件, channels 配置文件的输入分量数, failedProfiles 已损坏无法解析的ICC部件小写键集合, ctx 取消Context, onErr 非短路错误收集回调，nil时遇错即返回
// 返回: error 资源、解码、预算或取消错误
func (p *Package) validateCreatedResourcesCollect(pkg *packageReader, graph *resourceGraph, resources []requiredResource, checked map[string]bool, channels map[string]uint32, failedProfiles map[string]bool, ctx context.Context, onErr func(part, element, attr string, err error) error) error {
	report := func(part, element, attr string, err error) (bool, error) {
		if onErr == nil {
			return true, err
		}
		if cancelErr := onErr(part, element, attr, err); cancelErr != nil {
			return true, cancelErr
		}
		return false, nil
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
		checked[key] = true
		partKey := strings.ToLower(resource.Part)
		media, mediaErr := pkg.contentType(resource.Part)
		if mediaErr != nil {
			if resource.Kind == requiredProfile && failedProfiles != nil {
				failedProfiles[partKey] = true
			}
			if onErr == nil {
				return &PartError{Part: resource.Part, Err: mediaErr}
			}
			continue
		}
		if !requiredResourceMedia(resource.Kind, media) {
			if resource.Kind == requiredProfile && failedProfiles != nil {
				failedProfiles[partKey] = true
			}
			if onErr == nil {
				return &PartError{Part: resource.Part, Err: fmt.Errorf("%w: unexpected resource content type %q for %s", ErrInvalid, media, resource.Part)}
			}
			continue
		}
		data, err := pkg.readPart(resource.Part)
		if err != nil {
			if resource.Kind == requiredProfile && failedProfiles != nil {
				failedProfiles[partKey] = true
			}
			if stop, retErr := report(resource.Part, resource.Element, resource.Attribute, &PartError{Part: resource.Part, Err: err}); stop {
				return retErr
			}
			continue
		}
		if resource.Kind == requiredProfile {
			profile, err := validateCreatedICCProfile(data, ctx)
			if err != nil {
				if failedProfiles != nil {
					failedProfiles[partKey] = true
				}
				if stop, retErr := report(resource.Part, resource.Element, resource.Attribute, &PartError{Part: resource.Part, Err: err}); stop {
					return retErr
				}
				continue
			}
			channels[partKey] = uint32(profile.inputChannels())
		} else {
			img, err := decodeRasterImageContext(ctx, data, media, p.maxImagePixels)
			if err == nil && len(img.profile) != 0 {
				profile := img.profile
				if img.profileCompressed {
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
			if err != nil {
				if stop, retErr := report(resource.Part, resource.Element, resource.Attribute, &PartError{Part: resource.Part, Err: err}); stop {
					return retErr
				}
			}
		}
	}
	return validateCreatedContextColorsCollect(graph, channels, failedProfiles, ctx, onErr)
}

// validateCreatedContextColorsCollect 检查颜色分量与ICC输入是否匹配，跳过已损坏ICC并支持非短路收集诊断
// 入参: graph 包含远程字典的页面资源图, channels 已校验配置文件的输入分量数, failedProfiles 已损坏无法解析的ICC部件小写键集合, ctx 取消Context, onErr 非短路错误收集回调，nil时遇错即返回
// 返回: error 颜色、引用、分量数量或取消错误
func validateCreatedContextColorsCollect(graph *resourceGraph, channels map[string]uint32, failedProfiles map[string]bool, ctx context.Context, onErr func(part, element, attr string, err error) error) error {
	report := func(part, element, attr string, err error) (bool, error) {
		if onErr == nil {
			return true, err
		}
		if cancelErr := onErr(part, element, attr, err); cancelErr != nil {
			return true, cancelErr
		}
		return false, nil
	}
	for _, node := range graph.Nodes {
		if err := checkContext(ctx); err != nil {
			return err
		}
		nodePart := graph.Parts[node]
		for _, attribute := range node.Attr {
			if attribute.Name.Space != "" || !requiredColorAttribute(node.Name.Local, attribute.Name.Local) || graph.Bindings[node][attribute.Name.Local] != nil {
				continue
			}
			if _, reference, err := parseResourceReference(attribute.Value); err != nil {
				if stop, retErr := report(nodePart, node.Name.Local, attribute.Name.Local, err); stop {
					return retErr
				}
				continue
			} else if reference {
				continue
			}
			value, err := parseBrushColor(attribute.Value, node.Name.Space)
			if err != nil {
				if stop, retErr := report(nodePart, node.Name.Local, attribute.Name.Local, err); stop {
					return retErr
				}
				continue
			}
			if value.Space != ColorContext {
				continue
			}
			part, err := resolvePart(nodePart, value.ProfileURI)
			if err != nil {
				if stop, retErr := report(nodePart, node.Name.Local, attribute.Name.Local, err); stop {
					return retErr
				}
				continue
			}
			profileKey := strings.ToLower(part)
			if failedProfiles[profileKey] {
				continue
			}
			count, present := channels[profileKey]
			if !present || count != uint32(len(value.Components)) {
				mismatchErr := &PartError{Part: nodePart, Element: node.Name.Local, Err: fmt.Errorf("%w: %s color components do not match ICC profile %s", ErrInvalid, attribute.Name.Local, part)}
				if stop, retErr := report(nodePart, node.Name.Local, attribute.Name.Local, mismatchErr); stop {
					return retErr
				}
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
	navigation, err := newCreatedNavigation(g.reader, ctx)
	if err != nil {
		return err
	}
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
			if structure.Outline != nil {
				for _, entry := range structure.Outline.Entries {
					if err := g.step(1); err != nil {
						return err
					}
					if err := navigation.outlineTarget(structure.Part, entry.Target); err != nil {
						return &PartError{Part: structure.Part, Element: "OutlineEntry", Err: err}
					}
				}
			}
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

// resolveLayoutPartName 在文档序列与全部固定文档及页面中按小写键查找原始大小写的规范部件名
// 入参: sequence 文档序列部件名, documents 固定文档列表, key 小写部件键
// 返回: string 原始大小写部件名，未匹配时为空
func resolveLayoutPartName(sequence string, documents []Document, key string) string {
	if strings.EqualFold(sequence, key) {
		return sequence
	}
	for _, document := range documents {
		if strings.EqualFold(document.Part, key) {
			return document.Part
		}
		for _, page := range document.Pages {
			if strings.EqualFold(page.Part, key) {
				return page.Part
			}
		}
	}
	return ""
}

// buildFixedDocumentPageContentNode 构造单个FixedDocument的PageContent元素节点
// 入参: format 文档方言, docPart 所属固定文档URI, page 页面引用信息
// 返回: *xmlElement PageContent节点, error 相对路径错误
func buildFixedDocumentPageContentNode(format Format, docPart string, page PageReference) (*xmlElement, error) {
	ns := formatNamespace(format)
	child := createdNode(ns, "PageContent")
	pageSource, err := relativePart(docPart, page.Part)
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
		container := createdNode(ns, "PageContent.LinkTargets")
		for _, name := range page.LinkTargets {
			target := createdNode(ns, "LinkTarget")
			target.Attr = []xml.Attr{{Name: xml.Name{Local: "Name"}, Value: name}}
			container.Children = append(container.Children, target)
		}
		child.Children = []*xmlElement{container}
	}
	return child, nil
}

// buildFixedDocumentNode 构造单个FixedDocument根节点及其全部PageContent子元素
// 入参: format 文档方言, doc 固定文档索引
// 返回: *xmlElement FixedDocument根节点, error 相对路径错误
func buildFixedDocumentNode(format Format, doc Document) (*xmlElement, error) {
	root := createdNode(formatNamespace(format), "FixedDocument")
	for _, page := range doc.Pages {
		child, err := buildFixedDocumentPageContentNode(format, doc.Part, page)
		if err != nil {
			return nil, err
		}
		root.Children = append(root.Children, child)
	}
	return root, nil
}

// buildFixedDocumentSequenceNode 构造FixedDocumentSequence根节点及其全部DocumentReference子元素
// 入参: format 文档方言, sequence 文档序列URI, documents 固定文档列表
// 返回: *xmlElement FixedDocumentSequence根节点, error 相对路径错误
func buildFixedDocumentSequenceNode(format Format, sequence string, documents []Document) (*xmlElement, error) {
	ns := formatNamespace(format)
	root := createdNode(ns, "FixedDocumentSequence")
	for _, document := range documents {
		reference := createdNode(ns, "DocumentReference")
		documentSource, err := relativePart(sequence, document.Part)
		if err != nil {
			return nil, err
		}
		reference.Attr = []xml.Attr{{Name: xml.Name{Local: "Source"}, Value: documentSource}}
		root.Children = append(root.Children, reference)
	}
	return root, nil
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
	if part, exists := p.parts[source]; exists && part.name != "" {
		return part.name
	}
	if name := resolveLayoutPartName(p.sequence, p.documents, source); name != "" {
		return name
	}
	return source
}

// validateRequiredResourcesCollect 复用已收集依赖列表校验页面RequiredResource关系及媒体类型匹配，onErr非nil时按条目非短路收集诊断
// 入参: pagePart 规范页面部件URI, dependencies 已收集页面依赖列表, onErr 非短路错误收集回调，nil时遇错即返回
// 返回: error 关系、目标、媒体类型或取消错误
func (r *Reader) validateRequiredResourcesCollect(pagePart string, dependencies []requiredResource, onErr func(part, element, attr string, err error) error) error {
	report := func(part, element, attr string, err error) (bool, error) {
		if onErr == nil {
			return true, err
		}
		if cancelErr := onErr(part, element, attr, err); cancelErr != nil {
			return true, cancelErr
		}
		return false, nil
	}
	relations, err := r.pkg.relationships(pagePart)
	if err != nil {
		if stop, retErr := report(pagePart, "Relationships", "", &PartError{Part: pagePart, Err: err}); stop {
			return retErr
		}
		return nil
	}
	typeURI := formatNamespace(r.format) + "/required-resource"
	targets := make(map[string]string, len(relations))
	missingTargets := make(map[string]bool)
	for _, relation := range relations {
		if relation.Type != typeURI {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			if stop, retErr := report(pagePart, "Relationship", "TargetMode", &PartError{Part: pagePart, Err: fmt.Errorf("%w: external Required Resource relationship %q", ErrInvalid, relation.ID)}); stop {
				return retErr
			}
			continue
		}
		target, err := resolvePart(pagePart, relation.Target)
		if err != nil {
			if stop, retErr := report(pagePart, "Relationship", "Target", &PartError{Part: pagePart, Err: err}); stop {
				return retErr
			}
			continue
		}
		targetKey := strings.ToLower(target)
		media, err := r.pkg.contentType(target)
		if err != nil {
			missingTargets[targetKey] = true
			if stop, retErr := report(target, "Relationship", "Target", &PartError{Part: pagePart, Err: fmt.Errorf("Required Resource relationship %q target %s: %w", relation.ID, target, err)}); stop {
				return retErr
			}
			continue
		}
		targets[targetKey] = media
	}
	for _, dependency := range dependencies {
		depKey := strings.ToLower(dependency.Part)
		media, ok := targets[depKey]
		if !ok {
			if missingTargets[depKey] {
				continue
			}
			if stop, retErr := report(dependency.Part, dependency.Element, dependency.Attribute, requiredResourceError(dependency, fmt.Errorf("%w: missing Required Resource relationship from page %s to %s", ErrInvalid, pagePart, dependency.Part))); stop {
				return retErr
			}
			continue
		}
		if !requiredResourceMedia(dependency.Kind, media) {
			if stop, retErr := report(dependency.Part, dependency.Element, dependency.Attribute, requiredResourceError(dependency, fmt.Errorf("%w: unexpected resource content type %q for %s", ErrInvalid, media, dependency.Part))); stop {
				return retErr
			}
		}
	}
	checked := make(map[string]bool, len(dependencies))
	for _, dependency := range dependencies {
		key := strings.ToLower(dependency.Part)
		if checked[key] {
			continue
		}
		checked[key] = true
		depRels, err := r.pkg.relationships(dependency.Part)
		if err != nil {
			if stop, retErr := report(dependency.Part, "Relationships", "", &PartError{Part: dependency.Part, Err: err}); stop {
				return retErr
			}
			continue
		}
		for _, relation := range depRels {
			if relation.Type == typeURI {
				if stop, retErr := report(dependency.Part, "Relationship", "Type", &PartError{Part: dependency.Part, Err: fmt.Errorf("%w: Required Resource relationship %q must originate from FixedPage, not a resource part", ErrInvalid, relation.ID)}); stop {
					return retErr
				}
			}
		}
	}
	return nil
}

// changedResourcesWithDeps 复用已收集依赖列表判断页面或其任一依赖是否发生修改
// 入参: pagePart 规范页面部件URI, dependencies 已收集页面依赖列表
// 返回: bool 是否需要执行生产者资源校验
func (p *Package) changedResourcesWithDeps(pagePart string, dependencies []requiredResource) bool {
	if p.original == nil || p.dirty[strings.ToLower(pagePart)] {
		return true
	}
	for _, resource := range dependencies {
		if p.dirty[strings.ToLower(resource.Part)] {
			return true
		}
	}
	return false
}

// reader 构造独立部件索引，单遍完成全部页面解析、依赖关系合成与资源校验，不创建中间ZIP
// 入参: ctx 取消Context
// 返回: *Reader 已校验快照, error 结构、资源或取消错误
func (p *Package) reader(ctx context.Context) (*Reader, error) {
	r, _, err := p.assembleAndValidate(ctx, false)
	return r, err
}

// assembleAndValidate 统一执行包编排、关系合成与全链路校验，collect为false时短路报错返回只读快照，collect为true时非短路收集全部诊断
// 入参: ctx 已规范化取消Context, collect 是否启用非短路诊断收集模式
// 返回: *Reader 快照读取器，collect模式可能为部分组装视图, []Diagnostic 非短路诊断列表, error 短路模式校验错误或取消错误
func (p *Package) assembleAndValidate(ctx context.Context, collect bool) (*Reader, []Diagnostic, error) {
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	var diagnostics []Diagnostic
	report := func(part, element, attr string, err error) error {
		if err == nil {
			return nil
		}
		if !collect {
			return err
		}
		return appendValidationError(&diagnostics, part, element, attr, err)
	}
	var onErr func(part, element, attr string, err error) error
	if collect {
		onErr = report
	}
	if len(p.documents) == 0 {
		if err := report(p.sequence, "FixedDocumentSequence", "", fmt.Errorf("%w: package needs a document", ErrInvalid)); err != nil {
			return nil, nil, err
		}
	}
	if collect {
		for _, key := range slices.Sorted(maps.Keys(p.parts)) {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			part := p.parts[key]
			if err := report(part.name, "", "ContentType", validatePackageMediaForFormat(p.format, part.media)); err != nil {
				return nil, nil, err
			}
		}
	}
	pkg := p.partReader()
	var allPages []PageReference
	for _, document := range p.documents {
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		if len(document.Pages) == 0 {
			if err := report(document.Part, "FixedDocument", "", fmt.Errorf("%w: document %s needs a page", ErrInvalid, document.Part)); err != nil {
				return nil, nil, err
			}
		}
		docTargets := make(map[string]string)
		for _, pageRef := range document.Pages {
			allPages = append(allPages, pageRef)
			if len(pageRef.LinkTargets) != 0 {
				pageSeen := make(map[string]bool, len(pageRef.LinkTargets))
				for _, target := range pageRef.LinkTargets {
					if pageSeen[target] {
						if err := report(document.Part, "LinkTarget", "Name", fmt.Errorf("%w: duplicate LinkTarget %q on page %s", ErrInvalid, target, pageRef.Part)); err != nil {
							return nil, nil, err
						}
					}
					pageSeen[target] = true
					if p.format == FormatXPS {
						if prev, exists := docTargets[target]; exists {
							if err := report(document.Part, "LinkTarget", "Name", fmt.Errorf("%w: duplicate XPS LinkTarget %q on pages %s and %s", ErrInvalid, target, prev, pageRef.Part)); err != nil {
								return nil, nil, err
							}
						} else {
							docTargets[target] = pageRef.Part
						}
					}
				}
			}
		}
		if _, present := p.original[strings.ToLower(document.Part)]; present && !p.dirty[strings.ToLower(document.Part)] {
			continue
		}
		root, err := buildFixedDocumentNode(p.format, document)
		if err != nil {
			if retErr := report(document.Part, "FixedDocument", "Source", err); retErr != nil {
				return nil, nil, retErr
			}
			continue
		}
		data, err := createdMarkup(root, p.limits, ctx)
		if err != nil {
			if retErr := report(document.Part, "FixedDocument", "", err); retErr != nil {
				return nil, nil, retErr
			}
			continue
		}
		createdPut(pkg, document.Part, fixedContentType("fixeddocument"), data)
	}
	if _, present := p.original[strings.ToLower(p.sequence)]; !present || p.dirty[strings.ToLower(p.sequence)] {
		sequence, err := buildFixedDocumentSequenceNode(p.format, p.sequence, p.documents)
		if err != nil {
			if retErr := report(p.sequence, "FixedDocumentSequence", "Source", err); retErr != nil {
				return nil, nil, retErr
			}
		} else {
			data, err := createdMarkup(sequence, p.limits, ctx)
			if err != nil {
				if retErr := report(p.sequence, "FixedDocumentSequence", "", err); retErr != nil {
					return nil, nil, retErr
				}
			} else {
				createdPut(pkg, p.sequence, fixedContentType("fixeddocumentsequence"), data)
			}
		}
	}
	deferred := make(map[string]bool, len(p.documents)+len(allPages)+1)
	deferred["/"] = true
	for _, document := range p.documents {
		deferred[strings.ToLower(document.Part)] = true
		for _, page := range document.Pages {
			deferred[strings.ToLower(page.Part)] = true
		}
	}
	for _, source := range slices.Sorted(maps.Keys(p.relations)) {
		if err := checkContext(ctx); err != nil {
			return nil, nil, err
		}
		if deferred[source] {
			continue
		}
		sourceName := p.relationSourceName(pkg, source)
		if err := report(createdRelationshipPart(sourceName), "Relationships", "", p.composeRelationships(pkg, sourceName, nil, ctx)); err != nil {
			return nil, nil, err
		}
	}
	rootRelations := []Relationship{{Type: formatNamespace(p.format) + "/fixedrepresentation", Target: p.sequence, TargetMode: TargetModeInternal}}
	if err := report(createdRelationshipPart("/"), "Relationships", "", p.composeRelationships(pkg, "/", rootRelations, ctx)); err != nil {
		return nil, nil, err
	}
	r := &Reader{pkg: pkg, format: p.format, limits: p.limits}
	if err := r.readSequence(); err != nil {
		if retErr := report(p.sequence, "FixedDocumentSequence", "", err); retErr != nil {
			return nil, nil, retErr
		}
		r.sequence, r.documents, r.pages = p.sequence, p.documents, allPages
	}
	if _, err := r.CoreProperties(ctx); err != nil {
		if retErr := report("/", "CoreProperties", "", err); retErr != nil {
			return nil, nil, retErr
		}
	}
	navigation, err := newCreatedNavigation(r, ctx)
	if err != nil {
		return nil, nil, err
	}
	fonts := fontCache{pkg: pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: p.limits.MaxPackageBytes, maxFaces: p.limits.MaxPartCount}
	restricted := make(map[string][]Relationship)
	checkedResources := make(map[string]bool)
	profileChannels := make(map[string]uint32)
	var failedProfiles map[string]bool
	if collect {
		failedProfiles = make(map[string]bool)
	}
	ns := formatNamespace(p.format)
	loadDict := func(part string) (*xmlElement, error) { return r.readResourceDictionaryLoader(part, nil, ctx) }
	for _, document := range r.documents {
		docKey := strings.ToLower(document.Part)
		for _, page := range document.Pages {
			if err := checkContext(ctx); err != nil {
				return nil, nil, err
			}
			root, err := r.readFixedPartLoader(page.Part, "fixedpage", "FixedPage", nil, ctx)
			if err != nil {
				if retErr := report(page.Part, "FixedPage", "", err); retErr != nil {
					return nil, nil, retErr
				}
				continue
			}
			if _, err := parsePageHeader(root, page.Part, r.format); err != nil {
				if retErr := report(page.Part, "FixedPage", "", err); retErr != nil {
					return nil, nil, retErr
				}
			}
			if collect && len(page.LinkTargets) != 0 {
				pageNames := make(map[string]bool)
				for _, name := range createdPageTargets(root) {
					pageNames[name] = true
				}
				for _, target := range page.LinkTargets {
					if !pageNames[target] {
						if err := report(page.Part, "LinkTarget", "Name", fmt.Errorf("%w: LinkTarget %q is absent from page", ErrInvalid, target)); err != nil {
							return nil, nil, err
						}
					}
				}
			}
			graph, err := parseResourceGraphContext(page.Part, root, r.format, r.limits, loadDict, ctx)
			if err != nil {
				if retErr := report(page.Part, "FixedPage", "", err); retErr != nil {
					return nil, nil, retErr
				}
				continue
			}
			if _, err := newSceneParser(r.format, graph).parse(root); err != nil {
				if retErr := report(page.Part, "FixedPage", "", err); retErr != nil {
					return nil, nil, retErr
				}
			}
			if err := navigation.validateCollect(page.Part, graph, ctx, onErr); err != nil {
				return nil, nil, err
			}
			dependencies, err := collectRequiredResources(graph, p.format)
			if err != nil {
				if retErr := report(page.Part, "FixedPage", "", err); retErr != nil {
					return nil, nil, retErr
				}
				continue
			}
			var relations []Relationship
			seen := make(map[string]bool, len(dependencies))
			for _, dependency := range dependencies {
				depKey := strings.ToLower(dependency.Part)
				if seen[depKey] {
					continue
				}
				seen[depKey] = true
				relations = append(relations, Relationship{Type: ns + "/required-resource", Target: dependency.Part, TargetMode: TargetModeInternal})
			}
			if err := report(createdRelationshipPart(page.Part), "Relationships", "", p.composeRelationships(pkg, page.Part, relations, ctx)); err != nil {
				return nil, nil, err
			}
			if err := r.validateRequiredResourcesCollect(page.Part, dependencies, onErr); err != nil {
				return nil, nil, err
			}
			if collect || p.changedResourcesWithDeps(page.Part, dependencies) {
				parts, err := validateCreatedFontsCollect(&fonts, graph, p.format, ctx, onErr)
				if err != nil {
					return nil, nil, err
				}
				if err := p.validateCreatedResourcesCollect(pkg, graph, dependencies, checkedResources, profileChannels, failedProfiles, ctx, onErr); err != nil {
					return nil, nil, err
				}
				for _, part := range parts {
					duplicate := false
					for _, relation := range restricted[docKey] {
						duplicate = duplicate || strings.EqualFold(relation.Target, part)
					}
					if !duplicate {
						restricted[docKey] = append(restricted[docKey], Relationship{Type: ns + "/restricted-font", Target: part, TargetMode: TargetModeInternal})
					}
				}
			}
		}
	}
	for _, document := range r.documents {
		if err := report(createdRelationshipPart(document.Part), "Relationships", "", p.composeRelationships(pkg, document.Part, restricted[strings.ToLower(document.Part)], ctx)); err != nil {
			return nil, nil, err
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
			if retErr := report(opcTypesName, "Types", "", err); retErr != nil {
				return nil, nil, retErr
			}
		}
	}
	if data != nil {
		createdPut(pkg, opcTypesName, "", data)
	}
	registry := newPartNameRegistry()
	if _, hasTypes := pkg.parts[strings.ToLower(opcTypesName)]; !hasTypes {
		registry.register(opcTypesName)
	}
	for _, key := range slices.Sorted(maps.Keys(pkg.parts)) {
		name := pkg.names[key]
		if name == "" {
			continue
		}
		if err := registry.available(name); err != nil {
			if !collect {
				return nil, nil, fmt.Errorf("%w: derived generated part name", ErrInvalid)
			}
			diagnostics = append(diagnostics, Diagnostic{Part: name, Message: err.Error()})
		}
		registry.register(name)
	}
	if registry.count() > p.limits.MaxPartCount {
		if !collect {
			return nil, nil, fmt.Errorf("%w: generated package part count", ErrLimit)
		}
		diagnostics = append(diagnostics, Diagnostic{Part: "/", Message: "package exceeds MaxPartCount"})
	}
	var total int64
	packageLimitReported := false
	for _, key := range slices.Sorted(maps.Keys(pkg.data)) {
		raw := pkg.data[key]
		if int64(len(raw)) > p.limits.MaxPartBytes {
			if !collect {
				return nil, nil, fmt.Errorf("%w: generated package byte budget", ErrLimit)
			}
			diagnostics = append(diagnostics, Diagnostic{Part: pkg.names[key], Message: "part exceeds MaxPartBytes"})
		}
		if int64(len(raw)) > p.limits.MaxPackageBytes-total {
			if !collect {
				return nil, nil, fmt.Errorf("%w: generated package byte budget", ErrLimit)
			}
			if !packageLimitReported {
				diagnostics = append(diagnostics, Diagnostic{Part: "/", Message: "package exceeds MaxPackageBytes"})
				packageLimitReported = true
			}
		} else {
			total += int64(len(raw))
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	if err := report("/", "RequiredResource", "", r.validateRequiredResourceLinks(ctx)); err != nil {
		return nil, nil, err
	}
	if err := report("/", "PrintTicket", "", r.validatePrintTicketLinks(ctx)); err != nil {
		return nil, nil, err
	}
	if err := report("/", "SignatureDefinitions", "", r.validateSignatureDefinitionLinks(ctx)); err != nil {
		return nil, nil, err
	}
	if err := report("/", "Thumbnail", "", p.validateThumbnailLinks(r, ctx)); err != nil {
		return nil, nil, err
	}
	control, err := r.DiscardControl(ctx)
	if err != nil {
		if retErr := report("/", "DiscardControl", "", err); retErr != nil {
			return nil, nil, retErr
		}
	} else if control != nil {
		if control.Ignored != 0 {
			if !collect {
				return nil, nil, fmt.Errorf("%w: invalid produced discard reference", ErrInvalid)
			}
			diagnostics = append(diagnostics, Diagnostic{Part: control.Part.Name, Element: "DiscardControl", Message: "invalid discard reference"})
		}
		pageSet := make(map[string]bool, len(r.pages))
		for _, pageRef := range r.pages {
			pageSet[strings.ToLower(pageRef.Part)] = true
		}
		for _, hint := range control.Hints {
			if _, exists := pkg.parts[strings.ToLower(hint.Target)]; !exists {
				if !collect {
					return nil, nil, fmt.Errorf("%w: discard target is absent", ErrInvalid)
				}
				diagnostics = append(diagnostics, Diagnostic{Part: control.Part.Name, Element: "Discard", Attribute: "Target", Message: fmt.Sprintf("discard target %s is absent", hint.Target)})
			}
			if !pageSet[strings.ToLower(hint.SentinelPage)] {
				if !collect {
					return nil, nil, fmt.Errorf("%w: discard sentinel is not a fixed page", ErrInvalid)
				}
				diagnostics = append(diagnostics, Diagnostic{Part: control.Part.Name, Element: "Discard", Attribute: "SentinelPage", Message: fmt.Sprintf("discard sentinel %s is not a fixed page", hint.SentinelPage)})
			}
		}
		if len(control.Hints) != 0 {
			if err := report(control.Part.Name, "DiscardControl", "", r.validateDiscardLifetime(control, ctx)); err != nil {
				return nil, nil, err
			}
		}
	}
	if err := report("/", "DocumentStructure", "", r.validateStoryLinks(ctx)); err != nil {
		return nil, nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, nil, err
	}
	return r, diagnostics, nil
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
	isMCEPrefixList := func(node *xmlElement, attr xml.Attr) bool {
		return attr.Name.Space == mcNamespace && (attr.Name.Local == "Ignorable" || attr.Name.Local == "MustUnderstand") || node.Name == (xml.Name{Space: mcNamespace, Local: "Choice"}) && attr.Name == (xml.Name{Local: "Requires"})
	}
	isMCEQNameList := func(attr xml.Attr) bool {
		return attr.Name.Space == mcNamespace && (attr.Name.Local == "ProcessContent" || attr.Name.Local == "PreserveElements" || attr.Name.Local == "PreserveAttributes")
	}
	lookupNS := func(primary, fallback map[string]string, prefix string) string {
		if uri := primary[prefix]; uri != "" {
			return uri
		}
		return fallback[prefix]
	}
	count := 0
	var scanPreserved func(*xmlElement, map[string]string, map[string]bool, int) error
	scanPreserved = func(node *xmlElement, fallbackNS map[string]string, localIgnorable map[string]bool, depth int) error {
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
		curIgnorable := localIgnorable
		if value, ok := node.attributeNS(mcNamespace, "Ignorable"); ok {
			words := compatibilityWords(value)
			if len(words) != 0 {
				curIgnorable = maps.Clone(localIgnorable)
				if curIgnorable == nil {
					curIgnorable = make(map[string]bool, len(words))
				}
				for _, prefix := range words {
					uri := lookupNS(node.Namespaces, fallbackNS, prefix)
					if !xmlNCName(prefix) || uri == "" || prefix == "xmlns" {
						return fmt.Errorf("%w: invalid or undeclared MCE prefix %q", ErrInvalid, prefix)
					}
					curIgnorable[uri] = true
					if _, err := bindPrefix(uri, hints); err != nil {
						return err
					}
				}
			}
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
			if isMCEPrefixList(node, attr) {
				for _, prefix := range compatibilityWords(attr.Value) {
					uri := lookupNS(node.Namespaces, fallbackNS, prefix)
					if !xmlNCName(prefix) || uri == "" || prefix == "xmlns" {
						return fmt.Errorf("%w: invalid or undeclared MCE prefix %q", ErrInvalid, prefix)
					}
					if _, err := bindPrefix(uri, hints); err != nil {
						return err
					}
				}
			} else if isMCEQNameList(attr) {
				for _, word := range compatibilityWords(attr.Value) {
					prefix, local, qualified := strings.Cut(word, ":")
					uri := lookupNS(node.Namespaces, fallbackNS, prefix)
					if !qualified || !xmlNCName(prefix) || local != "*" && !xmlNCName(local) || uri == "" || prefix == "xmlns" {
						return fmt.Errorf("%w: invalid or undeclared MCE QName %q", ErrInvalid, word)
					}
					if _, err := bindPrefix(uri, hints); err != nil {
						return err
					}
				}
			}
			if attr.Name.Space == "" || attr.Name.Space == xmlnsNamespace || attr.Name.Space == xmlNamespace {
				continue
			}
			prefix, err := bindPrefix(attr.Name.Space, hints)
			if err != nil {
				return err
			}
			if attr.Name.Space != mcNamespace && attr.Name.Space != defaultNS && attr.Name.Space != defaultNS+"/resourcedictionary-key" && !curIgnorable[attr.Name.Space] {
				ignorable[prefix] = true
			}
		}
		for _, attr := range node.PreservedAttributes {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if attr.Name.Space != "" && attr.Name.Space != xmlNamespace {
				prefix, err := bindPrefix(attr.Name.Space, hints)
				if err != nil {
					return err
				}
				if attr.Name.Space != mcNamespace && attr.Name.Space != defaultNS && attr.Name.Space != defaultNS+"/resourcedictionary-key" && !curIgnorable[attr.Name.Space] {
					ignorable[prefix] = true
				}
			}
		}
		for _, child := range node.Children {
			if err := scanPreserved(child, hints, curIgnorable, depth+1); err != nil {
				return err
			}
		}
		for _, item := range node.PreservedElements {
			if err := scanPreserved(item, hints, curIgnorable, depth+1); err != nil {
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
			if attr.Name.Space == "" || attr.Name.Space == xmlnsNamespace || attr.Name.Space == xmlNamespace {
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
			if err := scanPreserved(item, node.Namespaces, nil, depth+1); err != nil {
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
	rewritePrefix := func(uri string) string {
		if uri == xmlNamespace {
			return "xml"
		}
		return prefixes[uri]
	}
	var encodeNode func(*xmlElement, map[string]string, bool, bool, bool) error
	encodeNode = func(node *xmlElement, fallbackNS map[string]string, isRoot, isPreserved, emptyDefault bool) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		hints := node.Namespaces
		if len(hints) == 0 {
			hints = fallbackNS
		}
		localName := node.Name.Local
		needEmptyDefault := false
		needRestoreDefault := false
		if node.Name.Space == "" {
			if isPreserved && defaultNS != "" && !emptyDefault {
				needEmptyDefault = true
			}
		} else if node.Name.Space == defaultNS {
			if emptyDefault && defaultNS != "" {
				needRestoreDefault = true
			}
		} else if prefix := prefixes[node.Name.Space]; prefix != "" {
			localName = prefix + ":" + node.Name.Local
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
		} else if needRestoreDefault {
			start.Attr = append(start.Attr, xml.Attr{Name: xml.Name{Local: "xmlns"}, Value: defaultNS})
		}
		appendAttr := func(attr xml.Attr) {
			if isPreserved {
				if isMCEPrefixList(node, attr) {
					words := compatibilityWords(attr.Value)
					remapped := make([]string, 0, len(words))
					for _, prefix := range words {
						if mapped := rewritePrefix(lookupNS(node.Namespaces, fallbackNS, prefix)); mapped != "" {
							remapped = append(remapped, mapped)
						}
					}
					attr.Value = strings.Join(remapped, " ")
				} else if isMCEQNameList(attr) {
					words := compatibilityWords(attr.Value)
					remapped := make([]string, 0, len(words))
					for _, word := range words {
						prefix, local, _ := strings.Cut(word, ":")
						if mapped := rewritePrefix(lookupNS(node.Namespaces, fallbackNS, prefix)); mapped != "" {
							remapped = append(remapped, mapped+":"+local)
						}
					}
					attr.Value = strings.Join(remapped, " ")
				}
			}
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
				if prefix := prefixes[attr.Name.Space]; prefix != "" {
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
		childEmptyDefault := emptyDefault
		if needEmptyDefault {
			childEmptyDefault = true
		} else if needRestoreDefault {
			childEmptyDefault = false
		}
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
							if err := encodeNode(item.element, hints, false, isPreserved, childEmptyDefault); err != nil {
								return err
							}
						} else if allowedPreserved[item.element] {
							emitted[item.element] = true
							if err := encodeNode(item.element, hints, false, true, childEmptyDefault); err != nil {
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
						if err := encodeNode(child, hints, false, isPreserved, childEmptyDefault); err != nil {
							return err
						}
					}
				}
				for _, item := range node.PreservedElements {
					if !emitted[item] {
						if err := encodeNode(item, hints, false, true, childEmptyDefault); err != nil {
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
			if err := encodeNode(child, hints, false, isPreserved, childEmptyDefault); err != nil {
				return err
			}
		}
		for _, item := range node.PreservedElements {
			if err := encodeNode(item, hints, false, true, childEmptyDefault); err != nil {
				return err
			}
		}
		return encoder.EncodeToken(start.End())
	}
	if err := encodeNode(root, root.Namespaces, true, false, false); err != nil {
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

// validatePackageMediaForFormat 按OPC规则及当前方言[M12.8]标准表校验内容类型，禁止标准表内类型携带任何MIME参数
// 入参: format 文档方言，FormatUnknown仅校验OPC自有媒体类型, value 内容类型
// 返回: error 非法内容类型或禁止参数错误
func validatePackageMediaForFormat(format Format, value string) error {
	media, parameters, err := mime.ParseMediaType(value)
	if err != nil || !strings.Contains(media, "/") || strings.ContainsAny(value, "\r\n\t") || strings.TrimSpace(value) != value || !xmlTextValid(value) {
		return fmt.Errorf("%w: invalid content type", ErrInvalid)
	}
	if strings.Contains(value, ";") {
		if len(parameters) == 0 {
			return fmt.Errorf("%w: empty parameter in content type", ErrInvalid)
		}
		if opcSpecificContentType(media) {
			return fmt.Errorf("%w: parameters on package-specific content type", ErrInvalid)
		}
		if format != FormatUnknown && standardXPSContentType(format, opcMediaTypeBase(value)) {
			return fmt.Errorf("%w: M12.8 prohibits MIME parameters on standard XPS content type %q", ErrInvalid, media)
		}
	}
	return nil
}
