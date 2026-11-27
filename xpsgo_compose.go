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
	"cmp"
	"context"
	"encoding/xml"
	"errors"
	"fmt"
	"io"
	"maps"
	"math"
	"net/url"
	"slices"
	"sort"
	"strconv"
	"strings"
)

// PageSelection 指定源阅读器中的零基全局页号，同一页面可在不同输出位置重复选用
type PageSelection struct {
	Reader *Reader
	Page   int
}

// ComposePage 指定源阅读器中的零基全局页号及可选单页几何变换，零值变换字段表示保持原页不变
// Rotate仅允许0、90、180、270顺时针旋转；CropBox在原页面坐标系裁剪；TargetWidth与TargetHeight按正有限尺寸等比缩放，同时指定时等比缩放居中至目标尺寸，仅指定单边时按比例推导另一边
type ComposePage struct {
	Reader       *Reader
	Page         int
	Rotate       int
	CropBox      *Rect
	TargetWidth  float64
	TargetHeight float64
}

// ComposeOptions 设置组合输出格式、累计资源上限、元数据来源、舍弃策略、剪枝及资源去重
// Format和Metadata未指定时取首张页面所在来源，Limits和MaxImagePixels零值采用默认上限
// DiscardSignatures允许舍弃源签名起点，DiscardSignatureLocations允许移除未选页面的普通签署位置
// PruneUnselectedOutlines允许剪除指向未选页面的目录条目，StripDanglingNavigateUri允许剥离悬空内部超链接，DeduplicateResources启用跨源静态二进制资源摘要去重
type ComposeOptions struct {
	Format                    Format
	Limits                    Limits
	MaxImagePixels            uint64
	Metadata                  *Reader
	DiscardSignatures         bool
	DiscardSignatureLocations bool
	PruneUnselectedOutlines   bool
	StripDanglingNavigateUri  bool
	DeduplicateResources      bool
}

// compositionPageTransform 保存单页可选裁剪、顺时针旋转与目标尺寸缩放配置
type compositionPageTransform struct {
	rotate       int
	cropBox      *Rect
	targetWidth  float64
	targetHeight float64
}

// compositionXMLCache 保存单个只读XML部件已解析的原始树，在构造期写入并在后续只读阶段并发复用
type compositionXMLCache struct {
	data   []byte
	limits Limits
	raw    *xmlElement
}

// compositionReaderSelection 汇总单个阅读器的选页，不同时持有多个源阅读器的锁
type compositionReaderSelection struct {
	reader *Reader
	pages  []int
	seen   map[int]bool
}

// compositionTicketClass 保存本次校验中已逐字节确认相同的票据集合
type compositionTicketClass struct {
	parent *compositionTicketClass
	rank   uint8
}

// compositionBudget 累计页面组合的源读取和引用工作量，不按输出实例重复计费同一源部件
type compositionBudget struct {
	limits  Limits
	bytes   int64
	scans   int64
	work    int
	parts   int
	context context.Context
}

// compositionPageSelection 用源快照序号和原包全局页号标识一次选页
type compositionPageSelection struct {
	source int
	index  int
}

// compositionPageKey 标识原包中的唯一页面，不把输出中的重复副本合并
type compositionPageKey struct {
	source int
	index  int
}

// compositionPartKey 区分源部件及其输出作用域，document和page为-1时表示共享资源
type compositionPartKey struct {
	source   int
	part     string
	document int
	page     int
}

// compositionPageInstance 保存页面副本的源身份、输出位置及独立部件名
type compositionPageInstance struct {
	source    int
	index     int
	document  int
	position  int
	reference PageReference
}

// compositionDocumentInstance 保存目标文档及页面实例，complete只表示原文档原序完整复制
type compositionDocumentInstance struct {
	part     string
	pages    []int
	source   int
	original int
	complete bool
}

// compositionSourceIndex 保存原文档的页号边界，重复选页不反复扫描全部文档
type compositionSourceIndex struct {
	starts []int
}

// compositionPlan 记录页面组合的源部件身份映射与输出副本规划
type compositionPlan struct {
	format                    Format
	mixed                     bool
	sequence                  string
	sources                   []*compositionSource
	indices                   []*compositionSourceIndex
	documents                 []compositionDocumentInstance
	pages                     []compositionPageInstance
	transforms                []compositionPageTransform
	instances                 map[compositionPageKey][]int
	resources                 map[compositionPartKey]string
	fixed                     map[compositionPartKey]string
	claimed                   map[string]bool
	names                     *Package
	budget                    *compositionBudget
	parts                     int
	allocated                 int
	maxImagePixels            uint64
	protected                 []map[string]bool
	fonts                     []*compositionFontReport
	discardSignatureLocations bool
	pruneUnselectedOutlines   bool
	stripDanglingNavigateUri  bool
	deduplicateResources      bool
}

// compositionIndex 缓存原索引及当前能力下的消费视图，原文保留与派生投影分别检查
type compositionIndex struct {
	original packagePart
	format   Format
	limits   Limits
	raw      *xmlElement
	active   *xmlElement
	ordered  map[*xmlElement][]xmlContent
	checked  bool
	retained bool
}

// compositionSource 保存单个源包的独立快照，按小写规范化URI索引部件及原始关系XML
type compositionSource struct {
	format            Format
	sourceFormat      Format
	targetFormat      Format
	sequence          string
	documents         []Document
	pages             []PageReference
	selected          map[int]bool
	parts             map[string]packagePart
	relationships     map[string][]Relationship
	parsedRels        map[string][]Relationship
	parsedXML         map[string]*compositionXMLCache
	rootRelationships packagePart
	auxiliary         map[string]bool
	retained          map[string]bool
	indices           map[string]*compositionIndex
	restricted        map[string]bool
	printResources    map[string][]printResourceReference
	signatureOrigin   bool
}

// compositionCapture 在单个源阅读器的读锁内展开资源闭包，不获取其他阅读器的锁
type compositionCapture struct {
	reader   *Reader
	budget   *compositionBudget
	source   *compositionSource
	layout   map[string]bool
	queued   map[compositionSourcePart]bool
	queue    []compositionSourcePart
	roles    *createdNavigation
	owners   map[string]bool
	unbound  map[string]bool
	opaque   map[string]bool
	profiles map[string]bool
}

// compositionSourcePart 区分共享资源字典的所属页面，避免重复复制同一部件字节
type compositionSourcePart struct {
	part  string
	owner string
}

// DefaultComposeOptions 返回页面组合的默认资源上限配置
// 返回: ComposeOptions 组合选项
func DefaultComposeOptions() ComposeOptions {
	return ComposeOptions{Limits: DefaultLimits(), MaxImagePixels: DefaultImageOptions().MaxPixels}
}

// Compose 按外层文档顺序和内层页序创建独立可编辑包，不修改源阅读器，关闭源后仍可读写
// 每个输出文档须含页面；未支持的格式转换、兼容分支投影或元数据合并返回ErrUnsupported
// 入参: ctx 取消Context，nil采用Background, documents 输出文档及所选原页面, options 组合选项，nil采用默认值
// 返回: *Package 独立可编辑包，失败为nil, error 参数、结构、能力、许可、预算、关闭或取消错误
func Compose(ctx context.Context, documents [][]PageSelection, options *ComposeOptions) (*Package, error) {
	converted := make([][]ComposePage, len(documents))
	for i, pages := range documents {
		if len(pages) == 0 {
			continue
		}
		list := make([]ComposePage, len(pages))
		for j, page := range pages {
			list[j] = ComposePage{Reader: page.Reader, Page: page.Page}
		}
		converted[i] = list
	}
	return ComposePages(ctx, converted, options)
}

// ComposePages 按外层文档顺序和内层页序组合页面并支持单页裁剪、旋转与缩放，不修改源阅读器，关闭源后仍可读写
// 每个输出文档须含页面；未支持的格式转换、兼容分支投影或元数据合并返回ErrUnsupported
// 入参: ctx 取消Context，nil采用Background, documents 输出文档及所选原页面与单页几何配置, options 组合选项，nil采用默认值
// 返回: *Package 独立可编辑包，失败为nil, error 参数、结构、能力、许可、预算、关闭或取消错误
func ComposePages(ctx context.Context, documents [][]ComposePage, options *ComposeOptions) (*Package, error) {
	ctx = normalizeContext(ctx)
	configuration := ComposeOptions{}
	if options != nil {
		configuration = *options
	}
	budget, err := newCompositionBudget(configuration.Limits, ctx)
	if err != nil {
		return nil, err
	}
	if configuration.Format != FormatUnknown && formatNamespace(configuration.Format) == "" {
		return nil, fmt.Errorf("%w: composition output format", ErrInvalid)
	}
	if len(documents) == 0 {
		return nil, fmt.Errorf("%w: empty composition", ErrInvalid)
	}
	if len(documents) > budget.limits.MaxPartCount-3 {
		return nil, fmt.Errorf("%w: composition document count", ErrLimit)
	}
	readers := make(map[*Reader]int)
	var sources []compositionReaderSelection
	selected := make([][]compositionPageSelection, len(documents))
	var transforms []compositionPageTransform
	hasTransforms := false
	count := 0
	for document, pages := range documents {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if len(pages) == 0 {
			return nil, fmt.Errorf("%w: empty composition document", ErrInvalid)
		}
		if len(pages) > budget.limits.MaxPageCount-count || len(pages) > budget.limits.MaxPartCount-3-len(documents)-count {
			return nil, fmt.Errorf("%w: composition page count", ErrLimit)
		}
		count += len(pages)
		selected[document] = make([]compositionPageSelection, len(pages))
		for index, page := range pages {
			if err := budget.step(1); err != nil {
				return nil, err
			}
			if page.Reader == nil || page.Page < 0 {
				return nil, fmt.Errorf("%w: composition page selection", ErrInvalid)
			}
			transform, active, err := normalizeCompositionPageTransform(page)
			if err != nil {
				return nil, err
			}
			hasTransforms = hasTransforms || active
			transforms = append(transforms, transform)
			source, exists := readers[page.Reader]
			if !exists {
				source = len(sources)
				readers[page.Reader] = source
				sources = append(sources, compositionReaderSelection{reader: page.Reader, seen: make(map[int]bool)})
			}
			selected[document][index] = compositionPageSelection{source, page.Page}
			if !sources[source].seen[page.Page] {
				sources[source].seen[page.Page] = true
				sources[source].pages = append(sources[source].pages, page.Page)
			}
		}
	}
	root := 0
	if configuration.Metadata != nil {
		var exists bool
		root, exists = readers[configuration.Metadata]
		if !exists {
			return nil, fmt.Errorf("%w: composition metadata source is not selected", ErrInvalid)
		}
	}
	snapshots := make([]*compositionSource, len(sources))
	protectedList := make([]map[string]bool, len(sources))
	fontReports := make([]*compositionFontReport, len(sources))
	fixed := make(map[compositionPartKey]bool)
	format := configuration.Format
	for index, source := range sources {
		value, err := captureCompositionSourceForTarget(source.reader, source.pages, format, budget)
		if err != nil {
			return nil, err
		}
		if value.signatureOrigin && !configuration.DiscardSignatures {
			return nil, fmt.Errorf("%w: composition requires explicit signature discard", ErrUnsupported)
		}
		protected, err := compositionProtection(value, budget)
		if err != nil {
			return nil, err
		}
		protectedList[index] = protected
		if format == FormatUnknown {
			format = value.format
		}
		snapshots[index], fontReports[index], err = convertCompositionSourceWithReport(value, format, protected, budget)
		if err != nil {
			return nil, err
		}
		for part := range protected {
			if err := budget.step(1); err != nil {
				return nil, err
			}
			if !opcRelationshipName(part) {
				fixed[compositionPartKey{index, part, -1, -1}] = true
			}
		}
	}
	plan, err := newCompositionPlan(snapshots, selected, fixed, budget)
	if err != nil {
		return nil, err
	}
	plan.maxImagePixels = configuration.MaxImagePixels
	plan.protected = protectedList
	plan.fonts = fontReports
	plan.discardSignatureLocations = configuration.DiscardSignatureLocations
	plan.pruneUnselectedOutlines = configuration.PruneUnselectedOutlines
	plan.stripDanglingNavigateUri = configuration.StripDanglingNavigateUri
	plan.deduplicateResources = configuration.DeduplicateResources
	if hasTransforms {
		plan.transforms = transforms
	}
	names, err := newCompositionNames(plan)
	if err != nil {
		return nil, err
	}
	return executeCompositionPlan(plan, names, root)
}

// normalizeCompositionPageTransform 校验单页旋转角度、裁剪区域与目标尺寸，并返回独立只读变换配置
// 入参: page 单页选择与几何编辑选项
// 返回: compositionPageTransform 规范化变换配置, bool 是否存在非零几何变换, error 参数非法错误
func normalizeCompositionPageTransform(page ComposePage) (compositionPageTransform, bool, error) {
	if page.Rotate != 0 && page.Rotate != 90 && page.Rotate != 180 && page.Rotate != 270 {
		return compositionPageTransform{}, false, fmt.Errorf("%w: composition page rotate %d", ErrInvalid, page.Rotate)
	}
	var crop *Rect
	if page.CropBox != nil {
		r := *page.CropBox
		if !geometryFinite(r.X) || !geometryFinite(r.Y) || !geometryFinite(r.Width) || !geometryFinite(r.Height) || r.Width <= 0 || r.Height <= 0 {
			return compositionPageTransform{}, false, fmt.Errorf("%w: composition page crop box", ErrInvalid)
		}
		crop = &r
	}
	if !geometryFinite(page.TargetWidth) || !geometryFinite(page.TargetHeight) || page.TargetWidth < 0 || page.TargetHeight < 0 {
		return compositionPageTransform{}, false, fmt.Errorf("%w: composition page target size", ErrInvalid)
	}
	active := page.Rotate != 0 || crop != nil || page.TargetWidth > 0 || page.TargetHeight > 0
	return compositionPageTransform{rotate: page.Rotate, cropBox: crop, targetWidth: page.TargetWidth, targetHeight: page.TargetHeight}, active, nil
}

// ConvertFormat 将源阅读器的全部文档与页面按原结构一步转换为指定目标方言的独立可编辑包
// 内部复用Compose保留核心属性、目录结构、打印票据与签署请求；受限或不可无损转换内容返回对应错误
// 入参: ctx 取消Context，nil采用Background, source 源阅读器, targetFormat 目标方言, options 可选组合参数，nil采用默认值
// 返回: *Package 目标方言的独立可编辑包，失败为nil, error 参数、格式、支持范围、许可、预算、关闭或取消错误
func ConvertFormat(ctx context.Context, source *Reader, targetFormat Format, options *ComposeOptions) (*Package, error) {
	ctx = normalizeContext(ctx)
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if source == nil || formatNamespace(targetFormat) == "" {
		return nil, fmt.Errorf("%w: format conversion source or target format", ErrInvalid)
	}
	configuration := ComposeOptions{}
	if options != nil {
		configuration = *options
		if configuration.Format != FormatUnknown && configuration.Format != targetFormat {
			return nil, fmt.Errorf("%w: conflicting format conversion target", ErrInvalid)
		}
		if configuration.Metadata != nil && configuration.Metadata != source {
			return nil, fmt.Errorf("%w: format conversion metadata source must match source reader", ErrInvalid)
		}
	}
	if err := source.readLock(); err != nil {
		return nil, err
	}
	docCount := len(source.documents)
	pageCounts := make([]int, docCount)
	totalPages := len(source.pages)
	for i, doc := range source.documents {
		pageCounts[i] = len(doc.Pages)
	}
	source.mu.RUnlock()
	if docCount == 0 || totalPages == 0 {
		return nil, fmt.Errorf("%w: empty source package for format conversion", ErrInvalid)
	}
	selections := make([][]PageSelection, docCount)
	pageIndex := 0
	for docIdx, count := range pageCounts {
		if count == 0 {
			return nil, fmt.Errorf("%w: empty document in format conversion", ErrInvalid)
		}
		pages := make([]PageSelection, count)
		for pos := range count {
			pages[pos] = PageSelection{Reader: source, Page: pageIndex}
			pageIndex++
		}
		selections[docIdx] = pages
	}
	configuration.Format = targetFormat
	configuration.Metadata = source
	return Compose(ctx, selections, &configuration)
}

// root 查找票据的等价类并缩短后续查找路径，不保存跨校验的内容结论
// 返回: *compositionTicketClass 当前集合的根
func (c *compositionTicketClass) root() *compositionTicketClass {
	for c.parent != nil {
		if c.parent.parent != nil {
			c.parent = c.parent.parent
		}
		c = c.parent
	}
	return c
}

// join 合并已确认内容相同的两个集合，按树高连接以限制后续查找开销
// 入参: other 已确认等价的集合
// 返回: *compositionTicketClass 合并后的根
func (c *compositionTicketClass) join(other *compositionTicketClass) *compositionTicketClass {
	c, other = c.root(), other.root()
	if c == other {
		return c
	}
	if c.rank < other.rank {
		c, other = other, c
	}
	other.parent = c
	if c.rank == other.rank {
		c.rank++
	}
	return c
}

// newCompositionBudget 合并默认上限并建立单次组合预算，不改变调用方配置
// 入参: limits 资源上限，零值采用默认值, ctx 取消Context
// 返回: *compositionBudget 独立预算，失败为nil, error 配置或取消错误
func newCompositionBudget(limits Limits, ctx context.Context) (*compositionBudget, error) {
	ctx = normalizeContext(ctx)
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	limits = mergeLimits(DefaultLimits(), limits)
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	return &compositionBudget{limits: limits, bytes: limits.MaxPackageBytes, scans: limits.MaxPackageBytes, work: limits.MaxXMLNodes, context: ctx}, nil
}

// step 在扫描索引、引用或标记前累计工作量，检查失败时不消耗剩余预算
// 入参: count 本次工作单元数
// 返回: error 参数、预算或取消错误
func (b *compositionBudget) step(count int) error {
	if err := checkContext(b.context); err != nil {
		return err
	}
	if count < 0 {
		return fmt.Errorf("%w: negative composition work", ErrInvalid)
	}
	if count > b.work {
		return fmt.Errorf("%w: composition work budget", ErrLimit)
	}
	b.work -= count
	return nil
}

// read 在读取新的源部件前扣除声明字节及部件数量，不把零长度部件排除在数量限制之外
// 入参: size 部件声明或内存数据长度
// 返回: error 部件、累计预算或取消错误
func (b *compositionBudget) read(size uint64) error {
	if err := b.step(0); err != nil {
		return err
	}
	if size > uint64(b.limits.MaxPartBytes) || b.bytes < 0 || size > uint64(b.bytes) || b.parts >= b.limits.MaxPartCount {
		return fmt.Errorf("%w: composition source part budget", ErrLimit)
	}
	b.bytes -= int64(size)
	b.parts++
	return nil
}

// scan 扣减标记与URI扫描字节预算，防止重复扫描超出上限
// 入参: size 本次将扫描的字节数
// 返回: error 参数、扫描预算或取消错误
func (b *compositionBudget) scan(size int64) error {
	if err := b.step(0); err != nil {
		return err
	}
	if size < 0 {
		return fmt.Errorf("%w: negative composition scan", ErrInvalid)
	}
	if size > b.scans {
		return fmt.Errorf("%w: composition scan byte budget", ErrLimit)
	}
	b.scans -= size
	return nil
}

// retain 将原文硬依赖纳入保留闭包，首次提升已扫描部件时重新展开其依赖
// 入参: part 实际依赖URI, owner 字典所属页面，非页面资源可为空
// 返回: error 目标、资源、预算或取消错误
func (s *compositionCapture) retain(part, owner string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	key := strings.ToLower(part)
	name, exists := s.reader.pkg.names[key]
	if !exists {
		return &PartError{Part: part, Err: fmt.Errorf("%w: missing retained composition part", ErrInvalid)}
	}
	media, err := s.reader.pkg.contentType(name)
	if err != nil {
		return err
	}
	role := createdNavigationOther
	switch {
	case strings.EqualFold(media, fixedContentType("fixedpage")):
		role, owner = createdNavigationPage, name
	case strings.EqualFold(media, fixedContentType("fixeddocument")):
		role = createdNavigationDocument
	case strings.EqualFold(media, fixedContentType("fixeddocumentsequence")):
		role = createdNavigationSequence
	}
	if !strings.EqualFold(media, resourceDictionaryContentType) && role != createdNavigationPage {
		owner = ""
	}
	if role != createdNavigationOther {
		s.layout[key], s.roles.parts[key] = true, role
	}
	if !s.source.retained[key] {
		s.source.retained[key] = true
		if _, loaded := s.source.parts[key]; loaded {
			s.queue = append(s.queue, compositionSourcePart{part: name, owner: owner})
		}
	}
	return s.add(name, owner)
}

// dependency 按源部件保留状态登记普通资源引用或原文硬依赖
// 入参: source 引用定义部件, target 明确资源URI, owner 当前所属页面
// 返回: error 目标、资源、预算或取消错误
func (s *compositionCapture) dependency(source, target, owner string) error {
	if s.source.retained[strings.ToLower(source)] {
		return s.retain(target, owner)
	}
	return s.add(target, owner)
}

// layoutReference 按保留目的跟随原始布局Source，保留分支页面与打印辅助页面均不改变阅读索引
// 入参: source 原始布局部件, target 引用部件, required 标准要求的布局类型
// 返回: error 类型、闭包、资源或取消错误
func (s *compositionCapture) layoutReference(source, target, required string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	media, err := s.reader.pkg.contentType(target)
	if err != nil {
		return err
	}
	if !strings.EqualFold(media, fixedContentType(required)) {
		return &PartError{Part: target, Err: fmt.Errorf("%w: retained layout source content type", ErrInvalid)}
	}
	key := strings.ToLower(source)
	if s.source.auxiliary[key] {
		if err := s.auxiliaryResource(target, required); err != nil {
			return err
		}
	}
	if s.source.retained[key] {
		return s.retain(target, "")
	}
	return nil
}

// newCompositionPlan 为选页组合规划独立输出身份，优先保留受保护部件名称再分配冲突名称
// 入参: sources 源包独立快照, selections 目标文档及页序, protected 必须保留原名的源部件, budget 累计预算
// 返回: *compositionPlan 独立规划，失败为nil, error 参数、冲突、许可、预算或取消错误
func newCompositionPlan(sources []*compositionSource, selections [][]compositionPageSelection, protected map[compositionPartKey]bool, budget *compositionBudget) (*compositionPlan, error) {
	if budget == nil || len(sources) == 0 || len(selections) == 0 {
		return nil, fmt.Errorf("%w: incomplete composition selection", ErrInvalid)
	}
	if err := budget.step(len(sources)); err != nil {
		return nil, err
	}
	if len(selections) > budget.limits.MaxPartCount-3 {
		return nil, fmt.Errorf("%w: composition document count", ErrLimit)
	}
	count := 0
	for _, document := range selections {
		if len(document) == 0 {
			return nil, fmt.Errorf("%w: empty composition document", ErrInvalid)
		}
		if len(document) > budget.limits.MaxPageCount-count || len(document) > budget.limits.MaxPartCount-3-len(selections)-count {
			return nil, fmt.Errorf("%w: composition page count", ErrLimit)
		}
		count += len(document)
		for _, page := range document {
			if err := budget.step(1); err != nil {
				return nil, err
			}
			if page.source < 0 || page.source >= len(sources) || sources[page.source] == nil {
				return nil, fmt.Errorf("%w: composition source index", ErrInvalid)
			}
			source := sources[page.source]
			if page.index < 0 || page.index >= len(source.pages) || !source.selected[page.index] || formatNamespace(source.format) == "" {
				return nil, fmt.Errorf("%w: composition source page", ErrInvalid)
			}
		}
	}
	p := &compositionPlan{sources: slices.Clone(sources), indices: make([]*compositionSourceIndex, len(sources)), documents: make([]compositionDocumentInstance, 0, len(selections)), pages: make([]compositionPageInstance, 0, count), instances: make(map[compositionPageKey][]int), resources: make(map[compositionPartKey]string), fixed: make(map[compositionPartKey]string), claimed: make(map[string]bool), names: &Package{names: make(map[string]bool), parents: make(map[string]int)}, budget: budget}
	for _, selected := range selections {
		for _, page := range selected {
			if p.indices[page.source] == nil {
				index, err := newCompositionSourceIndex(sources[page.source], budget)
				if err != nil {
					return nil, err
				}
				p.indices[page.source] = index
			}
		}
	}
	fixed := make([]compositionPartKey, 0, len(protected))
	for key, preserve := range protected {
		if preserve {
			fixed = append(fixed, key)
		}
	}
	slices.SortFunc(fixed, func(a, b compositionPartKey) int {
		if value := cmp.Compare(a.source, b.source); value != 0 {
			return value
		}
		return strings.Compare(strings.ToLower(a.part), strings.ToLower(b.part))
	})
	for _, key := range fixed {
		if key.source < 0 || key.source >= len(sources) || sources[key.source] == nil || key.document != -1 || key.page != -1 {
			return nil, fmt.Errorf("%w: protected composition identity", ErrInvalid)
		}
		part, err := opcPartName(key.part)
		if err != nil {
			return nil, err
		}
		if opcRelationshipName(part) || strings.EqualFold(part, opcTypesName) {
			return nil, fmt.Errorf("%w: protected composition metadata identity", ErrInvalid)
		}
		key.part = strings.ToLower(part)
		if _, exists := p.fixed[key]; exists {
			continue
		}
		value, exists := sources[key.source].parts[key.part]
		if !exists {
			return nil, fmt.Errorf("%w: protected composition part is not selected", ErrRestricted)
		}
		name, err := p.allocate(value.name, compositionHasRelationships(sources[key.source], key.part), true)
		if err != nil {
			return nil, err
		}
		p.fixed[key], p.resources[key] = name, name
	}
	if _, err := p.allocate("/_rels/.rels", false, true); err != nil {
		return nil, err
	}
	first := sources[selections[0][0].source]
	p.format = first.format
	sequenceRelations := false
	for _, source := range sources {
		if source != nil {
			sequenceRelations = sequenceRelations || compositionHasRelationships(source, source.sequence)
		}
	}
	var err error
	p.sequence, err = p.allocate(first.sequence, sequenceRelations, false)
	if err != nil {
		return nil, err
	}
	for documentIndex, selected := range selections {
		if err := p.addDocument(documentIndex, selected); err != nil {
			return nil, err
		}
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return p, nil
}

// addDocument 保留原文档完整性信息，部分文档和混合文档不借用受保护文档的身份
// 入参: index 输出文档序号, selected 本文档的页面选择
// 返回: error 原索引、许可、名称、预算或取消错误
func (p *compositionPlan) addDocument(index int, selected []compositionPageSelection) error {
	first := selected[0]
	source := p.sources[first.source]
	original, start, err := p.documentPage(first.source, first.index)
	if err != nil {
		return err
	}
	document := compositionDocumentInstance{source: first.source, original: original, complete: len(selected) == len(source.documents[original].Pages)}
	prefer := source.documents[original].Part
	relations := compositionHasRelationships(source, prefer)
	for position, selection := range selected {
		if err := p.budget.step(1); err != nil {
			return err
		}
		owner, _, err := p.documentPage(selection.source, selection.index)
		if err != nil {
			return err
		}
		if selection.source != first.source || owner != original {
			document.source, document.original, document.complete = -1, -1, false
		}
		document.complete = document.complete && selection.index == start+position
		relations = relations || compositionHasRelationships(p.sources[selection.source], p.sources[selection.source].documents[owner].Part)
		p.mixed = p.mixed || p.sources[selection.source].format != p.format
	}
	for _, selection := range selected {
		owner, _, err := p.documentPage(selection.source, selection.index)
		if err != nil {
			return err
		}
		key := compositionPartKey{source: selection.source, part: strings.ToLower(p.sources[selection.source].documents[owner].Part), document: -1, page: -1}
		if _, fixed := p.fixed[key]; fixed && !document.complete {
			return fmt.Errorf("%w: protected document selection is not a complete original unit", ErrRestricted)
		}
	}
	if document.original < 0 {
		prefer = "/Documents/" + strconv.Itoa(index+1) + "/FixedDoc.fdoc"
	}
	key := compositionPartKey{source: first.source, part: strings.ToLower(source.documents[original].Part), document: -1, page: -1}
	if document.original >= 0 {
		document.part, err = p.layout(key, compositionPartKey{source: first.source, part: key.part, document: index, page: -1}, prefer, relations)
	} else {
		document.part, err = p.allocate(prefer, relations, false)
	}
	if err != nil {
		return err
	}
	for position, selection := range selected {
		if err := p.budget.step(1); err != nil {
			return err
		}
		source := p.sources[selection.source]
		reference := source.pages[selection.index]
		key := compositionPartKey{source: selection.source, part: strings.ToLower(reference.Part), document: -1, page: -1}
		if _, exists := source.parts[key.part]; !exists {
			return fmt.Errorf("%w: selected page bytes are absent", ErrInvalid)
		}
		identity := compositionPartKey{source: selection.source, part: key.part, document: index, page: len(p.pages)}
		part, err := p.layout(key, identity, reference.Part, compositionHasRelationships(source, key.part))
		if err != nil {
			return err
		}
		reference.Part, reference.LinkTargets = part, slices.Clone(reference.LinkTargets)
		document.pages = append(document.pages, len(p.pages))
		pageKey := compositionPageKey{source: selection.source, index: selection.index}
		p.instances[pageKey] = append(p.instances[pageKey], len(p.pages))
		p.pages = append(p.pages, compositionPageInstance{source: selection.source, index: selection.index, document: index, position: position, reference: reference})
	}
	p.documents = append(p.documents, document)
	return nil
}

// newCompositionSourceIndex 检查原文档页号边界，不分配与全部源页面数量等长的归属表
// 入参: source 源快照, budget 累计预算
// 返回: *compositionSourceIndex 文档边界，失败为nil, error 索引、预算或取消错误
func newCompositionSourceIndex(source *compositionSource, budget *compositionBudget) (*compositionSourceIndex, error) {
	result := &compositionSourceIndex{starts: make([]int, 1, len(source.documents)+1)}
	first := 0
	for _, document := range source.documents {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if len(document.Pages) > len(source.pages)-first {
			return nil, fmt.Errorf("%w: inconsistent composition document index", ErrInvalid)
		}
		first += len(document.Pages)
		result.starts = append(result.starts, first)
	}
	if first != len(source.pages) {
		return nil, fmt.Errorf("%w: incomplete composition document index", ErrInvalid)
	}
	return result, nil
}

// documentPage 按原包全局页号二分定位归属，不从输出位置推断来源或忽略空文档边界
// 入参: source 原包序号, page 原包全局页号
// 返回: int 原文档序号, int 原文档首张全局页号, error 索引、预算或取消错误
func (p *compositionPlan) documentPage(source, page int) (int, int, error) {
	if err := p.budget.step(1); err != nil {
		return 0, 0, err
	}
	index := p.indices[source]
	owner := sort.Search(len(index.starts)-1, func(i int) bool { return index.starts[i+1] > page })
	if owner >= len(p.sources[source].documents) || page < 0 || page >= len(p.sources[source].pages) {
		return 0, 0, fmt.Errorf("%w: composition page has no document", ErrInvalid)
	}
	first := index.starts[owner]
	if !strings.EqualFold(p.sources[source].documents[owner].Pages[page-first].Part, p.sources[source].pages[page].Part) {
		return 0, 0, fmt.Errorf("%w: inconsistent composition source page index", ErrInvalid)
	}
	return owner, first, nil
}

// layout 分配布局副本，受保护名称只能对应一个输出布局实例
// 入参: original 源部件身份, instance 输出副本身份, prefer 建议名称, relations 是否需要关系部件
// 返回: string 输出部件名, error 许可、名称、预算或取消错误
func (p *compositionPlan) layout(original, instance compositionPartKey, prefer string, relations bool) (string, error) {
	if name, fixed := p.fixed[original]; fixed {
		key := strings.ToLower(name)
		if p.claimed[key] {
			return "", fmt.Errorf("%w: protected layout cannot be renamed for a duplicate instance", ErrRestricted)
		}
		p.claimed[key] = true
		p.resources[instance] = name
		return name, nil
	}
	name, err := p.allocate(prefer, relations, false)
	if err == nil {
		p.resources[instance] = name
	}
	return name, err
}

// resource 按源身份与输出归属分配资源名称，普通二进制资源在输出页面间共享
// 入参: source 源快照序号, part 原部件URI, document 目标文档序号，共享资源为-1, page 全局页面实例序号，共享或文档资源为-1
// 返回: string 目标部件名, error 身份、归属、名称、预算或取消错误
func (p *compositionPlan) resource(source int, part string, document, page int) (string, error) {
	return p.resourceIdentity(source, part, document, page, true)
}

// resourceIdentity 查询资源绑定，试探原身份时不占用输出名称或部件额度
// 入参: source 源序号, part 原资源URI, document 输出文档序号, page 页面实例序号, reserve 是否分配输出身份
// 返回: string 输出名称，试探需迁移时为空, error 身份、边界、预算或取消错误
func (p *compositionPlan) resourceIdentity(source int, part string, document, page int, reserve bool) (string, error) {
	if err := p.budget.step(1); err != nil {
		return "", err
	}
	if source < 0 || source >= len(p.sources) || p.sources[source] == nil || document < -1 || document >= len(p.documents) || page < -1 || page >= len(p.pages) || page >= 0 && (document < 0 || p.pages[page].document != document || p.pages[page].source != source) {
		return "", fmt.Errorf("%w: composition resource context", ErrInvalid)
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return "", err
	}
	key := compositionPartKey{source: source, part: strings.ToLower(canonical), document: document, page: page}
	value, exists := p.sources[source].parts[key.part]
	if !exists {
		return "", fmt.Errorf("%w: composition resource is absent", ErrInvalid)
	}
	if opcRelationshipName(value.name) || strings.EqualFold(value.name, opcTypesName) || compositionLayoutMedia(value.media) && !p.sources[source].auxiliary[key.part] && !p.sources[source].retained[key.part] {
		return "", fmt.Errorf("%w: composition layout is not an ordinary resource", ErrInvalid)
	}
	if name, exists := p.resources[key]; exists {
		return name, nil
	}
	original := compositionPartKey{source: source, part: key.part, document: -1, page: -1}
	if name, fixed := p.fixed[original]; fixed {
		if reserve {
			p.resources[key] = name
		}
		return name, nil
	}
	if !reserve {
		if p.resourceNameAvailable(value.name, compositionHasRelationships(p.sources[source], key.part)) {
			return value.name, nil
		}
		return "", nil
	}
	name, err := p.allocate(value.name, compositionHasRelationships(p.sources[source], key.part), false)
	if err == nil {
		p.resources[key] = name
	}
	return name, err
}

// compositionHasRelationships 检查原始关系部件或消费后的关系，避免遗漏未选中兼容分支的名称占用
// 入参: source 源快照, part 关系所属部件URI
// 返回: bool 是否需要预留伴生关系部件
func compositionHasRelationships(source *compositionSource, part string) bool {
	_, exists := source.parts[strings.ToLower(createdRelationshipPart(part))]
	return exists || len(source.relationships[strings.ToLower(part)]) != 0
}

// target 选择原页面对应的输出副本，自身链接留在当前副本，其他链接取输出顺序中的首个副本
// 入参: source 原包序号, page 原包全局页号, current 当前输出页面实例，非页面场景为-1
// 返回: int 输出全局页号，未选入时为-1, error 参数、预算或取消错误
func (p *compositionPlan) target(source, page, current int) (int, error) {
	if err := p.budget.step(1); err != nil {
		return -1, err
	}
	if source < 0 || source >= len(p.sources) || p.sources[source] == nil || page < 0 || page >= len(p.sources[source].pages) || current < -1 || current >= len(p.pages) {
		return -1, fmt.Errorf("%w: composition target identity", ErrInvalid)
	}
	if current >= 0 && p.pages[current].source == source && p.pages[current].index == page {
		return current, nil
	}
	if instances := p.instances[compositionPageKey{source: source, index: page}]; len(instances) != 0 {
		return instances[0], nil
	}
	return -1, nil
}

// allocate 处理大小写及父子派生冲突，迁移时只改目录，保留混淆字体所用的GUID文件名
// 入参: prefer 建议名称, relations 是否同时保留关系部件位置, fixed 是否禁止改名
// 返回: string 已保留的名称, error 名称、许可、预算或取消错误
func (p *compositionPlan) allocate(prefer string, relations, fixed bool) (string, error) {
	canonical, err := opcPartName(prefer)
	if err != nil {
		return "", err
	}
	if strings.EqualFold(canonical, opcTypesName) || opcRelationshipName(canonical) && canonical != "/_rels/.rels" {
		return "", fmt.Errorf("%w: reserved composition part name", ErrInvalid)
	}
	base := canonical[strings.LastIndexByte(canonical, '/')+1:]
	for {
		if err := p.budget.step(1); err != nil {
			return "", err
		}
		if p.resourceNameAvailable(canonical, relations) {
			needed := 1
			if relations {
				needed++
			}
			if needed > p.budget.limits.MaxPartCount-p.parts-1 {
				return "", fmt.Errorf("%w: composition output part count", ErrLimit)
			}
			p.names.registerName(canonical)
			if relations {
				p.names.registerName(createdRelationshipPart(canonical))
			}
			p.parts += needed
			return canonical, nil
		}
		if fixed {
			return "", fmt.Errorf("%w: protected composition part name collision", ErrRestricted)
		}
		if p.allocated == math.MaxInt {
			return "", fmt.Errorf("%w: composition name counter", ErrLimit)
		}
		p.allocated++
		canonical = "/Parts" + strconv.Itoa(p.allocated) + "/" + base
	}
}

// resourceNameAvailable 检查部件及伴生关系名称的冲突，不修改名称表或输出计数
// 入参: canonical 包根部件URI, relations 是否同时需要关系部件
// 返回: bool 两个名称均可原样使用
func (p *compositionPlan) resourceNameAvailable(canonical string, relations bool) bool {
	if p.names.availableName(canonical) != nil {
		return false
	}
	if !relations {
		return true
	}
	companion := createdRelationshipPart(canonical)
	return p.names.availableName(companion) == nil && !strings.HasPrefix(strings.ToLower(companion), strings.ToLower(canonical)+"/")
}

// convertCompositionSourceWithReport 将共通标准内容转换为目标方言并返回已完成的字体校验报告
// 入参: source 原快照, format 目标格式, protected 原文保护集合, budget 共享预算
// 返回: *compositionSource 目标快照, *compositionFontReport 跨方言字体报告，同格式为nil, error 格式、保护、表达能力、预算或取消错误
func convertCompositionSourceWithReport(source *compositionSource, format Format, protected map[string]bool, budget *compositionBudget) (*compositionSource, *compositionFontReport, error) {
	if source == nil || budget == nil || formatNamespace(source.format) == "" || formatNamespace(format) == "" {
		return nil, nil, fmt.Errorf("%w: composition format input", ErrInvalid)
	}
	if err := budget.step(0); err != nil {
		return nil, nil, err
	}
	if source.format == format {
		return source, nil, nil
	}
	if len(protected) != 0 {
		return nil, nil, fmt.Errorf("%w: composition changes protected document format", ErrRestricted)
	}
	report, err := validateCompositionFonts(source, budget)
	if err != nil {
		return nil, nil, err
	}
	if len(report.restricted) != 0 {
		return nil, nil, fmt.Errorf("%w: composition changes restricted font document format", ErrRestricted)
	}
	if err := budget.step(len(source.parts) + len(source.relationships)); err != nil {
		return nil, nil, err
	}
	result := *source
	result.indices = nil
	result.parsedXML = nil
	result.parsedRels = nil
	result.retained = maps.Clone(source.retained)
	result.sourceFormat = source.format
	result.targetFormat = FormatUnknown
	result.format, result.parts = format, make(map[string]packagePart, len(source.parts))
	result.relationships = make(map[string][]Relationship, len(source.relationships))
	result.pages = make([]PageReference, len(source.pages))
	for i, page := range source.pages {
		page.LinkTargets = slices.Clone(page.LinkTargets)
		result.pages[i] = page
	}
	result.documents = make([]Document, len(source.documents))
	for i, doc := range source.documents {
		doc.Pages = make([]PageReference, len(doc.Pages))
		for j, page := range source.documents[i].Pages {
			page.LinkTargets = slices.Clone(page.LinkTargets)
			doc.Pages[j] = page
		}
		result.documents[i] = doc
	}
	if source.rootRelationships.name != "" {
		part, err := convertCompositionPartMarkup(source.rootRelationships, source.format, format, source.parts, budget)
		if err != nil {
			return nil, nil, &PartError{Part: source.rootRelationships.name, Err: err}
		}
		result.rootRelationships = part
	}
	for _, key := range slices.Sorted(maps.Keys(source.parts)) {
		part := source.parts[key]
		if compositionIndexRoot(part.media) != "" && !source.retained[key] && !source.auxiliary[key] {
			index, err := source.indexPart(part, budget)
			if err != nil {
				return nil, nil, &PartError{Part: part.name, Err: err}
			}
			part, err = index.project(part, budget)
			if err != nil {
				return nil, nil, &PartError{Part: source.parts[key].name, Err: err}
			}
		}
		part, err := convertCompositionPartMarkup(part, source.format, format, source.parts, budget)
		if err != nil {
			return nil, nil, &PartError{Part: source.parts[key].name, Err: err}
		}
		result.parts[key] = part
	}
	for _, key := range slices.Sorted(maps.Keys(source.relationships)) {
		relations := slices.Clone(source.relationships[key])
		relSource := key
		if owner, exists := source.parts[key]; exists {
			relSource = owner.name
		}
		for index := range relations {
			if err := budget.step(1); err != nil {
				return nil, nil, err
			}
			if err := validateCompositionFormatTicket(relSource, relations[index], source.format, format, source.parts); err != nil {
				return nil, nil, err
			}
			kind, err := compositionFormatRelationship(relations[index].Type, source.format, format)
			if err != nil {
				return nil, nil, err
			}
			relations[index].Type = kind
		}
		result.relationships[key] = relations
	}
	if err := budget.step(0); err != nil {
		return nil, nil, err
	}
	return &result, report, nil
}

// validateCompositionFormatTicket 在OpenXPS转换到XPS时提前拦截非标准Microsoft打印票据内容类型
// 入参: source 关系源部件, relation 源关系, from 原格式, to 目标格式, parts 原快照部件表
// 返回: error 不支持的非标准票据媒体类型错误
func validateCompositionFormatTicket(source string, relation Relationship, from, to Format, parts map[string]packagePart) error {
	if from != FormatOpenXPS || to != FormatXPS || relation.Type != openXPSNamespace+"/printticket" || relation.TargetMode != TargetModeInternal || parts == nil {
		return nil
	}
	target, err := resolvePart(source, relation.Target)
	if err != nil {
		return nil
	}
	if part, present := parts[strings.ToLower(target)]; present && !strings.EqualFold(part.media, printTicketType) {
		return &PartError{Part: part.name, Err: fmt.Errorf("%w: OpenXPS custom print ticket content type %s cannot convert to XPS 1.0", ErrUnsupported, part.media)}
	}
	return nil
}

// convertCompositionPartMarkup 转换方言命名空间、关系类型及相对引用绑定，保持原编码并在目标方言下复核校验
// 入参: part 原部件, source 原格式, target 目标格式, parts 可选原快照部件表, budget 共享预算
// 返回: packagePart 目标部件, error 转换、预算或校验错误
func convertCompositionPartMarkup(part packagePart, source, target Format, parts map[string]packagePart, budget *compositionBudget) (packagePart, error) {
	if err := budget.step(1); err != nil {
		return packagePart{}, err
	}
	layout, _ := fontUsageMarkup(part.media)
	index := compositionIndexRoot(part.media) != ""
	relations := opcRelationshipName(part.name)
	definition := strings.EqualFold(part.media, fixedContentType("signaturedefinitions"))
	discard := strings.EqualFold(part.media, fixedContentType("discard-control"))
	if relations {
		relSource := relationshipSource(part.name)
		records, err := compositionRelationshipRecords(relSource, part, budget)
		if err != nil {
			return packagePart{}, err
		}
		edited := false
		for index := range records {
			if err := budget.step(1); err != nil {
				return packagePart{}, err
			}
			if err := validateCompositionFormatTicket(relSource, records[index], source, target, parts); err != nil {
				return packagePart{}, err
			}
			kind, err := compositionFormatRelationship(records[index].Type, source, target)
			if err != nil {
				return packagePart{}, err
			}
			edited = edited || kind != records[index].Type
			records[index].Type = kind
		}
		data, err := compositionRelationshipMarkup(part, records, edited, budget)
		if err != nil {
			return packagePart{}, err
		}
		if edited {
			part.data, part.items = data, nil
		}
		return part, nil
	}
	if !layout && !definition && !discard {
		return part, nil
	}
	if source != target {
		risky, err := compositionPartMCETargetRisk(part.data, source, target, budget)
		if err != nil {
			return packagePart{}, err
		}
		if risky {
			if index {
				return packagePart{}, fmt.Errorf("%w: composition index acquires target-format semantics", ErrUnsupported)
			}
			part, err = projectCompositionPartMCE(part, source, target, budget)
			if err != nil {
				return packagePart{}, err
			}
		}
	}
	if err := validateCompositionFormatMarkup(part, source, budget); err != nil {
		return packagePart{}, err
	}
	namespace, destination := formatNamespace(source), formatNamespace(target)
	namespaces := map[string]string{namespace: destination}
	for _, suffix := range []string{"/resourcedictionary-key", "/documentstructure", "/signature-definitions", "/discard-control"} {
		namespaces[namespace+suffix] = destination + suffix
	}
	targetNamespaces := compositionDialectNamespaces(target)
	for range 2 {
		if err := budget.scan(int64(len(part.data))); err != nil {
			return packagePart{}, err
		}
	}
	filter := newCompositionConvertMCEFilter(part, source, layout, budget.context)
	data, changed, err := rewriteXMLAttributes(part.data, budget.limits, budget.context, namespaces, filter, func(node *xmlElement, attribute xml.Attr) (string, bool, error) {
		if err := budget.step(1); err != nil {
			return "", false, err
		}
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			value, mapped := namespaces[attribute.Value]
			return value, mapped, nil
		}
		if source != target && (node.Name == (xml.Name{Space: mcNamespace, Local: "Choice"}) && attribute.Name == (xml.Name{Local: "Requires"}) || attribute.Name == (xml.Name{Space: mcNamespace, Local: "MustUnderstand"}) || attribute.Name == (xml.Name{Space: mcNamespace, Local: "Ignorable"})) {
			if err := budget.scan(int64(len(attribute.Value))); err != nil {
				return "", false, err
			}
			uris, err := compatibilityPrefixes(node, attribute.Value)
			if err != nil {
				return "", false, err
			}
			if err := budget.step(len(uris)); err != nil {
				return "", false, err
			}
			for _, uri := range uris {
				if targetNamespaces[uri] {
					return "", false, fmt.Errorf("%w: composition markup acquires target-format semantics", ErrUnsupported)
				}
			}
		}
		if source == FormatXPS && target == FormatOpenXPS && node.Name == (xml.Name{Space: namespace, Local: "LinkTarget"}) && attribute.Name == (xml.Name{Local: "Name"}) {
			value := strings.Trim(attribute.Value, " \t\r\n")
			return value, value != attribute.Value, nil
		}
		if layout && source != target && node.Name.Space == namespace && attribute.Name.Space == "" {
			if attribute.Name.Local == "Source" && (node.Name.Local == "DocumentReference" || node.Name.Local == "PageContent") {
				partName, err := resolvePart(part.name, attribute.Value)
				if err != nil {
					return "", false, err
				}
				value, err := relativePart(part.name, partName)
				if err != nil {
					return "", false, err
				}
				maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
				if int64(len(value)) > maximum {
					return "", false, fmt.Errorf("%w: composition format reference size", ErrLimit)
				}
				if err := budget.scan(int64(len(value))); err != nil {
					return "", false, err
				}
				return value, value != attribute.Value, nil
			}
			references, err := resourceAttributeReferences(node, attribute)
			if err != nil || len(references) == 0 {
				return attribute.Value, false, err
			}
			return compositionResourceAttribute(part.name, part.name, node, attribute, nil, budget, true)
		}
		return attribute.Value, false, nil
	})
	if err != nil {
		return packagePart{}, err
	}
	result := part
	result.data = data
	if changed {
		result.items = nil
	}
	nameFormat := target
	if source == FormatOpenXPS && target == FormatXPS && strings.EqualFold(result.media, fixedContentType("fixeddocument")) {
		nameFormat = FormatOpenXPS
	}
	if err := validateCompositionFormatMarkupMode(result, target, nameFormat, budget); err != nil {
		if errors.Is(err, ErrInvalid) {
			return packagePart{}, fmt.Errorf("%w: target document format: %v", ErrUnsupported, err)
		}
		return packagePart{}, err
	}
	return result, nil
}

// newCompositionConvertMCEFilter 构建跨方言转换时的词元级MCE过滤器，跳过Ignorable子树与保留子树内未选分支后代，保留存活容器与已知兼容分支以完成命名空间及URI重写
// 入参: part 原部件, source 源方言, layout 是否为固定布局或字典, ctx 取消Context
// 返回: func(xml.Token, *xmlElement) (bool, error) 词元跳过回调
func newCompositionConvertMCEFilter(part packagePart, source Format, layout bool, ctx context.Context) func(xml.Token, *xmlElement) (bool, error) {
	var tracker *resourceMarkupScopeTracker
	if layout {
		tracker = newResourceMarkupIgnoreTracker(source, source == FormatOpenXPS, ctx)
	} else {
		understood := map[string]bool{mcNamespace: true, xmlNamespace: true}
		for _, uri := range compositionPartUnderstoodNamespaces(part, source) {
			understood[uri] = true
		}
		tracker = &resourceMarkupScopeTracker{format: source, ignoreOnly: true, processor: compatibilityProcessor{understood: understood, context: ctx}}
	}
	return func(token xml.Token, node *xmlElement) (bool, error) {
		_, _, err := tracker.visit(token, node)
		if err != nil {
			return false, err
		}
		if _, start := token.(xml.StartElement); !start {
			return true, nil
		}
		return tracker.ignoredDepth > 0 || tracker.preservedSkipDepth > 0, nil
	}
}

// compositionDialectNamespaces 返回指定方言的全部标准及标准扩展命名空间集合
// 入参: format 文档方言
// 返回: map[string]bool 命名空间集合
func compositionDialectNamespaces(format Format) map[string]bool {
	ns := formatNamespace(format)
	if ns == "" {
		return nil
	}
	result := map[string]bool{
		ns:                             true,
		ns + "/resourcedictionary-key": true,
		ns + "/documentstructure":      true,
		ns + "/signature-definitions":  true,
		ns + "/discard-control":        true,
	}
	if format == FormatOpenXPS {
		result[openXPS3DNamespace] = true
	}
	return result
}

// compositionPartUnderstoodNamespaces 返回部件在指定方言下可理解的标准命名空间列表
// 入参: part XML部件, format 文档方言
// 返回: []string 理解的命名空间列表
func compositionPartUnderstoodNamespaces(part packagePart, format Format) []string {
	ns := formatNamespace(format)
	switch {
	case strings.EqualFold(part.media, fixedContentType("signaturedefinitions")):
		return []string{ns + "/signature-definitions"}
	case strings.EqualFold(part.media, fixedContentType("discard-control")):
		return []string{ns + "/discard-control"}
	case strings.EqualFold(part.media, fixedContentType("documentstructure")), strings.EqualFold(part.media, fixedContentType("storyfragments")):
		return []string{structureNamespace(format)}
	default:
		return []string{ns, ns + "/resourcedictionary-key"}
	}
}

// compositionPartMCETargetRisk 检查原始XML中的MCE声明是否命中目标方言命名空间激活或源独占扩展冲突
// 入参: data 原始XML字节, source 原方言, target 目标方言, budget 共享预算
// 返回: bool 是否命中跨方言MCE语义变化风险, error XML、前缀解析、源独占扩展不可转换、预算或取消错误
func compositionPartMCETargetRisk(data []byte, source, target Format, budget *compositionBudget) (bool, error) {
	if source == target {
		return false, nil
	}
	if err := budget.scan(int64(len(data))); err != nil {
		return false, err
	}
	targetNS := compositionDialectNamespaces(target)
	understood := map[string]bool{mcNamespace: true, xmlNamespace: true}
	for uri := range compositionDialectNamespaces(source) {
		understood[uri] = true
	}
	tracker := &resourceMarkupScopeTracker{format: source, ignoreOnly: true, processor: compatibilityProcessor{understood: understood, context: budget.context}}
	risky := false
	_, err := decodeXMLVisit(data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := budget.step(1); err != nil {
			return err
		}
		_, _, _ = tracker.visit(token, node)
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if targetNS[node.Name.Space] || source == FormatOpenXPS && target == FormatXPS && node.Name.Space == openXPS3DNamespace {
			risky = true
		}
		ignoredSubtree := tracker.ignoredDepth > 0 || tracker.preservedSkipDepth > 0
		for _, attr := range node.Attr {
			if err := budget.step(1); err != nil {
				return err
			}
			if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
				continue
			}
			if targetNS[attr.Name.Space] || source == FormatOpenXPS && target == FormatXPS && attr.Name.Space == openXPS3DNamespace {
				risky = true
			}
			if ignoredSubtree {
				continue
			}
			checkTarget := node.Name == (xml.Name{Space: mcNamespace, Local: "Choice"}) && attr.Name == (xml.Name{Local: "Requires"}) || attr.Name == (xml.Name{Space: mcNamespace, Local: "MustUnderstand"}) || attr.Name == (xml.Name{Space: mcNamespace, Local: "Ignorable"})
			if !checkTarget {
				continue
			}
			if err := budget.scan(int64(len(attr.Value))); err != nil {
				return err
			}
			uris, err := compatibilityPrefixes(node, attr.Value)
			if err != nil {
				return err
			}
			if err := budget.step(len(uris)); err != nil {
				return err
			}
			for _, uri := range uris {
				if source == FormatOpenXPS && target == FormatXPS && uri == openXPS3DNamespace {
					if attr.Name.Local != "Ignorable" {
						return fmt.Errorf("%w: openxps 3d extension cannot convert to xps", ErrUnsupported)
					}
					risky = true
				}
				if targetNS[uri] {
					risky = true
				}
			}
		}
		return nil
	})
	return risky, err
}

// compositionCanProjectTargetChoices 判断非索引部件在跨方言转换中是否仅含目标方言标准命名空间条件分支而无未知第三方分支
// 入参: part 原始XML部件, source 原方言, target 目标方言, budget 共享预算
// 返回: bool 是否可按源方言有效分支安全跳过沉睡目标方言分支, error XML、前缀解析、预算或取消错误
func compositionCanProjectTargetChoices(part packagePart, source, target Format, budget *compositionBudget) (bool, error) {
	if target == FormatUnknown || source == target || compositionIndexRoot(part.media) != "" {
		return false, nil
	}
	if err := budget.scan(int64(len(part.data))); err != nil {
		return false, err
	}
	sourceNS := map[string]bool{mcNamespace: true, xmlNamespace: true}
	for _, uri := range compositionPartUnderstoodNamespaces(part, source) {
		sourceNS[uri] = true
	}
	targetNS := compositionDialectNamespaces(target)
	hasTargetChoice := false
	hasUnknownChoice := false
	_, err := decodeXMLVisit(part.data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := budget.step(1); err != nil {
			return err
		}
		if hasUnknownChoice {
			return nil
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if node.Name != (xml.Name{Space: mcNamespace, Local: "Choice"}) {
			return nil
		}
		requires, ok := node.attribute("Requires")
		if !ok {
			return nil
		}
		if err := budget.scan(int64(len(requires))); err != nil {
			return err
		}
		uris, err := compatibilityPrefixes(node, requires)
		if err != nil {
			return err
		}
		if err := budget.step(len(uris)); err != nil {
			return err
		}
		for _, uri := range uris {
			if sourceNS[uri] {
				continue
			}
			if targetNS[uri] {
				hasTargetChoice = true
				continue
			}
			hasUnknownChoice = true
			return nil
		}
		return nil
	})
	if err != nil {
		return false, err
	}
	return hasTargetChoice && !hasUnknownChoice, nil
}

// projectCompositionPartMCE 在源方言下执行MCE预处理投影固化当前有效分支，若保留扩展仍冲突目标方言则返回ErrUnsupported
// 入参: part 原部件, source 原方言, target 目标方言, budget 共享预算
// 返回: packagePart 投影固化后的源方言部件, error MCE、冲突扩展、预算或取消错误
func projectCompositionPartMCE(part packagePart, source, target Format, budget *compositionBudget) (packagePart, error) {
	if err := budget.scan(int64(len(part.data))); err != nil {
		return packagePart{}, err
	}
	understood := compositionPartUnderstoodNamespaces(part, source)
	active, ordered, err := preprocessXMLContentContext(part.data, understood, budget.limits, budget.context)
	if err != nil {
		return packagePart{}, err
	}
	targetNS := compositionDialectNamespaces(target)
	forbiddenNS := func(ns string) bool {
		return targetNS[ns] || source == FormatOpenXPS && target == FormatXPS && ns == openXPS3DNamespace
	}
	var checkNode func(*xmlElement, bool) error
	checkNode = func(node *xmlElement, preserved bool) error {
		if err := budget.step(1); err != nil {
			return err
		}
		if forbiddenNS(node.Name.Space) {
			return fmt.Errorf("%w: composition markup preserves target-format namespace %q", ErrUnsupported, node.Name.Space)
		}
		if !preserved {
			var kept []xml.Attr
			for _, attr := range node.Attr {
				if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
					continue
				}
				if forbiddenNS(attr.Name.Space) {
					return fmt.Errorf("%w: composition markup preserves target-format attribute namespace %q", ErrUnsupported, attr.Name.Space)
				}
				kept = append(kept, attr)
			}
			node.Attr = kept
		} else {
			for _, attr := range node.Attr {
				if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
					continue
				}
				if forbiddenNS(attr.Name.Space) {
					return fmt.Errorf("%w: composition markup preserves target-format attribute namespace %q", ErrUnsupported, attr.Name.Space)
				}
				if node.Name == (xml.Name{Space: mcNamespace, Local: "Choice"}) && attr.Name == (xml.Name{Local: "Requires"}) || attr.Name == (xml.Name{Space: mcNamespace, Local: "MustUnderstand"}) || attr.Name == (xml.Name{Space: mcNamespace, Local: "Ignorable"}) {
					uris, err := compatibilityPrefixes(node, attr.Value)
					if err != nil {
						return err
					}
					for _, uri := range uris {
						if forbiddenNS(uri) {
							return fmt.Errorf("%w: composition preserved subtree references target-format namespace %q", ErrUnsupported, uri)
						}
					}
				}
			}
		}
		for _, attr := range node.PreservedAttributes {
			if forbiddenNS(attr.Name.Space) {
				return fmt.Errorf("%w: composition markup preserves target-format attribute namespace %q", ErrUnsupported, attr.Name.Space)
			}
		}
		for _, child := range node.Children {
			if err := checkNode(child, preserved); err != nil {
				return err
			}
		}
		for _, item := range node.PreservedElements {
			if err := checkNode(item, true); err != nil {
				return err
			}
		}
		return nil
	}
	if err := checkNode(active, false); err != nil {
		return packagePart{}, err
	}
	limits := budget.limits
	if strings.EqualFold(part.media, fixedContentType("signaturedefinitions")) || strings.EqualFold(part.media, fixedContentType("discard-control")) {
		limits.MaxPartBytes = min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes)
	}
	projected, err := createdPreservedMarkup(active, ordered, limits, budget.context)
	if err != nil {
		return packagePart{}, err
	}
	maximum := min(limits.MaxPartBytes, limits.MaxPackageBytes, int64(math.MaxInt))
	restored, err := restoreXMLEncoding(part.data, projected, maximum, budget.context)
	if err != nil {
		return packagePart{}, err
	}
	if err := budget.scan(int64(len(restored))); err != nil {
		return packagePart{}, err
	}
	result := part
	result.data, result.items = restored, nil
	return result, nil
}

// normalizeCompositionDocumentLinkTargets 在跨方言整文档保留路径中按实际页面名称映射与去重表规范化LinkTarget，空容器的保留扩展提升至PageContent
// 入参: part 已切换命名空间的原固定文档部件, document 目标文档实例, plan 组合规划, names 已确定的页面名称映射与去重集合
// 返回: []byte 规范化后的文档XML, error 解析、编码、预算或取消错误
func normalizeCompositionDocumentLinkTargets(part packagePart, document compositionDocumentInstance, plan *compositionPlan, names *compositionNames) ([]byte, error) {
	budget := plan.budget
	if err := budget.scan(int64(len(part.data))); err != nil {
		return nil, err
	}
	namespace := formatNamespace(plan.format)
	active, ordered, err := preprocessXMLContentContext(part.data, []string{namespace, namespace + "/resourcedictionary-key"}, budget.limits, budget.context)
	if err != nil {
		return nil, err
	}
	pageCursor := 0
	for _, pageNode := range active.Children {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if pageNode.Name != (xml.Name{Space: namespace, Local: "PageContent"}) {
			continue
		}
		if pageCursor >= len(document.pages) {
			return nil, fmt.Errorf("%w: composition document page count mismatch", ErrInvalid)
		}
		pageInst := document.pages[pageCursor]
		pageCursor++
		outputPagePart := plan.pages[pageInst].reference.Part
		relSource, err := relativePart(document.part, outputPagePart)
		if err != nil {
			return nil, err
		}
		for i := range pageNode.Attr {
			if pageNode.Attr[i].Name.Space == "" && pageNode.Attr[i].Name.Local == "Source" {
				pageNode.Attr[i].Value = relSource
				break
			}
		}
		mapping := names.pages[pageInst]
		dropped := names.droppedTargets[pageInst]
		seenInPage := make(map[string]bool)
		keptPageChildren := make([]*xmlElement, 0, len(pageNode.Children))
		promoted := make(map[*xmlElement][]*xmlElement)
		for _, child := range pageNode.Children {
			if child.Name != (xml.Name{Space: namespace, Local: "PageContent.LinkTargets"}) {
				keptPageChildren = append(keptPageChildren, child)
				continue
			}
			keptLinks := make([]*xmlElement, 0, len(child.Children))
			liftedLinks := make(map[*xmlElement][]*xmlElement)
			var liftedAttrs []xml.Attr
			for _, link := range child.Children {
				if err := budget.step(1); err != nil {
					return nil, err
				}
				if link.Name != (xml.Name{Space: namespace, Local: "LinkTarget"}) {
					keptLinks = append(keptLinks, link)
					continue
				}
				val, ok := link.attribute("Name")
				if !ok {
					keptLinks = append(keptLinks, link)
					continue
				}
				removeLink := dropped[val]
				targetName := ""
				if !removeLink {
					var exists bool
					targetName, exists = mapping[val]
					if !exists {
						return nil, fmt.Errorf("%w: missing composition LinkTarget mapping %q", ErrInvalid, val)
					}
					if seenInPage[targetName] {
						removeLink = true
					}
				}
				if removeLink {
					if len(link.PreservedElements) != 0 {
						child.PreservedElements = append(child.PreservedElements, link.PreservedElements...)
						liftedLinks[link] = link.PreservedElements
					}
					if len(link.PreservedAttributes) != 0 {
						liftedAttrs = append(liftedAttrs, link.PreservedAttributes...)
					}
					continue
				}
				seenInPage[targetName] = true
				for i := range link.Attr {
					if link.Attr[i].Name.Space == "" && link.Attr[i].Name.Local == "Name" {
						link.Attr[i].Value = targetName
						break
					}
				}
				keptLinks = append(keptLinks, link)
			}
			if len(liftedLinks) != 0 && ordered != nil {
				if items, ok := ordered[child]; ok {
					replaced := make([]xmlContent, 0, len(items))
					for _, item := range items {
						if item.element != nil {
							if lifted, hit := liftedLinks[item.element]; hit {
								for _, elem := range lifted {
									replaced = append(replaced, xmlContent{element: elem})
								}
								continue
							}
						}
						replaced = append(replaced, item)
					}
					ordered[child] = replaced
				}
			}
			if len(keptLinks) == 0 {
				if len(child.PreservedElements) != 0 {
					elems := child.PreservedElements
					if ordered != nil {
						if items, ok := ordered[child]; ok {
							allowed := make(map[*xmlElement]bool, len(child.PreservedElements))
							for _, elem := range child.PreservedElements {
								allowed[elem] = true
							}
							seenElem := make(map[*xmlElement]bool, len(child.PreservedElements))
							sortedElems := make([]*xmlElement, 0, len(child.PreservedElements))
							for _, item := range items {
								if item.element != nil && allowed[item.element] && !seenElem[item.element] {
									seenElem[item.element] = true
									sortedElems = append(sortedElems, item.element)
								}
							}
							for _, elem := range child.PreservedElements {
								if !seenElem[elem] {
									sortedElems = append(sortedElems, elem)
								}
							}
							elems = sortedElems
						}
					}
					pageNode.PreservedElements = append(pageNode.PreservedElements, elems...)
					promoted[child] = elems
				}
				if err := mergeCompositionPreservedAttributes(pageNode, child.PreservedAttributes, "PageContent"); err != nil {
					return nil, err
				}
				if err := mergeCompositionPreservedAttributes(pageNode, liftedAttrs, "PageContent"); err != nil {
					return nil, err
				}
				continue
			}
			if err := mergeCompositionPreservedAttributes(child, liftedAttrs, "PageContent.LinkTargets"); err != nil {
				return nil, err
			}
			child.Children = keptLinks
			keptPageChildren = append(keptPageChildren, child)
		}
		pageNode.Children = keptPageChildren
		if len(promoted) != 0 && ordered != nil {
			if items, ok := ordered[pageNode]; ok {
				replaced := make([]xmlContent, 0, len(items))
				for _, item := range items {
					if item.element != nil {
						if lifted, hit := promoted[item.element]; hit {
							for _, elem := range lifted {
								replaced = append(replaced, xmlContent{element: elem})
							}
							continue
						}
					}
					replaced = append(replaced, item)
				}
				ordered[pageNode] = replaced
			}
		}
	}
	var stripNS func(*xmlElement)
	stripNS = func(node *xmlElement) {
		var attrs []xml.Attr
		for _, attr := range node.Attr {
			if attr.Name.Space != xmlnsNamespace && attr.Name != (xml.Name{Local: "xmlns"}) {
				attrs = append(attrs, attr)
			}
		}
		node.Attr = attrs
		for _, child := range node.Children {
			stripNS(child)
		}
	}
	stripNS(active)
	limits := budget.limits
	limits.MaxMetadataBytes = min(limits.MaxMetadataBytes, limits.MaxPackageBytes)
	data, err := createdMarkupContent(active, ordered, limits, budget.context)
	if err != nil {
		return nil, err
	}
	maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
	data, err = restoreXMLEncoding(part.data, data, maximum, budget.context)
	if err != nil {
		return nil, err
	}
	if err := budget.scan(int64(len(data))); err != nil {
		return nil, err
	}
	if err := validateCompositionFormatMarkup(packagePart{name: document.part, media: part.media, data: data}, plan.format, budget); err != nil {
		return nil, err
	}
	return data, nil
}

// mergeCompositionPreservedAttributes 将提升的保留属性合入目标节点，同名同值去重，同名异值返回不支持错误
// 入参: target 目标容器元素, incoming 待合入保留属性列表, container 目标容器错误标识名称
// 返回: error 同展开名异值冲突错误
func mergeCompositionPreservedAttributes(target *xmlElement, incoming []xml.Attr, container string) error {
	for _, attr := range incoming {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		matched := false
		for _, existing := range target.Attr {
			if existing.Name.Space == xmlnsNamespace || existing.Name == (xml.Name{Local: "xmlns"}) {
				continue
			}
			if existing.Name == attr.Name {
				if existing.Value != attr.Value {
					return fmt.Errorf("%w: preserved attribute conflict on %s", ErrUnsupported, container)
				}
				matched = true
				break
			}
		}
		if matched {
			continue
		}
		for _, existing := range target.PreservedAttributes {
			if existing.Name == attr.Name {
				if existing.Value != attr.Value {
					return fmt.Errorf("%w: preserved attribute conflict on %s", ErrUnsupported, container)
				}
				matched = true
				break
			}
		}
		if !matched {
			target.PreservedAttributes = append(target.PreservedAttributes, attr)
		}
	}
	return nil
}

// validateCompositionFixedDocumentNames 按OpenXPS规则校验已切换XPS命名空间的固定文档LinkTarget名称，允许跨页重复与非NCName等待规划阶段规范化
// 入参: root 预处理后的固定文档根节点, namespace 当前文档元素命名空间
// 返回: error 空或非法字符模式名称错误
func validateCompositionFixedDocumentNames(root *xmlElement, namespace string) error {
	var visit func(*xmlElement) error
	visit = func(node *xmlElement) error {
		if node.Name.Space != namespace {
			return nil
		}
		if node.Name.Local == "LinkTarget" {
			for _, attr := range node.Attr {
				if attr.Name.Space == "" && attr.Name.Local == "Name" && !fixedNamePattern(attr.Value) {
					return fmt.Errorf("%w: invalid Name %q on LinkTarget", ErrInvalid, attr.Value)
				}
			}
		}
		for _, child := range node.Children {
			if err := visit(child); err != nil {
				return err
			}
		}
		return nil
	}
	return visit(root)
}

// validateCompositionFormatMarkup 校验方言差异及关系、签署请求等结构，不用目标规则替代源规则
// 入参: part 待校验部件, format 当前格式, budget 共享预算
// 返回: error XML、名称、文字、颜色、关系、预算或取消错误
func validateCompositionFormatMarkup(part packagePart, format Format, budget *compositionBudget) error {
	return validateCompositionFormatMarkupMode(part, format, format, budget)
}

// validateCompositionFormatMarkupMode 校验方言结构并按指定名称规则校验LinkTarget，支持跨方言延后规范化
// 入参: part 待校验部件, format 当前XML结构方言, nameFormat 名称校验采用的方言, budget 共享预算
// 返回: error XML、名称、文字、颜色、关系、预算或取消错误
func validateCompositionFormatMarkupMode(part packagePart, format, nameFormat Format, budget *compositionBudget) error {
	if compositionIndexRoot(part.media) != "" {
		view, err := newCompositionIndexWithNameFormat(part, format, nameFormat, budget)
		if err != nil {
			return err
		}
		return view.inspect(true, budget)
	}
	if err := budget.scan(int64(len(part.data))); err != nil {
		return err
	}
	layout, _ := fontUsageMarkup(part.media)
	relations := opcRelationshipName(part.name)
	definition := strings.EqualFold(part.media, fixedContentType("signaturedefinitions"))
	discard := strings.EqualFold(part.media, fixedContentType("discard-control"))
	namespace := formatNamespace(format)
	graph := compositionProtectionGraph{source: &compositionSource{format: format}, budget: budget}
	tracker := newResourceMarkupScopeTracker(format, format == FormatOpenXPS, budget.context)
	root, err := decodeXMLVisit(part.data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := budget.step(1); err != nil {
			return err
		}
		if layout {
			skip, _, err := tracker.visit(token, node)
			if err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if skip {
				return nil
			}
		} else {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if relations {
				return compositionRelationshipElement(node, budget)
			}
			if definition {
				return graph.definition(node)
			}
			return nil
		}
		if node.Name.Space == namespace && (node.Name.Local == "PolyBezierSegment" || node.Name.Local == "PolyQuadraticBezierSegment") {
			value, present := node.attribute("Points")
			if !present {
				return fmt.Errorf("%w: missing curve points", ErrInvalid)
			}
			points, err := geometryXMLPointsLimited(value, false, false, func(int) error { return budget.step(1) })
			if err != nil {
				return err
			}
			stride := 3
			if node.Name.Local == "PolyQuadraticBezierSegment" {
				stride = 2
			}
			if len(points)%stride != 0 {
				return fmt.Errorf("%w: incomplete curve point group", ErrInvalid)
			}
		}
		for _, attribute := range node.Attr {
			if err := budget.step(1); err != nil {
				return err
			}
			if _, err := resourceAttributeReferences(node, attribute); err != nil {
				return err
			}
			if node.Name == (xml.Name{Space: namespace, Local: "Glyphs"}) && attribute.Name.Space == "" && (attribute.Name.Local == "UnicodeString" || attribute.Name.Local == "DeviceFontName") {
				if err := validateUnicodeString(attribute.Value, format); err != nil {
					return err
				}
			}
		}
		return nil
	})
	if err != nil {
		return err
	}
	if relations {
		_, err = parseRelationshipMarkup(relationshipSource(part.name), part.data, budget.limits, budget.context)
		return err
	}
	if definition {
		_, err = readSignatureDefinitions(part.data, namespace+"/signature-definitions", budget.limits, budget.context)
		return err
	}
	if discard {
		_, err = processDiscardControl(root, part.name, format, budget.context)
		return err
	}
	known := compositionLayoutUnderstoodNamespaces(format)
	if strings.EqualFold(part.media, fixedContentType("documentstructure")) || strings.EqualFold(part.media, fixedContentType("storyfragments")) {
		known = []string{structureNamespace(format)}
	}
	root, err = preprocessXMLContext(root, known, budget.context)
	if err != nil {
		return err
	}
	for _, expected := range []struct{ media, local string }{
		{fixedContentType("fixedpage"), "FixedPage"},
		{fixedContentType("fixeddocument"), "FixedDocument"},
		{fixedContentType("fixeddocumentsequence"), "FixedDocumentSequence"},
		{resourceDictionaryContentType, "ResourceDictionary"},
		{fixedContentType("documentstructure"), "DocumentStructure"},
		{fixedContentType("storyfragments"), "StoryFragments"},
	} {
		if strings.EqualFold(part.media, expected.media) && root.Name != (xml.Name{Space: known[0], Local: expected.local}) {
			return fmt.Errorf("%w: composition format root does not match content type", ErrInvalid)
		}
	}
	return validateFixedNames(root, format)
}

// compositionFormatRelationship 转换已定义的方言关系，不改写相似前缀的自定义类型或其他URI
// 入参: value 原关系类型, source 原格式, target 目标格式
// 返回: string 目标关系类型, error 未理解的方言关系或语义冲突
func compositionFormatRelationship(value string, source, target Format) (string, error) {
	original, destination := formatNamespace(source), formatNamespace(target)
	for _, kind := range []string{"fixedrepresentation", "required-resource", "restricted-font", "printticket", "documentstructure", "storyfragments", "signature-definitions", "discard-control"} {
		if value == original+"/"+kind {
			return destination + "/" + kind, nil
		}
		if value == destination+"/"+kind {
			return "", fmt.Errorf("%w: composition relation acquires target-format semantics", ErrUnsupported)
		}
	}
	if strings.HasPrefix(value, original+"/") {
		return "", fmt.Errorf("%w: custom composition dialect relationship", ErrUnsupported)
	}
	return value, nil
}

// compositionIndexRoot 返回主索引的标准根名称，不包含页面和结构部件
// 入参: media 部件媒体类型
// 返回: string 标准根名称，非主索引时为空
func compositionIndexRoot(media string) string {
	if strings.EqualFold(media, fixedContentType("fixeddocumentsequence")) {
		return "FixedDocumentSequence"
	}
	if strings.EqualFold(media, fixedContentType("fixeddocument")) {
		return "FixedDocument"
	}
	return ""
}

// newCompositionIndex 复用标准兼容性选择器读取主索引，不解释未选分支的后代
// 入参: value 原索引部件, format 原方言, budget 共享预算
// 返回: *compositionIndex 独立索引视图, error 结构、预算或取消错误
func newCompositionIndex(value packagePart, format Format, budget *compositionBudget) (*compositionIndex, error) {
	return newCompositionIndexWithNameFormat(value, format, format, budget)
}

// newCompositionIndexWithNameFormat 复用标准兼容性选择器读取主索引，支持跨方言延后校验XPS 1.0唯一LinkTarget
// 入参: value 原索引部件, format 当前XML命名空间方言, nameFormat 名称校验采用的方言, budget 共享预算
// 返回: *compositionIndex 独立索引视图, error 结构、预算或取消错误
func newCompositionIndexWithNameFormat(value packagePart, format, nameFormat Format, budget *compositionBudget) (*compositionIndex, error) {
	local, namespace := compositionIndexRoot(value.media), formatNamespace(format)
	if local == "" || namespace == "" {
		return nil, fmt.Errorf("%w: composition index input", ErrInvalid)
	}
	if int64(len(value.data)) > budget.limits.MaxPartBytes {
		return nil, fmt.Errorf("%w: composition index bytes", ErrLimit)
	}
	if err := budget.scan(int64(len(value.data))); err != nil {
		return nil, err
	}
	nodes := 0
	content := &xmlContentReader{context: budget.context, limit: budget.limits.MaxXMLNodes, nodes: make(map[*xmlElement][]xmlContent)}
	root, err := decodeXMLVisit(value.data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := budget.step(1); err != nil {
			return err
		}
		if err := content.visit(token, node); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); start {
			nodes++
			return budget.step(len(node.Attr))
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if err := budget.step(nodes); err != nil {
		return nil, err
	}
	processor := compatibilityProcessor{understood: map[string]bool{namespace: true, namespace + "/resourcedictionary-key": true, mcNamespace: true, xmlNamespace: true}, content: content.nodes, includePreserved: true, context: budget.context}
	fragment, err := processor.element(root, compatibilityScope{})
	if err != nil {
		return nil, err
	}
	if len(fragment.elements) != 1 || len(compatibilityWords(fragment.text)) != 0 {
		return nil, fmt.Errorf("%w: MCE preprocessing must retain exactly one root element", ErrInvalid)
	}
	active := fragment.elements[0]
	if active.Name != (xml.Name{Space: namespace, Local: local}) {
		return nil, fmt.Errorf("%w: composition index root", ErrInvalid)
	}
	if err := validateFixedStructure(active, format); err != nil {
		return nil, err
	}
	if nameFormat == FormatOpenXPS && format == FormatXPS && local == "FixedDocument" {
		if err := validateCompositionFixedDocumentNames(active, namespace); err != nil {
			return nil, err
		}
	} else if err := validateFixedNames(active, format); err != nil {
		return nil, err
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return &compositionIndex{original: value, format: format, limits: budget.limits, raw: root, active: active, ordered: content.nodes}, nil
}

// matches 检查索引视图是否与指定原始部件身份及字节内容一致
// 入参: value 原部件, format 原方言
// 返回: bool 部件身份及不可变数据是否一致
func (c *compositionIndex) matches(value packagePart, format Format) bool {
	return c != nil && c.format == format && c.original.name == value.name && strings.EqualFold(c.original.media, value.media) && len(value.data) != 0 && len(c.original.data) == len(value.data) && &c.original.data[0] == &value.data[0]
}

// indexPart 共享同一源部件的索引解析，不将输出实例的身份写入源缓存
// 入参: value 原索引部件, budget 共享预算
// 返回: *compositionIndex 只读树及派生缓存, error 结构、预算或取消错误
func (s *compositionSource) indexPart(value packagePart, budget *compositionBudget) (*compositionIndex, error) {
	if err := budget.step(1); err != nil {
		return nil, err
	}
	if int64(len(value.data)) > budget.limits.MaxPartBytes {
		return nil, fmt.Errorf("%w: composition index bytes", ErrLimit)
	}
	key := strings.ToLower(value.name)
	if index := s.indices[key]; index.matches(value, s.format) {
		if budget.limits.MaxXMLNodes >= index.limits.MaxXMLNodes && budget.limits.MaxXMLDepth >= index.limits.MaxXMLDepth && budget.limits.MaxXMLBindings >= index.limits.MaxXMLBindings {
			copy := *index
			copy.checked, copy.retained = false, false
			return &copy, nil
		}
	}
	nameFormat := s.format
	if s.sourceFormat == FormatOpenXPS && s.format == FormatXPS {
		nameFormat = FormatOpenXPS
	}
	index, err := newCompositionIndexWithNameFormat(value, s.format, nameFormat, budget)
	if err != nil {
		return nil, err
	}
	return index, nil
}

// inspect 检查主索引的引用语义，派生时只访问实际选中内容，原文保持时检查潜在闭包边界
// 入参: retain 是否保留原始索引, budget 共享预算
// 返回: error 未支持语义、预算或取消错误
func (c *compositionIndex) inspect(retain bool, budget *compositionBudget) error {
	if err := budget.step(0); err != nil {
		return err
	}
	if retain && c.retained || !retain && c.checked {
		return nil
	}
	if !retain {
		if err := c.visit(c.active, func(_ xml.Token, node *xmlElement) error {
			if err := budget.step(len(node.Attr) + 1); err != nil {
				return err
			}
			return compositionIndexAttributes(node, c.format, compatibilityScope{}, false)
		}); err != nil {
			return err
		}
		if err := budget.step(0); err != nil {
			return err
		}
		c.checked = true
		return nil
	}
	ns := formatNamespace(c.format)
	processor := compatibilityProcessor{understood: map[string]bool{ns: true, ns + "/resourcedictionary-key": true, mcNamespace: true, xmlNamespace: true}, context: budget.context}
	var visit func(*xmlElement, compatibilityScope) error
	visit = func(node *xmlElement, inherited compatibilityScope) error {
		if err := budget.step(len(node.Attr) + 1); err != nil {
			return err
		}
		isBranch := node.Name.Space == mcNamespace && (node.Name.Local == "Choice" || node.Name.Local == "Fallback")
		scope, err := processor.rulesChecked(node, inherited, !isBranch)
		if err != nil {
			return err
		}
		if node.Name.Space != ns && node.Name.Space != mcNamespace {
			if !scope.ignorable[node.Name.Space] {
				return fmt.Errorf("%w: opaque composition index element", ErrUnsupported)
			}
			if scope.processes(node.Name) {
				if err := compatibilityNoXMLContext(node); err != nil {
					return err
				}
				if err := processor.validateAttributes(node, scope, false); err != nil {
					return err
				}
				if err := compositionIndexAttributes(node, c.format, scope, true); err != nil {
					return err
				}
				for _, child := range node.Children {
					if err := visit(child, scope); err != nil {
						return err
					}
				}
				return nil
			}
			if !scope.preservesElement(node.Name) {
				return fmt.Errorf("%w: opaque composition index element", ErrUnsupported)
			}
			if _, err := processor.preserveElement(node, scope); err != nil {
				return err
			}
			return nil
		}
		if err := compositionIndexAttributes(node, c.format, scope, true); err != nil {
			return err
		}
		if node.Name.Space == mcNamespace && node.Name.Local == "AlternateContent" {
			var selection compatibilitySelection
			for _, child := range node.Children {
				if err := processor.alternative(child, scope, &selection); err != nil {
					return err
				}
			}
		}
		for _, child := range node.Children {
			if err := visit(child, scope); err != nil {
				return err
			}
		}
		return nil
	}
	if err := visit(c.raw, compatibilityScope{}); err != nil {
		return err
	}
	if err := budget.step(0); err != nil {
		return err
	}
	c.retained = true
	return nil
}

// compositionIndexAttributes 限定索引和兼容性包装的已知属性，原文保留路径仅放行声明保留的扩展属性
// 入参: node 原始节点, format 原方言, scope 当前生效MCE作用域, retain 是否检查原文保留边界
// 返回: error 未理解的元素或属性
func compositionIndexAttributes(node *xmlElement, format Format, scope compatibilityScope, retain bool) error {
	var allowed []string
	if node.Name.Space == formatNamespace(format) {
		switch node.Name.Local {
		case "FixedDocumentSequence", "FixedDocument", "PageContent.LinkTargets":
		case "DocumentReference":
			allowed = []string{"Source"}
		case "PageContent":
			allowed = []string{"Source", "Width", "Height"}
		case "LinkTarget":
			allowed = []string{"Name"}
		default:
			return fmt.Errorf("%w: composition index element", ErrUnsupported)
		}
	} else if node.Name.Space == mcNamespace {
		if !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
			return fmt.Errorf("%w: composition index compatibility element", ErrUnsupported)
		}
		if node.Name.Local == "Choice" {
			allowed = []string{"Requires"}
		}
	}
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if attr.Name.Space == mcNamespace && slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attr.Name.Local) {
			continue
		}
		if attr.Name.Space != "" && scope.ignorable[attr.Name.Space] && (!retain || scope.preservesAttribute(attr.Name)) {
			continue
		}
		if attr.Name.Space != "" || !slices.Contains(allowed, attr.Name.Local) {
			return fmt.Errorf("%w: composition index private attribute", ErrUnsupported)
		}
	}
	return nil
}

// visit 遍历已解析的索引树，不重复解析或累计原文字节，访问工作量由回调计费
// 入参: root 只读索引树, visit 节点回调
// 返回: error 回调错误
func (c *compositionIndex) visit(root *xmlElement, visit func(xml.Token, *xmlElement) error) error {
	if err := visit(xml.StartElement{Name: root.Name, Attr: root.Attr}, root); err != nil {
		return err
	}
	for _, child := range root.Children {
		if err := c.visit(child, visit); err != nil {
			return err
		}
	}
	return nil
}

// project 为明确派生的主索引生成独立核心标记，保留MCE声明的保留元素、保留属性及文档相对顺序
// 入参: part 原部件身份, budget 共享预算
// 返回: packagePart 独立派生索引, error 结构、预算或取消错误
func (c *compositionIndex) project(part packagePart, budget *compositionBudget) (packagePart, error) {
	if err := c.inspect(false, budget); err != nil {
		return packagePart{}, err
	}
	clonedOrdered := make(map[*xmlElement][]xmlContent)
	var clone func(*xmlElement, bool) (*xmlElement, error)
	clone = func(node *xmlElement, preserved bool) (*xmlElement, error) {
		if err := budget.step(2 + len(node.Attr) + len(node.Children) + len(node.PreservedElements) + len(node.PreservedAttributes)); err != nil {
			return nil, err
		}
		copied := &xmlElement{
			Name:                node.Name,
			Text:                node.Text,
			Namespaces:          maps.Clone(node.Namespaces),
			PreservedAttributes: slices.Clone(node.PreservedAttributes),
		}
		if preserved {
			copied.Attr = slices.Clone(node.Attr)
		} else {
			for _, attr := range node.Attr {
				if attr.Name.Space != xmlnsNamespace && attr.Name != (xml.Name{Local: "xmlns"}) {
					copied.Attr = append(copied.Attr, attr)
				}
			}
		}
		childMap := make(map[*xmlElement]*xmlElement, len(node.Children)+len(node.PreservedElements))
		if len(node.Children) != 0 {
			copied.Children = make([]*xmlElement, len(node.Children))
			for index, child := range node.Children {
				value, err := clone(child, preserved)
				if err != nil {
					return nil, err
				}
				copied.Children[index] = value
				childMap[child] = value
			}
		}
		if len(node.PreservedElements) != 0 {
			copied.PreservedElements = make([]*xmlElement, len(node.PreservedElements))
			for index, item := range node.PreservedElements {
				value, err := clone(item, true)
				if err != nil {
					return nil, err
				}
				copied.PreservedElements[index] = value
				childMap[item] = value
			}
		}
		if c.ordered != nil {
			if items, ok := c.ordered[node]; ok {
				mapped := make([]xmlContent, 0, len(items))
				for _, item := range items {
					if item.element != nil {
						if value, exists := childMap[item.element]; exists {
							mapped = append(mapped, xmlContent{element: value})
						}
						continue
					}
					mapped = append(mapped, item)
				}
				clonedOrdered[copied] = mapped
			}
		}
		return copied, nil
	}
	root, err := clone(c.active, false)
	if err != nil {
		return packagePart{}, err
	}
	limits := budget.limits
	limits.MaxMetadataBytes = min(limits.MaxMetadataBytes, limits.MaxPackageBytes)
	data, err := createdMarkupContent(root, clonedOrdered, limits, budget.context)
	if err != nil {
		return packagePart{}, err
	}
	if err := budget.scan(int64(len(data))); err != nil {
		return packagePart{}, err
	}
	if err := budget.step(0); err != nil {
		return packagePart{}, err
	}
	part.data, part.items = data, nil
	return part, nil
}

// captureCompositionSourceForTarget 按可选目标方言捕获源快照，跨方言转换时允许对纯目标方言兼容分支延后投影固化
// 入参: r 源阅读器, selected 零基页面索引，可重复, targetFormat 可选目标方言，未知时不启用跨方言兼容投影, budget 多源共享的累计预算
// 返回: *compositionSource 关闭源后仍可使用的快照，失败为nil, error 结构、资源、取消或关闭错误
func captureCompositionSourceForTarget(r *Reader, selected []int, targetFormat Format, budget *compositionBudget) (*compositionSource, error) {
	if budget == nil {
		return nil, fmt.Errorf("%w: missing composition budget", ErrInvalid)
	}
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	shared := budget
	local := *shared
	local.limits.MaxPartBytes = min(local.limits.MaxPartBytes, r.limits.MaxPartBytes)
	local.limits.MaxMetadataBytes = min(local.limits.MaxMetadataBytes, r.limits.MaxMetadataBytes)
	local.limits.MaxXMLDepth = min(local.limits.MaxXMLDepth, r.limits.MaxXMLDepth)
	local.limits.MaxXMLNodes = min(local.limits.MaxXMLNodes, r.limits.MaxXMLNodes)
	local.limits.MaxXMLBindings = min(local.limits.MaxXMLBindings, r.limits.MaxXMLBindings)
	budget = &local
	defer func() {
		local.limits = shared.limits
		*shared = local
	}()
	if err := budget.step(0); err != nil {
		return nil, err
	}
	if len(selected) == 0 || r.pkg == nil {
		return nil, fmt.Errorf("%w: empty composition selection", ErrInvalid)
	}
	if len(r.pages) > budget.limits.MaxPageCount || len(r.documents) > budget.limits.MaxPageCount {
		return nil, fmt.Errorf("%w: composition source index", ErrLimit)
	}
	s := &compositionCapture{reader: r, budget: budget, source: &compositionSource{format: r.format, targetFormat: targetFormat, sequence: r.sequence, selected: make(map[int]bool), parts: make(map[string]packagePart), relationships: make(map[string][]Relationship), parsedRels: make(map[string][]Relationship), parsedXML: make(map[string]*compositionXMLCache), auxiliary: make(map[string]bool), retained: make(map[string]bool), restricted: make(map[string]bool), printResources: make(map[string][]printResourceReference)}, layout: make(map[string]bool), queued: make(map[compositionSourcePart]bool), roles: &createdNavigation{parts: make(map[string]createdNavigationKind)}, owners: make(map[string]bool), unbound: make(map[string]bool), opaque: make(map[string]bool), profiles: make(map[string]bool)}
	for _, index := range selected {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if index < 0 || index >= len(r.pages) {
			return nil, fmt.Errorf("%w: composition page index", ErrInvalid)
		}
		s.source.selected[index] = true
	}
	if err := s.index(); err != nil {
		return nil, err
	}
	if err := s.add(r.sequence, ""); err != nil {
		return nil, err
	}
	if err := s.relations("/", ""); err != nil {
		return nil, err
	}
	for position := 0; position < len(s.queue); position++ {
		item := s.queue[position]
		part, err := s.load(item.part)
		if err != nil {
			return nil, err
		}
		if err := s.markup(part, item.owner); err != nil {
			return nil, &PartError{Part: part.name, Err: err}
		}
		if err := s.relations(part.name, item.owner); err != nil {
			return nil, err
		}
	}
	for part := range s.unbound {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if !s.owners[part] {
			return nil, &PartError{Part: part, Err: fmt.Errorf("%w: dictionary navigation lacks page context", ErrUnsupported)}
		}
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return s.source, nil
}

// index 独立复制完整索引，在扫描前将完整选择的文档或源序列纳入原文保留闭包
// 返回: error 索引、工作量或取消错误
func (s *compositionCapture) index() error {
	r, b := s.reader, s.budget
	if err := b.step(len(r.documents)); err != nil {
		return err
	}
	s.source.documents = make([]Document, len(r.documents))
	first := 0
	s.layout[strings.ToLower(r.sequence)] = true
	s.roles.parts[strings.ToLower(r.sequence)] = createdNavigationSequence
	for index, document := range r.documents {
		if len(document.Pages) > len(r.pages)-first {
			return fmt.Errorf("%w: inconsistent composition document index", ErrInvalid)
		}
		if err := b.step(len(document.Pages)); err != nil {
			return err
		}
		copy := Document{Part: document.Part, Pages: make([]PageReference, len(document.Pages))}
		s.roles.parts[strings.ToLower(document.Part)] = createdNavigationDocument
		selected := false
		complete := len(document.Pages) != 0
		for offset, page := range document.Pages {
			s.roles.parts[strings.ToLower(page.Part)] = createdNavigationPage
			if !strings.EqualFold(page.Part, r.pages[first+offset].Part) {
				return fmt.Errorf("%w: inconsistent composition page index", ErrInvalid)
			}
			if err := b.step(len(page.LinkTargets)); err != nil {
				return err
			}
			page.LinkTargets = slices.Clone(page.LinkTargets)
			copy.Pages[offset] = page
			selected = selected || s.source.selected[first+offset]
			complete = complete && s.source.selected[first+offset]
			if s.source.selected[first+offset] {
				s.layout[strings.ToLower(page.Part)] = true
				if err := s.add(page.Part, page.Part); err != nil {
					return err
				}
			}
		}
		s.source.documents[index] = copy
		if selected {
			s.layout[strings.ToLower(document.Part)] = true
			if err := s.add(document.Part, ""); err != nil {
				return err
			}
		}
		if complete {
			if err := s.retain(document.Part, ""); err != nil {
				return err
			}
			for _, page := range document.Pages {
				if err := s.retain(page.Part, page.Part); err != nil {
					return err
				}
			}
		}
		first += len(document.Pages)
	}
	if first != len(r.pages) {
		return fmt.Errorf("%w: incomplete composition document index", ErrInvalid)
	}
	if err := b.step(len(r.pages)); err != nil {
		return err
	}
	s.source.pages = make([]PageReference, len(r.pages))
	for index, page := range r.pages {
		if err := b.step(len(page.LinkTargets)); err != nil {
			return err
		}
		page.LinkTargets = slices.Clone(page.LinkTargets)
		s.source.pages[index] = page
	}
	if len(s.source.selected) == len(r.pages) {
		return s.retain(r.sequence, "")
	}
	return nil
}

// add 登记资源依赖，拒绝通过内部资源关系夹带未选中的布局或已排除的包元数据
// 入参: name 规范化目标部件URI, owner 引用所属页面，非页面场景可为空
// 返回: error 部件、依赖语义、工作量或取消错误
func (s *compositionCapture) add(name, owner string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	key := strings.ToLower(name)
	actual, exists := s.reader.pkg.names[key]
	if !exists {
		_, err := s.reader.pkg.contentType(name)
		if err == nil {
			err = fmt.Errorf("%w: missing composition source name", ErrInvalid)
		}
		return &PartError{Part: name, Err: err}
	}
	if key == strings.ToLower(opcTypesName) || opcRelationshipName(actual) {
		return &PartError{Part: name, Err: fmt.Errorf("%w: composition resource part", ErrInvalid)}
	}
	media, err := s.reader.pkg.contentType(actual)
	if err != nil {
		return err
	}
	model, err := resourceModelMedia(media)
	if err != nil {
		return &PartError{Part: actual, Err: err}
	}
	if model {
		return &PartError{Part: actual, Err: fmt.Errorf("%w: composition requires opaque X3D dependency preservation", ErrUnsupported)}
	}
	if compositionLayoutMedia(media) && !s.layout[key] {
		return &PartError{Part: actual, Err: fmt.Errorf("%w: resource depends on unselected layout", ErrUnsupported)}
	}
	if strings.EqualFold(media, opcSignatureType) || strings.EqualFold(media, opcSignatureOriginType) || strings.EqualFold(media, fixedContentType("discard-control")) {
		return &PartError{Part: actual, Err: fmt.Errorf("%w: resource depends on excluded package metadata", ErrUnsupported)}
	}
	if strings.EqualFold(media, fixedContentType("fixedpage")) {
		owner = actual
	} else if !strings.EqualFold(media, resourceDictionaryContentType) {
		owner = ""
	}
	item := compositionSourcePart{part: actual, owner: owner}
	if !s.queued[item] {
		s.queued[item] = true
		s.queue = append(s.queue, item)
	}
	return nil
}

// load 在读取前扣除部件和字节预算，同一来源部件只解压并复制一次
// 入参: name 实际部件URI
// 返回: packagePart 原字节及独立条目元数据, error 读取、封装、预算或取消错误
func (s *compositionCapture) load(name string) (packagePart, error) {
	if err := s.budget.step(1); err != nil {
		return packagePart{}, err
	}
	key := strings.ToLower(name)
	if part, present := s.source.parts[key]; present {
		return part, nil
	}
	p := s.reader.pkg
	media, err := p.contentType(name)
	if err != nil {
		return packagePart{}, err
	}
	size, err := p.partSize(key)
	if err != nil {
		return packagePart{}, err
	}
	limit := s.budget.limits.MaxPartBytes
	if opcMetadataPart(name, media) || s.opaque[key] {
		limit = min(limit, s.budget.limits.MaxMetadataBytes)
	}
	if size > uint64(limit) {
		return packagePart{}, &PartError{Part: name, Err: fmt.Errorf("%w: composition metadata or part size", ErrLimit)}
	}
	if err := s.budget.read(size); err != nil {
		return packagePart{}, err
	}
	stream, err := p.openPartStream(s.budget.context, key, PartReadOptions{MaxBytes: limit})
	if err != nil {
		return packagePart{}, &PartError{Part: name, Err: err}
	}
	data, err := io.ReadAll(stream)
	closeErr := stream.Close()
	if err == nil {
		err = closeErr
	}
	if err != nil {
		return packagePart{}, &PartError{Part: name, Err: err}
	}
	if err := s.budget.step(len(p.parts[key]) + len(p.original[key].items)); err != nil {
		return packagePart{}, err
	}
	items, err := p.importItems(key, data)
	if err != nil {
		return packagePart{}, err
	}
	part := packagePart{name: p.names[key], media: media, data: data, items: items}
	s.source.parts[key] = part
	return part, nil
}

// compositionXML 判断需要元数据字节限额的XML媒体类型，不把二进制扩展名当作XML依据
// 入参: media 部件内容类型
// 返回: bool 是否为XML媒体类型
func compositionXML(media string) bool {
	media = strings.ToLower(media)
	return strings.HasSuffix(media, "+xml") || media == "application/xml" || media == "text/xml"
}

// markup 扫描已知保留分支中的资源引用与非布局内部导航目标
// 入参: part 已独立复制的部件, owner 引用所属页面
// 返回: error 未知引用语义、XML、资源或预算错误
func (s *compositionCapture) markup(part packagePart, owner string) error {
	if s.opaque[strings.ToLower(part.name)] {
		return s.budget.step(1)
	}
	var index *compositionIndex
	var indexRoot *xmlElement
	if compositionIndexRoot(part.media) != "" {
		view, err := s.source.indexPart(part, s.budget)
		if err != nil {
			return err
		}
		retain := s.source.retained[strings.ToLower(part.name)] || s.source.auxiliary[strings.ToLower(part.name)]
		if err := view.inspect(retain, s.budget); err != nil {
			return err
		}
		if s.source.indices == nil {
			s.source.indices = make(map[string]*compositionIndex)
		}
		s.source.indices[strings.ToLower(part.name)] = view
		index, indexRoot = view, view.active
		if retain {
			indexRoot = view.raw
		}
	}
	layout, err := fontUsageMarkup(part.media)
	knownPrint, _ := printResourceMedia(part.media)
	if err != nil && !knownPrint {
		return err
	}
	if !layout && !compositionXML(part.media) {
		return nil
	}
	if index == nil {
		if err := s.budget.scan(int64(len(part.data))); err != nil {
			return err
		}
	}
	selectAlt := false
	if layout && index == nil {
		var err error
		selectAlt, err = compositionCanProjectTargetChoices(part, s.source.format, s.source.targetFormat, s.budget)
		if err != nil {
			return err
		}
	}
	tracker := newResourceMarkupScopeTrackerWithAlternate(s.source.format, s.source.format == FormatOpenXPS, selectAlt, s.budget.context)
	visit := func(token xml.Token, node *xmlElement) error {
		if err := s.budget.step(1); err != nil {
			return err
		}
		if layout && index == nil {
			skip, _, err := tracker.visit(token, node)
			if err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := s.budget.step(len(node.Attr)); err != nil {
				return err
			}
			if skip {
				return nil
			}
		} else {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := s.budget.step(len(node.Attr)); err != nil {
				return err
			}
			if !layout {
				return nil
			}
		}
		for _, attribute := range node.Attr {
			if err := s.budget.scan(int64(len(attribute.Value))); err != nil {
				return err
			}
			if (s.source.auxiliary[strings.ToLower(part.name)] || s.source.retained[strings.ToLower(part.name)]) && node.Name.Space == formatNamespace(s.source.format) && attribute.Name.Space == "" && attribute.Name.Local == "Source" {
				kind := ""
				if node.Name.Local == "PageContent" {
					kind = "fixedpage"
				} else if node.Name.Local == "DocumentReference" {
					kind = "fixeddocument"
				}
				if kind != "" {
					target, err := resolvePart(part.name, attribute.Value)
					if err != nil {
						return err
					}
					if err := s.layoutReference(part.name, target, kind); err != nil {
						return err
					}
				}
			}
			if resourceIdentityAttribute(node, attribute, s.source.format) {
				base := part.name
				if attribute.Name.Local == "FixedPage.NavigateUri" {
					if owner == "" {
						if !linkExternal(structureURI(attribute.Value)) {
							s.unbound[strings.ToLower(part.name)] = true
						}
						continue
					}
					base = owner
					s.owners[strings.ToLower(part.name)] = true
					if err := s.budget.scan(int64(len(attribute.Value))); err != nil {
						return err
					}
					if err := s.roles.target(base, attribute.Value); err != nil {
						return err
					}
				}
				if err := s.navigation(base, attribute.Value); err != nil {
					return err
				}
			}
			references, err := resourceAttributeReferences(node, attribute)
			if err != nil {
				return err
			}
			for _, reference := range references {
				if err := s.budget.scan(int64(len(reference.uri))); err != nil {
					return err
				}
				target, err := resolvePart(part.name, reference.uri)
				if err != nil {
					return err
				}
				media, err := s.reader.pkg.contentType(target)
				if err != nil {
					return err
				}
				if !requiredResourceMedia(reference.kind, media) {
					return &PartError{Part: target, Err: fmt.Errorf("%w: composition resource content type", ErrInvalid)}
				}
				if err := s.dependency(part.name, target, owner); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if index != nil {
		err = index.visit(indexRoot, visit)
	} else {
		var root *xmlElement
		root, err = decodeXMLVisit(part.data, s.budget.limits, visit)
		if err == nil && root != nil && layout {
			s.source.parsedXML[strings.ToLower(part.name)] = &compositionXMLCache{data: part.data, limits: s.budget.limits, raw: root}
		}
	}
	if err != nil {
		return err
	}
	return s.printResources(part)
}

// relations 复制关系原字节并收集各兼容分支的资源闭包，跳过包级签名与释放提示目标
// 入参: source 关系源URI，包级关系使用/, owner 引用所属页面
// 返回: error 关系、引用、XML、预算或取消错误
func (s *compositionCapture) relations(source, owner string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	name := createdRelationshipPart(source)
	key := strings.ToLower(name)
	if _, present := s.reader.pkg.parts[key]; !present {
		return nil
	}
	part, err := s.load(name)
	if err != nil {
		return err
	}
	if s.source.retained[strings.ToLower(source)] {
		s.source.retained[key] = true
	}
	if err := s.budget.scan(int64(len(part.data))); err != nil {
		return err
	}
	root, err := decodeXMLVisit(part.data, s.budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := s.budget.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := compositionRelationshipElement(node, s.budget); err != nil {
			return err
		}
		for _, attribute := range node.Attr {
			if err := s.budget.scan(int64(len(attribute.Value))); err != nil {
				return err
			}
		}
		if node.Name.Space == mcNamespace {
			return nil
		}
		if node.Name.Local == "Relationships" {
			return nil
		}
		attributes, err := opcMetadataAttributes(node, opcRelsNS)
		if err != nil {
			return err
		}
		relation, err := parseRelationship(source, xml.StartElement{Name: node.Name, Attr: node.Attr}, attributes, make(map[string]bool))
		if err != nil {
			return err
		}
		if relation.Type == formatNamespace(s.source.format)+"/required-resource" && (s.roles.parts[strings.ToLower(source)] != createdNavigationPage || relation.TargetMode != TargetModeInternal) {
			return fmt.Errorf("%w: required resource relationship owner or mode", ErrInvalid)
		}
		restricted := relation.Type == formatNamespace(s.source.format)+"/restricted-font"
		if restricted && (s.roles.parts[strings.ToLower(source)] != createdNavigationDocument || relation.TargetMode != TargetModeInternal) {
			return fmt.Errorf("%w: restricted font relationship owner or mode", ErrInvalid)
		}
		if source == "/" && relation.Type == opcSignatureOriginRel {
			s.source.signatureOrigin = true
		}
		if source == "/" && s.omitRootRelation(relation) || relation.TargetMode == TargetModeExternal {
			return s.budget.step(1)
		}
		if err := s.budget.scan(int64(len(relation.Target))); err != nil {
			return err
		}
		target, err := resolvePart(source, relation.Target)
		if err != nil {
			return err
		}
		if restricted {
			media, err := s.reader.pkg.contentType(target)
			if err != nil {
				return err
			}
			if !requiredResourceMedia(requiredFont, media) {
				return fmt.Errorf("%w: restricted font content type", ErrInvalid)
			}
			s.source.restricted[strings.ToLower(source)] = true
			if err := s.retain(source, ""); err != nil {
				return err
			}
			s.source.retained[key] = true
		}
		if relation.Type == formatNamespace(s.source.format)+"/printticket" {
			if err := s.ticket(source, target); err != nil {
				return err
			}
		}
		return s.dependency(source, target, owner)
	})
	if err != nil {
		return &PartError{Part: part.name, Err: err}
	}
	for range 2 {
		if err := s.budget.scan(int64(len(part.data))); err != nil {
			return err
		}
	}
	relations, err := parseCompositionRelationshipRoot(source, root, s.budget.context)
	if err != nil {
		return err
	}
	s.source.parsedRels[key] = relations
	if source == "/" {
		relations = slices.DeleteFunc(slices.Clone(relations), s.omitRootRelation)
		s.source.rootRelationships = part
		delete(s.source.parts, key)
	}
	s.source.relationships[strings.ToLower(source)] = relations
	return nil
}

// parseCompositionRelationshipRoot 在已解码的关系XML树上执行MCE预处理与OPC关系语义解析，避免重复解码
// 入参: source 已规范化关系源部件或包根, root 已解码原始XML根, ctx 取消Context
// 返回: []Relationship 当前消费分支的关系, error MCE、结构、关系或取消错误
func parseCompositionRelationshipRoot(source string, root *xmlElement, ctx context.Context) ([]Relationship, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	processed, err := preprocessXMLContext(root, []string{opcRelsNS}, ctx)
	if err != nil {
		return nil, err
	}
	var result []Relationship
	ids := make(map[string]bool)
	err = opcMetadataElements(processed, opcRelsNS, "Relationships", func(element xml.StartElement, attrs map[string]string) error {
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
		return nil, err
	}
	return result, checkContext(ctx)
}

// ticket 按关系角色识别OpenXPS自定义票据，保持不透明载荷，不豁免布局资源的类型约束
// 入参: source 票据所属布局部件, target 票据部件URI
// 返回: error 关系位置、用途冲突、内容类型或预算错误
func (s *compositionCapture) ticket(source, target string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	if s.roles.parts[strings.ToLower(source)] == createdNavigationOther {
		return fmt.Errorf("%w: print ticket source is not fixed layout", ErrInvalid)
	}
	media, err := s.reader.pkg.contentType(target)
	if err != nil {
		return err
	}
	if strings.EqualFold(media, printTicketType) {
		return nil
	}
	if s.source.format != FormatOpenXPS {
		return fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)
	}
	if known, capabilities := printResourceMedia(media); known {
		if capabilities {
			return fmt.Errorf("%w: print capabilities cannot be used as a print ticket", ErrInvalid)
		}
		return nil
	}
	layout, _ := fontUsageMarkup(media)
	if layout {
		return &PartError{Part: target, Err: fmt.Errorf("%w: print ticket conflicts with layout resource type", ErrInvalid)}
	}
	s.opaque[strings.ToLower(target)] = true
	return nil
}

// navigation 将存在的非布局内部导航目标纳入闭包，不复制未选页面或访问外部地址
// 入参: source 所属页面或结构部件URI, value 原始导航URI
// 返回: error URI、资源、工作量或取消错误
func (s *compositionCapture) navigation(source, value string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	if err := s.budget.scan(int64(len(value))); err != nil {
		return err
	}
	value = structureURI(value)
	if linkExternal(value) {
		return nil
	}
	uri, err := url.Parse(value)
	if err != nil {
		return fmt.Errorf("%w: composition navigation URI", ErrInvalid)
	}
	part := source
	if uri.Path != "" {
		part, err = resolvePart(source, uri.EscapedPath())
		if err != nil {
			return err
		}
	}
	key := strings.ToLower(part)
	if s.roles.parts[key] != createdNavigationOther {
		return nil
	}
	if _, present := s.reader.pkg.names[key]; !present {
		return nil
	}
	media, err := s.reader.pkg.contentType(part)
	if err != nil {
		return err
	}
	if compositionLayoutMedia(media) {
		return nil
	}
	return s.add(part, "")
}

// omitRootRelation 判断新包不继承的源签名及页面释放提示关系，不排除签署请求
// 入参: relation 包级关系
// 返回: bool 是否从包级关系记录中排除
func (s *compositionCapture) omitRootRelation(relation Relationship) bool {
	return relation.Type == opcSignatureOriginRel || relation.Type == formatNamespace(s.source.format)+"/discard-control"
}
