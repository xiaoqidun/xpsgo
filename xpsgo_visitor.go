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
	"errors"
	"fmt"
	"math"
	"slices"
	"sort"
	"strings"
)

// defaultWalkMaxBrushDepth 等常量定义场景遍历器默认深度、分辨率与预算上限
const (
	defaultWalkMaxBrushDepth = 8
	defaultWalkFallbackDPI   = 96.0
	defaultWalkMaxElements   = 1 << 20
	defaultWalkMaxGlyphs     = 1 << 20
	defaultWalkMaxFonts      = 256
	defaultWalkMaxFontBytes  = 64 << 20
)

const (
	// WalkGroupCanvas 表示由Canvas节点开启的隔离渲染组
	WalkGroupCanvas WalkGroupKind = iota
	// WalkGroupVisualBrush 表示展开VisualBrush内容时开启的隔离渲染组
	WalkGroupVisualBrush
)

// WalkGroupKind 表示场景遍历器进入或离开的隔离组类别
type WalkGroupKind uint8

// WalkOptions 设置场景遍历器的画刷展开深度、字形轮廓解析、根变换、水印、回退分辨率及资源上限
// MaxBrushDepth默认8、RenderFallbackDPI默认96（负值返回ErrInvalid），Limits零值字段沿用阅读器上限
// Transform可左乘PrintSheet.BackFlipTransform()用于背面遍历；Watermark省略时含水印放置标记NeedsRasterFallback
type WalkOptions struct {
	MaxBrushDepth        int
	ExpandVisualBrush    bool
	ResolveGlyphOutlines bool
	RenderFallbackDPI    float64
	Transform            *Matrix
	Watermark            *PrintWatermarkOptions
	Limits               Limits
}

// WalkClip 保存单层裁切路径几何及其生效时的累计仿射变换矩阵
type WalkClip struct {
	Geometry *Geometry
	Matrix   Matrix
}

// WalkState 保存当前遍历节点累计的规范化图形与文档状态，Index、DocumentIndex与PageIndex为零基页号（辅助页均为-1）
// Opacity为扁平累计不透明度，EdgeMode自祖先Canvas向下继承，按EnterGroup/LeaveGroup构建隔离组应使用LocalOpacity避免双重乘算
// Clip内Geometry指针与OpacityMask指针均为只读零拷贝视图，回调期间及返回后不得修改
type WalkState struct {
	PagePart      string
	Index         int
	DocumentIndex int
	PageIndex     int
	Matrix        Matrix
	Clip          []WalkClip
	Opacity       float64
	OpacityMask   *Brush
	EdgeMode      EdgeMode
	Language      string
	NavigateURI   string
	Name          string
}

// WalkPathEvent 保存规范化后的路径绘制事件及可选光栅化回退建议
// State.Opacity为扁平累计不透明度，LocalOpacity为当前路径自身不透明度，供配合隔离组回调使用
// Data、Fill、Stroke及State内指针字段均为只读零拷贝视图，回调期间及返回后不得修改所指向内容
type WalkPathEvent struct {
	State               WalkState
	LocalOpacity        float64
	Data                *Geometry
	Fill                *Brush
	Stroke              *Brush
	StrokeThickness     float64
	StrokeDashArray     []float64
	StrokeDashOffset    float64
	StrokeDashCap       LineCap
	StrokeStartLineCap  LineCap
	StrokeEndLineCap    LineCap
	StrokeLineJoin      LineJoin
	StrokeMiterLimit    float64
	SnapsToDevicePixels *bool
	AutomationName      string
	AutomationHelpText  string
	NeedsRasterFallback bool
	FallbackDPI         float64
}

// WalkGlyphsEvent 保存规范化字形序列、定位结果与按需提取的矢量轮廓，State.Opacity为累计不透明度，LocalOpacity为自身不透明度
// FontURI为包根绝对URI（含可选#CollectionIndex），Outlines按Glyphs顺序保存字体设计单位轮廓（含粗体扩张与OpenXPS偏移）及最终Transform
// Fill、Outlines元素及State内指针字段均为只读零拷贝视图，回调期间及返回后不得修改
type WalkGlyphsEvent struct {
	State               WalkState
	LocalOpacity        float64
	FontURI             string
	FontPart            string
	CollectionIndex     uint32
	HasCollectionIndex  bool
	FontSize            float64
	Origin              Point
	Text                string
	Indices             []GlyphCluster
	BidiLevel           int
	IsSideways          bool
	StyleSimulations    StyleSimulation
	CaretStops          string
	DeviceFontName      string
	Fill                *Brush
	Glyphs              []GlyphPosition
	Outlines            []*Geometry
	NeedsRasterFallback bool
	FallbackDPI         float64
}

// WalkImageEvent 保存ImageBrush驱动的图像绘制事件，State.Opacity已计入Brush.Opacity，LocalOpacity为宿主路径与Brush.Opacity局部乘积
// ImageTransform已包含State.Matrix并将96DPI源图像映射至页面或纸面坐标，Bounds与ClipPath保持元素局部坐标
// Brush、ClipPath及State内指针字段均为只读零拷贝视图，回调期间及返回后不得修改
type WalkImageEvent struct {
	State               WalkState
	LocalOpacity        float64
	ImagePart           string
	ImageProfilePart    string
	Brush               *Brush
	ImageTransform      Matrix
	Bounds              Rect
	ClipPath            *Geometry
	TileMode            TileMode
	NeedsRasterFallback bool
	FallbackDPI         float64
}

// WalkGroupEvent 保存进入或离开Canvas与VisualBrush隔离组时的图形状态信息
// State.Opacity为扁平累计不透明度，LocalOpacity为本层隔离组不透明度
// Brush及State内指针字段均为只读零拷贝视图，回调期间及返回后不得修改所指向内容
type WalkGroupEvent struct {
	State               WalkState
	Kind                WalkGroupKind
	Brush               *Brush
	LocalOpacity        float64
	EdgeMode            EdgeMode
	NeedsRasterFallback bool
	FallbackDPI         float64
}

// SceneVisitor 定义按绘制顺序接收页面与拼版场景事件的可选回调集合
type SceneVisitor struct {
	EnterGroup func(ctx context.Context, event WalkGroupEvent) error
	LeaveGroup func(ctx context.Context, event WalkGroupEvent) error
	Path       func(ctx context.Context, event WalkPathEvent) error
	Glyphs     func(ctx context.Context, event WalkGlyphsEvent) error
	Image      func(ctx context.Context, event WalkImageEvent) error
	Diagnostic func(diag Diagnostic)
}

// walkConfiguration 保存归一化后的场景遍历参数
type walkConfiguration struct {
	maxBrushDepth        int
	expandVisualBrush    bool
	resolveGlyphOutlines bool
	fallbackDPI          float64
	rootTransform        Matrix
	watermark            *PrintWatermarkOptions
	limits               Limits
}

// sceneWalker 保存单次场景遍历的私有缓存、递归保护状态及资源预算
type sceneWalker struct {
	reader             *Reader
	visitor            *SceneVisitor
	config             walkConfiguration
	forceFallback      bool
	remainingElements  int
	remainingGlyphs    int
	remainingFontBytes int64
	remainingBoldEdges int
	remainingBoldWork  uint64
	remainingBoldExact int
	maxFonts           int
	maxDepth           int
	activeElements     map[Element]bool
	activeBrushes      map[*Brush]bool
	fontData           map[string][]byte
	fontFaces          map[fontCacheKey]*fontSource
}

// String 返回隔离组类别的可读名称
// 返回: string 类别名称
func (k WalkGroupKind) String() string {
	switch k {
	case WalkGroupCanvas:
		return "canvas"
	case WalkGroupVisualBrush:
		return "visual-brush"
	default:
		return fmt.Sprintf("WalkGroupKind(%d)", k)
	}
}

// DefaultWalkOptions 返回场景遍历器的默认配置，采用八层画刷上限、九十六DPI回退分辨率及默认资源上限
// 返回: WalkOptions 场景遍历选项
func DefaultWalkOptions() WalkOptions {
	return WalkOptions{
		MaxBrushDepth:     defaultWalkMaxBrushDepth,
		RenderFallbackDPI: defaultWalkFallbackDPI,
		Limits:            DefaultLimits(),
	}
}

// Walk 按严格绘制顺序遍历指定页面的矢量、文字与图像场景
// 调用回调期间不持有阅读器读锁，允许回调安全调用Font、Image或ResolveLink等只读方法
// 入参: ctx 取消Context，nil采用Background, pageIndex 从零开始的全局页号, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 页面读取、参数、资源上限、取消或回调返回的错误
func (r *Reader) Walk(ctx context.Context, pageIndex int, visitor *SceneVisitor, options *WalkOptions) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	config, err := r.walkConfig(options)
	if err != nil {
		return err
	}
	page, docIndex, localIndex, err := r.loadScenePageByIndex(ctx, pageIndex, config.limits)
	if err != nil {
		return err
	}
	walker := newSceneWalker(r, visitor, config)
	initial := WalkState{
		PagePart:      page.Part,
		Index:         pageIndex,
		DocumentIndex: docIndex,
		PageIndex:     localIndex,
		Matrix:        config.rootTransform,
		Clip:          walkPageRootClips(page, config.rootTransform),
		Opacity:       1,
		Language:      page.Language,
	}
	return walker.walkPageElements(ctx, page.Diagnostics, page.Elements, initial)
}

// WalkPart 按页面部件URI遍历固定页面场景，支持未列入主索引的辅助页面
// 入参: ctx 取消Context，nil采用Background, part 页面部件包根URI, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 页面读取、参数、资源上限、取消或回调返回的错误
func (r *Reader) WalkPart(ctx context.Context, part string, visitor *SceneVisitor, options *WalkOptions) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	config, err := r.walkConfig(options)
	if err != nil {
		return err
	}
	page, globalIndex, docIndex, localIndex, err := r.loadScenePageByPart(ctx, part, config.limits)
	if err != nil {
		return err
	}
	walker := newSceneWalker(r, visitor, config)
	initial := WalkState{
		PagePart:      page.Part,
		Index:         globalIndex,
		DocumentIndex: docIndex,
		PageIndex:     localIndex,
		Matrix:        config.rootTransform,
		Clip:          walkPageRootClips(page, config.rootTransform),
		Opacity:       1,
		Language:      page.Language,
	}
	return walker.walkPageElements(ctx, page.Diagnostics, page.Elements, initial)
}

// WalkPrintSide 按拼版纸面放置顺序遍历物理纸面场景并注入每页变换与裁切，同纸面重复源页仅解析一次
// 回调期间不持有阅读器读锁，可通过WalkOptions.Transform左乘PrintSheet.BackFlipTransform()完成背面翻转遍历
// 入参: ctx 取消Context，nil采用Background, side 拼版纸面模型, visitor 事件回调集合, options 遍历选项，nil采用默认值
// 返回: error 纸面布局、页面读取、资源上限、取消或回调返回的错误
func (r *Reader) WalkPrintSide(ctx context.Context, side *PrintSide, visitor *SceneVisitor, options *WalkOptions) error {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return err
	}
	config, err := r.walkConfig(options)
	if err != nil {
		return err
	}
	if side == nil {
		return fmt.Errorf("%w: nil print side", ErrInvalid)
	}
	if !geometryFinite(side.Width, side.Height) || side.Width <= 0 || side.Height <= 0 {
		return fmt.Errorf("%w: print side dimensions", ErrInvalid)
	}
	if !printBoxWithin(side.MediaClip, Rect{Width: side.Width, Height: side.Height}) {
		return fmt.Errorf("%w: print side media clip", ErrInvalid)
	}
	sideClip, err := printSideGutterClip(side.MediaClip, side.Gutter)
	if err != nil {
		return err
	}
	walker := newSceneWalker(r, visitor, config)
	pageCache := make(map[string]*Page)
	for _, placement := range side.Pages {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(placement.PageClip.X, placement.PageClip.Y, placement.PageClip.Width, placement.PageClip.Height, placement.PageClip.X+placement.PageClip.Width, placement.PageClip.Y+placement.PageClip.Height) || placement.PageClip.Width < 0 || placement.PageClip.Height < 0 || !printBoxWithin(placement.MediaClip, Rect{Width: side.Width, Height: side.Height}) {
			return fmt.Errorf("%w: print placement", ErrInvalid)
		}
		mapped := printTransformBox(placement.PageClip, placement.Transform)
		if !geometryFinite(mapped.X, mapped.Y, mapped.Width, mapped.Height, mapped.X+mapped.Width, mapped.Y+mapped.Height) {
			return fmt.Errorf("%w: print placement transform range", ErrInvalid)
		}
		effectiveMatrix := strokePathCompose(config.rootTransform, placement.Transform)
		if !geometryFillMatrixFinite(effectiveMatrix) {
			return fmt.Errorf("%w: print placement transform range", ErrLimit)
		}
		part, globalIndex, docIndex, localIndex, err := r.resolveWalkPlacement(placement)
		if err != nil {
			return err
		}
		key := strings.ToLower(part)
		page, cached := pageCache[key]
		if !cached {
			page, _, _, _, err = r.loadScenePageByPart(ctx, part, config.limits)
			if err != nil {
				return err
			}
			pageCache[key] = page
		}
		elements := page.Elements
		placementFallback := false
		if placement.Watermark != nil {
			if config.watermark != nil && config.watermark.FontURI != "" {
				materialized, err := r.materializeWalkWatermark(ctx, page.Part, page.Elements, placement.Watermark, config.watermark, config.limits)
				if err != nil {
					if cerr := walkContextError(ctx, err); cerr != nil {
						return cerr
					}
					if errors.Is(err, ErrClosed) || errors.Is(err, ErrLimit) {
						return err
					}
					walker.reportDiagnostic(Diagnostic{Part: page.Part, Element: "PrintWatermark", Message: err.Error()})
					placementFallback = true
				} else {
					elements = materialized
				}
			} else {
				walker.reportDiagnostic(Diagnostic{Part: page.Part, Element: "PrintWatermark", Message: "print placement watermark requires raster fallback or explicit WalkOptions.Watermark"})
				placementFallback = true
			}
		}
		if placement.Negative {
			walker.reportDiagnostic(Diagnostic{Part: page.Part, Element: "PrintNegative", Message: "negative print placement requires raster fallback"})
			placementFallback = true
		}
		clips := walkPrintPlacementClips(sideClip, placement, config.rootTransform, effectiveMatrix)
		initial := WalkState{
			PagePart:      page.Part,
			Index:         globalIndex,
			DocumentIndex: docIndex,
			PageIndex:     localIndex,
			Matrix:        effectiveMatrix,
			Clip:          clips,
			Opacity:       1,
			Language:      page.Language,
		}
		walker.forceFallback = placementFallback
		err = walker.walkPageElements(ctx, page.Diagnostics, elements, initial)
		walker.forceFallback = false
		if err != nil {
			return err
		}
	}
	return nil
}

// walkConfig 合并并校验遍历选项与阅读器默认资源上限
// 入参: options 可选遍历参数
// 返回: walkConfiguration 归一化配置, error 非法参数错误
func (r *Reader) walkConfig(options *WalkOptions) (walkConfiguration, error) {
	if err := r.readLock(); err != nil {
		return walkConfiguration{}, err
	}
	baseLimits := r.limits
	r.mu.RUnlock()
	config := walkConfiguration{
		maxBrushDepth: defaultWalkMaxBrushDepth,
		fallbackDPI:   defaultWalkFallbackDPI,
		rootTransform: IdentityMatrix(),
		limits:        baseLimits,
	}
	if options != nil {
		if options.MaxBrushDepth < 0 {
			return walkConfiguration{}, fmt.Errorf("%w: invalid max brush depth", ErrInvalid)
		}
		if options.MaxBrushDepth > 0 {
			config.maxBrushDepth = options.MaxBrushDepth
		}
		config.expandVisualBrush = options.ExpandVisualBrush
		config.resolveGlyphOutlines = options.ResolveGlyphOutlines
		if options.RenderFallbackDPI != 0 {
			if !geometryFinite(options.RenderFallbackDPI) || options.RenderFallbackDPI < 0 {
				return walkConfiguration{}, fmt.Errorf("%w: invalid render fallback DPI", ErrInvalid)
			}
			config.fallbackDPI = options.RenderFallbackDPI
		}
		if options.Transform != nil {
			if !geometryFillMatrixFinite(*options.Transform) {
				return walkConfiguration{}, fmt.Errorf("%w: invalid walk transform", ErrInvalid)
			}
			config.rootTransform = *options.Transform
		}
		if options.Watermark != nil {
			copied := *options.Watermark
			config.watermark = &copied
		}
		if options.Limits != (Limits{}) {
			config.limits = mergeLimits(baseLimits, options.Limits)
		}
	}
	if err := validateLimits(config.limits); err != nil {
		return walkConfiguration{}, err
	}
	return config, nil
}

// loadScenePageByIndex 在读锁保护下按全局页号加载独立页面及其所属文档与文档内页序号
// 入参: ctx 取消Context, index 全局零基页号, limits 有效资源上限
// 返回: *Page 独立页面, int 文档序号, int 文档内局部页号, error 读取或状态错误
func (r *Reader) loadScenePageByIndex(ctx context.Context, index int, limits Limits) (*Page, int, int, error) {
	if err := r.readLock(); err != nil {
		return nil, -1, -1, err
	}
	defer r.mu.RUnlock()
	scoped := r.scopedWalkReader(limits)
	page, err := scoped.readPageSceneLoaders(index, false, nil, nil, ctx)
	if err != nil {
		return nil, -1, -1, err
	}
	_, docIndex, localIndex := r.pageLocation(index)
	return page, docIndex, localIndex, nil
}

// loadScenePageByPart 在读锁保护下按部件URI加载独立页面及其主索引位置
// 入参: ctx 取消Context, part 页面部件URI, limits 有效资源上限
// 返回: *Page 独立页面, int 全局页号, int 文档序号, int 文档内局部页号, error 读取或状态错误
func (r *Reader) loadScenePageByPart(ctx context.Context, part string, limits Limits) (*Page, int, int, int, error) {
	if err := r.readLock(); err != nil {
		return nil, -1, -1, -1, err
	}
	defer r.mu.RUnlock()
	scoped := r.scopedWalkReader(limits)
	page, err := scoped.readPagePartHeader(part, nil, ctx)
	if err != nil {
		return nil, -1, -1, -1, err
	}
	page, err = scoped.readPageSceneContent(page, false, nil, ctx)
	if err != nil {
		return nil, -1, -1, -1, err
	}
	globalIndex, docIndex, localIndex := r.walkLocationForPart(page.Part)
	return page, globalIndex, docIndex, localIndex, nil
}

// materializeWalkWatermark 短暂持读锁将拼版放置水印物化为独立矢量场景元素后立即释放锁
// 入参: ctx 取消Context, part 页面部件URI, elements 原页面元素, watermark 水印描述, options 水印字体配置, limits 资源上限
// 返回: []Element 组合水印后的独立元素切片, error 水印、字体、预算、关闭或取消错误
func (r *Reader) materializeWalkWatermark(ctx context.Context, part string, elements []Element, watermark *PrintWatermark, options *PrintWatermarkOptions, limits Limits) ([]Element, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	settings := defaultSceneRenderOptions()
	settings.context = ctx
	settings.elements = min(defaultWalkMaxElements, limits.MaxXMLNodes)
	settings.glyphs = defaultWalkMaxGlyphs
	settings.fonts = defaultWalkMaxFonts
	settings.fontBytes = min(int64(defaultWalkMaxFontBytes), limits.MaxPackageBytes)
	scoped := r.scopedWalkReader(limits)
	renderer := newPrintWatermarkRenderer(scoped, options, settings)
	return renderer.elements(part, elements, watermark)
}

// resolveWalkPlacement 在读锁保护下解析纸面放置指向的页面部件及全局、文档、局部页码索引
// 入参: placement 纸面页面放置
// 返回: string 规范化页面URI, int 全局页号, int 文档序号, int 文档内局部页号, error 状态或索引错误
func (r *Reader) resolveWalkPlacement(placement PrintPlacement) (string, int, int, int, error) {
	if err := r.readLock(); err != nil {
		return "", -1, -1, -1, err
	}
	defer r.mu.RUnlock()
	part, err := r.printPlacementPart(placement)
	if err != nil {
		return "", -1, -1, -1, err
	}
	if placement.Part != "" {
		if placement.DocumentIndex < -1 || placement.DocumentIndex >= len(r.documents) {
			return "", -1, -1, -1, fmt.Errorf("%w: print placement document index", ErrInvalid)
		}
		globalIndex, docIndex, localIndex := r.walkLocationForPart(part)
		if globalIndex >= 0 {
			if placement.DocumentIndex != -1 && placement.DocumentIndex != docIndex {
				return "", -1, -1, -1, fmt.Errorf("%w: print placement document index", ErrInvalid)
			}
			return part, globalIndex, docIndex, localIndex, nil
		}
		if placement.DocumentIndex != -1 {
			return "", -1, -1, -1, fmt.Errorf("%w: auxiliary print placement document index", ErrInvalid)
		}
		return part, -1, -1, -1, nil
	}
	_, docIndex, localIndex := r.pageLocation(placement.Page)
	return part, placement.Page, docIndex, localIndex, nil
}

// scopedWalkReader 构造使用独立资源上限的浅拷贝阅读器视图，不改变原阅读器配置
// 入参: limits 本次遍历的资源上限
// 返回: *Reader 临时只读阅读器视图
func (r *Reader) scopedWalkReader(limits Limits) *Reader {
	pkg := *r.pkg
	pkg.limits = limits
	return &Reader{
		pkg:       &pkg,
		format:    r.format,
		limits:    limits,
		sequence:  r.sequence,
		documents: r.documents,
		pages:     r.pages,
		fixedXML:  r.fixedXML,
	}
}

// walkLocationForPart 按OPC等价部件名查找页面在主索引中的全局页号、文档序号与文档内局部页号
// 入参: part 页面部件URI
// 返回: int 全局页号, int 文档序号, int 文档内局部页号，辅助页面返回-1, -1, -1
func (r *Reader) walkLocationForPart(part string) (int, int, int) {
	offset := 0
	for docIndex, doc := range r.documents {
		for localIndex, ref := range doc.Pages {
			if strings.EqualFold(ref.Part, part) {
				return offset + localIndex, docIndex, localIndex
			}
		}
		offset += len(doc.Pages)
	}
	return -1, -1, -1
}

// readWalkFontFace 短暂持读锁按预算读取并解混淆单个字体面，随后立即释放锁
// 入参: ctx 取消Context, part 规范化字体部件URI, index 集合索引, maximum 本次允许读取的字节上限
// 返回: *fontFace 独立字体面, error 读取、预算、取消或关闭错误
func (r *Reader) readWalkFontFace(ctx context.Context, part string, index uint32, maximum int64) (*fontFace, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	size, err := r.pkg.partSize(strings.ToLower(part))
	if err != nil {
		return nil, wrapPartError(part, "", err)
	}
	if maximum < 0 || size > uint64(maximum) {
		return nil, wrapPartError(part, "", fmt.Errorf("%w: font byte budget", ErrLimit))
	}
	return r.pkg.readFontFaceLimit(part, index, maximum)
}

// newSceneWalker 创建单次遍历独占的场景遍历器状态
// 入参: r 阅读器实例, visitor 事件回调集合, config 归一化配置
// 返回: *sceneWalker 遍历器实例
func newSceneWalker(r *Reader, visitor *SceneVisitor, config walkConfiguration) *sceneWalker {
	if visitor == nil {
		visitor = &SceneVisitor{}
	}
	fontBudget := min(int64(defaultWalkMaxFontBytes), config.limits.MaxPackageBytes)
	boldDefaults := defaultSceneRenderOptions()
	return &sceneWalker{
		reader:             r,
		visitor:            visitor,
		config:             config,
		remainingElements:  min(defaultWalkMaxElements, config.limits.MaxXMLNodes),
		remainingGlyphs:    defaultWalkMaxGlyphs,
		remainingFontBytes: fontBudget,
		remainingBoldEdges: boldDefaults.edges,
		remainingBoldWork:  boldDefaults.work,
		remainingBoldExact: rasterMaxExact,
		maxFonts:           defaultWalkMaxFonts,
		maxDepth:           config.limits.MaxXMLDepth,
		activeElements:     make(map[Element]bool),
		activeBrushes:      make(map[*Brush]bool),
		fontData:           make(map[string][]byte),
		fontFaces:          make(map[fontCacheKey]*fontSource),
	}
}

// walkPageElements 转发页面诊断并按声明顺序遍历给定根元素切片
// 入参: ctx 取消Context, diagnostics 页面诊断列表, elements 根元素列表, initial 页面根状态
// 返回: error 遍历、资源、取消或回调错误
func (w *sceneWalker) walkPageElements(ctx context.Context, diagnostics []Diagnostic, elements []Element, initial WalkState) error {
	for _, diag := range diagnostics {
		w.reportDiagnostic(diag)
	}
	return w.walkElements(ctx, elements, initial, 0, 0)
}

// walkElements 按Z-order依次遍历同级元素列表
// 入参: ctx 取消Context, elements 元素列表, state 父级累计状态, depth 元素嵌套深度, brushDepth 视觉画刷递归深度
// 返回: error 遍历、资源、取消或回调错误
func (w *sceneWalker) walkElements(ctx context.Context, elements []Element, state WalkState, depth, brushDepth int) error {
	for _, element := range elements {
		if err := w.walkElement(ctx, element, state, depth, brushDepth); err != nil {
			return err
		}
	}
	return nil
}

// walkElement 维护节点递归保护、更新局部图形状态并按元素类型分发事件
// 入参: ctx 取消Context, element 当前元素, parent 父级累计状态, depth 元素深度, brushDepth 视觉画刷深度
// 返回: error 遍历、资源、取消或回调错误
func (w *sceneWalker) walkElement(ctx context.Context, element Element, parent WalkState, depth, brushDepth int) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if depth >= w.maxDepth {
		return fmt.Errorf("%w: scene walk depth exceeded", ErrLimit)
	}
	if w.remainingElements <= 0 {
		return fmt.Errorf("%w: scene walk element budget exceeded", ErrLimit)
	}
	w.remainingElements--
	props := contentProperties(element)
	if props == nil {
		return fmt.Errorf("%w: nil or unknown scene element", ErrInvalid)
	}
	if w.activeElements[element] {
		return fmt.Errorf("%w: cyclic visual tree", ErrInvalid)
	}
	w.activeElements[element] = true
	defer delete(w.activeElements, element)
	state, err := applyElementState(parent, props)
	if err != nil {
		return wrapPartError(parent.PagePart, "", err)
	}
	if canvas, ok := element.(*Canvas); ok {
		switch canvas.EdgeMode {
		case "":
		case EdgeModeAliased:
			state.EdgeMode = EdgeModeAliased
		default:
			return wrapPartError(state.PagePart, "Canvas", fmt.Errorf("%w: canvas edge mode", ErrInvalid))
		}
	}
	if props.Opacity == 0 || state.Opacity == 0 || geometryMatrixSingular(state.Matrix) {
		return nil
	}
	switch node := element.(type) {
	case *Canvas:
		return w.walkCanvas(ctx, node, state, depth, brushDepth)
	case *Path:
		return w.walkPath(ctx, node, state, depth, brushDepth)
	case *Glyphs:
		return w.walkGlyphs(ctx, node, state)
	default:
		return fmt.Errorf("%w: unknown scene element", ErrInvalid)
	}
}

// walkCanvas 发出Canvas进入与离开组事件并按声明顺序遍历子元素
// 入参: ctx 取消Context, canvas 画布元素, state 当前有效状态, depth 当前深度, brushDepth 画刷深度
// 返回: error 遍历或回调错误
func (w *sceneWalker) walkCanvas(ctx context.Context, canvas *Canvas, state WalkState, depth, brushDepth int) error {
	groupEvent := WalkGroupEvent{
		State:               state.clone(),
		Kind:                WalkGroupCanvas,
		LocalOpacity:        canvas.Opacity,
		EdgeMode:            state.EdgeMode,
		NeedsRasterFallback: w.forceFallback || state.OpacityMask != nil,
		FallbackDPI:         w.config.fallbackDPI,
	}
	if w.visitor.EnterGroup != nil {
		if err := w.visitor.EnterGroup(ctx, groupEvent); err != nil {
			return err
		}
	}
	prevFallback := w.forceFallback
	if state.OpacityMask != nil {
		w.forceFallback = true
	}
	childState := state
	childState.OpacityMask = nil
	childState.Name = ""
	err := w.walkElements(ctx, canvas.Elements, childState, depth+1, brushDepth)
	w.forceFallback = prevFallback
	if err != nil {
		return err
	}
	if w.visitor.LeaveGroup != nil {
		groupEvent.State = state.clone()
		if err := w.visitor.LeaveGroup(ctx, groupEvent); err != nil {
			return err
		}
	}
	return nil
}

// walkPath 分发Path关联的图像、可展开VisualBrush以及常规矢量路径事件
// 入参: ctx 取消Context, path 路径元素, state 当前有效状态, depth 元素深度, brushDepth 画刷深度
// 返回: error 遍历或回调错误
func (w *sceneWalker) walkPath(ctx context.Context, path *Path, state WalkState, depth, brushDepth int) error {
	if path.Fill == nil && path.Stroke == nil {
		return nil
	}
	if path.Data == nil {
		return wrapPartError(state.PagePart, "Path", fmt.Errorf("%w: missing scene geometry", ErrInvalid))
	}
	if len(path.Data.Figures) == 0 {
		return nil
	}
	if path.Fill != nil && path.Fill.Kind == BrushImage && w.visitor.Image != nil {
		if path.Stroke != nil && (path.Opacity < 1 || state.OpacityMask != nil) {
			if w.visitor.Path != nil {
				return w.emitPathEvent(ctx, path, state, path.Fill, path.Stroke, true)
			}
			return w.emitImageBrush(ctx, path, state, true)
		}
		if err := w.emitImageBrush(ctx, path, state, false); err != nil {
			return err
		}
		if path.Stroke == nil {
			return nil
		}
		return w.emitPathEvent(ctx, path, state, nil, path.Stroke, path.Stroke.Kind == BrushVisual || path.Stroke.Kind == BrushImage)
	}
	if path.Fill != nil && path.Fill.Kind == BrushVisual && w.config.expandVisualBrush {
		expanded, err := w.expandVisualBrush(ctx, path, path.Fill, state, depth, brushDepth)
		if err != nil {
			return err
		}
		if expanded {
			if path.Stroke == nil {
				return nil
			}
			return w.emitPathEvent(ctx, path, state, nil, path.Stroke, path.Stroke.Kind == BrushVisual || path.Stroke.Kind == BrushImage)
		}
		return w.emitPathEvent(ctx, path, state, path.Fill, path.Stroke, true)
	}
	needsFallback := state.OpacityMask != nil || (path.Fill != nil && (path.Fill.Kind == BrushVisual || path.Fill.Kind == BrushImage)) || (path.Stroke != nil && (path.Stroke.Kind == BrushVisual || path.Stroke.Kind == BrushImage))
	return w.emitPathEvent(ctx, path, state, path.Fill, path.Stroke, needsFallback)
}

// emitImageBrush 解析ImageBrush部件引用、放置变换与宿主几何外包矩形并触发Image回调
// 入参: ctx 取消Context, path 宿主路径, state 当前有效状态, forceFallback 是否强制标记光栅回退
// 返回: error 回调或边界错误
func (w *sceneWalker) emitImageBrush(ctx context.Context, path *Path, state WalkState, forceFallback bool) error {
	brush := path.Fill
	basePart := brush.Part
	if basePart == "" {
		basePart = state.PagePart
	}
	if basePart == "" {
		basePart = "/"
	}
	brushFallback := false
	imagePart, err := resolvePart(basePart, brush.ImageSource)
	if err != nil {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "ImageSource", Message: err.Error()})
		imagePart = brush.ImageSource
		brushFallback = true
	}
	profilePart := ""
	if brush.ImageProfileURI != "" {
		resolved, profErr := resolvePart(basePart, brush.ImageProfileURI)
		if profErr != nil {
			w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "ImageProfileUri", Message: profErr.Error()})
			profilePart = brush.ImageProfileURI
			brushFallback = true
		} else {
			profilePart = resolved
		}
	}
	bounds, err := walkGeometryBounds(path.Data)
	if err != nil {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Path", Attribute: "Data", Message: err.Error()})
		brushFallback = true
	}
	brushOpacity := 1.0
	if !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "Opacity", Message: "image brush opacity out of range"})
		brushFallback = true
	} else {
		brushOpacity = brush.Opacity
	}
	imageTransform := state.Matrix
	if brush.TileMode > TileFlipXY {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Message: "invalid image brush tile mode"})
		brushFallback = true
	} else if !geometryFinite(brush.Viewbox.X, brush.Viewbox.Y, brush.Viewbox.Width, brush.Viewbox.Height, brush.Viewport.X, brush.Viewport.Y, brush.Viewport.Width, brush.Viewport.Height) || brush.Viewbox.Width <= 0 || brush.Viewbox.Height <= 0 || brush.Viewport.Width <= 0 || brush.Viewport.Height <= 0 {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "Viewbox", Message: "degenerate image brush viewbox or viewport"})
		brushFallback = true
	} else {
		transformOK := true
		brushMatrix := state.Matrix
		if brush.Transform != nil {
			if !geometryFillMatrixFinite(*brush.Transform) {
				w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "Transform", Message: "non-finite image brush transform"})
				brushFallback = true
				transformOK = false
			} else {
				brushMatrix = strokePathCompose(brushMatrix, *brush.Transform)
			}
		}
		if transformOK {
			sx := brush.Viewport.Width / brush.Viewbox.Width
			sy := brush.Viewport.Height / brush.Viewbox.Height
			mapping := Matrix{A: sx, D: sy, E: brush.Viewport.X - brush.Viewbox.X*sx, F: brush.Viewport.Y - brush.Viewbox.Y*sy}
			composed := strokePathCompose(brushMatrix, mapping)
			if !geometryFillMatrixFinite(composed) {
				w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "ImageBrush", Attribute: "Transform", Message: "image brush transform overflow"})
				brushFallback = true
			} else {
				imageTransform = composed
			}
		}
	}
	imgState := state.clone()
	imgState.Opacity = colorClamp(state.Opacity * brushOpacity)
	event := WalkImageEvent{
		State:               imgState,
		LocalOpacity:        colorClamp(path.Opacity * brushOpacity),
		ImagePart:           imagePart,
		ImageProfilePart:    profilePart,
		Brush:               brush,
		ImageTransform:      imageTransform,
		Bounds:              bounds,
		ClipPath:            path.Data,
		TileMode:            brush.TileMode,
		NeedsRasterFallback: w.forceFallback || forceFallback || brushFallback || state.OpacityMask != nil,
		FallbackDPI:         w.config.fallbackDPI,
	}
	return w.visitor.Image(ctx, event)
}

// emitPathEvent 构造WalkPathEvent并调用Path回调，Data、Fill与Stroke作为只读零拷贝视图透传
// 入参: ctx 取消Context, path 路径元素, state 当前有效状态, fill 生效填充画刷, stroke 生效描边画刷, needsFallback 是否建议局部光栅化回退
// 返回: error 回调错误
func (w *sceneWalker) emitPathEvent(ctx context.Context, path *Path, state WalkState, fill, stroke *Brush, needsFallback bool) error {
	if w.visitor.Path == nil {
		return nil
	}
	event := WalkPathEvent{
		State:               state.clone(),
		LocalOpacity:        path.Opacity,
		Data:                path.Data,
		Fill:                fill,
		Stroke:              stroke,
		StrokeThickness:     path.StrokeThickness,
		StrokeDashArray:     slices.Clone(path.StrokeDashArray),
		StrokeDashOffset:    path.StrokeDashOffset,
		StrokeDashCap:       path.StrokeDashCap,
		StrokeStartLineCap:  path.StrokeStartLineCap,
		StrokeEndLineCap:    path.StrokeEndLineCap,
		StrokeLineJoin:      path.StrokeLineJoin,
		StrokeMiterLimit:    path.StrokeMiterLimit,
		SnapsToDevicePixels: cloneBoolPtr(path.SnapsToDevicePixels),
		AutomationName:      path.AutomationName,
		AutomationHelpText:  path.AutomationHelpText,
		NeedsRasterFallback: w.forceFallback || needsFallback,
		FallbackDPI:         w.config.fallbackDPI,
	}
	return w.visitor.Path(ctx, event)
}

// expandVisualBrush 校验深度上限、环引用、平铺模式、蒙版及坐标映射，满足条件时展开VisualBrush内部矢量子树
// 入参: ctx 取消Context, path 宿主路径, brush 视觉画刷, state 宿主状态, depth 元素深度, brushDepth 画刷深度
// 返回: bool 是否成功完成矢量展开, error 取消、资源上限或回调错误
func (w *sceneWalker) expandVisualBrush(ctx context.Context, path *Path, brush *Brush, state WalkState, depth, brushDepth int) (bool, error) {
	if brush == nil || brush.Visual == nil {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "Visual", Message: "visual brush has no visual content"})
		return false, nil
	}
	if brush.TileMode > TileFlipXY {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Message: "invalid visual brush tile mode"})
		return false, nil
	}
	if brush.TileMode != TileNone {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "TileMode", Message: "tiled visual brush requires raster fallback"})
		return false, nil
	}
	if state.OpacityMask != nil {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "OpacityMask", Message: "visual brush host opacity mask requires raster fallback"})
		return false, nil
	}
	if path.Stroke != nil && path.Opacity < 1 {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "Opacity", Message: "translucent stroked visual brush host requires raster fallback"})
		return false, nil
	}
	if brushDepth >= w.config.maxBrushDepth {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Message: fmt.Sprintf("visual brush recursion depth exceeds limit %d", w.config.maxBrushDepth)})
		return false, nil
	}
	if w.activeBrushes[brush] || w.activeElements[brush.Visual] {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Message: "cyclic visual brush reference detected"})
		return false, nil
	}
	brushMatrix := state.Matrix
	if brush.Transform != nil {
		if !geometryFillMatrixFinite(*brush.Transform) {
			w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "Transform", Message: "non-finite visual brush transform"})
			return false, nil
		}
		brushMatrix = strokePathCompose(brushMatrix, *brush.Transform)
	}
	if !geometryFillMatrixFinite(brushMatrix) {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "Transform", Message: "visual brush transform overflow"})
		return false, nil
	}
	if !geometryFinite(brush.Viewbox.X, brush.Viewbox.Y, brush.Viewbox.Width, brush.Viewbox.Height, brush.Viewport.X, brush.Viewport.Y, brush.Viewport.Width, brush.Viewport.Height) || brush.Viewbox.Width <= 0 || brush.Viewbox.Height <= 0 || brush.Viewport.Width <= 0 || brush.Viewport.Height <= 0 {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Attribute: "Viewbox", Message: "degenerate visual brush viewbox or viewport"})
		return false, nil
	}
	sx := brush.Viewport.Width / brush.Viewbox.Width
	sy := brush.Viewport.Height / brush.Viewbox.Height
	mapping := Matrix{A: sx, D: sy, E: brush.Viewport.X - brush.Viewbox.X*sx, F: brush.Viewport.Y - brush.Viewbox.Y*sy}
	visualMatrix := strokePathCompose(brushMatrix, mapping)
	if !geometryFillMatrixFinite(visualMatrix) || !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 {
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "VisualBrush", Message: "visual brush mapping or opacity out of range"})
		return false, nil
	}
	groupClips := slices.Clone(state.Clip)
	if path.Data != nil {
		groupClips = append(groupClips, WalkClip{Geometry: path.Data, Matrix: state.Matrix})
	}
	groupClips = append(groupClips, WalkClip{Geometry: renderBoxGeometry(brush.Viewport), Matrix: brushMatrix})
	groupState := WalkState{
		PagePart:      state.PagePart,
		Index:         state.Index,
		DocumentIndex: state.DocumentIndex,
		PageIndex:     state.PageIndex,
		Matrix:        visualMatrix,
		Clip:          groupClips,
		Opacity:       colorClamp(state.Opacity * brush.Opacity),
		EdgeMode:      state.EdgeMode,
		Language:      state.Language,
		NavigateURI:   state.NavigateURI,
	}
	groupEvent := WalkGroupEvent{
		State:               groupState.clone(),
		Kind:                WalkGroupVisualBrush,
		Brush:               brush,
		LocalOpacity:        colorClamp(path.Opacity * brush.Opacity),
		EdgeMode:            state.EdgeMode,
		NeedsRasterFallback: w.forceFallback,
		FallbackDPI:         w.config.fallbackDPI,
	}
	w.activeBrushes[brush] = true
	defer delete(w.activeBrushes, brush)
	if w.visitor.EnterGroup != nil {
		if err := w.visitor.EnterGroup(ctx, groupEvent); err != nil {
			return false, err
		}
	}
	if err := w.walkElement(ctx, brush.Visual, groupState, depth+1, brushDepth+1); err != nil {
		return false, err
	}
	if w.visitor.LeaveGroup != nil {
		groupEvent.State = groupState.clone()
		if err := w.visitor.LeaveGroup(ctx, groupEvent); err != nil {
			return false, err
		}
	}
	return true, nil
}

// walkGlyphs 解析规范化字体URI、字形定位与按需轮廓几何并触发Glyphs回调
// 入参: ctx 取消Context, glyphs 字形元素, state 当前有效状态
// 返回: error 资源上限、取消或回调错误
func (w *sceneWalker) walkGlyphs(ctx context.Context, glyphs *Glyphs, state WalkState) error {
	if w.visitor.Glyphs == nil {
		return nil
	}
	fontPart := glyphs.FontPart
	collectionIndex := glyphs.CollectionIndex
	hasCollectionIndex := glyphs.HasCollectionIndex
	invalidFontURI := false
	if fontPart == "" {
		if glyphs.FontURI == "" {
			w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Attribute: "FontUri", Message: "missing font URI"})
			invalidFontURI = true
		} else {
			partURI, idx, hasIdx, err := ParseFontURI(strings.Trim(glyphs.FontURI, " \t\r\n"))
			if err != nil {
				w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Attribute: "FontUri", Message: err.Error()})
				invalidFontURI = true
			} else {
				basePart := glyphs.Part
				if basePart == "" {
					basePart = state.PagePart
				}
				if basePart == "" {
					basePart = "/"
				}
				resolved, resErr := resolvePart(basePart, partURI)
				if resErr != nil {
					w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Attribute: "FontUri", Message: resErr.Error()})
					invalidFontURI = true
				} else {
					fontPart = resolved
					collectionIndex = idx
					hasCollectionIndex = hasIdx
				}
			}
		}
	}
	fontURI := fontPart
	if fontPart != "" && hasCollectionIndex {
		fontURI = fmt.Sprintf("%s#%d", fontPart, collectionIndex)
	} else if fontURI == "" {
		fontURI = glyphs.FontURI
	}
	event := WalkGlyphsEvent{
		State:               state.clone(),
		LocalOpacity:        glyphs.Opacity,
		FontURI:             fontURI,
		FontPart:            fontPart,
		CollectionIndex:     collectionIndex,
		HasCollectionIndex:  hasCollectionIndex,
		FontSize:            glyphs.FontRenderingEmSize,
		Origin:              glyphs.Origin,
		Text:                glyphs.Text,
		Indices:             cloneGlyphClusters(glyphs.Indices),
		BidiLevel:           glyphs.BidiLevel,
		IsSideways:          glyphs.IsSideways,
		StyleSimulations:    glyphs.StyleSimulations,
		CaretStops:          glyphs.CaretStops,
		DeviceFontName:      glyphs.DeviceFontName,
		Fill:                glyphs.Fill,
		NeedsRasterFallback: w.forceFallback || invalidFontURI || state.OpacityMask != nil || (glyphs.Fill != nil && (glyphs.Fill.Kind == BrushVisual || glyphs.Fill.Kind == BrushImage)),
		FallbackDPI:         w.config.fallbackDPI,
	}
	if fontPart != "" {
		if err := w.populateGlyphPositions(ctx, glyphs, fontPart, collectionIndex, state, &event); err != nil {
			return err
		}
	}
	return w.visitor.Glyphs(ctx, event)
}

// populateGlyphPositions 复用字形定位和轮廓原语填充Glyphs事件，非致命字体问题通过诊断上报并标记回退
// 入参: ctx 取消Context, glyphs 字形元素, fontPart 规范化字体部件URI, collectionIndex 字体集合索引, state 当前有效状态, event 待填充事件
// 返回: error 取消、关闭或资源上限错误
func (w *sceneWalker) populateGlyphPositions(ctx context.Context, glyphs *Glyphs, fontPart string, collectionIndex uint32, state WalkState, event *WalkGlyphsEvent) error {
	count, err := glyphRunCount(glyphs, w.remainingGlyphs)
	if err != nil {
		if errors.Is(err, ErrLimit) {
			return wrapPartError(state.PagePart, "Glyphs", err)
		}
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: err.Error()})
		event.NeedsRasterFallback = true
		return nil
	}
	source, err := w.loadFont(ctx, fontPart, collectionIndex)
	if err != nil {
		if cerr := walkContextError(ctx, err); cerr != nil {
			return cerr
		}
		if errors.Is(err, ErrClosed) || errors.Is(err, ErrLimit) {
			return err
		}
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Attribute: "FontUri", Message: err.Error()})
		event.NeedsRasterFallback = true
		return nil
	}
	bitmapOnly := fontIsBitmapOnly(source.face)
	yMax := source.glyphYMax
	if bitmapOnly {
		event.NeedsRasterFallback = true
		if glyphs.IsSideways {
			bitmapYMax, bitmapErr := w.bitmapGlyphYMax(ctx, source, glyphs, state.Matrix)
			if bitmapErr != nil {
				if cerr := walkContextError(ctx, bitmapErr); cerr != nil {
					return cerr
				}
				if errors.Is(bitmapErr, ErrLimit) {
					return wrapPartError(state.PagePart, "Glyphs", bitmapErr)
				}
				w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: bitmapErr.Error()})
				return nil
			}
			yMax = bitmapYMax
		}
	}
	run, err := resolveGlyphRunWithStep(glyphs, source.metrics, source.glyphIndex, yMax, count, func() error {
		return checkContext(ctx)
	})
	if err != nil {
		if cerr := walkContextError(ctx, err); cerr != nil {
			return cerr
		}
		if errors.Is(err, ErrLimit) {
			return err
		}
		w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: err.Error()})
		event.NeedsRasterFallback = true
		return nil
	}
	w.remainingGlyphs -= len(run.glyphs)
	positions := make([]GlyphPosition, 0, len(run.glyphs))
	var outlines []*Geometry
	if w.config.resolveGlyphOutlines {
		outlines = make([]*Geometry, len(run.glyphs))
		if bitmapOnly {
			w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: "bitmap-only font has no scalable outline"})
		}
	}
	for i, glyph := range run.glyphs {
		if err := checkContext(ctx); err != nil {
			return err
		}
		shifted := glyph
		if run.bold && w.reader.format == FormatOpenXPS {
			shift := glyphs.FontRenderingEmSize / 100
			shifted.origin.X += shift
			shifted.origin.Y -= shift
			shifted.matrix.E += shift
			shifted.matrix.F -= shift
			if !geometryFinite(shifted.origin.X, shifted.origin.Y, shifted.matrix.E, shifted.matrix.F) {
				return wrapPartError(state.PagePart, "Glyphs", fmt.Errorf("%w: bold glyph transform range", ErrLimit))
			}
		}
		pos, err := contentGlyphPosition(shifted, state.Matrix, run.rtl)
		if err != nil {
			return wrapPartError(state.PagePart, "Glyphs", err)
		}
		positions = append(positions, pos)
		if w.config.resolveGlyphOutlines && !bitmapOnly {
			outline, outlineErr := source.glyphOutline(glyph.gid)
			if outlineErr != nil {
				w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: outlineErr.Error()})
				event.NeedsRasterFallback = true
				continue
			}
			if run.bold && len(outline.Figures) > 0 {
				expanded, boldErr := w.walkBoldOutline(ctx, &outline, run.boldRadius, source.metrics.unitsPerEm)
				if boldErr != nil {
					if cerr := walkContextError(ctx, boldErr); cerr != nil {
						return cerr
					}
					if errors.Is(boldErr, ErrLimit) {
						return wrapPartError(state.PagePart, "Glyphs", boldErr)
					}
					w.reportDiagnostic(Diagnostic{Part: state.PagePart, Element: "Glyphs", Message: boldErr.Error()})
					event.NeedsRasterFallback = true
					continue
				}
				outline = expanded
			}
			transform := pos.Transform
			outline.Transform = &transform
			outlines[i] = &outline
		}
	}
	event.Glyphs = positions
	if w.config.resolveGlyphOutlines {
		event.Outlines = outlines
	}
	return nil
}

// bitmapGlyphYMax 为竖排纯位图字体提供基于EBLC/EBDT位图度量的顶部高度查询回调
// 入参: ctx 取消Context, source 已加载纯位图字体, glyphs 字形元素, transform 当前有效变换
// 返回: func(uint16) (float64, error) 字形顶部高度回调, error 取消、预算或位图索引错误
func (w *sceneWalker) bitmapGlyphYMax(ctx context.Context, source *fontSource, glyphs *Glyphs, transform Matrix) (func(uint16) (float64, error), error) {
	charge := func(amount uint64) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if amount > w.remainingBoldWork {
			return fmt.Errorf("%w: scene walk bitmap work budget", ErrLimit)
		}
		w.remainingBoldWork -= amount
		return nil
	}
	if err := charge(uint64(source.face.tables["EBLC"].length) + uint64(source.face.tables["EBSC"].length) + 1); err != nil {
		return nil, err
	}
	x, y := math.Hypot(transform.A, transform.B), math.Hypot(transform.C, transform.D)
	if glyphs.IsSideways {
		x, y = y, x
	}
	x, y = x*glyphs.FontRenderingEmSize, y*glyphs.FontRenderingEmSize
	px, py := math.Round(x), math.Round(y)
	var strike *fontBitmapStrike
	scaleY := 1.0
	var ppemY uint8
	if geometryFinite(x, y) && px >= 1 && py >= 1 && px <= 255 && py <= 255 && math.Abs(x-px) <= 1e-9 && math.Abs(y-py) <= 1e-9 {
		selection, present, err := source.selectBitmapStrikeWithWork(uint16(px), uint16(py), charge)
		if err != nil {
			return nil, err
		}
		if present {
			strike = &source.bitmaps.strikes[selection.strike]
			scaleY = selection.scaleY
			ppemY = selection.ppemY
		}
	}
	if strike == nil {
		if err := source.loadBitmaps(charge); err != nil {
			return nil, err
		}
		if source.bitmaps == nil || len(source.bitmaps.strikes) == 0 {
			return nil, fmt.Errorf("%w: no matching bitmap strike", ErrUnsupported)
		}
		bestDist := math.Inf(1)
		for i := range source.bitmaps.strikes {
			candidate := &source.bitmaps.strikes[i]
			if candidate.ppemY == 0 {
				continue
			}
			dist := 0.0
			if geometryFinite(x, y) {
				dist = math.Hypot(float64(candidate.ppemX)-x, float64(candidate.ppemY)-y)
			}
			if strike == nil || dist < bestDist {
				strike = candidate
				ppemY = candidate.ppemY
				bestDist = dist
			}
		}
	}
	if strike == nil || ppemY == 0 {
		return nil, fmt.Errorf("%w: no matching bitmap strike", ErrUnsupported)
	}
	return func(gid uint16) (float64, error) {
		if err := checkContext(ctx); err != nil {
			return 0, err
		}
		i := sort.Search(len(strike.entries), func(i int) bool { return strike.entries[i].gid >= gid })
		if i == len(strike.entries) || strike.entries[i].gid != gid {
			return 0, fmt.Errorf("%w: selected bitmap glyph %d is absent", ErrUnsupported, gid)
		}
		entry := strike.entries[i]
		metrics, _, err := strike.imageMetrics(entry, source.bitmaps.data[entry.start:entry.end])
		if err != nil {
			return 0, err
		}
		if metrics.hasVertical {
			return 0, nil
		}
		if !metrics.hasHorizontal {
			return 0, fmt.Errorf("%w: bitmap glyph has no positioning metrics", ErrUnsupported)
		}
		return math.Round(float64(metrics.horizontal.bearingY)*scaleY) * float64(source.metrics.unitsPerEm) / float64(ppemY), nil
	}, nil
}

// loadFont 在单次遍历私有缓存中按需加载字体源，仅在缓存未命中时短暂获取阅读器读锁
// 入参: ctx 取消Context, fontPart 字体部件URI, collectionIndex 字体集合索引
// 返回: *fontSource 只读字体源, error 读取、解析、预算、取消或关闭错误
func (w *sceneWalker) loadFont(ctx context.Context, fontPart string, collectionIndex uint32) (*fontSource, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	part, err := opcPartName(fontPart)
	if err != nil {
		return nil, err
	}
	key := fontCacheKey{part: strings.ToLower(part), index: collectionIndex}
	if source := w.fontFaces[key]; source != nil {
		return source, nil
	}
	if len(w.fontFaces) >= w.maxFonts {
		return nil, fmt.Errorf("%w: font face budget", ErrLimit)
	}
	var face *fontFace
	if data, ok := w.fontData[key.part]; ok {
		face, err = parseFontFace(data, key.index)
	} else {
		limit := min(w.remainingFontBytes, w.config.limits.MaxPartBytes)
		face, err = w.reader.readWalkFontFace(ctx, part, key.index, limit)
		if err == nil {
			w.remainingFontBytes -= int64(len(face.data))
			w.fontData[key.part] = face.data
		}
	}
	if err != nil {
		return nil, err
	}
	source, err := newFontSource(face)
	if err != nil {
		return nil, wrapPartError(part, "", err)
	}
	w.fontFaces[key] = source
	return source, nil
}

// reportDiagnostic 在调用方注册了Diagnostic回调时上报非致命诊断
// 入参: diag 诊断记录
func (w *sceneWalker) reportDiagnostic(diag Diagnostic) {
	if w.visitor.Diagnostic != nil {
		w.visitor.Diagnostic(diag)
	}
}

// clone 返回带独立裁切切片副本的状态快照
// 返回: WalkState 独立状态副本
func (s WalkState) clone() WalkState {
	copyState := s
	copyState.Clip = slices.Clone(s.Clip)
	return copyState
}

// applyElementState 将当前元素的局部变换、裁切、不透明度、蒙版、语言和超链接合并到父状态
// 入参: parent 父级累计状态, props 当前元素局部属性
// 返回: WalkState 当前元素有效状态, error 数值范围或非法属性错误
func applyElementState(parent WalkState, props *ElementProperties) (WalkState, error) {
	if !geometryFinite(props.Opacity) || props.Opacity < 0 || props.Opacity > 1 {
		return WalkState{}, fmt.Errorf("%w: element opacity", ErrInvalid)
	}
	state := parent
	state.Name = props.Name
	state.OpacityMask = props.OpacityMask
	state.Opacity = colorClamp(parent.Opacity * props.Opacity)
	if props.Language != nil {
		state.Language = *props.Language
	}
	if props.NavigateURI != nil {
		state.NavigateURI = *props.NavigateURI
	}
	if props.RenderTransform != nil {
		if !geometryFillMatrixFinite(*props.RenderTransform) {
			return WalkState{}, fmt.Errorf("%w: element transform", ErrInvalid)
		}
		state.Matrix = strokePathCompose(parent.Matrix, *props.RenderTransform)
		if !geometryFillMatrixFinite(state.Matrix) {
			return WalkState{}, fmt.Errorf("%w: element transform range", ErrLimit)
		}
	}
	if props.Clip != nil {
		clips := slices.Clone(parent.Clip)
		clips = append(clips, WalkClip{Geometry: props.Clip, Matrix: state.Matrix})
		state.Clip = clips
	}
	return state, nil
}

// walkPageRootClips 在页面宽高为正时构造初始页面边界裁切栈
// 入参: page 已加载页面, rootTransform 遍历根变换
// 返回: []WalkClip 页面根裁切栈
func walkPageRootClips(page *Page, rootTransform Matrix) []WalkClip {
	if page == nil || !geometryFinite(page.Width, page.Height) || page.Width <= 0 || page.Height <= 0 {
		return nil
	}
	return []WalkClip{{Geometry: renderBoxGeometry(Rect{Width: page.Width, Height: page.Height}), Matrix: rootTransform}}
}

// walkPrintPlacementClips 构造拼版放置生效的纸面留白裁切、放置介质裁切及逻辑页裁切栈
// 入参: sideClip 纸面可打印及留白裁切几何, placement 单个逻辑页放置, rootTransform 纸面根变换, effectiveMatrix 逻辑页累计变换
// 返回: []WalkClip 按生效顺序排列的裁切栈
func walkPrintPlacementClips(sideClip *Geometry, placement PrintPlacement, rootTransform, effectiveMatrix Matrix) []WalkClip {
	clips := make([]WalkClip, 0, 3)
	if sideClip != nil {
		clips = append(clips, WalkClip{Geometry: sideClip, Matrix: rootTransform})
	}
	if placement.MediaClip != (Rect{}) {
		clips = append(clips, WalkClip{Geometry: renderBoxGeometry(placement.MediaClip), Matrix: rootTransform})
	}
	clips = append(clips, WalkClip{Geometry: renderBoxGeometry(placement.PageClip), Matrix: effectiveMatrix})
	return clips
}

// walkContextError 优先返回取消或超时错误，确保Context中止不会被PartError包装
// 入参: ctx 取消Context, err 下层返回的错误
// 返回: error 取消或超时错误，未中止时为nil
func walkContextError(ctx context.Context, err error) error {
	if cerr := checkContext(ctx); cerr != nil {
		return cerr
	}
	if errors.Is(err, context.Canceled) {
		return context.Canceled
	}
	if errors.Is(err, context.DeadlineExceeded) {
		return context.DeadlineExceeded
	}
	return nil
}

// walkBoldOutline 复用渲染器粗体扩张管线在设计单位空间生成加粗矢量轮廓，并累计消耗单次遍历的共享预算
// 入参: ctx 取消Context, outline 原始设计单位轮廓, radius 设计单位扩张半径, unitsPerEm 字体每em单位数
// 返回: Geometry 非零填充加粗轮廓, error 几何、数值、预算或取消错误
func (w *sceneWalker) walkBoldOutline(ctx context.Context, outline *Geometry, radius float64, unitsPerEm uint16) (Geometry, error) {
	options := defaultSceneRenderOptions()
	options.context = ctx
	options.tolerance = max(0.25, float64(unitsPerEm)/256)
	renderer := sceneRenderer{options: options, edges: w.remainingBoldEdges, work: w.remainingBoldWork, exact: w.remainingBoldExact}
	region, err := renderer.bold(outline, radius, IdentityMatrix(), true)
	w.remainingBoldEdges = max(0, renderer.edges)
	w.remainingBoldWork = renderer.work
	w.remainingBoldExact = max(0, renderer.exact)
	if err != nil {
		return Geometry{}, err
	}
	return walkEdgesToGeometry(region.edges), nil
}

// walkEdgesToGeometry 将闭合有向边集还原为非零绕数规则的矢量闭合子路径几何
// 入参: edges 经反向抵消后的闭合有向边切片
// 返回: Geometry 独立矢量几何
func walkEdgesToGeometry(edges []geometryEdge) Geometry {
	result := Geometry{FillRule: GeometryNonZero}
	if len(edges) == 0 {
		return result
	}
	outgoing := make(map[Point][]int, len(edges))
	used := make([]bool, len(edges))
	for i, edge := range edges {
		if edge.start == edge.end {
			used[i] = true
			continue
		}
		outgoing[edge.start] = append(outgoing[edge.start], i)
	}
	for i, edge := range edges {
		if used[i] {
			continue
		}
		used[i] = true
		start := edge.start
		current := edge.end
		segments := []GeometrySegment{{Kind: GeometryLine, Point: current}}
		for current != start {
			list := outgoing[current]
			nextIdx := -1
			for len(list) > 0 {
				candidate := list[0]
				list = list[1:]
				if !used[candidate] {
					nextIdx = candidate
					break
				}
			}
			outgoing[current] = list
			if nextIdx < 0 {
				break
			}
			used[nextIdx] = true
			current = edges[nextIdx].end
			if current != start {
				segments = append(segments, GeometrySegment{Kind: GeometryLine, Point: current})
			}
		}
		if len(segments) >= 2 {
			result.Figures = append(result.Figures, GeometryFigure{
				StartPoint: start,
				IsFilled:   true,
				IsClosed:   true,
				Segments:   segments,
			})
		}
	}
	return result
}

// walkGeometryBounds 计算包含可选Geometry.Transform的路径轴对齐外包矩形
// 入参: g 路径几何，nil返回零矩形
// 返回: Rect 外包矩形, error 几何坐标范围错误
func walkGeometryBounds(g *Geometry) (Rect, error) {
	if g == nil {
		return Rect{}, nil
	}
	bounds, err := g.Bounds()
	if err != nil || g.Transform == nil {
		return bounds, err
	}
	if !geometryFillMatrixFinite(*g.Transform) {
		return Rect{}, fmt.Errorf("%w: non-finite geometry transform", ErrInvalid)
	}
	corners := [4]Point{
		{bounds.X, bounds.Y},
		{bounds.X + bounds.Width, bounds.Y},
		{bounds.X, bounds.Y + bounds.Height},
		{bounds.X + bounds.Width, bounds.Y + bounds.Height},
	}
	first, err := geometryFillPoint(*g.Transform, corners[0])
	if err != nil {
		return Rect{}, err
	}
	minX, minY, maxX, maxY := first.X, first.Y, first.X, first.Y
	for _, corner := range corners[1:] {
		point, err := geometryFillPoint(*g.Transform, corner)
		if err != nil {
			return Rect{}, err
		}
		minX, minY = min(minX, point.X), min(minY, point.Y)
		maxX, maxY = max(maxX, point.X), max(maxY, point.Y)
	}
	width, height := maxX-minX, maxY-minY
	if !geometryFinite(width, height) {
		return Rect{}, fmt.Errorf("%w: transformed geometry bounds overflow", ErrLimit)
	}
	return Rect{X: minX, Y: minY, Width: width, Height: height}, nil
}

// cloneBoolPtr 复制可选布尔指针，避免事件修改影响源元素
// 入参: value 源指针
// 返回: *bool 独立指针副本
func cloneBoolPtr(value *bool) *bool {
	if value == nil {
		return nil
	}
	copied := *value
	return &copied
}

// cloneGlyphClusters 深拷贝字形簇列表及其子字形切片
// 入参: source 源字形簇列表
// 返回: []GlyphCluster 独立副本
func cloneGlyphClusters(source []GlyphCluster) []GlyphCluster {
	if len(source) == 0 {
		return nil
	}
	result := make([]GlyphCluster, len(source))
	for i, cluster := range source {
		cluster.Glyphs = slices.Clone(cluster.Glyphs)
		result[i] = cluster
	}
	return result
}
