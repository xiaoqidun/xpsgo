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
	"fmt"
	"image"
	"image/color"
	"math"
	"math/bits"
	"strings"
	"sync"

	"github.com/xiaoqidun/jxrgo"
)

// imageBrushFilterMaxWork 与同组常量限制图像画刷滤波采样工作量及颜色缓存上限
const (
	imageBrushFilterMaxWork  = 1 << 26
	imageBrushFilterMaxCache = 1 << 20
)

// visualBrushFilterSamples 与同组常量限制视觉画刷平均积分点数及条带均值缓存
const (
	visualBrushFilterSamples = 64
	visualBrushFilterCache   = 8
)

// imageByteToUnit 缓存八位无符号字节到零至一浮点值的查找表
var imageByteToUnit = makeImageByteToUnit()

// imageSampleCache 保存单个工作Goroutine独占的像素中心颜色与JPEG XR滑动行缓存
type imageSampleCache struct {
	sampler *imageSampler
	point   Point
	color   renderColor
	valid   bool
	jxr     jxrRowCache
}

// imageSampler 保存图像画刷的设备逆变换、物理坐标、色彩编码及颜色采样状态
type imageSampler struct {
	image          *rasterImage
	inverse        Matrix
	viewbox        Rect
	viewport       Rect
	tile           TileMode
	opacity        float64
	space          renderColorSpace
	alphaOnly      bool
	filterX        bool
	filterY        bool
	charge         func(uint64) error
	reserve        func(int) error
	release        func(int)
	reserved       int
	filter         *imageBrushFilter
	filterErr      error
	filterWork     uint64
	lastPoint      Point
	lastColor      renderColor
	lastValid      bool
	jxr            jxrRowCache
	jxrMode        jxrSampleMode
	jxrKey         jxrLinearKey
	cicp           *imageCICPTransform
	gammaChroma    *imageGammaChromaTransform
	toneMapPeak    float64
	hdrNominalPeak float64
	cachePool      sync.Pool
	convert        func([iccMaxChannels]float64, float64, bool) (renderColor, error)
	mu             sync.Mutex
}

// imageBrushFilter 保存已转入合成空间的常量或单轴均值，不持有源像素的可变副本
type imageBrushFilter struct {
	values []renderColor
	first  int
}

// imageBrushFilterAxis 保存源像素积分区间或零长度轴的像素中心插值范围
type imageBrushFilterAxis struct {
	first, last        int
	start, end, length float64
	average            bool
}

// visualSampler 保存使用位置独立的视觉场景和图块映射，不修改共享的源元素
type visualSampler struct {
	renderer  *sceneRenderer
	node      *sceneNode
	transform Matrix
	inverse   Matrix
	viewport  Rect
	tile      TileMode
	opacity   float64
}

// visualBrushFilter 在独立参考坐标中平均细小图块，保留未缩小方向的覆盖及设备字体尺寸
type visualBrushFilter struct {
	renderer   *sceneRenderer
	node       *sceneNode
	inverse    Matrix
	viewport   Rect
	width      float64
	height     float64
	filterX    bool
	filterY    bool
	pointX     bool
	pointY     bool
	tile       TileMode
	opacity    float64
	lastPoint  Point
	lastCenter Point
	lastColor  renderColor
	lastValid  bool
	cache      []visualBrushFilterValue
	reserved   int
	next       int
	read       sceneSample
	mu         sync.Mutex
}

// visualBrushFilterValue 保存未平均轴的位置及条带颜色，每项按两个预乘像素计入存活预算
type visualBrushFilterValue struct {
	point  float64
	center float64
	color  renderColor
	valid  bool
}

// makeImageByteToUnit 预计算八位无符号通道经十六位扩展后的归一化浮点查找表
// 返回: [256]float64 逐比特等价于uint16(v)*257/65535的查找表
func makeImageByteToUnit() [256]float64 {
	var table [256]float64
	for i := range table {
		table[i] = float64(uint16(i)*257) / 65535
	}
	return table
}

// newImageSampler 按渲染意图与HDR峰值亮度构建图像画刷采样器，统一处理JXR三模式、PNG CICP、gAMA/cHRM与色调映射
// 入参: brush 图像画刷, source 图像资源, transform 所属元素的设备变换, space 合成空间, alphaOnly 是否仅读取透明度, jxrIntent 显式源渲染意图, hdrPeakNits 可选HDR参考峰值亮度
// 返回: *imageSampler 本次绘制独占的采样器, error 属性、能力或数值错误
func newImageSampler(brush *Brush, source *rasterImage, transform Matrix, space renderColorSpace, alphaOnly bool, jxrIntent RenderingIntent, hdrPeakNits float64) (*imageSampler, error) {
	if brush == nil || brush.Kind != BrushImage || source == nil || source.bounds().Empty() || !geometryFinite(source.dpi.X, source.dpi.Y) || source.dpi.X <= 0 || source.dpi.Y <= 0 {
		return nil, fmt.Errorf("%w: image brush source", ErrInvalid)
	}
	if !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 || brush.TileMode > TileFlipXY || !geometryFillMatrixFinite(transform) {
		return nil, fmt.Errorf("%w: image brush attributes", ErrInvalid)
	}
	if space != renderSRGB && space != renderScRGB {
		return nil, fmt.Errorf("%w: image blend space", ErrUnsupported)
	}
	var cicpTransform *imageCICPTransform
	var gammaChroma *imageGammaChromaTransform
	var jxrMode jxrSampleMode
	var jxrKey jxrLinearKey
	var toneMapPeak float64
	var hdrNominalPeak float64
	channels := imageColorChannels(source)
	if source.jxr == nil && brush.ImageProfileURI == "" && !source.associatedProfile && source.selectedProfile == nil && imageCICPUsable(source.cicp) {
		if source.transform != nil {
			view := *source
			view.transform = nil
			source = &view
		}
		effectivePeak := hdrPeakNits
		if effectivePeak == 0 && source.cicp.transfer == 16 && geometryFinite(source.hdrPeakNits) && source.hdrPeakNits > 0 {
			effectivePeak = source.hdrPeakNits
		}
		var err error
		cicpTransform, err = prepareImageCICP(source.cicp, channels, imageSourceBitDepth(source), effectivePeak)
		if err != nil {
			return nil, err
		}
		if cicpTransform != nil {
			if cicpTransform.hdr {
				toneMapPeak = cicpTransform.peakNits
				if !alphaOnly {
					if cicpTransform.transfer == 16 {
						if hdrPeakNits == 0 && geometryFinite(source.hdrPeakNits) && source.hdrPeakNits > 0 {
							hdrNominalPeak = source.hdrPeakNits
						} else {
							hdrNominalPeak = 10000
						}
					} else {
						hdrNominalPeak = 1000
					}
				}
			} else if hdrPeakNits > 0 && source.linear {
				toneMapPeak = hdrPeakNits
			}
		}
	} else {
		var err error
		source, err = standaloneImageColor(source)
		if err != nil {
			return nil, err
		}
		if source.jxr != nil {
			effectiveProfile := source.selectedProfile
			if source.transform != nil {
				effectiveProfile = source.transform.profile
			}
			isExternal := effectiveProfile != nil && (brush.ImageProfileURI != "" || source.associatedProfile || len(source.jxr.info.ICCProfile) == 0 || !bytes.Equal(effectiveProfile.data, source.jxr.info.ICCProfile))
			if !source.jxr.ycc {
				if effectiveProfile != nil {
					jxrMode = jxrSampleNative
				} else if source.jxr.info.ColorEncoding != nil {
					jxrMode = jxrSampleLinear
					jxrKey = jxrLinearKey{applyCICP: true, intent: jxrIntentFromRender(jxrIntent), hdrPeakNits: hdrPeakNits}
				} else {
					jxrMode = jxrSampleNative
				}
			} else if effectiveProfile != nil && (isExternal || source.selectedProfile != nil || effectiveProfile.class == "nmcl") {
				if effectiveProfile.space == "YCbr" {
					jxrMode = jxrSampleNative
				} else {
					jxrMode = jxrSampleRGB
				}
			} else {
				hasEmbeddedICC := len(source.profile) > 0 && len(source.jxr.info.ICCProfile) > 0
				hasCICP := source.jxr.info.ColorEncoding != nil
				if !hasEmbeddedICC && !hasCICP && source.jxr.info.ColorHint == jxrgo.ColorHintUnspecified {
					jxrMode = jxrSampleRGB
				} else {
					jxrMode = jxrSampleLinear
					intent := jxrIntentFromRender(jxrIntent)
					if jxrIntent == IntentDefault && source.transform != nil {
						intent = jxrIntentFromICC(source.transform.intent)
					}
					jxrKey = jxrLinearKey{
						applyCICP:   hasCICP,
						applyICC:    hasEmbeddedICC,
						intent:      intent,
						hdrPeakNits: hdrPeakNits,
					}
				}
			}
			if jxrMode == jxrSampleLinear && !jxrKey.applyICC && jxrKey.applyCICP && source.cicp != nil && (source.cicp.transfer == 16 || source.cicp.transfer == 18) {
				if hdrPeakNits > 0 {
					toneMapPeak = hdrPeakNits
				} else if source.cicp.transfer == 16 {
					toneMapPeak = 10000
				} else {
					toneMapPeak = 1000
				}
				if !alphaOnly {
					if source.cicp.transfer == 16 {
						hdrNominalPeak = 10000
					} else {
						hdrNominalPeak = 1000
					}
				}
			} else if hdrPeakNits > 0 && source.linear {
				toneMapPeak = hdrPeakNits
			}
		} else {
			if brush.ImageProfileURI == "" && !source.associatedProfile && source.selectedProfile == nil && source.transform == nil && source.gammaChroma != nil {
				gammaChroma = prepareImageGammaChroma(source.gammaChroma, channels)
			}
			if hdrPeakNits > 0 && source.linear {
				toneMapPeak = hdrPeakNits
			}
		}
	}
	if !alphaOnly && source.transform == nil && source.selectedProfile == nil && cicpTransform == nil && (channels == 2 || channels > 4 || channels == 4 && source.multiChannel) {
		return nil, fmt.Errorf("%w: default device image color conversion", ErrUnsupported)
	}
	for _, box := range []Rect{brush.Viewbox, brush.Viewport} {
		if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
			return nil, fmt.Errorf("%w: image brush rectangle", ErrInvalid)
		}
	}
	if brush.Transform != nil {
		if !geometryFillMatrixFinite(*brush.Transform) {
			return nil, fmt.Errorf("%w: image brush transform", ErrInvalid)
		}
		transform = strokePathCompose(transform, *brush.Transform)
	}
	if !geometryFillMatrixFinite(transform) {
		return nil, fmt.Errorf("%w: image brush transform range", ErrLimit)
	}
	collapsed := geometryMatrixSingular(transform)
	if collapsed {
		transform = IdentityMatrix()
	}
	filterX, filterY, err := brushTileFilter(brush.Viewport, transform)
	if err != nil {
		return nil, err
	}
	inverse, err := transform.Inverse()
	if err != nil {
		return nil, err
	}
	sampler := &imageSampler{
		image:          source,
		inverse:        inverse,
		viewbox:        brush.Viewbox,
		viewport:       brush.Viewport,
		tile:           brush.TileMode,
		opacity:        brush.Opacity,
		space:          space,
		alphaOnly:      alphaOnly,
		filterX:        filterX,
		filterY:        filterY,
		jxrMode:        jxrMode,
		jxrKey:         jxrKey,
		cicp:           cicpTransform,
		gammaChroma:    gammaChroma,
		toneMapPeak:    toneMapPeak,
		hdrNominalPeak: hdrNominalPeak,
	}
	if collapsed {
		sampler.filterX, sampler.filterY = true, true
		if sampler.tile == TileNone {
			sampler.viewport = Rect{}
		}
	}
	return sampler, nil
}

// imageSourceBitDepth 返回非JXR图像源编码的单通道位深，浮点图像返回零
// 入参: source 源图像
// 返回: int 编码位深（0、8或16）
func imageSourceBitDepth(source *rasterImage) int {
	if source.native != nil {
		if source.native.floating != nil {
			return 0
		}
		return 16
	}
	switch source.pixels.(type) {
	case *image.NRGBA64, *image.RGBA64, *image.Gray16:
		return 16
	default:
		return 8
	}
}

// coordinate 将设备位置映射到源图像像素坐标，平铺位置直接计算以避免累计取整误差
// 入参: point 设备位置, clip 是否裁去单图块外部
// 返回: Point 源像素坐标, bool 是否位于图块内, error 坐标范围错误
func (s *imageSampler) coordinate(point Point, clip bool) (Point, bool, error) {
	if !geometryFinite(point.X, point.Y) {
		return Point{}, false, fmt.Errorf("%w: image device coordinates", ErrLimit)
	}
	p := s.inverse.Transform(point)
	u, visible, err := imageTileCoordinate(p.X, s.viewport.X, s.viewport.Width, s.filterX, clip, s.tile, s.tile == TileFlipX || s.tile == TileFlipXY)
	if err != nil || !visible {
		return Point{}, false, err
	}
	v, visible, err := imageTileCoordinate(p.Y, s.viewport.Y, s.viewport.Height, s.filterY, clip, s.tile, s.tile == TileFlipY || s.tile == TileFlipXY)
	if err != nil || !visible {
		return Point{}, false, err
	}
	p = Point{(s.viewbox.X + u*s.viewbox.Width) * (s.image.dpi.X / 96), (s.viewbox.Y + v*s.viewbox.Height) * (s.image.dpi.Y / 96)}
	if !geometryFinite(p.X, p.Y) {
		return Point{}, false, fmt.Errorf("%w: image source coordinates", ErrLimit)
	}
	return p, true, nil
}

// imageTileFraction 计算任意正负图块位置的局部比例，翻转周期为两个图块
// 入参: value 图块坐标, flip 是否交替镜像
// 返回: float64 局部比例
func imageTileFraction(value float64, flip bool) float64 {
	if !flip {
		return value - math.Floor(value)
	}
	value = math.Mod(value, 2)
	if value < 0 {
		value += 2
	}
	if value > 1 {
		value = 2 - value
	}
	return value
}

// sampleAt 分别判断当前覆盖位置和指定像素中心的颜色，供嵌套视觉图块保持设备采样相位
// 入参: point 当前设备位置, center 映射后的原设备像素中心
// 返回: renderColor 预乘颜色, error 采样或数值错误
func (s *imageSampler) sampleAt(point, center Point) (renderColor, error) {
	return s.sampleAtWith(point, center, &s.lastPoint, &s.lastColor, &s.lastValid, &s.jxr, false)
}

// sampleAtCached 使用工作Goroutine独占缓存执行并发安全采样，常规未平均路径零锁运行
// 入参: point 当前设备位置, center 映射后的原设备像素中心, cache 独占单点及行缓存, concurrent 是否处于多核并发阶段
// 返回: renderColor 预乘颜色, error 采样或数值错误
func (s *imageSampler) sampleAtCached(point, center Point, cache *imageSampleCache, concurrent bool) (renderColor, error) {
	if cache == nil {
		if concurrent {
			return s.sampleAtPooled(point, center)
		}
		return s.sampleAt(point, center)
	}
	if cache.sampler != s {
		cache.valid = false
		cache.sampler = s
	}
	return s.sampleAtWith(point, center, &cache.point, &cache.color, &cache.valid, &cache.jxr, concurrent)
}

// sampleAtPooled 在并发闭包未透传工作缓存时从采样器对象池复用单点及JPEG XR行缓存
// 入参: point 当前设备位置, center 映射后的原设备像素中心
// 返回: renderColor 预乘颜色, error 采样或数值错误
func (s *imageSampler) sampleAtPooled(point, center Point) (renderColor, error) {
	var cache *imageSampleCache
	if pooled, ok := s.cachePool.Get().(*imageSampleCache); ok && pooled != nil {
		cache = pooled
	} else {
		cache = &imageSampleCache{}
	}
	c, err := s.sampleAtCached(point, center, cache, true)
	s.cachePool.Put(cache)
	return c, err
}

// sampleAtWith 执行图像画刷覆盖判断、单点缓存查找及透明度调制
// 入参: point 当前设备位置, center 映射后的原设备像素中心, lastPoint 缓存坐标指针, lastColor 缓存颜色指针, lastValid 缓存有效标志指针, jxr 可选JPEG XR行缓存, concurrent 是否处于多核并发阶段
// 返回: renderColor 预乘颜色, error 采样或数值错误
func (s *imageSampler) sampleAtWith(point, center Point, lastPoint *Point, lastColor *renderColor, lastValid *bool, jxr *jxrRowCache, concurrent bool) (renderColor, error) {
	if !geometryFinite(point.X, point.Y, center.X, center.Y) {
		return renderColor{}, fmt.Errorf("%w: image device coordinates", ErrLimit)
	}
	filtered := s.filterX || s.filterY
	if filtered && concurrent {
		s.mu.Lock()
		defer s.mu.Unlock()
	}
	if filtered {
		if err := s.imageFilterCharge(1); err != nil {
			return renderColor{}, err
		}
	}
	p, visible, err := s.coordinate(point, true)
	if err != nil || !visible {
		return renderColor{}, err
	}
	bounds := s.image.bounds()
	if !s.filterX && (p.X < 0 || p.X >= float64(bounds.Dx())) || !s.filterY && (p.Y < 0 || p.Y >= float64(bounds.Dy())) {
		return renderColor{}, nil
	}
	p, _, err = s.coordinate(center, false)
	if err != nil {
		return renderColor{}, err
	}
	c := *lastColor
	if !*lastValid || p != *lastPoint {
		if filtered {
			c, err = s.filteredColor(p)
		} else {
			c, err = s.bilinearWithCache(p, jxr)
		}
		if err != nil {
			return renderColor{}, err
		}
		*lastPoint, *lastColor, *lastValid = p, c, true
	}
	if s.space == renderSRGB && s.opacity == 1 && (c.a > 0 || c == (renderColor{})) {
		return c, nil
	}
	return renderColorModulate(c, s.opacity, 1)
}

// bilinearWithCache 对源像素中心作预乘双线性插值，JPEG XR源可复用工作Goroutine滑动行缓存
// 入参: point 已换算物理分辨率的源像素坐标, jxrCache 可选JPEG XR两行滑动缓存
// 返回: renderColor 插值颜色, error 颜色转换错误
func (s *imageSampler) bilinearWithCache(point Point, jxrCache *jxrRowCache) (renderColor, error) {
	bounds := s.image.bounds()
	dx, dy := bounds.Dx(), bounds.Dy()
	x := max(0, min(float64(dx-1), point.X-0.5))
	y := max(0, min(float64(dy-1), point.Y-0.5))
	x0, y0 := int(math.Floor(x)), int(math.Floor(y))
	tx, ty := x-float64(x0), y-float64(y0)
	if tx == 0 && ty == 0 {
		c, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y0, jxrCache)
		if err != nil {
			return renderColor{}, err
		}
		c.a = colorClamp(c.a)
		return c, nil
	}
	x1, y1 := min(x0+1, dx-1), min(y0+1, dy-1)
	if ty == 0 {
		c0, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y0, jxrCache)
		if err != nil {
			return renderColor{}, err
		}
		c1, err := s.pixelColorWithCache(bounds.Min.X+x1, bounds.Min.Y+y0, jxrCache)
		if err != nil {
			return renderColor{}, err
		}
		w0 := 1 - tx
		return renderColor{c0.r*w0 + c1.r*tx, c0.g*w0 + c1.g*tx, c0.b*w0 + c1.b*tx, colorClamp(c0.a*w0 + c1.a*tx)}, nil
	}
	if tx == 0 {
		c0, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y0, jxrCache)
		if err != nil {
			return renderColor{}, err
		}
		c1, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y1, jxrCache)
		if err != nil {
			return renderColor{}, err
		}
		w0 := 1 - ty
		return renderColor{c0.r*w0 + c1.r*ty, c0.g*w0 + c1.g*ty, c0.b*w0 + c1.b*ty, colorClamp(c0.a*w0 + c1.a*ty)}, nil
	}
	wx0, wx1 := 1-tx, tx
	wy0, wy1 := 1-ty, ty
	c00, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y0, jxrCache)
	if err != nil {
		return renderColor{}, err
	}
	c10, err := s.pixelColorWithCache(bounds.Min.X+x1, bounds.Min.Y+y0, jxrCache)
	if err != nil {
		return renderColor{}, err
	}
	c01, err := s.pixelColorWithCache(bounds.Min.X+x0, bounds.Min.Y+y1, jxrCache)
	if err != nil {
		return renderColor{}, err
	}
	c11, err := s.pixelColorWithCache(bounds.Min.X+x1, bounds.Min.Y+y1, jxrCache)
	if err != nil {
		return renderColor{}, err
	}
	w00, w10, w01, w11 := wx0*wy0, wx1*wy0, wx0*wy1, wx1*wy1
	var result renderColor
	result.r = ((c00.r*w00 + c10.r*w10) + c01.r*w01) + c11.r*w11
	result.g = ((c00.g*w00 + c10.g*w10) + c01.g*w01) + c11.g*w11
	result.b = ((c00.b*w00 + c10.b*w10) + c01.b*w01) + c11.b*w11
	result.a = colorClamp(((c00.a*w00 + c10.a*w10) + c01.a*w01) + c11.a*w11)
	return result, nil
}

// sampleSourceComponents 读取源像素原生分量并完成JXR、CICP、PNG gAMA/cHRM及无ICC sYCC前置预处理
// 入参: x 源横坐标, y 源纵坐标, jxrCache 可选JPEG XR滑动行缓存
// 返回: [iccMaxChannels]float64 分量数组, float64 有限透明度, int 有效通道数, bool 分量是否已线性化为scRGB, bool 是否已由JXR线性读取器完成色彩转换, error 读取或非有限错误
func (s *imageSampler) sampleSourceComponents(x, y int, jxrCache *jxrRowCache) ([iccMaxChannels]float64, float64, int, bool, bool, error) {
	var components [iccMaxChannels]float64
	alpha, channels, jxrLinear, colorLinear := 1.0, imageColorChannels(s.image), false, false
	if source := s.image.jxr; source != nil {
		var err error
		if jxrCache != nil {
			alpha, err = jxrCache.sample(source, x, y, components[:], s.jxrMode, s.jxrKey)
		} else {
			switch s.jxrMode {
			case jxrSampleLinear:
				alpha, err = source.sampleLinear(x, y, components[:], s.jxrKey)
			case jxrSampleRGB:
				alpha, err = source.sampleRGB(x, y, components[:])
			default:
				alpha, err = source.sample(x, y, components[:])
			}
		}
		if err != nil {
			return components, 0, 0, false, false, err
		}
		if s.jxrMode == jxrSampleLinear {
			jxrLinear = true
			channels = 3
		} else if s.jxrMode == jxrSampleRGB {
			channels = 3
		}
	} else if source := s.image.native; source != nil {
		if source.channels < 1 || source.channels > len(components) {
			return components, 0, 0, false, false, fmt.Errorf("%w: image source channels", ErrUnsupported)
		}
		stride := source.channels
		if source.alpha {
			stride++
		}
		at := ((y-source.bounds.Min.Y)*source.bounds.Dx() + x - source.bounds.Min.X) * stride
		if source.floating != nil {
			copy(components[:], source.floating[at:at+source.channels])
			if source.alpha {
				alpha = source.floating[at+source.channels]
			}
		} else {
			for axis := range source.channels {
				components[axis] = float64(source.values[at+axis]) / 65535
			}
			if source.alpha {
				alpha = float64(source.values[at+source.channels]) / 65535
			}
		}
	} else if source, ok := s.image.pixels.(*image.CMYK); ok {
		value := source.CMYKAt(x, y)
		components[0], components[1], components[2], components[3] = float64(value.C)/255, float64(value.M)/255, float64(value.Y)/255, float64(value.K)/255
	} else {
		value := imagePixel(s.image.pixels, x, y)
		components[0], components[1], components[2] = float64(value.R)/65535, float64(value.G)/65535, float64(value.B)/65535
		alpha = float64(value.A) / 65535
	}
	if !geometryFinite(alpha) {
		return components, 0, 0, false, false, fmt.Errorf("%w: non-finite raster alpha interpretation", ErrUnsupported)
	}
	if alpha == 0 {
		return components, 0, channels, false, jxrLinear, nil
	}
	if s.alphaOnly && s.convert == nil {
		return components, colorClamp(alpha), channels, false, jxrLinear, nil
	}
	if s.image.native != nil && s.image.native.floating != nil || s.image.jxr != nil && s.image.linear {
		for i := range channels {
			if !geometryFinite(components[i]) {
				return components, 0, 0, false, false, fmt.Errorf("%w: non-finite raster color interpretation", ErrUnsupported)
			}
		}
	}
	if !jxrLinear && s.image.transform == nil && s.image.selectedProfile == nil {
		if s.cicp != nil {
			rgb := s.cicp.toLinearSRGB(components[0], components[1], components[2], channels == 1)
			components[0], components[1], components[2] = rgb[0], rgb[1], rgb[2]
			colorLinear = true
			channels = 3
		} else if s.gammaChroma != nil {
			rgb := s.gammaChroma.toLinearSRGB(components[0], components[1], components[2], channels == 1)
			components[0], components[1], components[2] = rgb[0], rgb[1], rgb[2]
			colorLinear = true
			channels = 3
		} else if s.image.jxr != nil && s.jxrMode == jxrSampleRGB {
			components[0] = renderSignedSRGBToLinear(components[0])
			components[1] = renderSignedSRGBToLinear(components[1])
			components[2] = renderSignedSRGBToLinear(components[2])
			colorLinear = true
			channels = 3
		}
	}
	if channels == 1 && s.image.transform == nil && s.image.selectedProfile == nil {
		components[1], components[2] = components[0], components[0]
	}
	return components, alpha, channels, s.image.linear || jxrLinear || colorLinear, jxrLinear, nil
}

// pixelColorWithCache 在原生通道上执行颜色转换并预乘透明度，支持JPEG XR滑动行缓存、CICP、gAMA/cHRM与常见格式零分配快路径
// 入参: x 源横坐标, y 源纵坐标, jxrCache 可选JPEG XR滑动行缓存
// 返回: renderColor 合成空间颜色, error 颜色或通道错误
func (s *imageSampler) pixelColorWithCache(x, y int, jxrCache *jxrRowCache) (renderColor, error) {
	if s.image.jxr == nil && s.image.native == nil && s.image.transform == nil && s.convert == nil && s.cicp == nil && s.gammaChroma == nil && s.toneMapPeak == 0 && !s.image.linear && s.image.channels != 1 && (s.space == renderSRGB || s.space == renderScRGB) {
		if nrgba, ok := s.image.pixels.(*image.NRGBA); ok {
			if !image.Pt(x, y).In(nrgba.Rect) {
				return renderColor{}, nil
			}
			i := nrgba.PixOffset(x, y)
			a := nrgba.Pix[i+3]
			if a == 0 {
				return renderColor{}, nil
			}
			r, g, b, av := imageByteToUnit[nrgba.Pix[i]], imageByteToUnit[nrgba.Pix[i+1]], imageByteToUnit[nrgba.Pix[i+2]], imageByteToUnit[a]
			if s.space == renderScRGB {
				r = renderSRGBToLinear(r)
				g = renderSRGBToLinear(g)
				b = renderSRGBToLinear(b)
			}
			return renderColor{r * av, g * av, b * av, av}, nil
		}
	}
	components, alpha, channels, linear, jxrLinear, err := s.sampleSourceComponents(x, y, jxrCache)
	if err != nil {
		return renderColor{}, err
	}
	if alpha == 0 {
		return renderColor{}, nil
	}
	if s.alphaOnly && s.convert == nil {
		return renderColor{a: alpha}, nil
	}
	if s.image.transform != nil && !jxrLinear {
		if channels < 1 || channels > len(components) {
			return renderColor{}, fmt.Errorf("%w: image source channels", ErrUnsupported)
		}
		if s.convert != nil {
			return s.convert(components, alpha, s.image.linear)
		}
		if !imageProfileCompatible(s.image, s.image.transform) {
			return renderColor{}, fmt.Errorf("%w: image profile channels", ErrInvalid)
		}
		input := components[:s.image.transform.inputChannels()]
		if s.image.transform.pipeline != nil && !s.image.transform.pipeline.floating && imageRejectClampedLUT(s.image, input) {
			return renderColor{}, fmt.Errorf("%w: extended-range image requires floating-point ICC DToB or matrix-TRC transform", ErrUnsupported)
		}
		rgb, err := s.image.transform.linearRGB(input, imageUseExtendedTRC(s.image, s.jxrMode))
		if err != nil {
			return renderColor{}, err
		}
		return imageRGBToRenderColor(rgb[0], rgb[1], rgb[2], alpha, ColorScRGB, s.space, s.toneMapPeak)
	}
	if s.convert != nil {
		if channels < 1 || channels > len(components) {
			return renderColor{}, fmt.Errorf("%w: image source channels", ErrUnsupported)
		}
		return s.convert(components, alpha, linear)
	}
	if channels == 4 && !s.image.multiChannel {
		c, m, yv, k := colorClamp(components[0]), colorClamp(components[1]), colorClamp(components[2]), colorClamp(components[3])
		components[0], components[1], components[2] = (1-c)*(1-k), (1-m)*(1-k), (1-yv)*(1-k)
	} else if channels != 1 && channels != 3 {
		return renderColor{}, fmt.Errorf("%w: default device image color conversion", ErrUnsupported)
	}
	space := ColorSRGB
	if linear {
		space = ColorScRGB
	}
	return imageRGBToRenderColor(components[0], components[1], components[2], alpha, space, s.space, s.toneMapPeak)
}

// jxrHasExtendedFormat 判断JPEG XR图像是否包含定点、浮点或RGBE等扩展范围颜色通道
// 入参: source JPEG XR图像视图
// 返回: bool 是否含非无符号扩展范围颜色通道
func jxrHasExtendedFormat(source *jxrImage) bool {
	if source == nil {
		return false
	}
	for i := range source.channels {
		if source.components[i].Info().Format != jxrgo.SampleUnsigned {
			return true
		}
	}
	return false
}

// imageUseExtendedTRC 判断当前图像采样送入ICC矩阵或灰阶TRC时是否启用无裁剪扩展外推
// 入参: source 图像资源, mode JPEG XR采样模式
// 返回: bool 是否启用TRC扩展范围外推
func imageUseExtendedTRC(source *rasterImage, mode jxrSampleMode) bool {
	if source.linear || source.native != nil && source.native.floating != nil {
		return true
	}
	return source.jxr != nil && (mode == jxrSampleRGB || jxrHasExtendedFormat(source.jxr))
}

// imageRejectClampedLUT 判断扩展范围样本送入非浮点整数ICC查找表时是否应拒绝静默裁剪
// 入参: source 图像资源, input 送入ICC转换的源分量切片
// 返回: bool 是否需要浮点DToB或矩阵TRC避免整数LUT静默截断
func imageRejectClampedLUT(source *rasterImage, input []float64) bool {
	hasExtendedType := source.native != nil && source.native.floating != nil || jxrHasExtendedFormat(source.jxr)
	if source.linear {
		if hasExtendedType {
			return true
		}
		for _, value := range input {
			if value < 0 || value > 1 {
				return true
			}
		}
		return false
	}
	if !hasExtendedType {
		return false
	}
	for _, value := range input {
		if value < 0 || value > 1 {
			return true
		}
	}
	return false
}

// imageRGBToRenderColor 将非预乘RGB分量转换至目标合成空间，并在HDR输出至sRGB时执行BT.2446方法A色调映射
// 入参: r, g, b 源RGB分量, alpha 透明度, srcSpace 源颜色空间, target 目标合成空间, toneMapPeak HDR峰值亮度，零值不启用色调映射
// 返回: renderColor 预乘颜色, error 非法数值或颜色空间错误
func imageRGBToRenderColor(r, g, b, alpha float64, srcSpace ColorSpace, target renderColorSpace, toneMapPeak float64) (renderColor, error) {
	if target != renderSRGB && target != renderScRGB {
		return renderColor{}, fmt.Errorf("%w: compositor color space", ErrUnsupported)
	}
	if !geometryFinite(alpha, r, g, b) {
		return renderColor{}, fmt.Errorf("%w: non-finite color component", ErrInvalid)
	}
	if srcSpace == ColorSRGB {
		if r < 0 || r > 1 || g < 0 || g > 1 || b < 0 || b > 1 {
			return renderColor{}, fmt.Errorf("%w: sRGB component outside unit range", ErrInvalid)
		}
		if target == renderScRGB {
			r = renderSRGBToLinear(r)
			g = renderSRGBToLinear(g)
			b = renderSRGBToLinear(b)
		}
	} else if target == renderSRGB {
		if toneMapPeak > 0 {
			mapped := renderBT2446MethodA([3]float64{r, g, b}, toneMapPeak)
			r, g, b = mapped[0], mapped[1], mapped[2]
		}
		r = renderLinearToSRGB(colorClamp(r))
		g = renderLinearToSRGB(colorClamp(g))
		b = renderLinearToSRGB(colorClamp(b))
	}
	a := colorClamp(alpha)
	if a == 0 {
		return renderColor{}, nil
	}
	return renderColor{r * a, g * a, b * a, a}, nil
}

// imagePixel 读取非预乘16位颜色，索引色板与常见非预乘格式直接读取源条目避免预乘往返失真
// 入参: source 源图像, x 横坐标, y 纵坐标
// 返回: color.NRGBA64 非预乘颜色
func imagePixel(source image.Image, x, y int) color.NRGBA64 {
	switch value := source.(type) {
	case *image.NRGBA:
		c := value.NRGBAAt(x, y)
		return color.NRGBA64{uint16(c.R) * 257, uint16(c.G) * 257, uint16(c.B) * 257, uint16(c.A) * 257}
	case *image.NRGBA64:
		return value.NRGBA64At(x, y)
	case *image.Paletted:
		if !image.Pt(x, y).In(value.Rect) || len(value.Palette) == 0 {
			return color.NRGBA64{}
		}
		index := int(value.ColorIndexAt(x, y))
		if index >= len(value.Palette) {
			return color.NRGBA64{}
		}
		return imageStraightColor(value.Palette[index])
	case *image.RGBA:
		c := value.RGBA64At(x, y)
		return imageStraightPixel(c)
	case *image.RGBA64:
		return imageStraightPixel(value.RGBA64At(x, y))
	case *image.Gray:
		gray := uint16(value.GrayAt(x, y).Y) * 257
		return color.NRGBA64{gray, gray, gray, 65535}
	case *image.Gray16:
		gray := value.Gray16At(x, y).Y
		return color.NRGBA64{gray, gray, gray, 65535}
	case *image.YCbCr:
		c := value.YCbCrAt(x, y)
		r, g, b, a := c.RGBA()
		return color.NRGBA64{uint16(r), uint16(g), uint16(b), uint16(a)}
	case *image.NYCbCrA:
		c := value.NYCbCrAAt(x, y)
		r, g, b, _ := c.YCbCr.RGBA()
		return color.NRGBA64{uint16(r), uint16(g), uint16(b), uint16(c.A) * 257}
	default:
		return imageStraightColor(source.At(x, y))
	}
}

// imageStraightColor 直接保留非预乘颜色值，避免调色板等非预乘条目经RGBA预乘量化失真
// 入参: value 源颜色Interface值
// 返回: color.NRGBA64 非预乘16位颜色
func imageStraightColor(value color.Color) color.NRGBA64 {
	if value == nil {
		return color.NRGBA64{}
	}
	switch c := value.(type) {
	case color.NRGBA:
		return color.NRGBA64{uint16(c.R) * 257, uint16(c.G) * 257, uint16(c.B) * 257, uint16(c.A) * 257}
	case color.NRGBA64:
		return c
	case color.RGBA:
		return imageStraightPixel(color.RGBA64{uint16(c.R) * 257, uint16(c.G) * 257, uint16(c.B) * 257, uint16(c.A) * 257})
	case color.RGBA64:
		return imageStraightPixel(c)
	case color.Gray:
		gray := uint16(c.Y) * 257
		return color.NRGBA64{gray, gray, gray, 65535}
	case color.Gray16:
		return color.NRGBA64{c.Y, c.Y, c.Y, 65535}
	default:
		r, g, b, a := value.RGBA()
		return imageStraightPixel(color.RGBA64{uint16(r), uint16(g), uint16(b), uint16(a)})
	}
}

// imageStraightPixel 将标准图像的预乘16位像素还原为非预乘值
// 入参: value 预乘颜色
// 返回: color.NRGBA64 非预乘颜色
func imageStraightPixel(value color.RGBA64) color.NRGBA64 {
	if value.A == 0 {
		return color.NRGBA64{}
	}
	a := uint32(value.A)
	return color.NRGBA64{uint16(uint32(value.R) * 65535 / a), uint16(uint32(value.G) * 65535 / a), uint16(uint32(value.B) * 65535 / a), value.A}
}

// imageTileCoordinate 计算单轴图块相位，已平均轴不再计算重复图块的相位
// 入参: value 画刷位置, origin 图块起点, size 图块长度, filtered 是否平均, clip 是否裁剪, tile 平铺方式, flip 是否镜像
// 返回: float64 局部比例, bool 是否可见, error 未平均轴的数值或相位错误
func imageTileCoordinate(value, origin, size float64, filtered, clip bool, tile TileMode, flip bool) (float64, bool, error) {
	if filtered {
		if tile == TileNone && (size == 0 || clip && (value < origin || value >= origin+size)) {
			return 0, false, nil
		}
		return 0, true, nil
	}
	u := (value - origin) / size
	if !geometryFinite(u) {
		return 0, false, fmt.Errorf("%w: image tile coordinates", ErrLimit)
	}
	if tile == TileNone {
		if clip && (u < 0 || u >= 1) {
			return 0, false, nil
		}
		return colorClamp(u), true, nil
	}
	if math.Abs(u) >= 1<<52 {
		return 0, false, fmt.Errorf("%w: image tile phase precision", ErrLimit)
	}
	return imageTileFraction(u, flip), true, nil
}

// imageFilterCharge 在分配及积分前扣除共享工作量，并限制独立采样器的累计工作量
// 入参: amount 本次工作量，零值仅检查取消状态
// 返回: error 共享预算、取消或内部工作上限错误
func (s *imageSampler) imageFilterCharge(amount uint64) error {
	if amount > imageBrushFilterMaxWork-s.filterWork {
		return fmt.Errorf("%w: image brush filter work", ErrLimit)
	}
	if s.charge != nil {
		if err := s.charge(amount); err != nil {
			return err
		}
	}
	s.filterWork += amount
	return nil
}

// newImageBrushFilterAxis 将物理viewbox换算为源像素范围，超出源图像的部分仍保留在平均分母内
// 入参: origin 物理起点, size 物理长度, scale 每物理单位的像素数, count 源轴像素数, average 是否积分
// 返回: imageBrushFilterAxis 半开像素范围, error 源坐标溢出错误
func newImageBrushFilterAxis(origin, size, scale float64, count int, average bool) (imageBrushFilterAxis, error) {
	if count <= 0 || uint64(count) > 1<<52 {
		return imageBrushFilterAxis{}, fmt.Errorf("%w: image brush filter source precision", ErrLimit)
	}
	start, length := origin*scale, size*scale
	end := start + length
	if !geometryFinite(start, length, end) {
		return imageBrushFilterAxis{}, fmt.Errorf("%w: image brush filter source range", ErrLimit)
	}
	a := imageBrushFilterAxis{start: start, end: end, length: length, average: average}
	if average && length > 0 {
		left, right := max(0, start), min(float64(count), end)
		if left < right {
			a.first, a.last = int(math.Floor(left)), int(math.Ceil(right))
		} else if start == end && start >= 0 && start < float64(count) {
			a.first = int(math.Floor(start))
			a.last = a.first + 1
		}
	} else {
		if length == 0 && (start < 0 || start >= float64(count)) || end < 0 || start >= float64(count) {
			return a, nil
		}
		a.first = int(math.Floor(max(0, min(float64(count-1), start-0.5))))
		a.last = min(count, int(math.Floor(max(0, min(float64(count-1), end-0.5))))+2)
	}
	return a, nil
}

// weight 返回实际源像素覆盖权重，零viewbox轴沿像素中心作线性点采样
// 入参: index 源轴像素索引
// 返回: float64 包含透明越界分母的归一化权重
func (a imageBrushFilterAxis) weight(index int) float64 {
	if !a.average {
		return 1
	}
	if a.length > 0 {
		if a.start >= float64(index) && a.start < float64(index+1) {
			return min(a.length, float64(index+1)-a.start) / a.length
		}
		return max(0, min(float64(index+1), a.end)-max(float64(index), a.start)) / a.length
	}
	t := min(float64(a.last-1), max(0, a.start-0.5)) - float64(a.first)
	if index == a.first {
		return 1 - min(1, t)
	}
	return min(1, t)
}

// prepareImageFilter 延迟构建小图块面积加权均值缓存，零尺寸视口轴保留点或线采样
// 返回: error 颜色、数值、资源或取消错误
func (s *imageSampler) prepareImageFilter() error {
	if s.filter != nil || s.filterErr != nil {
		return s.filterErr
	}
	value, err := s.buildImageFilter()
	if err != nil {
		s.filterErr = err
		return err
	}
	s.filter = value
	return nil
}

// buildImageFilter 在完整预算通过后积分源像素，单轴仅缓存未平均方向的行或列
// 返回: *imageBrushFilter 完整私有缓存, error 转换、预算或取消错误
func (s *imageSampler) buildImageFilter() (*imageBrushFilter, error) {
	bounds := s.image.bounds()
	x, err := newImageBrushFilterAxis(s.viewbox.X, s.viewbox.Width, s.image.dpi.X/96, bounds.Dx(), s.filterX)
	if err != nil {
		return nil, err
	}
	y, err := newImageBrushFilterAxis(s.viewbox.Y, s.viewbox.Height, s.image.dpi.Y/96, bounds.Dy(), s.filterY)
	if err != nil {
		return nil, err
	}
	nx, ny := uint64(x.last-x.first), uint64(y.last-y.first)
	first, count := 0, 1
	if !s.filterX {
		first, count = x.first, int(nx)
	} else if !s.filterY {
		first, count = y.first, int(ny)
	}
	if nx == 0 || ny == 0 {
		first, count = 0, 1
	}
	if count > imageBrushFilterMaxCache || ny != 0 && nx > imageBrushFilterMaxWork/ny {
		return nil, fmt.Errorf("%w: image brush filter cache", ErrLimit)
	}
	if err := s.imageFilterCharge(nx*ny + uint64(count)*4); err != nil {
		return nil, err
	}
	committed := false
	if s.reserve != nil {
		if err := s.reserve(count); err != nil {
			return nil, err
		}
		s.reserved += count
		defer func() {
			if !committed && s.release != nil && count > 0 {
				s.reserved -= count
				s.release(count)
			}
		}()
	}
	values := make([]renderColor, count)
	if nx == 0 || ny == 0 {
		committed = true
		return &imageBrushFilter{values: values}, nil
	}
	var rows jxrRowCache
	var visited uint64
	for py := y.first; py < y.last; py++ {
		wy := y.weight(py)
		for px := x.first; px < x.last; px++ {
			if visited%256 == 0 {
				if err := s.imageFilterCharge(0); err != nil {
					return nil, err
				}
			}
			visited++
			weight := x.weight(px) * wy
			if weight == 0 {
				continue
			}
			c, err := s.pixelColorWithCache(bounds.Min.X+px, bounds.Min.Y+py, &rows)
			if err != nil {
				return nil, err
			}
			index := 0
			if !s.filterX {
				index = px - first
			} else if !s.filterY {
				index = py - first
			}
			v := &values[index]
			v.r += c.r * weight
			v.g += c.g * weight
			v.b += c.b * weight
			v.a += c.a * weight
		}
	}
	if err := s.imageFilterCharge(0); err != nil {
		return nil, err
	}
	committed = true
	return &imageBrushFilter{values: values, first: first}, nil
}

// releaseFilter 释放图像画刷过滤与行缓存并归还存活像素预算
func (s *imageSampler) releaseFilter() {
	s.filter = nil
	s.jxr.source = nil
	s.jxr.valid = [2]bool{}
	if s.reserved != 0 && s.release != nil {
		count := s.reserved
		s.reserved = 0
		s.release(count)
	}
}

// filteredColor 读取缓存均值，未平均轴保持原设备像素中心的线性插值
// 入参: point 像素中心对应的源像素位置
// 返回: renderColor 预乘颜色, error 缓存生成错误
func (s *imageSampler) filteredColor(point Point) (renderColor, error) {
	if err := s.prepareImageFilter(); err != nil {
		return renderColor{}, err
	}
	f := s.filter
	if len(f.values) == 0 {
		return renderColor{}, nil
	}
	if s.filterX && s.filterY {
		c := f.values[0]
		c.a = colorClamp(c.a)
		return c, nil
	}
	position, count := point.X, s.image.bounds().Dx()
	if s.filterX {
		position, count = point.Y, s.image.bounds().Dy()
	}
	p := max(0, min(float64(count-1), position-0.5))
	index := int(math.Floor(p))
	t := p - float64(index)
	i, j := max(0, min(len(f.values)-1, index-f.first)), max(0, min(len(f.values)-1, index+1-f.first))
	a, b := f.values[i], f.values[j]
	return renderColor{a.r*(1-t) + b.r*t, a.g*(1-t) + b.g*t, a.b*(1-t) + b.b*t, colorClamp(a.a*(1-t) + b.a*t)}, nil
}

// scenePixelCenter 取得全局设备像素中心，负坐标采用相同的半开像素区间
// 入参: point 当前设备位置
// 返回: Point 所属像素中心
func scenePixelCenter(point Point) Point {
	return Point{math.Floor(point.X) + 0.5, math.Floor(point.Y) + 0.5}
}

// visualBrush 在使用位置准备视觉内容并向子树透传透明度掩模状态，图块映射先于视觉自身的变换
// 入参: brush 视觉画刷, transform 所属元素的设备变换, aliased 继承的边缘模式, depth 当前元素深度, maskOnly 是否仅用作透明度掩模
// 返回: sceneSample 视觉采样器, error 结构、数值或资源错误
func (r *sceneRenderer) visualBrush(brush *Brush, transform Matrix, aliased bool, depth int, maskOnly bool) (sceneSample, error) {
	previousMask := r.maskOnly
	r.maskOnly = previousMask || maskOnly
	defer func() { r.maskOnly = previousMask }()
	if brush.Visual == nil || brush.TileMode > TileFlipXY {
		return nil, fmt.Errorf("%w: visual brush source or attributes", ErrInvalid)
	}
	for _, box := range []Rect{brush.Viewbox, brush.Viewport} {
		if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
			return nil, fmt.Errorf("%w: visual brush rectangle", ErrInvalid)
		}
	}
	if brush.Transform != nil {
		if !geometryFillMatrixFinite(*brush.Transform) {
			return nil, fmt.Errorf("%w: visual brush transform", ErrInvalid)
		}
		transform = strokePathCompose(transform, *brush.Transform)
	}
	if !geometryFillMatrixFinite(transform) {
		return nil, fmt.Errorf("%w: visual brush transform range", ErrLimit)
	}
	if geometryMatrixSingular(transform) {
		if brush.TileMode == TileNone {
			return func(Point, Point) (renderColor, error) { return renderColor{}, nil }, nil
		}
		return r.filteredVisualBrush(brush, transform, aliased, depth, true, true)
	}
	filterX, filterY, err := brushTileFilter(brush.Viewport, transform)
	if err != nil {
		return nil, err
	}
	filterX = filterX || brush.Viewbox.Width == 0
	filterY = filterY || brush.Viewbox.Height == 0
	if filterX || filterY {
		return r.filteredVisualBrush(brush, transform, aliased, depth, filterX, filterY)
	}
	inverse, err := transform.Inverse()
	if err != nil {
		return nil, err
	}
	limit := float64((1 << 30) / r.options.samples)
	for _, corner := range []Point{{brush.Viewport.X, brush.Viewport.Y}, {brush.Viewport.X + brush.Viewport.Width, brush.Viewport.Y}, {brush.Viewport.X, brush.Viewport.Y + brush.Viewport.Height}, {brush.Viewport.X + brush.Viewport.Width, brush.Viewport.Y + brush.Viewport.Height}} {
		point := transform.Transform(corner)
		if !geometryFinite(point.X, point.Y) || math.Abs(point.X) > limit || math.Abs(point.Y) > limit {
			return nil, fmt.Errorf("%w: visual base tile coordinates", ErrLimit)
		}
	}
	sx, sy := brush.Viewport.Width/brush.Viewbox.Width, brush.Viewport.Height/brush.Viewbox.Height
	if sx == 0 || sy == 0 {
		return nil, fmt.Errorf("%w: visual tile scale underflow", ErrLimit)
	}
	mapping := Matrix{A: sx, D: sy, E: brush.Viewport.X - brush.Viewbox.X*sx, F: brush.Viewport.Y - brush.Viewbox.Y*sy}
	effective := strokePathCompose(transform, mapping)
	if !geometryFillMatrixFinite(effective) {
		return nil, fmt.Errorf("%w: visual tile mapping range", ErrLimit)
	}
	if geometryMatrixSingular(effective) {
		return nil, fmt.Errorf("%w: visual tile mapping precision", ErrLimit)
	}
	nodes, err := r.prepare([]Element{brush.Visual}, effective, aliased, depth+1)
	if err != nil {
		return nil, err
	}
	s := &visualSampler{renderer: r, node: nodes[0], transform: transform, inverse: inverse, viewport: brush.Viewport, tile: brush.TileMode, opacity: brush.Opacity}
	if r.printRuntime != nil {
		r.nativeSample = func(point, center Point) (printNativeColor, error) {
			p, c, visible, err := s.coordinate(point, center)
			if err != nil || !visible {
				return printNativeColor{}, err
			}
			value, err := r.samplePrintColorNode(s.node, p, c)
			value.alpha *= s.opacity
			return value, err
		}
	}
	r.brushMeta.sampleCached = s.sampleCached
	return s.sample, nil
}

// sample 按当前图块映射视觉和像素中心，内部合成完成后只施加一次画刷透明度
// 入参: point 当前覆盖位置, center 原设备像素中心
// 返回: renderColor 隔离合成后的预乘颜色, error 采样或资源错误
func (s *visualSampler) sample(point, center Point) (renderColor, error) {
	return s.sampleCached(point, center, nil)
}

// sampleCached 使用调用方提供的图像采样缓存映射并合成视觉图块
// 入参: point 当前覆盖位置, center 原设备像素中心, cache 可选工作Goroutine图像缓存
// 返回: renderColor 隔离合成后的预乘颜色, error 采样或资源错误
func (s *visualSampler) sampleCached(point, center Point, cache *imageSampleCache) (renderColor, error) {
	p, c, visible, err := s.coordinate(point, center)
	if err != nil || !visible {
		return renderColor{}, err
	}
	color, err := s.renderer.sampleNode(s.node, p, c, cache)
	if err != nil {
		return renderColor{}, err
	}
	return renderColorModulate(color, s.opacity, 1)
}

// coordinate 将位置和像素中心映射到同一个基准图块，翻转在画刷变换之前进行
// 入参: point 当前覆盖位置, center 原设备像素中心
// 返回: Point 基准图块位置, Point 同图块像素中心, bool 是否可见, error 数值错误
func (s *visualSampler) coordinate(point, center Point) (Point, Point, bool, error) {
	p, c := s.inverse.Transform(point), s.inverse.Transform(center)
	u, v := (p.X-s.viewport.X)/s.viewport.Width, (p.Y-s.viewport.Y)/s.viewport.Height
	x, y := (c.X-s.viewport.X)/s.viewport.Width, (c.Y-s.viewport.Y)/s.viewport.Height
	if !geometryFinite(u, v, x, y) {
		return Point{}, Point{}, false, fmt.Errorf("%w: visual tile coordinates", ErrLimit)
	}
	if s.tile == TileNone {
		if u < 0 || u >= 1 || v < 0 || v >= 1 {
			return Point{}, Point{}, false, nil
		}
	} else {
		if math.Abs(u) >= 1<<52 || math.Abs(v) >= 1<<52 {
			return Point{}, Point{}, false, fmt.Errorf("%w: visual tile phase precision", ErrLimit)
		}
		column, row := math.Floor(u), math.Floor(v)
		u, v, x, y = u-column, v-row, x-column, y-row
		if (s.tile == TileFlipX || s.tile == TileFlipXY) && math.Mod(column, 2) != 0 {
			u, x = 1-u, 1-x
		}
		if (s.tile == TileFlipY || s.tile == TileFlipXY) && math.Mod(row, 2) != 0 {
			v, y = 1-v, 1-y
		}
	}
	p = s.transform.Transform(Point{s.viewport.X + u*s.viewport.Width, s.viewport.Y + v*s.viewport.Height})
	c = s.transform.Transform(Point{s.viewport.X + x*s.viewport.Width, s.viewport.Y + y*s.viewport.Height})
	if !geometryFinite(p.X, p.Y, c.X, c.Y) {
		return Point{}, Point{}, false, fmt.Errorf("%w: visual tile mapped coordinates", ErrLimit)
	}
	return p, c, true, nil
}

// sampleNode 在单个位置完成视觉节点的内部合成，再应用节点裁剪、掩模及透明度
// 入参: node 已准备节点, point 基准图块位置, center 映射后的设备像素中心, cache 可选工作Goroutine图像缓存
// 返回: renderColor 节点隔离颜色, error 带部件位置的绘制错误
func (r *sceneRenderer) sampleNode(node *sceneNode, point, center Point, cache *imageSampleCache) (result renderColor, err error) {
	defer func() {
		if err != nil {
			err = wrapPartError(node.part, node.kind, err)
		}
	}()
	if err = r.charge(1); err != nil {
		return renderColor{}, err
	}
	if node.opacity == 0 {
		return renderColor{}, nil
	}
	if point.X < float64(node.bounds.Min.X) && center.X < float64(node.bounds.Min.X) || point.X >= float64(node.bounds.Max.X) && center.X >= float64(node.bounds.Max.X) || point.Y < float64(node.bounds.Min.Y) && center.Y < float64(node.bounds.Min.Y) || point.Y >= float64(node.bounds.Max.Y) && center.Y >= float64(node.bounds.Max.Y) {
		return renderColor{}, nil
	}
	if node.clip != nil {
		inside, e := r.regionContains(*node.clip, point, center, node.aliased)
		if e != nil {
			return renderColor{}, e
		}
		if !inside {
			return renderColor{}, nil
		}
	}
	for _, paint := range node.paints {
		inside := false
		for _, region := range paint.regions {
			inside, err = r.regionContains(region, point, center, paint.aliased)
			if err != nil {
				return renderColor{}, err
			}
			if inside {
				break
			}
		}
		if !inside {
			continue
		}
		var color renderColor
		var e error
		switch {
		case paint.image != nil && cache != nil:
			color, e = paint.image.sampleAtCached(point, center, cache, r.concurrent)
		case paint.sampleCached != nil && cache != nil:
			color, e = paint.sampleCached(point, center, cache)
		default:
			color, e = paint.sample(point, center)
		}
		if e != nil {
			return renderColor{}, e
		}
		result, err = renderSourceOver(color, result)
		if err != nil {
			return renderColor{}, err
		}
	}
	for _, child := range node.children {
		color, e := r.sampleNode(child, point, center, cache)
		if e != nil {
			return renderColor{}, e
		}
		result, err = renderSourceOver(color, result)
		if err != nil {
			return renderColor{}, err
		}
	}
	alpha := 1.0
	if node.mask != nil {
		var color renderColor
		var e error
		switch {
		case node.maskImage != nil && cache != nil:
			color, e = node.maskImage.sampleAtCached(point, center, cache, r.concurrent)
		case node.maskCached != nil && cache != nil:
			color, e = node.maskCached(point, center, cache)
		default:
			color, e = node.mask(point, center)
		}
		if e != nil {
			return renderColor{}, e
		}
		alpha = color.a
	}
	return renderColorModulate(result, node.opacity, alpha)
}

// regionContains 按栅格化器相同的半开边界规则检查区域，并累计精确计算及扫描预算
// 入参: region 独立填充区域, point 当前位置, center 设备像素中心, aliased 是否采用像素中心
// 返回: bool 是否命中区域, error 精确计算或资源错误
func (r *sceneRenderer) regionContains(region rasterRegion, point, center Point, aliased bool) (bool, error) {
	if err := r.charge(1 + uint64(len(region.edges))); err != nil {
		return false, err
	}
	if aliased {
		point = center
	} else {
		scale := float64(r.options.samples)
		point = Point{point.X * scale, point.Y * scale}
	}
	if !geometryFinite(point.X, point.Y) {
		return false, fmt.Errorf("%w: visual sample coordinates", ErrLimit)
	}
	winding := 0
	var localExact int
	var exactPtr *int
	if r.concurrent {
		r.budgetMu.Lock()
		localExact = r.exact
		r.budgetMu.Unlock()
		exactPtr = &localExact
	} else {
		exactPtr = &r.exact
	}
	startExact := *exactPtr
	for _, edge := range region.edges {
		a, b, direction := edge.start, edge.end, 1
		if a.Y == b.Y {
			continue
		}
		if a.Y > b.Y {
			a, b, direction = b, a, -1
		}
		if point.Y < a.Y || point.Y >= b.Y {
			continue
		}
		right, err := rasterAtOrRight(a, b, point, exactPtr)
		if err != nil {
			if r.concurrent && startExact > localExact {
				r.budgetMu.Lock()
				r.exact = max(0, r.exact-(startExact-localExact))
				r.budgetMu.Unlock()
			}
			return false, err
		}
		if !right {
			continue
		}
		if region.rule == GeometryEvenOdd {
			winding ^= 1
		} else {
			winding += direction
		}
	}
	if r.concurrent && startExact > localExact {
		used := startExact - localExact
		r.budgetMu.Lock()
		if used > r.exact {
			r.exact = 0
			r.budgetMu.Unlock()
			return false, fmt.Errorf("%w: raster exact arithmetic work", ErrLimit)
		}
		r.exact -= used
		r.budgetMu.Unlock()
	}
	return winding != 0, nil
}

// filteredVisualBrush 构建微小图块视觉画刷的参考场景采样器，在固定参考坐标中计算均值
// 入参: brush 视觉画刷, transform 设备变换, aliased 继承边缘模式, depth 元素深度, filterX 横轴平均, filterY 纵轴平均
// 返回: sceneSample 预乘颜色采样器, error 结构、资源或数值错误
func (r *sceneRenderer) filteredVisualBrush(brush *Brush, transform Matrix, aliased bool, depth int, filterX, filterY bool) (sceneSample, error) {
	collapsed := geometryMatrixSingular(transform)
	inverse := IdentityMatrix()
	var err error
	if !collapsed {
		inverse, err = transform.Inverse()
		if err != nil {
			return nil, err
		}
	}
	w, h := float64(visualBrushFilterSamples), float64(visualBrushFilterSamples)
	if !collapsed {
		w = math.Max(w, math.Hypot(transform.A, transform.B)*brush.Viewport.Width)
		h = math.Max(h, math.Hypot(transform.C, transform.D)*brush.Viewport.Height)
	}
	width, height := brush.Viewbox.Width, brush.Viewbox.Height
	if width == 0 {
		width = 1
	}
	if height == 0 {
		height = 1
	}
	sx, sy := w/width, h/height
	reference := Matrix{A: sx, D: sy, E: -brush.Viewbox.X * sx, F: -brush.Viewbox.Y * sy}
	if !geometryFillMatrixFinite(reference) || geometryMatrixSingular(reference) {
		return nil, fmt.Errorf("%w: visual filter reference transform", ErrLimit)
	}
	back := Matrix{A: brush.Viewport.Width / w, D: brush.Viewport.Height / h, E: brush.Viewport.X, F: brush.Viewport.Y}
	if brush.Viewbox.Width == 0 {
		back.A = 1 / w
	}
	if brush.Viewbox.Height == 0 {
		back.D = 1 / h
	}
	density := strokePathCompose(transform, back)
	if collapsed {
		density, err = reference.Inverse()
		if err != nil {
			return nil, err
		}
	}
	previous := r.options.bitmapDensity
	if previous != nil {
		density = strokePathCompose(*previous, density)
	}
	r.options.bitmapDensity = &density
	nodes, err := r.prepare([]Element{brush.Visual}, reference, aliased, depth+1)
	r.options.bitmapDensity = previous
	if err != nil {
		return nil, err
	}
	s := &visualBrushFilter{renderer: r, node: nodes[0], inverse: inverse, viewport: brush.Viewport, width: w, height: h, filterX: filterX, filterY: filterY, pointX: brush.Viewbox.Width == 0, pointY: brush.Viewbox.Height == 0, tile: brush.TileMode, opacity: brush.Opacity}
	if r.printRuntime != nil {
		r.nativeSample = r.printRuntime.filteredVisual(s)
	}
	r.brushMeta.sampleCached = s.sampleCached
	return s.sample, nil
}

// visualFilterAxis 仅在未平均方向计算平铺相位，单图块的覆盖范围保持不变
// 入参: point 覆盖坐标, center 像素中心, start 图块起点, extent 图块长度, filtered 是否平均, tile 平铺模式, flip 是否翻转
// 返回: float64 局部覆盖坐标, float64 局部像素中心, bool 是否可见, error 数值错误
func visualFilterAxis(point, center, start, extent float64, filtered bool, tile TileMode, flip bool) (float64, float64, bool, error) {
	if filtered && tile != TileNone {
		return 0.5, 0.5, true, nil
	}
	if !geometryFinite(point, center) {
		return 0, 0, false, fmt.Errorf("%w: visual filter coordinates", ErrLimit)
	}
	if tile == TileNone && (extent == 0 || point < start || point >= start+extent) {
		return 0, 0, false, nil
	}
	if filtered {
		return 0.5, 0.5, true, nil
	}
	u, c := (point-start)/extent, (center-start)/extent
	if !geometryFinite(u, c) {
		return 0, 0, false, fmt.Errorf("%w: visual filter phase", ErrLimit)
	}
	if tile != TileNone {
		if math.Abs(u) >= 1<<52 {
			return 0, 0, false, fmt.Errorf("%w: visual filter phase precision", ErrLimit)
		}
		index := math.Floor(u)
		u, c = u-index, c-index
		if flip && math.Mod(index, 2) != 0 {
			u, c = 1-u, 1-c
		}
	}
	return u, c, true, nil
}

// visualFilterPosition 在各分层内交错布置积分点，降低规则细纹与固定采样网格的相位混叠
// 入参: index 分层序号, extent 参考轴长度
// 返回: float64 当前积分坐标
func visualFilterPosition(index int, extent float64) float64 {
	offset := float64(bits.Reverse64(uint64(index))>>58) + 0.5
	return (float64(index) + offset/visualBrushFilterSamples) * (extent / visualBrushFilterSamples)
}

// sample 对缩小方向作有界分层积分，在预乘合成后施加一次画刷透明度
// 入参: point 当前覆盖位置, center 设备像素中心
// 返回: renderColor 平均预乘颜色, error 绘制、预算或取消错误
func (s *visualBrushFilter) sample(point, center Point) (renderColor, error) {
	return s.sampleCached(point, center, nil)
}

// sampleCached 使用调用方图像采样缓存对缩小方向作有界分层积分
// 入参: point 当前覆盖位置, center 设备像素中心, cache 可选工作Goroutine图像缓存
// 返回: renderColor 平均预乘颜色, error 绘制、预算或取消错误
func (s *visualBrushFilter) sampleCached(point, center Point, cache *imageSampleCache) (renderColor, error) {
	if s.renderer.concurrent {
		s.mu.Lock()
		defer s.mu.Unlock()
	}
	if err := s.renderer.charge(0); err != nil {
		return renderColor{}, err
	}
	if !geometryFinite(point.X, point.Y, center.X, center.Y) {
		return renderColor{}, fmt.Errorf("%w: visual filter device coordinates", ErrLimit)
	}
	p, c := s.inverse.Transform(point), s.inverse.Transform(center)
	u, x, visible, err := visualFilterAxis(p.X, c.X, s.viewport.X, s.viewport.Width, s.filterX, s.tile, s.tile == TileFlipX || s.tile == TileFlipXY)
	if err != nil || !visible {
		return renderColor{}, err
	}
	v, y, visible, err := visualFilterAxis(p.Y, c.Y, s.viewport.Y, s.viewport.Height, s.filterY, s.tile, s.tile == TileFlipY || s.tile == TileFlipXY)
	if err != nil || !visible {
		return renderColor{}, err
	}
	p, c = Point{u * s.width, v * s.height}, Point{x * s.width, y * s.height}
	if s.pointX {
		p.X, c.X = 0, 0
	}
	if s.pointY {
		p.Y, c.Y = 0, 0
	}
	if !geometryFinite(p.X, p.Y, c.X, c.Y) {
		return renderColor{}, fmt.Errorf("%w: visual filter mapped coordinates", ErrLimit)
	}
	if s.lastValid && p == s.lastPoint && c == s.lastCenter {
		return s.lastColor, nil
	}
	position, midpoint := p.Y, c.Y
	if !s.filterX {
		position, midpoint = p.X, c.X
	}
	if s.filterX != s.filterY {
		if err := s.renderer.charge(1); err != nil {
			return renderColor{}, err
		}
		if s.cache == nil {
			if err := s.renderer.reservePixels(visualBrushFilterCache * 2); err != nil {
				return renderColor{}, err
			}
			s.reserved += visualBrushFilterCache * 2
			s.renderer.registerCleanup(s.releaseFilter)
			s.cache = make([]visualBrushFilterValue, visualBrushFilterCache)
		}
		for _, value := range s.cache {
			if value.valid && value.point == position && value.center == midpoint {
				s.lastPoint, s.lastCenter, s.lastColor, s.lastValid = p, c, value.color, true
				return value.color, nil
			}
		}
	}
	nx, ny := 1, 1
	if s.filterX && !s.pointX {
		nx = visualBrushFilterSamples
	}
	if s.filterY && !s.pointY {
		ny = visualBrushFilterSamples
	}
	if err := s.renderer.charge(uint64(nx * ny)); err != nil {
		return renderColor{}, err
	}
	var result renderColor
	weight := 1 / float64(nx*ny)
	for j := range ny {
		for i := range nx {
			q, d := p, c
			if s.filterX && !s.pointX {
				q.X = visualFilterPosition(i, s.width)
				d.X = q.X
			}
			if s.filterY && !s.pointY {
				q.Y = visualFilterPosition(j, s.height)
				d.Y = q.Y
			}
			var color renderColor
			var err error
			if s.read != nil {
				color, err = s.read(q, d)
			} else {
				color, err = s.renderer.sampleNode(s.node, q, d, cache)
			}
			if err != nil {
				return renderColor{}, err
			}
			result.r += color.r * weight
			result.g += color.g * weight
			result.b += color.b * weight
			result.a += color.a * weight
		}
	}
	if err := s.renderer.charge(0); err != nil {
		return renderColor{}, err
	}
	result, err = renderColorModulate(result, s.opacity, 1)
	if err != nil {
		return renderColor{}, err
	}
	s.lastPoint, s.lastCenter, s.lastColor, s.lastValid = p, c, result, true
	if s.cache != nil {
		s.cache[s.next] = visualBrushFilterValue{point: position, center: midpoint, color: result, valid: true}
		s.next = (s.next + 1) % len(s.cache)
	}
	return result, nil
}

// releaseFilter 释放视觉画刷条带均值缓存并归还存活像素预算
func (s *visualBrushFilter) releaseFilter() {
	s.cache = nil
	if s.reserved != 0 {
		count := s.reserved
		s.reserved = 0
		s.renderer.releaseLive(count)
	}
}

// RenderBrushTile 隔离光栅化VisualBrush、ImageBrush或渐变画刷的单个Viewport瓦片到透明背景画布
// 综合options.DPI（默认96）、options.Transform与平铺画刷Transform的两轴线性尺度确定像素分辨率，渐变画刷保留Transform
// 入参: ctx 取消Context，nil采用Background, brush 待光栅化画刷, options 绘制参数，nil采用96DPI透明默认配置
// 返回: *image.NRGBA 透明背景单瓦片图像, Rect 瓦片物理范围矩形, error 参数、画刷、资源、预算或取消错误
func (r *Reader) RenderBrushTile(ctx context.Context, brush *Brush, options *RenderOptions) (*image.NRGBA, Rect, error) {
	return r.RenderBrushTileWithState(ctx, brush, "", WalkState{Opacity: 1, Matrix: IdentityMatrix()}, options)
}

// RenderBrushTileWithState 在指定图形与打印色彩状态下隔离光栅化单个画刷瓦片到透明背景画布
// 综合options.DPI、options.Transform、state.Matrix与平铺画刷Transform两轴线性尺度计算像素尺寸，并透传PrintColor、PrintColorPlan与Negative
// 入参: ctx 取消Context，nil采用Background, brush 待光栅化画刷, basePart 相对资源解析基准部件，空值回退brush.Part与state.PagePart, state 图形与打印色彩状态, options 绘制参数，nil采用96DPI透明默认配置
// 返回: *image.NRGBA 透明背景单瓦片图像, Rect 瓦片物理范围矩形, error 参数、画刷、资源、预算或取消错误
func (r *Reader) RenderBrushTileWithState(ctx context.Context, brush *Brush, basePart string, state WalkState, options *RenderOptions) (*image.NRGBA, Rect, error) {
	ctx = normalizeContext(ctx)
	if err := checkContext(ctx); err != nil {
		return nil, Rect{}, err
	}
	if err := r.readLock(); err != nil {
		return nil, Rect{}, err
	}
	defer r.mu.RUnlock()
	if brush == nil || !geometryFinite(brush.Opacity) || brush.Opacity < 0 || brush.Opacity > 1 {
		return nil, Rect{}, fmt.Errorf("%w: brush tile source", ErrInvalid)
	}
	if state.EdgeMode != "" && state.EdgeMode != EdgeModeAliased {
		return nil, Rect{}, fmt.Errorf("%w: brush tile edge mode", ErrInvalid)
	}
	if err := validatePrintColor(state.PrintColor); err != nil {
		return nil, Rect{}, err
	}
	effectivePart := brush.Part
	if effectivePart == "" {
		effectivePart = basePart
	}
	if effectivePart == "" {
		effectivePart = state.PagePart
	}
	if effectivePart != "" {
		var err error
		effectivePart, err = opcPartName(effectivePart)
		if err != nil {
			return nil, Rect{}, err
		}
	}
	configuration := RenderOptions{}
	if options != nil {
		configuration = *options
	}
	configuration.Background = color.Transparent
	settings, _, err := configuration.settings(ctx)
	if err != nil {
		return nil, Rect{}, err
	}
	settings.outputColor = state.PrintColor.Mode
	viewport, err := brushTileViewport(brush)
	if err != nil {
		return nil, Rect{}, err
	}
	scaleMatrix := IdentityMatrix()
	if configuration.Transform != nil {
		if geometryMatrixSingular(*configuration.Transform) {
			return nil, Rect{}, fmt.Errorf("%w: singular brush tile render transform", ErrInvalid)
		}
		scaleMatrix = strokePathCompose(scaleMatrix, *configuration.Transform)
	}
	if state.Matrix != (Matrix{}) {
		if !geometryFillMatrixFinite(state.Matrix) {
			return nil, Rect{}, fmt.Errorf("%w: brush tile state matrix", ErrInvalid)
		}
		scaleMatrix = strokePathCompose(scaleMatrix, state.Matrix)
	}
	isTileBrush := brush.Kind == BrushVisual || brush.Kind == BrushImage
	if isTileBrush && brush.Transform != nil {
		scaleMatrix = strokePathCompose(scaleMatrix, *brush.Transform)
	}
	if !geometryFillMatrixFinite(scaleMatrix) {
		return nil, Rect{}, fmt.Errorf("%w: brush tile scale range", ErrLimit)
	}
	axisX := math.Hypot(scaleMatrix.A, scaleMatrix.B)
	axisY := math.Hypot(scaleMatrix.C, scaleMatrix.D)
	if !geometryFinite(axisX, axisY) {
		return nil, Rect{}, fmt.Errorf("%w: brush tile scale range", ErrLimit)
	}
	if viewport.Width == 0 || viewport.Height == 0 || brush.Opacity == 0 || axisX == 0 || axisY == 0 || geometryMatrixSingular(scaleMatrix) {
		return image.NewNRGBA(image.Rectangle{}), viewport, nil
	}
	dpi := configuration.DPI
	if dpi == 0 {
		dpi = 96
	}
	scale := dpi / 96
	rawW, rawH := viewport.Width*scale*axisX, viewport.Height*scale*axisY
	if !geometryFinite(rawW, rawH) || rawW > float64(rasterMaxDimension) || rawH > float64(rasterMaxDimension) {
		return nil, Rect{}, fmt.Errorf("%w: brush tile pixel dimensions", ErrLimit)
	}
	pixelW := max(1, int(math.Ceil(rawW)))
	pixelH := max(1, int(math.Ceil(rawH)))
	sx := float64(pixelW) / viewport.Width
	sy := float64(pixelH) / viewport.Height
	tileTransform := Matrix{A: sx, D: sy, E: -viewport.X * sx, F: -viewport.Y * sy}
	if !geometryFillMatrixFinite(tileTransform) || geometryMatrixSingular(tileTransform) {
		return nil, Rect{}, fmt.Errorf("%w: brush tile mapping range", ErrLimit)
	}
	tileBrush := *brush
	if tileBrush.Part == "" {
		tileBrush.Part = effectivePart
	}
	if isTileBrush {
		tileBrush.Transform = nil
		tileBrush.TileMode = TileNone
	}
	var root Element = &Path{
		ElementProperties: ElementProperties{Part: effectivePart, Opacity: 1},
		Data:              renderBoxGeometry(viewport),
		Fill:              &tileBrush,
	}
	if state.EdgeMode == EdgeModeAliased {
		root = &Canvas{ElementProperties: ElementProperties{Part: effectivePart, Opacity: 1}, EdgeMode: EdgeModeAliased, Elements: []Element{root}}
	}
	if state.Negative {
		negCanvas := &Canvas{ElementProperties: ElementProperties{Part: effectivePart, Opacity: 1}, Elements: []Element{root}}
		settings.negative = map[*Canvas]bool{negCanvas: true}
		root = negCanvas
	}
	var output *image.NRGBA
	bounds := image.Rect(0, 0, pixelW, pixelH)
	if state.PrintColorPlan != nil {
		planCanvas := &Canvas{ElementProperties: ElementProperties{Part: effectivePart, Opacity: 1}, Elements: []Element{root}}
		if err := attachPrintColorPlanPreview(ctx, &settings, configuration, planCanvas, state.PrintColorPlan); err != nil {
			return nil, Rect{}, err
		}
		output, err = r.renderLoadedElementsPrintPreview([]Element{planCanvas}, tileTransform, bounds, settings)
	} else {
		output, err = r.renderLoadedElements([]Element{root}, tileTransform, bounds, settings)
	}
	if err != nil {
		return nil, Rect{}, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, Rect{}, err
	}
	return output, viewport, nil
}

// brushTileViewport 校验画刷属性并确定单瓦片物理范围，渐变画刷在缺省Viewport时结合Transform计算精确采样域
// 入参: brush 源画刷
// 返回: Rect 物理采样范围矩形, error 画刷参数或不支持种类错误
func brushTileViewport(brush *Brush) (Rect, error) {
	switch brush.Kind {
	case BrushVisual:
		if brush.Visual == nil || brush.TileMode > TileFlipXY {
			return Rect{}, fmt.Errorf("%w: visual brush tile source", ErrInvalid)
		}
		if brush.Transform != nil && !geometryFillMatrixFinite(*brush.Transform) {
			return Rect{}, fmt.Errorf("%w: visual brush tile transform", ErrInvalid)
		}
		for _, box := range []Rect{brush.Viewbox, brush.Viewport} {
			if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
				return Rect{}, fmt.Errorf("%w: visual brush tile rectangle", ErrInvalid)
			}
		}
		return brush.Viewport, nil
	case BrushImage:
		if brush.ImageSource == "" || brush.TileMode > TileFlipXY {
			return Rect{}, fmt.Errorf("%w: image brush tile source", ErrInvalid)
		}
		if brush.Transform != nil && !geometryFillMatrixFinite(*brush.Transform) {
			return Rect{}, fmt.Errorf("%w: image brush tile transform", ErrInvalid)
		}
		for _, box := range []Rect{brush.Viewbox, brush.Viewport} {
			if !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) || box.Width < 0 || box.Height < 0 {
				return Rect{}, fmt.Errorf("%w: image brush tile rectangle", ErrInvalid)
			}
		}
		return brush.Viewport, nil
	case BrushLinearGradient:
		if err := validateBrushTileGradient(brush); err != nil {
			return Rect{}, err
		}
		if !geometryFinite(brush.StartPoint.X, brush.StartPoint.Y, brush.EndPoint.X, brush.EndPoint.Y) {
			return Rect{}, fmt.Errorf("%w: linear gradient brush points", ErrInvalid)
		}
		if brush.Transform != nil && !geometryFillMatrixFinite(*brush.Transform) {
			return Rect{}, fmt.Errorf("%w: linear gradient brush transform", ErrInvalid)
		}
		if brush.Viewport != (Rect{}) {
			if !geometryFinite(brush.Viewport.X, brush.Viewport.Y, brush.Viewport.Width, brush.Viewport.Height, brush.Viewport.X+brush.Viewport.Width, brush.Viewport.Y+brush.Viewport.Height) || brush.Viewport.Width < 0 || brush.Viewport.Height < 0 {
				return Rect{}, fmt.Errorf("%w: gradient brush viewport", ErrInvalid)
			}
			return brush.Viewport, nil
		}
		start, end := brush.StartPoint, brush.EndPoint
		if brush.Transform != nil {
			var err error
			start, err = geometryFillPoint(*brush.Transform, start)
			if err != nil {
				return Rect{}, err
			}
			end, err = geometryFillPoint(*brush.Transform, end)
			if err != nil {
				return Rect{}, err
			}
		}
		minX, maxX := min(start.X, end.X), max(start.X, end.X)
		minY, maxY := min(start.Y, end.Y), max(start.Y, end.Y)
		w, h := maxX-minX, maxY-minY
		if !geometryFinite(w, h) {
			return Rect{}, fmt.Errorf("%w: linear gradient viewport range", ErrLimit)
		}
		if w == 0 {
			w = 1
		}
		if h == 0 {
			h = 1
		}
		return Rect{X: minX, Y: minY, Width: w, Height: h}, nil
	case BrushRadialGradient:
		if err := validateBrushTileGradient(brush); err != nil {
			return Rect{}, err
		}
		if !geometryFinite(brush.Center.X, brush.Center.Y, brush.GradientOrigin.X, brush.GradientOrigin.Y, brush.RadiusX, brush.RadiusY) || brush.RadiusX < 0 || brush.RadiusY < 0 {
			return Rect{}, fmt.Errorf("%w: radial gradient brush geometry", ErrInvalid)
		}
		if brush.Transform != nil && !geometryFillMatrixFinite(*brush.Transform) {
			return Rect{}, fmt.Errorf("%w: radial gradient brush transform", ErrInvalid)
		}
		if brush.Viewport != (Rect{}) {
			if !geometryFinite(brush.Viewport.X, brush.Viewport.Y, brush.Viewport.Width, brush.Viewport.Height, brush.Viewport.X+brush.Viewport.Width, brush.Viewport.Y+brush.Viewport.Height) || brush.Viewport.Width < 0 || brush.Viewport.Height < 0 {
				return Rect{}, fmt.Errorf("%w: gradient brush viewport", ErrInvalid)
			}
			return brush.Viewport, nil
		}
		center, origin := brush.Center, brush.GradientOrigin
		rx, ry := brush.RadiusX, brush.RadiusY
		if brush.Transform != nil {
			m := *brush.Transform
			var err error
			center, err = geometryFillPoint(m, center)
			if err != nil {
				return Rect{}, err
			}
			origin, err = geometryFillPoint(m, origin)
			if err != nil {
				return Rect{}, err
			}
			rx = math.Hypot(m.A*brush.RadiusX, m.C*brush.RadiusY)
			ry = math.Hypot(m.B*brush.RadiusX, m.D*brush.RadiusY)
			if !geometryFinite(rx, ry) {
				return Rect{}, fmt.Errorf("%w: radial gradient viewport range", ErrLimit)
			}
		}
		minX := min(center.X-rx, origin.X)
		maxX := max(center.X+rx, origin.X)
		minY := min(center.Y-ry, origin.Y)
		maxY := max(center.Y+ry, origin.Y)
		w, h := maxX-minX, maxY-minY
		if !geometryFinite(w, h) {
			return Rect{}, fmt.Errorf("%w: radial gradient viewport range", ErrLimit)
		}
		if w == 0 {
			w = 1
		}
		if h == 0 {
			h = 1
		}
		return Rect{X: minX, Y: minY, Width: w, Height: h}, nil
	case BrushSolidColor:
		if err := validateBrushTileColor(brush.Color); err != nil {
			return Rect{}, err
		}
		if brush.Viewport != (Rect{}) {
			if !geometryFinite(brush.Viewport.X, brush.Viewport.Y, brush.Viewport.Width, brush.Viewport.Height, brush.Viewport.X+brush.Viewport.Width, brush.Viewport.Y+brush.Viewport.Height) || brush.Viewport.Width < 0 || brush.Viewport.Height < 0 {
				return Rect{}, fmt.Errorf("%w: solid brush viewport", ErrInvalid)
			}
			return brush.Viewport, nil
		}
		return Rect{Width: 1, Height: 1}, nil
	default:
		return Rect{}, fmt.Errorf("%w: unsupported brush tile kind %d", ErrUnsupported, brush.Kind)
	}
}

// validateBrushTileGradient 校验渐变画刷的插值模式、延展方式与停靠点基础合法性，防止零透明度提前返回跳过错误校验
// 入参: brush 线性或径向渐变画刷
// 返回: error 渐变属性或停靠点错误
func validateBrushTileGradient(brush *Brush) error {
	if brush.ColorInterpolationMode > ColorInterpolationScRGB || brush.SpreadMethod > SpreadRepeat || len(brush.Stops) < 2 {
		return fmt.Errorf("%w: invalid gradient attributes or stops", ErrInvalid)
	}
	for i, stop := range brush.Stops {
		if !geometryFinite(stop.Offset) {
			return fmt.Errorf("%w: gradient stop %d offset", ErrInvalid, i)
		}
		if err := validateBrushTileColor(stop.Color); err != nil {
			return fmt.Errorf("gradient stop %d: %w", i, err)
		}
	}
	return nil
}

// validateBrushTileColor 校验单瓦片画刷中纯色或渐变停靠点颜色的色彩空间、透明度与分量有限性
// 入参: value 待校验颜色
// 返回: error 颜色格式、空间或分量范围错误
func validateBrushTileColor(value Color) error {
	if !geometryFinite(value.Alpha) || value.Alpha < 0 || value.Alpha > 1 {
		return fmt.Errorf("%w: invalid brush color alpha", ErrInvalid)
	}
	for _, component := range value.Components {
		if !geometryFinite(component) {
			return fmt.Errorf("%w: non-finite brush color component", ErrInvalid)
		}
	}
	switch value.Space {
	case ColorSRGB:
		if len(value.Components) != 3 {
			return fmt.Errorf("%w: sRGB color requires three components", ErrInvalid)
		}
		for _, component := range value.Components {
			if component < 0 || component > 1 {
				return fmt.Errorf("%w: sRGB component outside unit range", ErrInvalid)
			}
		}
		return nil
	case ColorScRGB:
		if len(value.Components) != 3 {
			return fmt.Errorf("%w: scRGB color requires three components", ErrInvalid)
		}
		return nil
	case ColorContext:
		if strings.Trim(value.ProfileURI, " \t\r\n") == "" || len(value.Components) == 0 || len(value.Components) > iccMaxChannels {
			return fmt.Errorf("%w: invalid ContextColor profile or components", ErrInvalid)
		}
		return nil
	default:
		return fmt.Errorf("%w: unknown brush color space", ErrInvalid)
	}
}
