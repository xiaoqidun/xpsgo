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
	"encoding/xml"
	"fmt"
	"math"
	"strings"
)

// printMicronUnit 定义微米到96 DPI固定页坐标单位的换算系数
const printMicronUnit = 96.0 / 25400

const (
	// PrintBindingNone 表示不执行装订
	PrintBindingNone PrintBinding = iota
	// PrintBindingBale 表示捆扎装订方式
	PrintBindingBale
	// PrintBindingBottom 表示底边装订方式
	PrintBindingBottom
	// PrintBindingLeft 表示左边装订方式
	PrintBindingLeft
	// PrintBindingRight 表示右边装订方式
	PrintBindingRight
	// PrintBindingTop 表示顶边装订方式
	PrintBindingTop
	// PrintBindingBooklet 表示小册子对折装订方式
	PrintBindingBooklet
	// PrintBindingStitchBottom 表示底边骑马钉装订方式
	PrintBindingStitchBottom
	// PrintBindingStitchLeft 表示左边骑马钉装订方式
	PrintBindingStitchLeft
	// PrintBindingStitchRight 表示右边骑马钉装订方式
	PrintBindingStitchRight
	// PrintBindingStitchTop 表示顶边骑马钉装订方式
	PrintBindingStitchTop
	// PrintBindingFold 表示折叠整理方式
	PrintBindingFold
	// PrintBindingJogOffset 表示错位分套整理方式
	PrintBindingJogOffset
	// PrintBindingTrim 表示裁切整理方式
	PrintBindingTrim
)

// printMediaSizes 保存Print Schema公开纸型的推荐微米尺寸，零高度表示卷纸长度未定
var printMediaSizes = map[string][2]int{
	"BusinessCard":                        {55000, 91000},
	"CreditCard":                          {54000, 86000},
	"ISOA0":                               {841000, 1189000},
	"ISOA1":                               {594000, 841000},
	"ISOA10":                              {26000, 37000},
	"ISOA2":                               {420000, 594000},
	"ISOA3":                               {297000, 420000},
	"ISOA3Extra":                          {322000, 445000},
	"ISOA3Rotated":                        {420000, 297000},
	"ISOA4":                               {210000, 297000},
	"ISOA4Extra":                          {235500, 322300},
	"ISOA4Rotated":                        {297000, 210000},
	"ISOA5":                               {148000, 210000},
	"ISOA5Extra":                          {174000, 235000},
	"ISOA5Rotated":                        {210000, 148000},
	"ISOA6":                               {105000, 148000},
	"ISOA6Rotated":                        {148000, 105000},
	"ISOA7":                               {74000, 105000},
	"ISOA8":                               {52000, 74000},
	"ISOA9":                               {37000, 52000},
	"ISOB0":                               {1000000, 1414000},
	"ISOB1":                               {707000, 1000000},
	"ISOB10":                              {31000, 44000},
	"ISOB2":                               {500000, 707000},
	"ISOB3":                               {353000, 500000},
	"ISOB4":                               {250000, 353000},
	"ISOB4Envelope":                       {250000, 353000},
	"ISOB5Envelope":                       {176000, 250000},
	"ISOB5Extra":                          {201000, 276000},
	"ISOB7":                               {88000, 125000},
	"ISOB8":                               {62000, 88000},
	"ISOB9":                               {44000, 62000},
	"ISOC0":                               {917000, 1297000},
	"ISOC1":                               {648000, 917000},
	"ISOC10":                              {28000, 40000},
	"ISOC2":                               {458000, 648000},
	"ISOC3":                               {324000, 458000},
	"ISOC3Envelope":                       {324000, 458000},
	"ISOC4":                               {229000, 324000},
	"ISOC4Envelope":                       {229000, 324000},
	"ISOC5":                               {162000, 229000},
	"ISOC5Envelope":                       {162000, 229000},
	"ISOC6":                               {114000, 162000},
	"ISOC6C5Envelope":                     {114000, 229000},
	"ISOC6Envelope":                       {114000, 162000},
	"ISOC7":                               {81000, 114000},
	"ISOC8":                               {57000, 81000},
	"ISOC9":                               {40000, 57000},
	"ISODLEnvelope":                       {110000, 220000},
	"ISODLEnvelopeRotated":                {220000, 110000},
	"ISOSRA3":                             {320000, 450000},
	"Japan2LPhoto":                        {127000, 178000},
	"JapanChou3Envelope":                  {120000, 235000},
	"JapanChou3EnvelopeRotated":           {235000, 120000},
	"JapanChou4Envelope":                  {90000, 205000},
	"JapanChou4EnvelopeRotated":           {205000, 90000},
	"JapanDoubleHagakiPostcard":           {200000, 148000},
	"JapanDoubleHagakiPostcardRotated":    {148000, 200000},
	"JapanHagakiPostcard":                 {100000, 148000},
	"JapanHagakiPostcardRotated":          {148000, 100000},
	"JapanKaku2Envelope":                  {240000, 332000},
	"JapanKaku2EnvelopeRotated":           {332000, 240000},
	"JapanKaku3Envelope":                  {216000, 277000},
	"JapanKaku3EnvelopeRotated":           {277000, 216000},
	"JapanLPhoto":                         {89000, 127000},
	"JapanQuadrupleHagakiPostcard":        {200000, 297000},
	"JapanYou1Envelope":                   {120000, 176000},
	"JapanYou2Envelope":                   {114000, 162000},
	"JapanYou3Envelope":                   {98000, 148000},
	"JapanYou4Envelope":                   {105000, 235000},
	"JapanYou4EnvelopeRotated":            {235000, 105000},
	"JapanYou6Envelope":                   {98000, 190000},
	"JapanYou6EnvelopeRotated":            {98000, 190000},
	"JISB0":                               {1030000, 1456000},
	"JISB1":                               {728000, 1030000},
	"JISB10":                              {32000, 45000},
	"JISB2":                               {515000, 728000},
	"JISB3":                               {364000, 515000},
	"JISB4":                               {257000, 364000},
	"JISB4Rotated":                        {364000, 257000},
	"JISB5":                               {182000, 257000},
	"JISB5Rotated":                        {257000, 182000},
	"JISB6":                               {128000, 182000},
	"JISB6Rotated":                        {182000, 128000},
	"JISB7":                               {91000, 128000},
	"JISB8":                               {64000, 91000},
	"JISB9":                               {45000, 64000},
	"NorthAmerica10x11":                   {254000, 279400},
	"NorthAmerica10x12":                   {254000, 304800},
	"NorthAmerica10x14":                   {254000, 355600},
	"NorthAmerica11x17":                   {279400, 431800},
	"NorthAmerica14x17":                   {355600, 431800},
	"NorthAmerica4x6":                     {101600, 152400},
	"NorthAmerica4x8":                     {101600, 203200},
	"NorthAmerica5x7":                     {127000, 177800},
	"NorthAmerica8x10":                    {203200, 254000},
	"NorthAmerica9x11":                    {228600, 279400},
	"NorthAmericaArchitectureASheet":      {228600, 304800},
	"NorthAmericaArchitectureBSheet":      {304800, 457200},
	"NorthAmericaArchitectureCSheet":      {457200, 609600},
	"NorthAmericaArchitectureDSheet":      {609600, 914400},
	"NorthAmericaArchitectureESheet":      {914400, 1219200},
	"NorthAmericaCSheet":                  {431800, 558800},
	"NorthAmericaDSheet":                  {558800, 863600},
	"NorthAmericaESheet":                  {863600, 1117600},
	"NorthAmericaExecutive":               {184150, 266700},
	"NorthAmericaGermanLegalFanfold":      {215900, 330200},
	"NorthAmericaGermanStandardFanfold":   {215900, 304800},
	"NorthAmericaLegal":                   {215900, 355600},
	"NorthAmericaLegalExtra":              {241300, 381000},
	"NorthAmericaLetter":                  {215900, 279400},
	"NorthAmericaLetterExtra":             {241300, 304800},
	"NorthAmericaLetterPlus":              {215900, 322326},
	"NorthAmericaLetterRotated":           {279400, 215900},
	"NorthAmericaMonarchEnvelope":         {98425, 177800},
	"NorthAmericaNote":                    {215900, 279400},
	"NorthAmericaNumber10Envelope":        {104775, 241300},
	"NorthAmericaNumber10EnvelopeRotated": {241300, 104775},
	"NorthAmericaNumber11Envelope":        {114300, 263525},
	"NorthAmericaNumber12Envelope":        {120650, 279400},
	"NorthAmericaNumber14Envelope":        {127000, 292100},
	"NorthAmericaNumber9Envelope":         {98425, 225425},
	"NorthAmericaPersonalEnvelope":        {92075, 165100},
	"NorthAmericaQuarto":                  {215000, 275000},
	"NorthAmericaStatement":               {139700, 215900},
	"NorthAmericaSuperA":                  {227000, 356000},
	"NorthAmericaSuperB":                  {305000, 487000},
	"NorthAmericaTabloid":                 {279400, 431800},
	"NorthAmericaTabloidExtra":            {296926, 457200},
	"OtherMetricA3Plus":                   {329000, 483000},
	"OtherMetricA4Plus":                   {210000, 330000},
	"OtherMetricFolio":                    {215900, 330200},
	"OtherMetricInviteEnvelope":           {220000, 220000},
	"OtherMetricItalianEnvelope":          {110000, 230000},
	"PRC10Envelope":                       {324000, 458000},
	"PRC10EnvelopeRotated":                {458000, 324000},
	"PRC16K":                              {146000, 215000},
	"PRC16KRotated":                       {215000, 146000},
	"PRC1Envelope":                        {102000, 165000},
	"PRC1EnvelopeRotated":                 {165000, 102000},
	"PRC2Envelope":                        {102000, 176000},
	"PRC2EnvelopeRotated":                 {176000, 102000},
	"PRC32K":                              {97000, 151000},
	"PRC32KBig":                           {97000, 151000},
	"PRC32KRotated":                       {151000, 97000},
	"PRC3Envelope":                        {125000, 176000},
	"PRC3EnvelopeRotated":                 {176000, 125000},
	"PRC4Envelope":                        {110000, 208000},
	"PRC4EnvelopeRotated":                 {208000, 110000},
	"PRC5Envelope":                        {110000, 220000},
	"PRC5EnvelopeRotated":                 {220000, 110000},
	"PRC6Envelope":                        {120000, 230000},
	"PRC6EnvelopeRotated":                 {230000, 120000},
	"PRC7Envelope":                        {160000, 230000},
	"PRC7EnvelopeRotated":                 {230000, 160000},
	"PRC8Envelope":                        {120000, 309000},
	"PRC8EnvelopeRotated":                 {309000, 120000},
	"PRC9Envelope":                        {229000, 324000},
	"PRC9EnvelopeRotated":                 {324000, 229000},
	"Roll04Inch":                          {101600, 0},
	"Roll06Inch":                          {152400, 0},
	"Roll08Inch":                          {203200, 0},
	"Roll12Inch":                          {304800, 0},
	"Roll15Inch":                          {381000, 0},
	"Roll18Inch":                          {457200, 0},
	"Roll22Inch":                          {558800, 0},
	"Roll24Inch":                          {609600, 0},
	"Roll30Inch":                          {762000, 0},
	"Roll36Inch":                          {914400, 0},
	"Roll54Inch":                          {1371600, 0},
}

// printBindingNames 映射Print Schema公开装订Option名称到PrintBinding
var printBindingNames = map[string]PrintBinding{
	"None": PrintBindingNone, "Bale": PrintBindingBale,
	"BindBottom": PrintBindingBottom, "BindLeft": PrintBindingLeft,
	"BindRight": PrintBindingRight, "BindTop": PrintBindingTop,
	"Booklet": PrintBindingBooklet, "EdgeStitchBottom": PrintBindingStitchBottom,
	"EdgeStitchLeft": PrintBindingStitchLeft, "EdgeStitchRight": PrintBindingStitchRight,
	"EdgeStitchTop": PrintBindingStitchTop, "Fold": PrintBindingFold,
	"JogOffset": PrintBindingJogOffset, "Trim": PrintBindingTrim,
}

// printMediaPlacement 保存进纸坐标系中的图像旋转方向及偏移
type printMediaPlacement struct {
	rotation Matrix
	offset   Point
}

// PrintLayoutOptions 设置页面打印的基础票据、物理介质及解析预算，Settings.Scope须为Unknown
// Defaults提供消费者基础设置，文档中更具体的票据项优先
type PrintLayoutOptions struct {
	Defaults *PrintSettings
	Media    PrintMedia
	Settings PrintSettingsOptions
}

// PrintMedia 指定物理介质尺寸与可打印区域，单位为九十六分之一英寸；未指定宽高时回退票据或页面尺寸，ImageableArea为nil时采用整张介质
// LandscapeReverse为true时将Landscape解释为逆时针270度，默认为逆时针90度
// PSCustomMediaSize采用进纸坐标系（宽为跨进纸方向，高为沿进纸方向，进纸指向负Y），PS偏移在缩放旋转后应用
type PrintMedia struct {
	Width, Height    float64
	ImageableArea    *Rect
	LandscapeReverse bool
}

// PrintLayout 保存页面到物理介质的变换及裁剪区域，PageClip位于页面空间，MediaClip位于介质空间
// PageBorderless为Borderless时采用出血区域裁剪，否则按固定页面宽高校验和裁剪
type PrintLayout struct {
	Width, Height float64
	Transform     Matrix
	PageClip      Rect
	MediaClip     Rect
}

// printLayoutSettings 保存已校验票据及参数初始值，只读取当前布局引用的参数
type printLayoutSettings struct {
	model   *PrintSettings
	values  map[xml.Name]*PrintValue
	options printSettingsConfig
}

// PrintBinding 表示票据声明的装订方式
type PrintBinding uint8

// PrintFinishing 保存装订方式与留白宽度（单位为九十六分之一英寸），作业级与文档级设置分开保存
type PrintFinishing struct {
	Binding PrintBinding
	Gutter  float64
}

// DefaultPrintLayoutOptions 返回默认的页面打印布局参数
// 返回: PrintLayoutOptions 打印布局参数
func DefaultPrintLayoutOptions() PrintLayoutOptions {
	return PrintLayoutOptions{Settings: DefaultPrintSettingsOptions()}
}

// String 返回装订方式名称
// 返回: string 装订方式名称
func (b PrintBinding) String() string {
	switch b {
	case PrintBindingNone:
		return "None"
	case PrintBindingBale:
		return "Bale"
	case PrintBindingBottom:
		return "BindBottom"
	case PrintBindingLeft:
		return "BindLeft"
	case PrintBindingRight:
		return "BindRight"
	case PrintBindingTop:
		return "BindTop"
	case PrintBindingBooklet:
		return "Booklet"
	case PrintBindingStitchBottom:
		return "EdgeStitchBottom"
	case PrintBindingStitchLeft:
		return "EdgeStitchLeft"
	case PrintBindingStitchRight:
		return "EdgeStitchRight"
	case PrintBindingStitchTop:
		return "EdgeStitchTop"
	case PrintBindingFold:
		return "Fold"
	case PrintBindingJogOffset:
		return "JogOffset"
	case PrintBindingTrim:
		return "Trim"
	default:
		return fmt.Sprintf("PrintBinding(%d)", b)
	}
}

// mediaSize 解析显式介质几何或公开纸型默认尺寸，并校验是否与调用方物理介质冲突
// 入参: media 待确定的物理介质，PS自定义介质使用跨进纸宽度和沿进纸高度
// 返回: printMediaPlacement 介质方向及独立偏移, error 描述值、缺参、未知尺寸或冲突错误
func (s *printLayoutSettings) mediaSize(media *PrintMedia) (printMediaPlacement, error) {
	placement := printMediaPlacement{rotation: IdentityMatrix()}
	option, _, err := s.option(s.model.Elements, "PageMediaSize")
	if err != nil || option == nil {
		return placement, err
	}
	if option.Name == (xml.Name{Space: printKeywordsNS, Local: "PSCustomMediaSize"}) {
		return s.postScriptMedia(option, media)
	}
	dimensions, predefined := printMediaSizes[option.Name.Local]
	predefined = predefined && option.Name.Space == printKeywordsNS
	custom := option.Name == (xml.Name{Space: printKeywordsNS, Local: "CustomMediaSize"})
	if option.Name.Space == printKeywordsNS && !predefined && !custom {
		return placement, fmt.Errorf("%w: unknown public print media %s", ErrUnsupported, option.Name.Local)
	}
	if err := printOptionProperties(option, "MediaSizeWidth", "MediaSizeHeight"); err != nil {
		return placement, err
	}
	width, hasWidth, err := s.number(option, "MediaSizeWidth")
	if err != nil {
		return placement, err
	}
	height, hasHeight, err := s.number(option, "MediaSizeHeight")
	if err != nil {
		return placement, err
	}
	if !hasWidth && !hasHeight && predefined {
		width, height = float64(dimensions[0]), float64(dimensions[1])
		if height == 0 {
			if media.Width == 0 {
				return placement, fmt.Errorf("%w: roll media requires an explicit length", ErrUnsupported)
			}
			if !printCoordinateEqual(media.Width, width*printMicronUnit) {
				return placement, fmt.Errorf("%w: physical roll width conflicts with print ticket", ErrInvalid)
			}
			return placement, nil
		}
	} else if !hasWidth && !hasHeight && !custom && media.Width > 0 {
		return placement, nil
	} else if !hasWidth || !hasHeight {
		return placement, fmt.Errorf("%w: print media option requires dimensions", ErrUnsupported)
	}
	return placement, printSetMediaSize(media, width, height)
}

// postScriptMedia 解析PSCustomMediaSize的五个PostScript参数并换算进纸方向与偏移
// 入参: option PS自定义选择, media 跨进纸宽度及沿进纸高度
// 返回: printMediaPlacement 内容方向及微米换算后的偏移, error 缺参、非法数、尺寸或冲突错误
func (s *printLayoutSettings) postScriptMedia(option *PrintSetting, media *PrintMedia) (printMediaPlacement, error) {
	var placement printMediaPlacement
	names := [...]string{"PSWidth", "PSHeight", "PSWidthOffset", "PSHeightOffset", "PSOrientation"}
	if err := printOptionProperties(option, names[:]...); err != nil {
		return placement, err
	}
	var values [5]float64
	for index, name := range names {
		value, exists, err := s.number(option, name)
		if err != nil {
			return placement, err
		}
		if !exists {
			return placement, fmt.Errorf("%w: missing print media %s", ErrUnsupported, name)
		}
		values[index] = value
	}
	if values[4] < 0 || values[4] > 3 {
		return placement, fmt.Errorf("%w: print media PSOrientation", ErrInvalid)
	}
	if err := printSetMediaSize(media, values[0], values[1]); err != nil {
		return placement, err
	}
	switch values[4] {
	case 0:
		placement.rotation = Matrix{B: 1, C: -1, E: media.Width}
	case 1:
		placement.rotation = IdentityMatrix()
	case 2:
		placement.rotation = Matrix{B: -1, C: 1, F: media.Height}
	case 3:
		placement.rotation = Matrix{A: -1, D: -1, E: media.Width, F: media.Height}
	}
	placement.offset = Point{X: values[2] * printMicronUnit, Y: values[3] * printMicronUnit}
	return placement, nil
}

// printSetMediaSize 将正微米尺寸换算为布局单位，并要求调用方显式尺寸与票据一致
// 入参: media 待确定的介质, width, height 票据微米尺寸
// 返回: error 非正尺寸或物理介质冲突错误
func printSetMediaSize(media *PrintMedia, width, height float64) error {
	if width <= 0 || height <= 0 {
		return fmt.Errorf("%w: print media dimensions", ErrInvalid)
	}
	width, height = width*printMicronUnit, height*printMicronUnit
	if media.Width > 0 && (!printCoordinateEqual(media.Width, width) || !printCoordinateEqual(media.Height, height)) {
		return fmt.Errorf("%w: physical media conflicts with print ticket", ErrInvalid)
	}
	media.Width, media.Height = width, height
	return nil
}

// PrintSettings 合并基础设置和指定页面的作业、文档及页面票据，不执行设备约束或选择默认Option
// 每份票据先按关联层级过滤，较具体的设置整项覆盖同名根设置；默认保留所有有效层级
// 入参: ctx 取消Context，nil采用Background, index 页面序号, defaults 基础设置，nil为空设置, options 输出作用域及资源参数
// 返回: *PrintSettings 独立有效设置, error 序号、票据格式、关联、资源或取消错误
func (r *Reader) PrintSettings(ctx context.Context, index int, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	return r.readPrintSettings(ctx, index, defaults, options)
}

// readPrintSettings 在调用方持有读锁时合并票据链，不重复获取阅读器锁或修改输入设置
// 入参: ctx 取消Context, index 页面序号, defaults 基础设置, options 输出过滤及资源参数
// 返回: *PrintSettings 合并设置, error 状态、读取、合并或取消错误
func (r *Reader) readPrintSettings(ctx context.Context, index int, defaults *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, error) {
	if r.closed {
		return nil, ErrClosed
	}
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if err := checkContext(configuration.context); err != nil {
		return nil, err
	}
	outputScope := configuration.Scope
	configuration.Scope = PrintScopeUnknown
	empty := &PrintSettings{Version: 1}
	if defaults == nil {
		defaults = empty
	}
	result, err := MergePrintSettings(configuration.context, empty, defaults, &configuration.PrintSettingsOptions)
	if err != nil {
		return nil, err
	}
	tickets, err := r.readPrintTicketHierarchyOptions(index, configuration.Limits, configuration.context)
	if err != nil {
		return nil, err
	}
	for _, ticket := range tickets {
		local := configuration.PrintSettingsOptions
		local.Scope = ticket.Scope
		settings, err := ticket.Settings(configuration.context, &local)
		if err != nil {
			return nil, &PartError{Part: ticket.Part, Err: err}
		}
		result, err = MergePrintSettings(configuration.context, result, settings, &configuration.PrintSettingsOptions)
		if err != nil {
			return nil, &PartError{Part: ticket.Part, Err: err}
		}
	}
	if outputScope != PrintScopeUnknown {
		configuration.Scope = outputScope
		return MergePrintSettings(configuration.context, result, empty, &configuration.PrintSettingsOptions)
	}
	return result, checkContext(configuration.context)
}

// PrintLayout 加载页面并应用其有效票据，返回可用于矢量或栅格输出的物理布局
// 入参: ctx 取消Context，nil采用Background, index 页面序号, options 基础票据、介质及资源参数，nil采用默认值
// 返回: *PrintLayout 独立布局, error 页面、票据、设置、资源或取消错误
func (r *Reader) PrintLayout(ctx context.Context, index int, options *PrintLayoutOptions) (*PrintLayout, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	configuration := DefaultPrintLayoutOptions()
	if options != nil {
		configuration = *options
	}
	_, _, layout, err := r.readPrintPage(ctx, index, configuration)
	return layout, err
}

// readPrintPage 在一个读锁下读取页面、有效票据及布局，供打印绘制复用
// 入参: ctx 取消Context, index 页面序号, options 打印布局参数
// 返回: *Page 独立页面, *PrintSettings 有效票据, *PrintLayout 布局, error 读取或布局错误
func (r *Reader) readPrintPage(ctx context.Context, index int, options PrintLayoutOptions) (*Page, *PrintSettings, *PrintLayout, error) {
	page, settings, layout, err := r.readPrintPageHeader(ctx, index, options)
	if err != nil {
		return nil, nil, nil, err
	}
	page, err = r.readPageSceneContent(page, false, nil, ctx)
	if err != nil {
		return nil, nil, nil, err
	}
	return page, settings, layout, nil
}

// readPrintPageHeader 读取有效票据和页面尺寸并计算布局，供输出预检在资源加载前执行
// 入参: ctx 取消Context, index 页面序号, options 打印布局参数
// 返回: *Page 私有页面头及源树, *PrintSettings 有效票据, *PrintLayout 布局, error 票据、页面头或布局错误
func (r *Reader) readPrintPageHeader(ctx context.Context, index int, options PrintLayoutOptions) (*Page, *PrintSettings, *PrintLayout, error) {
	if options.Settings.Scope != PrintScopeUnknown {
		return nil, nil, nil, fmt.Errorf("%w: scope on print page layout", ErrInvalid)
	}
	settings, err := r.readPrintSettings(ctx, index, options.Defaults, &options.Settings)
	if err != nil {
		return nil, nil, nil, err
	}
	page, err := r.readPageHeader(index, nil, ctx)
	if err != nil {
		return nil, nil, nil, err
	}
	layout, err := settings.Layout(ctx, page, options.Media, &options.Settings)
	if err != nil {
		return nil, nil, nil, err
	}
	return page, settings, layout, nil
}

// Layout 按Print Schema计算介质、方向、缩放、对齐与镜像布局，不执行作业编排或设备控制
// 未指定缩放时保持原尺寸与原点；自动适配默认居中，自定义缩放以页面原点为基准，冲突时返回ErrUnsupported
// 入参: ctx 取消Context，nil采用Background, page 页面尺寸及区域, media 已选物理介质, options 资源参数，Scope须为Unknown
// 返回: *PrintLayout 独立布局, error 页面、设置、未支持组合、资源或取消错误
func (s *PrintSettings) Layout(ctx context.Context, page *Page, media PrintMedia, options *PrintSettingsOptions) (*PrintLayout, error) {
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, err
	}
	if configuration.Scope != PrintScopeUnknown || page == nil || !geometryFinite(page.Width, page.Height, media.Width, media.Height) || page.Width < 1 || page.Height < 1 || media.Width < 0 || media.Height < 0 || (media.Width == 0) != (media.Height == 0) {
		return nil, fmt.Errorf("%w: print layout page or media", ErrInvalid)
	}
	if media.ImageableArea != nil {
		area := *media.ImageableArea
		if !geometryFinite(area.X, area.Y, area.Width, area.Height, area.X+area.Width, area.Y+area.Height) || area.Width <= 0 || area.Height <= 0 {
			return nil, fmt.Errorf("%w: print imageable area", ErrInvalid)
		}
	}
	if s == nil {
		s = &PrintSettings{Version: 1}
	}
	root, err := printSettingsRoot(s, configuration)
	if err != nil {
		return nil, err
	}
	model, err := parsePrintSettings(root, configuration)
	if err != nil {
		return nil, err
	}
	return newPrintLayoutSettings(model, configuration).layout(page, media)
}

// option 读取指定层级的唯一选择，不按局部名称匹配其他命名空间
// 入参: elements 当前设置层级, name 公共Feature名称
// 返回: *PrintSetting 已选Option, *PrintSetting Feature，未声明时均为nil, error 选择数量错误
func (s *printLayoutSettings) option(elements []PrintSetting, name string) (*PrintSetting, *PrintSetting, error) {
	for index := range elements {
		feature := &elements[index]
		if feature.Kind != PrintSettingFeature || feature.Name != (xml.Name{Space: printKeywordsNS, Local: name}) {
			continue
		}
		var selected *PrintSetting
		for child := range feature.Children {
			value := &feature.Children[child]
			if value.Kind == PrintSettingOption {
				if selected != nil {
					return nil, feature, fmt.Errorf("%w: multiple print layout options for %s", ErrInvalid, name)
				}
				selected = value
			}
		}
		if selected == nil {
			return nil, feature, fmt.Errorf("%w: missing print layout option for %s", ErrInvalid, name)
		}
		return selected, feature, nil
	}
	return nil, nil, nil
}

// keyword 读取公共Option名称，允许说明性Property但不接受配置描述，私有选择不当作同名标准选项
// 入参: option 已选Option，nil表示未声明, fallback 实现默认值
// 返回: string 公共名称, error 私有或非空选项错误
func (s *printLayoutSettings) keyword(option *PrintSetting, fallback string) (string, error) {
	if option == nil {
		return fallback, nil
	}
	if option.Name.Space != printKeywordsNS {
		return "", fmt.Errorf("%w: print layout option {%s}%s", ErrUnsupported, option.Name.Space, option.Name.Local)
	}
	for _, child := range option.Children {
		if child.Kind != PrintSettingProperty {
			return "", fmt.Errorf("%w: unexpected print layout option content", ErrInvalid)
		}
	}
	return option.Name.Local, nil
}

// number 读取布局Option的整数描述值，参数引用只取显式初始化，不猜测设备默认值
// 入参: option 已选Option, name 公共描述值名称
// 返回: float64 数值, bool 是否声明, error 类型、缺失参数或数值范围错误
func (s *printLayoutSettings) number(option *PrintSetting, name string) (float64, bool, error) {
	if option == nil {
		return 0, false, nil
	}
	for _, child := range option.Children {
		if child.Kind != PrintSettingScoredProperty || child.Name != (xml.Name{Space: printKeywordsNS, Local: name}) {
			continue
		}
		value, reference := printScoredValue(child.Children)
		if reference != (xml.Name{}) {
			value = s.values[reference]
			if value == nil {
				return 0, true, fmt.Errorf("%w: print layout parameter {%s}%s not initialized", ErrUnsupported, reference.Space, reference.Local)
			}
		}
		if value == nil || value.Type != (xml.Name{Space: printValueNS, Local: "integer"}) || !printInteger(strings.Trim(value.Text, " \t\r\n")) {
			return 0, true, fmt.Errorf("%w: print layout integer %s", ErrInvalid, name)
		}
		decimal, err := printParameterNumber(value.Text, s.options)
		if err != nil {
			return 0, true, err
		}
		result, _ := decimal.Float64()
		if !geometryFinite(result) {
			return 0, true, fmt.Errorf("%w: print layout numeric range", ErrLimit)
		}
		return result, true, nil
	}
	return 0, false, nil
}

// layout 组合页面镜像、内容缩放及物理介质方向，保持两个坐标空间的裁剪独立
// 入参: page 页面, media 物理介质
// 返回: *PrintLayout 布局, error 设置、区域或变换错误
func (s *printLayoutSettings) layout(page *Page, media PrintMedia) (*PrintLayout, error) {
	if err := checkContext(s.options.context); err != nil {
		return nil, err
	}
	for _, value := range s.model.Elements {
		if value.Kind == PrintSettingFeature && value.Name == (xml.Name{Space: printKeywordsNS, Local: "ScaleOffsetAlignment"}) {
			return nil, fmt.Errorf("%w: ScaleOffsetAlignment must be a child of PageScaling", ErrInvalid)
		}
	}
	orientationOption, _, err := s.option(s.model.Elements, "PageOrientation")
	if err != nil {
		return nil, err
	}
	orientation, err := s.keyword(orientationOption, "Portrait")
	if err != nil {
		return nil, err
	}
	placement, err := s.mediaSize(&media)
	if err != nil {
		return nil, err
	}
	if media.Width == 0 {
		media.Width, media.Height = page.Width, page.Height
		if orientation == "Landscape" || orientation == "ReverseLandscape" {
			media.Width, media.Height = media.Height, media.Width
		}
	}
	orientedMedia := media
	if placement.rotation.A == 0 {
		orientedMedia.Width, orientedMedia.Height = media.Height, media.Width
	}
	rotation, err := printOrientation(orientation, orientedMedia)
	if err != nil {
		return nil, err
	}
	rotation = placement.rotation.Mul(rotation)
	physical := Rect{Width: media.Width, Height: media.Height}
	area := physical
	if media.ImageableArea != nil {
		area = *media.ImageableArea
		if !printBoxWithin(area, physical) || area.Width <= 0 || area.Height <= 0 {
			return nil, fmt.Errorf("%w: print imageable area", ErrInvalid)
		}
	}
	inverse, err := rotation.Inverse()
	if err != nil {
		return nil, err
	}
	pageBox := Rect{Width: page.Width, Height: page.Height}
	content, bleed := pageBox, pageBox
	if page.HasContentBox {
		content = page.ContentBox
		if !printBoxWithin(content, pageBox) {
			return nil, fmt.Errorf("%w: print content box", ErrInvalid)
		}
	}
	if page.HasBleedBox {
		bleed = page.BleedBox
		if !printBoxWithin(pageBox, bleed) {
			return nil, fmt.Errorf("%w: print bleed box", ErrInvalid)
		}
	}
	mirrorOption, _, err := s.option(s.model.Elements, "PageMirrorImage")
	if err != nil {
		return nil, err
	}
	mirrorName, err := s.keyword(mirrorOption, "None")
	if err != nil {
		return nil, err
	}
	mirror := IdentityMatrix()
	switch mirrorName {
	case "None":
	case "MirrorImageWidth":
		mirror.A, mirror.E = -1, page.Width
	case "MirrorImageHeight":
		mirror.D, mirror.F = -1, page.Height
	default:
		return nil, fmt.Errorf("%w: print mirror option %s", ErrUnsupported, mirrorName)
	}
	content, bleed = printTransformBox(content, mirror), printTransformBox(bleed, mirror)
	scaling, feature, err := s.option(s.model.Elements, "PageScaling")
	if err != nil {
		return nil, err
	}
	scale, err := s.scale(scaling, feature, content, bleed, pageBox, printTransformBox(area, inverse), printTransformBox(physical, inverse))
	if err != nil {
		return nil, err
	}
	borderOption, _, err := s.option(s.model.Elements, "PageBorderless")
	if err != nil {
		return nil, err
	}
	border, err := s.keyword(borderOption, "None")
	if err != nil {
		return nil, err
	}
	pageClip := pageBox
	switch border {
	case "None":
	case "Borderless":
		area = physical
		if page.HasBleedBox {
			pageClip = page.BleedBox
		}
	default:
		return nil, fmt.Errorf("%w: print border option %s", ErrUnsupported, border)
	}
	transform := rotation.Mul(scale).Mul(mirror)
	transform.E += placement.offset.X
	transform.F += placement.offset.Y
	outputBox := printTransformBox(pageClip, transform)
	if media.Width <= 0 || media.Height <= 0 || !geometryFillMatrixFinite(transform) || !geometryFinite(media.Width, media.Height, area.X+area.Width, area.Y+area.Height, outputBox.X, outputBox.Y, outputBox.Width, outputBox.Height, outputBox.X+outputBox.Width, outputBox.Y+outputBox.Height) {
		return nil, fmt.Errorf("%w: print layout transform range", ErrLimit)
	}
	return &PrintLayout{Width: media.Width, Height: media.Height, Transform: transform, PageClip: pageClip, MediaClip: area}, nil
}

// printOrientation 将内容坐标空间映射到物理介质坐标空间，旋转角采用Print Schema的逆时针约定
// 入参: name 方向选项, media 物理尺寸及Landscape设备选择
// 返回: Matrix 方向变换, error 未支持方向错误
func printOrientation(name string, media PrintMedia) (Matrix, error) {
	switch name {
	case "Portrait":
		return IdentityMatrix(), nil
	case "Landscape":
		if !media.LandscapeReverse {
			return Matrix{B: -1, C: 1, F: media.Height}, nil
		}
		fallthrough
	case "ReverseLandscape":
		return Matrix{B: 1, C: -1, E: media.Width}, nil
	case "ReversePortrait":
		return Matrix{A: -1, D: -1, E: media.Width, F: media.Height}, nil
	default:
		return Matrix{}, fmt.Errorf("%w: print orientation %s", ErrUnsupported, name)
	}
}

// printTransformBox 计算直角旋转、镜像或轴缩放后的轴对齐区域
// 入参: box 原区域, transform 变换
// 返回: Rect 变换后包围区域
func printTransformBox(box Rect, transform Matrix) Rect {
	a := transform.Transform(Point{box.X, box.Y})
	b := transform.Transform(Point{box.X + box.Width, box.Y})
	c := transform.Transform(Point{box.X + box.Width, box.Y + box.Height})
	d := transform.Transform(Point{box.X, box.Y + box.Height})
	x, y := min(a.X, b.X, c.X, d.X), min(a.Y, b.Y, c.Y, d.Y)
	return Rect{X: x, Y: y, Width: max(a.X, b.X, c.X, d.X) - x, Height: max(a.Y, b.Y, c.Y, d.Y) - y}
}

// printBoxWithin 校验有限非负区域是否完整落入另一区域，不使用裁剪掩盖非法设备参数
// 入参: inner 内部区域, outer 外部区域
// 返回: bool 是否包含
func printBoxWithin(inner, outer Rect) bool {
	return geometryFinite(inner.X, inner.Y, inner.Width, inner.Height, outer.X, outer.Y, outer.Width, outer.Height, inner.X+inner.Width, inner.Y+inner.Height, outer.X+outer.Width, outer.Y+outer.Height) && inner.Width >= 0 && inner.Height >= 0 && outer.Width >= 0 && outer.Height >= 0 && inner.X >= outer.X && inner.Y >= outer.Y && inner.Width <= outer.X+outer.Width-inner.X && inner.Height <= outer.Y+outer.Height-inner.Y
}

// printFitBoxWithin 校验适配结果区域是否在浮点容差内落入目标范围
// 入参: inner 适配结果, outer 目标区域
// 返回: bool 是否落入目标范围
func printFitBoxWithin(inner, outer Rect) bool {
	allowance := math.Max(1, max(math.Abs(outer.X), math.Abs(outer.Y), outer.Width, outer.Height)) * 1e-12
	return printBoxWithin(inner, Rect{X: outer.X - allowance, Y: outer.Y - allowance, Width: outer.Width + allowance*2, Height: outer.Height + allowance*2})
}

// printCoordinateEqual 在有限坐标范围内允许单位换算的浮点舍入，不忽略实际介质尺寸差异
// 入参: a, b 待比较尺寸
// 返回: bool 是否在八倍浮点相对精度内相等
func printCoordinateEqual(a, b float64) bool {
	return geometryFinite(a, b) && math.Abs(a-b) <= max(math.Abs(a), math.Abs(b))*8*2.220446049250313e-16
}

// newPrintLayoutSettings 为已校验设置建立参数索引，布局与作业编排共用显式初始化规则
// 入参: model 有效设置, options 数值及取消参数
// 返回: *printLayoutSettings 私有只读设置视图
func newPrintLayoutSettings(model *PrintSettings, options printSettingsConfig) *printLayoutSettings {
	settings := &printLayoutSettings{model: model, values: make(map[xml.Name]*PrintValue), options: options}
	for _, element := range model.Elements {
		if element.Kind == PrintSettingParameterInit {
			settings.values[element.Name] = element.Children[0].Value
		}
	}
	return settings
}

// leafOption 读取不允许子Feature的选择，避免执行父设置后静默丢弃未知后代
// 入参: elements 当前层级, name 公共Feature名称
// 返回: *PrintSetting 选择，未声明为nil, error 结构或未支持的子Feature错误
func (s *printLayoutSettings) leafOption(elements []PrintSetting, name string) (*PrintSetting, error) {
	option, feature, err := s.option(elements, name)
	if err != nil || feature == nil {
		return option, err
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature {
			return nil, fmt.Errorf("%w: print leaf subfeature %s", ErrUnsupported, name)
		}
	}
	return option, nil
}

// printOptionProperties 保留说明性Property，拒绝未执行的配置描述及嵌套ScoredProperty
// 入参: option 已选Option, names 当前能力支持的公共描述名称
// 返回: error 未支持的描述或嵌套配置错误
func printOptionProperties(option *PrintSetting, names ...string) error {
	for _, child := range option.Children {
		if child.Kind == PrintSettingProperty {
			continue
		}
		allowed := false
		for _, name := range names {
			if child.Kind == PrintSettingScoredProperty && child.Name == (xml.Name{Space: printKeywordsNS, Local: name}) {
				allowed = true
				break
			}
		}
		if !allowed {
			return fmt.Errorf("%w: print option description {%s}%s", ErrUnsupported, child.Name.Space, child.Name.Local)
		}
		for _, value := range child.Children {
			if value.Kind == PrintSettingScoredProperty {
				return fmt.Errorf("%w: nested print option description", ErrUnsupported)
			}
		}
	}
	return nil
}

// scale 计算内容坐标空间内的缩放和位置，参数偏移不随缩放再次放大
// 入参: option 缩放选择, feature 缩放Feature, content 内容区域, bleed 出血区域, page 页面区域, imageable 可打印区域, media 介质区域
// 返回: Matrix 缩放定位, error 选择、参数或适配冲突错误
func (s *printLayoutSettings) scale(option, feature *PrintSetting, content, bleed, page, imageable, media Rect) (Matrix, error) {
	if option == nil {
		return IdentityMatrix(), nil
	}
	if option.Name.Space != printKeywordsNS {
		return Matrix{}, fmt.Errorf("%w: private print scaling option", ErrUnsupported)
	}
	name := option.Name.Local
	anchor, selected, err := s.alignment(feature)
	if err != nil {
		return Matrix{}, err
	}
	if name != "Custom" && name != "CustomSquare" {
		for _, child := range option.Children {
			if child.Kind != PrintSettingProperty {
				return Matrix{}, fmt.Errorf("%w: print scaling description", ErrInvalid)
			}
		}
	}
	if name == "None" {
		return IdentityMatrix(), nil
	}
	if name == "Custom" || name == "CustomSquare" {
		return s.customScale(option, content, anchor, selected)
	}
	source, target := page, imageable
	switch name {
	case "FitApplicationBleedSizeToPageImageableSize":
		source = bleed
	case "FitApplicationContentSizeToPageImageableSize":
		source = content
	case "FitApplicationMediaSizeToPageImageableSize":
	case "FitApplicationMediaSizeToPageMediaSize":
		target = media
	default:
		return Matrix{}, fmt.Errorf("%w: print scaling option %s", ErrUnsupported, name)
	}
	if source.Width <= 0 || source.Height <= 0 {
		return Matrix{}, fmt.Errorf("%w: empty application region cannot determine print scaling", ErrUnsupported)
	}
	factor := min(target.Width/source.Width, target.Height/source.Height)
	result := Matrix{A: factor, D: factor, E: target.X + (target.Width-source.Width*factor)/2 - source.X*factor, F: target.Y + (target.Height-source.Height*factor)/2 - source.Y*factor}
	if selected {
		x, y := content.X+content.Width*anchor.X, content.Y+content.Height*anchor.Y
		result.E, result.F = x-factor*x, y-factor*y
		if !printFitBoxWithin(printTransformBox(source, result), target) {
			return Matrix{}, fmt.Errorf("%w: print alignment conflicts with fit bounds", ErrUnsupported)
		}
	}
	return result, nil
}

// alignment 读取缩放Feature内的九点对齐，定位基准是缩放前的应用内容区域
// 入参: feature PageScaling
// 返回: Point 归一化锚点, bool 是否声明, error 选择、位置或关键字错误
func (s *printLayoutSettings) alignment(feature *PrintSetting) (Point, bool, error) {
	option, err := s.leafOption(feature.Children, "ScaleOffsetAlignment")
	if err != nil || option == nil {
		return Point{}, false, err
	}
	name, err := s.keyword(option, "")
	if err != nil {
		return Point{}, true, err
	}
	switch name {
	case "BottomCenter":
		return Point{X: 0.5, Y: 1}, true, nil
	case "BottomLeft":
		return Point{Y: 1}, true, nil
	case "BottomRight":
		return Point{X: 1, Y: 1}, true, nil
	case "Center":
		return Point{X: 0.5, Y: 0.5}, true, nil
	case "CenterLeft":
		return Point{Y: 0.5}, true, nil
	case "CenterRight":
		return Point{X: 1, Y: 0.5}, true, nil
	case "TopCenter":
		return Point{X: 0.5}, true, nil
	case "TopLeft":
		return Point{}, true, nil
	case "TopRight":
		return Point{X: 1}, true, nil
	default:
		return Point{}, true, fmt.Errorf("%w: print alignment %s", ErrUnsupported, name)
	}
}

// customScale 按百分比缩放并应用以微米声明的偏移，未引用的ParameterInit不参与计算
// 入参: option Custom或CustomSquare, content 原内容区域, anchor 对齐锚点, aligned 是否声明对齐
// 返回: Matrix 内容空间变换, error 描述值、参数或范围错误
func (s *printLayoutSettings) customScale(option *PrintSetting, content Rect, anchor Point, aligned bool) (Matrix, error) {
	xName, yName := "ScaleWidth", "ScaleHeight"
	if option.Name.Local == "CustomSquare" {
		xName, yName = "Scale", "Scale"
	}
	x, hasX, err := s.number(option, xName)
	if err != nil {
		return Matrix{}, err
	}
	y, hasY, err := s.number(option, yName)
	if err != nil {
		return Matrix{}, err
	}
	offsetX, hasOffsetX, err := s.number(option, "OffsetWidth")
	if err != nil {
		return Matrix{}, err
	}
	offsetY, hasOffsetY, err := s.number(option, "OffsetHeight")
	if err != nil {
		return Matrix{}, err
	}
	if !hasX || !hasY || !hasOffsetX || !hasOffsetY {
		return Matrix{}, fmt.Errorf("%w: incomplete custom print scaling", ErrInvalid)
	}
	if x < 0 || y < 0 {
		return Matrix{}, fmt.Errorf("%w: negative print scaling", ErrInvalid)
	}
	if err := printOptionProperties(option, xName, yName, "OffsetWidth", "OffsetHeight"); err != nil {
		return Matrix{}, err
	}
	result := Matrix{A: x / 100, D: y / 100, E: offsetX * printMicronUnit, F: offsetY * printMicronUnit}
	if aligned {
		position := Point{content.X + content.Width*anchor.X, content.Y + content.Height*anchor.Y}
		result.E += position.X * (1 - result.A)
		result.F += position.Y * (1 - result.D)
	}
	return result, nil
}

// validatePrintLayoutFeatures 校验有效票据不含单页布局未支持的Feature
// 入参: settings 有效票据
// 返回: error 未支持设置错误
func validatePrintLayoutFeatures(settings *PrintSettings) error {
	for _, value := range settings.Elements {
		if value.Kind != PrintSettingFeature {
			continue
		}
		if value.Name.Space != printKeywordsNS {
			return fmt.Errorf("%w: print rendering feature {%s}%s", ErrUnsupported, value.Name.Space, value.Name.Local)
		}
		switch value.Name.Local {
		case "PageMediaSize", "PageOrientation", "PageScaling", "PageMirrorImage", "PageBorderless":
		default:
			return fmt.Errorf("%w: print rendering feature %s", ErrUnsupported, value.Name.Local)
		}
		for _, child := range value.Children {
			if child.Kind == PrintSettingFeature && (value.Name.Local != "PageScaling" || child.Name != (xml.Name{Space: printKeywordsNS, Local: "ScaleOffsetAlignment"})) {
				return fmt.Errorf("%w: print rendering subfeature {%s}%s", ErrUnsupported, child.Name.Space, child.Name.Local)
			}
		}
	}
	return nil
}

// checkBindingConflict 只检查两级装订声明是否冲突，不提前求值尚可被覆盖的文档默认参数
// 返回: error 结构或互斥错误
func (s *printLayoutSettings) checkBindingConflict() error {
	_, job, err := s.option(s.model.Elements, "JobBindAllDocuments")
	if err != nil {
		return err
	}
	_, document, err := s.option(s.model.Elements, "DocumentBinding")
	if err != nil {
		return err
	}
	if job != nil && document != nil {
		return fmt.Errorf("%w: simultaneous job and document binding", ErrInvalid)
	}
	return nil
}

// binding 解析公共装订方式和显式留白，不猜测设备参数或专有装订位置
// 入参: name 作业或文档Feature名称
// 返回: PrintFinishing 设置, bool 是否声明, error 描述、参数或能力错误
func (s *printLayoutSettings) binding(name string) (PrintFinishing, bool, error) {
	option, feature, err := s.option(s.model.Elements, name)
	if err != nil || option == nil {
		return PrintFinishing{}, feature != nil, err
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature {
			return PrintFinishing{}, true, fmt.Errorf("%w: print binding subfeature", ErrUnsupported)
		}
	}
	method, known := printBindingNames[option.Name.Local]
	if option.Name.Space != printKeywordsNS || !known {
		return PrintFinishing{}, true, fmt.Errorf("%w: print binding option {%s}%s", ErrUnsupported, option.Name.Space, option.Name.Local)
	}
	if method == PrintBindingNone {
		return PrintFinishing{}, true, printOptionProperties(option)
	}
	if err := printOptionProperties(option, "BindingGutter"); err != nil {
		return PrintFinishing{}, true, err
	}
	width, present, err := s.number(option, "BindingGutter")
	if err != nil {
		return PrintFinishing{}, true, err
	}
	if !present {
		return PrintFinishing{}, true, fmt.Errorf("%w: binding requires an explicit gutter", ErrUnsupported)
	}
	if width < 0 {
		return PrintFinishing{}, true, fmt.Errorf("%w: negative binding gutter", ErrInvalid)
	}
	if width > 0 && (method == PrintBindingBale || method == PrintBindingFold || method == PrintBindingJogOffset || method == PrintBindingTrim) {
		return PrintFinishing{}, true, fmt.Errorf("%w: device-defined binding gutter position", ErrUnsupported)
	}
	return PrintFinishing{Binding: method, Gutter: width * printMicronUnit}, true, nil
}

// printBindingGutter 计算装订留白与可打印区域的交集，背面按双面翻页方向镜像物理装订边
// 入参: finishing 装订设置, side 物理纸面, duplex 双面方向, back 是否为背面
// 返回: *Rect 实际禁止落墨的纸面区域，未相交或宽度为零时为nil
func printBindingGutter(finishing PrintFinishing, side PrintSide, duplex PrintDuplex, back bool) *Rect {
	if finishing.Binding == PrintBindingNone || finishing.Gutter == 0 {
		return nil
	}
	method := finishing.Binding
	if back {
		if duplex == PrintDuplexLongEdge {
			switch method {
			case PrintBindingLeft, PrintBindingStitchLeft:
				method = PrintBindingRight
			case PrintBindingRight, PrintBindingStitchRight:
				method = PrintBindingLeft
			}
		} else if duplex == PrintDuplexShortEdge {
			switch method {
			case PrintBindingTop, PrintBindingStitchTop:
				method = PrintBindingBottom
			case PrintBindingBottom, PrintBindingStitchBottom:
				method = PrintBindingTop
			}
		}
	}
	band := Rect{Width: side.Width, Height: side.Height}
	switch method {
	case PrintBindingLeft, PrintBindingStitchLeft:
		band.Width = min(finishing.Gutter, side.Width)
	case PrintBindingRight, PrintBindingStitchRight:
		band.Width = min(finishing.Gutter, side.Width)
		band.X = side.Width - band.Width
	case PrintBindingTop, PrintBindingStitchTop:
		band.Height = min(finishing.Gutter, side.Height)
	case PrintBindingBottom, PrintBindingStitchBottom:
		band.Height = min(finishing.Gutter, side.Height)
		band.Y = side.Height - band.Height
	case PrintBindingBooklet:
		band.Width = min(finishing.Gutter, side.Width)
		band.X = (side.Width - band.Width) / 2
	default:
		return nil
	}
	x, y := max(band.X, side.MediaClip.X), max(band.Y, side.MediaClip.Y)
	right := min(band.X+band.Width, side.MediaClip.X+side.MediaClip.Width)
	bottom := min(band.Y+band.Height, side.MediaClip.Y+side.MediaClip.Height)
	if right <= x || bottom <= y {
		return nil
	}
	return &Rect{X: x, Y: y, Width: right - x, Height: bottom - y}
}

// poster 从PagePoster的SheetsPerPage读取每页海报分幅纸张数
// 入参: maximum 单页分幅容量上限
// 返回: int 每页纸张数，未声明为1, error 描述值、类型或容量错误
func (s *printLayoutSettings) poster(maximum int) (int, error) {
	option, feature, err := s.option(s.model.Elements, "PagePoster")
	if err != nil || option == nil {
		return 1, err
	}
	for _, child := range feature.Children {
		if child.Kind == PrintSettingFeature {
			return 0, fmt.Errorf("%w: print poster subfeature", ErrUnsupported)
		}
	}
	value, err := s.scored(option, "SheetsPerPage")
	if err != nil {
		return 0, err
	}
	if value == nil {
		return 0, fmt.Errorf("%w: print poster requires a sheet-count description", ErrUnsupported)
	}
	if err := printOptionProperties(option, "SheetsPerPage"); err != nil {
		return 0, err
	}
	return s.integer(value, "SheetsPerPage", maximum)
}

// poster 按整除网格与行优先顺序将单页分幅为独立单面纸张并追加到输出
// 入参: page 页面描述, document 文档设置
// 返回: error 冲突、几何、取消或容量错误
func (p *printSheetPacker) poster(page printPlanPage, document printPlanDocument) error {
	if document.nup != 1 {
		return fmt.Errorf("%w: poster and NUp require incompatible sheet counts", ErrUnsupported)
	}
	if err := p.flush(); err != nil {
		return err
	}
	columns, rows, err := p.posterGrid(page.poster, page.layout.MediaClip)
	if err != nil {
		return err
	}
	area := page.layout.MediaClip
	factor := float64(min(columns, rows))
	for row := range rows {
		for column := range columns {
			if err := p.builder.step(1); err != nil {
				return err
			}
			mapping := Matrix{A: factor, D: factor,
				E: area.X*(1-factor) + (float64(columns)-factor)*area.Width/2 - float64(column)*area.Width,
				F: area.Y*(1-factor) + (float64(rows)-factor)*area.Height/2 - float64(row)*area.Height}
			placement := PrintPlacement{Page: page.index, DocumentIndex: page.document, Transform: mapping.Mul(page.layout.Transform), PageClip: page.layout.PageClip, MediaClip: area, Watermark: page.watermark, Negative: page.negative, Color: clonePrintColorPlan(page.colorPlan)}
			box := printTransformBox(page.layout.PageClip, placement.Transform)
			if !geometryFillMatrixFinite(placement.Transform) || !geometryFinite(box.X, box.Y, box.Width, box.Height, box.X+box.Width, box.Y+box.Height) {
				return fmt.Errorf("%w: print poster mapping", ErrLimit)
			}
			sheet := PrintSheet{Front: PrintSide{Width: page.layout.Width, Height: page.layout.Height, MediaClip: area, Pages: []PrintPlacement{placement}, Color: page.color}}
			sheet.Front.Gutter = printBindingGutter(document.finishing, sheet.Front, PrintSimplex, false)
			if err := p.builder.appendSheet(p.output, sheet, p.temporary); err != nil {
				return err
			}
		}
	}
	return nil
}

// posterGrid 按纸张数与可打印区域宽高比计算近方形整除分幅网格并计入工作预算
// 入参: count 纸张数, area 可打印区域
// 返回: int 列数, int 行数, error 取消、容量或无效区域错误
func (p *printSheetPacker) posterGrid(count int, area Rect) (int, int, error) {
	if count < 1 || area.Width <= 0 || area.Height <= 0 {
		return 0, 0, fmt.Errorf("%w: print poster grid", ErrInvalid)
	}
	columns := int(math.Sqrt(float64(count)))
	for columns > count/columns {
		columns--
	}
	for count%columns != 0 {
		if err := p.builder.step(1); err != nil {
			return 0, 0, err
		}
		columns--
	}
	rows := count / columns
	if area.Width >= area.Height {
		columns, rows = rows, columns
	}
	return columns, rows, p.builder.step(1)
}

// printSinglePosterSettings 移除单张海报的恒等设置，拒绝在单页绘制接口中静默丢弃分幅
// 入参: settings 有效设置, options 描述值的资源及取消参数
// 返回: *PrintSettings 单页设置视图, error 类型、能力或容量错误
func printSinglePosterSettings(settings *PrintSettings, options printSettingsConfig) (*PrintSettings, error) {
	present := false
	for _, element := range settings.Elements {
		if element.Kind == PrintSettingFeature && element.Name == (xml.Name{Space: printKeywordsNS, Local: "PagePoster"}) {
			present = true
			break
		}
	}
	if !present {
		return settings, nil
	}
	configuration, err := printSettingsOptions(options.context, &options.PrintSettingsOptions)
	if err != nil {
		return nil, err
	}
	control := newPrintLayoutSettings(settings, configuration)
	count, err := control.poster(int(^uint(0) >> 1))
	if err != nil {
		return nil, err
	}
	if count != 1 {
		return nil, fmt.Errorf("%w: multiple poster sheets require PrintPlan", ErrUnsupported)
	}
	result := &PrintSettings{Version: settings.Version}
	for _, element := range settings.Elements {
		if element.Kind != PrintSettingFeature || element.Name != (xml.Name{Space: printKeywordsNS, Local: "PagePoster"}) {
			result.Elements = append(result.Elements, element)
		}
	}
	return result, nil
}
