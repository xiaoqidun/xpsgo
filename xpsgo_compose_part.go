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
	"cmp"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"maps"
	"math"
	"net/url"
	"slices"
	"strconv"
	"strings"
)

// compositionFontReport 记录存在受限字体关系的原始文档集合
type compositionFontReport struct {
	restricted map[string]bool
}

// compositionFontMarkup 保存原始各已知分支的字体、字典和页面引用，不依据当前消费分支裁剪
type compositionFontMarkup struct {
	fonts        []Glyphs
	dictionaries []string
	pages        []string
	documents    []string
}

// compositionFontPage 区分同一页面部件在不同原始文档中的实际使用位置
type compositionFontPage struct {
	document string
	page     string
}

// compositionFontCheck 在单个只读快照内共享字体解混淆数据、字体面许可和标记解析结果
type compositionFontCheck struct {
	source    *compositionSource
	budget    *compositionBudget
	pkg       *packageReader
	markup    map[string]*compositionFontMarkup
	data      map[string][]byte
	faces     map[fontCacheKey]*fontOS2Metrics
	relations map[string]map[string]bool
}

// compositionLinkScope 保存原包中可寻址布局的范围，不随输出页序改变
type compositionLinkScope struct {
	kind  createdNavigationKind
	first int
	count int
}

// compositionDestination 保留原地址的确定身份，未知片段仍按原范围首页处理
type compositionDestination struct {
	part     string
	page     int
	name     string
	external bool
	scoped   bool
	uri      string
}

// compositionLinkIndex 缓存原包的首个命名声明，选页后不把已知或未知地址重新绑定到另一页面
type compositionLinkIndex struct {
	source *compositionSource
	scopes map[string]compositionLinkScope
	names  map[string]map[string]int
	budget *compositionBudget
}

// compositionMarkupOptions 提供原始布局标记的输出位置、名称映射及资源与导航改写回调
type compositionMarkupOptions struct {
	format      Format
	destination string
	owner       string
	names       map[string]string
	index       *compositionIndex
	resource    func(string) (string, error)
	navigation  func(string, string) (string, bool, error)
	budget      *compositionBudget
}

// compositionNames 保存各输出页面的元素名称映射及跨方言同源去重移除的LinkTarget集合
type compositionNames struct {
	pages          []map[string]string
	droppedTargets []map[string]bool
	budget         *compositionBudget
}

// compositionNameCollector 汇总原始页面和文档的名称，不过滤已知MCE分支
type compositionNameCollector struct {
	budget *compositionBudget
	format Format
	mce    compatibilityProcessor
	source *compositionSource
	retain bool
}

// compositionNamePage 保存一个页面的原名称集合及其禁止改名状态
type compositionNamePage struct {
	names map[string]bool
	fixed bool
}

// compositionNavigation 按源地址绑定及输出名称索引改写导航，不把缺失页面重绑到保留页
type compositionNavigation struct {
	plan    *compositionPlan
	pages   []map[string]string
	sources []*compositionLinkIndex
	output  *compositionLinkIndex
}

// compositionPrintText 保存Value字符数据在原XML的UTF-8视图中的范围
type compositionPrintText struct {
	start int
	end   int
}

// compositionProtectionGraph 复核快照中的原文硬依赖闭包
type compositionProtectionGraph struct {
	source *compositionSource
	budget *compositionBudget
	parts  map[string]bool
	queue  []string
	roots  map[string]bool
}

// validateCompositionFonts 预检组合涉及字体面的嵌入许可及文档受限关系，登记需整文档保留的受限文档
// 入参: source 独立源快照, budget 多源共享的扫描、工作和取消预算
// 返回: *compositionFontReport 需整文档保留的文档键，失败为nil, error 许可、闭包、能力或预算错误
func validateCompositionFonts(source *compositionSource, budget *compositionBudget) (*compositionFontReport, error) {
	if source == nil || budget == nil || formatNamespace(source.format) == "" {
		return nil, fmt.Errorf("%w: composition font input", ErrInvalid)
	}
	if len(source.parts) > budget.limits.MaxPartCount {
		return nil, fmt.Errorf("%w: composition font snapshot part count", ErrLimit)
	}
	if len(source.pages) > budget.limits.MaxPageCount || len(source.documents) > budget.limits.MaxPageCount {
		return nil, fmt.Errorf("%w: composition font source index", ErrLimit)
	}
	if err := budget.step(len(source.parts)); err != nil {
		return nil, err
	}
	c := &compositionFontCheck{source: source, budget: budget, pkg: &packageReader{parts: make(map[string][]*zip.File), names: make(map[string]string), data: make(map[string][]byte), defaults: make(map[string]string), overrides: make(map[string]string), limits: budget.limits}, markup: make(map[string]*compositionFontMarkup), data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontOS2Metrics), relations: make(map[string]map[string]bool)}
	selected := make(map[string]bool)
	pending := make(map[compositionFontPage]bool)
	for index, active := range source.selected {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if !active {
			continue
		}
		if index < 0 || index >= len(source.pages) {
			return nil, fmt.Errorf("%w: composition font page index", ErrInvalid)
		}
		part, err := c.part(source.pages[index].Part, fixedContentType("fixedpage"))
		if err != nil {
			return nil, err
		}
		selected[strings.ToLower(part.name)] = true
	}
	first := 0
	for _, document := range source.documents {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if len(document.Pages) > len(source.pages)-first {
			return nil, fmt.Errorf("%w: composition font document index", ErrInvalid)
		}
		for offset, page := range document.Pages {
			if err := budget.step(1); err != nil {
				return nil, err
			}
			if !strings.EqualFold(page.Part, source.pages[first+offset].Part) {
				return nil, fmt.Errorf("%w: composition font page owner index", ErrInvalid)
			}
			if source.selected[first+offset] {
				pending[compositionFontPage{strings.ToLower(document.Part), strings.ToLower(page.Part)}] = true
			}
		}
		first += len(document.Pages)
	}
	if first != len(source.pages) {
		return nil, fmt.Errorf("%w: incomplete composition font page index", ErrInvalid)
	}
	report := &compositionFontReport{restricted: make(map[string]bool)}
	owned := make(map[string]bool)
	auxiliaryOwned := make(map[string]bool)
	wholeDocuments := make(map[string]bool)
	auxiliaryDocuments := make(map[string]bool)
	for _, key := range slices.Sorted(maps.Keys(source.parts)) {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		part := source.parts[key]
		if !strings.EqualFold(part.media, fixedContentType("fixeddocumentsequence")) || !source.retained[key] && !source.auxiliary[key] {
			continue
		}
		refs, err := c.parse(part, false)
		if err != nil {
			return nil, err
		}
		for _, name := range refs.documents {
			document, err := c.part(name, fixedContentType("fixeddocument"))
			if err != nil {
				return nil, err
			}
			wholeDocuments[strings.ToLower(document.name)] = true
			if source.auxiliary[key] {
				auxiliaryDocuments[strings.ToLower(document.name)] = true
			}
		}
	}
	for _, key := range slices.Sorted(maps.Keys(source.parts)) {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		part := source.parts[key]
		if !strings.EqualFold(part.media, fixedContentType("fixeddocument")) {
			continue
		}
		part, err := c.part(part.name, fixedContentType("fixeddocument"))
		if err != nil {
			return nil, err
		}
		restricted, err := c.document(part)
		if err != nil {
			return nil, err
		}
		if len(restricted) != 0 {
			report.restricted[key] = true
		}
		whole := wholeDocuments[key] || source.retained[key] || source.auxiliary[key] || len(restricted) != 0
		refs, err := c.parse(part, whole)
		if err != nil {
			return nil, err
		}
		visited := make(map[string]bool)
		for _, name := range refs.pages {
			if err := budget.step(1); err != nil {
				return nil, err
			}
			pageKey := strings.ToLower(name)
			use := compositionFontPage{key, pageKey}
			if !whole && !pending[use] {
				continue
			}
			page, err := c.part(name, fixedContentType("fixedpage"))
			if err != nil {
				return nil, err
			}
			if err := c.page(page, restricted, visited); err != nil {
				return nil, &PartError{Part: part.name, Err: err}
			}
			owned[pageKey] = true
			delete(pending, use)
			if source.auxiliary[key] || auxiliaryDocuments[key] {
				auxiliaryOwned[pageKey] = true
			}
		}
	}
	for _, key := range slices.Sorted(maps.Keys(source.parts)) {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		part := source.parts[key]
		if !strings.EqualFold(part.media, fixedContentType("fixedpage")) {
			continue
		}
		if selected[key] && !owned[key] {
			return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: selected page lacks document closure", ErrInvalid)}
		}
		if !source.auxiliary[key] || auxiliaryOwned[key] {
			if !source.retained[key] || owned[key] {
				continue
			}
		}
		if err := c.page(part, nil, make(map[string]bool)); err != nil {
			return nil, err
		}
	}
	if len(pending) != 0 {
		return nil, fmt.Errorf("%w: selected page lacks original document context", ErrInvalid)
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return report, nil
}

// part 复核快照部件的身份和类型，不读取外部资源或修改原始字节
// 入参: name 包内部件URI, media 预期媒体类型，空值不限
// 返回: packagePart 原始部件, error 闭包、类型或预算错误
func (c *compositionFontCheck) part(name, media string) (packagePart, error) {
	if err := c.budget.step(1); err != nil {
		return packagePart{}, err
	}
	if err := c.budget.scan(int64(len(name))); err != nil {
		return packagePart{}, err
	}
	canonical, err := opcPartName(name)
	if err != nil {
		return packagePart{}, err
	}
	part, present := c.source.parts[strings.ToLower(canonical)]
	if !present || !strings.EqualFold(part.name, canonical) || part.media == "" {
		return packagePart{}, &PartError{Part: name, Err: fmt.Errorf("%w: missing composition font dependency", ErrInvalid)}
	}
	if media != "" && !strings.EqualFold(part.media, media) {
		return packagePart{}, &PartError{Part: name, Err: fmt.Errorf("%w: composition font dependency type", ErrInvalid)}
	}
	if int64(len(part.data)) > c.budget.limits.MaxPartBytes {
		return packagePart{}, fmt.Errorf("%w: composition font part bytes", ErrLimit)
	}
	return part, nil
}

// parse 按原始标记展开全部已知分支，字典和VisualBrush中的Glyphs采用其定义部件解析字体URI
// 入参: part 页面、文档、文档序列或远程字典, whole 是否要求完整文档的潜在闭包
// 返回: *compositionFontMarkup 只读引用缓存, error 标记、闭包、能力或预算错误
func (c *compositionFontCheck) parse(part packagePart, whole bool) (*compositionFontMarkup, error) {
	key := strings.ToLower(part.name)
	retain := c.source.retained[key] || c.source.auxiliary[key] || whole
	cacheKey := key
	if retain {
		cacheKey += "\x00retained"
	}
	if result := c.markup[cacheKey]; result != nil {
		return result, c.budget.step(0)
	}
	var index *compositionIndex
	var indexRoot *xmlElement
	if compositionIndexRoot(part.media) != "" {
		var err error
		index, err = c.source.indexPart(part, c.budget)
		if err != nil {
			return nil, err
		}
		if err := index.inspect(retain, c.budget); err != nil {
			return nil, err
		}
		indexRoot = index.active
		if retain {
			indexRoot = index.raw
		}
	}
	if int64(len(part.data)) > c.budget.limits.MaxPartBytes {
		return nil, fmt.Errorf("%w: composition font markup bytes", ErrLimit)
	}
	if index == nil {
		if err := c.budget.scan(int64(len(part.data))); err != nil {
			return nil, err
		}
	}
	result := &compositionFontMarkup{}
	tracker := newResourceMarkupScopeTracker(c.source.format, c.source.format == FormatOpenXPS, c.budget.context)
	visit := func(token xml.Token, node *xmlElement) error {
		if err := c.budget.step(1); err != nil {
			return err
		}
		if index == nil {
			skip, _, err := tracker.visit(token, node)
			if err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if err := c.budget.step(len(node.Attr)); err != nil {
				return err
			}
			if skip {
				return nil
			}
		} else {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if node.Name.Space == mcNamespace && !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
				return fmt.Errorf("%w: composition font compatibility element", ErrUnsupported)
			}
			if err := c.budget.step(len(node.Attr)); err != nil {
				return err
			}
		}
		for _, attr := range node.Attr {
			if attr.Name.Space == mcNamespace && !slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attr.Name.Local) {
				return fmt.Errorf("%w: composition font compatibility attribute", ErrUnsupported)
			}
			if err := c.budget.scan(int64(len(attr.Value))); err != nil {
				return err
			}
		}
		if node.Name.Space != formatNamespace(c.source.format) {
			return nil
		}
		switch node.Name.Local {
		case "Glyphs":
			value, present := node.attribute("FontUri")
			if !present {
				return fmt.Errorf("%w: composition glyph font URI", ErrInvalid)
			}
			uri, face, present, err := ParseFontURI(strings.Trim(value, " \t\r\n"))
			if err != nil {
				return err
			}
			name, err := resolvePart(part.name, uri)
			if err != nil {
				return err
			}
			result.fonts = append(result.fonts, Glyphs{FontPart: name, CollectionIndex: face, HasCollectionIndex: present})
		case "PageContent", "DocumentReference", "ResourceDictionary":
			uri, present := node.attribute("Source")
			if !present && node.Name.Local == "ResourceDictionary" {
				return nil
			}
			if !present || strings.TrimSpace(uri) == "" {
				return fmt.Errorf("%w: composition font markup Source", ErrInvalid)
			}
			name, err := resolvePart(part.name, uri)
			if err != nil {
				return err
			}
			if node.Name.Local == "PageContent" {
				result.pages = append(result.pages, name)
			} else if node.Name.Local == "DocumentReference" {
				result.documents = append(result.documents, name)
			} else {
				result.dictionaries = append(result.dictionaries, name)
			}
		}
		return nil
	}
	var root *xmlElement
	var err error
	if index != nil {
		err = index.visit(indexRoot, visit)
		root = index.active
	} else {
		root, err = decodeXMLVisit(part.data, c.budget.limits, visit)
	}
	if err != nil {
		return nil, &PartError{Part: part.name, Err: err}
	}
	expected := "ResourceDictionary"
	if strings.EqualFold(part.media, fixedContentType("fixedpage")) {
		expected = "FixedPage"
	} else if strings.EqualFold(part.media, fixedContentType("fixeddocument")) {
		expected = "FixedDocument"
	} else if strings.EqualFold(part.media, fixedContentType("fixeddocumentsequence")) {
		expected = "FixedDocumentSequence"
	}
	if root.Name != (xml.Name{Space: formatNamespace(c.source.format), Local: expected}) {
		return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: composition font markup root", ErrInvalid)}
	}
	c.markup[cacheKey] = result
	return result, nil
}

// document 从原始关系各已知分支提取当前文档的受限字体部件集合
// 入参: document 文档部件
// 返回: map[string]bool 受限字体部件键, error 关系、闭包、能力或预算错误
func (c *compositionFontCheck) document(document packagePart) (map[string]bool, error) {
	key := strings.ToLower(document.name)
	if result, present := c.relations[key]; present {
		return result, c.budget.step(0)
	}
	result := make(map[string]bool)
	name := createdRelationshipPart(document.name)
	part, present := c.source.parts[strings.ToLower(name)]
	if !present {
		if _, indexed := c.source.relationships[key]; indexed || c.source.restricted[key] {
			return nil, &PartError{Part: name, Err: fmt.Errorf("%w: missing composition font relationships", ErrInvalid)}
		}
		c.relations[key] = result
		return result, nil
	}
	part, err := c.part(name, opcRelsType)
	if err != nil {
		return nil, err
	}
	if int64(len(part.data)) > c.budget.limits.MaxMetadataBytes {
		return nil, fmt.Errorf("%w: composition font relationship bytes", ErrLimit)
	}
	if err := c.budget.scan(int64(len(part.data))); err != nil {
		return nil, err
	}
	root, err := decodeXMLVisit(part.data, c.budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := c.budget.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := resourceRelationshipNode(node); err != nil {
			return err
		}
		if err := c.budget.step(len(node.Attr)); err != nil {
			return err
		}
		for _, attr := range node.Attr {
			if err := c.budget.scan(int64(len(attr.Value))); err != nil {
				return err
			}
		}
		if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
			return nil
		}
		attrs, err := opcMetadataAttributes(node, opcRelsNS)
		if err != nil {
			return err
		}
		relation, err := parseRelationship(document.name, xml.StartElement{Name: node.Name, Attr: node.Attr}, attrs, make(map[string]bool))
		if err != nil || relation.Type != formatNamespace(c.source.format)+"/restricted-font" {
			return err
		}
		if relation.TargetMode != TargetModeInternal {
			return fmt.Errorf("%w: external composition restricted font", ErrInvalid)
		}
		target, err := resolvePart(document.name, relation.Target)
		if err != nil {
			return err
		}
		font, err := c.part(target, "")
		if err != nil {
			return err
		}
		if !requiredResourceMedia(requiredFont, font.media) {
			return fmt.Errorf("%w: composition restricted font content type", ErrInvalid)
		}
		result[strings.ToLower(target)] = true
		return nil
	})
	if err != nil {
		return nil, &PartError{Part: name, Err: err}
	}
	if root.Name != (xml.Name{Space: opcRelsNS, Local: "Relationships"}) {
		return nil, fmt.Errorf("%w: composition font relationship root", ErrInvalid)
	}
	c.relations[key] = result
	return result, nil
}

// page 按文档归属遍历页面及远程字典，校验全部使用字体面的嵌入许可
// 入参: page 页面部件, restricted 所属文档的受限字体，nil表示无文档归属, visited 当前文档已检查的标记
// 返回: error 字体许可、资源闭包、能力或预算错误
func (c *compositionFontCheck) page(page packagePart, restricted map[string]bool, visited map[string]bool) error {
	queue := []packagePart{page}
	for position := 0; position < len(queue); position++ {
		if err := c.budget.step(1); err != nil {
			return err
		}
		part := queue[position]
		key := strings.ToLower(part.name)
		if visited[key] {
			continue
		}
		visited[key] = true
		refs, err := c.parse(part, false)
		if err != nil {
			return err
		}
		for _, glyphs := range refs.fonts {
			if err := c.budget.step(1); err != nil {
				return err
			}
			metrics, err := c.font(glyphs)
			if err != nil {
				return err
			}
			if metrics.fsType&4 != 0 && restricted == nil {
				return &PartError{Part: page.name, Err: fmt.Errorf("%w: preview and print auxiliary page lacks document context", ErrUnsupported)}
			}
			if metrics.fsType&4 != 0 && !restricted[strings.ToLower(glyphs.FontPart)] {
				return &PartError{Part: glyphs.FontPart, Err: fmt.Errorf("%w: preview and print font lacks document restricted font relationship", ErrRestricted)}
			}
		}
		for _, name := range refs.dictionaries {
			part, err := c.part(name, resourceDictionaryContentType)
			if err != nil {
				return err
			}
			if !visited[strings.ToLower(part.name)] {
				queue = append(queue, part)
			}
		}
	}
	return nil
}

// font 检查实际使用字体面的生产者嵌入许可，复用已解混淆字体数据与集合字体面缓存
// 入参: glyphs 已解析的字体部件和集合索引
// 返回: *fontOS2Metrics 原始许可位, error 封装、许可、能力或预算错误
func (c *compositionFontCheck) font(glyphs Glyphs) (*fontOS2Metrics, error) {
	key := fontCacheKey{part: strings.ToLower(glyphs.FontPart), index: glyphs.CollectionIndex}
	if metrics := c.faces[key]; metrics != nil {
		return metrics, c.budget.step(0)
	}
	if len(c.faces) >= c.budget.limits.MaxPartCount {
		return nil, fmt.Errorf("%w: composition font face count", ErrLimit)
	}
	part, err := c.part(glyphs.FontPart, "")
	if err != nil {
		return nil, err
	}
	if !requiredResourceMedia(requiredFont, part.media) {
		return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: composition font content type", ErrInvalid)}
	}
	var face *fontFace
	if data, present := c.data[key.part]; present {
		face, err = parseFontFace(data, key.index)
	} else {
		if err := c.budget.scan(int64(len(part.data))); err != nil {
			return nil, err
		}
		createdPut(c.pkg, part.name, part.media, part.data)
		face, err = c.pkg.readFontFaceLimit(part.name, key.index, c.budget.limits.MaxPartBytes)
		if err == nil {
			c.data[key.part] = face.data
		}
	}
	if err != nil {
		return nil, err
	}
	if err := c.budget.step(len(face.tables)); err != nil {
		return nil, err
	}
	if _, present := face.tables["OS/2"]; !present {
		return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: composition font lacks embedding rights", ErrUnsupported)}
	}
	metrics, err := parseFontOS2Metrics(face)
	if err != nil {
		return nil, &PartError{Part: part.name, Err: err}
	}
	rights, err := fontEmbeddingRights(metrics)
	if err != nil {
		return nil, &PartError{Part: part.name, Err: err}
	}
	if rights&2 != 0 {
		return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: composition font embedding requires owner permission", ErrRestricted)}
	}
	if rights&0x30c != 0 && !strings.EqualFold(part.media, "application/vnd.ms-package.obfuscated-opentype") {
		return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: composition font requires obfuscation", ErrRestricted)}
	}
	if rights&0x200 != 0 {
		_, outlines := face.tables["glyf"]
		if outlines || face.cff {
			return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: bitmap-only composition font contains outlines", ErrRestricted)}
		}
		maxp, err := fontMetricsTable(face, "maxp", 6)
		if err != nil {
			return nil, &PartError{Part: part.name, Err: err}
		}
		bitmaps, err := parseFontBitmapsWithWork(face, uint32(binary.BigEndian.Uint16(maxp[4:])), func(work uint64) error {
			if work > uint64(c.budget.work) {
				return fmt.Errorf("%w: composition font bitmap work", ErrLimit)
			}
			return c.budget.step(int(work))
		})
		if err != nil {
			return nil, &PartError{Part: part.name, Err: err}
		}
		characters := false
		if bitmaps != nil {
			for _, strike := range bitmaps.strikes {
				characters = characters || len(strike.entries) != 0
			}
		}
		if !characters {
			return nil, &PartError{Part: part.name, Err: fmt.Errorf("%w: bitmap-only composition font lacks bitmaps", ErrRestricted)}
		}
	}
	if err := c.budget.step(0); err != nil {
		return nil, err
	}
	c.faces[key] = metrics
	return metrics, nil
}

// newCompositionLinkIndex 建立原序列、文档和页面的地址范围，不读取字形或改变源标记
// 入参: source 独立源快照, budget 累计预算
// 返回: *compositionLinkIndex 原始地址索引，失败为nil, error 源结构、预算或取消错误
func newCompositionLinkIndex(source *compositionSource, budget *compositionBudget) (*compositionLinkIndex, error) {
	if source == nil || budget == nil {
		return nil, fmt.Errorf("%w: incomplete composition link source", ErrInvalid)
	}
	boundaries, err := newCompositionSourceIndex(source, budget)
	if err != nil {
		return nil, err
	}
	result := &compositionLinkIndex{source: source, scopes: make(map[string]compositionLinkScope), names: make(map[string]map[string]int), budget: budget}
	add := func(part string, scope compositionLinkScope) error {
		if err := budget.step(1); err != nil {
			return err
		}
		name, err := opcPartName(part)
		if err != nil {
			return err
		}
		key := strings.ToLower(name)
		if _, exists := result.scopes[key]; exists {
			return fmt.Errorf("%w: duplicate composition layout identity", ErrInvalid)
		}
		result.scopes[key] = scope
		return nil
	}
	if err := add(source.sequence, compositionLinkScope{kind: createdNavigationSequence, count: len(source.pages)}); err != nil {
		return nil, err
	}
	for index, document := range source.documents {
		if err := add(document.Part, compositionLinkScope{kind: createdNavigationDocument, first: boundaries.starts[index], count: len(document.Pages)}); err != nil {
			return nil, err
		}
		for position, page := range document.Pages {
			global := boundaries.starts[index] + position
			if !strings.EqualFold(page.Part, source.pages[global].Part) {
				return nil, fmt.Errorf("%w: inconsistent composition link index", ErrInvalid)
			}
			if err := add(page.Part, compositionLinkScope{kind: createdNavigationPage, first: global, count: 1}); err != nil {
				return nil, err
			}
		}
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return result, nil
}

// resolve 按原包身份绑定导航链接，解析序列数字片段、文档命名片段及非布局资源身份
// 入参: source 原始地址基准，字典导航由调用方传入所属页面, target 原始URI声明
// 返回: compositionDestination 已绑定地址, error URI、源身份、地址作用域、预算或取消错误
func (c *compositionLinkIndex) resolve(source, target string) (result compositionDestination, err error) {
	if err := c.budget.step(1); err != nil {
		return compositionDestination{}, err
	}
	defer func() {
		if err == nil {
			if late := c.budget.step(0); late != nil {
				result, err = compositionDestination{}, late
			}
		}
	}()
	if err := c.budget.scan(int64(len(source))); err != nil {
		return compositionDestination{}, err
	}
	if err := c.budget.scan(int64(len(target))); err != nil {
		return compositionDestination{}, err
	}
	base, err := opcPartName(source)
	if err != nil {
		return compositionDestination{}, err
	}
	baseKey := strings.ToLower(base)
	if _, layout := c.scopes[baseKey]; !layout {
		if _, exists := c.source.parts[baseKey]; !exists {
			return compositionDestination{}, fmt.Errorf("%w: composition link source is absent", ErrInvalid)
		}
	}
	value := structureURI(target)
	result = compositionDestination{page: -1, uri: value}
	if linkExternal(value) {
		result.external = true
		return result, nil
	}
	uri, err := url.Parse(value)
	if err != nil {
		return compositionDestination{}, fmt.Errorf("%w: composition navigation URI", ErrInvalid)
	}
	if uri.RawQuery != "" || uri.ForceQuery {
		return compositionDestination{}, fmt.Errorf("%w: query in composition navigation", ErrUnsupported)
	}
	part := base
	if uri.Path != "" {
		part, err = resolvePart(base, uri.EscapedPath())
		if err != nil {
			return compositionDestination{}, err
		}
	}
	result.part = part
	key := strings.ToLower(part)
	scope, exists := c.scopes[key]
	if !exists {
		part, exists := c.source.parts[key]
		if !exists {
			return compositionDestination{}, fmt.Errorf("%w: composition link target is absent", ErrInvalid)
		}
		if err := validateLinkFragment(part.media, uri.Fragment, false); err != nil {
			return compositionDestination{}, err
		}
		return result, nil
	}
	result.scoped = true
	if scope.count == 0 {
		media := fixedContentType("fixeddocument")
		if scope.kind == createdNavigationSequence {
			media = fixedContentType("fixeddocumentsequence")
		} else if scope.kind == createdNavigationPage {
			media = fixedContentType("fixedpage")
		}
		if err := validateLinkFragment(media, uri.Fragment, true); err != nil {
			return compositionDestination{}, err
		}
		return result, nil
	}
	result.page = scope.first
	if uri.Fragment == "" {
		return result, nil
	}
	if linkPageNumber(uri.Fragment) {
		if scope.kind != createdNavigationSequence {
			return compositionDestination{}, fmt.Errorf("%w: M9.8 composition page address must target the fixed document sequence", ErrInvalid)
		}
		number, err := strconv.ParseUint(uri.Fragment, 10, 64)
		if err == nil && number > 0 && number <= uint64(len(c.source.pages)) {
			result.page = int(number) - 1
		}
		return result, nil
	}
	if scope.kind == createdNavigationPage {
		return compositionDestination{}, fmt.Errorf("%w: M9.4 composition named address must target a fixed document or sequence", ErrInvalid)
	}
	page, declared, err := c.named(key, uri.Fragment, scope)
	if err != nil {
		return compositionDestination{}, err
	}
	result.page = page
	if declared {
		result.name = uri.Fragment
	}
	return result, nil
}

// named 缓存每个原始范围内首个声明，不按输出顺序或实际字形名称改变声明优先级
// 入参: key 原范围部件的小写URI, name 已解码的命名片段, scope 原始页面范围
// 返回: int 原包全局页号, bool 名称是否声明, error 预算或取消错误
func (c *compositionLinkIndex) named(key, name string, scope compositionLinkScope) (int, bool, error) {
	index, exists := c.names[key]
	if !exists {
		index = make(map[string]int)
		for page := scope.first; page < scope.first+scope.count; page++ {
			if err := c.budget.step(1); err != nil {
				return 0, false, err
			}
			for _, declared := range c.source.pages[page].LinkTargets {
				if err := c.budget.step(1); err != nil {
					return 0, false, err
				}
				if _, present := index[declared]; !present {
					index[declared] = page
				}
			}
		}
		if err := c.budget.step(0); err != nil {
			return 0, false, err
		}
		c.names[key] = index
	}
	if page, declared := index[name]; declared {
		return page, true, nil
	}
	return scope.first, false, nil
}

// rewriteCompositionMarkup 改写固定布局和资源字典属性，保留已知兼容分支与原始编码，不修改源部件
// 入参: value 原部件, options 输出配置与共享预算
// 返回: []byte 独立的原编码结果，失败为nil, error XML、引用、支持范围、预算或取消错误
func rewriteCompositionMarkup(value packagePart, options compositionMarkupOptions) ([]byte, error) {
	if options.format != FormatXPS && options.format != FormatOpenXPS {
		return nil, fmt.Errorf("%w: composition markup options", ErrInvalid)
	}
	budget := options.budget
	if err := budget.step(1); err != nil {
		return nil, err
	}
	maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
	if int64(len(value.data)) > maximum {
		return nil, fmt.Errorf("%w: composition markup input size", ErrLimit)
	}
	for _, uri := range []string{value.name, options.destination, options.owner} {
		if err := budget.scan(int64(len(uri))); err != nil {
			return nil, err
		}
	}
	source, err := opcPartName(value.name)
	if err != nil {
		return nil, err
	}
	destination, err := opcPartName(options.destination)
	if err != nil {
		return nil, err
	}
	owner := options.owner
	if owner != "" {
		owner, err = opcPartName(owner)
		if err != nil {
			return nil, err
		}
	}
	local := ""
	for _, kind := range []struct{ media, root string }{
		{fixedContentType("fixedpage"), "FixedPage"},
		{fixedContentType("fixeddocument"), "FixedDocument"},
		{fixedContentType("fixeddocumentsequence"), "FixedDocumentSequence"},
		{resourceDictionaryContentType, "ResourceDictionary"},
	} {
		if strings.EqualFold(value.media, kind.media) {
			local = kind.root
			break
		}
	}
	if local == "" {
		return nil, fmt.Errorf("%w: composition markup content type %q", ErrUnsupported, value.media)
	}
	namespace := formatNamespace(options.format)
	var processed *xmlElement
	if compositionIndexRoot(value.media) != "" {
		index := options.index
		if index != nil && !index.matches(value, options.format) {
			return nil, fmt.Errorf("%w: composition index source mismatch", ErrInvalid)
		}
		if index == nil || budget.limits.MaxXMLNodes < index.limits.MaxXMLNodes || budget.limits.MaxXMLDepth < index.limits.MaxXMLDepth || budget.limits.MaxXMLBindings < index.limits.MaxXMLBindings {
			index, err = newCompositionIndex(value, options.format, budget)
			if err != nil {
				return nil, err
			}
		}
		if err := index.inspect(true, budget); err != nil {
			return nil, err
		}
		processed = index.active
	} else {
		if options.index != nil {
			return nil, fmt.Errorf("%w: composition index proof for non-index markup", ErrInvalid)
		}
		if err := budget.scan(int64(len(value.data))); err != nil {
			return nil, err
		}
		tracker := newResourceMarkupScopeTracker(options.format, options.format == FormatOpenXPS, budget.context)
		root, err := decodeXMLVisit(value.data, budget.limits, func(token xml.Token, node *xmlElement) error {
			if err := budget.step(1); err != nil {
				return err
			}
			skip, scope, err := tracker.visit(token, node)
			if err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			if skip {
				return nil
			}
			if node.Name.Space == structureNamespace(options.format) || node.Name.Space == mcNamespace && !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
				return fmt.Errorf("%w: composition markup element %s", ErrUnsupported, node.Name.Local)
			}
			if err := budget.step(len(node.Attr)); err != nil {
				return err
			}
			if options.format == FormatOpenXPS && node.Name.Space == openXPS3DNamespace {
				return nil
			}
			for _, attr := range node.Attr {
				if attr.Name.Space != "" && scope.ignorable[attr.Name.Space] {
					continue
				}
				if !compositionMarkupAttribute(node, attr, options.format) {
					return fmt.Errorf("%w: composition markup attribute {%s}%s", ErrUnsupported, attr.Name.Space, attr.Name.Local)
				}
			}
			return nil
		})
		if err != nil {
			return nil, err
		}
		processed, err = preprocessXMLContext(root, []string{namespace, namespace + "/resourcedictionary-key"}, budget.context)
		if err != nil {
			return nil, err
		}
	}
	if processed.Name != (xml.Name{Space: namespace, Local: local}) {
		return nil, fmt.Errorf("%w: composition markup root", ErrInvalid)
	}
	aliases := make(map[string]string)
	resolve := func(uri string) (string, error) {
		if err := budget.step(1); err != nil {
			return "", err
		}
		if err := budget.scan(int64(len(uri))); err != nil {
			return "", err
		}
		part, err := resolvePart(source, uri)
		if err != nil {
			return "", err
		}
		key := strings.ToLower(part)
		if target, present := aliases[key]; present {
			return target, nil
		}
		if options.resource == nil {
			return "", fmt.Errorf("%w: missing composition resource callback", ErrInvalid)
		}
		target, err := options.resource(part)
		if err != nil {
			return "", err
		}
		if err := budget.scan(int64(len(target))); err != nil {
			return "", err
		}
		if int64(len(target)) > maximum {
			return "", fmt.Errorf("%w: composition resource mapping size", ErrLimit)
		}
		target, err = opcPartName(target)
		if err != nil {
			return "", err
		}
		if err := budget.step(0); err != nil {
			return "", err
		}
		aliases[key] = target
		return target, nil
	}
	collector := newCompositionNameCollector(options.format, budget)
	if err := budget.scan(int64(len(value.data))); err != nil {
		return nil, err
	}
	var rewriteTracker *resourceMarkupScopeTracker
	if compositionIndexRoot(value.media) != "" {
		rewriteTracker = newResourceMarkupIgnoreTracker(options.format, options.format == FormatOpenXPS, budget.context)
	} else {
		rewriteTracker = newResourceMarkupScopeTracker(options.format, options.format == FormatOpenXPS, budget.context)
	}
	return rewriteExtractMarkup(value.data, budget.limits, budget.context, func(token xml.Token, node *xmlElement) (bool, error) {
		skip, _, err := rewriteTracker.visit(token, node)
		return skip, err
	}, func(node *xmlElement, attr xml.Attr) (string, bool, error) {
		if err := budget.step(1); err != nil {
			return "", false, err
		}
		if err := budget.scan(int64(len(attr.Value))); err != nil {
			return "", false, err
		}
		isModel := options.format == FormatOpenXPS && node.Name.Space == openXPS3DNamespace
		if (node.Name.Space != namespace && !isModel) || attr.Name.Space != "" {
			return attr.Value, false, nil
		}
		if attr.Name.Local == "Name" && slices.Contains([]string{"FixedPage", "Canvas", "Path", "Glyphs"}, node.Name.Local) {
			name, err := collector.name(attr.Value, false)
			if err != nil || options.names == nil {
				return attr.Value, false, err
			}
			target, present := options.names[name]
			if !present {
				return "", false, fmt.Errorf("%w: composition Name mapping for %q", ErrInvalid, name)
			}
			normalized, err := collector.name(target, false)
			if err != nil || normalized != target {
				if err == nil {
					err = fmt.Errorf("%w: noncanonical composition Name mapping", ErrInvalid)
				}
				return "", false, err
			}
			return target, name != target, nil
		}
		if resourceIdentityAttribute(node, attr, options.format) {
			base := source
			if local == "ResourceDictionary" {
				base = owner
				if base == "" {
					if !linkExternal(structureURI(attr.Value)) {
						return "", false, fmt.Errorf("%w: composition dictionary navigation owner", ErrUnsupported)
					}
					base = source
				}
			}
			if options.navigation == nil {
				return "", false, fmt.Errorf("%w: missing composition navigation callback", ErrInvalid)
			}
			target, changed, err := options.navigation(base, attr.Value)
			if err != nil {
				return "", false, err
			}
			if err := budget.scan(int64(len(target))); err != nil {
				return "", false, err
			}
			if err := budget.step(0); err != nil {
				return "", false, err
			}
			return target, changed, nil
		}
		if attr.Name.Local == "Source" && (node.Name.Local == "PageContent" || node.Name.Local == "DocumentReference") {
			if node.Name.Local == "PageContent" && local != "FixedDocument" || node.Name.Local == "DocumentReference" && local != "FixedDocumentSequence" {
				return "", false, fmt.Errorf("%w: composition layout reference outside its index", ErrUnsupported)
			}
			target, err := resolve(attr.Value)
			if err != nil {
				return "", false, err
			}
			original, err := resolvePart(destination, attr.Value)
			if err == nil && strings.EqualFold(original, target) {
				return attr.Value, false, nil
			}
			target, err = relativePart(destination, target)
			if err != nil {
				return "", false, err
			}
			if int64(len(target)) > maximum {
				return "", false, fmt.Errorf("%w: composition layout reference size", ErrLimit)
			}
			if err := budget.scan(int64(len(target))); err != nil {
				return "", false, err
			}
			return target, target != attr.Value, nil
		}
		references, err := resourceAttributeReferences(node, attr)
		if err != nil {
			return "", false, err
		}
		for _, reference := range references {
			if _, err := resolve(reference.uri); err != nil {
				return "", false, err
			}
		}
		if len(references) == 0 {
			return attr.Value, false, nil
		}
		return compositionResourceAttribute(source, destination, node, attr, aliases, budget, false)
	})
}

// compositionMarkupAttribute 识别布局结构和资源属性，不把未知属性中的潜在引用当作普通文字
// 入参: node 所属元素, attribute 原属性, format 文档格式
// 返回: bool 是否已理解属性的引用语义
func compositionMarkupAttribute(node *xmlElement, attribute xml.Attr, format Format) bool {
	if dictionaryKnownAttribute(node, attribute, format) {
		return true
	}
	if node.Name.Space != formatNamespace(format) || attribute.Name.Space != "" {
		return false
	}
	switch node.Name.Local {
	case "FixedPage":
		return slices.Contains([]string{"Width", "Height", "ContentBox", "BleedBox", "Name"}, attribute.Name.Local)
	case "DocumentReference":
		return attribute.Name.Local == "Source"
	case "PageContent":
		return slices.Contains([]string{"Source", "Width", "Height"}, attribute.Name.Local)
	case "LinkTarget":
		return attribute.Name.Local == "Name"
	}
	return false
}

// newCompositionNames 协调同一输出文档中的元素名称，优先保留受保护原件再处理名称冲突
// 入参: plan 已建立页面身份和保护范围的组合规划
// 返回: *compositionNames 独立映射，失败为nil, error 名称、许可、预算或取消错误
func newCompositionNames(plan *compositionPlan) (*compositionNames, error) {
	if plan == nil || plan.budget == nil || formatNamespace(plan.format) == "" {
		return nil, fmt.Errorf("%w: incomplete composition name plan", ErrInvalid)
	}
	b := plan.budget
	if err := b.step(0); err != nil {
		return nil, err
	}
	if len(plan.pages) > b.limits.MaxPageCount {
		return nil, fmt.Errorf("%w: composition name page count", ErrLimit)
	}
	if err := b.step(len(plan.pages)); err != nil {
		return nil, err
	}
	result := &compositionNames{pages: make([]map[string]string, len(plan.pages)), droppedTargets: make([]map[string]bool, len(plan.pages)), budget: b}
	pages := make([]compositionNamePage, len(plan.pages))
	visualNames := make([]map[string]bool, len(plan.pages))
	pageOwners := make([]int, len(plan.pages))
	pageCache := make(map[compositionPartKey]map[string]bool)
	visualCache := make(map[compositionPartKey]map[string]bool)
	documentCache := make(map[compositionPartKey]map[string]map[string]bool)
	for index, instance := range plan.pages {
		if err := b.step(1); err != nil {
			return nil, err
		}
		if instance.source < 0 || instance.source >= len(plan.sources) || plan.sources[instance.source] == nil || instance.document < 0 || instance.document >= len(plan.documents) {
			return nil, fmt.Errorf("%w: composition name page identity", ErrInvalid)
		}
		source := plan.sources[instance.source]
		if instance.index < 0 || instance.index >= len(source.pages) || formatNamespace(source.format) == "" || instance.source >= len(plan.indices) || plan.indices[instance.source] == nil {
			return nil, fmt.Errorf("%w: composition name source identity", ErrInvalid)
		}
		owner, _, err := plan.documentPage(instance.source, instance.index)
		if err != nil {
			return nil, err
		}
		pageOwners[index] = owner
		original := source.pages[instance.index]
		output := plan.documents[instance.document]
		sameDialect := source.sourceFormat == FormatUnknown || source.sourceFormat == plan.format
		retain := output.complete && output.source == instance.source && output.original == owner && source.format == plan.format && sameDialect
		pageKey := compositionPartKey{source: instance.source, part: strings.ToLower(original.Part), page: instance.index, document: -1}
		if retain {
			pageKey.document = owner
		}
		names, exists := pageCache[pageKey]
		if !exists {
			collector := newCompositionNameCollector(source.format, b)
			collector.source = source
			collector.retain = retain
			documentKey := compositionPartKey{source: instance.source, part: strings.ToLower(source.documents[owner].Part), document: -1, page: -1}
			if !collector.retain {
				documentKey.page = 0
			}
			targets, exists := documentCache[documentKey]
			if !exists {
				part, exists := source.parts[documentKey.part]
				if !exists {
					return nil, fmt.Errorf("%w: composition name document is absent", ErrInvalid)
				}
				targets, err = collector.document(part)
				if err != nil {
					return nil, &PartError{Part: part.name, Err: err}
				}
				documentCache[documentKey] = targets
			}
			part, exists := source.parts[strings.ToLower(original.Part)]
			if !exists {
				return nil, fmt.Errorf("%w: composition name page is absent", ErrInvalid)
			}
			pageOnly, err := collector.page(part)
			if err != nil {
				return nil, &PartError{Part: part.name, Err: err}
			}
			visualCache[pageKey] = pageOnly
			names = maps.Clone(pageOnly)
			for name := range targets[strings.ToLower(original.Part)] {
				if err := b.step(1); err != nil {
					return nil, err
				}
				names[name] = true
			}
			for _, name := range original.LinkTargets {
				value, err := collector.name(name, true)
				if err != nil {
					return nil, err
				}
				names[value] = true
			}
			pageCache[pageKey] = names
		}
		visualNames[index] = visualCache[pageKey]
		fixed := false
		for _, part := range []string{original.Part, source.documents[owner].Part, source.sequence} {
			if err := b.step(1); err != nil {
				return nil, err
			}
			_, protected := plan.fixed[compositionPartKey{source: instance.source, part: strings.ToLower(part), document: -1, page: -1}]
			fixed = fixed || protected
		}
		pages[index] = compositionNamePage{names: maps.Clone(names), fixed: fixed}
	}
	visited := make([]bool, len(plan.pages))
	for document, instance := range plan.documents {
		preserve := false
		if instance.complete && instance.source >= 0 && instance.source < len(plan.sources) && instance.original >= 0 && instance.original < len(plan.sources[instance.source].documents) {
			source := plan.sources[instance.source]
			part := strings.ToLower(source.documents[instance.original].Part)
			_, preserve = plan.fixed[compositionPartKey{source: instance.source, part: part, document: -1, page: -1}]
			preserve = preserve || source.retained[part]
			sameDialect := source.sourceFormat == FormatUnknown || source.sourceFormat == plan.format
			preserve = preserve && source.format == plan.format && sameDialect
		}
		if plan.format == FormatXPS {
			type originTargetKey struct {
				source   int
				origDoc  int
				targetID string
			}
			firstOrigPage := make(map[originTargetKey]int)
			for _, page := range instance.pages {
				pi := plan.pages[page]
				src := plan.sources[pi.source]
				if src.sourceFormat != FormatOpenXPS {
					continue
				}
				for _, targetName := range pi.reference.LinkTargets {
					k := originTargetKey{source: pi.source, origDoc: pageOwners[page], targetID: targetName}
					if prev, ok := firstOrigPage[k]; !ok || pi.index < prev {
						firstOrigPage[k] = pi.index
					}
				}
			}
			for _, page := range instance.pages {
				pi := plan.pages[page]
				src := plan.sources[pi.source]
				if src.sourceFormat != FormatOpenXPS {
					continue
				}
				for _, targetName := range pi.reference.LinkTargets {
					k := originTargetKey{source: pi.source, origDoc: pageOwners[page], targetID: targetName}
					if minIdx, ok := firstOrigPage[k]; ok && pi.index > minIdx {
						if result.droppedTargets[page] == nil {
							result.droppedTargets[page] = make(map[string]bool)
						}
						result.droppedTargets[page][targetName] = true
						if !visualNames[page][targetName] {
							delete(pages[page].names, targetName)
						}
					}
				}
			}
		}
		if err := result.document(plan.format, document, instance.pages, pages, plan.pages, visited, preserve); err != nil {
			return nil, err
		}
	}
	for _, present := range visited {
		if !present {
			return nil, fmt.Errorf("%w: unassigned composition name page", ErrInvalid)
		}
	}
	if err := b.step(0); err != nil {
		return nil, err
	}
	return result, nil
}

// target 查询已收集的原名称，不推断缺失地址，也不验证LinkTarget的可寻址范围
// 入参: page 输出全局页面实例序号, name 按源类型规范化的原名称
// 返回: string 输出名称, error 索引、缺失映射、预算或取消错误
func (n *compositionNames) target(page int, name string) (string, error) {
	if n == nil || n.budget == nil {
		return "", fmt.Errorf("%w: missing composition names", ErrInvalid)
	}
	if err := n.budget.step(1); err != nil {
		return "", err
	}
	if err := n.budget.scan(int64(len(name))); err != nil {
		return "", err
	}
	if page < 0 || page >= len(n.pages) {
		return "", fmt.Errorf("%w: composition name page index", ErrInvalid)
	}
	value, exists := n.pages[page][name]
	if !exists {
		return "", fmt.Errorf("%w: missing composition name mapping", ErrInvalid)
	}
	if err := n.budget.step(0); err != nil {
		return "", err
	}
	return value, nil
}

// document 预留全部原名称，避免生成的名称占用后续页面的原名称
// 入参: format 输出格式, document 输出文档序号, order 页面实例顺序, pages 原名称及保护状态, instances 全部页面身份, visited 页面归属检查表, preserve 是否按完整原文档保留名称
// 返回: error 归属、名称、许可、预算或取消错误
func (n *compositionNames) document(format Format, document int, order []int, pages []compositionNamePage, instances []compositionPageInstance, visited []bool, preserve bool) error {
	reserved := make(map[string]bool)
	claimed := make(map[string]bool)
	names := make(map[int][]string)
	for _, page := range order {
		if err := n.budget.step(1); err != nil {
			return err
		}
		if page < 0 || page >= len(pages) || visited[page] || instances[page].document != document {
			return fmt.Errorf("%w: composition name document pages", ErrInvalid)
		}
		visited[page] = true
		if err := n.budget.step(len(pages[page].names)); err != nil {
			return err
		}
		n.pages[page] = make(map[string]string, len(pages[page].names))
		for name := range pages[page].names {
			if err := n.budget.scan(int64(len(name))); err != nil {
				return err
			}
			reserved[name] = true
			names[page] = append(names[page], name)
		}
		var sortError error
		slices.SortFunc(names[page], func(a, b string) int {
			if sortError == nil {
				sortError = n.budget.step(1)
			}
			if sortError == nil {
				sortError = n.budget.scan(int64(len(a)) + int64(len(b)))
			}
			if sortError != nil {
				return 0
			}
			return strings.Compare(a, b)
		})
		if sortError != nil {
			return sortError
		}
	}
	counter := 0
	for _, protected := range []bool{true, false} {
		for _, page := range order {
			if err := n.budget.step(1); err != nil {
				return err
			}
			if pages[page].fixed != protected {
				continue
			}
			for _, name := range names[page] {
				if err := n.budget.step(1); err != nil {
					return err
				}
				value := name
				compatible := format == FormatOpenXPS || xmlNCName(name)
				if claimed[name] && !preserve || !compatible {
					if protected {
						return fmt.Errorf("%w: protected composition Name collision or type conversion", ErrRestricted)
					}
					prefix := name
					if !compatible {
						prefix = "Name"
					}
					for {
						if err := n.budget.step(1); err != nil {
							return err
						}
						if counter == math.MaxInt {
							return fmt.Errorf("%w: composition name counter", ErrLimit)
						}
						counter++
						suffix := "_" + strconv.Itoa(counter)
						if int64(len(prefix)) > n.budget.limits.MaxPartBytes-int64(len(suffix)) {
							return fmt.Errorf("%w: composition name length", ErrLimit)
						}
						if err := n.budget.scan(int64(len(prefix)) + int64(len(suffix))); err != nil {
							return err
						}
						value = prefix + suffix
						if !reserved[value] && !claimed[value] {
							break
						}
					}
				}
				claimed[value] = true
				n.pages[page][name] = value
			}
		}
	}
	return nil
}

// newCompositionNameCollector 建立仅理解固定布局和MCE名称语义的收集器
// 入参: format 源格式, budget 共享预算
// 返回: compositionNameCollector 名称收集器
func newCompositionNameCollector(format Format, budget *compositionBudget) compositionNameCollector {
	namespace := formatNamespace(format)
	understood := map[string]bool{namespace: true, namespace + "/resourcedictionary-key": true, structureNamespace(format): true, mcNamespace: true, xmlNamespace: true}
	if format == FormatOpenXPS {
		understood[openXPS3DNamespace] = true
	}
	return compositionNameCollector{budget: budget, format: format, retain: true, mce: compatibilityProcessor{understood: understood, context: budget.context}}
}

// root 校验原始部件并计入扫描预算，不以过滤后的树替代保留标记
// 入参: part 原部件, local 预期根元素名称
// 返回: *xmlElement 原始元素树, error XML、支持范围、预算或取消错误
func (c *compositionNameCollector) root(part packagePart, local string) (*xmlElement, error) {
	if compositionIndexRoot(part.media) != "" {
		var index *compositionIndex
		var err error
		if c.source != nil {
			index, err = c.source.indexPart(part, c.budget)
		} else {
			index, err = newCompositionIndex(part, c.format, c.budget)
		}
		if err != nil {
			return nil, err
		}
		if err := index.inspect(c.retain, c.budget); err != nil {
			return nil, err
		}
		if c.retain {
			return index.raw, nil
		}
		return index.active, nil
	}
	if int64(len(part.data)) > c.budget.limits.MaxPartBytes {
		return nil, fmt.Errorf("%w: composition name XML size", ErrLimit)
	}
	if err := c.budget.scan(int64(len(part.data))); err != nil {
		return nil, err
	}
	nodes := 0
	tracker := newResourceMarkupScopeTracker(c.format, c.format == FormatOpenXPS, c.budget.context)
	root, err := decodeXMLVisit(part.data, c.budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := c.budget.step(1); err != nil {
			return err
		}
		_, _, err := tracker.visit(token, node)
		if err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); start {
			nodes++
			if err := c.budget.step(len(node.Attr)); err != nil {
				return err
			}
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if err := c.budget.step(nodes); err != nil {
		return nil, err
	}
	namespace := formatNamespace(c.format)
	processed, err := preprocessXMLContext(root, []string{namespace, namespace + "/resourcedictionary-key"}, c.budget.context)
	if err != nil {
		return nil, err
	}
	if processed.Name != (xml.Name{Space: formatNamespace(c.format), Local: local}) {
		return nil, fmt.Errorf("%w: composition name root element", ErrInvalid)
	}
	return root, nil
}

// name 按原格式的Name类型规范化并校验名称，OpenXPS的LinkTarget不套用xs:ID
// 入参: value 原属性值, target 是否为LinkTarget声明
// 返回: string 规范化名称, error 名称、预算或取消错误
func (c *compositionNameCollector) name(value string, target bool) (string, error) {
	if err := c.budget.step(1); err != nil {
		return "", err
	}
	if err := c.budget.scan(int64(len(value))); err != nil {
		return "", err
	}
	identifier := !target || c.format != FormatOpenXPS && (c.source == nil || c.source.sourceFormat != FormatOpenXPS)
	if identifier {
		value = strings.Trim(value, " \t\r\n")
	}
	if !fixedNamePattern(value) || identifier && !xmlNCName(value) {
		return "", fmt.Errorf("%w: composition Name %q", ErrInvalid, value)
	}
	return value, nil
}

// page 收集页面中的实际名称，互斥分支合并，能够同时出现的同名标识返回错误
// 入参: part 原FixedPage部件
// 返回: map[string]bool 原名称集合, error 名称、XML、预算或取消错误
func (c *compositionNameCollector) page(part packagePart) (map[string]bool, error) {
	root, err := c.root(part, "FixedPage")
	if err != nil {
		return nil, err
	}
	result := make(map[string]bool)
	if err := c.visual(root, false, false, result, compatibilityScope{}); err != nil {
		return nil, err
	}
	return result, nil
}

// visual 遍历全部已知分支，只有AlternateContent的不同候选分支允许复用同一名称
// 入参: node 原始节点, resource 是否位于资源字典内, branch 是否为直接候选分支, seen 可同时存在的名称, inherited 祖先MCE规则
// 返回: error 重复声明、资源名称、MCE、预算或取消错误
func (c *compositionNameCollector) visual(node *xmlElement, resource, branch bool, seen map[string]bool, inherited compatibilityScope) error {
	if err := c.budget.step(1); err != nil {
		return err
	}
	scope, err := c.mce.rules(node, inherited)
	if err != nil {
		return err
	}
	control := branch || node.Name.Space == mcNamespace && node.Name.Local == "AlternateContent"
	if err := c.mce.validateAttributes(node, scope, control); err != nil {
		return err
	}
	if !c.mce.understood[node.Name.Space] {
		if !scope.ignorable[node.Name.Space] {
			return fmt.Errorf("%w: composition page element namespace %q", ErrUnsupported, node.Name.Space)
		}
		if !scope.processes(node.Name) {
			return nil
		}
		if err := compatibilityNoXMLContext(node); err != nil {
			return err
		}
		for _, child := range node.Children {
			if err := c.visual(child, resource, false, seen, scope); err != nil {
				return err
			}
		}
		return nil
	}
	if node.Name.Space == mcNamespace {
		if node.Name.Local == "AlternateContent" {
			if len(compatibilityWords(node.Text)) != 0 {
				return fmt.Errorf("%w: text inside composition AlternateContent", ErrInvalid)
			}
			var selection compatibilitySelection
			union := make(map[string]bool)
			for _, child := range node.Children {
				if err := c.mce.alternative(child, scope, &selection); err != nil {
					return err
				}
				local := make(map[string]bool)
				if err := c.visual(child, resource, true, local, scope); err != nil {
					return err
				}
				for name := range local {
					if err := c.budget.step(1); err != nil {
						return err
					}
					union[name] = true
				}
			}
			if selection.choices == 0 {
				return fmt.Errorf("%w: composition AlternateContent requires Choice", ErrInvalid)
			}
			for name := range union {
				if err := c.budget.step(1); err != nil {
					return err
				}
				if seen[name] {
					return fmt.Errorf("%w: duplicate composition page Name %q", ErrInvalid, name)
				}
				seen[name] = true
			}
			return nil
		}
		if !branch || node.Name.Local != "Choice" && node.Name.Local != "Fallback" {
			return fmt.Errorf("%w: misplaced composition MCE branch", ErrInvalid)
		}
	}
	if node.Name.Space == formatNamespace(c.format) {
		switch node.Name.Local {
		case "FixedPage", "Canvas", "Path", "Glyphs":
			if raw, present := node.attribute("Name"); present {
				value, err := c.name(raw, false)
				if err != nil {
					return err
				}
				if resource || seen[value] {
					return fmt.Errorf("%w: duplicate or resource composition Name %q", ErrInvalid, value)
				}
				seen[value] = true
			}
		case "ResourceDictionary":
			resource = true
		}
	}
	for _, child := range node.Children {
		if err := c.visual(child, resource, false, seen, scope); err != nil {
			return err
		}
	}
	return nil
}

// document 收集原文档所有保留分支中声明的页面地址，不把未声明的页面元素自动变为链接目标
// 入参: part 原FixedDocument部件
// 返回: map[string]map[string]bool 原页面小写URI到声明名称的集合, error XML、地址、名称或预算错误
func (c *compositionNameCollector) document(part packagePart) (map[string]map[string]bool, error) {
	root, err := c.root(part, "FixedDocument")
	if err != nil {
		return nil, err
	}
	result := make(map[string]map[string]bool)
	var visit func(*xmlElement, string, bool) error
	visit = func(node *xmlElement, page string, targets bool) error {
		if err := c.budget.step(1); err != nil {
			return err
		}
		if node.Name.Space == formatNamespace(c.format) {
			switch node.Name.Local {
			case "PageContent":
				value, exists := node.attribute("Source")
				if !exists {
					return fmt.Errorf("%w: composition PageContent Source", ErrInvalid)
				}
				if err := c.budget.scan(int64(len(value))); err != nil {
					return err
				}
				resolved, err := resolvePart(part.name, value)
				if err != nil {
					return err
				}
				page, targets = strings.ToLower(resolved), false
			case "PageContent.LinkTargets":
				targets = true
			case "LinkTarget":
				value, exists := node.attribute("Name")
				if page == "" || !targets || !exists {
					return fmt.Errorf("%w: composition LinkTarget declaration", ErrInvalid)
				}
				name, err := c.name(value, true)
				if err != nil {
					return err
				}
				if result[page] == nil {
					result[page] = make(map[string]bool)
				}
				result[page][name] = true
			}
		}
		for _, child := range node.Children {
			if err := visit(child, page, targets); err != nil {
				return err
			}
		}
		return nil
	}
	if err := visit(root, "", false); err != nil {
		return nil, err
	}
	return result, nil
}

// newCompositionNavigation 独立保存名称映射与跨方言去重表并构造输出地址索引，尚未写出的资源仅登记地址身份
// 入参: plan 输出规划, names 各页面实例的原名称到输出名称映射, dropped 各页面因跨方言同源去重移除的原LinkTarget集合
// 返回: *compositionNavigation 地址改写器，失败为nil, error 名称、索引、预算或取消错误
func newCompositionNavigation(plan *compositionPlan, names []map[string]string, dropped []map[string]bool) (*compositionNavigation, error) {
	if len(names) != len(plan.pages) {
		return nil, fmt.Errorf("%w: incomplete composition navigation names", ErrInvalid)
	}
	if err := plan.budget.step(len(names) + len(plan.sources)); err != nil {
		return nil, err
	}
	c := &compositionNavigation{plan: plan, pages: make([]map[string]string, len(names)), sources: make([]*compositionLinkIndex, len(plan.sources))}
	output := &compositionSource{format: plan.format, sequence: plan.sequence, documents: make([]Document, len(plan.documents)), pages: make([]PageReference, len(plan.pages)), parts: make(map[string]packagePart)}
	for i, mapping := range names {
		if err := plan.budget.step(len(mapping)); err != nil {
			return nil, err
		}
		c.pages[i] = make(map[string]string, len(mapping))
		for original, target := range mapping {
			if err := plan.budget.scan(int64(len(original)) + int64(len(target))); err != nil {
				return nil, err
			}
			if !fixedNamePattern(original) || !fixedNamePattern(target) || plan.format == FormatXPS && !xmlNCName(target) {
				return nil, fmt.Errorf("%w: composition navigation name", ErrInvalid)
			}
			c.pages[i][original] = target
		}
		page := plan.pages[i].reference
		mappedTargets := make([]string, 0, len(page.LinkTargets))
		seenTargets := make(map[string]bool, len(page.LinkTargets))
		for _, name := range plan.pages[i].reference.LinkTargets {
			if err := plan.budget.step(1); err != nil {
				return nil, err
			}
			if i < len(dropped) && dropped[i][name] {
				continue
			}
			target, exists := c.pages[i][name]
			if !exists {
				return nil, fmt.Errorf("%w: missing composition advertised name", ErrInvalid)
			}
			if !seenTargets[target] {
				seenTargets[target] = true
				mappedTargets = append(mappedTargets, target)
			}
		}
		page.LinkTargets = mappedTargets
		output.pages[i] = page
	}
	for i, document := range plan.documents {
		if err := plan.budget.step(len(document.pages) + 1); err != nil {
			return nil, err
		}
		output.documents[i] = Document{Part: document.part, Pages: make([]PageReference, len(document.pages))}
		for j, page := range document.pages {
			output.documents[i].Pages[j] = output.pages[page]
		}
	}
	var err error
	c.output, err = newCompositionLinkIndex(output, plan.budget)
	if err != nil {
		return nil, err
	}
	for i, source := range plan.sources {
		if plan.indices[i] == nil {
			continue
		}
		c.sources[i], err = newCompositionLinkIndex(source, plan.budget)
		if err != nil {
			return nil, err
		}
	}
	if err := plan.budget.step(0); err != nil {
		return nil, err
	}
	return c, nil
}

// rewrite 将原始导航绑定映射到输出页面或资源，目标绑定未变时保留原URI
// 入参: source 源快照序号, original 原地址基准, destination 输出地址基准, value 原始导航, current 当前页面实例，非页面为-1, resources 当前作用域的资源映射
// 返回: string 输出URI, bool 是否修改, error 缺失目标、名称、地址、预算或取消错误
func (c *compositionNavigation) rewrite(source int, original, destination, value string, current int, resources map[string]string) (string, bool, error) {
	if c == nil || c.plan == nil || source < 0 || source >= len(c.sources) || c.sources[source] == nil || current < -1 || current >= len(c.plan.pages) || current >= 0 && c.plan.pages[current].source != source {
		return "", false, fmt.Errorf("%w: composition navigation context", ErrInvalid)
	}
	b := c.plan.budget
	if err := b.scan(int64(len(destination))); err != nil {
		return "", false, err
	}
	destination, err := opcPartName(destination)
	if err != nil {
		return "", false, err
	}
	binding, err := c.sources[source].resolve(original, value)
	if err != nil {
		return "", false, err
	}
	if binding.external {
		return value, false, nil
	}
	uri, err := url.Parse(binding.uri)
	if err != nil {
		return "", false, err
	}
	target, fragment, name, page := "", "", "", -1
	if binding.scoped {
		if binding.page < 0 {
			return "", false, fmt.Errorf("%w: composition navigation targets an empty original scope", ErrUnsupported)
		}
		page, err = c.plan.target(source, binding.page, current)
		if err != nil {
			return "", false, err
		}
		if page < 0 {
			return "", false, fmt.Errorf("%w: composition navigation targets an omitted page", ErrUnsupported)
		}
		instance := c.plan.pages[page]
		target = instance.reference.Part
		scope := c.sources[source].scopes[strings.ToLower(binding.part)]
		switch {
		case binding.name != "":
			var exists bool
			name, exists = c.pages[page][binding.name]
			if !exists {
				return "", false, fmt.Errorf("%w: composition navigation target name", ErrInvalid)
			}
			fragment, err = compositionNavigationFragment(name, b)
			if err != nil {
				return "", false, err
			}
			target = c.plan.documents[instance.document].part
		case linkPageNumber(uri.Fragment):
			target, fragment = c.plan.sequence, strconv.Itoa(page+1)
		case uri.Fragment == "" && scope.kind == createdNavigationDocument && instance.position == 0:
			target = c.plan.documents[instance.document].part
		case uri.Fragment == "" && scope.kind == createdNavigationSequence && page == 0:
			target = c.plan.sequence
		}
	} else {
		var exists bool
		target, exists = resources[strings.ToLower(binding.part)]
		if !exists {
			return "", false, fmt.Errorf("%w: composition navigation resource mapping", ErrUnsupported)
		}
		if err := b.scan(int64(len(target))); err != nil {
			return "", false, err
		}
		target, err = opcPartName(target)
		if err != nil {
			return "", false, err
		}
		if _, layout := c.output.scopes[strings.ToLower(target)]; layout {
			return "", false, fmt.Errorf("%w: composition resource navigation maps to primary layout", ErrInvalid)
		}
		fragment = uri.EscapedFragment()
	}
	maximum := min(b.limits.MaxPartBytes, b.limits.MaxPackageBytes, int64(math.MaxInt))
	size := int64(len(target))
	if fragment != "" {
		if int64(len(fragment))+1 > maximum-size {
			return "", false, fmt.Errorf("%w: composition navigation URI size", ErrLimit)
		}
		size += int64(len(fragment)) + 1
	}
	if size > maximum {
		return "", false, fmt.Errorf("%w: composition navigation URI size", ErrLimit)
	}
	for _, part := range []string{destination, target} {
		key := strings.ToLower(part)
		if _, exists := c.output.source.parts[key]; !exists {
			if err := b.step(1); err != nil {
				return "", false, err
			}
			if len(c.output.source.parts) >= b.limits.MaxPartCount {
				return "", false, fmt.Errorf("%w: composition navigation part count", ErrLimit)
			}
			c.output.source.parts[key] = packagePart{name: part}
		}
	}
	actual, err := c.output.resolve(destination, value)
	if err != nil && errors.Is(err, ErrLimit) {
		return "", false, err
	}
	if late := b.step(0); late != nil {
		return "", false, late
	}
	if err == nil && (binding.scoped && actual.scoped && actual.page == page && actual.name == name || !binding.scoped && !actual.scoped && strings.EqualFold(actual.part, target)) {
		return value, false, nil
	}
	result := target
	if fragment != "" {
		result += "#" + fragment
	}
	if err := b.scan(int64(len(result))); err != nil {
		return "", false, err
	}
	return result, result != value, nil
}

// compositionNavigationFragment 在转义合法名称前检查精确字节数，避免URI扩展超过输出预算
// 入参: name 已校验的固定布局名称, budget 累计预算
// 返回: string 已转义片段, error 字节预算或取消错误
func compositionNavigationFragment(name string, budget *compositionBudget) (string, error) {
	if err := budget.scan(int64(len(name))); err != nil {
		return "", err
	}
	maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
	var size int64
	for i := range len(name) {
		count := int64(1)
		if !opcUnreserved(name[i]) {
			count = 3
		}
		if count > maximum-size {
			return "", fmt.Errorf("%w: composition navigation fragment size", ErrLimit)
		}
		size += count
	}
	if err := budget.scan(size); err != nil {
		return "", err
	}
	result := url.PathEscape(name)
	if err := budget.step(0); err != nil {
		return "", err
	}
	return result, nil
}

// printResources 解析标准打印票据或能力文档的包内资源定位，保留原字节及模型路径
// 入参: part 已独立读取的标准元数据
// 返回: error Framework、资源、媒体类型、预算或取消错误
func (s *compositionCapture) printResources(part packagePart) error {
	known, capabilities := printResourceMedia(part.media)
	if !known {
		return nil
	}
	key := strings.ToLower(part.name)
	references, cached := s.source.printResources[key]
	if cached && !s.source.retained[key] {
		return nil
	}
	if !cached {
		if err := s.budget.scan(int64(len(part.data))); err != nil {
			return err
		}
		options := &PrintSettingsOptions{Limits: s.budget.limits}
		var model *PrintSettings
		var err error
		if capabilities {
			var value *PrintCapabilities
			value, err = ParsePrintCapabilities(s.budget.context, part.data, options)
			if err == nil {
				model = &PrintSettings{Version: value.Version, Elements: value.Elements}
			}
		} else {
			model, err = ParsePrintSettings(s.budget.context, part.data, options)
		}
		if err != nil {
			return err
		}
		var charge func([]PrintSetting) error
		charge = func(settings []PrintSetting) error {
			if err := s.budget.step(len(settings)); err != nil {
				return err
			}
			for _, setting := range settings {
				if err := charge(setting.Children); err != nil {
					return err
				}
			}
			return nil
		}
		if err := charge(model.Elements); err != nil {
			return err
		}
		references, err = collectPrintResourceReferences(s.budget.context, printResourceDocument{model: model, capabilities: capabilities, part: part.name}, options)
		if err != nil {
			return err
		}
	}
	for _, reference := range references {
		if err := s.budget.step(1); err != nil {
			return err
		}
		if err := s.budget.scan(int64(len(reference.uri))); err != nil {
			return err
		}
		if reference.kind == printResourceProfile {
			media, err := s.reader.pkg.contentType(reference.uri)
			if err != nil {
				return err
			}
			if !requiredResourceMedia(requiredProfile, media) {
				return &PartError{Part: reference.uri, Err: fmt.Errorf("%w: print color profile content type", ErrInvalid)}
			}
			if err := s.dependency(part.name, reference.uri, ""); err != nil {
				return err
			}
			key := strings.ToLower(reference.uri)
			if s.profiles[key] {
				continue
			}
			value, err := s.load(reference.uri)
			if err != nil {
				return err
			}
			if _, err := parseICCProfile(value.data); err != nil {
				return &PartError{Part: reference.uri, Err: err}
			}
			s.profiles[key] = true
		} else if reference.kind == printResourceContent {
			if err := s.auxiliaryResource(reference.uri, ""); err != nil {
				return err
			}
			if s.source.retained[key] {
				if err := s.retain(reference.uri, ""); err != nil {
					return err
				}
			}
		} else {
			return fmt.Errorf("%w: unclassified print resource", ErrInvalid)
		}
	}
	if err := s.budget.step(0); err != nil {
		return err
	}
	s.source.printResources[key] = references
	return nil
}

// auxiliaryResource 跟随显式横幅、封面或错误页内容，辅助布局不加入选定的阅读页序
// 入参: part 包根部件URI, required 子布局要求的类型，空值不限定内容种类
// 返回: error 来源、类型、引用、预算或取消错误
func (s *compositionCapture) auxiliaryResource(part, required string) error {
	if err := s.budget.step(1); err != nil {
		return err
	}
	media, err := s.reader.pkg.contentType(part)
	if err != nil {
		return err
	}
	if required != "" && !strings.EqualFold(media, fixedContentType(required)) {
		return &PartError{Part: part, Err: fmt.Errorf("%w: auxiliary layout content type", ErrInvalid)}
	}
	role := createdNavigationOther
	for _, entry := range []struct {
		name string
		kind createdNavigationKind
	}{
		{"fixedpage", createdNavigationPage},
		{"fixeddocument", createdNavigationDocument},
		{"fixeddocumentsequence", createdNavigationSequence},
	} {
		if strings.EqualFold(media, fixedContentType(entry.name)) {
			role = entry.kind
			break
		}
	}
	if role != createdNavigationOther {
		key := strings.ToLower(part)
		promoted := !s.source.auxiliary[key]
		s.source.auxiliary[key], s.layout[key], s.roles.parts[key] = true, true, role
		if _, loaded := s.source.parts[key]; promoted && loaded && role != createdNavigationPage {
			s.queue = append(s.queue, compositionSourcePart{part: s.reader.pkg.names[key]})
		}
	}
	return s.add(part, "")
}

// rewriteCompositionPrintResources 按原模型路径改写标准票据与能力文档的包内资源URI，保留其余原文与原编码
// 入参: part 原部件, mapping 原小写规范部件名到目标规范包根URI的映射, budget 共享累计预算
// 返回: []byte 独立结果，失败为nil, bool 是否修改, error 格式、映射、资源或取消错误
func rewriteCompositionPrintResources(part packagePart, mapping map[string]string, budget *compositionBudget) ([]byte, bool, error) {
	if budget == nil {
		return nil, false, fmt.Errorf("%w: missing composition budget", ErrInvalid)
	}
	if err := budget.step(0); err != nil {
		return nil, false, err
	}
	known, capabilities := printResourceMedia(part.media)
	if !known {
		return nil, false, fmt.Errorf("%w: opaque print document media", ErrUnsupported)
	}
	maximum := min(budget.limits.MaxMetadataBytes, budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
	if int64(len(part.data)) > maximum {
		return nil, false, fmt.Errorf("%w: print resource rewrite input", ErrLimit)
	}
	if err := budget.scan(int64(len(part.data))); err != nil {
		return nil, false, err
	}
	text := make(map[*xmlElement][]compositionPrintText)
	var version uint32
	root, err := decodeXMLVisitSpan(part.data, budget.limits, func(token xml.Token, node *xmlElement, start, end int64) error {
		if err := budget.step(1); err != nil {
			return err
		}
		switch token.(type) {
		case xml.StartElement:
			if version == 0 {
				if node.Name.Space == printFramework2NS {
					version = 2
				} else if node.Name.Space == printFrameworkNS {
					version = 1
				}
			}
			return compositionPrintRepresentable(node, version, capabilities)
		case xml.CharData:
			if node != nil && compositionPrintValueNode(node, version) {
				text[node] = append(text[node], compositionPrintText{start: int(start), end: int(end)})
			}
		}
		return nil
	})
	if err != nil {
		return nil, false, err
	}
	options, err := printSettingsOptions(budget.context, &PrintSettingsOptions{Limits: budget.limits})
	if err != nil {
		return nil, false, err
	}
	model, err := parsePrintDocument(root, options, capabilities)
	if err != nil {
		return nil, false, err
	}
	references, err := collectPrintResourceReferences(budget.context, printResourceDocument{model: model, capabilities: capabilities, part: part.name}, &options.PrintSettingsOptions)
	if err != nil {
		return nil, false, err
	}
	targets := make(map[*xmlElement]string)
	var changes []xmlValueReplacement
	intermediate := maximum
	if encoding, _ := xmlInputEncoding(part.data); encoding != "utf-8" {
		intermediate += min(maximum/2, int64(math.MaxInt)-maximum)
	}
	var replacementBytes int64
	for _, reference := range references {
		if err := budget.step(1 + len(reference.path)); err != nil {
			return nil, false, err
		}
		if err := budget.scan(int64(len(reference.uri))); err != nil {
			return nil, false, err
		}
		target, exists := mapping[strings.ToLower(reference.uri)]
		if !exists {
			return nil, false, fmt.Errorf("%w: missing print resource mapping for %s", ErrUnsupported, reference.uri)
		}
		if int64(len(target)) > maximum {
			return nil, false, fmt.Errorf("%w: print resource target length", ErrLimit)
		}
		if err := budget.scan(int64(len(target))); err != nil {
			return nil, false, err
		}
		canonical, err := opcPartName(target)
		if err != nil {
			return nil, false, err
		}
		if canonical != target {
			return nil, false, fmt.Errorf("%w: noncanonical print resource target", ErrInvalid)
		}
		node, err := resolveCompositionPrintValueNode(root, reference.path, version, capabilities)
		if err != nil {
			return nil, false, err
		}
		originalURI, originalError := opcPartName(node.Text)
		if !compositionPrintValueNode(node, version) || originalError != nil || originalURI != reference.uri {
			return nil, false, fmt.Errorf("%w: print resource rewrite value", ErrInvalid)
		}
		if previous, exists := targets[node]; exists {
			if previous != target {
				return nil, false, fmt.Errorf("%w: conflicting print resource mappings", ErrInvalid)
			}
			continue
		}
		targets[node] = target
		if reference.uri == target {
			continue
		}
		spans := text[node]
		if len(spans) == 0 {
			return nil, false, fmt.Errorf("%w: print resource text range", ErrUnsupported)
		}
		escaped := xmlRewriteBuffer{maximum: intermediate - replacementBytes, context: budget.context}
		if err := xml.EscapeText(&escaped, []byte(target)); err != nil {
			return nil, false, err
		}
		replacementBytes += int64(escaped.Len())
		for i, span := range spans {
			if err := budget.step(1); err != nil {
				return nil, false, err
			}
			change := xmlValueReplacement{start: span.start, end: span.end}
			if i == 0 {
				change.data = escaped.Bytes()
			}
			changes = append(changes, change)
		}
	}
	if len(changes) == 0 {
		if err := budget.scan(int64(len(part.data))); err != nil {
			return nil, false, err
		}
		output := bytes.Clone(part.data)
		if err := budget.step(0); err != nil {
			return nil, false, err
		}
		return output, false, nil
	}
	return compositionPrintReplace(part.data, changes, maximum, intermediate, budget)
}

// compositionPrintValueNode 判断XML节点是否为标准v1显式Value或v2可承载内联文本值的属性与参数节点
// 入参: node 已展开名称的节点, version 框架版本号
// 返回: bool 是否可承载标准打印资源URI文本
func compositionPrintValueNode(node *xmlElement, version uint32) bool {
	if version != 2 {
		return printSettingKind(node.Name) == PrintSettingValue
	}
	kind, psf2, err := printSettingKindForVersion(node, version)
	return err == nil && psf2 && (kind == PrintSettingProperty || kind == PrintSettingScoredProperty || kind == PrintSettingParameterInit)
}

// resolveCompositionPrintValueNode 将模型路径映射回原始打印XML节点，补偿PSF2的selectiontype与内联文本合成子节点偏移
// 入参: root 原始打印XML根, path 模型子元素索引路径, version 框架版本号, capabilities 是否为能力文档
// 返回: *xmlElement 原始XML值节点, error 路径越界或结构不匹配错误
func resolveCompositionPrintValueNode(root *xmlElement, path []int, version uint32, capabilities bool) (*xmlElement, error) {
	node := root
	for step, idx := range path {
		if step == 0 {
			if idx < 0 || idx >= len(node.Children) {
				return nil, fmt.Errorf("%w: print resource rewrite path", ErrInvalid)
			}
			node = node.Children[idx]
			continue
		}
		kind, psf2, err := printSettingKindForVersion(node, version)
		if err != nil {
			return nil, err
		}
		synthetic := 0
		if psf2 {
			if capabilities && kind == PrintSettingFeature {
				if _, hasSel := node.attributeNS(printFramework2NS, "selectiontype"); hasSel {
					if idx == 0 {
						return nil, fmt.Errorf("%w: print resource rewrite path", ErrInvalid)
					}
					synthetic++
				}
			}
			inlineCapable := kind == PrintSettingProperty || kind == PrintSettingScoredProperty || kind == PrintSettingParameterInit
			_, hasXSIType := node.attributeNS(xsiNamespace, "type")
			if inlineCapable && (len(node.Children) == 0 || hasXSIType || !xmlWhitespace(node.Text)) {
				if idx == synthetic {
					if step == len(path)-1 {
						return node, nil
					}
					return nil, fmt.Errorf("%w: print resource rewrite path", ErrInvalid)
				}
				synthetic++
			}
		}
		xmlIdx := idx - synthetic
		if xmlIdx < 0 || xmlIdx >= len(node.Children) {
			return nil, fmt.Errorf("%w: print resource rewrite path", ErrInvalid)
		}
		node = node.Children[xmlIdx]
	}
	return node, nil
}

// compositionPrintRepresentable 校验打印文档节点是否可由标准Print Schema v1或v2模型表示，拒绝未知XML扩展与属性
// 入参: node 已展开名称的节点, version 框架版本号, capabilities 是否为能力文档
// 返回: error 未支持的元素、属性或非法psftype错误
func compositionPrintRepresentable(node *xmlElement, version uint32, capabilities bool) error {
	expectedRootNS := printFrameworkNS
	if version == 2 {
		expectedRootNS = printFramework2NS
	}
	if node.Name.Space == expectedRootNS && (node.Name.Local == "PrintTicket" || node.Name.Local == "PrintCapabilities") {
		for _, attribute := range node.Attr {
			if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
				continue
			}
			if attribute.Name.Space != "" || attribute.Name.Local != "version" {
				return fmt.Errorf("%w: print resource XML attribute {%s}%s", ErrUnsupported, attribute.Name.Space, attribute.Name.Local)
			}
		}
		return nil
	}
	if version == 0 {
		return fmt.Errorf("%w: print resource XML extension {%s}%s", ErrUnsupported, node.Name.Space, node.Name.Local)
	}
	kind, psf2, err := printSettingKindForVersion(node, version)
	if err != nil {
		return err
	}
	if kind == PrintSettingUnknown {
		return fmt.Errorf("%w: print resource XML extension {%s}%s", ErrUnsupported, node.Name.Space, node.Name.Local)
	}
	inlineCapable := psf2 && (kind == PrintSettingProperty || kind == PrintSettingScoredProperty || kind == PrintSettingParameterInit)
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		allowed := false
		if psf2 {
			switch {
			case attribute.Name == (xml.Name{Space: printFramework2NS, Local: "psftype"}):
				allowed = true
			case inlineCapable && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"}):
				allowed = true
			case kind == PrintSettingOption && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "default"}):
				allowed = true
			case capabilities && kind == PrintSettingOption && (attribute.Name == (xml.Name{Local: "constrained"}) || attribute.Name == (xml.Name{Space: printFramework2NS, Local: "constrained"})):
				allowed = true
			case capabilities && kind == PrintSettingFeature && attribute.Name == (xml.Name{Space: printFramework2NS, Local: "selectiontype"}):
				allowed = true
			}
		} else {
			allowed = kind == PrintSettingValue && attribute.Name == (xml.Name{Space: xsiNamespace, Local: "type"})
			if attribute.Name.Space == "" {
				if kind != PrintSettingValue {
					allowed = attribute.Name.Local == "name" || capabilities && kind == PrintSettingOption && attribute.Name.Local == "constrained"
				}
			}
		}
		if !allowed {
			return fmt.Errorf("%w: print resource XML attribute {%s}%s", ErrUnsupported, attribute.Name.Space, attribute.Name.Local)
		}
	}
	return nil
}

// compositionPrintReplace 按互不重叠的字符范围替换数据，输出前恢复原编码并重新校验XML
// 入参: original 原数据, changes UTF-8范围及替换值, maximum 原编码上限, intermediate UTF-8上限, budget 共享预算
// 返回: []byte 独立结果，失败为nil, bool 是否修改, error 范围、资源、XML或取消错误
func compositionPrintReplace(original []byte, changes []xmlValueReplacement, maximum, intermediate int64, budget *compositionBudget) ([]byte, bool, error) {
	if err := budget.scan(int64(len(original))); err != nil {
		return nil, false, err
	}
	input, err := xmlUTF8(original)
	if err != nil {
		return nil, false, err
	}
	slices.SortFunc(changes, func(a, b xmlValueReplacement) int { return cmp.Compare(a.start, b.start) })
	outputSize := int64(len(input))
	position := 0
	for _, change := range changes {
		if err := budget.step(1); err != nil {
			return nil, false, err
		}
		if change.start < position || change.end < change.start || change.end > len(input) {
			return nil, false, fmt.Errorf("%w: overlapping print resource text", ErrInvalid)
		}
		outputSize += int64(len(change.data)) - int64(change.end-change.start)
		position = change.end
	}
	if outputSize < 0 || outputSize > intermediate {
		return nil, false, fmt.Errorf("%w: print resource rewrite output", ErrLimit)
	}
	if err := budget.scan(outputSize); err != nil {
		return nil, false, err
	}
	output := make([]byte, 0, int(outputSize))
	position = 0
	for _, change := range changes {
		if err := budget.step(1); err != nil {
			return nil, false, err
		}
		output = append(output, input[position:change.start]...)
		output = append(output, change.data...)
		position = change.end
	}
	output = append(output, input[position:]...)
	output, err = restoreXMLEncoding(original, output, maximum, budget.context)
	if err != nil {
		return nil, false, err
	}
	if err := budget.scan(int64(len(output))); err != nil {
		return nil, false, err
	}
	if _, err := decodeXMLVisit(output, budget.limits, func(_ xml.Token, _ *xmlElement) error { return budget.step(1) }); err != nil {
		return nil, false, err
	}
	if err := budget.step(0); err != nil {
		return nil, false, err
	}
	return output, true, nil
}

// compositionProtection 从受限文档根扫描原始布局、关系及标准票据，返回须保持原身份和原文的部件集合
// 入参: source 独立源快照, budget 共享工作及扫描预算
// 返回: map[string]bool 原URI、媒体类型及原文的保护集合，失败为nil, error 缺失依赖、未支持语义、预算或取消错误
func compositionProtection(source *compositionSource, budget *compositionBudget) (map[string]bool, error) {
	if source == nil || budget == nil || formatNamespace(source.format) == "" {
		return nil, fmt.Errorf("%w: composition protection input", ErrInvalid)
	}
	if err := budget.step(len(source.restricted)); err != nil {
		return nil, err
	}
	g := &compositionProtectionGraph{source: source, budget: budget, parts: make(map[string]bool), roots: make(map[string]bool)}
	for _, key := range slices.Sorted(maps.Keys(source.restricted)) {
		if !source.restricted[key] {
			continue
		}
		if err := g.add(key, fixedContentType("fixeddocument")); err != nil {
			return nil, err
		}
		g.roots[strings.ToLower(key)] = false
	}
	for index := 0; index < len(g.queue); index++ {
		part := source.parts[g.queue[index]]
		if err := g.markup(part); err != nil {
			return nil, &PartError{Part: part.name, Err: err}
		}
		if err := g.relationships(part); err != nil {
			return nil, err
		}
	}
	for root, found := range g.roots {
		if err := budget.step(1); err != nil {
			return nil, err
		}
		if !found {
			return nil, &PartError{Part: root, Err: fmt.Errorf("%w: protection root lacks original restricted font relationship", ErrInvalid)}
		}
	}
	if err := budget.step(0); err != nil {
		return nil, err
	}
	return g.parts, nil
}

// add 校验硬依赖的快照身份及预期媒体类型，同一部件只入队一次
// 入参: name 规范部件URI, media 要求的媒体类型，空值不限定
// 返回: error 快照缺失、类型、身份或预算错误
func (g *compositionProtectionGraph) add(name, media string) error {
	if err := g.budget.step(1); err != nil {
		return err
	}
	if err := g.budget.scan(int64(len(name))); err != nil {
		return err
	}
	canonical, err := opcPartName(name)
	if err != nil {
		return err
	}
	key := strings.ToLower(canonical)
	part, exists := g.source.parts[key]
	if !exists {
		return &PartError{Part: canonical, Err: fmt.Errorf("%w: missing protected snapshot dependency", ErrInvalid)}
	}
	actual, err := opcPartName(part.name)
	if err != nil || !strings.EqualFold(actual, canonical) || part.media == "" || opcRelationshipName(actual) || strings.EqualFold(actual, opcTypesName) {
		return fmt.Errorf("%w: protected snapshot identity", ErrInvalid)
	}
	if media != "" && !strings.EqualFold(media, part.media) {
		return &PartError{Part: part.name, Err: fmt.Errorf("%w: protected dependency content type", ErrInvalid)}
	}
	if int64(len(part.data)) > g.budget.limits.MaxPartBytes {
		return fmt.Errorf("%w: protected snapshot part bytes", ErrLimit)
	}
	if !g.parts[key] {
		if len(g.parts) >= g.budget.limits.MaxPartCount {
			return fmt.Errorf("%w: protected snapshot part count", ErrLimit)
		}
		g.parts[key] = true
		g.queue = append(g.queue, key)
	}
	return nil
}

// markup 按原标记语义展开全部已知保留分支，不从导航或消费页号推断硬依赖
// 入参: part 已确认身份的快照部件
// 返回: error XML、未支持语义、缺失依赖或预算错误
func (g *compositionProtectionGraph) markup(part packagePart) error {
	knownPrint, capabilities := printResourceMedia(part.media)
	layout, err := fontUsageMarkup(part.media)
	definition := strings.EqualFold(part.media, fixedContentType("signaturedefinitions"))
	if err != nil && !knownPrint {
		return err
	}
	if !layout && !knownPrint && !definition {
		if compositionXML(part.media) {
			return fmt.Errorf("%w: protected XML dependency semantics", ErrUnsupported)
		}
		return g.budget.step(0)
	}
	limit := g.budget.limits.MaxPartBytes
	if !layout {
		limit = min(limit, g.budget.limits.MaxMetadataBytes)
	}
	if int64(len(part.data)) > limit {
		return fmt.Errorf("%w: protected markup bytes", ErrLimit)
	}
	var index *compositionIndex
	if compositionIndexRoot(part.media) != "" {
		index, err = g.source.indexPart(part, g.budget)
		if err != nil {
			return err
		}
		if err := index.inspect(true, g.budget); err != nil {
			return err
		}
	} else {
		if err := g.budget.scan(int64(len(part.data))); err != nil {
			return err
		}
	}
	nodes := 0
	var printVersion uint32
	tracker := newResourceMarkupScopeTracker(g.source.format, g.source.format == FormatOpenXPS, g.budget.context)
	visit := func(token xml.Token, node *xmlElement) error {
		if err := g.budget.step(1); err != nil {
			return err
		}
		if !knownPrint && !definition && index == nil {
			skip, _, err := tracker.visit(token, node)
			if err != nil {
				return fmt.Errorf("%w: protected markup semantics: %v", ErrUnsupported, err)
			}
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			nodes++
			if err := g.attributes(node); err != nil {
				return err
			}
			if skip {
				return nil
			}
		} else {
			if _, start := token.(xml.StartElement); !start {
				return nil
			}
			nodes++
			if err := g.attributes(node); err != nil {
				return err
			}
			if knownPrint {
				if printVersion == 0 {
					if node.Name.Space == printFramework2NS {
						printVersion = 2
					} else if node.Name.Space == printFrameworkNS {
						printVersion = 1
					}
				}
				return compositionPrintRepresentable(node, printVersion, capabilities)
			}
			if definition {
				return g.definition(node)
			}
		}
		for _, attr := range node.Attr {
			if node.Name.Space == formatNamespace(g.source.format) && attr.Name == (xml.Name{Local: "Source"}) {
				kind := ""
				if node.Name.Local == "PageContent" {
					kind = "fixedpage"
				} else if node.Name.Local == "DocumentReference" {
					kind = "fixeddocument"
				}
				if kind != "" {
					target, err := resolvePart(part.name, attr.Value)
					if err != nil {
						return err
					}
					if err := g.add(target, fixedContentType(kind)); err != nil {
						return err
					}
				}
			}
			references, err := resourceAttributeReferences(node, attr)
			if err != nil {
				return err
			}
			for _, ref := range references {
				target, err := resolvePart(part.name, ref.uri)
				if err != nil {
					return err
				}
				if err := g.add(target, ""); err != nil {
					return err
				}
				if !requiredResourceMedia(ref.kind, g.source.parts[strings.ToLower(target)].media) {
					return fmt.Errorf("%w: protected resource content type", ErrInvalid)
				}
			}
		}
		return nil
	}
	var root *xmlElement
	if index != nil {
		root = index.raw
		err = index.visit(root, visit)
	} else {
		root, err = decodeXMLVisit(part.data, g.budget.limits, visit)
	}
	if err != nil || !knownPrint {
		return err
	}
	if err := g.budget.step(nodes); err != nil {
		return err
	}
	options := printSettingsConfig{PrintSettingsOptions: PrintSettingsOptions{Limits: g.budget.limits}, context: g.budget.context}
	model, err := parsePrintDocument(root, options, capabilities)
	if err != nil {
		return err
	}
	if err := g.budget.step(nodes); err != nil {
		return err
	}
	refs, err := collectPrintResourceReferences(g.budget.context, printResourceDocument{model: model, capabilities: capabilities, part: part.name}, &options.PrintSettingsOptions)
	if err != nil {
		return err
	}
	for _, ref := range refs {
		if err := g.add(ref.uri, ""); err != nil {
			return err
		}
		if ref.kind == printResourceProfile && !requiredResourceMedia(requiredProfile, g.source.parts[strings.ToLower(ref.uri)].media) {
			return fmt.Errorf("%w: protected print profile content type", ErrInvalid)
		}
		if ref.kind != printResourceContent && ref.kind != printResourceProfile {
			return fmt.Errorf("%w: protected print resource kind", ErrUnsupported)
		}
	}
	return nil
}

// relationships 从关系原文展开各已知分支的内部边，不以消费后的关系缓存代替原文
// 入参: source 已确认身份的关系源部件
// 返回: error 关系原文缺失、未支持语义、目标或预算错误
func (g *compositionProtectionGraph) relationships(source packagePart) error {
	name := createdRelationshipPart(source.name)
	key := strings.ToLower(name)
	part, exists := g.source.parts[key]
	if !exists {
		if _, indexed := g.source.relationships[strings.ToLower(source.name)]; indexed {
			return &PartError{Part: name, Err: fmt.Errorf("%w: missing protected relationship markup", ErrInvalid)}
		}
		return g.budget.step(0)
	}
	if !strings.EqualFold(part.name, name) || !strings.EqualFold(part.media, opcRelsType) {
		return fmt.Errorf("%w: protected relationship identity", ErrInvalid)
	}
	if len(g.parts) >= g.budget.limits.MaxPartCount || int64(len(part.data)) > min(g.budget.limits.MaxMetadataBytes, g.budget.limits.MaxPartBytes) {
		return fmt.Errorf("%w: protected relationship size", ErrLimit)
	}
	g.parts[key] = true
	if err := g.budget.scan(int64(len(part.data))); err != nil {
		return err
	}
	_, err := decodeXMLVisit(part.data, g.budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := g.budget.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := g.attributes(node); err != nil {
			return err
		}
		if err := resourceRelationshipNode(node); err != nil {
			return err
		}
		if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
			return nil
		}
		attributes, err := opcMetadataAttributes(node, opcRelsNS)
		if err != nil {
			return err
		}
		relation, err := parseRelationship(source.name, xml.StartElement{Name: node.Name, Attr: node.Attr}, attributes, make(map[string]bool))
		if err != nil {
			return err
		}
		if relation.Type == formatNamespace(g.source.format)+"/restricted-font" {
			if !strings.EqualFold(source.media, fixedContentType("fixeddocument")) || relation.TargetMode != TargetModeInternal {
				return fmt.Errorf("%w: protected restricted font relationship", ErrInvalid)
			}
			if _, root := g.roots[strings.ToLower(source.name)]; root {
				g.roots[strings.ToLower(source.name)] = true
			}
		}
		if relation.TargetMode == TargetModeExternal {
			return nil
		}
		target, err := resolvePart(source.name, relation.Target)
		if err != nil {
			return err
		}
		if err := g.add(target, ""); err != nil {
			return err
		}
		if relation.Type == formatNamespace(g.source.format)+"/printticket" {
			if known, _ := printResourceMedia(g.source.parts[strings.ToLower(target)].media); !known {
				return fmt.Errorf("%w: protected custom print ticket dependencies", ErrUnsupported)
			}
		}
		if relation.Type == formatNamespace(g.source.format)+"/restricted-font" && !requiredResourceMedia(requiredFont, g.source.parts[strings.ToLower(target)].media) {
			return fmt.Errorf("%w: protected restricted font content type", ErrInvalid)
		}
		return nil
	})
	if err != nil {
		return &PartError{Part: name, Err: err}
	}
	return nil
}

// attributes 累计原始属性的工作和扫描字节，不依赖各语法解析器的局部计数代替共享预算
// 入参: node 原始节点
// 返回: error 预算或取消错误
func (g *compositionProtectionGraph) attributes(node *xmlElement) error {
	if err := g.budget.step(len(node.Attr)); err != nil {
		return err
	}
	for _, attribute := range node.Attr {
		if attribute.Name.Space == mcNamespace && !slices.Contains([]string{"Ignorable", "MustUnderstand", "ProcessContent", "PreserveElements", "PreserveAttributes"}, attribute.Name.Local) {
			return fmt.Errorf("%w: protected compatibility attribute", ErrUnsupported)
		}
		if err := g.budget.scan(int64(len(attribute.Value))); err != nil {
			return err
		}
	}
	if node.Name.Space == mcNamespace && !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
		return fmt.Errorf("%w: protected compatibility element", ErrUnsupported)
	}
	return nil
}

// definition 识别签署请求中的已知非资源字段，不跟随可选页面位置或猜测扩展语义
// 入参: node 原始请求节点
// 返回: error 未支持元素、属性或兼容分支错误
func (g *compositionProtectionGraph) definition(node *xmlElement) error {
	namespace := formatNamespace(g.source.format) + "/signature-definitions"
	if node.Name.Space == mcNamespace {
		if !slices.Contains([]string{"AlternateContent", "Choice", "Fallback"}, node.Name.Local) {
			return fmt.Errorf("%w: protected signature compatibility element", ErrUnsupported)
		}
		if node.Name.Local == "Choice" {
			value, _ := node.attribute("Requires")
			for _, prefix := range compatibilityWords(value) {
				if node.Namespaces[prefix] != namespace {
					return fmt.Errorf("%w: protected signature compatibility requirement", ErrUnsupported)
				}
			}
		}
	} else if node.Name.Space != namespace || !slices.Contains([]string{"SignatureDefinitions", "SignatureDefinition", "SpotLocation", "Intent", "SignBy", "SigningLocation"}, node.Name.Local) {
		return fmt.Errorf("%w: protected signature definition element", ErrUnsupported)
	}
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) || attr.Name.Space == mcNamespace || attr.Name == (xml.Name{Space: xmlNamespace, Local: "lang"}) {
			continue
		}
		allowed := node.Name.Space == mcNamespace && node.Name.Local == "Choice" && attr.Name == (xml.Name{Local: "Requires"})
		allowed = allowed || node.Name.Local == "SignatureDefinition" && attr.Name.Space == "" && slices.Contains([]string{"SpotID", "SignerName"}, attr.Name.Local)
		allowed = allowed || node.Name.Local == "SpotLocation" && attr.Name.Space == "" && slices.Contains([]string{"PageURI", "StartX", "StartY"}, attr.Name.Local)
		if !allowed {
			return fmt.Errorf("%w: protected signature definition attribute", ErrUnsupported)
		}
	}
	return nil
}

// compositionResourceAttribute 将资源引用绑定到输出位置，格式转换时统一采用部件相对路径
// 入参: source 原定义部件, destination 输出定义部件, node 所属元素, attribute 原属性, aliases 资源映射，转换时nil表示原身份, budget 累计预算, convert 是否转换引用形式
// 返回: string 输出属性值, bool 是否改变, error 引用、映射、预算或取消错误
func compositionResourceAttribute(source, destination string, node *xmlElement, attribute xml.Attr, aliases map[string]string, budget *compositionBudget, convert bool) (string, bool, error) {
	if err := budget.step(1); err != nil {
		return "", false, err
	}
	maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes, int64(math.MaxInt))
	if int64(len(attribute.Value)) > maximum {
		return "", false, fmt.Errorf("%w: composition resource attribute size", ErrLimit)
	}
	for _, value := range []string{source, destination, attribute.Value} {
		if err := budget.scan(int64(len(value))); err != nil {
			return "", false, err
		}
	}
	var err error
	source, err = opcPartName(source)
	if err != nil {
		return "", false, err
	}
	destination, err = opcPartName(destination)
	if err != nil {
		return "", false, err
	}
	references, err := resourceAttributeReferences(node, attribute)
	if err != nil {
		return "", false, err
	}
	targets := make([]string, len(references))
	var removed, replacements int64
	changed := false
	for i, reference := range references {
		if err := budget.step(1); err != nil {
			return "", false, err
		}
		part, err := resolvePart(source, reference.uri)
		if err != nil {
			return "", false, err
		}
		target, exists := aliases[strings.ToLower(part)]
		if convert && aliases == nil {
			target, exists = part, true
		}
		if !exists {
			return "", false, fmt.Errorf("%w: composition resource mapping for %s", ErrInvalid, part)
		}
		if err := budget.scan(int64(len(target))); err != nil {
			return "", false, err
		}
		target, err = opcPartName(target)
		if err != nil {
			return "", false, err
		}
		resolved, err := resolvePart(destination, reference.uri)
		if !convert && err == nil && strings.EqualFold(resolved, target) {
			continue
		}
		target, err = relativePart(destination, target)
		if err != nil {
			return "", false, err
		}
		if target == reference.uri {
			continue
		}
		if int64(len(target)) > maximum-replacements {
			return "", false, fmt.Errorf("%w: composition resource replacement size", ErrLimit)
		}
		if err := budget.scan(int64(len(target))); err != nil {
			return "", false, err
		}
		removed += int64(reference.end - reference.start)
		replacements += int64(len(target))
		targets[i], changed = target, true
	}
	size := int64(len(attribute.Value)) - removed
	if replacements > maximum-size {
		return "", false, fmt.Errorf("%w: composition resource replacement size", ErrLimit)
	}
	size += replacements
	if err := budget.step(0); err != nil {
		return "", false, err
	}
	if !changed {
		return attribute.Value, false, nil
	}
	var output strings.Builder
	output.Grow(int(size))
	position := 0
	for i, target := range targets {
		if target == "" {
			continue
		}
		output.WriteString(attribute.Value[position:references[i].start])
		output.WriteString(target)
		position = references[i].end
	}
	output.WriteString(attribute.Value[position:])
	if err := budget.step(0); err != nil {
		return "", false, err
	}
	return output.String(), true, nil
}
