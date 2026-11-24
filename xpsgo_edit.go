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
	"encoding/xml"
	"fmt"
	"maps"
	"math"
	"net/url"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

// PartChange 表示相对导入包的逻辑部件变化，Deleted为true时原部件已被删除
type PartChange struct {
	Part    string
	Deleted bool
}

// createdStoryEncoder 在分配节点前累计结构规模和输出字节，不接触页面资源
type createdStoryEncoder struct {
	namespace string
	limits    Limits
	context   context.Context
	nodes     int
	bytes     int64
}

// documentExtraction 保存单次文档提取的资源闭包和累计预算，不改变源阅读器
type documentExtraction struct {
	reader  *Reader
	output  *Package
	context context.Context
	first   int
	count   int
	queued  map[extractionPart]bool
	scanned map[string]bool
	scopes  map[string]extractionLinkScope
	targets map[string]map[string]int
	queue   []extractionPart
	work    int
}

// extractionPart 区分共享字典的所属页面，普通资源不重复展开
type extractionPart struct {
	part  string
	owner string
}

// extractionLinkScope 保存链接可寻址的页面范围，页码沿用源包的全局索引
type extractionLinkScope struct {
	first int
	count int
}

// SetPage 替换指定页面的类型化内容并更新链接目标，保留原部件名和附属关系
// 入参: ctx 取消Context，nil采用Background, document 文档序号, index 文档内页面序号, page 页面模型，Part须为空或与原名称等价
// 返回: error 序号、模型、故事绑定、取消或资源预算错误
func (p *Package) SetPage(ctx context.Context, document, index int, page *Page) error {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if page == nil || document < 0 || document >= len(p.documents) || index < 0 || index >= len(p.documents[document].Pages) {
		return fmt.Errorf("%w: document index or page", ErrInvalid)
	}
	part := p.documents[document].Pages[index].Part
	if err := p.editable(p.documents[document].Part, part); err != nil {
		return err
	}
	if page.Part != "" {
		canonical, err := opcPartName(page.Part)
		if err != nil {
			return err
		}
		if !strings.EqualFold(canonical, part) {
			return fmt.Errorf("%w: replacement changes page part", ErrInvalid)
		}
	}
	value := *page
	value.Part = part
	if p.hasStoryRelationship(part, "storyfragments") {
		return p.setStoryPage(document, index, &value, ctx)
	}
	targets, err := p.storePage(&value, ctx)
	if err != nil {
		return err
	}
	p.documents[document].Pages[index] = PageReference{Part: part, LinkTargets: targets}
	p.dirty[strings.ToLower(p.documents[document].Part)] = true
	return nil
}

// MovePage 调整页面位置并维护故事归属，页面部件名及绘制内容保持不变
// 入参: document 来源文档序号, index 来源页面序号, target 目标文档序号, position 移动完成后的页面序号
// 返回: error 序号、结构、绑定或资源错误
func (p *Package) MovePage(document, index, target, position int) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if document < 0 || document >= len(p.documents) || target < 0 || target >= len(p.documents) || index < 0 || index >= len(p.documents[document].Pages) {
		return fmt.Errorf("%w: document or page index", ErrInvalid)
	}
	count := len(p.documents[target].Pages)
	if document == target {
		count--
	}
	if position < 0 || position > count {
		return fmt.Errorf("%w: target page position", ErrInvalid)
	}
	if document == target && index == position {
		return nil
	}
	if err := p.editable(p.documents[document].Part, p.documents[target].Part, p.documents[document].Pages[index].Part); err != nil {
		return err
	}
	if p.hasStoryRelationship(p.documents[document].Part, "documentstructure") || document != target && p.hasStoryRelationship(p.documents[target].Part, "documentstructure") {
		return p.moveStoryPage(document, index, target, position)
	}
	p.movePage(document, index, target, position)
	return nil
}

// movePage 更新已校验位置的页面索引，调用方持有写锁且拥有页面切片
// 入参: document 来源文档序号, index 来源页面序号, target 目标文档序号, position 移动后的页面序号
func (p *Package) movePage(document, index, target, position int) {
	page := p.documents[document].Pages[index]
	p.documents[document].Pages = slices.Delete(p.documents[document].Pages, index, index+1)
	p.documents[target].Pages = slices.Insert(p.documents[target].Pages, position, page)
	p.dirty[strings.ToLower(p.documents[document].Part)] = true
	p.dirty[strings.ToLower(p.documents[target].Part)] = true
}

// DeletePage 删除页面及其源关系并更新故事页码，不删除共享资源
// 删除后允许暂时空文档，写出时仍要求每个文档至少有一页
// 入参: document 文档序号, index 文档内页面序号
// 返回: error 序号、结构、绑定或资源错误
func (p *Package) DeletePage(document, index int) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if document < 0 || document >= len(p.documents) || index < 0 || index >= len(p.documents[document].Pages) {
		return fmt.Errorf("%w: document or page index", ErrInvalid)
	}
	if err := p.editable(p.documents[document].Part, p.documents[document].Pages[index].Part); err != nil {
		return err
	}
	if p.hasStoryRelationship(p.documents[document].Part, "documentstructure") {
		return p.deleteStoryPage(document, index)
	}
	p.deletePage(document, index)
	return nil
}

// deletePage 删除已校验的页面及其源关系，调用方持有写锁且拥有页面切片
// 入参: document 文档序号, index 文档内页面序号
func (p *Package) deletePage(document, index int) {
	p.removePart(p.documents[document].Pages[index].Part)
	p.documents[document].Pages = slices.Delete(p.documents[document].Pages, index, index+1)
	p.pageCount--
	p.dirty[strings.ToLower(p.documents[document].Part)] = true
}

// MoveDocument 调整文档序列中的顺序，不改变文档部件和页面内容
// 入参: index 来源文档序号, position 移动完成后的文档序号
// 返回: error 序号错误
func (p *Package) MoveDocument(index, position int) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if index < 0 || index >= len(p.documents) || position < 0 || position >= len(p.documents) {
		return fmt.Errorf("%w: document index", ErrInvalid)
	}
	if index == position {
		return nil
	}
	if err := p.editable(p.sequence); err != nil {
		return err
	}
	document := p.documents[index]
	p.documents = slices.Delete(p.documents, index, index+1)
	p.documents = slices.Insert(p.documents, position, document)
	p.dirty[strings.ToLower(p.sequence)] = true
	return nil
}

// DeleteDocument 删除指定文档及其全部页面和源关系，不隐式删除共享资源
// 入参: index 文档序号
// 返回: error 序号错误
func (p *Package) DeleteDocument(index int) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if index < 0 || index >= len(p.documents) {
		return fmt.Errorf("%w: document index", ErrInvalid)
	}
	if err := p.editable(p.documents[index].Part, p.sequence); err != nil {
		return err
	}
	for _, page := range p.documents[index].Pages {
		if err := p.editable(page.Part); err != nil {
			return err
		}
	}
	for _, page := range p.documents[index].Pages {
		p.removePart(page.Part)
	}
	p.pageCount -= len(p.documents[index].Pages)
	p.removePart(p.documents[index].Part)
	p.documents = slices.Delete(p.documents, index, index+1)
	p.dirty[strings.ToLower(p.sequence)] = true
	return nil
}

// DeletePart 删除资源或扩展部件及其源关系，不接受由固定布局模型管理的名称
// 不改写其他部件引用，遗漏的必需资源会在写出前报告
// 入参: part 部件URI
// 返回: error 名称、部件不存在或受模型管理错误
func (p *Package) DeletePart(part string) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	canonical, err := opcPartName(part)
	if err != nil {
		return err
	}
	key := strings.ToLower(canonical)
	if p.managed(canonical) || opcRelationshipName(canonical) {
		return fmt.Errorf("%w: managed package part", ErrInvalid)
	}
	if _, exists := p.parts[key]; !exists {
		return fmt.Errorf("%w: missing package part %s", ErrInvalid, canonical)
	}
	if err := p.editable(canonical); err != nil {
		return err
	}
	p.removePart(canonical)
	return nil
}

// removePart 移除模型部件并释放名称索引，必须持有模型写锁
// 入参: part 已登记的部件名称
func (p *Package) removePart(part string) {
	key := strings.ToLower(part)
	p.total -= int64(len(p.parts[key].data))
	delete(p.parts, key)
	delete(p.layout, key)
	p.unregisterName(part)
	delete(p.relations, key)
	p.total -= p.relationSizes[key]
	delete(p.relationSizes, key)
	name := createdRelationshipPart(part)
	relationKey := strings.ToLower(name)
	p.total -= int64(len(p.parts[relationKey].data))
	delete(p.parts, relationKey)
	p.unregisterName(name)
	p.dirty[key], p.dirtyRels[key] = true, true
}

// editable 检查导入文档中受字体嵌入许可保护的部件，不把签名变化等同于禁止编辑
// 入参: parts 将要修改的部件名
// 返回: error 受限字体引用导致的编辑限制
func (p *Package) editable(parts ...string) error {
	for _, part := range parts {
		if p.protected[strings.ToLower(part)] {
			return &PartError{Part: part, Err: ErrRestricted}
		}
	}
	return nil
}

// unregisterName 释放部件及其祖先的占用，不删除仍由其他部件占用的父路径
// 入参: part 已登记的部件名称
func (p *Package) unregisterName(part string) {
	key := strings.ToLower(part)
	if !p.names[key] {
		return
	}
	delete(p.names, key)
	for slash := strings.LastIndexByte(key, '/'); slash > 0; slash = strings.LastIndexByte(key[:slash], '/') {
		parent := key[:slash]
		p.parents[parent]--
		if p.parents[parent] == 0 {
			delete(p.parents, parent)
		}
	}
}

// SetPrintTicket 替换固定布局部件的打印票据关联，保留其他关系及已有关系ID，空目标仅移除关联
// 目标部件须已通过SetPart添加，不删除可能共用的票据部件，结构在生成阅读器或写出时校验
// 入参: source 源部件，空字符串表示文档序列, part 已通过SetPart添加的票据部件，空字符串移除关联
// 返回: error 来源、目标、关系或资源错误，失败时不改变包
func (p *Package) SetPrintTicket(source, part string) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if source == "" {
		source = p.sequence
	}
	canonical, err := opcPartName(source)
	if err != nil {
		return err
	}
	if p.printTicketScope(canonical) == PrintScopeUnknown {
		return fmt.Errorf("%w: print ticket source", ErrInvalid)
	}
	if part != "" {
		part, err = opcPartName(part)
		if err != nil {
			return err
		}
		if opcRelationshipName(part) || !p.names[strings.ToLower(part)] {
			return fmt.Errorf("%w: print ticket part", ErrInvalid)
		}
	}
	key := strings.ToLower(canonical)
	relations := slices.Clone(p.relations[key])
	if _, err := printTicketTarget(canonical, relations, p.format); err != nil {
		return err
	}
	kind := formatNamespace(p.format) + "/printticket"
	index := -1
	for i, relation := range relations {
		if relation.Type == kind {
			index = i
			break
		}
	}
	if part == "" {
		if index < 0 {
			return nil
		}
		relations = slices.Delete(relations, index, index+1)
	} else if index < 0 {
		nextID := createdRelationshipIDs(append(slices.Clone(relations), p.originalRels[key]...))
		relations = append(relations, Relationship{ID: nextID(), Type: kind, Target: part, TargetMode: "Internal"})
	} else {
		relations[index].Target, relations[index].TargetMode = part, "Internal"
	}
	return p.setRelationships(canonical, relations)
}

// printTicketScope 查找当前模型中的票据关联层级，不依赖尚未生成的布局XML
// 入参: source 已规范化源部件
// 返回: PrintScope 关联层级，非模型部件返回Unknown
func (p *Package) printTicketScope(source string) PrintScope {
	if strings.EqualFold(source, p.sequence) {
		return PrintScopeJob
	}
	for _, document := range p.documents {
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

// SetSignatureDefinitions 替换固定文档的签名定义关联，保留其他关系及可复用关系ID，空列表仅移除关联
// 目标部件须已通过SetPart存入模型，不删除可能共用的请求部件，内容在生成阅读器或写出时校验
// 入参: document 从零开始的固定文档序号, parts 请求部件URI列表，等价目标合并
// 返回: error 序号、目标、关系或资源错误，失败时不改变包
func (p *Package) SetSignatureDefinitions(document int, parts []string) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if document < 0 || document >= len(p.documents) {
		return fmt.Errorf("%w: signature definition document index", ErrInvalid)
	}
	source := p.documents[document].Part
	kind := formatNamespace(p.format) + "/signature-definitions"
	key := strings.ToLower(source)
	var result []Relationship
	existing := make(map[string]string)
	for _, relation := range p.relations[key] {
		if relation.Type != kind {
			result = append(result, relation)
			continue
		}
		if relation.TargetMode == "Internal" {
			if target, err := resolvePart(source, relation.Target); err == nil && existing[strings.ToLower(target)] == "" {
				existing[strings.ToLower(target)] = relation.ID
			}
		}
	}
	used := make(map[string]bool)
	nextID := createdRelationshipIDs(append(slices.Clone(p.relations[key]), p.originalRels[key]...))
	for _, name := range parts {
		part, err := opcPartName(name)
		if err != nil {
			return err
		}
		partKey := strings.ToLower(part)
		if used[partKey] {
			continue
		}
		value, exists := p.parts[partKey]
		if !exists || !strings.EqualFold(value.media, fixedContentType("signaturedefinitions")) {
			return fmt.Errorf("%w: signature definition target part", ErrInvalid)
		}
		id := existing[partKey]
		if id == "" {
			id = nextID()
		}
		used[partKey] = true
		result = append(result, Relationship{ID: id, Type: kind, Target: value.name, TargetMode: "Internal"})
	}
	return p.setRelationships(source, result)
}

// SetThumbnail 替换包级或页面缩略图关联，目标需由SetPart添加，空目标只移除关联
// 按显式关系替换规则保留其他已知关系，已有缩略图沿用首个关系ID，不删除可共享图像
// 入参: ctx 取消Context，nil采用Background, source 包根空值或/，或已有页面, part JPEG/PNG部件，空值取消关联
// 返回: error 来源、目标、图像、许可、资源或取消错误，失败不改变包
func (p *Package) SetThumbnail(ctx context.Context, source, part string) error {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if err := checkContext(ctx); err != nil {
		return err
	}
	if source == "" {
		source = "/"
	}
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return err
		}
		source = canonical
		if p.printTicketScope(source) != PrintScopePage {
			return fmt.Errorf("%w: thumbnail source is not a fixed page", ErrInvalid)
		}
	}
	if part != "" {
		canonical, err := opcPartName(part)
		if err != nil {
			return err
		}
		part = canonical
		value, exists := p.parts[strings.ToLower(part)]
		if !exists || !thumbnailMedia(value.media) {
			return fmt.Errorf("%w: thumbnail requires existing JPEG or PNG part", ErrInvalid)
		}
		if _, err := decodeRasterImageContext(ctx, value.data, value.media, p.maxImagePixels); err != nil {
			return &PartError{Part: part, Err: err}
		}
	}
	key := strings.ToLower(source)
	relations := slices.Clone(p.relations[key])
	id := ""
	retained := make([]Relationship, 0, len(relations)+1)
	for _, relation := range relations {
		if relation.Type != thumbnailRelationship {
			retained = append(retained, relation)
		} else if id == "" {
			id = relation.ID
		}
	}
	if part != "" {
		if id == "" {
			id = createdRelationshipIDs(append(slices.Clone(relations), p.originalRels[key]...))()
		}
		retained = append(retained, Relationship{ID: id, Type: thumbnailRelationship, Target: part, TargetMode: "Internal"})
	}
	q := p.signingCopy()
	if err := q.setRelationships(source, retained); err != nil {
		return err
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.dirty, p.dirtyRels = q.names, q.parents, q.allocated, q.dirty, q.dirtyRels
	return nil
}

// SetDiscardControl 替换包根释放提示关联，空目标移除关联但不删除提示部件或执行资源释放
// 目标需由SetPart添加，提示引用有效部件及已有页面；按显式关系替换规则保留其他已知关系与ID
// 入参: ctx 取消Context，nil采用Background, part 提示部件名，空值移除关联
// 返回: error 目标、提示、关系、许可、预算或取消错误，失败不改变包
func (p *Package) SetDiscardControl(ctx context.Context, part string) error {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	if err := checkContext(ctx); err != nil {
		return err
	}
	if part != "" {
		canonical, err := opcPartName(part)
		if err != nil {
			return err
		}
		part = canonical
		value, present := p.parts[strings.ToLower(part)]
		if !present || !strings.EqualFold(value.media, fixedContentType("discard-control")) {
			return fmt.Errorf("%w: discard control part", ErrInvalid)
		}
		control, err := readDiscardControl(value.data, part, p.format, p.limits, ctx)
		if err != nil {
			return err
		}
		if control.Ignored != 0 {
			return fmt.Errorf("%w: invalid produced discard reference", ErrInvalid)
		}
		pages := make(map[string]bool)
		for _, doc := range p.documents {
			for _, page := range doc.Pages {
				pages[strings.ToLower(page.Part)] = true
			}
		}
		for _, hint := range control.Hints {
			if err := checkContext(ctx); err != nil {
				return err
			}
			if !p.names[strings.ToLower(hint.Target)] || !pages[strings.ToLower(hint.SentinelPage)] {
				return fmt.Errorf("%w: discard resource or sentinel page is absent", ErrInvalid)
			}
		}
	}
	relations := slices.Clone(p.relations["/"])
	if _, err := discardControlTarget(relations, p.format); err != nil {
		return err
	}
	kind := formatNamespace(p.format) + "/discard-control"
	index := -1
	for i, relation := range relations {
		if relation.Type == kind {
			index = i
			break
		}
	}
	if part == "" {
		if index < 0 {
			return nil
		}
		relations = slices.Delete(relations, index, index+1)
	} else if index < 0 {
		nextID := createdRelationshipIDs(append(slices.Clone(relations), p.originalRels["/"]...))
		relations = append(relations, Relationship{ID: nextID(), Type: kind, Target: part, TargetMode: "Internal"})
	} else {
		relations[index].Target, relations[index].TargetMode = part, "Internal"
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	q := p.signingCopy()
	if err := q.setRelationships("/", relations); err != nil {
		return err
	}
	if part != "" && p.pageCount != 0 {
		view, err := q.reader(ctx)
		if err != nil {
			return err
		}
		view.Close()
	}
	if err := checkContext(ctx); err != nil {
		return err
	}
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.dirty, p.dirtyRels = q.names, q.parents, q.allocated, q.dirty, q.dirtyRels
	return nil
}

// modelRelationship 判断关系是否由固定布局和资源闭包管理，只匹配当前文档格式
// 入参: relation 关系
// 返回: bool 是否为模型管理关系
func (p *Package) modelRelationship(relation Relationship) bool {
	namespace := formatNamespace(p.format)
	return relation.Type == namespace+"/fixedrepresentation" || relation.Type == namespace+"/required-resource" || relation.Type == namespace+"/restricted-font"
}

// composeRelationships 合成源部件关系标记，未修改时保留原文及模型关系，修改时输出消费分支标准关系
// 入参: pkg 输出索引, source 源部件或包根, wanted 当前必需的模型关系, ctx 取消Context
// 返回: error URI、关系或资源错误
func (p *Package) composeRelationships(pkg *packageReader, source string, wanted []Relationship, ctx context.Context) error {
	key := strings.ToLower(source)
	name := createdRelationshipPart(source)
	relationKey := strings.ToLower(name)
	previous := p.originalRels[key]
	original, hasOriginal := p.original[relationKey]
	if current, present := p.parts[relationKey]; present && p.dirty[relationKey] && !p.dirtyRels[key] {
		var err error
		previous, err = parseRelationshipMarkup(source, current.data, p.limits, ctx)
		if err != nil {
			return err
		}
		original, hasOriginal = current, true
	}
	explicit := p.relations[key]
	byID := make(map[string]Relationship, len(explicit))
	for _, relation := range explicit {
		byID[relation.ID] = relation
	}
	needed := make(map[string]bool, len(wanted))
	for _, relation := range wanted {
		identity, err := relationshipIdentity(source, relation)
		if err != nil {
			return err
		}
		needed[identity] = true
	}
	nextID := createdRelationshipIDs(append(slices.Clone(explicit), previous...))
	seen := make(map[string]bool)
	var result []Relationship
	for _, old := range previous {
		if !p.modelRelationship(old) {
			if value, present := byID[old.ID]; present {
				result = append(result, value)
				delete(byID, old.ID)
			}
			continue
		}
		identity, err := relationshipIdentity(source, old)
		if err != nil {
			return err
		}
		if !needed[identity] && p.dirty[key] {
			continue
		}
		if _, conflict := byID[old.ID]; conflict {
			old.ID = nextID()
		}
		result = append(result, old)
		seen[identity] = true
	}
	for _, relation := range explicit {
		if _, present := byID[relation.ID]; present {
			result = append(result, relation)
		}
	}
	nextID = createdRelationshipIDs(result)
	for _, relation := range wanted {
		identity, err := relationshipIdentity(source, relation)
		if err != nil {
			return err
		}
		if !seen[identity] {
			relation.ID = nextID()
			result = append(result, relation)
			seen[identity] = true
		}
	}
	if !p.dirtyRels[key] && slices.Equal(result, previous) {
		if hasOriginal {
			createdPut(pkg, original.name, original.media, original.data)
			return nil
		}
	}
	if !p.dirtyRels[key] && len(result) > len(previous) && slices.Equal(result[:len(previous)], previous) {
		if hasOriginal {
			data, err := appendRelationshipMarkup(source, original.data, result[len(previous):], p.limits, ctx)
			if err != nil {
				return err
			}
			createdPut(pkg, original.name, original.media, data)
			actual, err := pkg.relationships(source)
			if err != nil {
				return err
			}
			if !slices.Equal(actual, result) {
				return fmt.Errorf("%w: appended relationships changed interpretation", ErrInvalid)
			}
			return nil
		}
	}
	if len(result) == 0 {
		delete(pkg.parts, relationKey)
		delete(pkg.names, relationKey)
		delete(pkg.data, relationKey)
		delete(pkg.overrides, relationKey)
		return nil
	}
	_, err := createdPutRelations(pkg, source, result, p.limits, ctx)
	return err
}

// relationshipIdentity 计算模型关系的类型及包内部件身份，不把不同URI拼写误判为不同资源
// 入参: source 来源部件, relation 包内模型关系
// 返回: string 类型与目标组成的键, error 关系目标错误
func relationshipIdentity(source string, relation Relationship) (string, error) {
	if relation.TargetMode != "" && relation.TargetMode != "Internal" {
		return "", fmt.Errorf("%w: external model relationship", ErrInvalid)
	}
	part, err := resolvePart(source, relation.Target)
	if err != nil {
		return "", err
	}
	return relation.Type + "\n" + strings.ToLower(part), nil
}

// originalTypes 检查逻辑部件集合和内容类型未改变时是否可以保留原类型流
// 入参: pkg 已构造部件索引
// 返回: []byte 原类型流，无可保留内容时为nil
func (p *Package) originalTypes(pkg *packageReader) []byte {
	if len(p.original) != len(pkg.parts)+1 {
		return nil
	}
	for key := range pkg.parts {
		old, present := p.original[key]
		if !present || old.media != pkg.overrides[key] {
			return nil
		}
	}
	return p.original[strings.ToLower(opcTypesName)].data
}

// changedResources 检查页面及其依赖是否被修改，未改变资源的导入页面沿用消费规则
// 入参: graph 完整页面资源图
// 返回: bool 是否需要生产者资源校验, error 依赖错误
func (p *Package) changedResources(graph *resourceGraph) (bool, error) {
	if p.original == nil || p.dirty[strings.ToLower(graph.PagePart)] {
		return true, nil
	}
	dependencies, err := collectRequiredResources(graph, p.format)
	if err != nil {
		return false, err
	}
	for _, resource := range dependencies {
		if p.dirty[strings.ToLower(resource.Part)] {
			return true, nil
		}
	}
	return false, nil
}

// Edit 复制已有包为独立编辑模型，不修改源数据，未修改的XML、关系、签名和扩展部件保留原字节
// 字体编辑限制按受限字体关系单独校验，缺少必需Restricted Font关系时返回错误
// 入参: ctx 取消Context，nil采用Background, options 模型资源选项，nil沿用读取上限
// 返回: *Package 独立编辑模型, error 封装、资源、字体编辑规则或取消错误
func (r *Reader) Edit(ctx context.Context, options *PackageOptions) (*Package, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	configuration := PackageOptions{Limits: r.limits}
	if options != nil {
		configuration.Limits = mergeLimits(configuration.Limits, options.Limits)
		configuration.MaxImagePixels = options.MaxImagePixels
	}
	p, err := NewPackage(r.format, &configuration)
	if err != nil {
		return nil, err
	}
	p.unregisterName(p.sequence)
	p.unregisterName("/_rels/.rels")
	clear(p.layout)
	p.sequence = r.sequence
	p.comment = r.pkg.comment
	p.original = make(map[string]packagePart)
	p.originalRels = make(map[string][]Relationship)
	if len(r.pkg.parts) > p.limits.MaxPartCount {
		return nil, fmt.Errorf("%w: imported package part count", ErrLimit)
	}
	keys := slices.Sorted(maps.Keys(r.pkg.parts))
	for _, key := range keys {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		limit := min(p.limits.MaxPartBytes, p.limits.MaxPackageBytes-p.total)
		if key == strings.ToLower(opcTypesName) || opcRelationshipName(r.pkg.names[key]) {
			limit = min(limit, p.limits.MaxMetadataBytes)
		}
		data, err := r.pkg.readItems(key, limit)
		if err != nil {
			return nil, err
		}
		if key == strings.ToLower(opcTypesName) {
			metadata := &packageReader{limits: p.limits, defaults: make(map[string]string), overrides: make(map[string]string)}
			if err := metadata.parseContentTypes(data); err != nil {
				return nil, err
			}
		}
		value := packagePart{name: r.pkg.names[key], data: data}
		value.items, err = r.pkg.importItems(key, data)
		if err != nil {
			return nil, err
		}
		if key != strings.ToLower(opcTypesName) {
			value.media, err = r.pkg.contentType(value.name)
			if err != nil {
				return nil, err
			}
			p.parts[key] = value
			p.registerName(value.name)
		}
		p.original[key] = value
		p.total += int64(len(data))
	}
	view := &Reader{pkg: p.partReader(), format: p.format, limits: p.limits}
	if err := view.readSequence(); err != nil {
		return nil, err
	}
	p.documents, p.pageCount = view.documents, len(view.pages)
	p.layout[strings.ToLower(p.sequence)] = true
	for _, document := range p.documents {
		p.layout[strings.ToLower(document.Part)] = true
		for _, page := range document.Pages {
			p.layout[strings.ToLower(page.Part)] = true
		}
	}
	for _, key := range keys {
		value := p.original[key]
		if !opcRelationshipName(value.name) {
			continue
		}
		source := relationshipSource(value.name)
		relations, err := view.pkg.relationships(source)
		if err != nil {
			return nil, err
		}
		source = strings.ToLower(source)
		p.originalRels[source] = relations
		for _, relation := range relations {
			if !p.modelRelationship(relation) {
				p.relations[source] = append(p.relations[source], relation)
			}
		}
	}
	if err := p.protectImported(view, ctx); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return p, nil
}

// Changes 返回已校验快照相对导入包的逻辑部件变化，新建包的所有部件视为新增
// 内容类型流不计入部件变化列表，且不删除未修改的签名部件
// 入参: ctx 取消Context，nil采用Background
// 返回: []PartChange 按部件名排列的变化, error 快照或取消错误
func (p *Package) Changes(ctx context.Context) ([]PartChange, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	r, err := p.snapshot().reader(ctx)
	if err != nil {
		return nil, err
	}
	defer r.Close()
	var result []PartChange
	for key, data := range r.pkg.data {
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		old, exists := p.original[key]
		if !exists || old.name != r.pkg.names[key] || old.media != r.pkg.overrides[key] || !bytes.Equal(old.data, data) {
			result = append(result, PartChange{Part: r.pkg.names[key]})
		}
	}
	for key, value := range p.original {
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if _, exists := r.pkg.data[key]; !exists {
			result = append(result, PartChange{Part: value.name, Deleted: true})
		}
	}
	slices.SortFunc(result, func(a, b PartChange) int { return strings.Compare(a.Part, b.Part) })
	return result, nil
}

// partReader 为当前不可变部件建立独立内存索引，不复制已由模型拥有的字节
// 返回: *packageReader 独立索引
func (p *Package) partReader() *packageReader {
	pkg := &packageReader{parts: make(map[string][]*zip.File), names: make(map[string]string), data: make(map[string][]byte), original: p.original, comment: p.comment, defaults: make(map[string]string), overrides: make(map[string]string), limits: p.limits}
	for _, value := range p.parts {
		createdPut(pkg, value.name, value.media, value.data)
	}
	return pkg
}

// importItems 复制原条目元数据及分片范围，已重写的内存部件不沿用旧分片
// 入参: key 逻辑部件索引, data 已校验的完整数据
// 返回: []packageItem 独立条目头, error 扩展字段或范围错误
func (p *packageReader) importItems(key string, data []byte) ([]packageItem, error) {
	var result []packageItem
	if p.data != nil {
		old, exists := p.original[key]
		if exists && bytes.Equal(old.data, data) {
			result = slices.Clone(old.items)
			for index := range result {
				result[index].header.Extra = bytes.Clone(result[index].header.Extra)
			}
		}
		return result, nil
	}
	start := 0
	for _, file := range p.parts[key] {
		header, err := writeEntryHeader(file, CompressionDeflate)
		if err != nil {
			return nil, err
		}
		if file.UncompressedSize64 > uint64(len(data)-start) {
			return nil, fmt.Errorf("%w: imported ZIP piece range", ErrInvalid)
		}
		end := start + int(file.UncompressedSize64)
		result = append(result, packageItem{header: header, start: start, end: end})
		start = end
	}
	if start != len(data) {
		return nil, fmt.Errorf("%w: imported ZIP piece size", ErrInvalid)
	}
	return result, nil
}

// relationshipSource 根据已校验的关系部件名还原源部件，不通过文件系统解析路径
// 入参: part 关系部件名
// 返回: string 源部件或包根/
func relationshipSource(part string) string {
	if strings.EqualFold(part, "/_rels/.rels") {
		return "/"
	}
	slash := strings.LastIndexByte(part, '/')
	return part[:slash-len("/_rels")] + "/" + part[slash+1:len(part)-len(".rels")]
}

// protectImported 检查导入文档的预览打印字体关系，将受限文档及其传递引用资源纳入写保护
// 入参: r 导入部件的独立视图, ctx 取消Context
// 返回: error 页面、字体、关系或取消错误
func (p *Package) protectImported(r *Reader, ctx context.Context) error {
	fonts := fontCache{pkg: r.pkg, data: make(map[string][]byte), faces: make(map[fontCacheKey]*fontSource), remaining: p.limits.MaxPackageBytes, maxFaces: p.limits.MaxPartCount}
	index := 0
	for _, document := range r.documents {
		docKey := strings.ToLower(document.Part)
		restricted := make(map[string]bool)
		for _, relation := range p.originalRels[docKey] {
			if relation.Type != formatNamespace(p.format)+"/restricted-font" {
				continue
			}
			if relation.TargetMode != "Internal" {
				return &PartError{Part: document.Part, Err: fmt.Errorf("%w: external restricted font", ErrInvalid)}
			}
			part, err := resolvePart(document.Part, relation.Target)
			if err != nil {
				return err
			}
			restricted[strings.ToLower(part)] = true
		}
		resources := []string{document.Part}
		queued := map[string]bool{docKey: true}
		enqueue := func(part string) error {
			key := strings.ToLower(part)
			if !queued[key] {
				if len(queued) >= p.limits.MaxPartCount {
					return fmt.Errorf("%w: protected resource closure", ErrLimit)
				}
				queued[key] = true
				resources = append(resources, part)
			}
			return nil
		}
		for range document.Pages {
			if err := checkContext(ctx); err != nil {
				return err
			}
			page, err := r.readPage(index)
			if err != nil {
				return err
			}
			index++
			if len(restricted) != 0 {
				if err := enqueue(page.Part); err != nil {
					return err
				}
			}
			dependencies, err := collectRequiredResources(page.resources, p.format)
			if err != nil {
				return err
			}
			for _, dependency := range dependencies {
				if len(restricted) != 0 {
					if err := enqueue(dependency.Part); err != nil {
						return err
					}
				}
			}
			for _, node := range page.resources.Nodes {
				if node.Name.Local != "Glyphs" {
					continue
				}
				if err := checkContext(ctx); err != nil {
					return err
				}
				text, _ := node.attribute("FontUri")
				uri, face, present, err := ParseFontURI(strings.Trim(text, " \t\r\n"))
				if err != nil {
					return err
				}
				part, err := resolvePart(page.resources.Parts[node], uri)
				if err != nil {
					return err
				}
				font, err := fonts.load(&Glyphs{FontPart: part, CollectionIndex: face, HasCollectionIndex: present})
				if err != nil {
					return err
				}
				if font.metrics.os2 != nil && font.metrics.os2.fsType&4 != 0 && !restricted[strings.ToLower(part)] {
					return &PartError{Part: document.Part, Err: fmt.Errorf("%w: preview and print font lacks restricted font relationship", ErrInvalid)}
				}
			}
		}
		if len(restricted) == 0 {
			continue
		}
		visited := make(map[string]bool)
		for position := 0; position < len(resources); position++ {
			if err := checkContext(ctx); err != nil {
				return err
			}
			key := strings.ToLower(resources[position])
			if visited[key] {
				continue
			}
			visited[key], p.protected[key] = true, true
			for _, relation := range p.originalRels[key] {
				if relation.TargetMode == "Internal" {
					target, err := resolvePart(resources[position], relation.Target)
					if err != nil {
						return err
					}
					if !visited[strings.ToLower(target)] {
						if err := enqueue(target); err != nil {
							return err
						}
					}
				}
			}
		}
	}
	return nil
}

// SetRelationships 替换源部件的附属关系，空列表删除附属关系，不复制被忽略的兼容性标记
// 固定表示、必需资源和受限字体关系由模型生成，不能通过此方法覆盖
// 入参: source 已有源部件或包根/, relations 关系列表，目标资源可在写出前补齐
// 返回: error 来源、关系结构、名称冲突或预算错误
func (p *Package) SetRelationships(source string, relations []Relationship) error {
	if err := p.lock(); err != nil {
		return err
	}
	defer p.mu.Unlock()
	return p.setRelationships(source, relations)
}

// setRelationships 在调用方持有写锁时校验并原子替换显式关系
// 入参: source 源部件或包根, relations 关系列表
// 返回: error 来源、关系或预算错误，失败时不改变包
func (p *Package) setRelationships(source string, relations []Relationship) error {
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return err
		}
		if opcRelationshipName(canonical) || !p.names[strings.ToLower(canonical)] {
			return fmt.Errorf("%w: relationship source", ErrInvalid)
		}
		source = canonical
	}
	if err := p.editable(source); err != nil {
		return err
	}
	if part, err := printTicketTarget(source, relations, p.format); err != nil {
		return err
	} else if part != "" && p.printTicketScope(source) == PrintScopeUnknown {
		return fmt.Errorf("%w: print ticket source", ErrInvalid)
	}
	for _, relation := range relations {
		if relation.Type == opcCoreRel && source != "/" {
			return fmt.Errorf("%w: core properties relationship source", ErrInvalid)
		}
		for _, namespace := range []string{xpsNamespace, openXPSNamespace} {
			if relation.Type == namespace+"/fixedrepresentation" || relation.Type == namespace+"/required-resource" || relation.Type == namespace+"/restricted-font" {
				return fmt.Errorf("%w: model-managed relationship", ErrInvalid)
			}
		}
	}
	key := strings.ToLower(source)
	name := createdRelationshipPart(source)
	relationKey := strings.ToLower(name)
	rawSize := int64(len(p.parts[relationKey].data))
	if len(relations) == 0 {
		keep := false
		for _, relation := range p.originalRels[key] {
			keep = keep || p.modelRelationship(relation)
		}
		if source != "/" && !keep {
			p.unregisterName(name)
		}
		delete(p.parts, relationKey)
		delete(p.relations, key)
		p.total -= p.relationSizes[key] + rawSize
		delete(p.relationSizes, key)
		p.dirtyRels[key] = true
		return nil
	}
	if source != "/" && !p.names[relationKey] {
		if len(p.names)+1 >= p.limits.MaxPartCount {
			return fmt.Errorf("%w: package part count", ErrLimit)
		}
		if err := p.availableName(name); err != nil {
			return err
		}
	}
	pkg := &packageReader{parts: map[string][]*zip.File{key: nil}, names: make(map[string]string), data: make(map[string][]byte), overrides: make(map[string]string), limits: p.limits}
	validated, err := createdPutRelations(pkg, source, relations, p.limits, nil)
	if err != nil {
		return err
	}
	size := int64(len(pkg.data[relationKey]))
	remaining := p.limits.MaxPackageBytes - (p.total - p.relationSizes[key] - rawSize)
	if size > remaining {
		return fmt.Errorf("%w: package byte budget", ErrLimit)
	}
	p.total += size - p.relationSizes[key] - rawSize
	delete(p.parts, relationKey)
	p.relationSizes[key] = size
	p.relations[key] = validated
	p.dirtyRels[key] = true
	if source != "/" && !p.names[relationKey] {
		p.registerName(name)
	}
	return nil
}

// Relationships 返回显式保存的附属关系副本，自动生成的关系通过Reader读取
// 入参: source 已有源部件或包根/
// 返回: []Relationship 关系副本, error 来源错误
func (p *Package) Relationships(source string) ([]Relationship, error) {
	if err := p.lock(); err != nil {
		return nil, err
	}
	defer p.mu.Unlock()
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return nil, err
		}
		if opcRelationshipName(canonical) || !p.names[strings.ToLower(canonical)] {
			return nil, fmt.Errorf("%w: relationship source", ErrInvalid)
		}
		source = canonical
	}
	return slices.Clone(p.relations[strings.ToLower(source)]), nil
}

// appendRelationshipMarkup 向原关系XML追加消费分支的标准关系，移除忽略内容并保留输入编码
// 入参: source 源部件或包根, original 原XML, relations 新增关系, limits 资源上限, ctx 取消Context
// 返回: []byte 更新后的关系XML, error XML、编码、资源或取消错误
func appendRelationshipMarkup(source string, original []byte, relations []Relationship, limits Limits, ctx context.Context) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	maximum := min(limits.MaxMetadataBytes, limits.MaxPartBytes)
	if int64(len(original)) > maximum {
		return nil, fmt.Errorf("%w: relationship XML byte budget", ErrLimit)
	}
	previous, err := parseRelationshipMarkup(source, original, limits, ctx)
	if err != nil {
		return nil, err
	}
	if len(relations) == 0 {
		return bytes.Clone(original), nil
	}
	if len(relations) >= limits.MaxXMLNodes-len(previous) {
		return nil, fmt.Errorf("%w: relationship XML complexity", ErrLimit)
	}
	data, err := createdRelationshipMarkup(append(previous, relations...), limits, ctx)
	if err != nil {
		return nil, err
	}
	data, err = restoreXMLEncoding(original, data, maximum, ctx)
	if err != nil {
		return nil, err
	}
	if _, err := parseRelationshipMarkup(source, data, limits, ctx); err != nil {
		return nil, err
	}
	return data, checkContext(ctx)
}

// setRelationshipMarkup 保存已校验的完整关系标记并同步显式关系索引，调用方须持有包写锁
// 入参: source 源部件或包根, data 原编码关系XML, ctx 取消Context
// 返回: error 来源、标记、名称、编辑许可或资源错误，失败时不改变包
func (p *Package) setRelationshipMarkup(source string, data []byte, ctx context.Context) error {
	if source != "/" {
		canonical, err := opcPartName(source)
		if err != nil {
			return err
		}
		if opcRelationshipName(canonical) || !p.names[strings.ToLower(canonical)] {
			return fmt.Errorf("%w: relationship markup source", ErrInvalid)
		}
		source = canonical
	}
	if err := p.editable(source); err != nil {
		return err
	}
	if int64(len(data)) > min(p.limits.MaxPartBytes, p.limits.MaxMetadataBytes) {
		return fmt.Errorf("%w: relationship markup byte budget", ErrLimit)
	}
	relations, err := parseRelationshipMarkup(source, data, p.limits, ctx)
	if err != nil {
		return err
	}
	if part, err := printTicketTarget(source, relations, p.format); err != nil {
		return err
	} else if part != "" && p.printTicketScope(source) == PrintScopeUnknown {
		return fmt.Errorf("%w: print ticket source", ErrInvalid)
	}
	key := strings.ToLower(source)
	name := createdRelationshipPart(source)
	relationKey := strings.ToLower(name)
	if !p.names[relationKey] {
		if len(p.names)+1 >= p.limits.MaxPartCount {
			return fmt.Errorf("%w: relationship markup part count", ErrLimit)
		}
		if err := p.availableName(name); err != nil {
			return err
		}
	}
	size := p.total - int64(len(p.parts[relationKey].data)) - p.relationSizes[key]
	if int64(len(data)) > p.limits.MaxPackageBytes-size {
		return fmt.Errorf("%w: relationship markup package budget", ErrLimit)
	}
	var explicit []Relationship
	for _, relation := range relations {
		if relation.Type == opcCoreRel && source != "/" {
			return fmt.Errorf("%w: core properties relationship source", ErrInvalid)
		}
		if !p.modelRelationship(relation) {
			explicit = append(explicit, relation)
		}
	}
	owned := bytes.Clone(data)
	if err := checkContext(ctx); err != nil {
		return err
	}
	p.parts[relationKey] = packagePart{name: name, media: opcRelsType, data: owned}
	p.relations[key] = explicit
	delete(p.relationSizes, key)
	p.total = size + int64(len(owned))
	p.dirty[relationKey], p.dirtyRels[key] = true, false
	if !p.names[relationKey] {
		p.registerName(name)
	}
	return nil
}

// parseRelationshipMarkup 沿用OPC关系与兼容性校验，使用独立索引读取指定关系标记
// 入参: source 已规范化源部件或包根, data 完整关系XML, limits 资源上限, ctx 取消Context
// 返回: []Relationship 当前消费分支的关系, error 标记或取消错误
func parseRelationshipMarkup(source string, data []byte, limits Limits, ctx context.Context) ([]Relationship, error) {
	if _, err := decodeXMLVisit(data, limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) }); err != nil {
		return nil, err
	}
	name := createdRelationshipPart(source)
	key := strings.ToLower(name)
	pkg := &packageReader{parts: map[string][]*zip.File{strings.ToLower(source): nil, key: nil}, names: map[string]string{key: name}, data: map[string][]byte{key: data}, limits: limits}
	relations, err := pkg.relationships(source)
	if err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return relations, nil
}

// hasStoryRelationship 检查当前显式关系是否关联指定文档结构，不按资源媒体类型猜测用途
// 入参: source 来源部件, kind 结构关系类型
// 返回: bool 是否存在当前方言的关联
func (p *Package) hasStoryRelationship(source, kind string) bool {
	for _, relation := range p.relations[strings.ToLower(source)] {
		if relation.Type == formatNamespace(p.format)+"/"+kind {
			return true
		}
	}
	return false
}

// editStoryReader 为结构编辑建立当前部件与文档索引，不要求其他文档已经补齐页面和资源
// 入参: ctx 取消Context
// 返回: *Reader 独立索引, error 关系或取消错误
func (p *Package) editStoryReader(ctx context.Context) (*Reader, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	pkg := p.partReader()
	if _, present := pkg.parts[strings.ToLower(p.sequence)]; !present {
		createdPut(pkg, p.sequence, fixedContentType("fixeddocumentsequence"), nil)
	}
	r := &Reader{pkg: pkg, format: p.format, limits: p.limits, sequence: p.sequence, documents: p.documents}
	for _, document := range p.documents {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if _, present := pkg.parts[strings.ToLower(document.Part)]; !present {
			createdPut(pkg, document.Part, fixedContentType("fixeddocument"), nil)
		}
		r.pages = append(r.pages, document.Pages...)
	}
	for _, source := range slices.Sorted(maps.Keys(p.relations)) {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		var wanted []Relationship
		for _, relation := range p.originalRels[source] {
			if p.modelRelationship(relation) {
				wanted = append(wanted, relation)
			}
		}
		if err := p.composeRelationships(pkg, p.relationSourceName(pkg, source), wanted, ctx); err != nil {
			return nil, err
		}
	}
	return r, nil
}

// storyCopy 复制页面索引及候选编辑会修改的映射，继续共享不可变资源字节
// 返回: *Package 独立候选状态
func (p *Package) storyCopy() *Package {
	q := p.signingCopy()
	q.layout = maps.Clone(p.layout)
	q.documents = slices.Clone(p.documents)
	for index := range q.documents {
		q.documents[index].Pages = slices.Clone(q.documents[index].Pages)
	}
	return q
}

// commitStory 在结构校验成功后提交候选状态，调用方持有原包写锁
// 入参: q 已校验的候选状态
func (p *Package) commitStory(q *Package) {
	p.documents, p.pageCount = q.documents, q.pageCount
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.layout = q.names, q.parents, q.allocated, q.layout
	p.dirty, p.dirtyRels = q.dirty, q.dirtyRels
}

// validateStoryEdit 检查候选状态的结构模式、片段及页面名称绑定，不生成中间ZIP
// 入参: ctx 取消Context
// 返回: error 关联、绑定、资源或取消错误
func (p *Package) validateStoryEdit(ctx context.Context) error {
	r, err := p.editStoryReader(ctx)
	if err != nil {
		return err
	}
	defer r.Close()
	return r.validateStoryLinks(ctx)
}

// setStoryPage 原子替换被故事片段引用的页面，不隐式猜测已删除命名元素的替代目标
// 入参: document 文档序号, index 页面序号, page 已固定部件名的页面, ctx 取消Context
// 返回: error 编码、绑定、资源或取消错误
func (p *Package) setStoryPage(document, index int, page *Page, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	q := p.storyCopy()
	targets, err := q.storePage(page, ctx)
	if err != nil {
		return err
	}
	q.documents[document].Pages[index] = PageReference{Part: page.Part, LinkTargets: targets}
	q.dirty[strings.ToLower(q.documents[document].Part)] = true
	if err := q.validateStoryEdit(ctx); err != nil {
		return err
	}
	p.commitStory(q)
	return nil
}

// storyStructures 统计结构部件所有者，只为待编辑文档解析独立模型
// 入参: r 当前结构索引, affected 待编辑文档序号
// 返回: []*DocumentStructure 待编辑文档对应结构, map[string]int 部件使用次数, error 读取或结构错误
func storyStructures(r *Reader, affected ...int) ([]*DocumentStructure, map[string]int, error) {
	result := make([]*DocumentStructure, len(r.documents))
	owners := make(map[string]int)
	graph := createdStoryGraph{reader: r, backend: r.pkg, work: r.limits.MaxXMLNodes, relations: make(map[string][]Relationship)}
	for _, document := range r.documents {
		part, err := graph.target(document.Part, "documentstructure")
		if err != nil {
			return nil, nil, err
		}
		if part != "" {
			owners[strings.ToLower(part)]++
		}
	}
	seen := make(map[int]bool, len(affected))
	for _, index := range affected {
		if seen[index] {
			continue
		}
		value, err := r.readDocumentStructure(index)
		if err != nil {
			return nil, nil, err
		}
		result[index] = value
		seen[index] = true
	}
	return result, owners, nil
}

// remapStoryPages 按页面部件身份更新一基页码，删除已移出文档的引用及因此变空的故事
// 入参: value 文档结构, previous 原页面顺序, current 新页面顺序
// 返回: bool 是否改变结构, error 原引用不在原文档范围内
func remapStoryPages(value *DocumentStructure, previous, current []PageReference) (bool, error) {
	if value == nil {
		return false, nil
	}
	positions := make(map[string]int, len(current))
	for index, page := range current {
		positions[strings.ToLower(page.Part)] = index + 1
	}
	changed := false
	stories := value.Stories[:0]
	for _, story := range value.Stories {
		fragments := story.Fragments[:0]
		for _, reference := range story.Fragments {
			if reference.PageNumber < 1 || reference.PageNumber > len(previous) {
				return false, fmt.Errorf("%w: story page outside previous document", ErrInvalid)
			}
			page, present := positions[strings.ToLower(previous[reference.PageNumber-1].Part)]
			if !present {
				changed = true
				continue
			}
			if int64(page) > 1<<31-1 {
				return false, fmt.Errorf("%w: story page exceeds XML integer range", ErrInvalid)
			}
			changed = changed || reference.PageNumber != page
			reference.PageNumber = page
			fragments = append(fragments, reference)
		}
		if len(fragments) == 0 {
			changed = true
			continue
		}
		story.Fragments = fragments
		stories = append(stories, story)
	}
	value.Stories = stories
	return changed, nil
}

// writeStoryStructure 更新已改变的文档结构，共享部件使用独立副本以免影响其他文档
// 入参: document 文档序号, value 待写结构, owners 原结构部件使用次数
// 返回: error 编码、编辑限制、关联或资源错误
func (p *Package) writeStoryStructure(document int, value *DocumentStructure, owners map[string]int) error {
	data, err := createdDocumentStructure(value, p.format, p.limits, nil)
	if err != nil {
		return err
	}
	part := value.Part
	pattern := ""
	if part == "" {
		base := p.documents[document].Part
		pattern = base[:strings.LastIndexByte(base, '/')+1] + "Structure%d.struct"
	} else if owners[strings.ToLower(part)] > 1 {
		pattern = part[:strings.LastIndexByte(part, '/')+1] + "Structure%d.struct"
	}
	if pattern != "" {
		part, err = p.newName(pattern, nil)
		if err != nil {
			return err
		}
	}
	if value.Part != "" {
		original := p.parts[strings.ToLower(value.Part)].data
		data, err = restoreXMLEncoding(original, data, min(p.limits.MaxPartBytes, p.limits.MaxMetadataBytes), nil)
		if err != nil {
			return err
		}
	}
	if err := p.editable(part); err != nil {
		return err
	}
	if err := p.store(part, fixedContentType("documentstructure"), data); err != nil {
		return err
	}
	if !strings.EqualFold(part, value.Part) {
		if err := p.replaceStoryRelationship(p.documents[document].Part, "documentstructure", part); err != nil {
			return err
		}
		if value.Part != "" {
			owners[strings.ToLower(value.Part)]--
		}
		owners[strings.ToLower(part)]++
		value.Part = part
	}
	p.commitName(pattern, part)
	return nil
}

// replaceStoryRelationship 替换一种结构关联并保留其他显式关系，优先沿用首个已有关系ID
// 入参: source 来源部件, kind 结构类型, target 新目标部件
// 返回: error 关系、编辑限制或资源错误
func (p *Package) replaceStoryRelationship(source, kind, target string) error {
	key := strings.ToLower(source)
	typ := formatNamespace(p.format) + "/" + kind
	previous := p.relations[key]
	result := make([]Relationship, 0, len(previous)+1)
	id := ""
	for _, relation := range previous {
		if relation.Type != typ {
			result = append(result, relation)
		} else if id == "" {
			id = relation.ID
		}
	}
	if id == "" {
		used := append(slices.Clone(p.originalRels[key]), previous...)
		id = createdRelationshipIDs(used)()
	}
	result = append(result, Relationship{ID: id, Type: typ, Target: target, TargetMode: "Internal"})
	return p.setRelationships(source, result)
}

// uniqueStoryName 为迁入故事分配文档内独立名称，不把同名的两个故事静默合并
// 入参: original 原故事名称, used 目标文档已用名称
// 返回: string 独立故事名称
func uniqueStoryName(original string, used map[string]bool) string {
	if !used[original] {
		used[original] = true
		return original
	}
	for index := 2; ; index++ {
		name := original + " (" + strconv.Itoa(index) + ")"
		if !used[name] {
			used[name] = true
			return name
		}
	}
}

// createdDocumentStructure 编码文档目录和有序故事定义，不输出模型的部件定位信息
// 入参: value 已解析的结构模型, format 输出方言, limits 资源上限, ctx 取消Context
// 返回: []byte 结构XML, error 模型、预算或取消错误
func createdDocumentStructure(value *DocumentStructure, format Format, limits Limits, ctx context.Context) ([]byte, error) {
	p, err := newCreatedStoryEncoder(format, limits, ctx)
	if err != nil {
		return nil, err
	}
	if value == nil {
		return nil, fmt.Errorf("%w: missing document structure", ErrInvalid)
	}
	root, err := p.node("DocumentStructure", 1)
	if err != nil {
		return nil, err
	}
	if value.Outline != nil {
		container, err := p.node("DocumentStructure.Outline", 2)
		if err != nil {
			return nil, err
		}
		outline, err := p.node("DocumentOutline", 3)
		if err != nil {
			return nil, err
		}
		if err := p.attribute(outline, xml.Name{Space: xmlNamespace, Local: "lang"}, value.Outline.Language); err != nil {
			return nil, err
		}
		for _, entry := range value.Outline.Entries {
			child, err := p.node("OutlineEntry", 4)
			if err != nil {
				return nil, err
			}
			for _, attr := range []struct{ name, value string }{
				{"OutlineLevel", strconv.FormatInt(int64(entry.Level), 10)},
				{"OutlineTarget", entry.Target}, {"Description", entry.Description},
			} {
				if err := p.attr(child, attr.name, attr.value); err != nil {
					return nil, err
				}
			}
			if entry.Language != nil {
				if err := p.attribute(child, xml.Name{Space: xmlNamespace, Local: "lang"}, *entry.Language); err != nil {
					return nil, err
				}
			}
			outline.Children = append(outline.Children, child)
		}
		container.Children = append(container.Children, outline)
		root.Children = append(root.Children, container)
	}
	for _, story := range value.Stories {
		child, err := p.node("Story", 2)
		if err != nil {
			return nil, err
		}
		if err := p.attr(child, "StoryName", story.Name); err != nil {
			return nil, err
		}
		for _, reference := range story.Fragments {
			node, err := p.node("StoryFragmentReference", 3)
			if err != nil {
				return nil, err
			}
			if err := p.attr(node, "Page", strconv.Itoa(reference.PageNumber)); err != nil {
				return nil, err
			}
			if reference.FragmentName != nil {
				if err := p.attr(node, "FragmentName", *reference.FragmentName); err != nil {
					return nil, err
				}
			}
			child.Children = append(child.Children, node)
		}
		root.Children = append(root.Children, child)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if _, err := parseDocumentStructure(root, p.namespace, math.MaxInt32); err != nil {
		return nil, err
	}
	return p.markup(root)
}

// createdStoryFragments 编码片段、首尾断点和语义树，保留可选名称的存在性
// 入参: value 已解析的片段模型, format 输出方言, limits 资源上限, ctx 取消Context
// 返回: []byte 片段XML, error 模型、预算或取消错误
func createdStoryFragments(value *StoryFragments, format Format, limits Limits, ctx context.Context) ([]byte, error) {
	p, err := newCreatedStoryEncoder(format, limits, ctx)
	if err != nil {
		return nil, err
	}
	if value == nil {
		return nil, fmt.Errorf("%w: missing story fragments", ErrInvalid)
	}
	root, err := p.node("StoryFragments", 1)
	if err != nil {
		return nil, err
	}
	for _, fragment := range value.Fragments {
		child, err := p.node("StoryFragment", 2)
		if err != nil {
			return nil, err
		}
		var kind string
		switch fragment.Type {
		case FragmentContent:
			kind = "Content"
		case FragmentHeader:
			kind = "Header"
		case FragmentFooter:
			kind = "Footer"
		default:
			return nil, fmt.Errorf("%w: invalid fragment type", ErrInvalid)
		}
		if err := p.attr(child, "FragmentType", kind); err != nil {
			return nil, err
		}
		for _, attr := range []struct {
			name  string
			value *string
		}{{"StoryName", fragment.StoryName}, {"FragmentName", fragment.FragmentName}} {
			if attr.value != nil {
				if err := p.attr(child, attr.name, *attr.value); err != nil {
					return nil, err
				}
			}
		}
		if fragment.BreakBefore {
			node, err := p.node("StoryBreak", 3)
			if err != nil {
				return nil, err
			}
			child.Children = append(child.Children, node)
		}
		for index := range fragment.Content {
			node, err := p.content(&fragment.Content[index], 3)
			if err != nil {
				return nil, err
			}
			child.Children = append(child.Children, node)
		}
		if fragment.BreakAfter {
			node, err := p.node("StoryBreak", 3)
			if err != nil {
				return nil, err
			}
			child.Children = append(child.Children, node)
		}
		root.Children = append(root.Children, child)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if _, err := parseStoryFragments(root, p.namespace, limits.MaxXMLDepth); err != nil {
		return nil, err
	}
	return p.markup(root)
}

// newCreatedStoryEncoder 校验方言和显式上限，预留根命名空间声明的字节
// 入参: format 输出方言, limits 资源上限, ctx 取消Context
// 返回: *createdStoryEncoder 编码状态, error 参数、预算或取消错误
func newCreatedStoryEncoder(format Format, limits Limits, ctx context.Context) (*createdStoryEncoder, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	namespace := structureNamespace(format)
	if namespace == "" {
		return nil, fmt.Errorf("%w: invalid structure format", ErrInvalid)
	}
	limits.MaxPartBytes = min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes)
	p := &createdStoryEncoder{namespace: namespace, limits: limits, context: ctx}
	if err := p.reserve(int64(len(namespace) + 9)); err != nil {
		return nil, err
	}
	return p, nil
}

// node 在分配元素及其两个命名空间绑定前检查深度、节点和字节预算
// 入参: name 元素名, depth 从一开始的XML深度
// 返回: *xmlElement 独立节点, error 预算或取消错误
func (p *createdStoryEncoder) node(name string, depth int) (*xmlElement, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	if depth > p.limits.MaxXMLDepth || p.nodes >= p.limits.MaxXMLNodes || p.nodes >= p.limits.MaxXMLBindings/2 {
		return nil, fmt.Errorf("%w: generated story structure complexity", ErrLimit)
	}
	if err := p.reserve(int64(2*len(name) + 5)); err != nil {
		return nil, err
	}
	p.nodes++
	return createdNode(p.namespace, name), nil
}

// reserve 累计输出字节，使用剩余额度比较避免整数溢出
// 入参: size 新增字节数
// 返回: error 字节预算错误
func (p *createdStoryEncoder) reserve(size int64) error {
	if size > p.limits.MaxPartBytes-p.bytes {
		return fmt.Errorf("%w: generated story structure bytes", ErrLimit)
	}
	p.bytes += size
	return nil
}

// attribute 在添加属性前检查字符并累计XML转义后的完整字节数
// 入参: node 目标元素, name 属性展开名称, value 属性值
// 返回: error 字符、预算或取消错误
func (p *createdStoryEncoder) attribute(node *xmlElement, name xml.Name, value string) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	size := int64(len(name.Local) + 4)
	if name.Space == xmlNamespace {
		size += 4
	}
	if err := p.reserve(size); err != nil {
		return err
	}
	if err := p.reserve(int64(len(value))); err != nil {
		return err
	}
	for offset := 0; offset < len(value); {
		if err := checkContext(p.context); err != nil {
			return err
		}
		character, width := utf8.DecodeRuneInString(value[offset:])
		if character == utf8.RuneError && width == 1 || character < 0x20 && character != '\t' && character != '\r' && character != '\n' || character == 0xfffe || character == 0xffff {
			return fmt.Errorf("%w: invalid story structure attribute %s", ErrInvalid, name.Local)
		}
		var extra int64
		switch character {
		case '&', '\'', '"', '\t', '\r', '\n':
			extra = 4
		case '<', '>':
			extra = 3
		}
		if err := p.reserve(extra); err != nil {
			return err
		}
		offset += width
	}
	node.Attr = append(node.Attr, xml.Attr{Name: name, Value: value})
	return nil
}

// attr 添加无命名空间的结构属性
// 入参: node 目标元素, name 属性名, value 属性值
// 返回: error 字符、预算或取消错误
func (p *createdStoryEncoder) attr(node *xmlElement, name, value string) error {
	return p.attribute(node, xml.Name{Local: name}, value)
}

// content 递归编码语义节点，拒绝当前类型不能表达的字段以免静默丢失模型数据
// 入参: value 内容节点, depth XML深度
// 返回: *xmlElement 语义节点, error 模型、预算或取消错误
func (p *createdStoryEncoder) content(value *ContentStructure, depth int) (*xmlElement, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	if value.Kind != StructureNamedElement && value.NameReference != "" || value.Kind != StructureListItem && value.Marker != nil || value.Kind != StructureCell && (value.RowSpan != 0 || value.ColumnSpan != 0) {
		return nil, fmt.Errorf("%w: fields do not belong to structure kind", ErrInvalid)
	}
	var name string
	switch value.Kind {
	case StructureSection:
		name = "SectionStructure"
	case StructureParagraph:
		name = "ParagraphStructure"
	case StructureTable:
		name = "TableStructure"
	case StructureRowGroup:
		name = "TableRowGroupStructure"
	case StructureRow:
		name = "TableRowStructure"
	case StructureCell:
		name = "TableCellStructure"
	case StructureList:
		name = "ListStructure"
	case StructureListItem:
		name = "ListItemStructure"
	case StructureFigure:
		name = "FigureStructure"
	case StructureNamedElement:
		name = "NamedElement"
	default:
		return nil, fmt.Errorf("%w: invalid structure kind", ErrInvalid)
	}
	node, err := p.node(name, depth)
	if err != nil {
		return nil, err
	}
	if value.Kind == StructureNamedElement {
		if err := p.attr(node, "NameReference", value.NameReference); err != nil {
			return nil, err
		}
	}
	if value.Marker != nil {
		if err := p.attr(node, "Marker", *value.Marker); err != nil {
			return nil, err
		}
	}
	if value.Kind == StructureCell {
		if err := p.attr(node, "RowSpan", strconv.FormatInt(int64(value.RowSpan), 10)); err != nil {
			return nil, err
		}
		if err := p.attr(node, "ColumnSpan", strconv.FormatInt(int64(value.ColumnSpan), 10)); err != nil {
			return nil, err
		}
	}
	for index := range value.Children {
		child, err := p.content(&value.Children[index], depth+1)
		if err != nil {
			return nil, err
		}
		node.Children = append(node.Children, child)
	}
	return node, nil
}

// markup 输出已校验的独立结构标记，取消或编码失败时不返回部分数据
// 入参: root 已完成模式校验的根元素
// 返回: []byte 结构XML, error 字符、预算或取消错误
func (p *createdStoryEncoder) markup(root *xmlElement) ([]byte, error) {
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	data, err := createdMarkup(root, p.limits, p.context)
	if err != nil {
		return nil, err
	}
	if err := checkContext(p.context); err != nil {
		return nil, err
	}
	return data, nil
}

// moveStoryPage 在独立候选中迁移故事引用，跨文档同名故事保持独立身份
// 入参: document 来源文档序号, index 来源页面序号, target 目标文档序号, position 移动后页面序号
// 返回: error 结构、绑定、编辑限制或资源错误
func (p *Package) moveStoryPage(document, index, target, position int) error {
	r, err := p.editStoryReader(nil)
	if err != nil {
		return err
	}
	defer r.Close()
	structures, owners, err := storyStructures(r, document, target)
	if err != nil {
		return err
	}
	q := p.storyCopy()
	q.movePage(document, index, target, position)
	if document == target {
		changed, err := remapStoryPages(structures[document], p.documents[document].Pages, q.documents[document].Pages)
		if err != nil {
			return err
		}
		if changed {
			if err := q.writeStoryStructure(document, structures[document], owners); err != nil {
				return err
			}
		}
	} else if err := q.transferPageStories(p, r, structures, owners, document, index, target, position); err != nil {
		return err
	}
	if err := q.validateStoryEdit(nil); err != nil {
		return err
	}
	p.commitStory(q)
	return nil
}

// deleteStoryPage 删除页面引用后重排剩余页码，不删除可能共享的结构资源
// 入参: document 文档序号, index 页面序号
// 返回: error 结构、绑定、编辑限制或资源错误
func (p *Package) deleteStoryPage(document, index int) error {
	r, err := p.editStoryReader(nil)
	if err != nil {
		return err
	}
	defer r.Close()
	structures, owners, err := storyStructures(r, document)
	if err != nil {
		return err
	}
	q := p.storyCopy()
	q.deletePage(document, index)
	changed, err := remapStoryPages(structures[document], p.documents[document].Pages, q.documents[document].Pages)
	if err != nil {
		return err
	}
	if changed {
		if err := q.writeStoryStructure(document, structures[document], owners); err != nil {
			return err
		}
	}
	if err := q.validateStoryEdit(nil); err != nil {
		return err
	}
	p.commitStory(q)
	return nil
}

// transferPageStories 保留原故事内的片段顺序，迁入目标文档时只重命名冲突的故事
// 入参: previous 原包, r 原结构索引, structures 各文档结构, owners 结构共享次数, document 来源文档, index 原页面, target 目标文档, position 新页面序号
// 返回: error 结构、绑定、编码或资源错误
func (p *Package) transferPageStories(previous *Package, r *Reader, structures []*DocumentStructure, owners map[string]int, document, index, target, position int) error {
	var incoming []Story
	if source := structures[document]; source != nil {
		for _, story := range source.Stories {
			value := Story{Name: story.Name}
			for _, reference := range story.Fragments {
				if reference.PageNumber == index+1 {
					if int64(position)+1 > 1<<31-1 {
						return fmt.Errorf("%w: story page exceeds XML integer range", ErrInvalid)
					}
					reference.PageNumber = position + 1
					value.Fragments = append(value.Fragments, reference)
				}
			}
			if len(value.Fragments) != 0 {
				incoming = append(incoming, value)
			}
		}
	}
	sourceChanged, err := remapStoryPages(structures[document], previous.documents[document].Pages, p.documents[document].Pages)
	if err != nil {
		return err
	}
	targetChanged, err := remapStoryPages(structures[target], previous.documents[target].Pages, p.documents[target].Pages)
	if err != nil {
		return err
	}
	if len(incoming) != 0 {
		if structures[target] == nil {
			structures[target] = &DocumentStructure{}
		}
		used, err := storyTargetNames(r, target, structures[target])
		if err != nil {
			return err
		}
		renames := make(map[string]string)
		for _, story := range incoming {
			name := uniqueStoryName(story.Name, used)
			if name != story.Name {
				renames[story.Name] = name
			}
			story.Name = name
			structures[target].Stories = append(structures[target].Stories, story)
		}
		page := previous.documents[document].Pages[index].Part
		if err := p.renamePageStories(r, page, renames); err != nil {
			return err
		}
		targetChanged = true
	}
	if sourceChanged {
		if err := p.writeStoryStructure(document, structures[document], owners); err != nil {
			return err
		}
	}
	if targetChanged {
		if err := p.writeStoryStructure(target, structures[target], owners); err != nil {
			return err
		}
	}
	return nil
}

// storyTargetNames 保留目标文档中已声明或已用于页面片段的名称，避免意外合并未定义的故事
// 入参: r 原结构索引, document 目标文档序号, value 目标文档结构
// 返回: map[string]bool 已用名称, error 片段读取或结构错误
func storyTargetNames(r *Reader, document int, value *DocumentStructure) (map[string]bool, error) {
	used := make(map[string]bool)
	for _, story := range value.Stories {
		used[story.Name] = true
	}
	first := 0
	for index := 0; index < document; index++ {
		first += len(r.documents[index].Pages)
	}
	graph := createdStoryGraph{reader: r, backend: r.pkg, work: r.limits.MaxXMLNodes, relations: make(map[string][]Relationship), fragments: make(map[string]*StoryFragments)}
	seen := make(map[string]bool)
	for index := range r.documents[document].Pages {
		fragments, err := graph.pageFragments(first + index)
		if err != nil {
			return nil, err
		}
		if fragments == nil {
			continue
		}
		key := strings.ToLower(fragments.Part)
		if seen[key] {
			continue
		}
		seen[key] = true
		for _, fragment := range fragments.Fragments {
			if err := graph.step(1); err != nil {
				return nil, err
			}
			if fragment.StoryName != nil {
				used[*fragment.StoryName] = true
			}
		}
	}
	return used, nil
}

// renamePageStories 更新迁移页面中的故事归属，共享片段部件采用独立副本
// 入参: r 原结构索引, page 迁移页面部件, renames 原故事名与目标独立名称
// 返回: error 片段、绑定、编码、关联或资源错误
func (p *Package) renamePageStories(r *Reader, page string, renames map[string]string) error {
	if len(renames) == 0 {
		return nil
	}
	number := -1
	for index, reference := range r.pages {
		if strings.EqualFold(reference.Part, page) {
			number = index
			break
		}
	}
	fragments, err := r.readStoryFragments(number)
	if err != nil {
		return err
	}
	if fragments == nil {
		return fmt.Errorf("%w: moved story page has no fragments", ErrInvalid)
	}
	for index := range fragments.Fragments {
		value := &fragments.Fragments[index]
		if value.StoryName != nil {
			if name, present := renames[*value.StoryName]; present {
				value.StoryName = &name
			}
		}
	}
	data, err := createdStoryFragments(fragments, p.format, p.limits, nil)
	if err != nil {
		return err
	}
	part := fragments.Part
	owners, err := storyFragmentOwners(r, part)
	if err != nil {
		return err
	}
	if owners > 1 {
		part, err = p.newName(page[:strings.LastIndexByte(page, '/')+1]+"Structure/%d.frag", nil)
		if err != nil {
			return err
		}
	}
	data, err = restoreXMLEncoding(p.parts[strings.ToLower(fragments.Part)].data, data, min(p.limits.MaxPartBytes, p.limits.MaxMetadataBytes), nil)
	if err != nil {
		return err
	}
	if err := p.editable(part); err != nil {
		return err
	}
	if err := p.store(part, fixedContentType("storyfragments"), data); err != nil {
		return err
	}
	if !strings.EqualFold(part, fragments.Part) {
		if err := p.replaceStoryRelationship(page, "storyfragments", part); err != nil {
			return err
		}
		p.commitName(page[:strings.LastIndexByte(page, '/')+1]+"Structure/%d.frag", part)
	}
	return nil
}

// storyFragmentOwners 统计指向同一片段部件的页面，每个页面只计一次
// 入参: r 原结构索引, part 片段部件
// 返回: int 页面使用次数, error 关系读取或目标错误
func storyFragmentOwners(r *Reader, part string) (int, error) {
	count := 0
	for _, page := range r.pages {
		relations, err := r.pkg.relationships(page.Part)
		if err != nil {
			return 0, err
		}
		for _, relation := range relations {
			if relation.Type != formatNamespace(r.format)+"/storyfragments" || relation.TargetMode != "Internal" {
				continue
			}
			target, err := resolvePart(page.Part, relation.Target)
			if err != nil {
				return 0, err
			}
			if strings.EqualFold(target, part) {
				count++
				break
			}
		}
	}
	return count, nil
}

// ExtractDocument 提取指定固定文档及其引用资源为独立可编辑包，不修改源数据，重编序列页码
// 新包不继承源签名与释放提示，跨文档引用、未知引用语义及受限字体改写返回错误
// 入参: ctx 取消Context，nil采用Background, index 零基文档序号, options 输出资源选项，nil沿用读取上限
// 返回: *Package 独立文档包，失败为nil, error 结构、引用、许可、资源、关闭或取消错误
func (r *Reader) ExtractDocument(ctx context.Context, index int, options *PackageOptions) (*Package, error) {
	ctx = normalizeContext(ctx)
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if index < 0 || index >= len(r.documents) {
		return nil, fmt.Errorf("%w: document index", ErrInvalid)
	}
	configuration := PackageOptions{Limits: r.limits}
	if options != nil {
		configuration.Limits = mergeLimits(configuration.Limits, options.Limits)
		configuration.MaxImagePixels = options.MaxImagePixels
	}
	p, err := NewPackage(r.format, &configuration)
	if err != nil {
		return nil, err
	}
	clear(p.names)
	clear(p.parents)
	clear(p.layout)
	p.sequence = r.sequence
	p.original = make(map[string]packagePart)
	p.originalRels = make(map[string][]Relationship)
	document := r.documents[index]
	document.Pages = slices.Clone(document.Pages)
	if len(document.Pages) > p.limits.MaxPageCount {
		return nil, fmt.Errorf("%w: extracted page count", ErrLimit)
	}
	p.documents, p.pageCount = []Document{document}, len(document.Pages)
	s := documentExtraction{reader: r, output: p, context: ctx, count: len(document.Pages), queued: make(map[extractionPart]bool), scanned: make(map[string]bool), scopes: make(map[string]extractionLinkScope), targets: make(map[string]map[string]int), work: p.limits.MaxXMLNodes}
	for _, prior := range r.documents[:index] {
		if err := s.step(1); err != nil {
			return nil, err
		}
		s.first += len(prior.Pages)
	}
	s.scopes[strings.ToLower(r.sequence)] = extractionLinkScope{count: len(r.pages)}
	s.scopes[strings.ToLower(document.Part)] = extractionLinkScope{first: s.first, count: s.count}
	for page := range document.Pages {
		if err := s.step(1); err != nil {
			return nil, err
		}
		document.Pages[page].LinkTargets = slices.Clone(document.Pages[page].LinkTargets)
		s.scopes[strings.ToLower(document.Pages[page].Part)] = extractionLinkScope{first: s.first + page, count: 1}
	}
	for part := range s.scopes {
		p.layout[part] = true
	}
	if err := s.relationships("/", ""); err != nil {
		return nil, err
	}
	if err := s.add(r.sequence, ""); err != nil {
		return nil, err
	}
	if err := s.add(document.Part, ""); err != nil {
		return nil, err
	}
	for _, page := range document.Pages {
		if err := s.add(page.Part, page.Part); err != nil {
			return nil, err
		}
	}
	for position := 0; position < len(s.queue); position++ {
		if err := s.part(s.queue[position]); err != nil {
			return nil, err
		}
	}
	p.dirty[strings.ToLower(p.sequence)] = true
	view := &Reader{pkg: p.partReader(), format: p.format, limits: p.limits, sequence: p.sequence, documents: p.documents, pages: p.documents[0].Pages}
	if err := p.protectImported(view, ctx); err != nil {
		return nil, err
	}
	for key := range p.dirty {
		if err := p.editable(p.parts[key].name); err != nil {
			return nil, err
		}
	}
	validated, err := p.reader(ctx)
	if err != nil {
		return nil, err
	}
	validated.Close()
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return p, nil
}

// step 在扩展引用或解析属性前扣除工作量，并检查取消状态
// 入参: count 本次工作单元数
// 返回: error 预算或取消错误
func (s *documentExtraction) step(count int) error {
	if err := checkContext(s.context); err != nil {
		return err
	}
	if count > s.work {
		return fmt.Errorf("%w: document extraction work budget", ErrLimit)
	}
	s.work -= count
	return nil
}

// add 按实际部件类型登记引用，不允许把未选择的固定布局部件作为隐藏资源带入
// 入参: part 目标部件URI, owner 引用所属页面，非布局资源可为空
// 返回: error 目标、类型、预算或取消错误
func (s *documentExtraction) add(part, owner string) error {
	if err := s.step(1); err != nil {
		return err
	}
	key := strings.ToLower(part)
	name, exists := s.reader.pkg.names[key]
	if !exists || key == strings.ToLower(opcTypesName) || opcRelationshipName(name) {
		return &PartError{Part: part, Err: fmt.Errorf("%w: extraction target part", ErrInvalid)}
	}
	media, err := s.reader.pkg.contentType(name)
	if err != nil {
		return err
	}
	model, err := resourceModelMedia(media)
	if err != nil {
		return &PartError{Part: name, Err: err}
	}
	if model {
		return &PartError{Part: name, Err: fmt.Errorf("%w: extraction requires opaque X3D dependency preservation", ErrUnsupported)}
	}
	if _, selected := s.scopes[key]; compositionLayoutMedia(media) && !selected {
		return &PartError{Part: name, Err: fmt.Errorf("%w: extraction references another fixed document", ErrUnsupported)}
	}
	if strings.EqualFold(media, opcSignatureType) || strings.EqualFold(media, opcSignatureOriginType) || strings.EqualFold(media, fixedContentType("discard-control")) {
		return &PartError{Part: name, Err: fmt.Errorf("%w: extraction references omitted package metadata", ErrUnsupported)}
	}
	if strings.EqualFold(media, fixedContentType("fixedpage")) {
		owner = name
	} else if !strings.EqualFold(media, resourceDictionaryContentType) {
		owner = ""
	}
	item := extractionPart{part: name, owner: owner}
	if !s.queued[item] {
		s.queued[item] = true
		s.queue = append(s.queue, item)
	}
	return nil
}

// load 只复制闭包内的部件，保留原字节和物理条目属性，累计检查输出容量
// 入参: part 原包中的部件URI
// 返回: packagePart 独立部件数据, error 读取、名称、预算或取消错误
func (s *documentExtraction) load(part string) (packagePart, error) {
	if err := s.step(1); err != nil {
		return packagePart{}, err
	}
	p := s.output
	key := strings.ToLower(part)
	if old, exists := p.original[key]; exists {
		return old, nil
	}
	if len(p.parts)+2 > p.limits.MaxPartCount {
		return packagePart{}, fmt.Errorf("%w: extracted part count", ErrLimit)
	}
	limit := min(p.limits.MaxPartBytes, p.limits.MaxPackageBytes-p.total)
	media, err := s.reader.pkg.contentType(part)
	if err != nil {
		return packagePart{}, err
	}
	if compositionXML(media) || opcRelationshipName(part) {
		limit = min(limit, p.limits.MaxMetadataBytes)
	}
	data, err := s.reader.pkg.readItems(key, limit)
	if err != nil {
		return packagePart{}, &PartError{Part: part, Err: err}
	}
	if err := p.availableName(part); err != nil {
		return packagePart{}, err
	}
	value := packagePart{name: s.reader.pkg.names[key], media: media, data: data}
	value.items, err = s.reader.pkg.importItems(key, data)
	if err != nil {
		return packagePart{}, err
	}
	p.parts[key], p.original[key] = value, value
	p.registerName(value.name)
	p.total += int64(len(data))
	return value, nil
}

// relationships 保留闭包内的附属关系，包级签名和释放提示不继承到新包
// 入参: source 关系源URI，包根为/, owner 当前所属页面
// 返回: error 关系、引用、预算或取消错误
func (s *documentExtraction) relationships(source, owner string) error {
	name := createdRelationshipPart(source)
	key := strings.ToLower(name)
	if _, present := s.reader.pkg.parts[key]; !present {
		return nil
	}
	value, err := s.load(name)
	if err != nil {
		return err
	}
	relations, err := parseRelationshipMarkup(source, value.data, s.output.limits, s.context)
	if err != nil {
		return err
	}
	sourceKey := strings.ToLower(source)
	s.output.originalRels[sourceKey] = relations
	if source == "/" {
		discard := formatNamespace(s.reader.format) + "/discard-control"
		if _, err := decodeXMLVisit(value.data, s.output.limits, func(token xml.Token, node *xmlElement) error {
			if _, start := token.(xml.StartElement); !start {
				return checkContext(s.context)
			}
			if err := s.step(1); err != nil {
				return err
			}
			if node.Name == (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
				kind, _ := node.attribute("Type")
				if kind == opcSignatureOriginRel || kind == discard {
					s.output.dirtyRels[sourceKey] = true
				}
			}
			return nil
		}); err != nil {
			return err
		}
	}
	var explicit []Relationship
	for _, relation := range relations {
		if err := s.step(1); err != nil {
			return err
		}
		if source == "/" && (relation.Type == opcSignatureOriginRel || relation.Type == formatNamespace(s.reader.format)+"/discard-control") {
			s.output.dirtyRels[sourceKey] = true
			continue
		}
		if relation.TargetMode == "Internal" {
			target, err := resolvePart(source, relation.Target)
			if err != nil {
				return err
			}
			if err := s.add(target, owner); err != nil {
				return err
			}
		}
		if !s.output.modelRelationship(relation) {
			explicit = append(explicit, relation)
		}
	}
	s.output.relations[sourceKey] = explicit
	return nil
}

// part 展开已登记部件的资源与导航引用，字典链接使用实际所属页面的地址基准
// 入参: item 部件及其所属页面
// 返回: error 标记、引用、许可、预算或取消错误
func (s *documentExtraction) part(item extractionPart) error {
	value, err := s.load(item.part)
	if err != nil {
		return err
	}
	if err := s.relationships(item.part, item.owner); err != nil {
		return err
	}
	markup, err := fontUsageMarkup(value.media)
	if err != nil {
		return &PartError{Part: item.part, Err: err}
	}
	if !markup {
		return nil
	}
	if _, err := decodeXMLVisit(value.data, s.output.limits, func(token xml.Token, node *xmlElement) error {
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := s.step(1); err != nil {
			return err
		}
		return validateResourceMarkupElement(node, s.reader.format)
	}); err != nil {
		return &PartError{Part: item.part, Err: err}
	}
	if strings.EqualFold(item.part, s.reader.sequence) {
		return nil
	}
	data, err := rewriteExtractMarkup(value.data, s.output.limits, s.context, func(node *xmlElement, attribute xml.Attr) (string, bool, error) {
		if err := s.step(1); err != nil {
			return "", false, err
		}
		references, err := resourceAttributeReferences(node, attribute)
		if err != nil {
			return "", false, err
		}
		for _, reference := range references {
			target, err := resolvePart(item.part, reference.uri)
			if err != nil {
				return "", false, err
			}
			if err := s.add(target, item.owner); err != nil {
				return "", false, err
			}
		}
		base := item.part
		if resourceIdentityAttribute(node, attribute, s.reader.format) {
			if attribute.Name.Local == "FixedPage.NavigateUri" {
				if item.owner == "" {
					return "", false, fmt.Errorf("%w: dictionary navigation lacks page context", ErrUnsupported)
				}
				base = item.owner
			}
			return s.navigation(base, attribute.Value)
		}
		return attribute.Value, false, nil
	})
	if err != nil {
		return &PartError{Part: item.part, Err: err}
	}
	key := strings.ToLower(item.part)
	if s.scanned[key] {
		if bytes.Equal(data, s.output.parts[key].data) {
			return nil
		}
		return &PartError{Part: item.part, Err: fmt.Errorf("%w: shared dictionary navigation differs between pages", ErrUnsupported)}
	}
	s.scanned[key] = true
	if !bytes.Equal(value.data, data) {
		current := int64(len(s.output.parts[key].data))
		if int64(len(data)) > s.output.limits.MaxPackageBytes-(s.output.total-current) {
			return fmt.Errorf("%w: extracted markup byte budget", ErrLimit)
		}
		value.data, value.items = data, nil
		s.output.total += int64(len(data)) - current
		s.output.parts[key], s.output.dirty[key] = value, true
	}
	return nil
}

// navigation 保持已知链接的页面身份，将序列的全局页号改为提取后的页号
// 入参: source 链接基准部件, value 原URI
// 返回: string 新URI, bool 是否改变, error 跨文档、地址、预算或取消错误
func (s *documentExtraction) navigation(source, value string) (string, bool, error) {
	if err := s.step(1); err != nil {
		return "", false, err
	}
	normalized := structureURI(value)
	if linkExternal(normalized) {
		return value, false, nil
	}
	uri, err := url.Parse(normalized)
	if err != nil {
		return "", false, fmt.Errorf("%w: extraction navigation URI", ErrInvalid)
	}
	if uri.RawQuery != "" || uri.ForceQuery {
		return "", false, fmt.Errorf("%w: query in extraction navigation", ErrUnsupported)
	}
	part := source
	if uri.Path != "" {
		part, err = resolvePart(source, uri.EscapedPath())
		if err != nil {
			return "", false, err
		}
	}
	if err := s.add(part, ""); err != nil {
		return "", false, err
	}
	scope := s.scopes[strings.ToLower(part)]
	first, count := scope.first, scope.count
	if count == 0 {
		return value, false, nil
	}
	if strings.EqualFold(part, s.reader.sequence) && linkPageNumber(uri.Fragment) {
		number, err := strconv.ParseUint(uri.Fragment, 10, 64)
		if err == nil && number > 0 && number <= uint64(len(s.reader.pages)) {
			first = int(number) - 1
			if first < s.first || first >= s.first+s.count {
				return "", false, fmt.Errorf("%w: navigation targets another document", ErrUnsupported)
			}
			uri.Fragment, uri.RawFragment = strconv.Itoa(first-s.first+1), ""
			return uri.String(), uri.String() != normalized, nil
		}
	} else if uri.Fragment != "" && !linkPageNumber(uri.Fragment) {
		page, err := s.namedTarget(part, uri.Fragment, scope)
		if err != nil {
			return "", false, err
		}
		first = page
	}
	if first < s.first || first >= s.first+s.count {
		return "", false, fmt.Errorf("%w: navigation targets another document", ErrUnsupported)
	}
	return value, false, nil
}

// namedTarget 为每个地址范围建立一次首个声明索引，重复链接不反复扫描页面
// 入参: part 地址部件, name 目标名称, scope 源包页面范围
// 返回: int 命名目标页号，未声明时为范围首页, error 预算或取消错误
func (s *documentExtraction) namedTarget(part, name string, scope extractionLinkScope) (int, error) {
	if err := s.step(0); err != nil {
		return 0, err
	}
	key := strings.ToLower(part)
	index, present := s.targets[key]
	if !present {
		index = make(map[string]int)
		for page := scope.first; page < scope.first+scope.count; page++ {
			if err := s.step(1); err != nil {
				return 0, err
			}
			for _, target := range s.reader.pages[page].LinkTargets {
				if err := s.step(1); err != nil {
					return 0, err
				}
				if _, exists := index[target]; !exists {
					index[target] = page
				}
			}
		}
		s.targets[key] = index
	}
	if page, present := index[name]; present {
		return page, nil
	}
	return scope.first, nil
}

// rewriteExtractMarkup 按属性顺序改写XML逻辑值并保留原编码及其他字节，禁止改写命名空间声明
// 入参: data 原始XML, limits 资源上限, ctx 取消Context, rewrite 属性改写函数
// 返回: []byte 独立的原编码结果，失败为nil, error XML、回调、资源或取消错误
func rewriteExtractMarkup(data []byte, limits Limits, ctx context.Context, rewrite func(*xmlElement, xml.Attr) (string, bool, error)) ([]byte, error) {
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	if rewrite == nil {
		return nil, fmt.Errorf("%w: missing extraction markup rewriter", ErrInvalid)
	}
	bindingLimit := limits.MaxXMLBindings
	if bindingLimit == 0 {
		bindingLimit = DefaultLimits().MaxXMLBindings
	}
	bindings := 0
	var source, snapshot *xmlElement
	output, _, err := rewriteXMLAttributes(data, limits, ctx, func(node *xmlElement, attribute xml.Attr) (string, bool, error) {
		if source != node {
			if len(node.Namespaces) > bindingLimit-bindings {
				return "", false, fmt.Errorf("%w: extraction markup namespace copy budget", ErrLimit)
			}
			bindings += len(node.Namespaces)
			snapshot = &xmlElement{Name: node.Name, rawName: node.rawName, Attr: slices.Clone(node.Attr), Namespaces: maps.Clone(node.Namespaces)}
			snapshot.namespaceOwner = snapshot
			source = node
		}
		value, changed, err := rewrite(snapshot, attribute)
		if err != nil {
			return "", false, err
		}
		if err := checkContext(ctx); err != nil {
			return "", false, err
		}
		return value, changed, nil
	})
	return output, err
}
