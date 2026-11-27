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
	"encoding/xml"
	"fmt"
	"io/fs"
	"maps"
	"slices"
	"strings"
)

// streamTicketScopeBit 返回打印票据作用域对应的校验位掩码，未知作用域返回零
// 入参: scope 打印票据作用域
// 返回: uint8 作用域位掩码
func streamTicketScopeBit(scope PrintScope) uint8 {
	switch scope {
	case PrintScopeJob:
		return 1 << 0
	case PrintScopeDocument:
		return 1 << 1
	case PrintScopePage:
		return 1 << 2
	default:
		return 0
	}
}

// selectedRelationships 对页面或元数据消费者启用规范关系部件的语义，不按媒体类型解释一般附加XML
// 入参: name 规范部件URI, media 声明类型
// 返回: bool 是否处理关系语义
func (p *streamPackage) selectedRelationships(name, media string) bool {
	return p.needsIndex() && opcRelationshipName(name) && strings.EqualFold(media, opcRelsType)
}

// consumeRelationships 在原根作用域下处理闭合关系子树，共用OPC、MCE及关系值校验
// 入参: part 关系部件, event 独立词元
// 返回: error 元数据、关联、预算、回调或取消错误
func (p *streamPackage) consumeRelationships(part *streamPart, event StreamXMLToken) error {
	if part.relations == nil {
		part.relations = &streamPartialRelationships{ids: make(map[string]bool), discards: make(map[string]int)}
	}
	s := part.relations
	if s.deferred {
		return nil
	}
	switch token := event.Token.(type) {
	case xml.StartElement:
		node := &xmlElement{Name: token.Name, Attr: append([]xml.Attr(nil), token.Attr...), Namespaces: p.cloneEventNamespaces(event.Namespaces)}
		if len(s.stack) == 0 {
			if s.root != nil {
				return fmt.Errorf("%w: multiple streamed relationship roots", ErrInvalid)
			}
			s.root = node
			if node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationships"}) {
				s.deferred = true
				return nil
			}
			if err := p.relationshipFragment(part, nil); err != nil {
				return err
			}
		} else if len(s.stack) > 1 {
			parent := s.stack[len(s.stack)-1]
			parent.Children = append(parent.Children, node)
		}
		s.stack = append(s.stack, node)
	case xml.CharData:
		if len(s.stack) == 0 {
			return nil
		}
		if len(s.stack) == 1 {
			if !xmlWhitespace(string(token)) {
				return fmt.Errorf("%w: streamed relationship root text", ErrInvalid)
			}
			return nil
		}
		node := s.stack[len(s.stack)-1]
		node.text = append(node.text, token...)
	case xml.EndElement:
		if len(s.stack) == 0 {
			return fmt.Errorf("%w: streamed relationship end", ErrInvalid)
		}
		node := s.stack[len(s.stack)-1]
		node.Text, node.text = string(node.text), nil
		s.stack[len(s.stack)-1] = nil
		s.stack = s.stack[:len(s.stack)-1]
		before := len(s.items)
		if len(s.stack) == 1 {
			if err := p.relationshipFragment(part, node); err != nil {
				return err
			}
		} else if len(s.stack) == 0 {
			s.closed = true
		} else {
			return nil
		}
		if err := p.activateStreamIndex(); err != nil {
			return err
		}
		if strings.EqualFold(part.name, "/_rels/.rels") {
			if err := p.emitMetadataCallbacks(); err != nil {
				return err
			}
		}
		if p.index != nil {
			if strings.EqualFold(part.name, "/_rels/.rels") {
				if s.discards[formatNamespace(p.index.format)+"/discard-control"] > 1 {
					return fmt.Errorf("%w: multiple discard control relationships", ErrInvalid)
				}
				if err := p.recordRelationshipHints("/", s.items); err != nil {
					return err
				}
				if p.options.OnPage != nil {
					if err := p.updateDiscard(p.index); err != nil {
						return err
					}
				}
				if err := p.applyLayoutIndex(); err != nil {
					return err
				}
				if err := p.emitMetadataCallbacks(); err != nil {
					return err
				}
				return p.emitReadyPages(part.name)
			}
			needed := s.closed
			ticketBound := false
			structBound := false
			requiredType := formatNamespace(p.index.format) + "/required-resource"
			ticketType := formatNamespace(p.index.format) + "/printticket"
			structType := formatNamespace(p.index.format) + "/documentstructure"
			for _, item := range s.items[before:] {
				if item.Type == requiredType {
					needed = true
				}
				if item.Type == ticketType {
					needed = true
					ticketBound = true
				}
				if item.Type == structType {
					structBound = true
				}
			}
			if structBound || ticketBound || s.closed {
				if err := p.recordRelationshipHints(relationshipSource(part.name), s.items); err != nil {
					return err
				}
				if err := p.emitMetadataCallbacks(); err != nil {
					return err
				}
			}
			if ticketBound {
				p.pageWait = nil
			}
			if needed {
				return p.emitReadyPages(part.name)
			}
		}
	}
	return nil
}

// relationshipFragment 共用关系元数据的兼容处理及解析，重复ID在整个逻辑部件内累积
// 入参: part 关系部件, child 闭合直接子树，nil校验根声明
// 返回: error 兼容性、结构、值或根关联重复错误
func (p *streamPackage) relationshipFragment(part *streamPart, child *xmlElement) error {
	s := part.relations
	fragment := &xmlElement{Name: s.root.Name, Attr: s.root.Attr, Namespaces: s.root.Namespaces}
	if child != nil {
		fragment.Children = []*xmlElement{child}
	}
	root, err := preprocessXMLContext(fragment, []string{opcRelsNS}, p.context)
	if err != nil {
		return err
	}
	source := relationshipSource(part.name)
	return opcMetadataElements(root, opcRelsNS, "Relationships", func(element xml.StartElement, attrs map[string]string) error {
		rel, err := parseRelationship(source, element, attrs, s.ids)
		if err != nil {
			return err
		}
		if source == "/" {
			switch rel.Type {
			case xpsNamespace + "/fixedrepresentation", openXPSNamespace + "/fixedrepresentation":
				if s.fixed {
					return fmt.Errorf("%w: multiple fixed representations", ErrInvalid)
				}
				s.fixed = true
			case xpsNamespace + "/discard-control", openXPSNamespace + "/discard-control":
				s.discards[rel.Type]++
			}
		}
		s.items = append(s.items, rel)
		return nil
	})
}

// relationshipSnapshot 为临时消费者提供独立关系前缀，未结束时记录当前页面等待的元数据部件
// 入参: source 规范源URI，包根为/
// 返回: []Relationship 独立前缀, bool 是否由流式状态处理, error 源或元数据错误
func (p *streamPackage) relationshipSnapshot(source string) ([]Relationship, bool, error) {
	if source != "/" && p.parts[strings.ToLower(source)] == nil {
		return nil, false, nil
	}
	name := createdRelationshipPart(source)
	part := p.parts[strings.ToLower(name)]
	if part == nil || part.relations == nil || part.relations.root == nil || part.relations.deferred {
		if source != "/" {
			if _, present := p.pagePkg.parts[strings.ToLower(source)]; !present {
				if _, complete := p.pagePkg.parts[strings.ToLower(name)]; complete {
					items, err := p.pagePkg.readRelationships(source, name)
					return items, true, err
				}
				if p.pageWait != nil {
					p.pageWait[strings.ToLower(name)] = true
				}
				return nil, true, nil
			}
		}
		return nil, false, nil
	}
	if !part.relations.closed && p.pageWait != nil {
		p.pageWait[strings.ToLower(name)] = true
	}
	return slices.Clone(part.relations.items), true, nil
}

// advanceRelationshipPart 推进规范关系部件的已到达分片，声明类型与元数据预算仍须成立
// 入参: name 关系部件URI
// 返回: error 类型、XML、预算或回调错误
func (p *streamPackage) advanceRelationshipPart(name string) error {
	part := p.parts[strings.ToLower(name)]
	if part == nil {
		return nil
	}
	media := p.types.declaredContentType(name)
	if !strings.EqualFold(media, opcRelsType) {
		return fmt.Errorf("%w: streamed relationship content type", ErrInvalid)
	}
	return p.advanceXML(part, media)
}

// activateStreamIndex 在固定表示关系明确后建立临时索引，没有闭合固定表示时继续接收
// 返回: error 完整根或已闭合关联错误
func (p *streamPackage) activateStreamIndex() error {
	if p.index != nil || p.pagePkg == nil {
		return nil
	}
	root := p.parts["/_rels/.rels"]
	if root != nil && root.relations != nil && !root.relations.deferred {
		if !root.relations.fixed && !root.relations.closed {
			return nil
		}
	} else if _, complete := p.pagePkg.parts["/_rels/.rels"]; !complete {
		return nil
	}
	index := &Reader{pkg: p.pagePkg, limits: p.options.Limits}
	if err := index.readFixedRepresentation(); err != nil {
		return err
	}
	p.index, p.seenPages, p.documentKeys = index, make(map[string]bool), make(map[string]bool)
	p.index.fixedXML = p.closedPageRoot
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		part := p.parts[key]
		if !opcRelationshipName(part.name) || !part.relsVerified || part.relsRecorded || part.relations == nil || part.relations.deferred {
			continue
		}
		if err := p.recordVerifiedRelationships(relationshipSource(part.name), part.relations.items); err != nil {
			return err
		}
		part.relsRecorded = true
	}
	return nil
}

// rootRelationshipsPending 判断包根关系部件是否仍处于增量接收阶段
// 返回: bool 根关系尚未结束
func (p *streamPackage) rootRelationshipsPending() bool {
	part := p.parts["/_rels/.rels"]
	if part != nil && part.relations != nil && !part.relations.deferred {
		return !part.relations.closed
	}
	_, complete := p.pagePkg.parts["/_rels/.rels"]
	return !complete
}

// verifyStreamRelationshipPrefix 核对最终完整关系列表与流式增量阶段记录的关系前缀完全一致
// 入参: part 关系部件状态, items 完整解析的关系列表
// 返回: error 前缀长度或内容冲突错误
func verifyStreamRelationshipPrefix(part *streamPart, items []Relationship) error {
	if part.relations == nil || part.relations.deferred {
		return nil
	}
	if len(items) < len(part.relations.items) {
		return fmt.Errorf("%w: streamed relationship prefix length", ErrInvalid)
	}
	for index, item := range part.relations.items {
		if items[index] != item {
			return fmt.Errorf("%w: streamed relationship prefix conflict", ErrInvalid)
		}
	}
	return nil
}

// finishRelationships 用完整索引校验前向关系结果及源存在性，较晚的关系错误不能被早期页面掩盖
// 入参: r 最终读取器
// 返回: error 关系、源、前缀冲突或取消错误
func (p *streamPackage) finishRelationships(r *Reader) error {
	if !p.needsIndex() {
		return nil
	}
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		part := p.parts[key]
		if !opcRelationshipName(part.name) {
			continue
		}
		if err := checkContext(p.context); err != nil {
			return err
		}
		items, err := r.pkg.relationships(relationshipSource(part.name))
		if err != nil {
			return err
		}
		if err := verifyStreamRelationshipPrefix(part, items); err != nil {
			return err
		}
	}
	return nil
}

// documentIndexByPart 按规范化固定文档URI查找所属文档序号，未发现返回-1
// 入参: part 固定文档部件URI
// 返回: int 文档零基序号或-1
func (p *streamPackage) documentIndexByPart(part string) int {
	for i, doc := range p.documents {
		if strings.EqualFold(doc, part) {
			return i
		}
	}
	if p.index != nil {
		for i, doc := range p.index.documents {
			if strings.EqualFold(doc.Part, part) {
				return i
			}
		}
	}
	return -1
}

// documentEndPage 计算指定文档在全局页序列中的结束位置（不含）
// 入参: source 当前文档索引, docIndex 文档序号
// 返回: int 累计总页数
func (p *streamPackage) documentEndPage(source *Reader, docIndex int) int {
	total := 0
	for i := 0; i <= docIndex && i < len(source.documents); i++ {
		total += len(source.documents[i].Pages)
	}
	return total
}

// openNextDocument 激活下一待开始文档并触发可选OnDocumentStart回调
// 入参: source 当前文档索引
// 返回: int 刚开启的文档零基序号, error 回调或取消错误
func (p *streamPackage) openNextDocument(source *Reader) (int, error) {
	d := p.nextDocumentStart
	p.activeDocument = d + 1
	p.nextDocumentStart = d + 1
	if p.options.OnDocumentStart != nil {
		if err := p.options.OnDocumentStart(p.context, StreamDocumentEvent{DocumentIndex: d, Part: source.documents[d].Part, PageCount: 0, BytesRead: p.input.count}); err != nil {
			return 0, err
		}
		if err := checkContext(p.context); err != nil {
			return 0, err
		}
	}
	return d, nil
}

// ensureDocumentStarted 确保目标文档已触发OnDocumentStart并按序关闭前序文档
// 入参: source 当前文档索引, docIndex 目标文档序号
// 返回: error 回调或取消错误
func (p *streamPackage) ensureDocumentStarted(source *Reader, docIndex int) error {
	if source == nil {
		return nil
	}
	if p.activeDocument > 0 && p.activeDocument-1 < docIndex {
		if err := p.closeActiveDocument(source); err != nil {
			return err
		}
	}
	for p.nextDocumentStart <= docIndex && p.nextDocumentStart < len(source.documents) {
		if p.activeDocument > 0 {
			if err := p.closeActiveDocument(source); err != nil {
				return err
			}
		}
		d, err := p.openNextDocument(source)
		if err != nil {
			return err
		}
		if d < docIndex {
			if err := p.closeActiveDocument(source); err != nil {
				return err
			}
		}
	}
	return nil
}

// closeActiveDocument 关闭当前活跃文档并触发OnDocumentEnd，携带精确页数与当前读取进度
// 入参: source 当前文档索引
// 返回: error 回调或取消错误
func (p *streamPackage) closeActiveDocument(source *Reader) error {
	if p.activeDocument <= 0 {
		return nil
	}
	d := p.activeDocument - 1
	p.activeDocument = 0
	p.deliveredDocuments++
	if p.options.OnDocumentEnd != nil && d < len(source.documents) {
		if err := p.options.OnDocumentEnd(p.context, StreamDocumentEvent{DocumentIndex: d, Part: source.documents[d].Part, PageCount: len(source.documents[d].Pages), BytesRead: p.input.count}); err != nil {
			return err
		}
		if err := checkContext(p.context); err != nil {
			return err
		}
	}
	return nil
}

// advanceDocumentEvents 按严格文档顺序推进OnDocumentStart与OnDocumentEnd边界事件及文档完成计数
// 入参: source 当前文档索引, final 是否处于EOF收尾阶段
// 返回: error 回调或取消错误
func (p *streamPackage) advanceDocumentEvents(source *Reader, final bool) error {
	if source == nil {
		return nil
	}
	for {
		if p.activeDocument == 0 {
			if p.nextDocumentStart >= len(source.documents) {
				return nil
			}
			if _, err := p.openNextDocument(source); err != nil {
				return err
			}
		}
		d := p.activeDocument - 1
		closed := final || d < p.document
		pagesReady := p.options.OnPage == nil || p.pages >= p.documentEndPage(source, d)
		if !closed || !pagesReady {
			return nil
		}
		if err := p.closeActiveDocument(source); err != nil {
			return err
		}
	}
}

// recordRelationshipHints 从当前已解析关系前缀中提取作业票据、文档结构与核心属性目标并拒绝包根非法票据关系
// 入参: source 关系源URI, items 关系列表
// 返回: error 关系目标合法性错误
func (p *streamPackage) recordRelationshipHints(source string, items []Relationship) error {
	if p.index == nil {
		return nil
	}
	if source == "/" {
		discardTarget, err := discardControlTarget(items, p.index.format)
		if err != nil {
			return err
		}
		if discardTarget != "" {
			p.discardTarget = discardTarget
		}
		corePart, err := streamCorePropertiesTarget(items)
		if err != nil {
			return err
		}
		if corePart != "" {
			p.corePropsTarget = corePart
		}
		rootTicket, err := printTicketTarget("/", items, p.index.format)
		if err != nil {
			return err
		}
		if rootTicket != "" {
			return &PartError{Part: "/", Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
		}
		return nil
	}
	ticket, err := printTicketTarget(source, items, p.index.format)
	if err != nil {
		return err
	}
	sourceKey := strings.ToLower(source)
	if ticket != "" {
		if p.ticketTargets == nil {
			p.ticketTargets = make(map[string]string)
			p.ticketSources = make(map[string]string)
		}
		p.ticketTargets[sourceKey] = ticket
		p.ticketSources[sourceKey] = source
		if strings.EqualFold(source, p.index.sequence) {
			p.jobTicketTarget = ticket
		}
		if p.types != nil {
			if bit := streamTicketScopeBit(printTicketScope(p.types.declaredContentType(source))); bit != 0 {
				if p.ticketRequiredScopes == nil {
					p.ticketRequiredScopes = make(map[string]uint8)
				}
				p.ticketRequiredScopes[strings.ToLower(ticket)] |= bit
			}
		}
	}
	structTarget, err := streamReadDocumentStructureTarget(source, items, p.index.format)
	if err != nil {
		return err
	}
	if structTarget != "" {
		if p.docStructTargets == nil {
			p.docStructTargets = make(map[string]string)
		}
		p.docStructTargets[sourceKey] = structTarget
	}
	return nil
}

// recordVerifiedRelationships 校验并登记已完成全量解析的关系部件语义，支持根关系唯一性及三级票据与结构目标记录
// 入参: source 关系源URI, items 完整关系列表
// 返回: error 关系冲突或非法目标错误
func (p *streamPackage) recordVerifiedRelationships(source string, items []Relationship) error {
	if p.index == nil {
		return nil
	}
	if source == "/" {
		sequence := ""
		var selected Format
		for _, rel := range items {
			var format Format
			switch rel.Type {
			case xpsNamespace + "/fixedrepresentation":
				format = FormatXPS
			case openXPSNamespace + "/fixedrepresentation":
				format = FormatOpenXPS
			default:
				continue
			}
			if sequence != "" {
				return fmt.Errorf("%w: multiple fixed representations", ErrInvalid)
			}
			if rel.TargetMode == TargetModeExternal {
				return fmt.Errorf("%w: external fixed representation", ErrInvalid)
			}
			var err error
			sequence, err = resolvePart("/", rel.Target)
			if err != nil {
				return err
			}
			selected = format
		}
		if sequence == "" || selected != p.index.format || !strings.EqualFold(sequence, p.index.sequence) {
			return fmt.Errorf("%w: streamed fixed representation conflict", ErrInvalid)
		}
	}
	if err := p.recordRelationshipHints(source, items); err != nil {
		return err
	}
	return nil
}

// verifyConsumeRelationships 终审纯前向消费模式下全包所有关系部件的源存在性、XML合法性与前缀一致性
// 返回: error 缺失源部件、损坏关系或前缀冲突错误
func (p *streamPackage) verifyConsumeRelationships() error {
	for _, key := range slices.Sorted(maps.Keys(p.parts)) {
		part := p.parts[key]
		if !opcRelationshipName(part.name) {
			continue
		}
		if err := checkContext(p.context); err != nil {
			return err
		}
		source := relationshipSource(part.name)
		if source != "/" {
			if p.parts[strings.ToLower(source)] == nil {
				return fmt.Errorf("%w: part %q: %w", ErrNotFound, strings.ToLower(source), fs.ErrNotExist)
			}
		}
		if !part.relsVerified {
			if part.reclaimed {
				return fmt.Errorf("%w: unverified reclaimed relationship part %q", ErrInvalid, part.name)
			}
			items, err := p.pagePkg.readRelationshipsContext(p.context, source, part.name)
			if err != nil {
				return err
			}
			if err := verifyStreamRelationshipPrefix(part, items); err != nil {
				return err
			}
			part.relsVerified = true
			if err := p.recordVerifiedRelationships(source, items); err != nil {
				return err
			}
			part.relsRecorded = true
		} else if !part.relsRecorded && part.relations != nil && !part.relations.deferred {
			if err := p.recordVerifiedRelationships(source, part.relations.items); err != nil {
				return err
			}
			part.relsRecorded = true
		}
	}
	return nil
}

// verifyConsumeTicketPart 按作用域位掩码校验关联打印票据的目标存在性、媒体类型规范以及XML与Framework合法性
// 入参: target 规范票据部件URI, scope 关联作用域
// 返回: error 缺失目标、内容类型、XML、框架结构或提前回收错误
func (p *streamPackage) verifyConsumeTicketPart(target string, scope PrintScope) error {
	bit := streamTicketScopeBit(scope)
	if bit == 0 {
		return &PartError{Part: target, Err: fmt.Errorf("%w: print ticket scope", ErrInvalid)}
	}
	key := strings.ToLower(target)
	part := p.parts[key]
	if part == nil {
		return &PartError{Part: target, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
	}
	typeName := p.types.declaredContentType(target)
	if typeName == "" {
		return &PartError{Part: target, Err: fmt.Errorf("%w: no content type for %q", ErrInvalid, target)}
	}
	if p.index.format == FormatXPS && !matchStandardContentType(FormatXPS, typeName, printTicketType) {
		return &PartError{Part: target, Err: fmt.Errorf("%w: XPS print ticket content type", ErrInvalid)}
	}
	known, capabilities := printResourceMedia(opcMediaTypeBase(typeName))
	if !known || capabilities || part.ticketVerifiedScopes&bit != 0 {
		return nil
	}
	if part.reclaimed {
		return &PartError{Part: target, Err: fmt.Errorf("%w: unverified reclaimed print ticket %q", ErrInvalid, target)}
	}
	if _, exists := p.pagePkg.parts[key]; !exists {
		return &PartError{Part: target, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
	}
	data, err := p.pagePkg.readItemsContext(p.context, key, min(p.options.Limits.MaxMetadataBytes, p.options.Limits.MaxPartBytes))
	if err != nil {
		return &PartError{Part: target, Err: err}
	}
	configuration, err := printSettingsOptions(p.context, &PrintSettingsOptions{Limits: p.options.Limits, Scope: scope})
	if err != nil {
		return err
	}
	root, err := decodeXML(data, configuration.Limits)
	if err != nil {
		return &PartError{Part: target, Err: err}
	}
	if _, err := parsePrintSettings(root, configuration); err != nil {
		return &PartError{Part: target, Err: err}
	}
	if err := xmlNamespaceTreeOutput(root, p.context); err != nil {
		return &PartError{Part: target, Err: err}
	}
	part.ticketVerifiedScopes |= bit
	return nil
}

// verifyConsumeTickets 终审纯前向消费模式下全包所有票据关系来源合法性、晚到冲突与按作用域分位结构校验
// 返回: error 非法来源、票据冲突、缺失目标、媒体类型或结构错误
func (p *streamPackage) verifyConsumeTickets() error {
	jobTicket := p.jobTicketTarget
	if jobTicket == "" {
		jobTicket = p.ticketTargets[strings.ToLower(p.index.sequence)]
	}
	if p.deliveredJobSet && !strings.EqualFold(jobTicket, p.deliveredJobTicket) {
		return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
	}
	for docIdx, doc := range p.index.documents {
		docKey := strings.ToLower(doc.Part)
		finalDocTicket := p.ticketTargets[docKey]
		if deliveredDoc, ok := p.deliveredDocTickets[docIdx]; ok && !strings.EqualFold(finalDocTicket, deliveredDoc) {
			return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
		}
	}
	for _, page := range p.index.pages {
		pageKey := strings.ToLower(page.Part)
		finalPageTicket := p.ticketTargets[pageKey]
		if pagePart := p.parts[pageKey]; pagePart != nil && pagePart.pageDelivered && !pagePart.deliveredRelsClosed && !strings.EqualFold(finalPageTicket, pagePart.deliveredPageTicket) {
			return fmt.Errorf("%w: streamed page print ticket conflict", ErrInvalid)
		}
	}
	for _, sourceKey := range slices.Sorted(maps.Keys(p.ticketTargets)) {
		if err := checkContext(p.context); err != nil {
			return err
		}
		target := p.ticketTargets[sourceKey]
		if target == "" {
			continue
		}
		source := p.ticketSources[sourceKey]
		if source == "" {
			source = sourceKey
		}
		if source == "/" {
			return &PartError{Part: "/", Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
		}
		media := p.types.declaredContentType(source)
		scope := printTicketScope(media)
		if media == "" || scope == PrintScopeUnknown {
			return &PartError{Part: source, Err: fmt.Errorf("%w: print ticket source", ErrInvalid)}
		}
		if err := p.verifyConsumeTicketPart(target, scope); err != nil {
			return err
		}
	}
	return nil
}

// verifyConsumeMetadataBounds 终审纯前向消费模式下所有已解析文档结构的故事页码上界及回调目标存在性
// 返回: error 页码越界或缺失目标错误
func (p *streamPackage) verifyConsumeMetadataBounds() error {
	for docIdx, maxPage := range p.docStructMaxPage {
		if docIdx >= 0 && docIdx < len(p.index.documents) && maxPage > len(p.index.documents[docIdx].Pages) {
			return fmt.Errorf("%w: story page %d outside its fixed document", ErrInvalid, maxPage)
		}
	}
	if p.options.OnCoreProperties != nil && !p.corePropsDelivered && p.corePropsTarget != "" {
		key := strings.ToLower(p.corePropsTarget)
		if p.parts[key] == nil {
			return &PartError{Part: p.corePropsTarget, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
		}
	}
	if p.options.OnDocumentStructure != nil {
		for docIdx, doc := range p.index.documents {
			if p.docStructDelivered != nil && p.docStructDelivered[docIdx] {
				continue
			}
			target := p.docStructTargets[strings.ToLower(doc.Part)]
			if target == "" {
				continue
			}
			key := strings.ToLower(target)
			if p.parts[key] == nil {
				return &PartError{Part: target, Err: fmt.Errorf("%w: part %q: %w", ErrNotFound, key, fs.ErrNotExist)}
			}
		}
	}
	return nil
}
