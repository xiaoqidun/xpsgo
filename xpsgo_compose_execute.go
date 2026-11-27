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
	"crypto/sha256"
	"encoding/xml"
	"errors"
	"fmt"
	"maps"
	"math"
	"net/url"
	"slices"
	"strings"
)

// compositionExecution 将一次规划落实为独立包，候选结果通过完整校验后才交还调用方
type compositionExecution struct {
	plan              *compositionPlan
	names             *compositionNames
	navigation        *compositionNavigation
	output            *Package
	protected         []map[string]bool
	targets           map[compositionExecutionPart]string
	relationshipsDone map[compositionRelationshipKey]bool
	queue             []compositionExecutionPart
	generated         map[compositionPartKey][]byte
	originals         map[compositionPartKey]packagePart
	tickets           map[string][]string
	stories           *compositionStories
	storyParts        map[string]string
	storyQueue        []compositionStoryPending
	documents         [][]compositionOrigin
	signatures        *compositionSignatures
	requests          []compositionPartKey
	hints             []compositionSignatureHint
	owners            map[string]compositionOrigin
	localPages        []map[compositionPageKey]int
	rawDocs           map[int]bool
	docParts          map[compositionOrigin][]int
	rawSequence       int
	dedupResources    map[compositionResourceDigest]string
	digestCache       map[compositionOrigin]compositionResourceDigest
	pageTransformed   map[int]bool
}

// compositionResourceDigest 以规范内容类型与内容SHA-256摘要唯一标识可跨源复用的静态二进制资源
type compositionResourceDigest struct {
	media string
	hash  [32]byte
}

// compositionExecutionPart 保存输出部件的实际页面归属及派生主序列角色
type compositionExecutionPart struct {
	compositionPartKey
	owner           string
	primarySequence bool
}

// compositionOrigin 标识一次输出关联所来自的原包及原拥有部件
type compositionOrigin struct {
	source int
	part   string
}

// compositionRelationshipKey 区分同址资源的页面归属、派生角色及故事投影
type compositionRelationshipKey struct {
	owner   compositionExecutionPart
	target  string
	project bool
	story   string
}

// compositionSignatureHint 保存受保护原文中的位置身份，不将可选提示变成资源依赖
type compositionSignatureHint struct {
	source int
	part   string
}

// compositionStoryPending 保存待改写的目录，输出硬依赖规划完成后再解析导航
type compositionStoryPending struct {
	key    compositionPartKey
	target string
	index  int
}

// executeCompositionPlan 按组合规划构建独立输出包并完成全量校验，不修改源快照
// 入参: plan 独立组合规划, names 对应的页面名称映射, rootSource 包级元数据来源
// 返回: *Package 可独立写出的候选包，失败为nil, error 结构、许可、支持范围、预算或取消错误
func executeCompositionPlan(plan *compositionPlan, names *compositionNames, rootSource int) (*Package, error) {
	if names.budget != plan.budget || len(names.pages) != len(plan.pages) || len(plan.indices) != len(plan.sources) || rootSource < 0 || rootSource >= len(plan.sources) || plan.indices[rootSource] == nil {
		return nil, fmt.Errorf("%w: composition execution input", ErrInvalid)
	}
	if err := plan.budget.step(len(plan.sources)); err != nil {
		return nil, err
	}
	if plan.mixed {
		return nil, fmt.Errorf("%w: composition dialect conversion", ErrUnsupported)
	}
	x := &compositionExecution{plan: plan, names: names, protected: make([]map[string]bool, len(plan.sources)), targets: make(map[compositionExecutionPart]string), generated: make(map[compositionPartKey][]byte), originals: make(map[compositionPartKey]packagePart), tickets: make(map[string][]string), storyParts: make(map[string]string), owners: make(map[string]compositionOrigin), rawDocs: make(map[int]bool), docParts: make(map[compositionOrigin][]int)}
	if plan.deduplicateResources {
		x.dedupResources = make(map[compositionResourceDigest]string)
		x.digestCache = make(map[compositionOrigin]compositionResourceDigest)
	}
	if len(plan.transforms) == len(plan.pages) {
		x.pageTransformed = make(map[int]bool)
		for i, tr := range plan.transforms {
			if tr.rotate != 0 || tr.cropBox != nil || tr.targetWidth > 0 || tr.targetHeight > 0 {
				x.pageTransformed[i] = true
			}
		}
	}
	for source, value := range plan.sources {
		if plan.indices[source] == nil {
			continue
		}
		var report *compositionFontReport
		if source < len(plan.fonts) {
			report = plan.fonts[source]
		}
		var err error
		if report == nil {
			report, err = validateCompositionFonts(value, plan.budget)
			if err != nil {
				return nil, err
			}
		}
		for part := range report.restricted {
			if !value.restricted[part] {
				return nil, fmt.Errorf("%w: composition protection root is absent", ErrRestricted)
			}
		}
		if source < len(plan.protected) && plan.protected[source] != nil {
			x.protected[source] = plan.protected[source]
		} else {
			x.protected[source], err = compositionProtection(value, plan.budget)
			if err != nil {
				return nil, err
			}
		}
		for part := range x.protected[source] {
			if err := plan.budget.step(1); err != nil {
				return nil, err
			}
			if !opcRelationshipName(part) && plan.fixed[compositionPartKey{source, part, -1, -1}] != value.parts[part].name {
				return nil, fmt.Errorf("%w: composition protected identity was not reserved", ErrRestricted)
			}
		}
	}
	var err error
	x.signatures, err = newCompositionSignatures(plan, x.protected)
	if err != nil {
		return nil, err
	}
	x.navigation, err = newCompositionNavigation(plan, names.pages, names.droppedTargets)
	if err != nil {
		return nil, err
	}
	x.stories, err = newCompositionStories(plan, names)
	if err != nil {
		return nil, err
	}
	x.output, err = NewPackage(plan.format, &PackageOptions{Limits: plan.budget.limits, MaxImagePixels: plan.maxImagePixels})
	if err != nil {
		return nil, err
	}
	p := x.output
	clear(p.names)
	clear(p.parents)
	clear(p.layout)
	p.sequence, p.pageCount = plan.sequence, len(plan.pages)
	p.original, p.originalRels = make(map[string]packagePart), make(map[string][]Relationship)
	p.documents = make([]Document, len(x.navigation.output.source.documents))
	for docIdx, doc := range x.navigation.output.source.documents {
		doc.Pages = slices.Clone(doc.Pages)
		p.documents[docIdx] = doc
	}
	if len(x.pageTransformed) != 0 {
		for i := range plan.pages {
			if !x.pageTransformed[i] {
				continue
			}
			instance := plan.pages[i]
			src := plan.sources[instance.source]
			pagePart := src.parts[strings.ToLower(src.pages[instance.index].Part)]
			origW, origH, err := readCompositionPageDimensions(pagePart, src, src.format, plan.budget.limits, plan.budget.context)
			if err != nil {
				return nil, &PartError{Part: pagePart.name, Err: err}
			}
			geom, err := computeCompositionPageGeometry(origW, origH, plan.transforms[i])
			if err != nil {
				return nil, err
			}
			p.documents[instance.document].Pages[instance.position].Width = geom.newWidth
			p.documents[instance.document].Pages[instance.position].Height = geom.newHeight
			x.navigation.output.source.documents[instance.document].Pages[instance.position].Width = geom.newWidth
			x.navigation.output.source.documents[instance.document].Pages[instance.position].Height = geom.newHeight
		}
	}
	x.documents = make([][]compositionOrigin, len(plan.documents))
	x.localPages = make([]map[compositionPageKey]int, len(plan.documents))
	p.registerName(p.sequence)
	p.registerName("/_rels/.rels")
	p.layout[strings.ToLower(p.sequence)] = true
	for _, document := range p.documents {
		p.registerName(document.Part)
		p.layout[strings.ToLower(document.Part)] = true
		for _, page := range document.Pages {
			p.registerName(page.Part)
			p.layout[strings.ToLower(page.Part)] = true
		}
	}
	seenDocuments := make([]map[compositionOrigin]bool, len(plan.documents))
	for i, instance := range plan.pages {
		key := compositionPartKey{instance.source, strings.ToLower(plan.sources[instance.source].pages[instance.index].Part), instance.document, i}
		if err := x.schedule(key, instance.reference.Part); err != nil {
			return nil, err
		}
		original, _, err := plan.documentPage(instance.source, instance.index)
		if err != nil {
			return nil, err
		}
		origin := compositionOrigin{instance.source, plan.sources[instance.source].documents[original].Part}
		if seenDocuments[instance.document] == nil {
			seenDocuments[instance.document] = make(map[compositionOrigin]bool)
			x.localPages[instance.document] = make(map[compositionPageKey]int)
		}
		pageKey := compositionPageKey{instance.source, instance.index}
		if _, exists := x.localPages[instance.document][pageKey]; !exists {
			x.localPages[instance.document][pageKey] = i
		}
		if !seenDocuments[instance.document][origin] {
			seenDocuments[instance.document][origin] = true
			x.documents[instance.document] = append(x.documents[instance.document], origin)
		}
	}
	for index, document := range plan.documents {
		if document.complete && document.source >= 0 && document.original >= 0 {
			source := plan.sources[document.source]
			part := strings.ToLower(source.documents[document.original].Part)
			if source.retained[part] {
				identity := true
				for _, page := range document.pages {
					if len(names.droppedTargets[page]) != 0 || x.pageTransformed[page] {
						identity = false
						break
					}
					for original, target := range names.pages[page] {
						if err := plan.budget.step(1); err != nil {
							return nil, err
						}
						if original != target {
							identity = false
							break
						}
					}
					if !identity {
						break
					}
				}
				if identity {
					x.rawDocs[index] = true
					origin := compositionOrigin{document.source, part}
					x.docParts[origin] = append(x.docParts[origin], index)
					if err := x.schedule(compositionPartKey{document.source, part, index, -1}, document.part); err != nil {
						return nil, err
					}
				} else if source.sourceFormat == FormatOpenXPS && plan.format == FormatXPS {
					data, err := normalizeCompositionDocumentLinkTargets(source.parts[part], document, plan, names)
					if err != nil {
						return nil, err
					}
					if err := x.put(source.parts[part], document.part, data); err != nil {
						return nil, err
					}
				}
			}
		}
	}
	if err := x.prepareSequence(); err != nil {
		return nil, err
	}
	for source, parts := range x.protected {
		for part := range parts {
			if opcRelationshipName(part) {
				continue
			}
			if _, err := x.resource(compositionPartKey{source, part, -1, -1}, part); err != nil {
				return nil, err
			}
		}
	}
	if err := x.projectStories(); err != nil {
		return nil, err
	}
	if err := x.mainRelationships(rootSource); err != nil {
		return nil, err
	}
	for position := 0; position < len(x.queue); position++ {
		if err := x.prepare(x.queue[position]); err != nil {
			return nil, err
		}
	}
	if err := x.finishStories(); err != nil {
		return nil, err
	}
	for position := 0; position < len(x.queue); position++ {
		if err := x.part(x.queue[position]); err != nil {
			return nil, err
		}
	}
	for _, key := range x.requests {
		if err := x.signature(key); err != nil {
			return nil, err
		}
	}
	if err := x.validateTickets(); err != nil {
		return nil, err
	}
	view, err := p.reader(plan.budget.context)
	if err != nil {
		return nil, err
	}
	defer view.Close()
	if err := x.validateSignatureHints(view.pkg); err != nil {
		return nil, err
	}
	for source, parts := range x.protected {
		for key := range parts {
			if err := plan.budget.step(1); err != nil {
				return nil, err
			}
			original := plan.sources[source].parts[key]
			data, err := view.pkg.readItemsContext(plan.budget.context, key, view.pkg.limits.MaxPartBytes)
			if err != nil {
				return nil, err
			}
			media, err := view.pkg.contentType(original.name)
			if err != nil || !strings.EqualFold(media, original.media) || view.pkg.names[key] != original.name || !bytes.Equal(data, original.data) {
				return nil, fmt.Errorf("%w: composition changed protected part %s", ErrRestricted, original.name)
			}
			p.protected[key] = true
		}
	}
	if err := plan.budget.step(0); err != nil {
		return nil, err
	}
	return p, nil
}

// schedule 登记已分配名称的部件实例，避免重复展开同一输出归属
// 入参: key 源身份及输出归属, target 已分配输出URI
// 返回: error 身份冲突、工作量或取消错误
func (x *compositionExecution) schedule(key compositionPartKey, target string) error {
	return x.schedulePart(x.instance(key), target)
}

// instance 补充页面部件的原始身份，非页面资源缺省不绑定页面
// 入参: key 基本输出归属
// 返回: compositionExecutionPart 实际部件归属
func (x *compositionExecution) instance(key compositionPartKey) compositionExecutionPart {
	item := compositionExecutionPart{compositionPartKey: key}
	if part := x.plan.sources[key.source].parts[key.part]; strings.EqualFold(part.media, fixedContentType("fixedpage")) {
		item.owner = part.name
	}
	return item
}

// schedulePart 按实际原页面归属登记字典副本，避免共享资源URI混淆相对导航
// 入参: item 源身份及所属原页面, target 输出URI
// 返回: error 身份冲突、工作量或取消错误
func (x *compositionExecution) schedulePart(item compositionExecutionPart, target string) error {
	if err := x.plan.budget.step(1); err != nil {
		return err
	}
	if previous, exists := x.targets[item]; exists {
		if previous != target {
			return fmt.Errorf("%w: inconsistent composition target", ErrInvalid)
		}
		return nil
	}
	origin := compositionOrigin{item.source, item.part}
	if previous, exists := x.owners[strings.ToLower(target)]; exists && previous != origin {
		return fmt.Errorf("%w: composition aliases different source identities", ErrInvalid)
	}
	x.owners[strings.ToLower(target)] = origin
	x.targets[item] = target
	x.queue = append(x.queue, item)
	return nil
}

// resource 将资源绑定到实际输出实例，字典按页面归属分配，二进制资源按来源共享
// 入参: owner 引用所在实例, part 原资源规范URI
// 返回: string 输出URI, error 缺失、布局边界、名称、预算或取消错误
func (x *compositionExecution) resource(owner compositionPartKey, part string) (string, error) {
	return x.resourceFor(x.instance(owner), part)
}

// resourceFor 将硬依赖绑定到实际页面归属，非主页面的远程字典使用独立实例
// 入参: owner 引用所在部件及原页面, part 原资源规范URI
// 返回: string 输出URI, error 缺失、布局边界、名称、预算或取消错误
func (x *compositionExecution) resourceFor(owner compositionExecutionPart, part string) (string, error) {
	return x.resourceTarget(owner, part, true)
}

// resourceTarget 绑定资源，关系保留检查仅查询原身份是否可用，不占用候选资源的输出额度
// 入参: owner 引用归属, part 原资源URI, schedule 是否分配身份并登记待输出资源
// 返回: string 输出URI，试探需迁移时为空, error 引用、名称、预算或取消错误
func (x *compositionExecution) resourceTarget(owner compositionExecutionPart, part string, schedule bool) (string, error) {
	if err := x.plan.budget.step(1); err != nil {
		return "", err
	}
	source := x.plan.sources[owner.source]
	key := compositionPartKey{owner.source, strings.ToLower(part), -1, -1}
	value, exists := source.parts[key.part]
	if !exists {
		return "", &PartError{Part: part, Err: fmt.Errorf("%w: composition resource is absent", ErrInvalid)}
	}
	if strings.EqualFold(value.media, resourceDictionaryContentType) {
		key.document, key.page = owner.document, owner.page
	}
	if strings.EqualFold(value.media, fixedContentType("fixeddocument")) {
		if name, exists := x.rawDocumentTarget(owner.source, part, owner.document); exists {
			return name, nil
		}
	}
	pagePart := strings.EqualFold(value.media, fixedContentType("fixedpage"))
	if pagePart {
		original := x.originalPage(owner.source, part)
		if original >= 0 && (owner.document >= 0 || !source.auxiliary[key.part] && !source.retained[key.part]) {
			if owner.document >= 0 && owner.page < 0 && x.rawDocs[owner.document] {
				if i, exists := x.localPages[owner.document][compositionPageKey{owner.source, original}]; exists {
					return x.plan.pages[i].reference.Part, nil
				}
			}
			i, err := x.plan.target(owner.source, original, owner.page)
			if err == nil && i >= 0 {
				return x.plan.pages[i].reference.Part, nil
			}
		}
		if !source.auxiliary[key.part] && !source.retained[key.part] {
			return "", fmt.Errorf("%w: composition hard reference to unselected layout", ErrUnsupported)
		}
		if owner.document >= 0 && x.rawDocs[owner.document] {
			key.document = owner.document
		}
	}
	item := x.instance(key)
	if strings.EqualFold(value.media, resourceDictionaryContentType) {
		item.owner = owner.owner
	}
	if name, exists := x.targets[item]; exists {
		return name, nil
	}
	var dedupDigest compositionResourceDigest
	dedupEligible := false
	if x.plan.deduplicateResources && key.document < 0 && key.page < 0 {
		var err error
		dedupDigest, dedupEligible, err = x.resourceDigest(key.source, key.part, value)
		if err != nil {
			return "", err
		}
		if dedupEligible && !x.protected[key.source][key.part] {
			if existing, hit := x.dedupResources[dedupDigest]; hit {
				return existing, nil
			}
		}
	}
	var name string
	var err error
	if strings.EqualFold(value.media, resourceDictionaryContentType) && key.page < 0 && item.owner != "" {
		if fixed := x.plan.fixed[compositionPartKey{key.source, key.part, -1, -1}]; fixed != "" {
			name = fixed
		} else if schedule {
			name, err = x.plan.allocate(value.name, compositionHasRelationships(source, key.part), false)
		} else if x.plan.resourceNameAvailable(value.name, compositionHasRelationships(source, key.part)) {
			name = value.name
		}
	} else {
		name, err = x.plan.resourceIdentity(key.source, value.name, key.document, key.page, schedule)
	}
	if err != nil {
		return "", err
	}
	if schedule {
		if err := x.schedulePart(item, name); err != nil {
			return "", err
		}
		if dedupEligible {
			if _, exists := x.dedupResources[dedupDigest]; !exists {
				x.dedupResources[dedupDigest] = name
			}
		}
	}
	return name, nil
}

// resourceDigest 为无差异关系的图像、ICC配置及普通或解混淆字体计算跨源复用内容摘要
// 入参: source 源快照序号, key 小写部件键, value 原部件字节与媒体类型
// 返回: compositionResourceDigest 规范媒体类型与SHA-256摘要, bool 是否允许跨源摘要去重, error 解混淆或扫描预算错误
func (x *compositionExecution) resourceDigest(source int, key string, value packagePart) (compositionResourceDigest, bool, error) {
	if !compositionDeduplicableMedia(value.media) || compositionHasRelationships(x.plan.sources[source], key) {
		return compositionResourceDigest{}, false, nil
	}
	origin := compositionOrigin{source: source, part: key}
	if cached, hit := x.digestCache[origin]; hit {
		return cached, true, nil
	}
	if err := x.plan.budget.scan(int64(len(value.data))); err != nil {
		return compositionResourceDigest{}, false, err
	}
	payload := value.data
	if strings.EqualFold(value.media, "application/vnd.ms-package.obfuscated-opentype") {
		decoded, err := DeobfuscateFont(value.name, value.data)
		if err != nil {
			return compositionResourceDigest{}, false, nil
		}
		payload = decoded
	}
	digest := compositionResourceDigest{media: strings.ToLower(value.media), hash: sha256.Sum256(payload)}
	x.digestCache[origin] = digest
	return digest, true, nil
}

// compositionDeduplicableMedia 判断内容类型是否属于支持内容摘要去重的静态二进制资源
// 入参: media 部件内容类型
// 返回: bool 是否为图像、ICC色彩配置或字体二进制资源
func compositionDeduplicableMedia(media string) bool {
	return requiredResourceMedia(requiredImage, media) || requiredResourceMedia(requiredProfile, media) || requiredResourceMedia(requiredFont, media)
}

// originalPage 查询源索引中的部件身份，不以同名的其他包页面补齐引用
// 入参: source 源序号, part 原URI
// 返回: int 原全局页号，不存在为-1
func (x *compositionExecution) originalPage(source int, part string) int {
	if scope, exists := x.navigation.sources[source].scopes[strings.ToLower(part)]; exists && scope.kind == createdNavigationPage {
		return scope.first
	}
	return -1
}

// put 存入不可变快照或新生成字节，不重复复制大资源，记录原始数据以保留物理条目信息
// 入参: original 原部件, target 输出URI, data 输出数据
// 返回: error 冲突、保护、容量或取消错误
func (x *compositionExecution) put(original packagePart, target string, data []byte) error {
	if err := x.plan.budget.step(1); err != nil {
		return err
	}
	p, key := x.output, strings.ToLower(target)
	if prior, exists := p.parts[key]; exists {
		if prior.name != target || !strings.EqualFold(prior.media, original.media) || !bytes.Equal(prior.data, data) {
			return fmt.Errorf("%w: composition shared part differs by context", ErrRestricted)
		}
		return nil
	}
	if int64(len(data)) > p.limits.MaxPartBytes || int64(len(data)) > p.limits.MaxPackageBytes-p.total || len(p.names) >= p.limits.MaxPartCount-1 && !p.names[key] {
		return fmt.Errorf("%w: composition output capacity", ErrLimit)
	}
	value := original
	value.name, value.data = target, data
	if !bytes.Equal(original.data, data) {
		value.items = nil
	}
	p.parts[key], p.original[key] = value, original
	p.registerName(target)
	p.total += int64(len(data))
	return nil
}

// part 改写布局与资源字节，复用准备阶段确定的附属关系
// 入参: item 已登记实例
// 返回: error 标记、引用、保护、容量或取消错误
func (x *compositionExecution) part(item compositionExecutionPart) error {
	if err := x.plan.budget.step(1); err != nil {
		return err
	}
	key := item.compositionPartKey
	source := x.plan.sources[key.source]
	value, target := source.parts[key.part], x.targets[item]
	if original, exists := x.originals[key]; exists {
		value = original
	}
	data, generated := x.generated[key]
	if !generated {
		data = value.data
		if strings.EqualFold(value.media, fixedContentType("signaturedefinitions")) {
			x.requests = append(x.requests, key)
			return x.relationships(target, []compositionOrigin{{key.source, value.name}}, item, false, "")
		}
		if known, _ := printResourceMedia(value.media); known {
			aliases := make(map[string]string)
			for _, reference := range source.printResources[key.part] {
				name, err := x.resourceFor(item, reference.uri)
				if err != nil {
					return err
				}
				aliases[strings.ToLower(reference.uri)] = name
			}
			var err error
			data, _, err = rewriteCompositionPrintResources(value, aliases, x.plan.budget)
			if err != nil {
				return err
			}
		} else {
			markup, err := fontUsageMarkup(value.media)
			if err != nil {
				return err
			}
			if markup {
				var index *compositionIndex
				if compositionIndexRoot(value.media) != "" {
					index, err = source.indexPart(value, x.plan.budget)
					if err != nil {
						return err
					}
					if err := index.inspect(true, x.plan.budget); err != nil {
						return err
					}
				}
				var names map[string]string
				owner := item.owner
				if key.page >= 0 {
					names = x.names.pages[key.page]
					owner = source.pages[x.plan.pages[key.page].index].Part
				}
				resolveDestination := func() (string, error) {
					if key.page >= 0 && strings.EqualFold(value.media, resourceDictionaryContentType) {
						return x.plan.pages[key.page].reference.Part, nil
					}
					if strings.EqualFold(value.media, resourceDictionaryContentType) && item.owner != "" {
						page := x.instance(compositionPartKey{key.source, strings.ToLower(item.owner), key.document, -1})
						if output, exists := x.targets[page]; exists {
							return output, nil
						}
						return "", fmt.Errorf("%w: composition dictionary output page", ErrUnsupported)
					}
					return target, nil
				}
				opts := compositionMarkupOptions{
					format:      source.format,
					destination: target,
					owner:       owner,
					names:       names,
					index:       index,
					source:      source,
					budget:      x.plan.budget,
					resource: func(part string) (string, error) {
						return x.resourceFor(item, part)
					},
					navigation: func(base, uri string) (string, bool, error) {
						destination, err := resolveDestination()
						if err != nil {
							return "", false, err
						}
						return x.navigate(item, base, destination, uri)
					},
				}
				if x.plan.stripDanglingNavigateUri {
					opts.navigationOptional = func(base, uri string) (string, bool, bool, error) {
						destination, err := resolveDestination()
						if err != nil {
							return "", false, false, err
						}
						return x.navigateOptional(item, base, destination, uri, true)
					}
				}
				data, err = rewriteCompositionMarkup(value, opts)
				if err != nil {
					return err
				}
				if key.page >= 0 && x.pageTransformed[key.page] {
					if x.protected[key.source][key.part] {
						return fmt.Errorf("%w: composition protected page transform", ErrRestricted)
					}
					maximum := min(x.plan.budget.limits.MaxPartBytes, x.plan.budget.limits.MaxPackageBytes, int64(math.MaxInt))
					data, err = transformCompositionPageMarkup(data, source.format, x.plan.transforms[key.page], maximum, x.plan.budget)
					if err != nil {
						return err
					}
				}
			}
		}
	}
	if x.protected[key.source][key.part] && !x.derivedSequence(item, target) && (value.name != target || !bytes.Equal(value.data, data)) {
		return fmt.Errorf("%w: composition protected markup rewrite", ErrRestricted)
	}
	if err := x.put(value, target, data); err != nil {
		return err
	}
	if _, synthetic := x.originals[key]; synthetic {
		return nil
	}
	return x.relationships(target, []compositionOrigin{{key.source, value.name}}, item, x.projectsStories(item), x.storyParts[strings.ToLower(target)])
}

// navigate 先按原作用域绑定链接，再迁移地址，不附带未选页面修复失效链接
// 入参: key 引用归属, base 原基准, target 输出基准, uri 原URI
// 返回: string 输出URI, bool 是否改变, error 引用、未支持作用域、预算或取消错误
func (x *compositionExecution) navigate(key compositionExecutionPart, base, target, uri string) (string, bool, error) {
	result, changed, _, err := x.navigateOptional(key, base, target, uri, false)
	return result, changed, err
}

// navigateOptional 迁移导航地址，开启allowOmitted时将指向未选中页面的内部布局导航标记为可剥离/剪枝
// 入参: key 引用归属, base 原基准, target 输出基准, uri 原URI, allowOmitted 是否允许将指向未选中页面的内部布局链接标记为省略
// 返回: string 输出URI, bool 是否改变, bool 是否指向未选中布局而省略, error 引用、未支持作用域、预算或取消错误
func (x *compositionExecution) navigateOptional(key compositionExecutionPart, base, target, uri string, allowOmitted bool) (string, bool, bool, error) {
	if value, handled, err := x.navigateRawScope(key, base, target, uri); handled || err != nil {
		return value, value != uri, false, err
	}
	binding, err := x.navigation.sources[key.source].resolve(base, uri)
	if err != nil {
		return "", false, false, err
	}
	if binding.external {
		return uri, false, false, nil
	}
	if document, exists := x.rawDocumentTarget(key.source, binding.part, key.document); exists {
		result, changed, err := rewriteCompositionScopeURI(target, uri, document, x.plan.budget)
		return result, changed, false, err
	}
	aliases := make(map[string]string)
	if binding.page < 0 && !binding.scoped {
		value := x.plan.sources[key.source].parts[strings.ToLower(binding.part)]
		if compositionLayoutMedia(value.media) {
			name := x.targets[x.instance(compositionPartKey{key.source, strings.ToLower(binding.part), key.document, -1})]
			if name == "" {
				name = x.targets[x.instance(compositionPartKey{key.source, strings.ToLower(binding.part), -1, -1})]
			}
			if name == "" {
				if allowOmitted {
					return "", false, true, nil
				}
				return "", false, false, fmt.Errorf("%w: unmaterialized auxiliary composition navigation", ErrUnsupported)
			}
			aliases[strings.ToLower(binding.part)] = name
		} else {
			name, err := x.resourceFor(key, binding.part)
			if err != nil {
				return "", false, false, err
			}
			aliases[strings.ToLower(binding.part)] = name
		}
	}
	current := key.page
	if current < 0 && key.document >= 0 && binding.scoped && binding.page >= 0 {
		if page, exists := x.localPages[key.document][compositionPageKey{key.source, binding.page}]; exists {
			current = page
		}
	}
	if allowOmitted && binding.scoped {
		if binding.page < 0 {
			return "", false, true, nil
		}
		mappedPage, targetErr := x.plan.target(key.source, binding.page, current)
		if targetErr != nil {
			return "", false, false, targetErr
		}
		if mappedPage < 0 {
			return "", false, true, nil
		}
	}
	result, changed, err := x.navigation.rewrite(key.source, base, target, uri, current, aliases)
	return result, changed, false, err
}

// prepareSequence 为单一来源的完整原序输出保留原始序列标记，不用消费后的索引替换其他兼容分支
// 返回: error 名称登记、预算或取消错误
func (x *compositionExecution) prepareSequence() error {
	selected := -1
	for source, index := range x.plan.indices {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		if index == nil {
			continue
		}
		if selected >= 0 {
			return nil
		}
		selected = source
	}
	if selected < 0 {
		return nil
	}
	source := x.plan.sources[selected]
	key := compositionPartKey{selected, strings.ToLower(source.sequence), -1, -1}
	if !source.retained[key.part] || len(source.documents) != len(x.plan.documents) {
		return nil
	}
	for index, document := range x.plan.documents {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		if document.source != selected || document.original != index || !document.complete || !x.rawDocs[index] {
			return nil
		}
	}
	x.rawSequence = selected + 1
	item := x.sequenceInstance(selected)
	if !item.primarySequence {
		x.plan.resources[key] = x.plan.sequence
	}
	return x.schedulePart(item, x.plan.sequence)
}

// sequenceInstance 区分新主入口与必须保留的原序列，资源引用仍绑定原始身份
// 入参: source 原包序号
// 返回: compositionExecutionPart 主序列的实际输出角色
func (x *compositionExecution) sequenceInstance(source int) compositionExecutionPart {
	value := x.plan.sources[source]
	item := x.instance(compositionPartKey{source, strings.ToLower(value.sequence), -1, -1})
	item.primarySequence = x.rawSequence == source+1 && x.protected[source][item.part] && value.sequence != x.plan.sequence
	return item
}

// derivedSequence 仅允许新主序列改写自己的地址，原受保护序列及其关系仍须原样验证
// 入参: item 输出实例, target 输出URI
// 返回: bool 是否为本次规划明确生成的派生主入口
func (x *compositionExecution) derivedSequence(item compositionExecutionPart, target string) bool {
	return item.primarySequence && target == x.plan.sequence
}

// rootRelationships 迁移元数据来源的有效包级关系，未修改时保留原始XML
// 入参: source 元数据来源索引
// 返回: error 关系、引用、预算或取消错误
func (x *compositionExecution) rootRelationships(source int) error {
	value := x.plan.sources[source]
	original := value.rootRelationships
	owner := x.instance(compositionPartKey{source, "/", -1, -1})
	if original.name == "" {
		return x.relationships("/", []compositionOrigin{{source, "/"}}, owner, false, "")
	}
	b := x.plan.budget
	relations, edited, err := filterCompositionRootRelationshipsRecords(original, value.format, b)
	if err != nil {
		return err
	}
	for index := range relations {
		if err := b.step(1); err != nil {
			return err
		}
		relation := &relations[index]
		if relation.TargetMode == TargetModeExternal {
			continue
		}
		target, err := resolvePart("/", relation.Target)
		if err != nil {
			return err
		}
		name := x.plan.sequence
		if relation.Type != formatNamespace(value.format)+"/fixedrepresentation" {
			name, err = x.resourceFor(owner, target)
			if err != nil {
				return err
			}
		}
		if !strings.EqualFold(name, target) {
			relation.Target, edited = name, true
		}
	}
	if !edited {
		edited, err = x.retainRelationshipTargets(compositionOrigin{source, "/"}, owner, original, false, "")
		if err != nil {
			return err
		}
	}
	data, err := compositionRelationshipMarkup(original, relations, edited, b)
	if err != nil {
		return err
	}
	if err := x.put(original, original.name, data); err != nil {
		return err
	}
	var explicit []Relationship
	for _, relation := range relations {
		if !x.output.modelRelationship(relation) {
			explicit = append(explicit, relation)
		}
	}
	x.output.relations["/"], x.output.originalRels["/"] = explicit, relations
	x.output.dirty[strings.ToLower(original.name)] = true
	x.output.dirtyRels["/"] = false
	return nil
}

// filterCompositionRootRelationships 移除原作业的签名和释放提示关联，发生编辑时输出有效分支
// 入参: value 原包根关系, format 包格式, budget 共享预算
// 返回: []byte 原编码结果，无修改时借用原字节, error XML、关系、预算或取消错误
func filterCompositionRootRelationships(value packagePart, format Format, budget *compositionBudget) ([]byte, error) {
	relations, edited, err := filterCompositionRootRelationshipsRecords(value, format, budget)
	if err != nil {
		return nil, err
	}
	return compositionRelationshipMarkup(value, relations, edited, budget)
}

// filterCompositionRootRelationshipsRecords 单遍解码并过滤包根关系中的签名与释放提示关联，返回有效关系切片与修改标记
// 入参: value 原包根关系, format 包格式, budget 共享预算
// 返回: []Relationship 过滤后的有效关系, bool 是否触发过滤编辑, error XML、关系、预算或取消错误
func filterCompositionRootRelationshipsRecords(value packagePart, format Format, budget *compositionBudget) ([]Relationship, bool, error) {
	if budget == nil || formatNamespace(format) == "" {
		return nil, false, fmt.Errorf("%w: composition root relationship input", ErrInvalid)
	}
	if int64(len(value.data)) > min(budget.limits.MaxMetadataBytes, budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes) {
		return nil, false, fmt.Errorf("%w: composition relationship capacity", ErrLimit)
	}
	if err := budget.scan(int64(len(value.data))); err != nil {
		return nil, false, err
	}
	discardType := formatNamespace(format) + "/discard-control"
	edited := false
	root, err := decodeXMLVisit(value.data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if node == nil {
			return budget.step(1)
		}
		if err := budget.step(len(node.Attr) + 1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); start && node.Name == (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
			kind, _ := node.attribute("Type")
			edited = edited || kind == opcSignatureOriginRel || kind == discardType
		}
		return nil
	})
	if err != nil {
		return nil, false, err
	}
	relations, err := parseCompositionRelationshipRoot("/", root, budget.context)
	if err != nil {
		return nil, false, err
	}
	var kept []Relationship
	for _, relation := range relations {
		if err := budget.step(1); err != nil {
			return nil, false, err
		}
		if relation.Type != opcSignatureOriginRel && relation.Type != discardType {
			kept = append(kept, relation)
		}
	}
	return kept, edited, nil
}

// rawDocumentTarget 为完整原文档保留所有分支的名称作用域，不将未选分支的名称提前降为当前首页
// 入参: source 原包序号, part 原文档URI, current 当前输出文档，非文档场景为-1
// 返回: string 输出文档URI, bool 是否具有完整原文作用域
func (x *compositionExecution) rawDocumentTarget(source int, part string, current int) (string, bool) {
	instances := x.docParts[compositionOrigin{source, strings.ToLower(part)}]
	if len(instances) == 0 {
		return "", false
	}
	if current >= 0 && x.rawDocs[current] {
		instance := x.plan.documents[current]
		if instance.source == source && strings.EqualFold(x.plan.sources[source].documents[instance.original].Part, part) {
			return instance.part, true
		}
	}
	return x.plan.documents[instances[0]].part, true
}

// navigateRawScope 保持完整布局的原始片段语义，仅使用已由硬依赖规划登记的辅助作用域
// 入参: item 输出实例, base 原导航基准, target 输出导航基准, value 原URI
// 返回: string 输出URI, bool 是否已处理, error 地址、预算或取消错误
func (x *compositionExecution) navigateRawScope(item compositionExecutionPart, base, target, value string) (string, bool, error) {
	b := x.plan.budget
	if err := b.step(1); err != nil {
		return "", false, err
	}
	if err := b.scan(int64(len(base)) + int64(len(value))); err != nil {
		return "", false, err
	}
	normalized := structureURI(value)
	if linkExternal(normalized) {
		return "", false, nil
	}
	uri, err := url.Parse(normalized)
	if err != nil || uri.RawQuery != "" || uri.ForceQuery {
		return "", false, nil
	}
	part, err := opcPartName(base)
	if err != nil {
		return "", false, err
	}
	source := x.plan.sources[item.source]
	if _, exists := source.parts[strings.ToLower(part)]; !exists {
		return "", false, fmt.Errorf("%w: composition link source is absent", ErrInvalid)
	}
	if uri.Path != "" {
		part, err = resolvePart(part, uri.EscapedPath())
		if err != nil {
			return "", false, err
		}
	}
	original := source.parts[strings.ToLower(part)]
	if !strings.EqualFold(original.media, fixedContentType("fixeddocument")) && !strings.EqualFold(original.media, fixedContentType("fixeddocumentsequence")) {
		return "", false, nil
	}
	name, exists := x.rawDocumentTarget(item.source, part, item.document)
	if !exists {
		key := compositionPartKey{item.source, strings.ToLower(part), item.document, -1}
		name = x.targets[x.instance(key)]
		if name == "" {
			key.document = -1
			name = x.targets[x.instance(key)]
		}
	}
	if name == "" {
		return "", false, nil
	}
	if err := validateLinkFragment(original.media, uri.Fragment, true); err != nil {
		return "", false, err
	}
	result, _, err := rewriteCompositionScopeURI(target, value, name, b)
	return result, true, err
}

// rewriteCompositionScopeURI 只迁移完整作用域的部件URI，名称片段及其原转义保持不变
// 入参: destination 输出引用基准, value 原导航URI, target 完整输出作用域URI, budget 共享预算
// 返回: string 输出URI, bool 是否改变, error URI、容量、预算或取消错误
func rewriteCompositionScopeURI(destination, value, target string, budget *compositionBudget) (string, bool, error) {
	if budget == nil {
		return "", false, fmt.Errorf("%w: missing composition scope budget", ErrInvalid)
	}
	if err := budget.step(1); err != nil {
		return "", false, err
	}
	if err := budget.scan(int64(len(value)) + int64(len(target)) + int64(len(destination))); err != nil {
		return "", false, err
	}
	normalized := structureURI(value)
	uri, err := url.Parse(normalized)
	if err != nil || linkExternal(normalized) || uri.RawQuery != "" || uri.ForceQuery {
		return "", false, fmt.Errorf("%w: composition document-scope URI", ErrInvalid)
	}
	resolved := destination
	if uri.Path != "" {
		resolved, err = resolvePart(destination, uri.EscapedPath())
	}
	if err == nil && strings.EqualFold(resolved, target) {
		return value, false, nil
	}
	fragment := uri.EscapedFragment()
	maximum := min(budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes)
	size := int64(len(target))
	if fragment != "" {
		if int64(len(fragment))+1 > maximum-size {
			return "", false, fmt.Errorf("%w: composition document-scope URI bytes", ErrLimit)
		}
		size += int64(len(fragment)) + 1
	}
	if size > maximum {
		return "", false, fmt.Errorf("%w: composition document-scope URI bytes", ErrLimit)
	}
	if err := budget.step(0); err != nil {
		return "", false, err
	}
	if fragment != "" {
		target += "#" + fragment
	}
	return target, target != value, nil
}

// signature 在硬依赖布局全部落实后投影请求标识及位置，不保留或生成真实签名字节
// 入参: key 请求部件实例
// 返回: error 模式、标识、位置、原文保护、容量或取消错误
func (x *compositionExecution) signature(key compositionPartKey) error {
	if err := x.plan.budget.step(1); err != nil {
		return err
	}
	value := x.plan.sources[key.source].parts[key.part]
	target := x.targets[x.instance(key)]
	data, err := rewriteCompositionSignatureMarkup(value, compositionSignatureMarkupOptions{format: x.plan.sources[key.source].format, part: target, budget: x.plan.budget, id: func(id string) (string, error) {
		return x.signatures.target(key.source, value.name, id)
	}, spot: func(uri string) (string, bool, error) {
		return x.signatureSpot(key, value.name, target, uri)
	}})
	if err != nil {
		return err
	}
	if x.protected[key.source][key.part] && (value.name != target || !bytes.Equal(value.data, data)) {
		return fmt.Errorf("%w: composition protected signature request rewrite", ErrRestricted)
	}
	return x.put(value, target, data)
}

// signatureSpot 映射签署请求页面位置，按舍弃策略省略未选普通位置，受保护请求保留原文
// 入参: key 请求身份, original 原部件URI, destination 输出部件URI, value 原PageURI
// 返回: string 输出位置, bool 是否保留SpotLocation, error 未支持URI、预算或取消错误
func (x *compositionExecution) signatureSpot(key compositionPartKey, original, destination, value string) (string, bool, error) {
	b := x.plan.budget
	if err := b.step(1); err != nil {
		return "", false, err
	}
	if err := b.scan(int64(len(value))); err != nil {
		return "", false, err
	}
	normalized := structureURI(value)
	if linkExternal(normalized) {
		return value, true, nil
	}
	uri, err := url.Parse(normalized)
	if err != nil || uri.RawQuery != "" || uri.ForceQuery || uri.Fragment != "" || uri.RawFragment != "" {
		return "", false, fmt.Errorf("%w: opaque composition signature location", ErrUnsupported)
	}
	part := original
	if uri.Path != "" {
		part, err = resolvePart(original, uri.EscapedPath())
		if err != nil {
			return "", false, fmt.Errorf("%w: non-package composition signature location", ErrUnsupported)
		}
	}
	partKey := strings.ToLower(part)
	target := ""
	if page := x.originalPage(key.source, part); page >= 0 {
		index, err := x.plan.target(key.source, page, -1)
		if err != nil {
			return "", false, err
		}
		if index >= 0 {
			target = x.plan.pages[index].reference.Part
		}
	}
	if target == "" {
		if value, exists := x.plan.sources[key.source].parts[partKey]; exists && strings.EqualFold(value.media, fixedContentType("fixedpage")) {
			target = x.targets[x.instance(compositionPartKey{key.source, partKey, -1, -1})]
		}
	}
	if target == "" {
		if x.protected[key.source][key.part] {
			x.hints = append(x.hints, compositionSignatureHint{key.source, partKey})
			return value, true, nil
		}
		if !x.plan.discardSignatureLocations {
			return "", false, fmt.Errorf("%w: composition omits a signature location", ErrUnsupported)
		}
		return "", false, nil
	}
	resolved, err := resolvePart(destination, uri.EscapedPath())
	if uri.Path == "" {
		resolved, err = destination, nil
	}
	if err == nil && strings.EqualFold(resolved, target) {
		return value, true, nil
	}
	if err := b.scan(int64(len(target))); err != nil {
		return "", false, err
	}
	return target, true, nil
}

// validateSignatureHints 防止保持原文的可选位置因另一个来源复用URI而意外指向其内容
// 入参: pkg 实际生成的包索引
// 返回: error 保护冲突、预算或取消错误
func (x *compositionExecution) validateSignatureHints(pkg *packageReader) error {
	for _, hint := range x.hints {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		if _, present := pkg.parts[hint.part]; !present {
			continue
		}
		if x.owners[hint.part] != (compositionOrigin{hint.source, hint.part}) {
			return fmt.Errorf("%w: protected signature hint rebound to another source", ErrRestricted)
		}
	}
	return nil
}

// prepare 在改写导航前登记实际输出闭包，避免部件排列顺序影响辅助布局的可寻址性
// 入参: item 已登记的输出实例
// 返回: error 引用、标记、预算或取消错误
func (x *compositionExecution) prepare(item compositionExecutionPart) error {
	if err := x.plan.budget.step(1); err != nil {
		return err
	}
	key, source := item.compositionPartKey, x.plan.sources[item.source]
	if _, synthetic := x.originals[key]; synthetic {
		return nil
	}
	value := source.parts[key.part]
	if _, generated := x.generated[key]; !generated {
		if known, _ := printResourceMedia(value.media); known {
			for _, reference := range source.printResources[key.part] {
				if _, err := x.resourceFor(item, reference.uri); err != nil {
					return err
				}
			}
		} else if markup, err := fontUsageMarkup(value.media); err != nil {
			return err
		} else if markup {
			if err := x.prepareMarkup(item, value); err != nil {
				return err
			}
		}
	}
	return x.prepareRelationships(item, value.name)
}

// prepareMarkup 解析全部已知兼容分支中的硬引用，导航仅登记已有的非布局资源
// 入参: item 输出实例及实际页面归属, value 原始布局部件
// 返回: error 标记、依赖、预算或取消错误
func (x *compositionExecution) prepareMarkup(item compositionExecutionPart, value packagePart) error {
	b := x.plan.budget
	if err := b.scan(int64(len(value.data))); err != nil {
		return err
	}
	source := x.plan.sources[item.source]
	format := source.format
	var tracker *resourceMarkupScopeTracker
	if compositionIndexRoot(value.media) != "" {
		tracker = newResourceMarkupIgnoreTracker(format, format == FormatOpenXPS, b.context)
	} else {
		tracker = newResourceMarkupScopeTracker(format, format == FormatOpenXPS, b.context)
	}
	visit := func(token xml.Token, node *xmlElement) error {
		if err := b.step(1); err != nil {
			return err
		}
		skip, _, err := tracker.visit(token, node)
		if err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start || skip {
			return nil
		}
		if node.Name.Space != formatNamespace(format) && !(format == FormatOpenXPS && node.Name.Space == openXPS3DNamespace) {
			return nil
		}
		for _, attr := range node.Attr {
			if err := b.step(1); err != nil {
				return err
			}
			if resourceIdentityAttribute(node, attr, format) {
				base := value.name
				if strings.EqualFold(value.media, resourceDictionaryContentType) && item.owner != "" {
					base = item.owner
				}
				if err := x.prepareNavigation(item, base, attr.Value); err != nil {
					return err
				}
				continue
			}
			if attr.Name == (xml.Name{Local: "Source"}) && (node.Name.Local == "PageContent" || node.Name.Local == "DocumentReference") {
				part, err := resolvePart(value.name, attr.Value)
				if err != nil {
					return err
				}
				if _, err := x.resourceFor(item, part); err != nil {
					return err
				}
				continue
			}
			references, err := resourceAttributeReferences(node, attr)
			if err != nil {
				return err
			}
			for _, reference := range references {
				part, err := resolvePart(value.name, reference.uri)
				if err != nil {
					return err
				}
				if _, err := x.resourceFor(item, part); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if cached := source.cachedXML(value, b.limits); cached != nil {
		return visitXMLElementTree(cached, visit)
	}
	_, err := decodeXMLVisit(value.data, b.limits, visit)
	return err
}

// prepareRelationships 先确定关系输出视图，仅为原样保留的关系展开全部兼容分支
// 入参: item 输出实例, owner 原关系拥有部件
// 返回: error 关系、依赖、预算或取消错误
func (x *compositionExecution) prepareRelationships(item compositionExecutionPart, owner string) error {
	target := x.targets[item]
	return x.relationships(target, []compositionOrigin{{item.source, owner}}, item, x.projectsStories(item), x.storyParts[strings.ToLower(target)])
}

// prepareNavigation 登记非布局导航资源的硬依赖，不以导航为理由复制额外页面或文档
// 入参: item 输出实例, base 原导航基准, value 原导航声明
// 返回: error 地址、依赖、预算或取消错误
func (x *compositionExecution) prepareNavigation(item compositionExecutionPart, base, value string) error {
	b := x.plan.budget
	if err := b.scan(int64(len(base)) + int64(len(value))); err != nil {
		return err
	}
	value = structureURI(value)
	if linkExternal(value) {
		return b.step(1)
	}
	uri, err := url.Parse(value)
	if err != nil {
		return fmt.Errorf("%w: composition navigation URI", ErrInvalid)
	}
	if uri.RawQuery != "" || uri.ForceQuery {
		return fmt.Errorf("%w: query in composition navigation", ErrUnsupported)
	}
	part := base
	if uri.Path != "" {
		part, err = resolvePart(base, uri.EscapedPath())
		if err != nil {
			return err
		}
	}
	valuePart, exists := x.plan.sources[item.source].parts[strings.ToLower(part)]
	if !exists || compositionLayoutMedia(valuePart.media) {
		return b.step(1)
	}
	_, err = x.resourceFor(item, part)
	return err
}

// compositionLayoutMedia 识别具有页面地址作用域的固定布局类型
// 入参: media 部件内容类型
// 返回: bool 是否为序列、文档或页面
func compositionLayoutMedia(media string) bool {
	return strings.EqualFold(media, fixedContentType("fixedpage")) || strings.EqualFold(media, fixedContentType("fixeddocument")) || strings.EqualFold(media, fixedContentType("fixeddocumentsequence"))
}

// projectsStories 判断实例是否属于本次投影的主文档或页面，不改变辅助原文的故事关联
// 入参: item 输出实例
// 返回: bool 是否使用投影后的故事部件
func (x *compositionExecution) projectsStories(item compositionExecutionPart) bool {
	if item.page >= 0 {
		return true
	}
	if item.document < 0 || !x.rawDocs[item.document] {
		return false
	}
	document := x.plan.documents[item.document]
	return item.source == document.source && strings.EqualFold(item.part, x.plan.sources[document.source].documents[document.original].Part)
}

// mainRelationships 合并主层级的实际关联，不将包级元数据或票据静默取自任意来源
// 入参: rootSource 包级元数据来源
// 返回: error 扩展、票据、引用、预算或取消错误
func (x *compositionExecution) mainRelationships(rootSource int) error {
	if err := x.rootRelationships(rootSource); err != nil {
		return err
	}
	var sequence []compositionOrigin
	for source, index := range x.plan.indices {
		if index == nil {
			continue
		}
		value := x.plan.sources[source]
		if x.rawSequence != source+1 {
			index, err := value.indexPart(value.parts[strings.ToLower(value.sequence)], x.plan.budget)
			if err != nil {
				return err
			}
			if err := index.inspect(false, x.plan.budget); err != nil {
				return err
			}
		}
		sequence = append(sequence, compositionOrigin{source, value.sequence})
	}
	if err := x.relationships(x.plan.sequence, sequence, x.sequenceInstance(rootSource), false, ""); err != nil {
		return err
	}
	for index, document := range x.plan.documents {
		origins := x.documents[index]
		for _, origin := range origins {
			if !x.rawDocs[index] && !x.protected[origin.source][strings.ToLower(origin.part)] {
				source := x.plan.sources[origin.source]
				view, err := source.indexPart(source.parts[strings.ToLower(origin.part)], x.plan.budget)
				if err != nil {
					return err
				}
				if err := view.inspect(false, x.plan.budget); err != nil {
					return err
				}
			}
		}
		owner := compositionPartKey{origins[0].source, strings.ToLower(origins[0].part), index, -1}
		if err := x.relationships(document.part, origins, x.instance(owner), true, x.storyParts[strings.ToLower(document.part)]); err != nil {
			return err
		}
	}
	return nil
}

// relationships 按来源作用域迁移有效关联，修改时不保留OPC规定忽略的内容
// 入参: target 输出拥有部件, origins 原关联来源, owner 输出归属, project 是否替换故事关联, story 生成的结构或片段URI
// 返回: error 关系、投影、保护、预算或取消错误
func (x *compositionExecution) relationships(target string, origins []compositionOrigin, owner compositionExecutionPart, project bool, story string) error {
	b := x.plan.budget
	if err := b.step(len(origins)); err != nil {
		return err
	}
	key := strings.ToLower(target)
	instance := compositionRelationshipKey{owner, key, project, story}
	if x.relationshipsDone[instance] {
		return nil
	}
	var relations, previous []Relationship
	var original packagePart
	var firstTicket compositionOrigin
	firstTicketTarget := ""
	hasTicketRelation := false
	var firstThumbOrigin compositionOrigin
	var firstThumbPart packagePart
	hasThumbRelation := false
	hasRaw := false
	storyAssigned := false
	for _, origin := range origins {
		source := x.plan.sources[origin.source]
		context := owner
		context.source = origin.source
		if context.page >= 0 && x.plan.pages[context.page].source != origin.source {
			return fmt.Errorf("%w: composition relationship page context", ErrInvalid)
		}
		relKey := strings.ToLower(createdRelationshipPart(origin.part))
		value, raw := source.parts[relKey]
		hasRaw = hasRaw || raw
		records := source.relationships[strings.ToLower(origin.part)]
		if raw {
			if cached, hit := source.parsedRels[relKey]; hit {
				records = cached
			} else {
				var err error
				records, err = compositionRelationshipRecords(origin.part, value, b)
				if err != nil {
					return err
				}
			}
		}
		if len(origins) == 1 {
			original, previous = value, records
		}
		var tickets []string
		for _, relation := range records {
			if err := b.step(1); err != nil {
				return err
			}
			if origin.part == "/" && relation.Type == formatNamespace(source.format)+"/fixedrepresentation" {
				continue
			}
			ticket := relation.Type == formatNamespace(source.format)+"/printticket"
			if ticket && relation.TargetMode != TargetModeInternal {
				return fmt.Errorf("%w: external composition ticket", ErrInvalid)
			}
			thumb := len(origins) > 1 && relation.Type == thumbnailRelationship
			if thumb && relation.TargetMode != TargetModeInternal {
				return fmt.Errorf("%w: external composition thumbnail", ErrInvalid)
			}
			mapped := relation
			projected := project && (relation.Type == formatNamespace(source.format)+"/documentstructure" || relation.Type == formatNamespace(source.format)+"/storyfragments")
			if projected {
				if story == "" || storyAssigned {
					continue
				}
				mapped.Target, mapped.TargetMode = story, TargetModeInternal
				storyAssigned = true
			} else if relation.TargetMode == TargetModeInternal {
				part, err := resolvePart(origin.part, relation.Target)
				if err != nil {
					return err
				}
				if thumb {
					partKey := strings.ToLower(part)
					cand, present := source.parts[partKey]
					if !present {
						return &PartError{Part: part, Err: fmt.Errorf("%w: missing composition thumbnail", ErrInvalid)}
					}
					if hasThumbRelation {
						equal, err := x.sameRawThumbnail(firstThumbOrigin, firstThumbPart, compositionOrigin{origin.source, part}, cand)
						if err != nil {
							return err
						}
						if !equal {
							return fmt.Errorf("%w: conflicting composition document thumbnails", ErrUnsupported)
						}
						continue
					}
					firstThumbOrigin = compositionOrigin{origin.source, part}
					firstThumbPart = cand
					hasThumbRelation = true
				}
				if ticket && len(origins) > 1 && firstTicketTarget != "" {
					equal, err := x.sameRawTicket(firstTicket, compositionOrigin{origin.source, part})
					if err != nil {
						return err
					}
					if equal {
						tickets = append(tickets, firstTicketTarget)
						continue
					}
				}
				mapped.Target, err = x.resourceFor(context, part)
				if err != nil {
					return err
				}
				if ticket && len(origins) > 1 && firstTicketTarget == "" {
					firstTicket = compositionOrigin{origin.source, part}
					firstTicketTarget = mapped.Target
				}
			}
			if mapped.TargetMode == TargetModeInternal {
				if resolved, err := resolvePart(target, relation.Target); err == nil && strings.EqualFold(resolved, mapped.Target) {
					mapped.Target = relation.Target
				}
			}
			if ticket {
				part, err := resolvePart(target, mapped.Target)
				if err != nil {
					return err
				}
				tickets = append(tickets, part)
				if len(origins) > 1 {
					if hasTicketRelation {
						continue
					}
					hasTicketRelation = true
				}
			}
			relations = append(relations, mapped)
		}
		if target != "/" && len(origins) > 1 {
			if len(tickets) == 0 {
				tickets = append(tickets, "")
			}
			x.tickets[key] = append(x.tickets[key], tickets...)
		}
	}
	if project && story != "" && !storyAssigned {
		kind := "documentstructure"
		if owner.page >= 0 {
			kind = "storyfragments"
		}
		next := createdRelationshipIDs(relations)
		relations = append(relations, Relationship{ID: next(), Type: formatNamespace(x.plan.format) + "/" + kind, Target: story, TargetMode: TargetModeInternal})
	}
	if len(relations) == 0 && !hasRaw {
		return nil
	}
	edited := len(origins) != 1 || origins[0].part != target || !slices.Equal(previous, relations)
	if !edited && original.name != "" {
		var err error
		edited, err = x.retainRelationshipTargets(origins[0], owner, original, project, story)
		if err != nil {
			return err
		}
	}
	if len(origins) > 1 {
		next := createdRelationshipIDs(nil)
		for index := range relations {
			relations[index].ID = next()
		}
	}
	part := createdRelationshipPart(target)
	data, err := compositionRelationshipMarkup(original, relations, edited, b)
	if err != nil {
		return err
	}
	if len(origins) == 1 && x.protected[origins[0].source][strings.ToLower(original.name)] && !x.derivedSequence(owner, target) && (original.name != part || !bytes.Equal(original.data, data)) {
		return fmt.Errorf("%w: composition protected relationship rewrite", ErrRestricted)
	}
	if original.name == "" {
		original = packagePart{name: part, media: opcRelsType}
	}
	if err := x.put(original, part, data); err != nil {
		return err
	}
	parsed := relations
	if !edited && original.data != nil && len(origins) == 1 {
		parsed = slices.Clone(previous)
	}
	var explicit []Relationship
	for _, relation := range parsed {
		if !x.output.modelRelationship(relation) {
			explicit = append(explicit, relation)
		}
	}
	x.output.relations[key], x.output.originalRels[key] = explicit, parsed
	x.output.dirty[strings.ToLower(part)] = true
	x.output.dirtyRels[key] = false
	if x.relationshipsDone == nil {
		x.relationshipsDone = make(map[compositionRelationshipKey]bool)
	}
	x.relationshipsDone[instance] = true
	return nil
}

// sameRawThumbnail 比较合并作用域中多源缩略图部件的媒体类型、字节内容及关系是否存在差异
// 入参: left 首个缩略图来源, leftPart 首个缩略图部件, right 后续缩略图来源, rightPart 后续缩略图部件
// 返回: bool 两份缩略图是否完全等价可去重, error 扫描预算或取消错误
func (x *compositionExecution) sameRawThumbnail(left compositionOrigin, leftPart packagePart, right compositionOrigin, rightPart packagePart) (bool, error) {
	if !strings.EqualFold(leftPart.media, rightPart.media) || len(leftPart.data) != len(rightPart.data) {
		return false, nil
	}
	if left.source == right.source && strings.EqualFold(left.part, right.part) {
		return true, nil
	}
	if compositionHasRelationships(x.plan.sources[left.source], left.part) || compositionHasRelationships(x.plan.sources[right.source], right.part) {
		return false, nil
	}
	if err := x.plan.budget.scan(int64(len(leftPart.data))); err != nil {
		return false, err
	}
	if err := x.plan.budget.scan(int64(len(rightPart.data))); err != nil {
		return false, err
	}
	return bytes.Equal(leftPart.data, rightPart.data), nil
}

// compositionRelationshipElement 限定可保留关系标记的语义，不接受未知属性中的潜在引用
// 入参: node 原始关系节点, budget 共享预算
// 返回: error 扩展、工作量或取消错误
func compositionRelationshipElement(node *xmlElement, budget *compositionBudget) error {
	if err := budget.step(len(node.Attr) + 1); err != nil {
		return err
	}
	return resourceRelationshipNode(node)
}

// sameRawTicket 比较原快照中无附属资源与关系的打印票据字节，一致时跳过冗余调度
// 入参: left 首个已调度票据的原定位, right 待合并票据的原定位
// 返回: bool 原快照是否字节等价且无需独立迁移, error 扫描预算或取消错误
func (x *compositionExecution) sameRawTicket(left, right compositionOrigin) (bool, error) {
	if left.part == "" || right.part == "" {
		return false, nil
	}
	sourceLeft, sourceRight := x.plan.sources[left.source], x.plan.sources[right.source]
	keyLeft, keyRight := strings.ToLower(left.part), strings.ToLower(right.part)
	if x.protected[right.source][keyRight] {
		return false, nil
	}
	if len(sourceLeft.printResources[keyLeft]) != 0 || len(sourceRight.printResources[keyRight]) != 0 {
		return false, nil
	}
	if compositionHasRelationships(sourceLeft, keyLeft) || compositionHasRelationships(sourceRight, keyRight) {
		return false, nil
	}
	partLeft, okLeft := sourceLeft.parts[keyLeft]
	partRight, okRight := sourceRight.parts[keyRight]
	if !okLeft || !okRight || !strings.EqualFold(partLeft.media, partRight.media) || len(partLeft.data) != len(partRight.data) {
		return false, nil
	}
	if left.source == right.source && keyLeft == keyRight {
		return true, nil
	}
	if err := x.plan.budget.scan(int64(len(partLeft.data))); err != nil {
		return false, err
	}
	if err := x.plan.budget.scan(int64(len(partRight.data))); err != nil {
		return false, err
	}
	return bytes.Equal(partLeft.data, partRight.data), nil
}

// validateTickets 在预算内比较迁移后的票据及缺省状态，同级无冲突标准票据合并并清理孤儿旧票据
// 返回: error 层级冲突、缺失、保护、预算或取消错误
func (x *compositionExecution) validateTickets() error {
	var classes map[string]*compositionTicketClass
	var orphans map[string]bool
	for _, scope := range slices.Sorted(maps.Keys(x.tickets)) {
		if err := checkContext(x.plan.budget.context); err != nil {
			return err
		}
		tickets := x.tickets[scope]
		if len(tickets) < 2 {
			continue
		}
		active := make([]string, 0, len(tickets))
		for index, ticket := range tickets {
			if index > 0 {
				if err := x.plan.budget.step(1); err != nil {
					return err
				}
			}
			if ticket != "" {
				active = append(active, ticket)
			}
		}
		if len(active) == 0 {
			continue
		}
		firstKey := strings.ToLower(active[0])
		first, exists := x.output.parts[firstKey]
		if !exists {
			return fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
		}
		if len(active) == 1 {
			continue
		}
		needsMerge := false
		hasScopeRels := len(x.output.originalRels[scope]) != 0 || len(x.output.relations[scope]) != 0
		var sameCopies []string
		for _, ticket := range active[1:] {
			key := strings.ToLower(ticket)
			value, present := x.output.parts[key]
			if !present || !strings.EqualFold(first.media, value.media) {
				return fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
			}
			if firstKey == key {
				continue
			}
			if len(first.data) != len(value.data) {
				needsMerge = true
				continue
			}
			a, b := classes[firstKey], classes[key]
			if a != nil {
				a = a.root()
			}
			if b != nil {
				b = b.root()
			}
			if a != nil && a == b {
				if hasScopeRels {
					sameCopies = append(sameCopies, key)
				}
				continue
			}
			if err := x.plan.budget.scan(int64(len(first.data))); err != nil {
				return err
			}
			if err := x.plan.budget.scan(int64(len(value.data))); err != nil {
				return err
			}
			if !bytes.Equal(first.data, value.data) {
				needsMerge = true
				continue
			}
			relsEqual, err := x.equalTicketRelationships(firstKey, key)
			if err != nil {
				return err
			}
			if !relsEqual {
				return fmt.Errorf("%w: conflicting composition print-ticket relationships", ErrUnsupported)
			}
			if hasScopeRels {
				sameCopies = append(sameCopies, key)
			}
			if classes == nil {
				classes = make(map[string]*compositionTicketClass)
			}
			switch {
			case a == nil && b == nil:
				a = &compositionTicketClass{}
				classes[firstKey], classes[key] = a, a
			case a == nil:
				classes[firstKey] = b
			case b == nil:
				classes[key] = a
			default:
				a.join(b)
			}
		}
		if needsMerge {
			replaced, err := x.mergeScopeTickets(scope, active, first.media)
			if err != nil {
				return err
			}
			if len(replaced) != 0 {
				if orphans == nil {
					orphans = make(map[string]bool, len(replaced))
				}
				for _, key := range replaced {
					orphans[key] = true
				}
			}
		} else if len(sameCopies) != 0 {
			if orphans == nil {
				orphans = make(map[string]bool, len(sameCopies))
			}
			for _, key := range sameCopies {
				orphans[key] = true
			}
		}
	}
	if len(orphans) != 0 {
		return x.cleanupOrphanTickets(orphans)
	}
	return checkContext(x.plan.budget.context)
}

// ticketRelationships 返回输出包中指定票据部件的规范关系列表及是否存在关系部件
// 入参: key 小写票据部件键
// 返回: []Relationship 有效关系列表, bool 是否存在非空关系或关系部件
func (x *compositionExecution) ticketRelationships(key string) ([]Relationship, bool) {
	if rels := x.output.originalRels[key]; len(rels) != 0 {
		return rels, true
	}
	if rels := x.output.relations[key]; len(rels) != 0 {
		return rels, true
	}
	if part, exists := x.output.parts[key]; exists {
		if _, relExists := x.output.parts[strings.ToLower(createdRelationshipPart(part.name))]; relExists {
			return nil, true
		}
	}
	return nil, false
}

// equalTicketRelationships 校验两份同字节打印票据的伴生关系是否语义等价，避免静默丢弃关系差异
// 入参: leftKey 保留票据小写键, rightKey 冗余票据小写键
// 返回: bool 两份票据关系是否完全等价, error 解析、预算或取消错误
func (x *compositionExecution) equalTicketRelationships(leftKey, rightKey string) (bool, error) {
	leftRels, leftHas := x.ticketRelationships(leftKey)
	rightRels, rightHas := x.ticketRelationships(rightKey)
	if !leftHas && !rightHas {
		return true, nil
	}
	if len(leftRels) != len(rightRels) {
		return false, nil
	}
	if len(leftRels) == 0 {
		return leftHas == rightHas, nil
	}
	leftPart, okLeft := x.output.parts[leftKey]
	rightPart, okRight := x.output.parts[rightKey]
	if !okLeft || !okRight {
		return false, nil
	}
	type normRel struct {
		typ      string
		mode     TargetMode
		target   string
		resolved string
	}
	normalize := func(owner string, rels []Relationship) ([]normRel, error) {
		out := make([]normRel, len(rels))
		for i, rel := range rels {
			mode := rel.TargetMode
			if mode == "" {
				mode = TargetModeInternal
			}
			item := normRel{typ: rel.Type, mode: mode, target: rel.Target}
			if mode == TargetModeInternal {
				resolved, err := resolvePart(owner, rel.Target)
				if err != nil {
					return nil, err
				}
				item.resolved = strings.ToLower(resolved)
			}
			out[i] = item
		}
		slices.SortFunc(out, func(a, b normRel) int {
			if v := strings.Compare(a.typ, b.typ); v != 0 {
				return v
			}
			if v := strings.Compare(string(a.mode), string(b.mode)); v != 0 {
				return v
			}
			if v := strings.Compare(a.resolved, b.resolved); v != 0 {
				return v
			}
			return strings.Compare(a.target, b.target)
		})
		return out, nil
	}
	leftNorm, err := normalize(leftPart.name, leftRels)
	if err != nil {
		return false, err
	}
	rightNorm, err := normalize(rightPart.name, rightRels)
	if err != nil {
		return false, err
	}
	for i := range leftNorm {
		l, r := leftNorm[i], rightNorm[i]
		if l.typ != r.typ || l.mode != r.mode {
			return false, nil
		}
		if l.mode != TargetModeInternal {
			if l.target != r.target {
				return false, nil
			}
			continue
		}
		if l.resolved == r.resolved {
			continue
		}
		lp, lok := x.output.parts[l.resolved]
		rp, rok := x.output.parts[r.resolved]
		if !lok || !rok || !strings.EqualFold(lp.media, rp.media) || len(lp.data) != len(rp.data) {
			return false, nil
		}
		if _, lh := x.ticketRelationships(l.resolved); lh {
			return false, nil
		}
		if _, rh := x.ticketRelationships(r.resolved); rh {
			return false, nil
		}
		if err := x.plan.budget.scan(int64(len(lp.data))); err != nil {
			return false, err
		}
		if err := x.plan.budget.scan(int64(len(rp.data))); err != nil {
			return false, err
		}
		if !bytes.Equal(lp.data, rp.data) {
			return false, nil
		}
	}
	return true, nil
}

// mergeScopeTickets 对同级无冲突标准打印票据执行语义合并，同级设置值冲突显式报错，返回被替换的旧票据键
// 入参: scope 小写作用域部件键, tickets 同级全部已迁移票据部件名, media 共享票据媒体类型
// 返回: []string 被替换的旧票据小写键列表, error 格式不支持、受限、冲突、预算或取消错误
func (x *compositionExecution) mergeScopeTickets(scope string, tickets []string, media string) ([]string, error) {
	if err := checkContext(x.plan.budget.context); err != nil {
		return nil, err
	}
	if known, capabilities := printResourceMedia(media); !known || capabilities {
		return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
	}
	sourceName := ""
	level := PrintScopeUnknown
	if x.output.sequence != "" && strings.EqualFold(x.output.sequence, scope) {
		sourceName, level = x.output.sequence, PrintScopeJob
	} else {
		for _, doc := range x.output.documents {
			if strings.EqualFold(doc.Part, scope) {
				sourceName, level = doc.Part, PrintScopeDocument
				break
			}
			for _, page := range doc.Pages {
				if strings.EqualFold(page.Part, scope) {
					sourceName, level = page.Part, PrintScopePage
					break
				}
			}
			if sourceName != "" {
				break
			}
		}
	}
	options := &PrintSettingsOptions{Limits: x.plan.budget.limits, Scope: level}
	var merged *PrintSettings
	seen := make(map[string]bool, len(tickets))
	var replaced []string
	for _, ticket := range tickets {
		if err := x.plan.budget.step(1); err != nil {
			return nil, err
		}
		key := strings.ToLower(ticket)
		part, present := x.output.parts[key]
		if !present || !strings.EqualFold(part.media, media) {
			return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
		}
		if seen[key] {
			continue
		}
		seen[key] = true
		if rels, _ := x.ticketRelationships(key); len(rels) != 0 {
			return nil, fmt.Errorf("%w: cannot merge print tickets with relationships", ErrUnsupported)
		}
		replaced = append(replaced, key)
		parsed, err := ParsePrintSettings(x.plan.budget.context, part.data, options)
		if err != nil {
			if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
				return nil, err
			}
			return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
		}
		if merged == nil {
			merged = parsed
			continue
		}
		conflict, err := printSettingsConflict(merged, parsed, x.plan.budget)
		if err != nil {
			return nil, err
		}
		if conflict {
			return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
		}
		merged, err = MergePrintSettings(x.plan.budget.context, merged, parsed, options)
		if err != nil {
			if errors.Is(err, ErrLimit) || errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
				return nil, err
			}
			return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
		}
	}
	if sourceName == "" {
		return nil, fmt.Errorf("%w: conflicting composition print-ticket scopes", ErrUnsupported)
	}
	relPartKey := strings.ToLower(createdRelationshipPart(sourceName))
	for _, parts := range x.protected {
		if parts[relPartKey] {
			return nil, fmt.Errorf("%w: protected print ticket relationship", ErrRestricted)
		}
	}
	var buffer bytes.Buffer
	if _, err := EncodePrintSettings(x.plan.budget.context, &buffer, merged, options); err != nil {
		return nil, err
	}
	first := x.output.parts[strings.ToLower(tickets[0])]
	dir := first.name[:strings.LastIndexByte(first.name, '/')+1]
	if dir == "" {
		dir = "/"
	}
	pattern := dir + "PrintTicket_%d.xml"
	partName, err := x.output.newName(pattern, nil)
	if err != nil {
		return nil, err
	}
	if err := x.output.store(partName, media, buffer.Bytes()); err != nil {
		return nil, err
	}
	x.output.commitName(pattern, partName)
	kind := formatNamespace(x.plan.format) + "/printticket"
	relations := slices.Clone(x.output.originalRels[scope])
	if len(relations) == 0 {
		relations = slices.Clone(x.output.relations[scope])
	}
	updated := false
	for index := range relations {
		if relations[index].Type == kind {
			relations[index].Target, relations[index].TargetMode = partName, TargetModeInternal
			updated = true
			break
		}
	}
	if !updated {
		nextID := createdRelationshipIDs(relations)
		relations = append(relations, Relationship{ID: nextID(), Type: kind, Target: partName, TargetMode: TargetModeInternal})
	}
	relData, err := createdRelationshipMarkup(relations, x.plan.budget.limits, x.plan.budget.context)
	if err != nil {
		return nil, err
	}
	if err := x.output.setRelationshipMarkup(sourceName, relData, x.plan.budget.context); err != nil {
		return nil, err
	}
	x.output.originalRels[scope] = relations
	return replaced, nil
}

// printSettingsConflict 检查两份同级已解析打印设置是否在共享关键字上存在相互矛盾的值
// 入参: left, right 同级打印设置, budget 共享预算
// 返回: bool 是否存在同级冲突, error 预算或取消错误
func printSettingsConflict(left, right *PrintSettings, budget *compositionBudget) (bool, error) {
	if err := checkContext(budget.context); err != nil {
		return false, err
	}
	if left.Version != right.Version {
		return true, nil
	}
	return printSettingListsConflict(left.Elements, right.Elements, budget)
}

// printSettingListsConflict 对比同级设置元素切片，仅允许正交互补或完全语义等价的重叠项，同时检出同前缀族作用域关键字冲突
// 入参: left, right 同级元素切片, budget 共享预算
// 返回: bool 是否存在冲突, error 预算或取消错误
func printSettingListsConflict(left, right []PrintSetting, budget *compositionBudget) (bool, error) {
	type key struct {
		kind PrintSettingKind
		name xml.Name
	}
	canonicalName := func(name xml.Name) xml.Name {
		if printFrameworkSpace(name.Space) {
			name.Space = printFrameworkNS
		}
		return name
	}
	byKey := make(map[key][]PrintSetting, len(left))
	leftFamilies := make(map[printPrefixKey]xml.Name, len(left))
	for _, item := range left {
		if err := budget.step(1); err != nil {
			return false, err
		}
		k := key{item.Kind, canonicalName(item.Name)}
		byKey[k] = append(byKey[k], item)
		if familyKey, _, ok := printPrefixFamily(item); ok {
			leftFamilies[familyKey] = canonicalName(item.Name)
		}
	}
	rightByKey := make(map[key][]PrintSetting, len(right))
	for _, item := range right {
		if err := budget.step(1); err != nil {
			return false, err
		}
		if familyKey, _, ok := printPrefixFamily(item); ok {
			if prevName, exists := leftFamilies[familyKey]; exists && prevName != canonicalName(item.Name) {
				return true, nil
			}
		}
		k := key{item.Kind, canonicalName(item.Name)}
		rightByKey[k] = append(rightByKey[k], item)
	}
	for k, rightItems := range rightByKey {
		leftItems, overlap := byKey[k]
		if !overlap {
			continue
		}
		if len(leftItems) != len(rightItems) {
			return true, nil
		}
		for i := range leftItems {
			equal, err := printSettingEqual(leftItems[i], rightItems[i], budget)
			if err != nil {
				return false, err
			}
			if !equal {
				return true, nil
			}
		}
	}
	return false, nil
}

// printSettingEqual 递归判断两个PrintSetting节点是否语义等价，QName按展开名、数值按精确数值比较且不依赖子节点顺序
// 入参: a, b 待比较节点, budget 共享预算
// 返回: bool 是否语义等价, error 预算或取消错误
func printSettingEqual(a, b PrintSetting, budget *compositionBudget) (bool, error) {
	if err := budget.step(1); err != nil {
		return false, err
	}
	nameA, nameB := a.Name, b.Name
	if printFrameworkSpace(nameA.Space) {
		nameA.Space = printFrameworkNS
	}
	if printFrameworkSpace(nameB.Space) {
		nameB.Space = printFrameworkNS
	}
	if a.Kind != b.Kind || nameA != nameB || a.Constraint != b.Constraint || a.HasDefault != b.HasDefault || a.Default != b.Default {
		return false, nil
	}
	if (a.Value == nil) != (b.Value == nil) {
		return false, nil
	}
	if a.Value != nil {
		typeA, typeB := a.Value.Type, b.Value.Type
		if typeA == (xml.Name{}) {
			typeA = xml.Name{Space: printValueNS, Local: "string"}
		}
		if typeB == (xml.Name{}) {
			typeB = xml.Name{Space: printValueNS, Local: "string"}
		}
		if typeA != typeB {
			return false, nil
		}
		if typeA.Space == printValueNS {
			switch typeA.Local {
			case "QName":
				if a.Value.QName != (xml.Name{}) || b.Value.QName != (xml.Name{}) {
					if a.Value.QName != b.Value.QName {
						return false, nil
					}
				} else if strings.Trim(a.Value.Text, " \t\r\n") != strings.Trim(b.Value.Text, " \t\r\n") {
					return false, nil
				}
			case "integer", "decimal":
				left := strings.Trim(a.Value.Text, " \t\r\n")
				right := strings.Trim(b.Value.Text, " \t\r\n")
				if left == "" || right == "" {
					if left != right {
						return false, nil
					}
				} else {
					if typeA.Local == "integer" && (!printInteger(left) || !printInteger(right)) {
						return false, nil
					}
					cfg := printSettingsConfig{PrintSettingsOptions: DefaultPrintSettingsOptions(), context: budget.context}
					numA, err := printParameterNumber(left, cfg)
					if err != nil {
						if errors.Is(err, ErrInvalid) {
							return false, nil
						}
						return false, err
					}
					numB, err := printParameterNumber(right, cfg)
					if err != nil {
						if errors.Is(err, ErrInvalid) {
							return false, nil
						}
						return false, err
					}
					if numA.Cmp(numB) != 0 {
						return false, nil
					}
				}
			default:
				if a.Value.Text != b.Value.Text || a.Value.QName != b.Value.QName {
					return false, nil
				}
			}
		} else if a.Value.Text != b.Value.Text || a.Value.QName != b.Value.QName {
			return false, nil
		}
	}
	if len(a.Children) != len(b.Children) {
		return false, nil
	}
	used := make([]bool, len(b.Children))
	for _, childA := range a.Children {
		matched := false
		for j, childB := range b.Children {
			if used[j] {
				continue
			}
			equal, err := printSettingEqual(childA, childB, budget)
			if err != nil {
				return false, err
			}
			if equal {
				used[j], matched = true, true
				break
			}
		}
		if !matched {
			return false, nil
		}
	}
	return true, nil
}

// cleanupOrphanTickets 清理票据合并替换后不再被输出包任意关系引用且不受保护的孤儿旧票据及其关系部件
// 入参: orphans 候选孤儿票据小写键集合
// 返回: error 取消或预算错误
func (x *compositionExecution) cleanupOrphanTickets(orphans map[string]bool) error {
	protected := make(map[string]bool)
	for _, parts := range x.protected {
		for key := range parts {
			protected[key] = true
		}
	}
	for len(orphans) != 0 {
		referenced := make(map[string]bool)
		collect := func(sourceKey string, rels []Relationship) error {
			if orphans[sourceKey] {
				return nil
			}
			sourceName := x.output.sourcePartName(sourceKey)
			if sourceName == "" {
				sourceName = "/"
			}
			for _, rel := range rels {
				if err := checkContext(x.plan.budget.context); err != nil {
					return err
				}
				if rel.TargetMode != "" && rel.TargetMode != TargetModeInternal {
					continue
				}
				target, err := resolvePart(sourceName, rel.Target)
				if err == nil {
					referenced[strings.ToLower(target)] = true
				}
			}
			return nil
		}
		for _, sourceKey := range slices.Sorted(maps.Keys(x.output.originalRels)) {
			if err := collect(sourceKey, x.output.originalRels[sourceKey]); err != nil {
				return err
			}
		}
		for _, sourceKey := range slices.Sorted(maps.Keys(x.output.relations)) {
			if err := collect(sourceKey, x.output.relations[sourceKey]); err != nil {
				return err
			}
		}
		var nextOrphans map[string]bool
		for _, key := range slices.Sorted(maps.Keys(orphans)) {
			if err := checkContext(x.plan.budget.context); err != nil {
				return err
			}
			if referenced[key] || protected[key] {
				continue
			}
			part, exists := x.output.parts[key]
			if !exists {
				continue
			}
			if rels, _ := x.ticketRelationships(key); len(rels) != 0 {
				for _, rel := range rels {
					if rel.TargetMode != "" && rel.TargetMode != TargetModeInternal {
						continue
					}
					if target, err := resolvePart(part.name, rel.Target); err == nil {
						targetKey := strings.ToLower(target)
						if !orphans[targetKey] && !protected[targetKey] {
							if nextOrphans == nil {
								nextOrphans = make(map[string]bool)
							}
							nextOrphans[targetKey] = true
						}
					}
				}
			}
			relKey := strings.ToLower(createdRelationshipPart(part.name))
			x.output.removePart(part.name)
			delete(x.output.originalRels, key)
			delete(x.output.original, key)
			delete(x.output.original, relKey)
		}
		orphans = nextOrphans
	}
	return checkContext(x.plan.budget.context)
}

// structureRelationships 将各原结构的关联迁移到合并结构，共享原结构只登记一次
// 入参: document 输出文档序号, target 合并后的结构部件URI
// 返回: error 原关联、资源迁移、标记合并、预算或取消错误
func (x *compositionExecution) structureRelationships(document int, target string) error {
	var origins []compositionOrigin
	seen := make(map[compositionOrigin]bool)
	for _, owner := range x.documents[document] {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		source := x.plan.sources[owner.source]
		for _, relation := range source.relationships[strings.ToLower(owner.part)] {
			if err := x.plan.budget.step(1); err != nil {
				return err
			}
			if relation.Type != formatNamespace(source.format)+"/documentstructure" {
				continue
			}
			part, err := resolvePart(owner.part, relation.Target)
			if err != nil {
				return err
			}
			if _, exists := source.parts[strings.ToLower(createdRelationshipPart(part))]; !exists {
				continue
			}
			origin := compositionOrigin{owner.source, strings.ToLower(part)}
			if !seen[origin] {
				seen[origin] = true
				origins = append(origins, compositionOrigin{owner.source, part})
			}
		}
	}
	if len(origins) == 0 {
		return nil
	}
	owner := compositionPartKey{origins[0].source, strings.ToLower(origins[0].part), document, -1}
	return x.relationships(target, origins, x.instance(owner), false, "")
}

// compositionRelationshipRecords 按原关系部件自身的兼容性作用域读取有效关联，单遍解码不消费未选分支
// 入参: source 关系源部件, value 原始关系XML, budget 共享预算
// 返回: []Relationship 有效关系, error XML、关系、预算或取消错误
func compositionRelationshipRecords(source string, value packagePart, budget *compositionBudget) ([]Relationship, error) {
	if int64(len(value.data)) > min(budget.limits.MaxMetadataBytes, budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: composition relationship capacity", ErrLimit)
	}
	if err := budget.scan(int64(len(value.data))); err != nil {
		return nil, err
	}
	root, err := decodeXMLVisit(value.data, budget.limits, func(_ xml.Token, node *xmlElement) error {
		if node == nil {
			return budget.step(1)
		}
		return budget.step(len(node.Attr) + 1)
	})
	if err != nil {
		return nil, err
	}
	return parseCompositionRelationshipRoot(source, root, budget.context)
}

// retainRelationshipTargets 为原样透传的关系保留各分支闭包，目标身份改变时改用有效视图输出
// 入参: origin 原关系来源, owner 输出归属, value 原始关系XML, project 是否投影故事关联, story 输出故事部件
// 返回: bool 是否存在需要改写的目标, error 引用、资源、预算或取消错误
func (x *compositionExecution) retainRelationshipTargets(origin compositionOrigin, owner compositionExecutionPart, value packagePart, project bool, story string) (bool, error) {
	b := x.plan.budget
	for _, schedule := range []bool{false, true} {
		changed, err := x.relationshipTargets(origin, owner, value, project, story, schedule)
		if err != nil || changed {
			return changed, err
		}
	}
	return false, b.step(1)
}

// relationshipTargets 检查各分支目标身份，确认原文可保留后才分配资源及验证保留标记
// 入参: origin 原关系来源, owner 输出归属, value 原始XML, project 是否投影故事, story 输出故事URI, schedule 是否展开资源闭包
// 返回: bool 是否需要改写, error 标记、引用、资源、预算或取消错误
func (x *compositionExecution) relationshipTargets(origin compositionOrigin, owner compositionExecutionPart, value packagePart, project bool, story string, schedule bool) (bool, error) {
	b := x.plan.budget
	if err := b.scan(int64(len(value.data))); err != nil {
		return false, err
	}
	changed := false
	_, err := decodeXMLVisit(value.data, b.limits, func(token xml.Token, node *xmlElement) error {
		if err := b.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if schedule {
			if err := compositionRelationshipElement(node, b); err != nil {
				return err
			}
		}
		if changed || node.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) {
			return nil
		}
		if mode, _ := node.attribute("TargetMode"); TargetMode(mode) == TargetModeExternal {
			return nil
		}
		kind, _ := node.attribute("Type")
		uri, _ := node.attribute("Target")
		part, err := resolvePart(origin.part, uri)
		if err != nil {
			return err
		}
		if origin.part == "/" && kind == formatNamespace(x.plan.format)+"/fixedrepresentation" {
			if !strings.EqualFold(part, x.plan.sources[origin.source].sequence) {
				return fmt.Errorf("%w: unchanged composition has an alternative start part", ErrUnsupported)
			}
			return nil
		}
		if project && (kind == formatNamespace(x.plan.format)+"/documentstructure" || kind == formatNamespace(x.plan.format)+"/storyfragments") {
			changed = changed || story == "" || !strings.EqualFold(story, part)
			return nil
		}
		name, err := x.resourceTarget(owner, part, schedule)
		if err != nil {
			return err
		}
		changed = changed || !strings.EqualFold(name, part)
		return nil
	})
	return changed, err
}

// compositionRelationshipMarkup 编辑关系时仅输出有效记录，未修改时保留原文，编码沿用原部件
// 入参: value 原始关系XML，无原件时为空, records 输出关系, edited 是否修改关系或解析基址, budget 共享预算
// 返回: []byte 关系XML，未修改时借用原字节, error 容量、结构或取消错误
func compositionRelationshipMarkup(value packagePart, records []Relationship, edited bool, budget *compositionBudget) ([]byte, error) {
	if err := budget.step(len(records) + 1); err != nil {
		return nil, err
	}
	if !edited && value.data != nil {
		return value.data, nil
	}
	data, err := createdRelationshipMarkup(records, budget.limits, budget.context)
	if err != nil {
		return nil, err
	}
	if err := budget.scan(int64(len(data))); err != nil {
		return nil, err
	}
	if value.data == nil {
		return data, nil
	}
	maximum := min(budget.limits.MaxMetadataBytes, budget.limits.MaxPartBytes, budget.limits.MaxPackageBytes)
	return restoreXMLEncoding(value.data, data, maximum, budget.context)
}

// projectStories 登记投影后的目录、片段及导航依赖，地址改写留待硬依赖规划完成
// 返回: error 模型、关联、保护、名称、预算或取消错误
func (x *compositionExecution) projectStories() error {
	for index, value := range x.stories.documents {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		if value == nil {
			continue
		}
		document := x.plan.documents[index]
		instance := x.plan.pages[document.pages[0]]
		key := compositionPartKey{instance.source, strings.ToLower(value.Part), index, -1}
		if value.Part == "" {
			target, err := x.plan.allocate(document.part[:strings.LastIndexByte(document.part, '/')+1]+"Structure.struct", false, false)
			if err != nil {
				return err
			}
			key.part = strings.ToLower(target)
			x.originals[key] = packagePart{name: target, media: fixedContentType("documentstructure")}
			x.plan.resources[key] = target
		}
		if _, generated := x.originals[key]; !generated {
			found := false
			for _, origin := range x.documents[index] {
				source := x.plan.sources[origin.source]
				for _, relation := range source.relationships[strings.ToLower(origin.part)] {
					if err := x.plan.budget.step(1); err != nil {
						return err
					}
					if relation.Type != formatNamespace(source.format)+"/documentstructure" {
						continue
					}
					part, err := resolvePart(origin.part, relation.Target)
					if err != nil {
						return err
					}
					if strings.EqualFold(part, value.Part) {
						key.source, found = origin.source, true
					}
				}
			}
			if !found {
				return fmt.Errorf("%w: projected composition structure association", ErrInvalid)
			}
		}
		if _, exists := x.plan.sources[key.source].parts[key.part]; !exists && x.originals[key].name == "" {
			return fmt.Errorf("%w: projected composition structure origin", ErrInvalid)
		}
		target := x.plan.resources[key]
		if target == "" {
			var err error
			target, err = x.plan.resource(key.source, value.Part, index, -1)
			if err != nil {
				return err
			}
		}
		if value.Outline != nil {
			if len(value.Outline.Entries) != len(x.stories.outlines[index]) {
				return fmt.Errorf("%w: composition outline provenance", ErrInvalid)
			}
			for i, origin := range x.stories.outlines[index] {
				context := compositionPartKey{origin.source, strings.ToLower(origin.part), index, -1}
				entry := &value.Outline.Entries[i]
				if err := x.prepareNavigation(x.instance(context), origin.part, entry.Target); err != nil {
					return err
				}
			}
		}
		if x.stories.keepDocuments[index] {
			original := x.plan.sources[key.source].parts[key.part]
			if err := x.plan.budget.scan(int64(len(original.data))); err != nil {
				return err
			}
			if _, err := decodeXMLVisit(original.data, x.plan.budget.limits, func(token xml.Token, node *xmlElement) error {
				if err := x.plan.budget.step(1); err != nil {
					return err
				}
				if _, start := token.(xml.StartElement); start && node.Name == (xml.Name{Space: structureNamespace(x.plan.format), Local: "OutlineEntry"}) {
					if uri, exists := node.attribute("OutlineTarget"); exists {
						return x.prepareNavigation(x.instance(key), original.name, uri)
					}
				}
				return nil
			}); err != nil {
				return err
			}
		}
		x.storyQueue = append(x.storyQueue, compositionStoryPending{key, target, index})
		x.generated[key] = nil
		if x.protected[key.source][key.part] {
			x.generated[compositionPartKey{key.source, key.part, -1, -1}] = nil
		}
		x.storyParts[strings.ToLower(document.part)] = target
		if err := x.schedule(key, target); err != nil {
			return err
		}
		if value.Part == "" {
			if err := x.structureRelationships(index, target); err != nil {
				return err
			}
		}
	}
	for index, value := range x.stories.fragments {
		if err := x.plan.budget.step(1); err != nil {
			return err
		}
		if value == nil {
			continue
		}
		instance := x.plan.pages[index]
		key := compositionPartKey{instance.source, strings.ToLower(value.Part), instance.document, index}
		target, err := x.plan.resource(key.source, value.Part, key.document, key.page)
		if err != nil {
			return err
		}
		var data []byte
		if x.stories.keepFragments[index] {
			data = x.plan.sources[key.source].parts[key.part].data
		} else {
			data, err = createdStoryFragments(value, x.plan.format, x.plan.budget.limits, x.plan.budget.context)
			if err != nil {
				return err
			}
		}
		x.generated[key] = data
		if x.protected[key.source][key.part] {
			x.generated[compositionPartKey{key.source, key.part, -1, -1}] = data
		}
		x.storyParts[strings.ToLower(instance.reference.Part)] = target
		if err := x.schedule(key, target); err != nil {
			return err
		}
	}
	return nil
}

// finishStories 在依赖闭包确定后改写目录导航，支持按开关剪除指向未选中页面的目录条目并省略空DocumentOutline
// 返回: error 目录、导航、保护、预算或取消错误
func (x *compositionExecution) finishStories() error {
	for _, pending := range x.storyQueue {
		key, target, index := pending.key, pending.target, pending.index
		value := x.stories.documents[index]
		pruned := false
		if value.Outline != nil {
			kept := make([]OutlineEntry, 0, len(value.Outline.Entries))
			for i, origin := range x.stories.outlines[index] {
				context := compositionPartKey{origin.source, strings.ToLower(origin.part), index, -1}
				entry := value.Outline.Entries[i]
				uri, changed, dropped, err := x.navigateOptional(x.instance(context), origin.part, target, entry.Target, x.plan.pruneUnselectedOutlines)
				if err != nil {
					return err
				}
				if dropped {
					if x.protected[origin.source][strings.ToLower(origin.part)] {
						return fmt.Errorf("%w: protected composition outline prune", ErrRestricted)
					}
					pruned = true
					continue
				}
				if changed && x.protected[origin.source][strings.ToLower(origin.part)] {
					return fmt.Errorf("%w: protected composition outline rewrite", ErrRestricted)
				}
				entry.Target = uri
				kept = append(kept, entry)
			}
			if pruned && len(kept) == 0 {
				value.Outline = nil
			} else {
				value.Outline.Entries = kept
			}
		}
		var data []byte
		var err error
		if x.stories.keepDocuments[index] && !pruned {
			original := x.plan.sources[key.source].parts[key.part]
			rewriteTracker := newResourceMarkupScopeTracker(x.plan.format, x.plan.format == FormatOpenXPS, x.plan.budget.context)
			data, err = rewriteExtractMarkup(original.data, x.plan.budget.limits, x.plan.budget.context, func(token xml.Token, node *xmlElement) (bool, error) {
				skip, _, err := rewriteTracker.visit(token, node)
				return skip, err
			}, func(node *xmlElement, attr xml.Attr) (string, bool, error) {
				if node.Name == (xml.Name{Space: structureNamespace(x.plan.format), Local: "OutlineEntry"}) && attr.Name == (xml.Name{Local: "OutlineTarget"}) {
					return x.navigate(x.instance(key), original.name, target, attr.Value)
				}
				return attr.Value, false, x.plan.budget.step(1)
			})
			if err != nil {
				return err
			}
		} else {
			data, err = createdDocumentStructure(value, x.plan.format, x.plan.budget.limits, x.plan.budget.context)
			if err != nil {
				return err
			}
		}
		x.generated[key] = data
		if x.protected[key.source][key.part] {
			x.generated[compositionPartKey{key.source, key.part, -1, -1}] = data
		}
	}
	return nil
}
