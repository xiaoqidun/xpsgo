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
	"cmp"
	"encoding/xml"
	"fmt"
	"maps"
	"math"
	"slices"
	"strconv"
	"strings"
)

// compositionStories 保存独立的故事投影，保留标记要求写出方沿用原部件而非重编码模型
type compositionStories struct {
	documents     []*DocumentStructure
	fragments     []*StoryFragments
	outlines      [][]compositionStoryOrigin
	keepDocuments []bool
	keepFragments []bool
}

// compositionStoryOrigin 保存目录条目的原始URI基准
type compositionStoryOrigin struct {
	source int
	part   string
}

// compositionStoryDocument 区分不同源包及同一包内的固定文档
type compositionStoryDocument struct {
	source   int
	document int
}

// compositionStoryInput 缓存一个原文档的标准模型及其选中页面，不推断未捕获页面的内容
type compositionStoryInput struct {
	structure         *DocumentStructure
	fragments         map[int]*StoryFragments
	locations         map[contentFragmentKey][]int
	extended          bool
	extendedFragments map[int]bool
}

// compositionStoryProjector 按输出文档协调故事身份，并共享组合预算
type compositionStoryProjector struct {
	plan    *compositionPlan
	names   *compositionNames
	result  *compositionStories
	inputs  map[compositionStoryDocument]*compositionStoryInput
	visuals map[compositionPageKey]map[string]bool
}

// compositionStoryNames 在一个故事作用域预留原名并分配副本名称
type compositionStoryNames struct {
	reserved map[string]bool
	used     map[string]bool
	next     int
}

// compositionStoryOccurrence 记录投影引用的原声明位置及输出片段位置
type compositionStoryOccurrence struct {
	ordinal  int
	page     int
	fragment int
}

// compositionStoryBoundary 保存片段两端的断点及必须保持续接的边界
type compositionStoryBoundary struct {
	breaks [2]bool
	joined [2]bool
}

// compositionSignatureKey 区分不同来源中的签署请求部件，同一原件的多个文档关联共用身份
type compositionSignatureKey struct {
	source int
	part   string
}

// compositionSignaturePart 保存原始各已知分支的请求标识及受保护状态
type compositionSignaturePart struct {
	key       compositionSignatureKey
	names     []string
	protected bool
}

// compositionSignatures 协调新包中的全局SpotID，不继承或伪造原包的真实数字签名
type compositionSignatures struct {
	parts  map[compositionSignatureKey]map[string]string
	budget *compositionBudget
}

// compositionSignatureMarkupOptions 提供签署标识与可选页面位置的改写回调，空回调保留原值
type compositionSignatureMarkupOptions struct {
	format Format
	part   string
	budget *compositionBudget
	id     func(string) (string, error)
	spot   func(string) (string, bool, error)
}

// newCompositionStories 投影作者声明的故事与片段，不分配部件URI或修改快照和规划
// 入参: plan 页面组合规划, names 与规划对应的页面名称映射
// 返回: *compositionStories 独立投影，失败为nil, error 关联、许可、支持范围、预算或取消错误
func newCompositionStories(plan *compositionPlan, names *compositionNames) (*compositionStories, error) {
	if plan == nil || plan.budget == nil || names == nil || names.budget != plan.budget || len(names.pages) != len(plan.pages) {
		return nil, fmt.Errorf("%w: composition story input", ErrInvalid)
	}
	if err := plan.budget.step(len(plan.documents) + len(plan.pages)); err != nil {
		return nil, err
	}
	g := &compositionStoryProjector{plan: plan, names: names, inputs: make(map[compositionStoryDocument]*compositionStoryInput), visuals: make(map[compositionPageKey]map[string]bool), result: &compositionStories{documents: make([]*DocumentStructure, len(plan.documents)), fragments: make([]*StoryFragments, len(plan.pages)), outlines: make([][]compositionStoryOrigin, len(plan.documents)), keepDocuments: make([]bool, len(plan.documents)), keepFragments: make([]bool, len(plan.pages))}}
	for document := range plan.documents {
		if err := g.document(document); err != nil {
			return nil, err
		}
	}
	if err := plan.budget.step(0); err != nil {
		return nil, err
	}
	return g.result, nil
}

// root 从实际关系和原始字节读取结构，兼容性过滤不会被误作原文完整保留
// 入参: source 源包序号, owner 所属部件, kind 关系类型, local 预期根元素名
// 返回: string 原部件URI, *xmlElement 标准消费树, bool 是否含模型不能保留的标记, error 关联或解析错误
func (g *compositionStoryProjector) root(source int, owner, kind, local string) (string, *xmlElement, bool, error) {
	s := g.plan.sources[source]
	part := ""
	for _, relation := range s.relationships[strings.ToLower(owner)] {
		if err := g.plan.budget.step(1); err != nil {
			return "", nil, false, err
		}
		if err := g.plan.budget.scan(int64(len(relation.Type)) + int64(len(relation.Target)) + int64(len(relation.TargetMode))); err != nil {
			return "", nil, false, err
		}
		if relation.Type != formatNamespace(s.format)+"/"+kind {
			continue
		}
		if relation.TargetMode != TargetModeInternal {
			return "", nil, false, fmt.Errorf("%w: external composition story", ErrInvalid)
		}
		target, err := resolvePart(owner, relation.Target)
		if err != nil {
			return "", nil, false, err
		}
		if part != "" && !strings.EqualFold(part, target) {
			return "", nil, false, fmt.Errorf("%w: multiple composition story targets", ErrInvalid)
		}
		part = target
	}
	if part == "" {
		return "", nil, false, nil
	}
	value, exists := s.parts[strings.ToLower(part)]
	if !exists || !strings.EqualFold(value.name, part) || !strings.EqualFold(value.media, fixedContentType(kind)) {
		return "", nil, false, &PartError{Part: part, Err: fmt.Errorf("%w: composition story part or content type", ErrInvalid)}
	}
	if int64(len(value.data)) > g.plan.budget.limits.MaxPartBytes {
		return "", nil, false, fmt.Errorf("%w: composition story XML bytes", ErrLimit)
	}
	if err := g.plan.budget.scan(int64(len(value.data))); err != nil {
		return "", nil, false, err
	}
	ns, extended := structureNamespace(s.format), false
	root, err := decodeXMLVisit(value.data, g.plan.budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); start {
			if err := g.plan.budget.step(len(node.Attr) + 1); err != nil {
				return err
			}
			if node.Name.Space != ns {
				extended = true
			}
			for _, attr := range node.Attr {
				if attr.Name.Space != "" && attr.Name.Space != xmlnsNamespace && attr.Name.Space != xmlNamespace {
					extended = true
				}
			}
		}
		return nil
	})
	if err == nil {
		root, err = preprocessXMLContext(root, []string{ns}, g.plan.budget.context)
	}
	if err != nil {
		return "", nil, false, &PartError{Part: part, Err: err}
	}
	if root.Name != (xml.Name{Space: ns, Local: local}) {
		return "", nil, false, &PartError{Part: part, Err: fmt.Errorf("%w: composition story root", ErrInvalid)}
	}
	return part, root, extended, nil
}

// input 建立原文档的故事索引，缺少片段不会被替换为空片段
// 入参: key 原包及原文档身份
// 返回: *compositionStoryInput 缓存模型, error 结构、引用、预算或取消错误
func (g *compositionStoryProjector) input(key compositionStoryDocument) (*compositionStoryInput, error) {
	if value, exists := g.inputs[key]; exists {
		return value, nil
	}
	s := g.plan.sources[key.source]
	document := s.documents[key.document]
	value := &compositionStoryInput{fragments: make(map[int]*StoryFragments), locations: make(map[contentFragmentKey][]int), extendedFragments: make(map[int]bool)}
	part, root, extended, err := g.root(key.source, document.Part, "documentstructure", "DocumentStructure")
	if err != nil {
		return nil, err
	}
	value.extended = extended
	known := make(map[string]bool)
	if root != nil {
		value.structure, err = parseDocumentStructure(root, structureNamespace(s.format), len(document.Pages))
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		value.structure.Part = part
		for _, story := range value.structure.Stories {
			known[story.Name] = true
		}
	}
	first := g.plan.indices[key.source].starts[key.document]
	fragmentNames := make(map[contentFragmentKey]bool)
	for local, page := range document.Pages {
		if err := g.plan.budget.step(1); err != nil {
			return nil, err
		}
		if !s.selected[first+local] {
			continue
		}
		part, root, extended, err := g.root(key.source, page.Part, "storyfragments", "StoryFragments")
		if err != nil {
			return nil, err
		}
		value.extendedFragments[first+local] = extended
		if root == nil {
			continue
		}
		fragments, err := parseStoryFragments(root, structureNamespace(s.format), g.plan.budget.limits.MaxXMLDepth)
		if err != nil {
			return nil, &PartError{Part: part, Err: err}
		}
		fragments.Part, value.fragments[first+local] = part, fragments
		for index, fragment := range fragments.Fragments {
			if err := g.plan.budget.step(1); err != nil {
				return nil, err
			}
			if fragment.StoryName == nil {
				continue
			}
			if !known[*fragment.StoryName] {
				return nil, &PartError{Part: part, Err: fmt.Errorf("%w: undefined composition story %q", ErrInvalid, *fragment.StoryName)}
			}
			location := contentFragmentKey{page: local, story: *fragment.StoryName}
			value.locations[location] = append(value.locations[location], index)
			if fragment.FragmentName != nil {
				location.named, location.name = true, *fragment.FragmentName
				value.locations[location] = append(value.locations[location], index)
				location.page = -1
				if fragmentNames[location] {
					return nil, fmt.Errorf("%w: duplicate composition fragment name", ErrInvalid)
				}
				fragmentNames[location] = true
			}
		}
	}
	if value.structure != nil {
		for _, story := range value.structure.Stories {
			for _, reference := range story.Fragments {
				if err := g.plan.budget.step(1); err != nil {
					return nil, err
				}
				if !s.selected[first+reference.PageNumber-1] {
					continue
				}
				location := compositionStoryLocation(story.Name, reference)
				if len(value.locations[location]) != 1 {
					return nil, &PartError{Part: value.structure.Part, Err: fmt.Errorf("%w: missing or ambiguous composition fragment", ErrInvalid)}
				}
			}
		}
	}
	g.inputs[key] = value
	return value, nil
}

// compositionStoryLocation 保留引用名称的省略状态，不把空字符串当作缺省名
// 入参: story 故事名, reference 原片段引用
// 返回: contentFragmentKey 文档内片段定位键
func compositionStoryLocation(story string, reference StoryFragmentReference) contentFragmentKey {
	key := contentFragmentKey{page: reference.PageNumber - 1, story: story}
	if reference.FragmentName != nil {
		key.named, key.name = true, *reference.FragmentName
	}
	return key
}

// allocate 先保留原名称的首次使用，再为重复身份选择不占用其他原名的名称
// 入参: original 原名称, budget 共享预算
// 返回: string 当前身份的独立名称, error 预算或取消错误
func (n *compositionStoryNames) allocate(original string, budget *compositionBudget) (string, error) {
	if err := budget.step(1); err != nil {
		return "", err
	}
	if err := budget.scan(int64(len(original))); err != nil {
		return "", err
	}
	if !n.used[original] {
		n.used[original] = true
		return original, nil
	}
	for {
		if err := budget.step(1); err != nil {
			return "", err
		}
		if n.next == math.MaxInt {
			return "", fmt.Errorf("%w: composition story name count", ErrLimit)
		}
		n.next++
		name := original + "_" + strconv.Itoa(n.next)
		if err := budget.scan(int64(len(name))); err != nil {
			return "", err
		}
		if !n.reserved[name] && !n.used[name] {
			n.used[name] = true
			return name, nil
		}
	}
}

// document 将各原文档作为独立故事域投影到一个输出文档，不按页面位置重排原故事
// 入参: index 输出文档序号
// 返回: error 原结构、投影、许可、预算或取消错误
func (g *compositionStoryProjector) document(index int) error {
	destination := g.plan.documents[index]
	var order []compositionStoryDocument
	inputs := make(map[compositionStoryDocument]*compositionStoryInput)
	pages := make(map[compositionStoryDocument]map[int][]int)
	outputs := make(map[compositionStoryDocument][]int)
	identity := destination.complete && g.plan.sources[destination.source].format == g.plan.format
	protected := false
	extended := false
	for _, output := range destination.pages {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		instance := g.plan.pages[output]
		document, _, err := g.plan.documentPage(instance.source, instance.index)
		if err != nil {
			return err
		}
		key := compositionStoryDocument{source: instance.source, document: document}
		if _, exists := inputs[key]; !exists {
			input, err := g.input(key)
			if err != nil {
				return err
			}
			inputs[key], pages[key] = input, make(map[int][]int)
			order = append(order, key)
		}
		if structure := inputs[key].structure; structure != nil {
			protected = protected || g.fixed(key.source, structure.Part)
		}
		if fragments := inputs[key].fragments[instance.index]; fragments != nil {
			protected = protected || g.fixed(key.source, fragments.Part)
		}
		pages[key][instance.index] = append(pages[key][instance.index], output)
		outputs[key] = append(outputs[key], output)
		extended = extended || inputs[key].extended || inputs[key].extendedFragments[instance.index]
		for original, name := range g.names.pages[output] {
			if err := g.plan.budget.step(1); err != nil {
				return err
			}
			identity = identity && original == name
		}
		source := g.plan.sources[key.source]
		protected = protected || source.restricted[strings.ToLower(source.documents[key.document].Part)] || g.fixed(key.source, source.documents[key.document].Part) || g.fixed(key.source, source.pages[instance.index].Part)
	}
	if protected && !identity {
		return fmt.Errorf("%w: protected composition story projection", ErrRestricted)
	}
	if extended && !identity {
		return fmt.Errorf("%w: composition story retained XML requires original document", ErrUnsupported)
	}
	storyNames := &compositionStoryNames{reserved: make(map[string]bool), used: make(map[string]bool)}
	for _, key := range order {
		if structure := inputs[key].structure; structure != nil {
			for _, story := range structure.Stories {
				if err := g.plan.budget.step(1); err != nil {
					return err
				}
				if err := g.plan.budget.scan(int64(len(story.Name))); err != nil {
					return err
				}
				storyNames.reserved[story.Name] = true
			}
		}
	}
	for _, key := range order {
		if err := g.project(index, key, inputs[key], pages[key], outputs[key], storyNames); err != nil {
			return err
		}
	}
	if identity && len(order) == 1 {
		input := inputs[order[0]]
		unchanged := equalDocumentStructure(input.structure, g.result.documents[index])
		for _, output := range destination.pages {
			original := input.fragments[g.plan.pages[output].index]
			unchanged = unchanged && equalStoryFragments(original, g.result.fragments[output])
		}
		if protected && !unchanged {
			return fmt.Errorf("%w: protected composition story changed", ErrRestricted)
		}
		if extended && !unchanged {
			return fmt.Errorf("%w: composition story extension rewrite", ErrUnsupported)
		}
		if unchanged {
			g.result.keepDocuments[index] = input.structure != nil
			for _, output := range destination.pages {
				g.result.keepFragments[output] = g.result.fragments[output] != nil
			}
		}
	}
	return nil
}

// fixed 检查部件是否属于组合规划要求保留原文的保护集合
// 入参: source 源包序号, part 原部件URI
// 返回: bool 是否固定
func (g *compositionStoryProjector) fixed(source int, part string) bool {
	_, found := g.plan.fixed[compositionPartKey{source: source, part: strings.ToLower(part), document: -1, page: -1}]
	return found
}

// project 复制原结构与选中片段，显式片段名仅在所属故事中协调
// 入参: document 输出文档序号, key 原文档身份, input 原模型, pages 原页到输出实例, outputs 本来源的输出页序, allocator 故事名称分配器
// 返回: error 复制、引用、许可、预算或取消错误
func (g *compositionStoryProjector) project(document int, key compositionStoryDocument, input *compositionStoryInput, pages map[int][]int, outputs []int, allocator *compositionStoryNames) error {
	mapping := make(map[string]string)
	fragmentNames := make(map[string]*compositionStoryNames)
	if input.structure != nil {
		for _, story := range input.structure.Stories {
			name, err := allocator.allocate(story.Name, g.plan.budget)
			if err != nil {
				return err
			}
			mapping[story.Name] = name
			fragmentNames[story.Name] = &compositionStoryNames{reserved: make(map[string]bool), used: make(map[string]bool)}
		}
	}
	for _, page := range outputs {
		instance := g.plan.pages[page]
		if instance.source != key.source || len(pages[instance.index]) == 0 {
			continue
		}
		if fragments := input.fragments[instance.index]; fragments != nil {
			for _, fragment := range fragments.Fragments {
				if err := g.plan.budget.step(1); err != nil {
					return err
				}
				if fragment.StoryName != nil && fragment.FragmentName != nil {
					fragmentNames[*fragment.StoryName].reserved[*fragment.FragmentName] = true
				}
			}
		}
	}
	for _, page := range outputs {
		instance := g.plan.pages[page]
		if instance.source != key.source || len(pages[instance.index]) == 0 || input.fragments[instance.index] == nil {
			continue
		}
		original := input.fragments[instance.index]
		result := &StoryFragments{Part: original.Part}
		for _, fragment := range original.Fragments {
			if err := g.plan.budget.step(1); err != nil {
				return err
			}
			clone := fragment
			clone.StoryName, clone.FragmentName = compositionStoryString(fragment.StoryName), compositionStoryString(fragment.FragmentName)
			if fragment.StoryName != nil {
				name := mapping[*fragment.StoryName]
				clone.StoryName = &name
				if fragment.FragmentName != nil {
					name, err := fragmentNames[*fragment.StoryName].allocate(*fragment.FragmentName, g.plan.budget)
					if err != nil {
						return err
					}
					clone.FragmentName = &name
				}
			}
			var err error
			clone.Content, err = g.content(page, fragment.Content, 0)
			if err != nil {
				return err
			}
			result.Fragments = append(result.Fragments, clone)
		}
		if g.fixed(key.source, original.Part) && !equalStoryFragments(original, result) {
			return fmt.Errorf("%w: protected composition fragments changed", ErrRestricted)
		}
		g.result.fragments[page] = result
	}
	if input.structure == nil {
		return nil
	}
	result := g.result.documents[document]
	if result == nil {
		result = &DocumentStructure{Part: input.structure.Part}
		g.result.documents[document] = result
	} else {
		result.Part = ""
	}
	if outline := input.structure.Outline; outline != nil {
		if result.Outline == nil {
			result.Outline = &DocumentOutline{Language: outline.Language}
		}
		for _, entry := range outline.Entries {
			if err := g.plan.budget.step(1); err != nil {
				return err
			}
			entry.Language = compositionStoryString(entry.Language)
			if entry.Language == nil && outline.Language != result.Outline.Language {
				language := outline.Language
				entry.Language = &language
			}
			result.Outline.Entries = append(result.Outline.Entries, entry)
			g.result.outlines[document] = append(g.result.outlines[document], compositionStoryOrigin{source: key.source, part: input.structure.Part})
		}
	}
	first := g.plan.indices[key.source].starts[key.document]
	for _, story := range input.structure.Stories {
		projected := Story{Name: mapping[story.Name]}
		var occurrences []compositionStoryOccurrence
		for ordinal, reference := range story.Fragments {
			if err := g.plan.budget.step(1); err != nil {
				return err
			}
			for _, page := range pages[first+reference.PageNumber-1] {
				if err := g.plan.budget.step(1); err != nil {
					return err
				}
				indices := input.locations[compositionStoryLocation(story.Name, reference)]
				if len(indices) != 1 {
					return fmt.Errorf("%w: composition story reference binding", ErrInvalid)
				}
				fragment := indices[0]
				position := g.plan.pages[page].position + 1
				if int64(position) > int64(1<<31-1) {
					return fmt.Errorf("%w: composition story page number", ErrLimit)
				}
				ref := StoryFragmentReference{PageNumber: position}
				if reference.FragmentName != nil {
					ref.FragmentName = compositionStoryString(g.result.fragments[page].Fragments[fragment].FragmentName)
				}
				projected.Fragments = append(projected.Fragments, ref)
				occurrences = append(occurrences, compositionStoryOccurrence{ordinal: ordinal, page: page, fragment: fragment})
			}
		}
		if err := g.breaks(occurrences, len(story.Fragments)); err != nil {
			return err
		}
		if len(projected.Fragments) != 0 {
			result.Stories = append(result.Stories, projected)
		} else {
			for _, page := range outputs {
				if err := g.plan.budget.step(1); err != nil {
					return err
				}
				instance := g.plan.pages[page]
				if instance.source != key.source || len(pages[instance.index]) == 0 || g.result.fragments[page] == nil {
					continue
				}
				for _, fragment := range g.result.fragments[page].Fragments {
					if fragment.StoryName != nil && *fragment.StoryName == projected.Name {
						return fmt.Errorf("%w: retained fragment has no projected story reference", ErrUnsupported)
					}
				}
			}
		}
	}
	if g.fixed(key.source, input.structure.Part) && !equalDocumentStructure(input.structure, result) {
		return fmt.Errorf("%w: protected composition structure changed", ErrRestricted)
	}
	return nil
}

// breaks 按相邻引用协调共享片段的断点，保留原有续接并隔断选页产生的新邻接
// 入参: occurrences 作者顺序展开的引用, count 原引用数
// 返回: error 续接约束无法同时满足、预算或取消错误
func (g *compositionStoryProjector) breaks(occurrences []compositionStoryOccurrence, count int) error {
	states := make(map[[2]int]compositionStoryBoundary)
	for _, occurrence := range occurrences {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		fragment := &g.result.fragments[occurrence.page].Fragments[occurrence.fragment]
		states[[2]int{occurrence.page, occurrence.fragment}] = compositionStoryBoundary{breaks: [2]bool{fragment.BreakBefore, fragment.BreakAfter}}
	}
	for index := 1; index < len(occurrences); index++ {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		previous, current := occurrences[index-1], occurrences[index]
		left, right := [2]int{previous.page, previous.fragment}, [2]int{current.page, current.fragment}
		if previous.ordinal+1 == current.ordinal && !states[left].breaks[1] && !states[right].breaks[0] {
			state := states[left]
			state.joined[1] = true
			states[left] = state
			state = states[right]
			state.joined[0] = true
			states[right] = state
		}
	}
	for index, occurrence := range occurrences {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		key := [2]int{occurrence.page, occurrence.fragment}
		state := states[key]
		if index == 0 && occurrence.ordinal != 0 && !state.joined[0] {
			state.breaks[0] = true
		}
		if index == len(occurrences)-1 && occurrence.ordinal != count-1 && !state.joined[1] {
			state.breaks[1] = true
		}
		states[key] = state
		if index == 0 {
			continue
		}
		previous := occurrences[index-1]
		left := [2]int{previous.page, previous.fragment}
		if previous.ordinal+1 == occurrence.ordinal && !states[left].breaks[1] && !states[key].breaks[0] {
			continue
		}
		state = states[left]
		if !state.joined[1] {
			state.breaks[1] = true
		}
		states[left] = state
		state = states[key]
		if !state.joined[0] {
			state.breaks[0] = true
		}
		states[key] = state
		if !states[left].breaks[1] && !states[key].breaks[0] {
			return fmt.Errorf("%w: one composition fragment requires incompatible continuation boundaries", ErrUnsupported)
		}
	}
	for key, state := range states {
		if err := g.plan.budget.step(1); err != nil {
			return err
		}
		fragment := &g.result.fragments[key[0]].Fragments[key[1]]
		fragment.BreakBefore, fragment.BreakAfter = state.breaks[0], state.breaks[1]
	}
	return nil
}

// content 复制语义树并重映视觉名称，不删除空单元格或改变列表与表格层次
// 入参: page 输出页面实例, source 原语义节点, depth 当前深度
// 返回: []ContentStructure 独立语义树, error 名称、深度、预算或取消错误
func (g *compositionStoryProjector) content(page int, source []ContentStructure, depth int) ([]ContentStructure, error) {
	if depth >= g.plan.budget.limits.MaxXMLDepth {
		return nil, fmt.Errorf("%w: composition story depth", ErrLimit)
	}
	var result []ContentStructure
	for _, node := range source {
		if err := g.plan.budget.step(1); err != nil {
			return nil, err
		}
		clone := node
		var err error
		if node.Kind == StructureNamedElement {
			if err := g.visual(page, node.NameReference); err != nil {
				return nil, err
			}
			clone.NameReference, err = g.names.target(page, node.NameReference)
			if err != nil {
				return nil, err
			}
		}
		if node.Marker != nil {
			if err := g.visual(page, *node.Marker); err != nil {
				return nil, err
			}
			marker, err := g.names.target(page, *node.Marker)
			if err != nil {
				return nil, err
			}
			clone.Marker = &marker
		}
		if len(node.Children) != 0 {
			clone.Children, err = g.content(page, node.Children, depth+1)
			if err != nil {
				return nil, err
			}
		}
		result = append(result, clone)
	}
	return result, nil
}

// visual 核对消费分支中的实际视觉名称是否存在于命名元素集合
// 入参: page 输出页面实例, name 原视觉名称
// 返回: error 名称、页面、预算或取消错误
func (g *compositionStoryProjector) visual(page int, name string) error {
	instance := g.plan.pages[page]
	key := compositionPageKey{source: instance.source, index: instance.index}
	names, exists := g.visuals[key]
	if !exists {
		source := g.plan.sources[key.source]
		part, found := source.parts[strings.ToLower(source.pages[key.index].Part)]
		if !found {
			return fmt.Errorf("%w: missing composition story page", ErrInvalid)
		}
		if int64(len(part.data)) > g.plan.budget.limits.MaxPartBytes {
			return fmt.Errorf("%w: composition story page bytes", ErrLimit)
		}
		if err := g.plan.budget.scan(int64(len(part.data))); err != nil {
			return err
		}
		root, err := decodeXMLVisit(part.data, g.plan.budget.limits, func(token xml.Token, node *xmlElement) error {
			return g.plan.budget.step(1)
		})
		if err == nil {
			root, err = preprocessXMLContext(root, []string{formatNamespace(source.format), formatNamespace(source.format) + "/resourcedictionary-key"}, g.plan.budget.context)
		}
		if err != nil {
			return err
		}
		if root.Name != (xml.Name{Space: formatNamespace(source.format), Local: "FixedPage"}) {
			return fmt.Errorf("%w: composition story page root", ErrInvalid)
		}
		names = make(map[string]bool)
		var visit func(*xmlElement) error
		visit = func(node *xmlElement) error {
			if err := g.plan.budget.step(1); err != nil {
				return err
			}
			if node.Name.Space == formatNamespace(source.format) {
				switch node.Name.Local {
				case "FixedPage", "Canvas", "Path", "Glyphs":
					if name, present := node.attribute("Name"); present {
						names[strings.Trim(name, " \t\r\n")] = true
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
		if err := visit(root); err != nil {
			return err
		}
		g.visuals[key] = names
	}
	if !names[name] {
		return fmt.Errorf("%w: missing composition story visual %q", ErrInvalid, name)
	}
	return g.plan.budget.step(1)
}

// compositionStoryString 复制可选字符串，保留省略与空值的区别
// 入参: value 原可选值
// 返回: *string 独立指针，省略时为nil
func compositionStoryString(value *string) *string {
	if value == nil {
		return nil
	}
	copy := *value
	return &copy
}

// equalOptionalString 比较可选字符串，保留nil与空值的区别
// 入参: a, b 可选字符串指针
// 返回: bool 是否完全等价
func equalOptionalString(a, b *string) bool {
	if a == nil || b == nil {
		return a == b
	}
	return *a == *b
}

// equalDocumentStructure 深度比较文档结构模型，区分nil与空切片
// 入参: a, b 文档结构指针
// 返回: bool 是否完全等价
func equalDocumentStructure(a, b *DocumentStructure) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || a.Part != b.Part || !equalDocumentOutline(a.Outline, b.Outline) || (a.Stories == nil) != (b.Stories == nil) || len(a.Stories) != len(b.Stories) {
		return false
	}
	for index := range a.Stories {
		if !equalStory(a.Stories[index], b.Stories[index]) {
			return false
		}
	}
	return true
}

// equalDocumentOutline 深度比较文档目录模型，区分nil与空切片
// 入参: a, b 目录指针
// 返回: bool 是否完全等价
func equalDocumentOutline(a, b *DocumentOutline) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || a.Language != b.Language || (a.Entries == nil) != (b.Entries == nil) || len(a.Entries) != len(b.Entries) {
		return false
	}
	for index := range a.Entries {
		left, right := a.Entries[index], b.Entries[index]
		if left.Level != right.Level || left.Target != right.Target || left.Description != right.Description || !equalOptionalString(left.Language, right.Language) {
			return false
		}
	}
	return true
}

// equalStory 深度比较故事定义及其片段引用序列，区分nil与空切片
// 入参: a, b 故事定义
// 返回: bool 是否完全等价
func equalStory(a, b Story) bool {
	if a.Name != b.Name || (a.Fragments == nil) != (b.Fragments == nil) || len(a.Fragments) != len(b.Fragments) {
		return false
	}
	for index := range a.Fragments {
		left, right := a.Fragments[index], b.Fragments[index]
		if left.PageNumber != right.PageNumber || !equalOptionalString(left.FragmentName, right.FragmentName) {
			return false
		}
	}
	return true
}

// equalStoryFragments 深度比较页面故事片段集合，区分nil与空切片
// 入参: a, b 片段集合指针
// 返回: bool 是否完全等价
func equalStoryFragments(a, b *StoryFragments) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || a.Part != b.Part || (a.Fragments == nil) != (b.Fragments == nil) || len(a.Fragments) != len(b.Fragments) {
		return false
	}
	for index := range a.Fragments {
		if !equalStoryFragment(a.Fragments[index], b.Fragments[index]) {
			return false
		}
	}
	return true
}

// equalStoryFragment 深度比较单个故事片段，保留指针省略与断点语义
// 入参: a, b 故事片段
// 返回: bool 是否完全等价
func equalStoryFragment(a, b StoryFragment) bool {
	if !equalOptionalString(a.StoryName, b.StoryName) || !equalOptionalString(a.FragmentName, b.FragmentName) || a.Type != b.Type || a.BreakBefore != b.BreakBefore || a.BreakAfter != b.BreakAfter {
		return false
	}
	return equalContentStructures(a.Content, b.Content)
}

// equalContentStructures 深度比较语义结构节点切片，区分nil与空切片
// 入参: a, b 语义节点切片
// 返回: bool 是否完全等价
func equalContentStructures(a, b []ContentStructure) bool {
	if (a == nil) != (b == nil) || len(a) != len(b) {
		return false
	}
	for index := range a {
		left, right := a[index], b[index]
		if left.Kind != right.Kind || left.NameReference != right.NameReference || !equalOptionalString(left.Marker, right.Marker) || left.RowSpan != right.RowSpan || left.ColumnSpan != right.ColumnSpan || !equalContentStructures(left.Children, right.Children) {
			return false
		}
	}
	return true
}

// newCompositionSignatures 预留全部原始标识后协调冲突，优先保持受保护请求原文
// 入参: plan 页面组合规划, protected 各源需保持原文的部件集合
// 返回: *compositionSignatures 标识映射，失败为nil, error 模式、原标识、许可、预算或取消错误
func newCompositionSignatures(plan *compositionPlan, protected []map[string]bool) (*compositionSignatures, error) {
	if plan == nil || plan.budget == nil || len(plan.indices) != len(plan.sources) || len(protected) != len(plan.sources) {
		return nil, fmt.Errorf("%w: composition signature input", ErrInvalid)
	}
	b := plan.budget
	if err := b.step(len(plan.sources)); err != nil {
		return nil, err
	}
	result := &compositionSignatures{parts: make(map[compositionSignatureKey]map[string]string), budget: b}
	reserved := make(map[string]bool)
	var parts []compositionSignaturePart
	for source, value := range plan.sources {
		if plan.indices[source] == nil {
			continue
		}
		active := make(map[string]bool)
		for _, owner := range slices.Sorted(maps.Keys(value.relationships)) {
			relations := value.relationships[owner]
			if err := b.step(len(relations) + 1); err != nil {
				return nil, err
			}
			if !strings.EqualFold(value.parts[owner].media, fixedContentType("fixeddocument")) {
				continue
			}
			for _, relation := range relations {
				if relation.Type == formatNamespace(value.format)+"/signature-definitions" && relation.TargetMode == TargetModeInternal {
					part, err := resolvePart(owner, relation.Target)
					if err != nil {
						return nil, err
					}
					active[strings.ToLower(part)] = true
				}
			}
		}
		seen := make(map[string]string)
		for _, part := range slices.Sorted(maps.Keys(value.parts)) {
			raw := value.parts[part]
			if err := b.step(1); err != nil {
				return nil, err
			}
			if !strings.EqualFold(raw.media, fixedContentType("signaturedefinitions")) {
				continue
			}
			if err := b.scan(int64(len(raw.data))); err != nil {
				return nil, err
			}
			definitions, err := readSignatureDefinitions(raw.data, formatNamespace(value.format)+"/signature-definitions", b.limits, b.context)
			if err != nil {
				return nil, &PartError{Part: raw.name, Err: err}
			}
			if err := b.step(len(definitions)); err != nil {
				return nil, err
			}
			if active[part] {
				for _, definition := range definitions {
					if previous, exists := seen[definition.ID]; exists && previous != part {
						return nil, fmt.Errorf("%w: duplicate original signature SpotID %q", ErrInvalid, definition.ID)
					}
					seen[definition.ID] = part
				}
			}
			ids, err := compositionSignatureNames(raw, value, b)
			if err != nil {
				return nil, err
			}
			key := compositionSignatureKey{source, part}
			result.parts[key] = make(map[string]string, len(ids))
			parts = append(parts, compositionSignaturePart{key: key, names: ids, protected: protected[source][part]})
			for _, name := range ids {
				reserved[name] = true
			}
		}
	}
	var sortError error
	slices.SortFunc(parts, func(a, c compositionSignaturePart) int {
		if sortError == nil {
			sortError = b.step(1)
		}
		if sortError == nil {
			sortError = b.scan(int64(len(a.key.part)) + int64(len(c.key.part)))
		}
		if order := cmp.Compare(a.key.source, c.key.source); order != 0 {
			return order
		}
		return strings.Compare(a.key.part, c.key.part)
	})
	if sortError != nil {
		return nil, sortError
	}
	claimed := make(map[string]bool)
	owners := make(map[string]int)
	counter := 0
	for _, fixed := range []bool{true, false} {
		for _, part := range parts {
			if err := b.step(1); err != nil {
				return nil, err
			}
			if part.protected != fixed {
				continue
			}
			for _, original := range part.names {
				if err := b.step(1); err != nil {
					return nil, err
				}
				name := original
				if claimed[name] && fixed && owners[name] != part.key.source {
					return nil, fmt.Errorf("%w: protected signature SpotID collision", ErrRestricted)
				}
				for claimed[name] && !fixed {
					if err := b.step(1); err != nil {
						return nil, err
					}
					if counter == math.MaxInt {
						return nil, fmt.Errorf("%w: composition signature name counter", ErrLimit)
					}
					counter++
					suffix := "_" + strconv.Itoa(counter)
					maximum := min(b.limits.MaxPartBytes, b.limits.MaxMetadataBytes, b.limits.MaxPackageBytes)
					if int64(len(original)) > maximum-int64(len(suffix)) {
						return nil, fmt.Errorf("%w: composition signature name bytes", ErrLimit)
					}
					name = original + suffix
					if reserved[name] {
						name = original
					}
				}
				if !claimed[name] {
					owners[name] = part.key.source
				}
				claimed[name] = true
				result.parts[part.key][original] = name
			}
		}
	}
	if err := b.step(0); err != nil {
		return nil, err
	}
	return result, nil
}

// compositionSignatureNames 收集签署请求各已知原始分支中的全部SpotID
// 入参: part 原请求部件, source 源快照, budget 共享预算
// 返回: []string 稳定排序的原始标识, error 模式、扩展、标识、预算或取消错误
func compositionSignatureNames(part packagePart, source *compositionSource, budget *compositionBudget) ([]string, error) {
	if err := budget.scan(int64(len(part.data))); err != nil {
		return nil, err
	}
	validator := compositionProtectionGraph{source: source, budget: budget}
	names := make(map[string]bool)
	_, err := decodeXMLVisit(part.data, budget.limits, func(token xml.Token, node *xmlElement) error {
		if err := budget.step(1); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		if err := validator.attributes(node); err != nil {
			return err
		}
		if err := validator.definition(node); err != nil {
			return err
		}
		if node.Name == (xml.Name{Space: formatNamespace(source.format) + "/signature-definitions", Local: "SignatureDefinition"}) {
			value, exists := node.attribute("SpotID")
			if err := budget.scan(int64(len(value))); err != nil {
				return err
			}
			value = strings.Trim(value, " \t\r\n")
			if !exists || !xmlNCName(value) {
				return fmt.Errorf("%w: preserved signature SpotID", ErrInvalid)
			}
			names[value] = true
		}
		return nil
	})
	if err != nil {
		return nil, &PartError{Part: part.name, Err: err}
	}
	if err := budget.step(len(names)); err != nil {
		return nil, err
	}
	result := slices.Collect(maps.Keys(names))
	var sortError error
	slices.SortFunc(result, func(a, b string) int {
		if sortError == nil {
			sortError = budget.step(1)
		}
		if sortError == nil {
			sortError = budget.scan(int64(len(a)) + int64(len(b)))
		}
		return strings.Compare(a, b)
	})
	if sortError != nil {
		return nil, sortError
	}
	return result, nil
}

// target 查询原请求标识的输出映射，不在写出过程中临时生成未协调的全局ID
// 入参: source 源序号, part 原请求URI, id 按xs:ID规范化的原标识
// 返回: string 输出标识, error 映射、预算或取消错误
func (s *compositionSignatures) target(source int, part, id string) (string, error) {
	if s == nil || s.budget == nil {
		return "", fmt.Errorf("%w: missing composition signature map", ErrInvalid)
	}
	if err := s.budget.step(1); err != nil {
		return "", err
	}
	if err := s.budget.scan(int64(len(part)) + int64(len(id))); err != nil {
		return "", err
	}
	canonical, err := opcPartName(part)
	if err != nil {
		return "", err
	}
	value, exists := s.parts[compositionSignatureKey{source, strings.ToLower(canonical)}][id]
	if !exists {
		return "", fmt.Errorf("%w: missing composition signature ID mapping", ErrInvalid)
	}
	return value, nil
}

// rewriteCompositionSignatureMarkup 定点改写签署请求标识与页面位置，保留兼容分支、原编码及其他字节
// 入参: value 原请求部件, options 输出位置、共享预算及改写回调
// 返回: []byte 独立的原编码结果，失败为nil, error 模式、扩展、回调、预算或取消错误
func rewriteCompositionSignatureMarkup(value packagePart, options compositionSignatureMarkupOptions) ([]byte, error) {
	if options.format != FormatXPS && options.format != FormatOpenXPS {
		return nil, fmt.Errorf("%w: composition signature markup options", ErrInvalid)
	}
	b := options.budget
	if err := b.step(1); err != nil {
		return nil, err
	}
	if !strings.EqualFold(value.media, fixedContentType("signaturedefinitions")) {
		return nil, fmt.Errorf("%w: composition signature content type", ErrUnsupported)
	}
	if err := b.scan(int64(len(options.part))); err != nil {
		return nil, err
	}
	if _, err := opcPartName(options.part); err != nil {
		return nil, err
	}
	maximum := min(b.limits.MaxMetadataBytes, b.limits.MaxPartBytes, b.limits.MaxPackageBytes, int64(math.MaxInt))
	if int64(len(value.data)) > maximum {
		return nil, fmt.Errorf("%w: composition signature input bytes", ErrLimit)
	}
	if err := b.scan(int64(len(value.data))); err != nil {
		return nil, err
	}
	namespace := formatNamespace(options.format) + "/signature-definitions"
	if _, err := readSignatureDefinitions(value.data, namespace, b.limits, b.context); err != nil {
		return nil, err
	}
	if err := b.scan(int64(len(value.data))); err != nil {
		return nil, err
	}
	input, err := xmlUTF8(value.data)
	if err != nil {
		return nil, err
	}
	g := compositionProtectionGraph{source: &compositionSource{format: options.format}, budget: b}
	var changes []xmlValueReplacement
	var identities map[*xmlElement]string
	omitted := make(map[*xmlElement]int)
	nodes := 0
	outputSize := int64(len(input))
	intermediateLimit := maximum
	if encoding, _ := xmlInputEncoding(value.data); encoding != "utf-8" {
		intermediateLimit += min(maximum/2, int64(math.MaxInt)-maximum)
	}
	var replacementBytes int64
	root, err := decodeXMLVisitSpan(value.data, b.limits, func(token xml.Token, node *xmlElement, start, end int64) error {
		if err := b.step(1); err != nil {
			return err
		}
		if _, endElement := token.(xml.EndElement); endElement {
			if position, present := omitted[node]; present {
				changes = append(changes, xmlValueReplacement{start: position, end: int(end)})
				outputSize -= end - int64(position)
				delete(omitted, node)
			}
			return nil
		}
		if _, startElement := token.(xml.StartElement); !startElement {
			return nil
		}
		nodes++
		if err := g.attributes(node); err != nil {
			return err
		}
		if err := g.definition(node); err != nil {
			return err
		}
		if node.Name.Space != namespace || node.Name.Local != "SignatureDefinition" && node.Name.Local != "SpotLocation" {
			return nil
		}
		attribute := "SpotID"
		if node.Name.Local == "SpotLocation" {
			attribute = "PageURI"
			for _, coordinate := range []string{"StartX", "StartY"} {
				value, _ := node.attribute(coordinate)
				if _, err := signatureDefinitionDouble(value); err != nil {
					return err
				}
			}
		}
		raw, present := node.attribute(attribute)
		if !present {
			return fmt.Errorf("%w: missing composition signature %s", ErrInvalid, attribute)
		}
		normalized := structureURI(raw)
		target := normalized
		if attribute == "SpotID" {
			if !xmlNCName(normalized) {
				return fmt.Errorf("%w: composition signature source ID", ErrInvalid)
			}
			if options.id != nil {
				target, err = options.id(normalized)
				if err != nil {
					return err
				}
			}
		} else if options.spot != nil {
			var keep bool
			target, keep, err = options.spot(normalized)
			if err != nil {
				return err
			}
			if !keep {
				if err := b.step(0); err != nil {
					return err
				}
				omitted[node] = int(start)
				return nil
			}
		}
		if err := b.scan(int64(len(target))); err != nil {
			return err
		}
		if attribute == "SpotID" {
			if !xmlNCName(target) || strings.Trim(target, " \t\r\n") != target {
				return fmt.Errorf("%w: composition signature replacement ID", ErrInvalid)
			}
			if target != normalized {
				if identities == nil {
					identities = make(map[*xmlElement]string)
				}
				identities[node] = target
			}
		}
		if !xmlTextValid(target) {
			return fmt.Errorf("%w: composition signature replacement text", ErrInvalid)
		}
		if target == normalized {
			return nil
		}
		if int64(len(target)) > intermediateLimit-replacementBytes {
			return fmt.Errorf("%w: composition signature replacement bytes", ErrLimit)
		}
		ranges, err := xmlStartAttributeRanges(input[start:end])
		if err != nil || len(ranges) != len(node.Attr) {
			return fmt.Errorf("%w: composition signature attribute ranges", ErrInvalid)
		}
		for index, attr := range node.Attr {
			if attr.Name != (xml.Name{Local: attribute}) {
				continue
			}
			escaped := xmlRewriteBuffer{maximum: intermediateLimit - replacementBytes, context: b.context}
			if err := xml.EscapeText(&escaped, []byte(target)); err != nil {
				return err
			}
			span := ranges[index]
			changes = append(changes, xmlValueReplacement{start: int(start) + span.start, end: int(start) + span.end, data: escaped.Bytes()})
			outputSize += int64(escaped.Len() - (span.end - span.start))
			replacementBytes += int64(escaped.Len())
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if err := b.step(nodes); err != nil {
		return nil, err
	}
	processor := compatibilityProcessor{understood: map[string]bool{namespace: true, mcNamespace: true, xmlNamespace: true}, context: b.context}
	mappings := []map[*xmlElement]string{nil}
	if len(identities) != 0 {
		mappings = append(mappings, identities)
	}
	for _, mapped := range mappings {
		if err := compositionSignatureMarkupIDs(root, processor, compatibilityScope{}, false, make(map[string]bool), mapped, b); err != nil {
			return nil, err
		}
	}
	if len(changes) == 0 {
		output := bytes.Clone(value.data)
		if err := b.step(0); err != nil {
			return nil, err
		}
		return output, nil
	}
	if outputSize < 0 || outputSize > intermediateLimit {
		return nil, fmt.Errorf("%w: composition signature output bytes", ErrLimit)
	}
	output := make([]byte, 0, int(outputSize))
	position := 0
	for _, change := range changes {
		if err := b.step(1); err != nil {
			return nil, err
		}
		if change.start < position || change.end < change.start || change.end > len(input) {
			return nil, fmt.Errorf("%w: overlapping composition signature edits", ErrInvalid)
		}
		output = append(output, input[position:change.start]...)
		output = append(output, change.data...)
		position = change.end
	}
	output = append(output, input[position:]...)
	output, err = restoreXMLEncoding(value.data, output, maximum, b.context)
	if err != nil {
		return nil, err
	}
	if err := b.scan(int64(len(output))); err != nil {
		return nil, err
	}
	if err := b.step(nodes); err != nil {
		return nil, err
	}
	if _, err := readSignatureDefinitions(output, namespace, b.limits, b.context); err != nil {
		return nil, err
	}
	if err := b.step(0); err != nil {
		return nil, err
	}
	return output, nil
}

// compositionSignatureMarkupIDs 检查可同时出现的签署标识，互斥兼容分支允许复用标识
// 入参: node 原始节点, processor 兼容处理器, inherited 祖先规则, branch 是否为直接候选分支, seen 当前标识集合, mapped 可选新标识, budget 共享预算
// 返回: error 重复标识、兼容结构、预算或取消错误
func compositionSignatureMarkupIDs(node *xmlElement, processor compatibilityProcessor, inherited compatibilityScope, branch bool, seen map[string]bool, mapped map[*xmlElement]string, budget *compositionBudget) error {
	if err := budget.step(1); err != nil {
		return err
	}
	scope, err := processor.rules(node, inherited)
	if err != nil {
		return err
	}
	if _, err := processor.attributes(node, scope, branch); err != nil {
		return err
	}
	if node.Name.Space == mcNamespace {
		if node.Name.Local == "AlternateContent" {
			if !xmlWhitespace(node.Text) {
				return fmt.Errorf("%w: composition signature compatibility text", ErrInvalid)
			}
			var selection compatibilitySelection
			union := make(map[string]bool)
			for _, child := range node.Children {
				if err := processor.alternative(child, scope, &selection); err != nil {
					return err
				}
				local := make(map[string]bool)
				if err := compositionSignatureMarkupIDs(child, processor, scope, true, local, mapped, budget); err != nil {
					return err
				}
				for id := range local {
					if err := budget.step(1); err != nil {
						return err
					}
					union[id] = true
				}
			}
			if selection.choices == 0 {
				return fmt.Errorf("%w: composition signature compatibility requires Choice", ErrInvalid)
			}
			for id := range union {
				if err := budget.step(1); err != nil {
					return err
				}
				if seen[id] {
					return fmt.Errorf("%w: duplicate composition signature ID", ErrInvalid)
				}
				seen[id] = true
			}
			return nil
		}
		if !branch || !slices.Contains([]string{"Choice", "Fallback"}, node.Name.Local) {
			return fmt.Errorf("%w: misplaced composition signature compatibility branch", ErrInvalid)
		}
	}
	if node.Name.Local == "SignatureDefinition" && node.Name.Space != mcNamespace {
		raw, _ := node.attribute("SpotID")
		id := structureURI(raw)
		if value, present := mapped[node]; present {
			id = value
		}
		if seen[id] {
			return fmt.Errorf("%w: duplicate composition signature ID", ErrInvalid)
		}
		seen[id] = true
	}
	for _, child := range node.Children {
		if err := compositionSignatureMarkupIDs(child, processor, scope, false, seen, mapped, budget); err != nil {
			return err
		}
	}
	return nil
}
