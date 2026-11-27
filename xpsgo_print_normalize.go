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
	"errors"
	"fmt"
	"math"
	"math/big"
	"strings"
	"unicode/utf8"
)

// PrintNormalizeOptions 设置PrintTicket规范化合并与设备能力补全的作用域及资源预算
type PrintNormalizeOptions struct {
	Settings PrintSettingsOptions
}

// printNormalizer 在单次规范化调用中保存能力索引、参数域、请求来源、比较预算及诊断列表
type printNormalizer struct {
	options     printSettingsConfig
	domains     map[xml.Name]*printParameterDomain
	deltaFeats  map[xml.Name]bool
	reqFeats    map[xml.Name]bool
	diagnostics []Diagnostic
	remaining   int
}

// NormalizePrintTicket 直接基于PrintCapabilities对基础票据与增量票据执行合并、约束消解、默认补全与参数量化
// 入参: ctx 取消Context，nil采用Background, capabilities 设备PrintCapabilities能力文档, base 基础票据，允许为nil, delta 优先增量票据，允许为nil, options 作用域及资源预算，nil采用默认值
// 返回: *PrintSettings 规范化后的独立打印设置, []Diagnostic 规范化过程产生的诊断记录, error 结构、能力、预算或取消错误
func NormalizePrintTicket(ctx context.Context, capabilities *PrintCapabilities, base, delta *PrintSettings, options *PrintSettingsOptions) (*PrintSettings, []Diagnostic, error) {
	if capabilities == nil {
		return nil, nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	configuration, err := printSettingsOptions(ctx, options)
	if err != nil {
		return nil, nil, err
	}
	return normalizePrintSettingsInternal(base, delta, &PrintSettings{Version: capabilities.Version, Elements: capabilities.Elements}, printDocumentCapabilities, configuration, false, true)
}

// NormalizePrintSettings 按Microsoft Print Schema规范对基础票据与增量票据执行合并、设备能力校验、约束消解、默认补全与参数量化
// capabilities支持PrintCapabilities或PrintDeviceCapabilities模型，输出完全合法且独立的PrintSettings
// 入参: ctx 取消Context，nil采用Background, base 基础票据，允许为nil, delta 优先增量票据，允许为nil, capabilities 设备能力文档, options 规范化参数，nil采用默认值
// 返回: *PrintSettings 规范化后的独立打印设置, []Diagnostic 规范化过程产生的诊断记录, error 结构、能力、预算或取消错误
func NormalizePrintSettings(ctx context.Context, base, delta, capabilities *PrintSettings, options *PrintNormalizeOptions) (*PrintSettings, []Diagnostic, error) {
	var settingsOpts *PrintSettingsOptions
	if options != nil {
		optsCopy := options.Settings
		settingsOpts = &optsCopy
	}
	configuration, err := printSettingsOptions(ctx, settingsOpts)
	if err != nil {
		return nil, nil, err
	}
	if capabilities == nil {
		return nil, nil, fmt.Errorf("%w: nil print capabilities", ErrInvalid)
	}
	return normalizePrintSettingsInternal(base, delta, capabilities, printCapabilitiesDocumentMode(capabilities), configuration, false, true)
}

// printCapabilitiesDocumentMode 按文档结构特征区分V4 PrintDeviceCapabilities与PrintCapabilities，而非仅凭Version判断
// 入参: capabilities 能力设置模型
// 返回: printDocumentMode 文档类别模式
func printCapabilitiesDocumentMode(capabilities *PrintSettings) printDocumentMode {
	if capabilities == nil || capabilities.Version != 2 {
		return printDocumentCapabilities
	}
	if capabilities.CapabilitiesChangeID != "" {
		return printDocumentDeviceCapabilities
	}
	for _, element := range capabilities.Elements {
		if printSettingHasImageableAreaType(element) {
			return printDocumentDeviceCapabilities
		}
	}
	return printDocumentCapabilities
}

// normalizePrintSettingsInternal 在纯内存中执行票据合并、能力校验、跨Feature冲突消解、约束回退与参数规范化
// 入参: base 基础票据或nil, delta 增量票据或nil, capabilities 设备能力模型, capMode 能力文档模式, configuration 已校验配置, capValidated 能力模型是否已预校验, checkBudget 是否执行最终序列化字节预算检查
// 返回: *PrintSettings 规范化后的独立打印设置, []Diagnostic 诊断列表, error 校验、预算或取消错误
func normalizePrintSettingsInternal(base, delta, capabilities *PrintSettings, capMode printDocumentMode, configuration printSettingsConfig, capValidated, checkBudget bool) (*PrintSettings, []Diagnostic, error) {
	capConfig := configuration
	capConfig.Scope = PrintScopeUnknown
	capModel := capabilities
	var err error
	if !capValidated {
		capModel, err = validatePrintSettingsModel(capabilities, capConfig, capMode)
		if err != nil {
			return nil, nil, err
		}
	}
	deltaFeats := make(map[xml.Name]bool)
	reqFeats := make(map[xml.Name]bool)
	var parsedBase, parsedDelta *PrintSettings
	if base != nil {
		parsedBase, err = validatePrintSettingsModel(base, configuration, printDocumentTicket)
		if err != nil {
			return nil, nil, err
		}
		for _, element := range parsedBase.Elements {
			if element.Kind == PrintSettingFeature {
				reqFeats[printCanonicalKey(element.Name)] = true
			}
		}
	}
	if delta != nil {
		parsedDelta, err = validatePrintSettingsModel(delta, configuration, printDocumentTicket)
		if err != nil {
			return nil, nil, err
		}
		for _, element := range parsedDelta.Elements {
			if element.Kind == PrintSettingFeature {
				key := printCanonicalKey(element.Name)
				deltaFeats[key] = true
				reqFeats[key] = true
			}
		}
	}
	var ticket *PrintSettings
	if parsedBase != nil && parsedDelta != nil {
		ticket, err = mergePrintSettingsValidated(parsedBase, parsedDelta, configuration)
		if err != nil {
			return nil, nil, err
		}
		ticket, err = validatePrintSettingsModel(ticket, configuration, printDocumentTicket)
		if err != nil {
			return nil, nil, err
		}
	} else if parsedBase != nil {
		ticket = parsedBase
	} else if parsedDelta != nil {
		ticket = parsedDelta
	} else {
		ticket = &PrintSettings{Version: capModel.Version}
	}
	normalizer := printNormalizer{
		options:    configuration,
		domains:    make(map[xml.Name]*printParameterDomain),
		deltaFeats: deltaFeats,
		reqFeats:   reqFeats,
		remaining:  configuration.MaxOptionComparisons,
	}
	for _, element := range capModel.Elements {
		if element.Kind != PrintSettingParameterDef {
			continue
		}
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		domain, err := printParameterDefinition(element, capConfig)
		if err != nil {
			return nil, nil, err
		}
		key := printCanonicalKey(element.Name)
		normalizer.domains[key] = domain
	}
	paramInits := make(map[xml.Name]PrintSetting)
	paramValues := make(map[xml.Name]*PrintValue)
	var rootProperties []PrintSetting
	for _, element := range ticket.Elements {
		if err := checkContext(configuration.context); err != nil {
			return nil, nil, err
		}
		switch element.Kind {
		case PrintSettingParameterInit:
			key := printCanonicalKey(element.Name)
			if normalizer.domains[key] == nil {
				normalizer.addDiagnostic("ParameterInit", "name", fmt.Sprintf("unsupported print ParameterInit %s removed", element.Name.Local))
				continue
			}
			paramInits[key] = element
			if len(element.Children) == 1 && element.Children[0].Value != nil {
				paramValues[key] = element.Children[0].Value
			}
		case PrintSettingProperty:
			rootProperties = append(rootProperties, element)
		}
	}
	skipCaps := normalizer.resolveRootMutexGroups(ticket.Elements, capModel.Elements, paramValues)
	normalizedFeatures, err := normalizer.normalizeFeatureList(ticket.Elements, capModel.Elements, paramInits, paramValues, true, skipCaps)
	if err != nil {
		return nil, nil, err
	}
	referenced := make(map[xml.Name]bool)
	printCollectParameterRefs(normalizedFeatures, referenced)
	normalizedParams, err := normalizer.normalizeParameters(capModel.Elements, paramInits, referenced)
	if err != nil {
		return nil, nil, err
	}
	effectiveParams := make(map[xml.Name]*PrintValue, len(normalizedParams)+len(normalizer.domains))
	for key, domain := range normalizer.domains {
		valCopy := domain.defaultValue
		effectiveParams[key] = &valCopy
	}
	for _, param := range normalizedParams {
		if len(param.Children) == 1 && param.Children[0].Value != nil {
			effectiveParams[printCanonicalKey(param.Name)] = param.Children[0].Value
		}
	}
	normalizedFeatures = normalizer.resolveCrossFeatureConflicts(normalizedFeatures, capModel.Elements, effectiveParams)
	finalReferenced := make(map[xml.Name]bool)
	printCollectParameterRefs(normalizedFeatures, finalReferenced)
	keptParams := make([]PrintSetting, 0, len(normalizedParams))
	keptParamKeys := make(map[xml.Name]bool, len(normalizedParams))
	for _, param := range normalizedParams {
		key := printCanonicalKey(param.Name)
		domain := normalizer.domains[key]
		_, hadInit := paramInits[key]
		if hadInit || finalReferenced[key] || domain != nil && domain.mandatory == "Unconditional" {
			keptParams = append(keptParams, param)
			keptParamKeys[key] = true
		}
	}
	for _, element := range capModel.Elements {
		if element.Kind != PrintSettingParameterDef {
			continue
		}
		key := printCanonicalKey(element.Name)
		if !finalReferenced[key] || keptParamKeys[key] {
			continue
		}
		if domain := normalizer.domains[key]; domain != nil {
			defaultCopy := domain.defaultValue
			keptParams = append(keptParams, PrintSetting{
				Kind:     PrintSettingParameterInit,
				Name:     element.Name,
				Children: []PrintSetting{{Kind: PrintSettingValue, Value: &defaultCopy}},
			})
			keptParamKeys[key] = true
		}
	}
	normalizedParams = keptParams
	resultElements := make([]PrintSetting, 0, len(normalizedFeatures)+len(rootProperties)+len(normalizedParams))
	usedKeys := make(map[xml.Name]bool, len(normalizedFeatures)+len(normalizedParams))
	for _, feature := range normalizedFeatures {
		resultElements = append(resultElements, feature)
		usedKeys[printCanonicalKey(feature.Name)] = true
	}
	for _, param := range normalizedParams {
		usedKeys[printCanonicalKey(param.Name)] = true
	}
	for _, prop := range rootProperties {
		if !usedKeys[printCanonicalKey(prop.Name)] {
			resultElements = append(resultElements, prop)
			usedKeys[printCanonicalKey(prop.Name)] = true
		}
	}
	resultElements = append(resultElements, normalizedParams...)
	version := ticket.Version
	if version == 0 {
		version = 1
	}
	if version > 1 && printSettingsHasAnonymousOption(resultElements) {
		version = 1
	}
	printStripOptionDefaults(resultElements)
	candidate := &PrintSettings{Version: version, Elements: resultElements}
	result, err := validatePrintSettingsModel(candidate, configuration, printDocumentTicket)
	if err != nil {
		return nil, nil, err
	}
	if checkBudget {
		if err := validatePrintSettingsOutputBudget(result, configuration, printDocumentTicket); err != nil {
			return nil, nil, err
		}
	}
	return result, normalizer.diagnostics, nil
}

// resolveRootMutexGroups 在根级规范化前消解作业级与文档级互斥Feature对，避免同时产出冲突设置
// 入参: requestedElements 票据根元素, capElements 能力根元素, paramValues 票据参数初值映射
// 返回: map[xml.Name]bool 需跳过规范化与默认补全的能力Feature规范键集合
func (n *printNormalizer) resolveRootMutexGroups(requestedElements, capElements []PrintSetting, paramValues map[xml.Name]*PrintValue) map[xml.Name]bool {
	skip := make(map[xml.Name]bool)
	capOrder := make(map[xml.Name]int)
	capFeats := make(map[xml.Name]PrintSetting)
	for index, element := range capElements {
		if element.Kind != PrintSettingFeature {
			continue
		}
		if n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(element.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(element.Name)
		capOrder[key] = index
		capFeats[key] = element
	}
	reqFeats := make(map[xml.Name]PrintSetting)
	for _, element := range requestedElements {
		if element.Kind == PrintSettingFeature {
			reqFeats[printCanonicalKey(element.Name)] = element
		}
	}
	pairs := [][2]string{
		{"JobBindAllDocuments", "DocumentBinding"},
		{"JobDuplexAllDocumentsContiguously", "DocumentDuplex"},
		{"JobNUpAllDocumentsContiguously", "DocumentNUp"},
	}
	for _, pair := range pairs {
		jobKey := xml.Name{Space: printKeywordsNS, Local: pair[0]}
		docKey := xml.Name{Space: printKeywordsNS, Local: pair[1]}
		_, hasCapJob := capFeats[jobKey]
		_, hasCapDoc := capFeats[docKey]
		if !hasCapJob || !hasCapDoc {
			continue
		}
		reqJob, hasReqJob := reqFeats[jobKey]
		reqDoc, hasReqDoc := reqFeats[docKey]
		if hasReqJob && !hasReqDoc {
			skip[docKey] = true
			continue
		}
		if !hasReqJob && hasReqDoc {
			skip[jobKey] = true
			continue
		}
		if hasReqJob && hasReqDoc {
			dropJob := true
			if n.deltaFeats[jobKey] && !n.deltaFeats[docKey] {
				dropJob = false
			} else if n.deltaFeats[docKey] && !n.deltaFeats[jobKey] {
				dropJob = true
			} else {
				jobNoOp := printMutexFeatureNoOp(reqJob, paramValues)
				docNoOp := printMutexFeatureNoOp(reqDoc, paramValues)
				if !jobNoOp && docNoOp {
					dropJob = false
				}
			}
			if dropJob {
				skip[jobKey] = true
				n.addDiagnostic("Feature", "name", fmt.Sprintf("conflicting print Feature %s removed in favor of %s", pair[0], pair[1]))
			} else {
				skip[docKey] = true
				n.addDiagnostic("Feature", "name", fmt.Sprintf("conflicting print Feature %s removed in favor of %s", pair[1], pair[0]))
			}
			continue
		}
		if capOrder[jobKey] < capOrder[docKey] {
			skip[docKey] = true
		} else {
			skip[jobKey] = true
		}
	}
	return skip
}

// printMutexFeatureNoOp 判断互斥装订、双面或拼版Feature在请求中是否为无效果恒等项
// 入参: feature 请求的Feature节点, paramValues 票据参数初值映射
// 返回: bool 是否为无效果恒等项
func printMutexFeatureNoOp(feature PrintSetting, paramValues map[xml.Name]*PrintValue) bool {
	for _, child := range feature.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		switch feature.Name.Local {
		case "JobBindAllDocuments", "DocumentBinding":
			return printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "None"
		case "JobDuplexAllDocumentsContiguously", "DocumentDuplex":
			return printPublicKeywordSpace(child.Name.Space) && child.Name.Local == "OneSided"
		case "JobNUpAllDocumentsContiguously", "DocumentNUp":
			for _, prop := range child.Children {
				if prop.Kind == PrintSettingScoredProperty && printPublicKeywordSpace(prop.Name.Space) && prop.Name.Local == "PagesPerSheet" {
					val, ref := printScoredValue(prop.Children)
					if ref != (xml.Name{}) {
						val = paramValues[printCanonicalKey(ref)]
					}
					return val != nil && strings.Trim(val.Text, " \t\r\n") == "1"
				}
			}
			return false
		}
	}
	return true
}

// addDiagnostic 记录一条规范化过程中的非致命修正诊断
// 入参: element 元素名称, attribute 属性名称, message 诊断消息
func (n *printNormalizer) addDiagnostic(element, attribute, message string) {
	n.diagnostics = append(n.diagnostics, Diagnostic{Element: element, Attribute: attribute, Message: message})
}

// step 在选项比较前检查取消状态与比较预算
// 返回: error 取消或预算超限错误
func (n *printNormalizer) step() error {
	if err := checkContext(n.options.context); err != nil {
		return err
	}
	if n.remaining == 0 {
		return fmt.Errorf("%w: print Option comparison budget", ErrLimit)
	}
	n.remaining--
	return nil
}

// featurePriority 返回根级Feature的冲突消解优先级，delta显式声明最高，base次之，默认补全最低
// 入参: key Feature规范化展开名
// 返回: int 优先级数值
func (n *printNormalizer) featurePriority(key xml.Name) int {
	if n.deltaFeats[key] {
		return 2
	}
	if n.reqFeats[key] {
		return 1
	}
	return 0
}

// resolveCrossFeatureConflicts 消解Booklet与OneSided、NUp、Poster、PageForceFrontSide及连续作业拼版与DocumentCollate=Uncollated等跨Feature冲突并记录诊断
// 入参: features 已规范化的根级Feature列表, capElements 能力根元素, paramValues 已规范化及默认补全的参数值映射
// 返回: []PrintSetting 冲突消解后的根级Feature列表
func (n *printNormalizer) resolveCrossFeatureConflicts(features, capElements []PrintSetting, paramValues map[xml.Name]*PrintValue) []PrintSetting {
	capByKey := make(map[xml.Name]PrintSetting)
	for _, el := range capElements {
		if el.Kind == PrintSettingFeature {
			capByKey[printCanonicalKey(el.Name)] = el
		}
	}
	findIdx := func(locals ...string) int {
		for idx, feat := range features {
			if feat.Kind != PrintSettingFeature || !printPublicKeywordSpace(feat.Name.Space) {
				continue
			}
			for _, local := range locals {
				if feat.Name.Local == local {
					return idx
				}
			}
		}
		return -1
	}
	removed := make([]bool, len(features))
	replaceOrDrop := func(idx int, opt *PrintSetting, msg string) {
		n.addDiagnostic("Feature", "name", msg)
		if opt == nil {
			removed[idx] = true
			return
		}
		var kept []PrintSetting
		kept = append(kept, printTicketOptionFromCapability(*opt))
		for _, child := range features[idx].Children {
			if child.Kind != PrintSettingOption {
				kept = append(kept, child)
			}
		}
		features[idx].Children = kept
	}
	findCapOption := func(feat PrintSetting, pred func(PrintSetting) bool) *PrintSetting {
		capFeat, ok := capByKey[printCanonicalKey(feat.Name)]
		if !ok {
			return nil
		}
		for _, child := range capFeat.Children {
			if child.Kind == PrintSettingOption && printOptionUnconstrained(child) && pred(child) {
				copyOpt := child
				return &copyOpt
			}
		}
		return nil
	}
	hasOptionKeyword := func(idx int, local string) bool {
		if idx < 0 || removed[idx] {
			return false
		}
		for _, child := range features[idx].Children {
			if child.Kind == PrintSettingOption && printPublicKeywordSpace(child.Name.Space) && child.Name.Local == local {
				return true
			}
		}
		return false
	}
	isBooklet := func(idx int) bool {
		return hasOptionKeyword(idx, "Booklet")
	}
	activeNUp := func(idx int) bool {
		if idx < 0 || removed[idx] {
			return false
		}
		for _, child := range features[idx].Children {
			if child.Kind == PrintSettingOption && printOptionScoredInt(child, "PagesPerSheet", paramValues) > 1 {
				return true
			}
		}
		return false
	}
	activePoster := func(idx int) bool {
		if idx < 0 || removed[idx] {
			return false
		}
		for _, child := range features[idx].Children {
			if child.Kind == PrintSettingOption && printOptionScoredInt(child, "SheetsPerPage", paramValues) > 1 {
				return true
			}
		}
		return false
	}
	isOneSided := func(idx int) bool {
		return hasOptionKeyword(idx, "OneSided")
	}
	dropBooklet := func(bindIdx int, rival string) {
		fallback := findCapOption(features[bindIdx], func(o PrintSetting) bool {
			return printPublicKeywordSpace(o.Name.Space) && o.Name.Local == "None"
		})
		if fallback == nil {
			fallback = findCapOption(features[bindIdx], func(o PrintSetting) bool {
				return !printPublicKeywordSpace(o.Name.Space) || o.Name.Local != "Booklet"
			})
		}
		replaceOrDrop(bindIdx, fallback, fmt.Sprintf("conflicting print Feature %s Booklet resolved in favor of %s", features[bindIdx].Name.Local, rival))
	}
	dropNUp := func(nupIdx int, rival string) {
		fallback := findCapOption(features[nupIdx], func(o PrintSetting) bool {
			return printOptionScoredInt(o, "PagesPerSheet", paramValues) == 1
		})
		replaceOrDrop(nupIdx, fallback, fmt.Sprintf("conflicting print Feature %s resolved in favor of %s", features[nupIdx].Name.Local, rival))
	}
	dropPoster := func(posterIdx int, rival string) {
		fallback := findCapOption(features[posterIdx], func(o PrintSetting) bool {
			return printOptionScoredInt(o, "SheetsPerPage", paramValues) == 1
		})
		replaceOrDrop(posterIdx, fallback, fmt.Sprintf("conflicting print Feature %s resolved in favor of %s", features[posterIdx].Name.Local, rival))
	}
	dropKeywordOption := func(idx int, fallbackLocal, rival string) {
		fallback := findCapOption(features[idx], func(o PrintSetting) bool {
			return printPublicKeywordSpace(o.Name.Space) && o.Name.Local == fallbackLocal
		})
		replaceOrDrop(idx, fallback, fmt.Sprintf("conflicting print Feature %s resolved in favor of %s", features[idx].Name.Local, rival))
	}
	bindIdx := findIdx("JobBindAllDocuments", "DocumentBinding")
	nupIdx := findIdx("JobNUpAllDocumentsContiguously", "DocumentNUp")
	posterIdx := findIdx("PagePoster")
	duplexIdx := findIdx("JobDuplexAllDocumentsContiguously", "DocumentDuplex")
	forceIdx := findIdx("PageForceFrontSide")
	var bookletTwoSided *PrintSetting
	if isBooklet(bindIdx) && isOneSided(duplexIdx) {
		bookletTwoSided = findCapOption(features[duplexIdx], func(o PrintSetting) bool {
			return printPublicKeywordSpace(o.Name.Space) && o.Name.Local == "TwoSidedShortEdge"
		})
		if bookletTwoSided == nil {
			bookletTwoSided = findCapOption(features[duplexIdx], func(o PrintSetting) bool {
				return printPublicKeywordSpace(o.Name.Space) && o.Name.Local == "TwoSidedLongEdge"
			})
		}
		if bookletTwoSided == nil || n.featurePriority(printCanonicalKey(features[duplexIdx].Name)) > n.featurePriority(printCanonicalKey(features[bindIdx].Name)) {
			dropBooklet(bindIdx, features[duplexIdx].Name.Local)
		}
	}
	if isBooklet(bindIdx) && activeNUp(nupIdx) {
		if n.featurePriority(printCanonicalKey(features[nupIdx].Name)) > n.featurePriority(printCanonicalKey(features[bindIdx].Name)) {
			dropBooklet(bindIdx, features[nupIdx].Name.Local)
		} else {
			dropNUp(nupIdx, features[bindIdx].Name.Local)
		}
	}
	if isBooklet(bindIdx) && activePoster(posterIdx) {
		if n.featurePriority(printCanonicalKey(features[posterIdx].Name)) > n.featurePriority(printCanonicalKey(features[bindIdx].Name)) {
			dropBooklet(bindIdx, features[posterIdx].Name.Local)
		} else {
			dropPoster(posterIdx, features[bindIdx].Name.Local)
		}
	}
	if isBooklet(bindIdx) && hasOptionKeyword(forceIdx, "ForceFrontSide") {
		if n.featurePriority(printCanonicalKey(features[forceIdx].Name)) > n.featurePriority(printCanonicalKey(features[bindIdx].Name)) {
			dropBooklet(bindIdx, features[forceIdx].Name.Local)
		} else {
			dropKeywordOption(forceIdx, "None", features[bindIdx].Name.Local)
		}
	}
	if isBooklet(bindIdx) && isOneSided(duplexIdx) && bookletTwoSided != nil {
		replaceOrDrop(duplexIdx, bookletTwoSided, fmt.Sprintf("conflicting print Feature %s OneSided upgraded for Booklet", features[duplexIdx].Name.Local))
	}
	if activeNUp(nupIdx) && activePoster(posterIdx) {
		if n.featurePriority(printCanonicalKey(features[posterIdx].Name)) > n.featurePriority(printCanonicalKey(features[nupIdx].Name)) {
			dropNUp(nupIdx, features[posterIdx].Name.Local)
		} else {
			dropPoster(posterIdx, features[nupIdx].Name.Local)
		}
	}
	jobNUpIdx := findIdx("JobNUpAllDocumentsContiguously")
	jobDuplexIdx := findIdx("JobDuplexAllDocumentsContiguously")
	docCollateIdx := findIdx("DocumentCollate")
	if hasOptionKeyword(docCollateIdx, "Uncollated") && activeNUp(jobNUpIdx) {
		if n.featurePriority(printCanonicalKey(features[docCollateIdx].Name)) > n.featurePriority(printCanonicalKey(features[jobNUpIdx].Name)) {
			dropNUp(jobNUpIdx, features[docCollateIdx].Name.Local)
		} else {
			dropKeywordOption(docCollateIdx, "Collated", features[jobNUpIdx].Name.Local)
		}
	}
	if hasOptionKeyword(docCollateIdx, "Uncollated") && jobDuplexIdx >= 0 && !removed[jobDuplexIdx] && !isOneSided(jobDuplexIdx) {
		if n.featurePriority(printCanonicalKey(features[docCollateIdx].Name)) > n.featurePriority(printCanonicalKey(features[jobDuplexIdx].Name)) {
			dropKeywordOption(jobDuplexIdx, "OneSided", features[docCollateIdx].Name.Local)
		} else {
			dropKeywordOption(docCollateIdx, "Collated", features[jobDuplexIdx].Name.Local)
		}
	}
	result := make([]PrintSetting, 0, len(features))
	for idx, feat := range features {
		if !removed[idx] {
			result = append(result, feat)
		}
	}
	return result
}

// normalizeFeatureList 在同一父级层级规范化Feature集合，移除未声明项、执行互斥跳过并对缺失项执行Defaulting
// 入参: requestedElements 票据当前层级元素, capElements 能力当前层级元素, paramInits 票据参数初值节点映射, paramValues 票据参数初值映射, isRoot 是否位于文档根层级, skipCaps 需跳过的能力Feature规范键集合
// 返回: []PrintSetting 规范化后的Feature列表, error 预算或取消错误
func (n *printNormalizer) normalizeFeatureList(requestedElements, capElements []PrintSetting, paramInits map[xml.Name]PrintSetting, paramValues map[xml.Name]*PrintValue, isRoot bool, skipCaps map[xml.Name]bool) ([]PrintSetting, error) {
	capByKey := make(map[xml.Name]PrintSetting)
	for _, element := range capElements {
		if element.Kind == PrintSettingFeature {
			capByKey[printCanonicalKey(element.Name)] = element
		}
	}
	reqByKey := make(map[xml.Name]PrintSetting)
	for _, element := range requestedElements {
		if element.Kind != PrintSettingFeature {
			continue
		}
		key := printCanonicalKey(element.Name)
		if _, exists := capByKey[key]; !exists {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("unsupported print Feature %s removed", element.Name.Local))
			continue
		}
		reqByKey[key] = element
	}
	var result []PrintSetting
	for _, capFeat := range capElements {
		if capFeat.Kind != PrintSettingFeature {
			continue
		}
		if err := checkContext(n.options.context); err != nil {
			return nil, err
		}
		if isRoot && n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(capFeat.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(capFeat.Name)
		if skipCaps[key] {
			continue
		}
		reqFeat, present := reqByKey[key]
		var reqPtr *PrintSetting
		if present {
			reqPtr = &reqFeat
		}
		normalized, ok, err := n.normalizeFeature(reqPtr, capFeat, paramInits, paramValues)
		if err != nil {
			return nil, err
		}
		if ok {
			result = append(result, normalized)
		}
	}
	return result, nil
}

// printFeatureSuppressesSubFeatures 判断指定Feature在当前选中项下是否应跳过子Feature默认补全及丢弃冲突子Feature
// 入参: featureName Feature名称, selectedOptions 最终选中的Option切片, hasRequestedSub 请求中是否显式声明了子Feature
// 返回: bool 是否跳过子Feature补全, bool 是否必须移除请求中携带的子Feature
func printFeatureSuppressesSubFeatures(featureName xml.Name, selectedOptions []PrintSetting, hasRequestedSub bool) (bool, bool) {
	if !printPublicKeywordSpace(featureName.Space) || len(selectedOptions) == 0 {
		return false, false
	}
	onlyNone := true
	for _, opt := range selectedOptions {
		if !printPublicKeywordSpace(opt.Name.Space) || opt.Name.Local != "None" {
			onlyNone = false
			break
		}
	}
	if !onlyNone {
		return false, false
	}
	if featureName.Local == "PageWatermark" {
		return true, true
	}
	if featureName.Local == "PageScaling" && !hasRequestedSub {
		return true, false
	}
	return false, false
}

// normalizeFeature 规范化单个Feature及其直接Option和子Feature，支持参数化补全、内联参数裁剪、约束就近评分与PickMany恒等消解
// 入参: requested 票据中的Feature指针，缺失时为nil, capability 设备能力中的Feature, paramInits 票据参数初值节点映射, paramValues 票据参数初值映射
// 返回: PrintSetting 规范化Feature, bool 是否生成有效Feature, error 预算或取消错误
func (n *printNormalizer) normalizeFeature(requested *PrintSetting, capability PrintSetting, paramInits map[xml.Name]PrintSetting, paramValues map[xml.Name]*PrintValue) (PrintSetting, bool, error) {
	selection, err := capability.Selection()
	if err != nil {
		return PrintSetting{}, false, err
	}
	var allOptions []PrintSetting
	var unconstrained []PrintSetting
	unconstrainedNames := make(map[xml.Name]bool)
	constrainedNames := make(map[xml.Name]bool)
	for _, child := range capability.Children {
		if child.Kind != PrintSettingOption {
			continue
		}
		allOptions = append(allOptions, child)
		if child.Constraint == PrintConstraintUnknown || child.Constraint == PrintConstraintNone {
			unconstrained = append(unconstrained, child)
			if child.Name != (xml.Name{}) {
				unconstrainedNames[printCanonicalKey(child.Name)] = true
			}
		} else if child.Name != (xml.Name{}) {
			constrainedNames[printCanonicalKey(child.Name)] = true
		}
	}
	defaultIndex := -1
	for index := range unconstrained {
		if unconstrained[index].Default {
			defaultIndex = index
			break
		}
	}
	if defaultIndex < 0 && len(unconstrained) > 0 {
		defaultIndex = 0
	}
	var selectedOptions []PrintSetting
	var selectedCaps []PrintSetting
	selectDefaultOptions := func() {
		if selection == PrintSelectionMany {
			for _, candidate := range unconstrained {
				if candidate.Default {
					selectedOptions = append(selectedOptions, printTicketOptionFromCapability(candidate))
					selectedCaps = append(selectedCaps, candidate)
				}
			}
			if len(selectedOptions) > 0 {
				return
			}
		}
		selectedOptions = append(selectedOptions, printTicketOptionFromCapability(unconstrained[defaultIndex]))
		selectedCaps = append(selectedCaps, unconstrained[defaultIndex])
	}
	if requested == nil {
		if len(allOptions) > 0 {
			if defaultIndex < 0 {
				return PrintSetting{}, false, nil
			}
			selectDefaultOptions()
		}
		var children []PrintSetting
		children = append(children, selectedOptions...)
		suppressSub, _ := printFeatureSuppressesSubFeatures(capability.Name, selectedOptions, false)
		if !suppressSub {
			subFeatures, err := n.normalizeFeatureList(nil, capability.Children, paramInits, paramValues, false, nil)
			if err != nil {
				return PrintSetting{}, false, err
			}
			children = append(children, subFeatures...)
		}
		if len(children) == 0 {
			return PrintSetting{}, false, nil
		}
		return PrintSetting{Kind: PrintSettingFeature, Name: capability.Name, Children: children}, true, nil
	}
	var reqOptions []PrintSetting
	var reqProps []PrintSetting
	hasRequestedSub := false
	for _, child := range requested.Children {
		if child.Kind == PrintSettingOption {
			reqOptions = append(reqOptions, child)
		} else if child.Kind == PrintSettingProperty {
			reqProps = append(reqProps, child)
		} else if child.Kind == PrintSettingFeature {
			hasRequestedSub = true
		}
	}
	if len(allOptions) > 0 {
		if defaultIndex < 0 {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("all options for print Feature %s are constrained", capability.Name.Local))
			return PrintSetting{}, false, nil
		}
		if len(reqOptions) == 0 {
			selectDefaultOptions()
		} else {
			if selection == PrintSelectionOne && len(reqOptions) > 1 {
				n.addDiagnostic("Feature", "name", fmt.Sprintf("multiple options on PickOne print Feature %s resolved", capability.Name.Local))
				chosenReq := reqOptions[0]
				picked := false
				for _, candidateReq := range reqOptions {
					if candidateReq.Name != (xml.Name{}) && constrainedNames[printCanonicalKey(candidateReq.Name)] && !unconstrainedNames[printCanonicalKey(candidateReq.Name)] {
						continue
					}
					matchedIndex, err := n.matchExactOption(candidateReq, unconstrained, paramValues)
					if err != nil {
						return PrintSetting{}, false, err
					}
					if matchedIndex >= 0 {
						chosenReq, picked = candidateReq, true
						break
					}
				}
				if !picked {
					for _, candidateReq := range reqOptions {
						if candidateReq.Name != (xml.Name{}) && constrainedNames[printCanonicalKey(candidateReq.Name)] && !unconstrainedNames[printCanonicalKey(candidateReq.Name)] {
							continue
						}
						if _, matchedIndex, ok, err := n.normalizeParameterizedOption(candidateReq, unconstrained, paramValues, false); err != nil {
							return PrintSetting{}, false, err
						} else if ok && matchedIndex >= 0 {
							chosenReq = candidateReq
							break
						}
					}
				}
				reqOptions = []PrintSetting{chosenReq}
			}
			selectedIndices := make(map[int]bool)
			for _, reqOpt := range reqOptions {
				reqConstrainedNamed := reqOpt.Name != (xml.Name{}) && constrainedNames[printCanonicalKey(reqOpt.Name)] && !unconstrainedNames[printCanonicalKey(reqOpt.Name)]
				if !reqConstrainedNamed {
					matchedIndex, err := n.matchExactOption(reqOpt, unconstrained, paramValues)
					if err != nil {
						return PrintSetting{}, false, err
					}
					if matchedIndex >= 0 {
						if selectedIndices[matchedIndex] {
							continue
						}
						selectedIndices[matchedIndex] = true
						kept := printCompleteOptionFromCapability(reqOpt, unconstrained[matchedIndex])
						selectedOptions = append(selectedOptions, kept)
						selectedCaps = append(selectedCaps, unconstrained[matchedIndex])
						continue
					}
					clampedOpt, clampedIndex, clampedOK, err := n.normalizeParameterizedOption(reqOpt, unconstrained, paramValues, true)
					if err != nil {
						return PrintSetting{}, false, err
					}
					if clampedOK && clampedIndex >= 0 {
						if selectedIndices[clampedIndex] {
							continue
						}
						selectedIndices[clampedIndex] = true
						selectedOptions = append(selectedOptions, clampedOpt)
						selectedCaps = append(selectedCaps, unconstrained[clampedIndex])
						continue
					}
				}
				scoringOpt := reqOpt
				if reqOpt.Name != (xml.Name{}) {
					reqKey := printCanonicalKey(reqOpt.Name)
					for _, capOpt := range allOptions {
						if printCanonicalKey(capOpt.Name) == reqKey && printScoredCount(capOpt.Children) > 0 {
							scoringOpt = printCompleteOptionFromCapability(reqOpt, capOpt)
							break
						}
					}
					if printScoredCount(scoringOpt.Children) == 0 && printPublicKeywordSpace(capability.Name.Space) && capability.Name.Local == "PageMediaSize" && printPublicKeywordSpace(reqOpt.Name.Space) {
						if dims, ok := printMediaSizes[reqOpt.Name.Local]; ok && dims[0] > 0 && dims[1] > 0 {
							scoringOpt = printTicketOptionFromCapability(reqOpt)
							scoringOpt.Children = append(scoringOpt.Children, printBuildIntScored("MediaSizeWidth", int64(dims[0])), printBuildIntScored("MediaSizeHeight", int64(dims[1])))
						}
					}
				}
				bestIndex, err := n.bestOption(scoringOpt, unconstrained, paramValues)
				if err != nil {
					return PrintSetting{}, false, err
				}
				chosenIndex := defaultIndex
				if bestIndex >= 0 {
					chosenIndex = bestIndex
				}
				chosen := unconstrained[chosenIndex]
				n.addDiagnostic("Option", "name", fmt.Sprintf("print Option %s on Feature %s replaced by %s", reqOpt.Name.Local, capability.Name.Local, chosen.Name.Local))
				if selectedIndices[chosenIndex] {
					continue
				}
				selectedIndices[chosenIndex] = true
				n.backfillParameterRefs(scoringOpt.Children, chosen.Children, paramInits, paramValues)
				selectedOptions = append(selectedOptions, printTicketOptionFromCapability(chosen))
				selectedCaps = append(selectedCaps, chosen)
			}
			if selection == PrintSelectionMany && len(selectedOptions) > 1 {
				hasIdentity, hasNonIdentity := false, false
				identities := make([]bool, len(selectedCaps))
				for index, capOpt := range selectedCaps {
					isID, err := capOpt.Identity()
					if err != nil {
						return PrintSetting{}, false, err
					}
					identities[index] = isID
					if isID {
						hasIdentity = true
					} else {
						hasNonIdentity = true
					}
				}
				if hasIdentity && hasNonIdentity {
					filtered := make([]PrintSetting, 0, len(selectedOptions))
					for index, opt := range selectedOptions {
						if identities[index] {
							n.addDiagnostic("Option", "name", fmt.Sprintf("identity print Option %s removed when combined with other Options on Feature %s", opt.Name.Local, capability.Name.Local))
							continue
						}
						filtered = append(filtered, opt)
					}
					selectedOptions = filtered
				}
			}
		}
	} else if len(reqOptions) > 0 {
		n.addDiagnostic("Option", "name", fmt.Sprintf("unsupported options on container print Feature %s removed", capability.Name.Local))
	}
	var children []PrintSetting
	children = append(children, selectedOptions...)
	suppressSub, dropReqSub := printFeatureSuppressesSubFeatures(capability.Name, selectedOptions, hasRequestedSub)
	var subFeatures []PrintSetting
	if suppressSub {
		if dropReqSub && hasRequestedSub {
			n.addDiagnostic("Feature", "name", fmt.Sprintf("incompatible subfeatures removed for print Feature %s", capability.Name.Local))
		}
	} else {
		subFeatures, err = n.normalizeFeatureList(requested.Children, capability.Children, paramInits, paramValues, false, nil)
		if err != nil {
			return PrintSetting{}, false, err
		}
		children = append(children, subFeatures...)
	}
	if len(children) == 0 {
		return PrintSetting{}, false, nil
	}
	usedPropKeys := make(map[xml.Name]bool, len(subFeatures))
	for _, sub := range subFeatures {
		usedPropKeys[printCanonicalKey(sub.Name)] = true
	}
	for _, prop := range reqProps {
		if !usedPropKeys[printCanonicalKey(prop.Name)] {
			children = append(children, printCloneSetting(prop))
		}
	}
	return PrintSetting{Kind: PrintSettingFeature, Name: requested.Name, Children: children}, true, nil
}

// backfillParameterRefs 在被约束或不支持选项回退至含ParameterRef的能力选项时，将原目标ScoredProperty值回填进参数初值表
// 入参: sourceChildren 原请求补齐后的子元素, targetChildren 选中能力选项的子元素, paramInits 参数初值节点映射, paramValues 参数初值映射
func (n *printNormalizer) backfillParameterRefs(sourceChildren, targetChildren []PrintSetting, paramInits map[xml.Name]PrintSetting, paramValues map[xml.Name]*PrintValue) {
	sourceByKey := make(map[xml.Name]PrintSetting)
	for _, child := range sourceChildren {
		if child.Kind == PrintSettingScoredProperty {
			sourceByKey[printCanonicalKey(child.Name)] = child
		}
	}
	for _, target := range targetChildren {
		if target.Kind != PrintSettingScoredProperty {
			continue
		}
		source, exists := sourceByKey[printCanonicalKey(target.Name)]
		if !exists {
			continue
		}
		_, capRef := printScoredValue(target.Children)
		if capRef != (xml.Name{}) {
			refKey := printCanonicalKey(capRef)
			if domain := n.domains[refKey]; domain != nil {
				srcVal, srcRef := printScoredValue(source.Children)
				if srcRef != (xml.Name{}) {
					srcVal = paramValues[printCanonicalKey(srcRef)]
				}
				if srcVal != nil {
					if normalized, _, ok, err := n.clampValueForDomain(*srcVal, domain); err == nil && ok {
						valCopy := normalized
						paramInits[refKey] = PrintSetting{
							Kind:     PrintSettingParameterInit,
							Name:     capRef,
							Children: []PrintSetting{{Kind: PrintSettingValue, Value: &valCopy}},
						}
						paramValues[refKey] = &valCopy
					}
				}
			}
		}
		n.backfillParameterRefs(source.Children, target.Children, paramInits, paramValues)
	}
}

// printCompleteOptionFromCapability 将匹配能力的请求Option转为合法票据Option并从能力Option补齐缺失ScoredProperty与ParameterRef
// 入参: reqOpt 请求Option节点, capOpt 匹配的能力Option节点
// 返回: PrintSetting 补齐后的独立票据Option节点
func printCompleteOptionFromCapability(reqOpt, capOpt PrintSetting) PrintSetting {
	kept := printTicketOptionFromCapability(reqOpt)
	if kept.Name == (xml.Name{}) && capOpt.Name != (xml.Name{}) {
		kept.Name = capOpt.Name
	}
	kept.Children = printMergeMissingScored(kept.Children, capOpt.Children)
	return kept
}

// printMergeMissingScored 递归将能力节点中缺失的ScoredProperty补入目标节点子列表，保持请求既有值不变
// 入参: dstChildren 请求侧已拷贝子列表, capChildren 能力侧子列表
// 返回: []PrintSetting 补齐后的子列表
func printMergeMissingScored(dstChildren, capChildren []PrintSetting) []PrintSetting {
	existing := make(map[xml.Name]int)
	for index, child := range dstChildren {
		if child.Kind == PrintSettingScoredProperty {
			existing[printCanonicalKey(child.Name)] = index
		}
	}
	for _, capChild := range capChildren {
		if capChild.Kind != PrintSettingScoredProperty {
			continue
		}
		key := printCanonicalKey(capChild.Name)
		if idx, ok := existing[key]; ok {
			dstChildren[idx].Children = printMergeMissingScored(dstChildren[idx].Children, capChild.Children)
			continue
		}
		dstChildren = append(dstChildren, printTicketOptionFromCapability(capChild))
		existing[key] = len(dstChildren) - 1
	}
	return dstChildren
}

// normalizeParameterizedOption 尝试将请求Option内联超界或未对齐的参数化ScoredProperty按对应ParameterDef裁剪量化以匹配未受约束候选
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射, emitDiag 是否记录修正诊断
// 返回: PrintSetting 裁剪补全后的票据Option, int 匹配候选下标, bool 是否匹配成功, error 预算或取消错误
func (n *printNormalizer) normalizeParameterizedOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue, emitDiag bool) (PrintSetting, int, bool, error) {
	if printScoredCount(reqOpt.Children) == 0 {
		return PrintSetting{}, -1, false, nil
	}
	reqKey := printCanonicalKey(reqOpt.Name)
	hasNamed := false
	if reqOpt.Name != (xml.Name{}) {
		for _, cand := range candidates {
			if printCanonicalKey(cand.Name) == reqKey {
				hasNamed = true
				break
			}
		}
	}
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return PrintSetting{}, -1, false, err
		}
		sameName := reqOpt.Name != (xml.Name{}) && printCanonicalKey(cand.Name) == reqKey
		if hasNamed && !sameName {
			continue
		}
		cloned := printTicketOptionFromCapability(reqOpt)
		if cloned.Name == (xml.Name{}) && cand.Name != (xml.Name{}) {
			cloned.Name = cand.Name
		}
		clampedChildren, changed, ok, err := n.normalizeParameterizedScored(cloned.Children, cand.Children, sameName, paramValues, emitDiag)
		if err != nil {
			return PrintSetting{}, -1, false, err
		}
		if ok && changed {
			cloned.Children = printMergeMissingScored(clampedChildren, cand.Children)
			return cloned, index, true, nil
		}
	}
	return PrintSetting{}, -1, false, nil
}

// normalizeParameterizedScored 递归校验并对参数化ScoredProperty的内联超界数值执行ParameterDef域内裁剪量化
// 入参: reqChildren 请求子元素, capChildren 能力子元素, subset 是否允许省略描述, paramValues 票据参数初值映射, emitDiag 是否记录诊断
// 返回: []PrintSetting 规范化后的子元素, bool 是否执行过参数裁剪量化, bool 是否完整匹配候选结构, error 预算或取消错误
func (n *printNormalizer) normalizeParameterizedScored(reqChildren, capChildren []PrintSetting, subset bool, paramValues map[xml.Name]*PrintValue, emitDiag bool) ([]PrintSetting, bool, bool, error) {
	if !subset && printScoredCount(reqChildren) != printScoredCount(capChildren) {
		return nil, false, false, nil
	}
	capByKey := make(map[xml.Name]PrintSetting)
	for _, setting := range capChildren {
		if setting.Kind == PrintSettingScoredProperty {
			capByKey[printCanonicalKey(setting.Name)] = setting
		}
	}
	result := make([]PrintSetting, len(reqChildren))
	copy(result, reqChildren)
	anyChanged := false
	for index := range result {
		setting := &result[index]
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := n.step(); err != nil {
			return nil, false, false, err
		}
		cand, exists := capByKey[printCanonicalKey(setting.Name)]
		if !exists {
			return nil, false, false, nil
		}
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if capRef != (xml.Name{}) {
			if reqRef != (xml.Name{}) {
				if printCanonicalKey(reqRef) != printCanonicalKey(capRef) {
					return nil, false, false, nil
				}
			} else {
				domain := n.domains[printCanonicalKey(capRef)]
				if domain == nil || reqVal == nil {
					return nil, false, false, nil
				}
				if _, err := domain.value(reqVal, n.options); err != nil {
					if !errors.Is(err, ErrInvalid) {
						return nil, false, false, err
					}
					clamped, adjusted, ok, err := n.clampValueForDomain(*reqVal, domain)
					if err != nil {
						return nil, false, false, err
					}
					if !ok {
						return nil, false, false, nil
					}
					for childIdx := range setting.Children {
						if setting.Children[childIdx].Kind == PrintSettingValue {
							valCopy := clamped
							setting.Children[childIdx].Value = &valCopy
							break
						}
					}
					if adjusted {
						anyChanged = true
						if emitDiag {
							n.addDiagnostic("ScoredProperty", "name", fmt.Sprintf("inline print ScoredProperty %s clamped or quantized to %s", setting.Name.Local, clamped.Text))
						}
					}
				}
			}
		} else {
			if reqRef != (xml.Name{}) {
				reqVal = paramValues[printCanonicalKey(reqRef)]
				if reqVal == nil {
					if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
						reqVal = &domain.defaultValue
					}
				}
			}
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil || !same {
				return nil, false, false, err
			}
		}
		nestedChildren, nestedChanged, nestedOK, err := n.normalizeParameterizedScored(setting.Children, cand.Children, subset, paramValues, emitDiag)
		if err != nil || !nestedOK {
			return nil, false, false, err
		}
		setting.Children = nestedChildren
		anyChanged = anyChanged || nestedChanged
	}
	return result, anyChanged, true, nil
}

// normalizeValueForDomain 按ParameterDef域定义裁剪数值、按Multiple步进量化或截断超长字符串，无法合法修正时返回回退原因
// 入参: val 原始标量值, domain 参数域定义
// 返回: PrintValue 规范化后的值, bool 是否产生裁剪或截断, string 无法修正时的回退诊断原因，空表示合法, error 算术预算或取消错误
func (n *printNormalizer) normalizeValueForDomain(val PrintValue, domain *printParameterDomain) (PrintValue, bool, string, error) {
	if val.Type == (xml.Name{}) {
		val.Type = xml.Name{Space: printValueNS, Local: "string"}
	}
	if val.Type != domain.kind {
		return PrintValue{}, false, "type mismatch reset to default", nil
	}
	switch domain.kind.Local {
	case "integer", "decimal":
		text := strings.Trim(val.Text, " \t\r\n")
		if text == "" || domain.kind.Local == "integer" && !printInteger(text) || domain.kind.Local == "decimal" && !printDecimal(text) {
			return PrintValue{}, false, "invalid numeric value reset to default", nil
		}
		num, err := printParameterNumber(text, n.options)
		if err != nil {
			if errors.Is(err, ErrInvalid) {
				return PrintValue{}, false, "invalid numeric value reset to default", nil
			}
			return PrintValue{}, false, "", err
		}
		adjusted := false
		if num.Cmp(domain.minimum) < 0 {
			num = new(big.Rat).Set(domain.minimum)
			adjusted = true
		} else if num.Cmp(domain.maximum) > 0 {
			num = new(big.Rat).Set(domain.maximum)
			adjusted = true
		}
		if domain.multiple != nil {
			diff := new(big.Rat).Sub(num, domain.minimum)
			quot := new(big.Rat).Quo(diff, domain.multiple)
			if !quot.IsInt() {
				qInt := new(big.Int).Quo(quot.Num(), quot.Denom())
				rem := new(big.Int).Rem(quot.Num(), quot.Denom())
				twiceRem := new(big.Int).Lsh(rem, 1)
				chosen := new(big.Int).Set(qInt)
				if twiceRem.Cmp(quot.Denom()) >= 0 {
					ceilQ := new(big.Int).Add(qInt, big.NewInt(1))
					ceilVal := new(big.Rat).Add(domain.minimum, new(big.Rat).Mul(new(big.Rat).SetInt(ceilQ), domain.multiple))
					if ceilVal.Cmp(domain.maximum) <= 0 {
						chosen = ceilQ
					}
				}
				num = new(big.Rat).Add(domain.minimum, new(big.Rat).Mul(new(big.Rat).SetInt(chosen), domain.multiple))
				adjusted = true
			}
		}
		if adjusted {
			if domain.kind.Local == "integer" {
				val.Text = num.Num().String()
			} else {
				val.Text = printFormatDecimalRat(num, n.options.MaxNumericDigits)
			}
		}
		return val, adjusted, "", nil
	case "string":
		if _, err := domain.value(&val, n.options); err == nil {
			return val, false, "", nil
		} else if !errors.Is(err, ErrInvalid) {
			return PrintValue{}, false, "", err
		}
		if domain.unit == "sRGB" {
			return PrintValue{}, false, "invalid sRGB string reset to default", nil
		}
		if domain.unit == "numeric" {
			for _, character := range val.Text {
				if character < '0' || character > '9' {
					return PrintValue{}, false, "invalid numeric string reset to default", nil
				}
			}
		}
		count := big.NewRat(int64(utf8.RuneCountInString(val.Text)), 1)
		if count.Cmp(domain.maximum) > 0 {
			if !domain.maximum.IsInt() || !domain.maximum.Num().IsInt64() {
				return PrintValue{}, false, "string length exceeded reset to default", nil
			}
			val.Text = printTruncateRunes(val.Text, int(domain.maximum.Num().Int64()))
			if _, err := domain.value(&val, n.options); err != nil {
				if errors.Is(err, ErrInvalid) {
					return PrintValue{}, false, "truncated string invalid reset to default", nil
				}
				return PrintValue{}, false, "", err
			}
			return val, true, "", nil
		}
		return PrintValue{}, false, "string shorter than MinLength reset to default", nil
	default:
		validated, err := domain.value(&val, n.options)
		if err == nil {
			return *validated, false, "", nil
		}
		if errors.Is(err, ErrInvalid) {
			return PrintValue{}, false, "invalid QName value reset to default", nil
		}
		return PrintValue{}, false, "", err
	}
}

// clampValueForDomain 将类型匹配的数值或字符串值按ParameterDef的上下界与Multiple步进裁剪量化
// 入参: val 原始标量值, domain 参数域定义
// 返回: PrintValue 规范化后的值, bool 是否产生修正, bool 是否可按该域合法裁剪, error 算术预算或取消错误
func (n *printNormalizer) clampValueForDomain(val PrintValue, domain *printParameterDomain) (PrintValue, bool, bool, error) {
	normalized, adjusted, reason, err := n.normalizeValueForDomain(val, domain)
	if err != nil || reason != "" {
		return PrintValue{}, false, false, err
	}
	return normalized, adjusted, true, nil
}

// matchExactOption 在未受约束候选中查找与请求Option精确匹配的下标，未命中返回负一
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射
// 返回: int 命中候选下标，未命中为负一, error 预算或取消错误
func (n *printNormalizer) matchExactOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue) (int, error) {
	reqKey := printCanonicalKey(reqOpt.Name)
	hasNamedCandidate := false
	if reqOpt.Name != (xml.Name{}) {
		for _, cand := range candidates {
			if printCanonicalKey(cand.Name) == reqKey {
				hasNamedCandidate = true
				break
			}
		}
	}
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return -1, err
		}
		sameName := reqOpt.Name != (xml.Name{}) && printCanonicalKey(cand.Name) == reqKey
		if hasNamedCandidate && !sameName {
			continue
		}
		if !sameName && printScoredCount(reqOpt.Children) == 0 {
			continue
		}
		matched, err := n.matchScoredExact(reqOpt.Children, cand.Children, sameName, paramValues)
		if err != nil {
			return -1, err
		}
		if matched {
			return index, nil
		}
	}
	return -1, nil
}

// matchScoredExact 检查请求Option与候选Option的ScoredProperty是否精确匹配
// 入参: requested 请求子元素, supported 候选子元素, subset 是否允许省略候选已知描述, paramValues 票据参数初值映射
// 返回: bool 是否精确匹配, error 预算或取消错误
func (n *printNormalizer) matchScoredExact(requested, supported []PrintSetting, subset bool, paramValues map[xml.Name]*PrintValue) (bool, error) {
	if !subset && printScoredCount(requested) != printScoredCount(supported) {
		return false, nil
	}
	index := make(map[xml.Name]PrintSetting)
	for _, setting := range supported {
		if setting.Kind == PrintSettingScoredProperty {
			index[printCanonicalKey(setting.Name)] = setting
		}
	}
	for _, setting := range requested {
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := n.step(); err != nil {
			return false, err
		}
		cand, exists := index[printCanonicalKey(setting.Name)]
		if !exists {
			return false, nil
		}
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if capRef != (xml.Name{}) {
			if reqRef != (xml.Name{}) {
				if printCanonicalKey(reqRef) != printCanonicalKey(capRef) {
					return false, nil
				}
			} else {
				domain := n.domains[printCanonicalKey(capRef)]
				if domain == nil {
					return false, nil
				}
				if _, err := domain.value(reqVal, n.options); err != nil {
					if errors.Is(err, ErrInvalid) {
						return false, nil
					}
					return false, err
				}
			}
		} else {
			if reqRef != (xml.Name{}) {
				reqVal = paramValues[printCanonicalKey(reqRef)]
				if reqVal == nil {
					if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
						reqVal = &domain.defaultValue
					}
				}
			}
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil || !same {
				return same, err
			}
		}
		if same, err := n.matchScoredExact(setting.Children, cand.Children, subset, paramValues); err != nil || !same {
			return same, err
		}
	}
	return true, nil
}

// bestOption 按ScoredProperty匹配度评分查找最接近的未受约束候选下标，无匹配时返回负一
// 入参: reqOpt 请求Option, candidates 未受约束候选列表, paramValues 票据参数初值映射
// 返回: int 最佳候选下标，无匹配为负一, error 预算或取消错误
func (n *printNormalizer) bestOption(reqOpt PrintSetting, candidates []PrintSetting, paramValues map[xml.Name]*PrintValue) (int, error) {
	if printScoredCount(reqOpt.Children) == 0 {
		return -1, nil
	}
	bestIndex := -1
	bestScore := 0.0
	for index, cand := range candidates {
		if err := n.step(); err != nil {
			return -1, err
		}
		score, err := n.scoreScored(reqOpt.Children, cand.Children, paramValues)
		if err != nil {
			return -1, err
		}
		if score > 0 && reqOpt.Name != (xml.Name{}) && printCanonicalKey(reqOpt.Name) == printCanonicalKey(cand.Name) {
			score += 0.5
		}
		if score > bestScore || score > 0 && score == bestScore && cand.Default && bestIndex >= 0 && !candidates[bestIndex].Default {
			bestScore = score
			bestIndex = index
		}
	}
	return bestIndex, nil
}

// scoreScored 递归计算两组ScoredProperty的相似度评分，精确值、数值接近度与参数域匹配分别计分
// 入参: requested 请求子元素, supported 候选子元素, paramValues 票据参数初值映射
// 返回: float64 相似度总分, error 预算或取消错误
func (n *printNormalizer) scoreScored(requested, supported []PrintSetting, paramValues map[xml.Name]*PrintValue) (float64, error) {
	index := make(map[xml.Name]PrintSetting)
	for _, setting := range supported {
		if setting.Kind == PrintSettingScoredProperty {
			index[printCanonicalKey(setting.Name)] = setting
		}
	}
	total := 0.0
	for _, setting := range requested {
		if setting.Kind != PrintSettingScoredProperty {
			continue
		}
		if err := n.step(); err != nil {
			return 0, err
		}
		cand, exists := index[printCanonicalKey(setting.Name)]
		if !exists {
			continue
		}
		total += 1.0
		reqVal, reqRef := printScoredValue(setting.Children)
		capVal, capRef := printScoredValue(cand.Children)
		if reqRef != (xml.Name{}) {
			if capRef != (xml.Name{}) && printCanonicalKey(reqRef) == printCanonicalKey(capRef) {
				total += 100.0
			} else if v := paramValues[printCanonicalKey(reqRef)]; v != nil {
				reqVal = v
			} else if domain := n.domains[printCanonicalKey(reqRef)]; domain != nil {
				reqVal = &domain.defaultValue
			}
		}
		if capRef != (xml.Name{}) {
			if reqVal != nil {
				if domain := n.domains[printCanonicalKey(capRef)]; domain != nil {
					if _, err := domain.value(reqVal, n.options); err == nil {
						total += 80.0
					} else if !errors.Is(err, ErrInvalid) {
						return 0, err
					} else {
						capVal = &domain.defaultValue
					}
				}
			}
		}
		if reqVal != nil && capVal != nil {
			same, err := n.valuesEqual(reqVal, capVal)
			if err != nil {
				return 0, err
			}
			if same {
				total += 100.0
			} else if proximity, ok, err := n.numericProximity(reqVal, capVal); err != nil {
				return 0, err
			} else if ok {
				total += proximity
			}
		}
		nested, err := n.scoreScored(setting.Children, cand.Children, paramValues)
		if err != nil {
			return 0, err
		}
		total += nested
	}
	return total, nil
}

// valuesEqual 按基本类型精确比较两个PrintValue是否等价
// 入参: requested 请求值, supported 候选值
// 返回: bool 是否等值, error 预算或取消错误
func (n *printNormalizer) valuesEqual(requested, supported *PrintValue) (bool, error) {
	if err := n.step(); err != nil {
		return false, err
	}
	return printValuesEqual(requested, supported, n.options, true)
}

// numericProximity 计算两个数值PrintValue的接近度加分，越接近分值越高
// 入参: requested 请求值, supported 候选值
// 返回: float64 接近度分值, bool 是否为可比较数值, error 算术预算或取消错误
func (n *printNormalizer) numericProximity(requested, supported *PrintValue) (float64, bool, error) {
	if requested == nil || supported == nil {
		return 0, false, nil
	}
	if (requested.Type.Local != "integer" && requested.Type.Local != "decimal") || (supported.Type.Local != "integer" && supported.Type.Local != "decimal") {
		return 0, false, nil
	}
	left, right := strings.Trim(requested.Text, " \t\r\n"), strings.Trim(supported.Text, " \t\r\n")
	if left == "" || right == "" {
		return 0, false, nil
	}
	a, err := printParameterNumber(left, n.options)
	if err != nil {
		if errors.Is(err, ErrInvalid) {
			return 0, false, nil
		}
		return 0, false, err
	}
	b, err := printParameterNumber(right, n.options)
	if err != nil {
		if errors.Is(err, ErrInvalid) {
			return 0, false, nil
		}
		return 0, false, err
	}
	fa, _ := a.Float64()
	fb, _ := b.Float64()
	if math.IsNaN(fa) || math.IsInf(fa, 0) || math.IsNaN(fb) || math.IsInf(fb, 0) {
		return 0, false, nil
	}
	diff := math.Abs(fa - fb)
	scale := max(math.Abs(fa), math.Abs(fb), 1.0)
	return 50.0 / (1.0 + diff/scale), true, nil
}

// normalizeParameters 按设备ParameterDef校验、补全、裁剪与量化票据中的ParameterInit集合
// 入参: capElements 能力根元素列表, paramInits 票据已有ParameterInit索引, referenced 选定Option引用的参数集合
// 返回: []PrintSetting 规范化后的ParameterInit列表, error 预算或取消错误
func (n *printNormalizer) normalizeParameters(capElements []PrintSetting, paramInits map[xml.Name]PrintSetting, referenced map[xml.Name]bool) ([]PrintSetting, error) {
	var result []PrintSetting
	for _, element := range capElements {
		if element.Kind != PrintSettingParameterDef {
			continue
		}
		if err := checkContext(n.options.context); err != nil {
			return nil, err
		}
		if n.options.Scope != PrintScopeUnknown {
			scope := printKeywordScope(element.Name)
			if scope != PrintScopeUnknown && scope < n.options.Scope {
				continue
			}
		}
		key := printCanonicalKey(element.Name)
		domain := n.domains[key]
		if domain == nil {
			continue
		}
		existing, present := paramInits[key]
		if !present {
			if domain.mandatory == "Unconditional" || referenced[key] {
				defaultCopy := domain.defaultValue
				result = append(result, PrintSetting{
					Kind:     PrintSettingParameterInit,
					Name:     element.Name,
					Children: []PrintSetting{{Kind: PrintSettingValue, Value: &defaultCopy}},
				})
				n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("missing print ParameterInit %s defaulted", element.Name.Local))
			}
			continue
		}
		normalized, err := n.normalizeParameterInit(existing, domain)
		if err != nil {
			return nil, err
		}
		result = append(result, normalized)
	}
	return result, nil
}

// normalizeParameterInit 校验单个ParameterInit，对越界数值裁剪量化、对越界字符串截断或回退默认值
// 入参: existing 票据已有ParameterInit, domain 对应参数域定义
// 返回: PrintSetting 规范化后的ParameterInit, error 算术预算或取消错误
func (n *printNormalizer) normalizeParameterInit(existing PrintSetting, domain *printParameterDomain) (PrintSetting, error) {
	fallback := func(reason string) PrintSetting {
		defaultCopy := domain.defaultValue
		n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s %s", existing.Name.Local, reason))
		return PrintSetting{
			Kind:     PrintSettingParameterInit,
			Name:     existing.Name,
			Children: []PrintSetting{{Kind: PrintSettingValue, Value: &defaultCopy}},
		}
	}
	if len(existing.Children) != 1 || existing.Children[0].Value == nil {
		return fallback("reset to default"), nil
	}
	normalized, adjusted, reason, err := n.normalizeValueForDomain(*existing.Children[0].Value, domain)
	if err != nil {
		return PrintSetting{}, err
	}
	if reason != "" {
		return fallback(reason), nil
	}
	if adjusted {
		if domain.kind.Local == "string" {
			n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s truncated to MaxLength", existing.Name.Local))
		} else {
			n.addDiagnostic("ParameterInit", "name", fmt.Sprintf("print ParameterInit %s clamped or quantized to %s", existing.Name.Local, normalized.Text))
		}
	}
	return PrintSetting{Kind: PrintSettingParameterInit, Name: existing.Name, Children: []PrintSetting{{Kind: PrintSettingValue, Value: &normalized}}}, nil
}

// printFormatDecimalRat 将有限十进制有理数精确格式化为XML Schema十进制词法字符串
// 入参: value 精确有理数, maxDigits 最大允许小数位数上限
// 返回: string 无多余尾随零的十进制字符串
func printFormatDecimalRat(value *big.Rat, maxDigits int) string {
	if value.IsInt() {
		return value.Num().String()
	}
	denom := new(big.Int).Set(value.Denom())
	two, five, zero := big.NewInt(2), big.NewInt(5), big.NewInt(0)
	rem := new(big.Int)
	c2, c5 := 0, 0
	for {
		q, _ := new(big.Int).QuoRem(denom, two, rem)
		if rem.Cmp(zero) != 0 {
			break
		}
		denom = q
		c2++
	}
	for {
		q, _ := new(big.Int).QuoRem(denom, five, rem)
		if rem.Cmp(zero) != 0 {
			break
		}
		denom = q
		c5++
	}
	prec := max(c2, c5)
	if denom.Cmp(big.NewInt(1)) != 0 || prec > maxDigits {
		prec = min(maxDigits, 32)
	}
	text := value.FloatString(prec)
	if strings.Contains(text, ".") {
		text = strings.TrimRight(text, "0")
		text = strings.TrimRight(text, ".")
	}
	return text
}

// printTruncateRunes 按Unicode码点数量截断字符串至指定上限
// 入参: text 原字符串, limit 最大Unicode码点数
// 返回: string 截断后的字符串
func printTruncateRunes(text string, limit int) string {
	if limit <= 0 {
		return ""
	}
	count := 0
	for index := range text {
		if count == limit {
			return text[:index]
		}
		count++
	}
	return text
}

// printCollectParameterRefs 递归收集设置树中全部ParameterRef的规范化名称
// 入参: settings 设置树元素列表, target 输出引用集合
func printCollectParameterRefs(settings []PrintSetting, target map[xml.Name]bool) {
	for _, setting := range settings {
		if setting.Kind == PrintSettingParameterRef {
			target[printCanonicalKey(setting.Name)] = true
			continue
		}
		printCollectParameterRefs(setting.Children, target)
	}
}

// printTicketOptionFromCapability 将能力或候选Option深拷贝为不含能力专属元数据的票据Option
// 入参: option 源Option节点
// 返回: PrintSetting 独立票据Option节点
func printTicketOptionFromCapability(option PrintSetting) PrintSetting {
	result := PrintSetting{Kind: option.Kind, Name: option.Name}
	if option.Value != nil {
		val := *option.Value
		result.Value = &val
	}
	for _, child := range option.Children {
		if child.Kind == PrintSettingProperty && (printFrameworkSpace(child.Name.Space) && (child.Name.Local == "SelectionType" || child.Name.Local == "IdentityOption") || printPublicKeywordSpace(child.Name.Space) && (child.Name.Local == "DisplayName" || child.Name.Local == "DisplayUI") || printSettingHasImageableAreaType(child)) {
			continue
		}
		result.Children = append(result.Children, printTicketOptionFromCapability(child))
	}
	return result
}

// printSettingHasImageableAreaType 检查Property节点或其子节点是否包含psf2:ImageableAreaType值
// 入参: setting 待检查设置节点
// 返回: bool 是否含PSF2可打印区域类型值
func printSettingHasImageableAreaType(setting PrintSetting) bool {
	if setting.Kind == PrintSettingValue && setting.Value != nil && setting.Value.Type == (xml.Name{Space: printFramework2NS, Local: "ImageableAreaType"}) {
		return true
	}
	for _, child := range setting.Children {
		if printSettingHasImageableAreaType(child) {
			return true
		}
	}
	return false
}

// printCloneSetting 深拷贝单个PrintSetting及其全部子元素和值指针
// 入参: setting 源设置节点
// 返回: PrintSetting 独立副本
func printCloneSetting(setting PrintSetting) PrintSetting {
	result := setting
	if setting.Value != nil {
		val := *setting.Value
		result.Value = &val
	}
	if len(setting.Children) > 0 {
		result.Children = make([]PrintSetting, len(setting.Children))
		for index, child := range setting.Children {
			result.Children[index] = printCloneSetting(child)
		}
	}
	return result
}

// printCloneSettings 深拷贝PrintSettings结构及其全部节点树与PDC变更标识
// 入参: src 源打印设置
// 返回: *PrintSettings 独立深拷贝，源为nil时返回nil
func printCloneSettings(src *PrintSettings) *PrintSettings {
	if src == nil {
		return nil
	}
	dst := &PrintSettings{Version: src.Version, CapabilitiesChangeID: src.CapabilitiesChangeID}
	if len(src.Elements) != 0 {
		dst.Elements = make([]PrintSetting, len(src.Elements))
		for index, element := range src.Elements {
			dst.Elements[index] = printCloneSetting(element)
		}
	}
	return dst
}
