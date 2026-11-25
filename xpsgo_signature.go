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
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"encoding/base64"
	"encoding/xml"
	"fmt"
	"hash"
	"io"
	"maps"
	"math/big"
	"mime"
	"net/url"
	"slices"
	"strconv"
	"strings"
	"time"
)

// xmlSignatureNamespace 等常量定义XML数字签名、规范化与算法命名空间及标识
const (
	xmlSignatureNamespace   = "http://www.w3.org/2000/09/xmldsig#"
	xmlSignature11Namespace = "http://www.w3.org/2009/xmldsig11#"
	opcSignatureNamespace   = "http://schemas.openxmlformats.org/package/2006/digital-signature"
	signatureCanonical      = "http://www.w3.org/TR/2001/REC-xml-c14n-20010315"
	signatureComments       = "http://www.w3.org/TR/2001/REC-xml-c14n-20010315#WithComments"
	signatureExcNamespace   = "http://www.w3.org/2001/10/xml-exc-c14n#"
	signatureExcCanonical   = "http://www.w3.org/2001/10/xml-exc-c14n#"
	signatureExcComments    = "http://www.w3.org/2001/10/xml-exc-c14n#WithComments"
	signatureCanonical11    = "http://www.w3.org/2006/12/xml-c14n11"
	signatureComments11     = "http://www.w3.org/2006/12/xml-c14n11#WithComments"
	signatureRelationships  = "http://schemas.openxmlformats.org/package/2006/RelationshipTransform"
	signaturePSSNamespace   = "http://www.w3.org/2007/05/xmldsig-more#"
	signatureMethodMGF1     = "http://www.w3.org/2007/05/xmldsig-more#MGF1"
	signatureMethodRSAPSS   = "http://www.w3.org/2007/05/xmldsig-more#rsa-pss"
	signatureMethodPSS256   = "http://www.w3.org/2007/05/xmldsig-more#sha256-rsa-MGF1"
	signatureMethodPSS384   = "http://www.w3.org/2007/05/xmldsig-more#sha384-rsa-MGF1"
	signatureMethodPSS512   = "http://www.w3.org/2007/05/xmldsig-more#sha512-rsa-MGF1"
	signatureMethodECDSA256 = "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha256"
	signatureMethodECDSA384 = "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha384"
	signatureMethodECDSA512 = "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha512"
)

// opcSignatureOriginType 等常量定义OPC数字签名内容类型与关系
const (
	opcSignatureOriginType = "application/vnd.openxmlformats-package.digital-signature-origin"
	opcSignatureType       = "application/vnd.openxmlformats-package.digital-signature-xmlsignature+xml"
	opcCertificateType     = "application/vnd.openxmlformats-package.digital-signature-certificate"
	opcSignatureOriginRel  = "http://schemas.openxmlformats.org/package/2006/relationships/digital-signature/origin"
	opcSignatureRel        = "http://schemas.openxmlformats.org/package/2006/relationships/digital-signature/signature"
	opcCertificateRel      = "http://schemas.openxmlformats.org/package/2006/relationships/digital-signature/certificate"
)

// signatureCoverageRequiredPart 等常量表示数字签名覆盖检查项类别
const (
	signatureCoverageRequiredPart = iota + 1
	signatureCoverageRequiredRelationship
	signatureCoverageOptionalPart
	signatureCoverageGroup
)

// c14n11URI 保存按RFC3986分解的URI结构组件，不含片段
type c14n11URI struct {
	scheme    string
	hasAuth   bool
	authority string
	path      string
	hasQuery  bool
	query     string
}

// SignatureInfo 保存签名XML中的算法、参数、引用及声明时间，不表示摘要、签名值或证书已经验证
// Certificates保存KeyInfo声明或检索的证书字节，签名XML中的证书优先于独立证书部件
// PublicKeys保存KeyValue解析出的公钥，PSS保存RSA-PSS参数，InclusiveNamespaces保存Exc-C14N前缀列表
type SignatureInfo struct {
	Part                PartInfo
	ID                  string
	Canonicalization    string
	InclusiveNamespaces []string
	Method              string
	PSS                 *SignaturePSSParams
	Value               []byte
	References          []SignatureReference
	Parts               []SignatureReference
	Time                SignatureTime
	Certificates        [][]byte
	PublicKeys          []crypto.PublicKey
}

// SignaturePSSParams 保存RSA-PSS签名方法的摘要、掩码函数、盐长度及尾部字段参数
type SignaturePSSParams struct {
	DigestMethod string
	MGFMethod    string
	MGFDigest    string
	SaltLength   int
	TrailerField int
}

// SignatureReference 保存原始引用及有序变换，Part和ContentType仅用于包部件引用
type SignatureReference struct {
	URI          string
	Type         string
	Part         string
	ContentType  string
	DigestMethod string
	Digest       []byte
	Transforms   []SignatureTransform
}

// SignatureTransform 保存签名变换算法、Exclusive C14N前缀列表及关系筛选条件
type SignatureTransform struct {
	Algorithm           string
	InclusiveNamespaces []string
	RelationshipIDs     []string
	RelationshipTypes   []string
}

// SignatureTime 保存OPC声明的时间格式及原始值，不补全日期精度或换算时区
type SignatureTime struct {
	Format string
	Value  string
}

// signatureXML 保存单次签名解析、证书检索缓存及私有处理预算，不修改原始签名字节
type signatureXML struct {
	context          context.Context
	ids              map[string]*xmlElement
	limits           Limits
	graph            *signaturePartGraph
	source           string
	data             []byte
	root             *xmlElement
	work             int64
	loaded           map[string]*signatureRetrievalPart
	certificateParts map[string]bool
}

// SignatureBinding 保存签署请求标识与签名根元素Id的声明关联，不表示该签名有效
// 一个请求可对应多个签名；Signatures为空表示当前未找到对应签名，不补造关联
type SignatureBinding struct {
	DefinitionPart PartInfo
	ID             string
	Signatures     []PartInfo
}

// SignaturePart 保存签名部件及其关联的独立证书部件，不表示签名或证书已经验证
// 部件名称保留包内大小写，Size为声明的解压字节数；内嵌证书不在Certificates中列出
type SignaturePart struct {
	Part         PartInfo
	Certificates []PartInfo
}

// signaturePartGraph 保存单次签名关联读取的Context及累计解压预算，不修改共享包索引
type signaturePartGraph struct {
	pkg       *packageReader
	context   context.Context
	remaining int64
	maximum   int
	work      func(uint64) error
}

// SignatureCoverage 保存同一签名的部件及关系覆盖差异，不表示密码学验证或证书信任成立
// Complete仅表示覆盖规则满足；不评价MCE扩展理解、打印票据理解或签署者身份
type SignatureCoverage struct {
	Part                    PartInfo
	Complete                bool
	MissingParts            []string
	MissingRelationships    []SignatureRelationship
	UnexpectedParts         []string
	UnexpectedRelationships []SignatureRelationship
	UngroupedSignatures     []SignatureRelationship
}

// SignatureRelationship 标识包内被签署或应被签署的关系，ID仅在Source范围内唯一
type SignatureRelationship struct {
	Source       string
	Relationship Relationship
}

// signatureCoverageKey 按OPC等价来源与关系ID区分关联，不把相同目标当作相同关系
type signatureCoverageKey struct {
	source string
	id     string
}

// signatureCoverageGraph 保存单次覆盖检查的部件角色、关系及私有读取预算
type signatureCoverageGraph struct {
	graph     *signaturePartGraph
	format    Format
	owners    map[string]string
	parts     map[string]bool
	required  map[string]bool
	relations map[signatureCoverageKey]SignatureRelationship
	modes     map[signatureCoverageKey]int
	targets   map[signatureCoverageKey]string
	bySource  map[string][]Relationship
	covered   map[signatureCoverageKey]bool
	ungrouped map[signatureCoverageKey]bool
}

// SignatureNamespace 保存签署内容通过MCE使用的未理解命名空间，不列出仅声明而未使用的前缀
type SignatureNamespace struct {
	Part      string
	Namespace string
}

// signatureNamespaceScan 保存原始XML的理解集合、需要检查的子树及本次取消Context
type signatureNamespaceScan struct {
	known    map[string]bool
	declared map[string]bool
	selected map[*xmlElement]bool
	needed   map[*xmlElement]bool
	unknown  map[string]bool
	context  context.Context
}

// signatureRelationship 保存关系变换筛选与规范化后的关系属性
type signatureRelationship struct {
	id    string
	typ   string
	attrs []xml.Attr
}

// signatureCanonicalOptions 指定C14N1.0、Exclusive C14N1.0或C14N1.1规范化处理方式
type signatureCanonicalOptions struct {
	limits        Limits
	maxBytes      int64
	algorithm     string
	comments      bool
	inclusive     map[string]bool
	context       context.Context
	selectElement func(*xmlElement, []xml.Name) bool
}

// signatureCanonicalWriter 保存Exclusive C14N1.0与C14N1.1规范化输出的流式状态
type signatureCanonicalWriter struct {
	options       signatureCanonicalOptions
	output        packageOutput
	ancestors     []*xmlElement
	path          []xml.Name
	rendered      []map[string]string
	selected      bool
	selectedDepth int
	rootPassed    bool
	nodes         int
}

// ReadSignature 读取已通过签名源关联的XML签名声明，校验OPC结构、引用及声明时间，不执行密码学或信任验证
// 关联与签名读取共用MaxPackageBytes预算，签名XML另受元数据及复杂度上限约束，失败时不返回部分结果
// 入参: ctx 取消Context，nil采用Background, part 签名部件的包根URI
// 返回: *SignatureInfo 独立声明信息，失败无部分结果, error 关联、XML、能力、资源、关闭或取消错误
func (r *Reader) ReadSignature(ctx context.Context, part string) (*SignatureInfo, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	result, _, _, err := r.loadSignature(ctx, part)
	return result, err
}

// loadSignature 在持有阅读器读锁时共用关联读取、原始XML及内容类型检查，返回同一次读取的验证输入
// 入参: ctx 非nil取消Context, part 签名部件的包根URI
// 返回: *SignatureInfo 声明信息, []byte 独立原始XML, *signaturePartGraph 本次读取预算, error 读取或声明错误
func (r *Reader) loadSignature(ctx context.Context, part string) (*SignatureInfo, []byte, *signaturePartGraph, error) {
	name, err := opcPartName(part)
	if err != nil {
		return nil, nil, nil, err
	}
	g := signaturePartGraph{context: ctx, remaining: r.limits.MaxPackageBytes}
	pkg := *r.pkg
	pkg.beforeRead, g.pkg = g.readAllowance, &pkg
	parts, err := g.read()
	if err != nil {
		return nil, nil, nil, err
	}
	var info PartInfo
	for _, candidate := range parts {
		if strings.EqualFold(candidate.Part.Name, name) {
			info = candidate.Part
			break
		}
	}
	if info.Name == "" {
		return nil, nil, nil, fmt.Errorf("%w: part %s is not an associated digital signature", ErrInvalid, name)
	}
	result, data, err := r.loadSignaturePart(info, &g)
	return result, data, &g, err
}

// loadSignaturePart 使用已校验的关联索引读取一份签名，与同次作业的其他签名共用预算
// 入参: info 已关联的签名部件, graph 本次私有读取图
// 返回: *SignatureInfo 声明信息, []byte 原始XML, error 读取、声明、预算或取消错误
func (r *Reader) loadSignaturePart(info PartInfo, graph *signaturePartGraph) (*SignatureInfo, []byte, error) {
	ctx, pkg := graph.context, graph.pkg
	data, err := pkg.readItems(strings.ToLower(info.Name), min(r.limits.MaxPartBytes, r.limits.MaxMetadataBytes))
	if err != nil {
		return nil, nil, &PartError{Part: info.Name, Err: err}
	}
	result, err := readPackageSignatureXML(data, r.limits, ctx, graph, info.Name)
	if err != nil {
		return nil, nil, &PartError{Part: info.Name, Element: "Signature", Err: err}
	}
	for _, reference := range result.Parts {
		if err := ctx.Err(); err != nil {
			return nil, nil, err
		}
		media, err := pkg.contentType(reference.Part)
		if err != nil {
			return nil, nil, err
		}
		if !strings.EqualFold(media, reference.ContentType) {
			return nil, nil, fmt.Errorf("%w: signature content type differs for %s", ErrInvalid, reference.Part)
		}
	}
	result.Part = info
	if err := ctx.Err(); err != nil {
		return nil, nil, err
	}
	return result, data, nil
}

// readSignatureXML 解析OPC签名声明，按展开名称和模式ID绑定引用，不从任意Id属性猜测标识
// 入参: data 原始XML字节, limits XML上限, ctx 取消Context
// 返回: *SignatureInfo 独立声明信息, error XML、结构、能力、资源或取消错误
func readSignatureXML(data []byte, limits Limits, ctx context.Context) (*SignatureInfo, error) {
	return readPackageSignatureXML(data, limits, ctx, nil, "")
}

// readPackageSignatureXML 解析签名声明，使用本次包读取预算处理KeyInfo的包内引用
// 入参: data 原始签名XML, limits 处理上限, ctx 取消Context, graph 可选包读取状态, source 签名部件URI
// 返回: *SignatureInfo 独立声明信息, error 结构、引用、能力、预算或取消错误
func readPackageSignatureXML(data []byte, limits Limits, ctx context.Context, graph *signaturePartGraph, source string) (*SignatureInfo, error) {
	limits = mergeLimits(DefaultLimits(), limits)
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	if int64(len(data)) > min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: signature XML bytes", ErrLimit)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	p := signatureXML{context: ctx, ids: make(map[string]*xmlElement), limits: limits, graph: graph, source: source, data: data, work: limits.MaxPackageBytes}
	root, err := decodeXMLVisit(data, limits, func(xml.Token, *xmlElement) error { return checkContext(ctx) })
	if err != nil {
		return nil, err
	}
	if root.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Signature"}) || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: XML signature root", ErrInvalid)
	}
	attrs, err := signatureAttributes(root, "Id")
	if err != nil {
		return nil, err
	}
	if err := p.identifiers(root); err != nil {
		return nil, err
	}
	p.root = root
	result := &SignatureInfo{ID: strings.Trim(attrs["Id"], " \t\r\n")}
	if len(root.Children) < 3 || root.Children[0].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "SignedInfo"}) || root.Children[1].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "SignatureValue"}) {
		return nil, fmt.Errorf("%w: XML signature child order", ErrInvalid)
	}
	value := root.Children[1]
	if _, err := signatureAttributes(value, "Id"); err != nil {
		return nil, err
	}
	result.Value, err = signatureBinary(value)
	if err != nil {
		return nil, err
	}
	index := 2
	if root.Children[index].Name == (xml.Name{Space: xmlSignatureNamespace, Local: "KeyInfo"}) {
		result.Certificates, result.PublicKeys, err = p.certificates(root.Children[index])
		if err != nil {
			return nil, err
		}
		index++
	}
	var object *xmlElement
	for _, node := range root.Children[index:] {
		if node.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Object"}) {
			return nil, fmt.Errorf("%w: unexpected XML signature child", ErrInvalid)
		}
		attrs, err := signatureAttributes(node, "Id", "MimeType", "Encoding")
		if err != nil {
			return nil, err
		}
		if !uriReference(strings.Trim(attrs["Encoding"], " \t\r\n")) {
			return nil, fmt.Errorf("%w: signature object encoding URI", ErrInvalid)
		}
		if strings.Trim(attrs["Id"], " \t\r\n") == "idPackageObject" {
			if object != nil {
				return nil, fmt.Errorf("%w: multiple package signature objects", ErrInvalid)
			}
			object = node
		}
	}
	if object == nil {
		return nil, fmt.Errorf("%w: missing package signature object", ErrInvalid)
	}
	if err := p.packageObject(object, result); err != nil {
		return nil, err
	}
	if err := p.signedInfo(root.Children[0], result); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// identifiers 收集XML签名模式中的ID及xml:id，拒绝重复标识，不把外部模式的普通Id当作ID
// 入参: root 签名根元素
// 返回: error 标识或取消错误
func (p *signatureXML) identifiers(root *xmlElement) error {
	stack := []*xmlElement{root}
	for len(stack) != 0 {
		if err := checkContext(p.context); err != nil {
			return err
		}
		node := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		stack = append(stack, node.Children...)
		for _, attr := range node.Attr {
			if !signatureIDAttribute(node, attr) {
				continue
			}
			id := strings.Trim(attr.Value, " \t\r\n")
			if !xmlNCName(id) || p.ids[id] != nil {
				return fmt.Errorf("%w: invalid or duplicate signature ID", ErrInvalid)
			}
			p.ids[id] = node
		}
	}
	return nil
}

// signatureIDAttribute 判断XML签名模式中的ID或xml:id，不通过属性局部名称猜测模式类型
// 入参: node 属性所属元素, attr 已展开命名空间的属性
// 返回: bool 是否为已识别的ID属性
func signatureIDAttribute(node *xmlElement, attr xml.Attr) bool {
	if attr.Name == (xml.Name{Space: xmlNamespace, Local: "id"}) {
		return true
	}
	if attr.Name == (xml.Name{Local: "Id"}) && node.Name.Space == xmlSignatureNamespace {
		switch node.Name.Local {
		case "Signature", "SignedInfo", "SignatureValue", "KeyInfo", "Object", "Reference", "Manifest", "SignatureProperties", "SignatureProperty":
			return true
		}
	}
	return false
}

// signatureAttributes 检查XML签名元素的无命名空间属性并忽略命名空间声明
// 入参: node 元素, allowed 允许的属性名称
// 返回: map[string]string 属性值, error 属性错误
func signatureAttributes(node *xmlElement, allowed ...string) (map[string]string, error) {
	attrs := make(map[string]string)
	for _, attr := range node.Attr {
		if attr.Name.Space == xmlnsNamespace || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if attr.Name.Space != "" {
			return nil, fmt.Errorf("%w: namespaced signature attribute %s", ErrInvalid, attr.Name.Local)
		}
		attrs[attr.Name.Local] = attr.Value
	}
	if err := opcAttributes(attrs, allowed...); err != nil {
		return nil, err
	}
	return attrs, nil
}

// SignatureBindings 按SpotID与Signature.Id规则读取固定文档签署请求与签名的声明关联，不执行密码学或覆盖验证
// 全部请求、签名与关系读取共用本次MaxPackageBytes预算，失败时不返回部分结果
// 入参: ctx 取消Context，nil采用Background
// 返回: []SignatureBinding 独立声明关联，失败无部分结果, error 关联、XML、能力、资源、关闭或取消错误
func (r *Reader) SignatureBindings(ctx context.Context) ([]SignatureBinding, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	g := signaturePartGraph{context: ctx, remaining: r.limits.MaxPackageBytes}
	pkg := *r.pkg
	pkg.beforeRead, g.pkg = g.readAllowance, &pkg
	requests, err := g.definitions(r.documents, r.format, r.limits)
	if err != nil {
		return nil, err
	}
	if len(requests) == 0 {
		return nil, ctx.Err()
	}
	byID := make(map[string][]PartInfo)
	for _, part := range requests {
		for _, definition := range part.Definitions {
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			byID[definition.ID] = nil
		}
	}
	parts, err := g.read()
	if err != nil {
		return nil, err
	}
	for _, part := range parts {
		data, err := pkg.readItems(strings.ToLower(part.Part.Name), min(r.limits.MaxPartBytes, r.limits.MaxMetadataBytes))
		if err != nil {
			return nil, &PartError{Part: part.Part.Name, Err: err}
		}
		info, err := readPackageSignatureXML(data, r.limits, ctx, &g, part.Part.Name)
		if err != nil {
			return nil, &PartError{Part: part.Part.Name, Element: "Signature", Err: err}
		}
		if _, requested := byID[info.ID]; requested {
			byID[info.ID] = append(byID[info.ID], part.Part)
		}
	}
	var result []SignatureBinding
	for _, part := range requests {
		for _, definition := range part.Definitions {
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			result = append(result, SignatureBinding{DefinitionPart: part.Part, ID: definition.ID, Signatures: slices.Clone(byID[definition.ID])})
		}
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return result, nil
}

// signatureHashPart 分块读取原始逻辑部件并验证每个ZIP分片的尺寸及CRC，不复制完整部件
// 入参: ctx 取消Context, pkg 本次验证的包读取器, name 规范部件名称, h 标准摘要器
// 返回: error 读取、解压、尺寸、预算或取消错误
func signatureHashPart(ctx context.Context, pkg *packageReader, name string, h hash.Hash) error {
	key := strings.ToLower(name)
	size, err := pkg.partSize(key)
	if err != nil {
		return err
	}
	limit := min(pkg.limits.MaxPartBytes, pkg.limits.MaxPackageBytes)
	if opcRelationshipName(name) {
		limit = min(limit, pkg.limits.MaxMetadataBytes)
	}
	if pkg.beforeRead != nil {
		allowed, err := pkg.beforeRead(key, size, limit)
		if err != nil {
			return err
		}
		if allowed < 0 {
			return fmt.Errorf("%w: signature part read allowance", ErrLimit)
		}
		limit = min(limit, allowed)
	}
	if size > uint64(limit) {
		return fmt.Errorf("%w: signature raw part bytes", ErrLimit)
	}
	if data, present := pkg.data[key]; present {
		return signatureHashBytes(ctx, h, data)
	}
	buffer := make([]byte, 32<<10)
	for _, file := range pkg.parts[key] {
		if err := checkContext(ctx); err != nil {
			return err
		}
		reader, err := file.Open()
		if err != nil {
			return &packageReadError{err: fmt.Errorf("%w: signature part %s: %w", ErrInvalid, name, err)}
		}
		count := uint64(0)
		for {
			if err := checkContext(ctx); err != nil {
				_ = reader.Close()
				return err
			}
			n, readErr := reader.Read(buffer)
			if uint64(n) > file.UncompressedSize64-count {
				_ = reader.Close()
				return &packageReadError{err: fmt.Errorf("%w: signature part %s exceeds declared size", ErrInvalid, name)}
			}
			count += uint64(n)
			if _, err := h.Write(buffer[:n]); err != nil {
				_ = reader.Close()
				return err
			}
			if readErr != nil {
				closeErr := reader.Close()
				if readErr != io.EOF {
					return &packageReadError{err: fmt.Errorf("%w: signature part %s: %w", ErrInvalid, name, readErr)}
				}
				if closeErr != nil {
					return &packageReadError{err: fmt.Errorf("%w: signature part %s: %w", ErrInvalid, name, closeErr)}
				}
				if count != file.UncompressedSize64 {
					return &packageReadError{err: fmt.Errorf("%w: signature part %s size or close", ErrInvalid, name)}
				}
				break
			}
			if n == 0 {
				_ = reader.Close()
				return &packageReadError{err: fmt.Errorf("%w: signature part %s: %w", ErrInvalid, name, io.ErrNoProgress)}
			}
		}
	}
	return checkContext(ctx)
}

// SignatureParts 按OPC关系读取签名及独立证书部件索引，校验签名源唯一性与目标类型，不读取载荷或执行验证
// 关系读取共用MaxPackageBytes预算，结果按部件URI排序并合并重复关系，失败时不返回部分结果
// 入参: ctx 取消Context，nil采用Background
// 返回: []SignaturePart 独立索引，无签名时为空，失败时不返回部分结果, error 结构、资源、关闭或取消错误
func (r *Reader) SignatureParts(ctx context.Context) ([]SignaturePart, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	g := signaturePartGraph{context: ctx, remaining: r.limits.MaxPackageBytes}
	pkg := *r.pkg
	pkg.beforeRead = g.readAllowance
	g.pkg = &pkg
	return g.read()
}

// read 校验签名源及所有声明签名的关联，证书部件可以共享或不随包提供
// 返回: []SignaturePart 独立签名部件索引, error 结构、资源或取消错误
func (g *signaturePartGraph) read() ([]SignaturePart, error) {
	keys := make([]string, 0)
	origin := ""
	for key := range g.pkg.parts {
		if err := g.context.Err(); err != nil {
			return nil, err
		}
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := g.pkg.contentType(key)
		if err != nil {
			return nil, err
		}
		switch {
		case strings.EqualFold(media, opcSignatureOriginType):
			if origin != "" {
				return nil, fmt.Errorf("%w: multiple digital signature origin parts", ErrInvalid)
			}
			origin = g.pkg.names[key]
		case strings.EqualFold(media, opcSignatureType):
			if g.maximum > 0 && len(keys) >= g.maximum {
				return nil, fmt.Errorf("%w: signature count", ErrLimit)
			}
			keys = append(keys, key)
		}
	}
	relationships, err := g.pkg.relationships("/")
	if err != nil {
		return nil, err
	}
	rooted := false
	for _, relationship := range relationships {
		if err := g.context.Err(); err != nil {
			return nil, err
		}
		if relationship.Type != opcSignatureOriginRel {
			continue
		}
		if rooted {
			return nil, fmt.Errorf("%w: multiple digital signature origin relationships", ErrInvalid)
		}
		part, err := g.target("/", relationship, opcSignatureOriginType)
		if err != nil {
			return nil, err
		}
		if part.Name != origin {
			return nil, fmt.Errorf("%w: unbound digital signature origin", ErrInvalid)
		}
		rooted = true
	}
	if origin == "" {
		if len(keys) != 0 {
			return nil, fmt.Errorf("%w: digital signatures without an origin part", ErrInvalid)
		}
		return nil, g.context.Err()
	}
	if !rooted {
		return nil, fmt.Errorf("%w: digital signature origin is not targeted from package root", ErrInvalid)
	}
	relationships, err = g.pkg.relationships(origin)
	if err != nil {
		return nil, err
	}
	linked := make(map[string]PartInfo, len(keys))
	for _, relationship := range relationships {
		if err := g.context.Err(); err != nil {
			return nil, err
		}
		if relationship.Type != opcSignatureRel {
			continue
		}
		part, err := g.target(origin, relationship, opcSignatureType)
		if err != nil {
			return nil, err
		}
		linked[strings.ToLower(part.Name)] = part
	}
	slices.Sort(keys)
	result := make([]SignaturePart, 0, len(keys))
	for _, key := range keys {
		if err := g.context.Err(); err != nil {
			return nil, err
		}
		part, present := linked[key]
		if !present {
			return nil, fmt.Errorf("%w: signature part %s is not targeted from its origin", ErrInvalid, g.pkg.names[key])
		}
		certificates, err := g.certificates(part.Name)
		if err != nil {
			return nil, err
		}
		result = append(result, SignaturePart{Part: part, Certificates: certificates})
	}
	if err := g.context.Err(); err != nil {
		return nil, err
	}
	return result, nil
}

// certificates 读取签名关联的证书部件索引，保留多证书关联并合并同一部件的重复关系
// 入参: source 签名部件名称
// 返回: []PartInfo 独立证书索引, error 结构、资源或取消错误
func (g *signaturePartGraph) certificates(source string) ([]PartInfo, error) {
	relationships, err := g.pkg.relationships(source)
	if err != nil {
		return nil, err
	}
	parts := make(map[string]PartInfo)
	for _, relationship := range relationships {
		if err := g.context.Err(); err != nil {
			return nil, err
		}
		if relationship.Type != opcCertificateRel {
			continue
		}
		part, err := g.target(source, relationship, opcCertificateType)
		if err != nil {
			return nil, err
		}
		parts[strings.ToLower(part.Name)] = part
	}
	keys := slices.Sorted(maps.Keys(parts))
	result := make([]PartInfo, 0, len(keys))
	for _, key := range keys {
		result = append(result, parts[key])
	}
	return result, nil
}

// target 解析包内关联并检查目标存在及内容类型，不读取目标载荷或访问外部位置
// 入参: source 源部件名称或包根, relationship 待解析关系, media 所需内容类型，空值不限定
// 返回: PartInfo 包内目标索引, error 目标、类型或取消错误
func (g *signaturePartGraph) target(source string, relationship Relationship, media string) (PartInfo, error) {
	if err := g.context.Err(); err != nil {
		return PartInfo{}, err
	}
	if relationship.TargetMode != TargetModeInternal {
		return PartInfo{}, fmt.Errorf("%w: external digital signature relationship %s", ErrInvalid, relationship.ID)
	}
	name, err := resolvePart(source, relationship.Target)
	if err != nil {
		return PartInfo{}, err
	}
	typ, err := g.pkg.contentType(name)
	if err != nil {
		return PartInfo{}, err
	}
	if media != "" && !strings.EqualFold(typ, media) {
		return PartInfo{}, fmt.Errorf("%w: digital signature relationship %s targets content type %s", ErrInvalid, relationship.ID, typ)
	}
	key := strings.ToLower(name)
	size, err := g.pkg.partSize(key)
	if err != nil {
		return PartInfo{}, err
	}
	return PartInfo{Name: g.pkg.names[key], ContentType: typ, Size: int64(size)}, nil
}

// readAllowance 在解压关系部件前检查取消及累计字节预算，限制实际读取不超过声明尺寸
// 入参: key 逻辑部件键, size 声明解压字节数, limit 单次读取上限
// 返回: int64 收紧后的读取上限, error 取消或预算错误
func (g *signaturePartGraph) readAllowance(key string, size uint64, limit int64) (int64, error) {
	if err := g.context.Err(); err != nil {
		return 0, err
	}
	if size > uint64(g.remaining) {
		return 0, fmt.Errorf("%w: signature relationship part %s exceeds byte budget", ErrLimit, key)
	}
	if g.work != nil {
		if err := g.work(size); err != nil {
			return 0, err
		}
	}
	g.remaining -= int64(size)
	return min(limit, int64(size)), nil
}

// SignatureCoverage 检查单个签名声明是否覆盖当前文档要求的全部部件与关系，不合并多签名或执行密码学验证
// 按当前方言规则处理缩略图，关系筛选保留原始OPC词元与大小写
// 入参: ctx 取消Context，nil采用Background, part 已关联签名部件的包根URI
// 返回: *SignatureCoverage 独立覆盖差异，结构或能力错误时为空, error 读取、结构、资源、关闭或取消错误
func (r *Reader) SignatureCoverage(ctx context.Context, part string) (*SignatureCoverage, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	info, _, graph, err := r.loadSignature(ctx, part)
	if err != nil {
		return nil, err
	}
	return r.signatureCoverage(info, graph)
}

// signatureCoverage 在调用方持有读锁时复用已加载的签名与累计读取预算
// 入参: info 同次读取的签名声明, graph 私有部件图
// 返回: *SignatureCoverage 独立覆盖差异, error 结构、资源或取消错误
func (r *Reader) signatureCoverage(info *SignatureInfo, graph *signaturePartGraph) (*SignatureCoverage, error) {
	ctx := graph.context
	c := signatureCoverageGraph{
		graph: graph, format: r.format, owners: make(map[string]string), parts: make(map[string]bool), required: make(map[string]bool),
		relations: make(map[signatureCoverageKey]SignatureRelationship), modes: make(map[signatureCoverageKey]int), targets: make(map[signatureCoverageKey]string),
		bySource: make(map[string][]Relationship), covered: make(map[signatureCoverageKey]bool), ungrouped: make(map[signatureCoverageKey]bool),
	}
	if err := c.collect(r, info.Part.Name); err != nil {
		return nil, err
	}
	result := &SignatureCoverage{Part: info.Part}
	signed := make(map[string]bool)
	unexpected := make(map[string]bool)
	for _, reference := range info.Parts {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		key := strings.ToLower(reference.Part)
		if opcRelationshipName(key) {
			if err := c.selectRelationships(reference); err != nil {
				return nil, &PartError{Part: reference.Part, Err: err}
			}
			continue
		}
		signed[key] = true
		if !c.parts[key] && !unexpected[key] {
			unexpected[key] = true
			result.UnexpectedParts = append(result.UnexpectedParts, graph.pkg.names[key])
		}
	}
	for key := range c.required {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		if !signed[key] {
			result.MissingParts = append(result.MissingParts, graph.pkg.names[key])
		}
	}
	for key, relationship := range c.relations {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		mode := c.modes[key]
		if (mode == signatureCoverageRequiredPart || mode == signatureCoverageRequiredRelationship || mode == signatureCoverageOptionalPart && signed[c.targets[key]]) && !c.covered[key] {
			result.MissingRelationships = append(result.MissingRelationships, relationship)
		}
		if c.covered[key] && mode == 0 {
			result.UnexpectedRelationships = append(result.UnexpectedRelationships, relationship)
		}
		if c.ungrouped[key] {
			result.UngroupedSignatures = append(result.UngroupedSignatures, relationship)
		}
	}
	slices.Sort(result.MissingParts)
	slices.Sort(result.UnexpectedParts)
	for _, relationships := range [][]SignatureRelationship{result.MissingRelationships, result.UnexpectedRelationships, result.UngroupedSignatures} {
		slices.SortFunc(relationships, func(a, b SignatureRelationship) int {
			if order := strings.Compare(a.Source, b.Source); order != 0 {
				return order
			}
			return strings.Compare(a.Relationship.ID, b.Relationship.ID)
		})
	}
	result.Complete = len(result.MissingParts)+len(result.MissingRelationships)+len(result.UnexpectedParts)+len(result.UnexpectedRelationships)+len(result.UngroupedSignatures) == 0
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return result, nil
}

// collect 按当前固定布局与有效关系建立签名覆盖规则与可选部件集合，支持会签其他已关联签名并排除自身及孤立部件
// 入参: reader 已持有读锁的阅读器, selfPart 当前检查或签署的签名部件URI
// 返回: error 关联、目标、资源或取消错误
func (c *signatureCoverageGraph) collect(reader *Reader, selfPart string) error {
	selfKey := strings.ToLower(selfPart)
	c.owners["/"] = "root"
	c.owners[strings.ToLower(reader.sequence)] = "sequence"
	c.parts[strings.ToLower(reader.sequence)], c.required[strings.ToLower(reader.sequence)] = true, true
	for _, document := range reader.documents {
		key := strings.ToLower(document.Part)
		c.owners[key], c.parts[key], c.required[key] = "document", true, true
		for _, page := range document.Pages {
			key := strings.ToLower(page.Part)
			c.owners[key], c.parts[key], c.required[key] = "page", true, true
		}
	}
	rootRelations, err := c.graph.pkg.relationships("/")
	if err != nil {
		return err
	}
	c.bySource["/"] = rootRelations
	origin := ""
	for _, relationship := range rootRelations {
		if err := c.graph.context.Err(); err != nil {
			return err
		}
		if relationship.Type != opcSignatureOriginRel {
			continue
		}
		if origin != "" {
			return &PartError{Part: "/", Err: fmt.Errorf("%w: multiple digital signature origin relationships", ErrInvalid)}
		}
		target, err := c.graph.target("/", relationship, opcSignatureOriginType)
		if err != nil {
			return &PartError{Part: "/", Err: err}
		}
		origin = target.Name
		c.owners[strings.ToLower(origin)] = "origin"
	}
	if origin != "" {
		originRelations, err := c.graph.pkg.relationships(origin)
		if err != nil {
			return err
		}
		c.bySource[strings.ToLower(origin)] = originRelations
		for _, relationship := range originRelations {
			if err := c.graph.context.Err(); err != nil {
				return err
			}
			if relationship.Type != opcSignatureRel {
				continue
			}
			target, err := c.graph.target(origin, relationship, opcSignatureType)
			if err != nil {
				return &PartError{Part: origin, Err: err}
			}
			targetKey := strings.ToLower(target.Name)
			c.owners[targetKey] = "signature"
			if targetKey != selfKey {
				c.parts[targetKey] = true
			}
		}
	}
	keys := slices.Sorted(maps.Keys(c.graph.pkg.parts))
	for _, key := range keys {
		if err := c.graph.context.Err(); err != nil {
			return err
		}
		if !opcRelationshipName(key) {
			continue
		}
		source := relationshipSource(c.graph.pkg.names[key])
		sourceKey := strings.ToLower(source)
		relations, cached := c.bySource[sourceKey]
		if !cached {
			var err error
			relations, err = c.graph.pkg.relationships(source)
			if err != nil {
				return err
			}
			c.bySource[sourceKey] = relations
		}
		for _, relationship := range relations {
			if err := c.graph.context.Err(); err != nil {
				return err
			}
			if len(c.relations) >= reader.limits.MaxXMLNodes {
				return fmt.Errorf("%w: signature coverage relationship count", ErrLimit)
			}
			id := signatureCoverageKey{sourceKey, relationship.ID}
			c.relations[id] = SignatureRelationship{Source: source, Relationship: relationship}
			mode, media := c.rule(c.owners[id.source], relationship.Type)
			c.modes[id] = mode
			if mode == 0 {
				continue
			}
			target, err := c.graph.target(source, relationship, media)
			if err != nil {
				return &PartError{Part: source, Err: err}
			}
			if relationship.Type == thumbnailRelationship && !thumbnailMedia(target.ContentType) {
				return &PartError{Part: target.Name, Err: fmt.Errorf("%w: signature thumbnail content type", ErrInvalid)}
			}
			c.targets[id] = strings.ToLower(target.Name)
			if mode == signatureCoverageRequiredPart || mode == signatureCoverageOptionalPart {
				c.parts[c.targets[id]] = true
			}
			if mode == signatureCoverageRequiredPart {
				c.required[c.targets[id]] = true
			}
		}
	}
	return c.graph.context.Err()
}

// rule 按双格式正文区分必需覆盖、条件覆盖及仅可按组签署的关系
// 入参: owner 来源在固定布局中的角色, typ 关系类型
// 返回: int 覆盖规则，零表示不在许可集合, string 指定目标内容类型，空值表示不限定
func (c *signatureCoverageGraph) rule(owner, typ string) (int, string) {
	namespace := formatNamespace(c.format)
	switch {
	case owner == "root" && typ == namespace+"/fixedrepresentation":
		return signatureCoverageRequiredPart, fixedContentType("fixeddocumentsequence")
	case owner == "document" && typ == namespace+"/documentstructure":
		return signatureCoverageRequiredPart, fixedContentType("documentstructure")
	case owner == "document" && typ == namespace+"/signature-definitions":
		return signatureCoverageRequiredPart, fixedContentType("signaturedefinitions")
	case owner == "page" && typ == namespace+"/storyfragments":
		return signatureCoverageRequiredPart, fixedContentType("storyfragments")
	case owner == "page" && typ == namespace+"/required-resource":
		return signatureCoverageRequiredPart, ""
	case owner == "document" && typ == namespace+"/restricted-font":
		return signatureCoverageRequiredRelationship, ""
	case (owner == "root" || owner == "document" || owner == "page") && typ == thumbnailRelationship:
		return signatureCoverageRequiredPart, ""
	case owner == "root" && typ == opcCoreRel:
		return signatureCoverageOptionalPart, opcCoreType
	case owner == "root" && typ == opcSignatureOriginRel:
		return signatureCoverageOptionalPart, opcSignatureOriginType
	case owner == "signature" && typ == opcCertificateRel:
		return signatureCoverageOptionalPart, opcCertificateType
	case owner == "root" && typ == namespace+"/discard-control":
		return signatureCoverageOptionalPart, fixedContentType("discard-control")
	case (owner == "sequence" || owner == "document" || owner == "page") && typ == namespace+"/printticket":
		if c.format == FormatXPS {
			return signatureCoverageOptionalPart, printTicketType
		}
		return signatureCoverageOptionalPart, ""
	case owner == "origin" && typ == opcSignatureRel:
		return signatureCoverageGroup, opcSignatureType
	}
	return 0, ""
}

// selectRelationships 依据原始词元执行关系筛选，整部件签署覆盖所有现有关系并保护追加关系
// 入参: reference 关系部件的签署声明
// 返回: error 变换、XML、资源或取消错误
func (c *signatureCoverageGraph) selectRelationships(reference SignatureReference) error {
	source := strings.ToLower(relationshipSource(reference.Part))
	var selection *SignatureTransform
	for _, transform := range reference.Transforms {
		if transform.Algorithm == signatureRelationships {
			selection = &transform
			break
		}
	}
	if selection == nil {
		for _, relationship := range c.bySource[source] {
			c.covered[signatureCoverageKey{source, relationship.ID}] = true
		}
		return c.graph.context.Err()
	}
	data, err := c.graph.pkg.readItems(strings.ToLower(reference.Part), min(c.graph.pkg.limits.MaxMetadataBytes, c.graph.pkg.limits.MaxPartBytes))
	if err != nil {
		return err
	}
	data, err = signatureRelationshipXML(data, *selection, c.graph.pkg.limits, c.graph.context)
	if err != nil {
		return err
	}
	grouped := slices.Contains(selection.RelationshipTypes, opcSignatureRel)
	return opcMetadataContext(c.graph.context, data, c.graph.pkg.limits, opcRelsNS, "Relationships", func(element xml.StartElement, attrs map[string]string) error {
		if err := c.graph.context.Err(); err != nil {
			return err
		}
		key := signatureCoverageKey{source, strings.Trim(attrs["Id"], " \t\r\n")}
		if _, exists := c.relations[key]; !exists {
			return fmt.Errorf("%w: selected relationship is not in package graph", ErrInvalid)
		}
		c.covered[key] = true
		if c.modes[key] == signatureCoverageGroup && !grouped {
			c.ungrouped[key] = true
		}
		return nil
	})
}

// signatureIsMetadataPart 判断签署部件是否属于受元数据字节上限约束的元数据XML
// 入参: part 部件路径, media 无参数内容类型
// 返回: bool 是否为元数据部件
func signatureIsMetadataPart(part, media string) bool {
	if opcRelationshipName(part) || strings.EqualFold(part, opcTypesName) || strings.EqualFold(media, opcRelsType) || strings.EqualFold(media, opcCoreType) || strings.EqualFold(media, opcSignatureType) {
		return true
	}
	if strings.EqualFold(media, fixedContentType("signaturedefinitions")) || strings.EqualFold(media, fixedContentType("discard-control")) {
		return true
	}
	known, _ := printResourceMedia(media)
	return known
}

// signaturePartByteLimit 按部件类别返回元数据或正文XML部件的字节上限，避免大页面被元数据限额拦截
// 入参: part 部件路径, media 无参数内容类型, limits 资源上限
// 返回: int64 部件允许的最大字节数
func signaturePartByteLimit(part, media string, limits Limits) int64 {
	limit := min(limits.MaxPartBytes, limits.MaxPackageBytes)
	if signatureIsMetadataPart(part, media) {
		return min(limit, limits.MaxMetadataBytes)
	}
	return limit
}

// signatureNamespaces 扫描签署XML与签名对象的全部MCE分支并收集未理解命名空间
// 入参: info 同次签名声明, data 原始签名XML, graph 私有读取预算, format 方言, namespaces 调用方确实理解的扩展URI
// 返回: []SignatureNamespace 独立命名空间证据, error XML、MCE、预算或取消错误
func signatureNamespaces(info *SignatureInfo, data []byte, graph *signaturePartGraph, format Format, namespaces []string) ([]SignatureNamespace, error) {
	var result []SignatureNamespace
	inspect := func(part, media string, data []byte, ids map[string]bool) error {
		known := signatureKnownNamespaces(media, format)
		for _, namespace := range namespaces {
			if err := checkContext(graph.context); err != nil {
				return err
			}
			if graph.work != nil {
				if err := graph.work(uint64(len(namespace)) + 1); err != nil {
					return &PartError{Part: part, Err: err}
				}
			}
			known[namespace] = true
		}
		limit := signaturePartByteLimit(part, media, graph.pkg.limits)
		unknown, err := scanSignatureNamespaces(data, ids, known, graph.pkg.limits, limit, graph.context)
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
		for _, namespace := range unknown {
			if len(result) >= graph.pkg.limits.MaxXMLNodes {
				return fmt.Errorf("%w: signature namespace evidence count", ErrLimit)
			}
			result = append(result, SignatureNamespace{Part: part, Namespace: namespace})
		}
		return nil
	}
	ids := make(map[string]bool)
	for _, reference := range info.References {
		id, err := signatureReferenceID(reference.URI)
		if err != nil {
			return nil, err
		}
		ids[id] = true
	}
	if err := inspect(info.Part.Name, opcSignatureType, data, ids); err != nil {
		return nil, err
	}
	seen := make(map[string]bool)
	for _, reference := range info.Parts {
		if err := graph.context.Err(); err != nil {
			return nil, err
		}
		key := strings.ToLower(reference.Part)
		if seen[key] {
			continue
		}
		seen[key] = true
		media, _, err := mime.ParseMediaType(reference.ContentType)
		if err != nil {
			return nil, fmt.Errorf("%w: signed XML media type: %w", ErrInvalid, err)
		}
		if !compositionXML(media) {
			continue
		}
		data, err := graph.pkg.readItems(key, signaturePartByteLimit(reference.Part, media, graph.pkg.limits))
		if err != nil {
			return nil, &PartError{Part: reference.Part, Err: err}
		}
		if err := inspect(graph.pkg.names[key], media, data, nil); err != nil {
			return nil, err
		}
	}
	slices.SortFunc(result, func(a, b SignatureNamespace) int {
		if order := strings.Compare(a.Part, b.Part); order != 0 {
			return order
		}
		return strings.Compare(a.Namespace, b.Namespace)
	})
	if err := graph.context.Err(); err != nil {
		return nil, err
	}
	return result, nil
}

// signatureKnownNamespaces 按XML部件的用途声明本库实现的命名空间，不把任意声明当作已经理解
// 入参: media 无参数内容类型, format 文档方言
// 返回: map[string]bool 本次检查专用集合
func signatureKnownNamespaces(media string, format Format) map[string]bool {
	known := map[string]bool{"": true, xmlNamespace: true, mcNamespace: true}
	if knownPrint, capabilities := printResourceMedia(media); knownPrint && !capabilities {
		for _, namespace := range []string{printFrameworkNS, printKeywordsNS, printValueNS, xsiNamespace} {
			known[namespace] = true
		}
		if strings.EqualFold(media, printTicket2Type) {
			for _, namespace := range []string{printFramework2NS, printKeywordsV11NS, printKeywordsV12NS, printKeywords2NS} {
				known[namespace] = true
			}
		}
		return known
	}
	switch strings.ToLower(media) {
	case opcRelsType:
		known[opcRelsNS] = true
	case opcSignatureType:
		for _, namespace := range []string{xmlSignatureNamespace, xmlSignature11Namespace, opcSignatureNamespace, signatureExcNamespace, signaturePSSNamespace} {
			known[namespace] = true
		}
	case opcCoreType:
		for _, namespace := range []string{opcCoreNS, dcNamespace, dcTermsNS, xsiNamespace} {
			known[namespace] = true
		}
	case fixedContentType("signaturedefinitions"):
		known[formatNamespace(format)+"/signature-definitions"] = true
	case fixedContentType("documentstructure"), fixedContentType("storyfragments"):
		known[structureNamespace(format)] = true
	case fixedContentType("discard-control"):
		known[formatNamespace(format)+"/discard-control"] = true
	case fixedContentType("fixedpage"), fixedContentType("fixeddocument"), fixedContentType("fixeddocumentsequence"), resourceDictionaryContentType:
		known[formatNamespace(format)], known[formatNamespace(format)+"/resourcedictionary-key"] = true, true
	}
	return known
}

// scanSignatureNamespaces 按指定字节上限读取原始树并扫描选定子树的未理解命名空间
// 入参: data 原始XML, ids 签名对象ID集合，nil表示整个部件, known 理解集合, limits XML上限, maxBytes 允许字节上限, ctx 取消Context
// 返回: []string 未理解且影响签署内容的URI, error XML、MCE或取消错误
func scanSignatureNamespaces(data []byte, ids map[string]bool, known map[string]bool, limits Limits, maxBytes int64, ctx context.Context) ([]string, error) {
	if int64(len(data)) > maxBytes {
		return nil, fmt.Errorf("%w: signed XML namespace inspection bytes", ErrLimit)
	}
	p := signatureNamespaceScan{known: known, declared: map[string]bool{mcNamespace: true, xmlNamespace: true}, selected: make(map[*xmlElement]bool), needed: make(map[*xmlElement]bool), unknown: make(map[string]bool), context: ctx}
	root, err := decodeXMLVisit(data, limits, func(token xml.Token, node *xmlElement) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if _, start := token.(xml.StartElement); !start {
			return nil
		}
		p.declared[node.Name.Space] = true
		for _, attribute := range node.Attr {
			if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
				p.declared[attribute.Value] = true
			} else {
				p.declared[attribute.Name.Space] = true
			}
			if signatureIDAttribute(node, attribute) && ids[strings.Trim(attribute.Value, " \t\r\n")] {
				p.selected[node] = true
			}
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if ids != nil && root.Name == (xml.Name{Space: xmlSignatureNamespace, Local: "Signature"}) {
		for _, child := range root.Children {
			if child.Name == (xml.Name{Space: xmlSignatureNamespace, Local: "SignedInfo"}) {
				p.selected[child] = true
			}
		}
	}
	var mark func(*xmlElement, bool) (bool, error)
	mark = func(node *xmlElement, active bool) (bool, error) {
		if err := checkContext(ctx); err != nil {
			return false, err
		}
		active = active || ids == nil || p.selected[node]
		needed := active
		for _, child := range node.Children {
			value, err := mark(child, active)
			if err != nil {
				return false, err
			}
			needed = needed || value
		}
		p.needed[node] = needed
		return needed, nil
	}
	if _, err := mark(root, false); err != nil {
		return nil, err
	}
	if err := p.walk(root, compatibilityScope{}, ids == nil, false); err != nil {
		return nil, err
	}
	result := slices.Sorted(maps.Keys(p.unknown))
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// walk 检查原始分支中的实际扩展使用和理解要求，未选定子树不产生扩展证据
// 入参: node 当前节点, inherited 祖先MCE作用域, active 是否位于签署子树, alternative 是否位于替代表示中
// 返回: error MCE或取消错误
func (p *signatureNamespaceScan) walk(node *xmlElement, inherited compatibilityScope, active, alternative bool) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	if !p.needed[node] {
		return nil
	}
	active = active || p.selected[node]
	parser := compatibilityProcessor{understood: p.declared, context: p.context}
	scope, err := parser.rules(node, inherited)
	if err != nil {
		return err
	}
	add := func(namespace string) {
		if active && !p.known[namespace] {
			p.unknown[namespace] = true
		}
	}
	for _, attribute := range node.Attr {
		if attribute.Name == (xml.Name{Space: mcNamespace, Local: "MustUnderstand"}) {
			uris, err := compatibilityPrefixes(node, attribute.Value)
			if err != nil {
				return err
			}
			for _, uri := range uris {
				add(uri)
			}
		}
	}
	if node.Name.Space == mcNamespace {
		if err := parser.validateAttributes(node, scope, true); err != nil {
			return err
		}
		switch node.Name.Local {
		case "AlternateContent", "Fallback":
			alternative = true
		case "Choice":
			alternative = true
			value, present := node.attribute("Requires")
			if !present {
				return fmt.Errorf("%w: signed Choice has no Requires", ErrInvalid)
			}
			uris, err := compatibilityPrefixes(node, value)
			if err != nil {
				return err
			}
			if len(uris) == 0 {
				return fmt.Errorf("%w: signed Choice Requires is empty", ErrInvalid)
			}
			for _, uri := range uris {
				add(uri)
			}
		default:
			return fmt.Errorf("%w: unexpected signed MCE control", ErrInvalid)
		}
	}
	if scope.ignorable[node.Name.Space] || alternative {
		add(node.Name.Space)
	}
	for _, attribute := range node.Attr {
		if attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		if scope.ignorable[attribute.Name.Space] || alternative {
			add(attribute.Name.Space)
		}
	}
	for _, child := range node.Children {
		if err := p.walk(child, scope, active, alternative); err != nil {
			return err
		}
	}
	return nil
}

// packageObject 检查包专用对象的两个必需元素及关系变换的跨引用唯一性
// 入参: node 包专用Object元素, result 待填充的独立声明信息
// 返回: error 结构、引用、时间或取消错误
func (p *signatureXML) packageObject(node *xmlElement, result *SignatureInfo) error {
	if len(node.Children) != 2 {
		return fmt.Errorf("%w: package signature object children", ErrInvalid)
	}
	var manifest, properties *xmlElement
	for _, child := range node.Children {
		switch child.Name {
		case xml.Name{Space: xmlSignatureNamespace, Local: "Manifest"}:
			manifest = child
		case xml.Name{Space: xmlSignatureNamespace, Local: "SignatureProperties"}:
			properties = child
		default:
			return fmt.Errorf("%w: unexpected package signature object child", ErrInvalid)
		}
	}
	if manifest == nil || properties == nil || len(manifest.Children) == 0 || !xmlWhitespace(manifest.Text) {
		return fmt.Errorf("%w: package signature manifest or properties", ErrInvalid)
	}
	if _, err := signatureAttributes(manifest, "Id"); err != nil {
		return err
	}
	relationships := make(map[string]bool)
	for _, child := range manifest.Children {
		if err := checkContext(p.context); err != nil {
			return err
		}
		reference, err := p.reference(child, true)
		if err != nil {
			return err
		}
		for _, transform := range reference.Transforms {
			if transform.Algorithm == signatureRelationships {
				key := strings.ToLower(reference.Part)
				if relationships[key] {
					return fmt.Errorf("%w: repeated relationship transform for one part", ErrInvalid)
				}
				relationships[key] = true
			}
		}
		result.Parts = append(result.Parts, reference)
	}
	if _, err := signatureAttributes(properties, "Id"); err != nil {
		return err
	}
	if len(properties.Children) == 0 || !xmlWhitespace(properties.Text) {
		return fmt.Errorf("%w: empty or invalid signature properties", ErrInvalid)
	}
	count := 0
	for _, child := range properties.Children {
		if err := checkContext(p.context); err != nil {
			return err
		}
		if child.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "SignatureProperty"}) || len(child.Children) == 0 {
			return fmt.Errorf("%w: signature property element", ErrInvalid)
		}
		attrs, err := signatureAttributes(child, "Id", "Target")
		if err != nil {
			return err
		}
		target, present := attrs["Target"]
		target = strings.Trim(target, " \t\r\n")
		if !present || !uriReference(target) {
			return fmt.Errorf("%w: signature property target", ErrInvalid)
		}
		for _, extension := range child.Children {
			if extension.Name.Space == "" || extension.Name.Space == xmlSignatureNamespace {
				return fmt.Errorf("%w: signature property requires extension elements", ErrInvalid)
			}
		}
		if strings.Trim(attrs["Id"], " \t\r\n") != "idSignatureTime" {
			continue
		}
		count++
		if target != "" {
			id, err := signatureReferenceID(target)
			if err != nil || result.ID == "" || id != result.ID {
				return fmt.Errorf("%w: signature time target differs from root ID", ErrInvalid)
			}
		}
		if len(child.Children) != 1 {
			return fmt.Errorf("%w: signature time property children", ErrInvalid)
		}
		result.Time, err = readSignatureTime(child.Children[0])
		if err != nil {
			return err
		}
	}
	if count != 1 {
		return fmt.Errorf("%w: signature requires one time property", ErrInvalid)
	}
	return nil
}

// certificates 读取KeyInfo直接声明或包内检索的证书及ECKeyValue公钥，不访问远程位置
// 入参: node KeyInfo元素
// 返回: [][]byte 独立证书字节, []crypto.PublicKey 解析出的公钥, error 结构、引用、能力、编码或取消错误
func (p *signatureXML) certificates(node *xmlElement) ([][]byte, []crypto.PublicKey, error) {
	if _, err := signatureAttributes(node, "Id"); err != nil {
		return nil, nil, err
	}
	if len(node.Children) == 0 || !xmlWhitespace(node.Text) {
		return nil, nil, fmt.Errorf("%w: empty signature KeyInfo", ErrInvalid)
	}
	var result [][]byte
	var retrievedParts [][]byte
	var publicKeys []crypto.PublicKey
	for _, child := range node.Children {
		if err := checkContext(p.context); err != nil {
			return nil, nil, err
		}
		if child.Name.Space != xmlSignatureNamespace {
			if child.Name.Space == "" {
				return nil, nil, fmt.Errorf("%w: unqualified KeyInfo extension", ErrInvalid)
			}
			continue
		}
		switch child.Name.Local {
		case "KeyName", "PGPData", "SPKIData", "MgmtData":
			continue
		case "KeyValue":
			if _, err := signatureAttributes(child); err != nil {
				return nil, nil, err
			}
			for _, value := range child.Children {
				if err := checkContext(p.context); err != nil {
					return nil, nil, err
				}
				if value.Name == (xml.Name{Space: xmlSignature11Namespace, Local: "ECKeyValue"}) {
					if len(publicKeys) >= min(signatureMaxCertificates, p.limits.MaxPartCount) {
						return nil, nil, fmt.Errorf("%w: signer key value count", ErrLimit)
					}
					key, err := parseSignatureECKeyValue(value)
					if err != nil {
						return nil, nil, err
					}
					if err := p.retrievalCharge(int64((key.Curve.Params().BitSize+7)/8)*2 + 1); err != nil {
						return nil, nil, err
					}
					publicKeys = append(publicKeys, key)
				}
			}
			continue
		case "RetrievalMethod":
			if err := p.retrievalMethod(child); err != nil {
				return nil, nil, err
			}
			data, embedded, err := p.retrievalCertificates(child)
			if err != nil {
				return nil, nil, err
			}
			if len(data) > min(signatureMaxCertificates, p.limits.MaxPartCount)-len(result)-len(retrievedParts) {
				return nil, nil, fmt.Errorf("%w: retrieved signer certificate count", ErrLimit)
			}
			if embedded {
				result = append(result, data...)
			} else {
				retrievedParts = append(retrievedParts, data...)
			}
			continue
		case "X509Data":
		default:
			return nil, nil, fmt.Errorf("%w: unexpected KeyInfo element", ErrInvalid)
		}
		if _, err := signatureAttributes(child); err != nil {
			return nil, nil, err
		}
		if len(child.Children) == 0 || !xmlWhitespace(child.Text) {
			return nil, nil, fmt.Errorf("%w: empty or invalid X509Data", ErrInvalid)
		}
		for _, certificate := range child.Children {
			if err := checkContext(p.context); err != nil {
				return nil, nil, err
			}
			if certificate.Name.Space != xmlSignatureNamespace {
				if certificate.Name.Space == "" {
					return nil, nil, fmt.Errorf("%w: unqualified X509Data extension", ErrInvalid)
				}
				continue
			}
			switch certificate.Name.Local {
			case "X509IssuerSerial", "X509SKI", "X509SubjectName", "X509CRL":
				continue
			case "X509Certificate":
			default:
				return nil, nil, fmt.Errorf("%w: unexpected X509Data element", ErrInvalid)
			}
			if _, err := signatureAttributes(certificate); err != nil {
				return nil, nil, err
			}
			data, err := signatureBinary(certificate)
			if err != nil {
				return nil, nil, err
			}
			if err := p.retrievalCharge(int64(len(data))); err != nil {
				return nil, nil, err
			}
			if len(result)+len(retrievedParts) >= min(signatureMaxCertificates, p.limits.MaxPartCount) {
				return nil, nil, fmt.Errorf("%w: embedded signer certificate count", ErrLimit)
			}
			result = append(result, data)
		}
	}
	if len(result) == 0 {
		return retrievedParts, publicKeys, nil
	}
	return result, publicKeys, nil
}

// retrievalMethod 校验KeyInfo的RetrievalMethod引用并拒绝包外远程证书位置
// 入参: node KeyInfo的RetrievalMethod元素
// 返回: error 结构、远程证书、悬空片段、类型不符、能力或取消错误
func (p *signatureXML) retrievalMethod(node *xmlElement) error {
	attrs, err := signatureAttributes(node, "URI", "Type")
	if err != nil {
		return err
	}
	uri, present := attrs["URI"]
	uri = strings.Trim(uri, " \t\r\n")
	typ := strings.Trim(attrs["Type"], " \t\r\n")
	if !present || !uriReference(uri) || !uriReference(typ) || !xmlWhitespace(node.Text) {
		return fmt.Errorf("%w: RetrievalMethod URI, Type or content", ErrInvalid)
	}
	if err := p.retrievalTransforms(node); err != nil {
		return err
	}
	reference, err := url.Parse(uri)
	if err != nil {
		return fmt.Errorf("%w: RetrievalMethod URI", ErrInvalid)
	}
	certificate := typ == xmlSignatureNamespace+"X509Data" || typ == xmlSignatureNamespace+"rawX509Certificate"
	nonCertificate := false
	switch typ {
	case xmlSignatureNamespace + "DSAKeyValue", xmlSignatureNamespace + "RSAKeyValue", xmlSignature11Namespace + "ECKeyValue", xmlSignatureNamespace + "PGPData", xmlSignatureNamespace + "SPKIData", xmlSignatureNamespace + "MgmtData":
		nonCertificate = true
	}
	if reference.Scheme != "" || strings.HasPrefix(uri, "//") {
		if certificate {
			return fmt.Errorf("%w: XPS M10.18 forbids remote certificate RetrievalMethod", ErrInvalid)
		}
		if nonCertificate && len(node.Children) == 0 {
			return nil
		}
		return fmt.Errorf("%w: RetrievalMethod external information or transforms", ErrUnsupported)
	}
	if nonCertificate && strings.HasPrefix(uri, "#") && uri != "#" {
		id, err := signatureReferenceID(uri)
		if err != nil {
			return err
		}
		target := p.ids[id]
		if target == nil {
			return fmt.Errorf("%w: unresolved RetrievalMethod fragment", ErrInvalid)
		}
		if len(node.Children) == 0 {
			want := xml.Name{Space: xmlSignatureNamespace, Local: strings.TrimPrefix(typ, xmlSignatureNamespace)}
			if strings.HasPrefix(typ, xmlSignature11Namespace) {
				want = xml.Name{Space: xmlSignature11Namespace, Local: strings.TrimPrefix(typ, xmlSignature11Namespace)}
			}
			if target.Name != want {
				return fmt.Errorf("%w: RetrievalMethod target differs from Type", ErrInvalid)
			}
			return nil
		}
	}
	if certificate || typ == "" {
		return nil
	}
	return fmt.Errorf("%w: RetrievalMethod unclassified information", ErrUnsupported)
}

// retrievalTransforms 检查检索变换算法列表并禁止在KeyInfo中使用关系变换
// 入参: node RetrievalMethod元素
// 返回: error 子元素、属性、算法URI或取消错误
func (p *signatureXML) retrievalTransforms(node *xmlElement) error {
	if len(node.Children) == 0 {
		return nil
	}
	if len(node.Children) != 1 || node.Children[0].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Transforms"}) {
		return fmt.Errorf("%w: RetrievalMethod children", ErrInvalid)
	}
	transforms := node.Children[0]
	if _, err := signatureAttributes(transforms); err != nil {
		return err
	}
	if len(transforms.Children) == 0 || !xmlWhitespace(transforms.Text) {
		return fmt.Errorf("%w: RetrievalMethod transforms", ErrInvalid)
	}
	for _, transform := range transforms.Children {
		if err := checkContext(p.context); err != nil {
			return err
		}
		if transform.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Transform"}) {
			return fmt.Errorf("%w: RetrievalMethod transform element", ErrInvalid)
		}
		attrs, err := signatureAttributes(transform, "Algorithm")
		if err != nil {
			return err
		}
		algorithm, present := attrs["Algorithm"]
		algorithm = strings.Trim(algorithm, " \t\r\n")
		if !present || algorithm == "" || !uriReference(algorithm) {
			return fmt.Errorf("%w: missing or invalid signature algorithm", ErrInvalid)
		}
		if !signatureCanonicalMethod(algorithm) {
			return fmt.Errorf("%w: OPC M6.19 forbids KeyInfo retrieval transform", ErrInvalid)
		}
		if _, _, err := signatureCanonicalNode(transform); err != nil {
			return err
		}
	}
	return nil
}

// readSignatureTime 按OPC的格式及值模式检查声明时间，不添加日期、时区或小数精度
// 入参: node SignatureTime元素
// 返回: SignatureTime 原始声明, error 元素或时间格式错误
func readSignatureTime(node *xmlElement) (SignatureTime, error) {
	var result SignatureTime
	if node.Name != (xml.Name{Space: opcSignatureNamespace, Local: "SignatureTime"}) || !xmlWhitespace(node.Text) || len(node.Children) != 2 {
		return result, fmt.Errorf("%w: signature time structure", ErrInvalid)
	}
	if _, err := signatureAttributes(node); err != nil {
		return result, err
	}
	for index, child := range node.Children {
		name := "Format"
		if index == 1 {
			name = "Value"
		}
		if child.Name != (xml.Name{Space: opcSignatureNamespace, Local: name}) || len(child.Children) != 0 {
			return result, fmt.Errorf("%w: signature time child order", ErrInvalid)
		}
		if _, err := signatureAttributes(child); err != nil {
			return result, err
		}
	}
	result.Format, result.Value = node.Children[0].Text, node.Children[1].Text
	if !signatureTimeValue(result.Format, result.Value) {
		return SignatureTime{}, fmt.Errorf("%w: signature time value does not match format", ErrInvalid)
	}
	return result, nil
}

// signatureTimeValue 检查OPC2006的六种时间粒度、日历及字段范围，小数秒支持一位或多位ASCII数字
// 入参: format 格式声明, value 时间值
// 返回: bool 是否符合声明的词法格式及字段范围
func signatureTimeValue(format, value string) bool {
	length := 0
	switch format {
	case "YYYY":
		length = 4
	case "YYYY-MM":
		length = 7
	case "YYYY-MM-DD":
		length = 10
	case "YYYY-MM-DDThh:mmTZD":
		length = 16
	case "YYYY-MM-DDThh:mm:ssTZD":
		length = 19
	case "YYYY-MM-DDThh:mm:ss.sTZD":
		length = 21
	default:
		return false
	}
	if len(value) < length {
		return false
	}
	for _, c := range value[:4] {
		if c < '0' || c > '9' {
			return false
		}
	}
	if length >= 7 && (value[4] != '-' || signatureTimeDigits(value[5:7]) < 1 || signatureTimeDigits(value[5:7]) > 12) {
		return false
	}
	if length >= 10 && (value[7] != '-' || signatureTimeDigits(value[8:10]) < 1 || signatureTimeDigits(value[8:10]) > 31) {
		return false
	}
	if length >= 10 {
		year, _ := strconv.Atoi(value[:4])
		month, day := signatureTimeDigits(value[5:7]), signatureTimeDigits(value[8:10])
		date := time.Date(year, time.Month(month), day, 0, 0, 0, 0, time.UTC)
		if int(date.Month()) != month || date.Day() != day {
			return false
		}
	}
	if length <= 10 {
		return len(value) == length
	}
	if value[10] != 'T' || value[13] != ':' || signatureTimeDigits(value[11:13]) < 0 || signatureTimeDigits(value[11:13]) > 23 || signatureTimeDigits(value[14:16]) < 0 || signatureTimeDigits(value[14:16]) > 59 {
		return false
	}
	if length >= 19 && (value[16] != ':' || signatureTimeDigits(value[17:19]) < 0 || signatureTimeDigits(value[17:19]) > 59) {
		return false
	}
	zonePos := length
	if length == 21 {
		if value[19] != '.' || value[20] < '0' || value[20] > '9' {
			return false
		}
		for zonePos < len(value) && value[zonePos] >= '0' && value[zonePos] <= '9' {
			zonePos++
		}
	}
	zone := value[zonePos:]
	if zone == "Z" {
		return true
	}
	return len(zone) == 6 && (zone[0] == '+' || zone[0] == '-') && zone[3] == ':' && signatureTimeDigits(zone[1:3]) >= 0 && signatureTimeDigits(zone[1:3]) <= 23 && signatureTimeDigits(zone[4:6]) >= 0 && signatureTimeDigits(zone[4:6]) <= 59
}

// signatureTimeDigits 读取两个ASCII数字，不接受符号或其他Unicode数字
// 入参: value 两字节字段
// 返回: int 字段值，非法时为 -1
func signatureTimeDigits(value string) int {
	if len(value) != 2 || value[0] < '0' || value[0] > '9' || value[1] < '0' || value[1] > '9' {
		return -1
	}
	return int(value[0]-'0')*10 + int(value[1]-'0')
}

// signedInfo 检查算法及有序引用，包专用对象必须且只能被引用一次
// 入参: node SignedInfo元素, result 待填充的独立声明信息
// 返回: error 结构、算法、引用或取消错误
func (p *signatureXML) signedInfo(node *xmlElement, result *SignatureInfo) error {
	if _, err := signatureAttributes(node, "Id"); err != nil {
		return err
	}
	if !xmlWhitespace(node.Text) || len(node.Children) < 3 || node.Children[0].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "CanonicalizationMethod"}) || node.Children[1].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "SignatureMethod"}) {
		return fmt.Errorf("%w: SignedInfo child order", ErrInvalid)
	}
	var err error
	result.Canonicalization, result.InclusiveNamespaces, err = signatureCanonicalNode(node.Children[0])
	if err != nil {
		return err
	}
	if !signatureCanonicalMethod(result.Canonicalization) {
		return fmt.Errorf("%w: signature canonicalization method", ErrUnsupported)
	}
	result.Method, result.PSS, err = signatureMethodNode(node.Children[1])
	if err != nil {
		return err
	}
	count := 0
	for _, child := range node.Children[2:] {
		if err := checkContext(p.context); err != nil {
			return err
		}
		reference, err := p.reference(child, false)
		if err != nil {
			return err
		}
		id, err := signatureReferenceID(reference.URI)
		if err != nil {
			return err
		}
		if p.ids[id] == nil {
			return fmt.Errorf("%w: unresolved signature reference ID", ErrInvalid)
		}
		if id == "idPackageObject" {
			count++
		}
		result.References = append(result.References, reference)
	}
	if count != 1 {
		return fmt.Errorf("%w: SignedInfo must reference its package object once", ErrInvalid)
	}
	return nil
}

// reference 读取引用、摘要声明及变换，不解压目标或计算摘要
// 入参: node Reference元素, packagePart 是否引用包部件
// 返回: SignatureReference 引用信息, error 结构、引用或算法错误
func (p *signatureXML) reference(node *xmlElement, packagePart bool) (SignatureReference, error) {
	var result SignatureReference
	if node.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Reference"}) || !xmlWhitespace(node.Text) {
		return result, fmt.Errorf("%w: signature Reference element", ErrInvalid)
	}
	attrs, err := signatureAttributes(node, "Id", "URI", "Type")
	if err != nil {
		return result, err
	}
	uri, present := attrs["URI"]
	if !present || !uriReference(strings.Trim(uri, " \t\r\n")) || !uriReference(strings.Trim(attrs["Type"], " \t\r\n")) {
		return result, fmt.Errorf("%w: signature reference URI", ErrInvalid)
	}
	result.URI, result.Type = uri, attrs["Type"]
	if packagePart {
		result.Part, result.ContentType, err = signaturePartReference(uri)
		if err != nil {
			return result, err
		}
	}
	index := 0
	if len(node.Children) != 0 && node.Children[0].Name == (xml.Name{Space: xmlSignatureNamespace, Local: "Transforms"}) {
		result.Transforms, err = p.transforms(node.Children[0], packagePart, result.Part)
		if err != nil {
			return result, err
		}
		index++
	}
	if len(node.Children) != index+2 || node.Children[index].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "DigestMethod"}) || node.Children[index+1].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "DigestValue"}) {
		return result, fmt.Errorf("%w: signature reference child order", ErrInvalid)
	}
	result.DigestMethod, err = signatureAlgorithm(node.Children[index])
	if err != nil {
		return result, err
	}
	if _, err := signatureAttributes(node.Children[index+1]); err != nil {
		return result, err
	}
	result.Digest, err = signatureBinary(node.Children[index+1])
	return result, err
}

// transforms 读取OPC支持的有序变换，关系变换仅用于关系部件且紧接规范化变换
// 入参: node Transforms元素, packagePart 是否引用包部件, part 引用的包部件名称
// 返回: []SignatureTransform 变换信息, error 结构、算法或取消错误
func (p *signatureXML) transforms(node *xmlElement, packagePart bool, part string) ([]SignatureTransform, error) {
	if _, err := signatureAttributes(node); err != nil {
		return nil, err
	}
	if !xmlWhitespace(node.Text) || len(node.Children) == 0 {
		return nil, fmt.Errorf("%w: empty or invalid signature transforms", ErrInvalid)
	}
	var result []SignatureTransform
	count := 0
	for _, child := range node.Children {
		if err := checkContext(p.context); err != nil {
			return nil, err
		}
		if child.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Transform"}) {
			return nil, fmt.Errorf("%w: unexpected signature transform child", ErrInvalid)
		}
		attrs, err := signatureAttributes(child, "Algorithm")
		if err != nil {
			return nil, err
		}
		algorithm, present := attrs["Algorithm"]
		algorithm = strings.Trim(algorithm, " \t\r\n")
		if !present || algorithm == "" || !uriReference(algorithm) {
			return nil, fmt.Errorf("%w: signature transform algorithm", ErrInvalid)
		}
		transform := SignatureTransform{Algorithm: algorithm}
		switch {
		case signatureCanonicalMethod(algorithm):
			_, inclusive, err := signatureCanonicalNode(child)
			if err != nil {
				return nil, err
			}
			transform.InclusiveNamespaces = inclusive
		case algorithm == signatureRelationships:
			if !packagePart || !opcRelationshipName(part) {
				return nil, fmt.Errorf("%w: relationship transform on non-relationship reference", ErrInvalid)
			}
			count++
			if count != 1 {
				return nil, fmt.Errorf("%w: multiple relationship transforms", ErrInvalid)
			}
			for _, filter := range child.Children {
				if err := checkContext(p.context); err != nil {
					return nil, err
				}
				if filter.Name.Space != opcSignatureNamespace || len(filter.Children) != 0 {
					return nil, fmt.Errorf("%w: relationship transform filter", ErrInvalid)
				}
				switch filter.Name.Local {
				case "RelationshipReference":
					attrs, err := signatureAttributes(filter, "SourceId")
					if err != nil {
						return nil, err
					}
					value, present := attrs["SourceId"]
					value = strings.Trim(value, " \t\r\n")
					if !present || !xmlNCName(value) {
						return nil, fmt.Errorf("%w: invalid or missing relationship SourceId", ErrInvalid)
					}
					transform.RelationshipIDs = append(transform.RelationshipIDs, value)
				case "RelationshipsGroupReference":
					attrs, err := signatureAttributes(filter, "SourceType")
					if err != nil {
						return nil, err
					}
					value, present := attrs["SourceType"]
					value = strings.Trim(value, " \t\r\n")
					if !present || !uriReference(value) {
						return nil, fmt.Errorf("%w: relationship SourceType URI", ErrInvalid)
					}
					transform.RelationshipTypes = append(transform.RelationshipTypes, value)
				default:
					return nil, fmt.Errorf("%w: unknown relationship transform filter", ErrInvalid)
				}
			}
		default:
			return nil, fmt.Errorf("%w: signature transform algorithm", ErrUnsupported)
		}
		result = append(result, transform)
	}
	for index, transform := range result {
		if transform.Algorithm == signatureRelationships && (index+1 == len(result) || !signatureCanonicalMethod(result[index+1].Algorithm)) {
			return nil, fmt.Errorf("%w: relationship transform is not followed by canonicalization", ErrInvalid)
		}
	}
	return result, nil
}

// signatureAlgorithm 读取算法标识，不忽略尚未支持的参数元素或混合文本
// 入参: node 算法声明元素
// 返回: string 算法URI, error 结构或参数能力错误
func signatureAlgorithm(node *xmlElement) (string, error) {
	attrs, err := signatureAttributes(node, "Algorithm")
	if err != nil {
		return "", err
	}
	value, present := attrs["Algorithm"]
	value = strings.Trim(value, " \t\r\n")
	if !present || value == "" || !uriReference(value) {
		return "", fmt.Errorf("%w: missing or invalid signature algorithm", ErrInvalid)
	}
	if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
		return "", fmt.Errorf("%w: signature algorithm parameters", ErrUnsupported)
	}
	return value, nil
}

// signatureCanonicalMethod 判断支持的C14N1.0、Exclusive C14N1.0及C14N1.1规范化算法标识
// 入参: value 算法URI
// 返回: bool 是否为支持的规范化算法
func signatureCanonicalMethod(value string) bool {
	switch value {
	case signatureCanonical, signatureComments, signatureExcCanonical, signatureExcComments, signatureCanonical11, signatureComments11:
		return true
	}
	return false
}

// signatureCanonicalComments 判断规范化算法是否保留XML注释
// 入参: value 算法URI
// 返回: bool 是否为保留注释的规范化算法
func signatureCanonicalComments(value string) bool {
	return value == signatureComments || value == signatureExcComments || value == signatureComments11
}

// signatureCanonicalExclusive 判断规范化算法是否属于Exclusive C14N1.0
// 入参: value 算法URI
// 返回: bool 是否为Exclusive C14N1.0算法
func signatureCanonicalExclusive(value string) bool {
	return value == signatureExcCanonical || value == signatureExcComments
}

// signatureCanonicalNode 解析规范化算法及Exclusive C14N可选InclusiveNamespaces前缀列表
// 入参: node CanonicalizationMethod或Transform元素
// 返回: string 算法URI, []string 前缀列表, error 结构、前缀或能力错误
func signatureCanonicalNode(node *xmlElement) (string, []string, error) {
	attrs, err := signatureAttributes(node, "Algorithm")
	if err != nil {
		return "", nil, err
	}
	value, present := attrs["Algorithm"]
	value = strings.Trim(value, " \t\r\n")
	if !present || value == "" || !uriReference(value) {
		return "", nil, fmt.Errorf("%w: missing or invalid signature algorithm", ErrInvalid)
	}
	if !signatureCanonicalExclusive(value) {
		if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return "", nil, fmt.Errorf("%w: canonical transform parameters", ErrUnsupported)
		}
		return value, nil, nil
	}
	if !xmlWhitespace(node.Text) {
		return "", nil, fmt.Errorf("%w: exclusive canonical transform text", ErrInvalid)
	}
	if len(node.Children) == 0 {
		return value, nil, nil
	}
	if len(node.Children) != 1 || node.Children[0].Name != (xml.Name{Space: signatureExcNamespace, Local: "InclusiveNamespaces"}) {
		return "", nil, fmt.Errorf("%w: exclusive canonical transform parameters", ErrUnsupported)
	}
	child := node.Children[0]
	if len(child.Children) != 0 || !xmlWhitespace(child.Text) {
		return "", nil, fmt.Errorf("%w: InclusiveNamespaces element content", ErrInvalid)
	}
	childAttrs, err := signatureAttributes(child, "PrefixList")
	if err != nil {
		return "", nil, err
	}
	prefixList, hasPrefixList := childAttrs["PrefixList"]
	if !hasPrefixList {
		return "", nil, fmt.Errorf("%w: InclusiveNamespaces missing PrefixList", ErrInvalid)
	}
	prefixes := compatibilityWords(prefixList)
	for _, prefix := range prefixes {
		if prefix != "#default" && (!xmlNCName(prefix) || prefix == "xmlns") {
			return "", nil, fmt.Errorf("%w: InclusiveNamespaces prefix %q", ErrInvalid, prefix)
		}
	}
	return value, prefixes, nil
}

// signatureMethodNode 解析SignatureMethod算法及RSA-PSS参数，拒绝未知算法参数
// 入参: node SignatureMethod元素
// 返回: string 签名方法URI, *SignaturePSSParams 可选RSA-PSS参数, error 结构、参数或能力错误
func signatureMethodNode(node *xmlElement) (string, *SignaturePSSParams, error) {
	attrs, err := signatureAttributes(node, "Algorithm")
	if err != nil {
		return "", nil, err
	}
	value, present := attrs["Algorithm"]
	value = strings.Trim(value, " \t\r\n")
	if !present || value == "" || !uriReference(value) {
		return "", nil, fmt.Errorf("%w: missing or invalid signature algorithm", ErrInvalid)
	}
	switch value {
	case signatureMethodRSAPSS:
		params, err := parseSignaturePSSParams(node)
		if err != nil {
			return "", nil, err
		}
		return value, params, nil
	case signatureMethodPSS256:
		if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return "", nil, fmt.Errorf("%w: signature algorithm parameters", ErrUnsupported)
		}
		return value, &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmlenc#sha256", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmlenc#sha256", SaltLength: 32, TrailerField: 1}, nil
	case signatureMethodPSS384:
		if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return "", nil, fmt.Errorf("%w: signature algorithm parameters", ErrUnsupported)
		}
		return value, &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmldsig-more#sha384", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmldsig-more#sha384", SaltLength: 48, TrailerField: 1}, nil
	case signatureMethodPSS512:
		if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return "", nil, fmt.Errorf("%w: signature algorithm parameters", ErrUnsupported)
		}
		return value, &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmlenc#sha512", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmlenc#sha512", SaltLength: 64, TrailerField: 1}, nil
	default:
		if len(node.Children) != 0 || !xmlWhitespace(node.Text) {
			return "", nil, fmt.Errorf("%w: signature algorithm parameters", ErrUnsupported)
		}
		return value, nil, nil
	}
}

// parseSignaturePSSParams 按RFC6931与RFC9231解析RSAPSSParams元素并补全标准缺省参数
// 入参: node SignatureMethod元素
// 返回: *SignaturePSSParams 解析并补全后的RSA-PSS参数, error 结构、参数值或能力错误
func parseSignaturePSSParams(node *xmlElement) (*SignaturePSSParams, error) {
	if !xmlWhitespace(node.Text) || len(node.Children) > 1 {
		return nil, fmt.Errorf("%w: RSA-PSS SignatureMethod children", ErrInvalid)
	}
	params := &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmlenc#sha256", MGFMethod: signatureMethodMGF1, TrailerField: 1}
	hasMGFDigest, hasSalt := false, false
	if len(node.Children) == 1 {
		root := node.Children[0]
		if root.Name != (xml.Name{Space: signaturePSSNamespace, Local: "RSAPSSParams"}) || !xmlWhitespace(root.Text) {
			return nil, fmt.Errorf("%w: expected RSAPSSParams element", ErrInvalid)
		}
		if _, err := signatureAttributes(root); err != nil {
			return nil, err
		}
		order := 0
		for _, child := range root.Children {
			rank := 0
			switch child.Name {
			case xml.Name{Space: xmlSignatureNamespace, Local: "DigestMethod"}:
				rank = 1
			case xml.Name{Space: signaturePSSNamespace, Local: "MaskGenerationFunction"}:
				rank = 2
			case xml.Name{Space: signaturePSSNamespace, Local: "SaltLength"}:
				rank = 3
			case xml.Name{Space: signaturePSSNamespace, Local: "TrailerField"}:
				rank = 4
			}
			if rank <= order {
				return nil, fmt.Errorf("%w: RSAPSSParams child order or element", ErrInvalid)
			}
			order = rank
			switch rank {
			case 1:
				digest, err := signatureAlgorithm(child)
				if err != nil {
					return nil, err
				}
				params.DigestMethod = digest
			case 2:
				mgfAttrs, err := signatureAttributes(child, "Algorithm")
				if err != nil {
					return nil, err
				}
				mgf := strings.Trim(mgfAttrs["Algorithm"], " \t\r\n")
				if mgf == "" || !uriReference(mgf) {
					return nil, fmt.Errorf("%w: MaskGenerationFunction algorithm", ErrInvalid)
				}
				if mgf != signatureMethodMGF1 {
					return nil, fmt.Errorf("%w: unsupported MaskGenerationFunction %s", ErrUnsupported, mgf)
				}
				if !xmlWhitespace(child.Text) || len(child.Children) > 1 {
					return nil, fmt.Errorf("%w: MaskGenerationFunction children", ErrInvalid)
				}
				params.MGFMethod = mgf
				if len(child.Children) == 1 {
					if child.Children[0].Name != (xml.Name{Space: xmlSignatureNamespace, Local: "DigestMethod"}) {
						return nil, fmt.Errorf("%w: MaskGenerationFunction DigestMethod", ErrInvalid)
					}
					mgfDigest, err := signatureAlgorithm(child.Children[0])
					if err != nil {
						return nil, err
					}
					params.MGFDigest = mgfDigest
					hasMGFDigest = true
				}
			case 3:
				if len(child.Children) != 0 {
					return nil, fmt.Errorf("%w: SaltLength children", ErrInvalid)
				}
				if _, err := signatureAttributes(child); err != nil {
					return nil, err
				}
				text := strings.Trim(child.Text, " \t\r\n")
				if !printInteger(text) {
					return nil, fmt.Errorf("%w: SaltLength integer", ErrInvalid)
				}
				value, err := strconv.Atoi(text)
				if err != nil || value < 0 {
					return nil, fmt.Errorf("%w: SaltLength range", ErrInvalid)
				}
				if value > signatureMaxKeyBits/8 {
					return nil, fmt.Errorf("%w: SaltLength limit", ErrLimit)
				}
				params.SaltLength = value
				hasSalt = true
			case 4:
				if len(child.Children) != 0 {
					return nil, fmt.Errorf("%w: TrailerField children", ErrInvalid)
				}
				if _, err := signatureAttributes(child); err != nil {
					return nil, err
				}
				text := strings.Trim(child.Text, " \t\r\n")
				if !printInteger(text) {
					return nil, fmt.Errorf("%w: TrailerField integer", ErrInvalid)
				}
				value, err := strconv.Atoi(text)
				if err != nil {
					return nil, fmt.Errorf("%w: TrailerField integer", ErrInvalid)
				}
				if value != 1 {
					return nil, fmt.Errorf("%w: unsupported RSA-PSS TrailerField %d", ErrUnsupported, value)
				}
				params.TrailerField = value
			}
		}
	}
	if !hasMGFDigest {
		params.MGFDigest = params.DigestMethod
	}
	if !hasSalt {
		switch params.DigestMethod {
		case xmlSignatureNamespace + "sha1":
			params.SaltLength = 20
		case "http://www.w3.org/2001/04/xmlenc#sha256":
			params.SaltLength = 32
		case "http://www.w3.org/2001/04/xmldsig-more#sha384":
			params.SaltLength = 48
		case "http://www.w3.org/2001/04/xmlenc#sha512":
			params.SaltLength = 64
		default:
			params.SaltLength = -1
		}
	}
	return params, nil
}

// parseSignatureECKeyValue 按XML-DSig1.1解析dsig11:ECKeyValue命名曲线与未压缩椭圆曲线公钥点
// 入参: node ECKeyValue元素
// 返回: *ecdsa.PublicKey 独立椭圆曲线公钥, error 结构、曲线或公钥点错误
func parseSignatureECKeyValue(node *xmlElement) (*ecdsa.PublicKey, error) {
	if _, err := signatureAttributes(node, "Id"); err != nil {
		return nil, err
	}
	if !xmlWhitespace(node.Text) || len(node.Children) != 2 {
		return nil, fmt.Errorf("%w: ECKeyValue structure", ErrInvalid)
	}
	curveNode, keyNode := node.Children[0], node.Children[1]
	if curveNode.Name == (xml.Name{Space: xmlSignature11Namespace, Local: "ECParameters"}) {
		return nil, fmt.Errorf("%w: explicit ECKeyValue parameters", ErrUnsupported)
	}
	if curveNode.Name != (xml.Name{Space: xmlSignature11Namespace, Local: "NamedCurve"}) || len(curveNode.Children) != 0 || !xmlWhitespace(curveNode.Text) {
		return nil, fmt.Errorf("%w: ECKeyValue NamedCurve", ErrInvalid)
	}
	curveAttrs, err := signatureAttributes(curveNode, "URI")
	if err != nil {
		return nil, err
	}
	uri := strings.Trim(curveAttrs["URI"], " \t\r\n")
	if uri == "" || !uriReference(uri) {
		return nil, fmt.Errorf("%w: ECKeyValue NamedCurve URI", ErrInvalid)
	}
	var curve elliptic.Curve
	switch uri {
	case "urn:oid:1.2.840.10045.3.1.7":
		curve = elliptic.P256()
	case "urn:oid:1.3.132.0.34":
		curve = elliptic.P384()
	case "urn:oid:1.3.132.0.35":
		curve = elliptic.P521()
	default:
		return nil, fmt.Errorf("%w: ECKeyValue NamedCurve %s", ErrUnsupported, uri)
	}
	if keyNode.Name != (xml.Name{Space: xmlSignature11Namespace, Local: "PublicKey"}) {
		return nil, fmt.Errorf("%w: ECKeyValue PublicKey", ErrInvalid)
	}
	if _, err := signatureAttributes(keyNode); err != nil {
		return nil, err
	}
	raw, err := signatureBinary(keyNode)
	if err != nil {
		return nil, err
	}
	coordLen := (curve.Params().BitSize + 7) / 8
	if len(raw) != 1+2*coordLen || raw[0] != 0x04 {
		return nil, fmt.Errorf("%w: ECKeyValue uncompressed point", ErrInvalid)
	}
	x := new(big.Int).SetBytes(raw[1 : 1+coordLen])
	y := new(big.Int).SetBytes(raw[1+coordLen:])
	if x.Cmp(curve.Params().P) >= 0 || y.Cmp(curve.Params().P) >= 0 || !curve.IsOnCurve(x, y) {
		return nil, fmt.Errorf("%w: ECKeyValue point off curve", ErrInvalid)
	}
	return &ecdsa.PublicKey{Curve: curve, X: x, Y: y}, nil
}

// signatureBinary 按XML Schema的base64Binary读取字节，仅移除XML空白并检查填充位
// 入参: node 不含子元素的base64元素
// 返回: []byte 独立字节, error 结构或编码错误
func signatureBinary(node *xmlElement) ([]byte, error) {
	if len(node.Children) != 0 {
		return nil, fmt.Errorf("%w: nested signature base64 content", ErrInvalid)
	}
	value := strings.Map(func(c rune) rune {
		if c == ' ' || c == '\t' || c == '\r' || c == '\n' {
			return -1
		}
		return c
	}, node.Text)
	data, err := base64.StdEncoding.Strict().DecodeString(value)
	if err != nil {
		return nil, fmt.Errorf("%w: signature base64 encoding", ErrInvalid)
	}
	return data, nil
}

// signatureReferenceID 解释同签名内的裸ID或单个id函数XPointer引用，不执行通用XPath
// 入参: value 原始URI属性值
// 返回: string 解码后的ID, error 引用或XPointer能力错误
func signatureReferenceID(value string) (string, error) {
	id, _, err := signatureFragment(value)
	return id, err
}

// signatureFragment 解释同文档ID引用及其注释保留规则，裸ID在规范化前移除注释
// 入参: value 原始URI属性值
// 返回: string 解码后的ID, bool 是否为保留注释的完整XPointer, error 引用或表达式能力错误
func signatureFragment(value string) (string, bool, error) {
	value = strings.Trim(value, " \t\r\n")
	if !strings.HasPrefix(value, "#") || !uriReference(value) {
		return "", false, fmt.Errorf("%w: signature reference is not a same-document fragment", ErrInvalid)
	}
	id, err := url.PathUnescape(value[1:])
	if err != nil {
		return "", false, fmt.Errorf("%w: signature fragment encoding", ErrInvalid)
	}
	comments := false
	if strings.HasPrefix(id, "xpointer(") {
		comments = true
		if !strings.HasPrefix(id, "xpointer(id(") || !strings.HasSuffix(id, "))") {
			return "", false, fmt.Errorf("%w: signature XPointer expression", ErrUnsupported)
		}
		inner := id[len("xpointer(id(") : len(id)-2]
		if len(inner) < 2 || inner[0] != '\'' && inner[0] != '"' || inner[len(inner)-1] != inner[0] {
			return "", false, fmt.Errorf("%w: signature XPointer ID", ErrInvalid)
		}
		id = inner[1 : len(inner)-1]
	}
	if !xmlNCName(id) {
		return "", false, fmt.Errorf("%w: invalid signature fragment ID", ErrInvalid)
	}
	return id, comments, nil
}

// signaturePartReference 读取OPC包根部件引用及内容类型，保留加号并仅解码百分号编码
// 入参: value 原始URI属性值
// 返回: string 规范部件名称, string 声明内容类型, error 引用或编码错误
func signaturePartReference(value string) (string, string, error) {
	value = strings.Trim(value, " \t\r\n")
	if !uriReference(value) || strings.Contains(value, "#") {
		return "", "", fmt.Errorf("%w: signature part reference URI", ErrInvalid)
	}
	name, query, present := strings.Cut(value, "?")
	if !present || !strings.HasPrefix(query, "ContentType=") {
		return "", "", fmt.Errorf("%w: signature part content type query", ErrInvalid)
	}
	name, err := opcPartName(name)
	if err != nil {
		return "", "", err
	}
	media, err := url.PathUnescape(strings.TrimPrefix(query, "ContentType="))
	if err != nil || media == "" {
		return "", "", fmt.Errorf("%w: signature content type encoding", ErrInvalid)
	}
	if err := validatePackageMedia(media); err != nil {
		return "", "", err
	}
	return name, media, nil
}

// signatureRelationshipXML 按ISO/IEC 29500-2:2008执行MCE、补全默认TargetMode、排序属性与关系并清除根内非元素内容
// 入参: data 原始关系XML, transform 关系选择条件, limits XML及输出上限, ctx 取消Context
// 返回: []byte 独立变换XML, error 结构、MCE、预算或取消错误，失败无部分结果
func signatureRelationshipXML(data []byte, transform SignatureTransform, limits Limits, ctx context.Context) ([]byte, error) {
	limits = mergeLimits(DefaultLimits(), limits)
	if err := validateLimits(limits); err != nil {
		return nil, err
	}
	limit := min(limits.MaxMetadataBytes, limits.MaxPartBytes, limits.MaxPackageBytes)
	if int64(len(data)) > limit || transform.Algorithm != signatureRelationships {
		if int64(len(data)) > limit {
			return nil, fmt.Errorf("%w: relationship transform input", ErrLimit)
		}
		return nil, fmt.Errorf("%w: relationship transform algorithm", ErrInvalid)
	}
	root, err := decodeXMLVisit(data, limits, func(_ xml.Token, _ *xmlElement) error { return checkContext(ctx) })
	if err != nil {
		return nil, err
	}
	processor := compatibilityProcessor{understood: map[string]bool{mcNamespace: true, xmlNamespace: true, opcRelsNS: true}, ignorePreservation: true, context: ctx}
	fragment, err := processor.element(root, compatibilityScope{})
	if err != nil {
		return nil, err
	}
	if len(fragment.elements) != 1 || !xmlWhitespace(fragment.text) {
		return nil, fmt.Errorf("%w: relationship transform requires one root", ErrInvalid)
	}
	root = fragment.elements[0]
	if root.Name != (xml.Name{Space: opcRelsNS, Local: "Relationships"}) || !xmlWhitespace(root.Text) {
		return nil, fmt.Errorf("%w: relationship transform root", ErrInvalid)
	}
	if _, err := signatureAttributes(root); err != nil {
		return nil, err
	}
	var relationships []signatureRelationship
	ids := make(map[string]bool)
	for _, child := range root.Children {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if child.Name != (xml.Name{Space: opcRelsNS, Local: "Relationship"}) || len(child.Children) != 0 {
			return nil, fmt.Errorf("%w: relationship transform child", ErrInvalid)
		}
		attrs, err := signatureAttributes(child, "Id", "Type", "Target", "TargetMode")
		if err != nil {
			return nil, err
		}
		id, hasID := attrs["Id"]
		id = strings.Trim(id, " \t\r\n")
		typ, hasType := attrs["Type"]
		target, hasTarget := attrs["Target"]
		if !hasID || !xmlNCName(id) || ids[id] || !hasType || !hasTarget || target == "" {
			return nil, fmt.Errorf("%w: relationship transform attributes", ErrInvalid)
		}
		ids[id] = true
		uri, err := opcURI(typ)
		if err != nil || uri.Scheme == "" || !uriReference(target) {
			return nil, fmt.Errorf("%w: relationship transform URI", ErrInvalid)
		}
		mode, hasMode := attrs["TargetMode"]
		if hasMode && TargetMode(mode) != TargetModeInternal && TargetMode(mode) != TargetModeExternal {
			return nil, fmt.Errorf("%w: relationship transform TargetMode", ErrInvalid)
		}
		item := signatureRelationship{id: id, typ: typ}
		for _, attr := range child.Attr {
			if attr.Name.Space == "" && attr.Name.Local != "xmlns" {
				item.attrs = append(item.attrs, attr)
			}
		}
		if !hasMode {
			item.attrs = append(item.attrs, xml.Attr{Name: xml.Name{Local: "TargetMode"}, Value: string(TargetModeInternal)})
		}
		slices.SortFunc(item.attrs, func(a, b xml.Attr) int { return strings.Compare(a.Name.Local, b.Name.Local) })
		relationships = append(relationships, item)
	}
	slices.SortFunc(relationships, func(a, b signatureRelationship) int { return strings.Compare(a.id, b.id) })
	wantedID := make(map[string]bool, len(transform.RelationshipIDs))
	wantedType := make(map[string]bool, len(transform.RelationshipTypes))
	for _, id := range transform.RelationshipIDs {
		wantedID[id] = true
	}
	for _, typ := range transform.RelationshipTypes {
		wantedType[typ] = true
	}
	selected := make([]signatureRelationship, 0, len(relationships))
	for _, relationship := range relationships {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		if wantedID[relationship.id] || wantedType[relationship.typ] {
			selected = append(selected, relationship)
		}
	}
	return signatureRelationshipOutput(selected, limit, ctx)
}

// signatureRelationshipOutput 按ISO/IEC 29500-2:2008输出纯关系根元素与排序筛选后的关系，不保留根内外注释及处理指令
// 入参: selected 排序筛选后的关系列表, limit 输出字节上限, ctx 取消Context
// 返回: []byte 独立XML字节, error 序列化、预算或取消错误
func signatureRelationshipOutput(selected []signatureRelationship, limit int64, ctx context.Context) ([]byte, error) {
	var output bytes.Buffer
	writer := packageOutput{writer: &output, context: ctx, limit: limit}
	encoder := xml.NewEncoder(&writer)
	root := xml.StartElement{Name: xml.Name{Local: "Relationships"}, Attr: []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: opcRelsNS}}}
	if err := encoder.EncodeToken(root); err != nil {
		return nil, err
	}
	for _, relationship := range selected {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		start := xml.StartElement{Name: xml.Name{Local: "Relationship"}, Attr: relationship.attrs}
		if err := encoder.EncodeToken(start); err != nil {
			return nil, err
		}
		if err := encoder.EncodeToken(start.End()); err != nil {
			return nil, err
		}
	}
	if err := encoder.EncodeToken(root.End()); err != nil {
		return nil, err
	}
	if err := encoder.Flush(); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// signatureInclusiveSet 将InclusiveNamespaces前缀切片转换为查找集合，并将#default映射为空前缀
// 入参: prefixes 已校验前缀列表
// 返回: map[string]bool 前缀查找集合
func signatureInclusiveSet(prefixes []string) map[string]bool {
	if len(prefixes) == 0 {
		return nil
	}
	result := make(map[string]bool, len(prefixes))
	for _, prefix := range prefixes {
		if prefix == "#default" {
			result[""] = true
		} else {
			result[prefix] = true
		}
	}
	return result
}

// signatureCanonicalXML 按C14N1.0、Exclusive C14N1.0或C14N1.1规范化XML文档或选定子树
// 入参: data XML原始字节, options 规范化算法、预算、前缀列表及取消选项
// 返回: []byte 独立规范化UTF-8字节, error 解析、选择、命名空间或预算错误
func signatureCanonicalXML(data []byte, options signatureCanonicalOptions) ([]byte, error) {
	if !signatureCanonicalMethod(options.algorithm) {
		return nil, fmt.Errorf("%w: signature canonicalization algorithm", ErrUnsupported)
	}
	if options.algorithm == signatureCanonical || options.algorithm == signatureComments {
		return canonicalXML(data, canonicalXMLOptions{limits: options.limits, maxBytes: options.maxBytes, comments: options.comments, context: options.context, selectElement: options.selectElement})
	}
	options.limits = mergeLimits(DefaultLimits(), options.limits)
	if err := validateLimits(options.limits); err != nil {
		return nil, err
	}
	limit := min(options.limits.MaxPartBytes, options.limits.MaxPackageBytes)
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("%w: canonical XML input bytes", ErrLimit)
	}
	if options.maxBytes == 0 {
		options.maxBytes = limit
	}
	if options.maxBytes < 0 {
		return nil, fmt.Errorf("%w: canonical XML output limit", ErrInvalid)
	}
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	var output bytes.Buffer
	w := signatureCanonicalWriter{options: options, output: packageOutput{writer: &output, context: options.context, limit: min(limit, options.maxBytes)}}
	if _, err := decodeXMLVisit(data, options.limits, w.token); err != nil {
		return nil, err
	}
	if options.selectElement != nil && !w.selected {
		return nil, fmt.Errorf("%w: canonical element not found", ErrInvalid)
	}
	if err := checkContext(options.context); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// token 按已校验词元流式输出Exclusive C14N1.0或C14N1.1规范化结果
// 入参: token 保留原始前缀的词元, node 当前元素或词元所属元素
// 返回: error 选择、命名空间、取消或输出错误
func (w *signatureCanonicalWriter) token(token xml.Token, node *xmlElement) error {
	if err := checkContext(w.options.context); err != nil {
		return err
	}
	if _, end := token.(xml.EndElement); !end {
		w.nodes++
		if w.nodes > w.options.limits.MaxXMLNodes {
			return fmt.Errorf("%w: canonical XML token count", ErrLimit)
		}
	}
	switch token := token.(type) {
	case xml.StartElement:
		for _, attr := range token.Attr {
			if attr.Name.Space != "xmlns" && attr.Name != (xml.Name{Local: "xmlns"}) {
				continue
			}
			namespace := attr.Value
			if namespace != "" {
				uri, err := opcURI(namespace)
				if err != nil || uri.Scheme == "" {
					return fmt.Errorf("%w: relative or invalid canonical namespace", ErrInvalid)
				}
			}
		}
		w.path = append(w.path, node.Name)
		selected := w.options.selectElement != nil && w.options.selectElement(node, w.path)
		if selected {
			if w.selected {
				return fmt.Errorf("%w: multiple canonical elements", ErrInvalid)
			}
			w.selected, w.selectedDepth = true, len(w.path)
		}
		if w.options.selectElement == nil || w.selectedDepth != 0 {
			if err := w.start(token, node, selected); err != nil {
				return err
			}
		}
		w.ancestors = append(w.ancestors, node)
	case xml.EndElement:
		if w.options.selectElement == nil || w.selectedDepth != 0 {
			if err := w.write("</" + canonicalQName(token.Name) + ">"); err != nil {
				return err
			}
			w.rendered = w.rendered[:len(w.rendered)-1]
		}
		if len(w.path) == w.selectedDepth {
			w.selectedDepth = 0
		}
		if len(w.path) == 1 {
			w.rootPassed = true
		}
		w.path = w.path[:len(w.path)-1]
		w.ancestors = w.ancestors[:len(w.ancestors)-1]
	case xml.CharData:
		if len(w.path) != 0 && (w.options.selectElement == nil || w.selectedDepth != 0) {
			return w.escaped(string(token), false)
		}
	case xml.Comment:
		if w.options.comments && (w.options.selectElement == nil || w.selectedDepth != 0) {
			return w.misc("<!--" + canonicalLineFeeds.Replace(string(token)) + "-->")
		}
	case xml.ProcInst:
		if token.Target != "xml" && (w.options.selectElement == nil || w.selectedDepth != 0) {
			value := "<?" + token.Target
			if len(token.Inst) != 0 {
				value += " " + canonicalLineFeeds.Replace(string(token.Inst))
			}
			return w.misc(value + "?>")
		}
	}
	return nil
}

// start 按Exclusive C14N1.0或C14N1.1规则输出起始标签、命名空间声明及排序属性
// 入参: token 起始词元, node 当前元素, selected 是否为选定子树根
// 返回: error 名称、URI合并或输出错误
func (w *signatureCanonicalWriter) start(token xml.StartElement, node *xmlElement, selected bool) error {
	if err := w.write("<" + canonicalQName(token.Name)); err != nil {
		return err
	}
	var parent map[string]string
	if len(w.rendered) != 0 {
		parent = w.rendered[len(w.rendered)-1]
	}
	exclusive := signatureCanonicalExclusive(w.options.algorithm)
	var prefixes []string
	var nextRendered map[string]string
	if exclusive {
		visiblyUtilized := map[string]bool{token.Name.Space: true}
		for _, attr := range token.Attr {
			if attr.Name.Space != "" && attr.Name.Space != "xmlns" && attr.Name.Space != "xml" {
				visiblyUtilized[attr.Name.Space] = true
			}
		}
		nextRendered = make(map[string]string, len(parent)+len(node.Namespaces))
		maps.Copy(nextRendered, parent)
		if visiblyUtilized[""] || w.options.inclusive[""] {
			defaultNS := node.Namespaces[""]
			if defaultNS != parent[""] {
				prefixes = append(prefixes, "")
				nextRendered[""] = defaultNS
			}
		}
		for prefix, namespace := range node.Namespaces {
			if prefix == "" || prefix == "xml" {
				continue
			}
			if (visiblyUtilized[prefix] || w.options.inclusive[prefix]) && namespace != parent[prefix] {
				prefixes = append(prefixes, prefix)
				nextRendered[prefix] = namespace
			}
		}
	} else {
		nextRendered = node.Namespaces
		for prefix, namespace := range node.Namespaces {
			if prefix != "xml" && namespace != parent[prefix] {
				prefixes = append(prefixes, prefix)
			}
		}
	}
	slices.Sort(prefixes)
	for _, prefix := range prefixes {
		name := xml.Name{Local: "xmlns"}
		if prefix != "" {
			name = xml.Name{Space: "xmlns", Local: prefix}
		}
		if err := w.attribute(name, nextRendered[prefix]); err != nil {
			return err
		}
	}
	var attributes []canonicalAttribute
	inherited := make(map[string]string)
	ancestorBase, hasBase := "", false
	if selected && !exclusive {
		for _, ancestor := range w.ancestors {
			for _, attr := range ancestor.Attr {
				if attr.Name.Space != xmlNamespace {
					continue
				}
				switch attr.Name.Local {
				case "lang", "space":
					inherited[attr.Name.Local] = attr.Value
				case "base":
					var err error
					ancestorBase, err = c14n11JoinURI(ancestorBase, attr.Value)
					if err != nil {
						return err
					}
					hasBase = true
				}
			}
		}
	}
	for _, attr := range token.Attr {
		if attr.Name.Space == "xmlns" || attr.Name == (xml.Name{Local: "xmlns"}) {
			continue
		}
		name, err := xmlExpandedName(node.Namespaces, attr.Name, false)
		if err != nil {
			return err
		}
		value := attr.Value
		if selected && !exclusive && name == (xml.Name{Space: xmlNamespace, Local: "base"}) && hasBase {
			value, err = c14n11JoinURI(ancestorBase, value)
			if err != nil {
				return err
			}
			hasBase = false
			if value == "" {
				continue
			}
		}
		attributes = append(attributes, canonicalAttribute{attr.Name, name, value})
		if name.Space == xmlNamespace {
			delete(inherited, name.Local)
		}
	}
	if selected && !exclusive && hasBase && ancestorBase != "" {
		attributes = append(attributes, canonicalAttribute{xml.Name{Space: "xml", Local: "base"}, xml.Name{Space: xmlNamespace, Local: "base"}, ancestorBase})
	}
	for local, value := range inherited {
		attributes = append(attributes, canonicalAttribute{xml.Name{Space: "xml", Local: local}, xml.Name{Space: xmlNamespace, Local: local}, value})
	}
	slices.SortFunc(attributes, func(a, b canonicalAttribute) int {
		if order := cmp.Compare(a.name.Space, b.name.Space); order != 0 {
			return order
		}
		return cmp.Compare(a.name.Local, b.name.Local)
	})
	for _, attr := range attributes {
		if err := w.attribute(attr.raw, attr.value); err != nil {
			return err
		}
	}
	w.rendered = append(w.rendered, nextRendered)
	return w.write(">")
}

// attribute 以双引号及C14N字符引用输出单个属性或命名空间声明
// 入参: name 原始QName, value 已完成XML输入规范化的值
// 返回: error 输出错误
func (w *signatureCanonicalWriter) attribute(name xml.Name, value string) error {
	if err := w.write(" " + canonicalQName(name) + "=\""); err != nil {
		return err
	}
	if err := w.escaped(value, true); err != nil {
		return err
	}
	return w.write("\"")
}

// escaped 按C14N规则逐段转义文本或属性值
// 入参: value XML解析后的内容, attribute 是否为属性值
// 返回: error 输出或取消错误
func (w *signatureCanonicalWriter) escaped(value string, attribute bool) error {
	start := 0
	for i := range len(value) {
		escape := ""
		switch value[i] {
		case '&':
			escape = "&amp;"
		case '<':
			escape = "&lt;"
		case '>':
			if !attribute {
				escape = "&gt;"
			}
		case '"':
			if attribute {
				escape = "&quot;"
			}
		case '\t':
			if attribute {
				escape = "&#x9;"
			}
		case '\n':
			if attribute {
				escape = "&#xA;"
			}
		case '\r':
			escape = "&#xD;"
		}
		if escape != "" {
			if err := w.write(value[start:i]); err != nil {
				return err
			}
			if err := w.write(escape); err != nil {
				return err
			}
			start = i + 1
		}
	}
	return w.write(value[start:])
}

// misc 按处理指令或注释相对文档根的位置添加规范化换行
// 入参: value 完整标记
// 返回: error 输出错误
func (w *signatureCanonicalWriter) misc(value string) error {
	if len(w.path) == 0 && w.rootPassed {
		if err := w.write("\n"); err != nil {
			return err
		}
	}
	if err := w.write(value); err != nil {
		return err
	}
	if len(w.path) == 0 && !w.rootPassed {
		return w.write("\n")
	}
	return nil
}

// write 在统一输出预算及取消检查下写入规范化片段
// 入参: value 输出片段
// 返回: error 输出错误
func (w *signatureCanonicalWriter) write(value string) error {
	_, err := io.WriteString(&w.output, value)
	return err
}

// parseC14N11URI 按RFC3986校验并拆分URI，确保查询串和片段中的分隔符不误判为Scheme或Authority
// 入参: raw 原始URI文本
// 返回: c14n11URI 分解组件, error 非法URI语法错误
func parseC14N11URI(raw string) (c14n11URI, error) {
	if _, err := url.Parse(raw); err != nil {
		return c14n11URI{}, fmt.Errorf("%w: invalid C14N1.1 xml:base URI", ErrInvalid)
	}
	beforeFrag, _, _ := strings.Cut(raw, "#")
	head, query, hasQuery := strings.Cut(beforeFrag, "?")
	result := c14n11URI{hasQuery: hasQuery, query: query}
	rest := head
	if colon := strings.IndexByte(head, ':'); colon > 0 {
		candidate := head[:colon]
		validScheme := candidate[0] >= 'A' && candidate[0] <= 'Z' || candidate[0] >= 'a' && candidate[0] <= 'z'
		for i := 1; validScheme && i < len(candidate); i++ {
			c := candidate[i]
			validScheme = c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z' || c >= '0' && c <= '9' || c == '+' || c == '-' || c == '.'
		}
		if validScheme {
			result.scheme = candidate
			rest = head[colon+1:]
		}
	}
	if strings.HasPrefix(rest, "//") {
		result.hasAuth = true
		tail := rest[2:]
		if slash := strings.IndexByte(tail, '/'); slash >= 0 {
			result.authority = tail[:slash]
			result.path = tail[slash:]
		} else {
			result.authority = tail
		}
	} else {
		result.path = rest
	}
	return result, nil
}

// c14n11JoinURI 按C14N1.1附录A与RFC3986合并祖先及当前节点的xml:base URI
// 入参: base 基准URI, ref 待合并的相对或绝对URI
// 返回: string 合并规范化后的URI, error 非法URI语法错误
func c14n11JoinURI(base, ref string) (string, error) {
	baseURI, err := parseC14N11URI(base)
	if err != nil {
		return "", err
	}
	refURI, err := parseC14N11URI(ref)
	if err != nil {
		return "", err
	}
	var out c14n11URI
	if refURI.scheme != "" {
		out.scheme = refURI.scheme
		out.hasAuth = refURI.hasAuth
		out.authority = refURI.authority
		if refURI.hasAuth || strings.HasPrefix(refURI.path, "/") {
			out.path = c14n11RemoveDotSegments(refURI.path, true)
		} else {
			out.path = refURI.path
		}
		out.hasQuery, out.query = refURI.hasQuery, refURI.query
	} else {
		out.scheme = baseURI.scheme
		if refURI.hasAuth {
			out.hasAuth = true
			out.authority = refURI.authority
			out.path = c14n11RemoveDotSegments(refURI.path, out.scheme != "")
			out.hasQuery, out.query = refURI.hasQuery, refURI.query
		} else {
			out.hasAuth = baseURI.hasAuth
			out.authority = baseURI.authority
			if refURI.path == "" {
				out.path = baseURI.path
				if refURI.hasQuery {
					out.hasQuery, out.query = true, refURI.query
				} else {
					out.hasQuery, out.query = baseURI.hasQuery, baseURI.query
				}
			} else {
				if strings.HasPrefix(refURI.path, "/") {
					out.path = c14n11RemoveDotSegments(refURI.path, out.scheme != "" || out.hasAuth)
				} else {
					var merged string
					if out.hasAuth && baseURI.path == "" {
						merged = "/" + refURI.path
					} else if slash := strings.LastIndexByte(baseURI.path, '/'); slash >= 0 {
						merged = baseURI.path[:slash+1] + refURI.path
					} else {
						merged = refURI.path
					}
					out.path = c14n11RemoveDotSegments(merged, out.scheme != "" || out.hasAuth)
				}
				out.hasQuery, out.query = refURI.hasQuery, refURI.query
			}
		}
	}
	var builder strings.Builder
	if out.scheme != "" {
		builder.WriteString(out.scheme)
		builder.WriteByte(':')
	}
	if out.hasAuth {
		builder.WriteString("//")
		builder.WriteString(out.authority)
	}
	builder.WriteString(out.path)
	if out.hasQuery {
		builder.WriteByte('?')
		builder.WriteString(out.query)
	}
	return builder.String(), nil
}

// c14n11RemoveDotSegments 按C14N1.1附录A移除路径中的点段并在相对路径中保留必要上级段
// 入参: input 待化简路径, absolute 是否为绝对URI路径
// 返回: string 化简后的路径
func c14n11RemoveDotSegments(input string, absolute bool) string {
	absolute = absolute || strings.HasPrefix(input, "/")
	output := ""
	for input != "" {
		if strings.HasPrefix(input, "./") {
			input = input[2:]
		} else if strings.HasPrefix(input, "../") {
			if !absolute {
				output += "../"
			}
			input = input[3:]
		} else if strings.HasPrefix(input, "/./") {
			input = "/" + input[3:]
		} else if input == "/." {
			input = "/"
		} else if strings.HasPrefix(input, "/../") || input == "/.." {
			tail := ""
			if strings.HasPrefix(input, "/../") {
				tail = input[4:]
			}
			slash := strings.LastIndexByte(output, '/')
			last := output[slash+1:]
			if !absolute && (output == "" || last == "..") {
				if output == "" {
					output = ".."
				} else {
					output += "/.."
				}
				input = "/" + tail
			} else if slash >= 0 {
				output = output[:slash]
				input = "/" + tail
			} else {
				output = ""
				if !absolute {
					input = tail
				} else {
					input = "/" + tail
				}
			}
		} else if input == "." {
			input = ""
		} else if input == ".." {
			if !absolute {
				output += "../"
			}
			input = ""
		} else {
			start := 0
			if input[0] == '/' {
				start = 1
			}
			next := strings.IndexByte(input[start:], '/')
			if next < 0 {
				output += input
				input = ""
			} else {
				output += input[:start+next]
				input = input[start+next:]
			}
		}
	}
	if !absolute && (output == ".." || strings.HasSuffix(output, "/..")) {
		output += "/"
	}
	return output
}
