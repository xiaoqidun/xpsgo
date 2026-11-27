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
	"crypto"
	"crypto/dsa"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/asn1"
	"encoding/base64"
	"encoding/xml"
	"errors"
	"fmt"
	"io"
	"maps"
	"math"
	"math/big"
	"mime"
	"net/url"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"time"
)

// signatureDefinitionNumber 匹配xs:double的有限数值词法，不套用固定页面实数的额外限制
var signatureDefinitionNumber = regexp.MustCompile(`^[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?$`)

// SignatureSignOptions 设置签署标识、请求绑定、声明时间、算法、规范化与可选覆盖，Hash缺省时按密钥类型自动选择
// SpotID非空时须匹配文档SignatureDefinitions中的请求标识并自动用作Signature.Id，若同时提供ID须一致
// PSS非nil且签名器为RSA时采用RSASSA-PSS；SeparateCertificate为true时证书写入独立部件并建立证书关系
// SignCertificateParts在SeparateCertificate为true时自动将新建独立证书部件及证书关系纳入签名清单
// ProtectSignatures按类型组覆盖已有及本次签名关系；存在MCE或签署票据时须提供Validate校验原始内容
type SignatureSignOptions struct {
	ID                   string
	SpotID               string
	Time                 time.Time
	Hash                 crypto.Hash
	PSS                  *rsa.PSSOptions
	Canonicalization     string
	InclusiveNamespaces  []string
	SeparateCertificate  bool
	SignCertificateParts bool
	Parts                []string
	ProtectSignatures    bool
	Validate             func(context.Context, PartInfo, []byte) error
}

// SignatureDefinitionPart 保存签署请求及引用它的固定文档，不表示已经存在真实签名
type SignatureDefinitionPart struct {
	Part        PartInfo
	Documents   []string
	Definitions []SignatureDefinition
}

// SignatureDefinition 保存声明的签名位置及签署说明，字符串指针区分省略和空值
// ID为SpotID，不限定为GUID；SignBy保留UTC声明，不用于回溯证书有效性
type SignatureDefinition struct {
	ID              string
	SignerName      *string
	Language        *string
	Spot            *SignatureSpot
	Intent          *string
	SignBy          *string
	SigningLocation *string
}

// SignatureSpot 保存页面URI及位置声明，不访问外部URI或推断签名图形的大小
// 坐标按xs:double解析，可包含非有限值；实际显示前须判断位置是否可用
type SignatureSpot struct {
	PageURI string
	Start   Point
}

// Sign 按当前方言创建完整文档数字签名并保留已有签名，失败时不修改包状态；certificates须包含与signer匹配的证书
// 支持RSA、RSA-PSS、ECDSA及DSA签名器，DSA-SHA1与DSA-SHA256签名器分别须返回40或64字节r||s值，ECDSA签名器遵循crypto.Signer返回ASN.1签名
// 入参: ctx 取消Context，nil采用Background, signer 可用且调用期间不变的签名器, certificates 与签名器匹配的X509证书列表, options 可选签署参数，nil采用默认值
// 返回: PartInfo 新签名部件，失败为零值, error 结构、策略、算法、证书、签名器、预算或取消错误
func (p *Package) Sign(ctx context.Context, signer crypto.Signer, certificates []*x509.Certificate, options *SignatureSignOptions) (PartInfo, error) {
	if err := p.lock(); err != nil {
		return PartInfo{}, err
	}
	defer p.mu.Unlock()
	ctx = normalizeContext(ctx)
	if err := ctx.Err(); err != nil {
		return PartInfo{}, err
	}
	if signer == nil {
		return PartInfo{}, fmt.Errorf("%w: signing needs a signer", ErrInvalid)
	}
	configuration := SignatureSignOptions{}
	if options != nil {
		configuration = *options
		configuration.InclusiveNamespaces = slices.Clone(options.InclusiveNamespaces)
		configuration.Parts = slices.Clone(options.Parts)
		if options.PSS != nil {
			pssCopy := *options.PSS
			configuration.PSS = &pssCopy
		}
	}
	spotID := strings.Trim(configuration.SpotID, " \t\r\n")
	if configuration.SpotID != "" {
		if int64(len(spotID)) > p.limits.MaxMetadataBytes {
			return PartInfo{}, fmt.Errorf("%w: signing spot ID byte budget", ErrLimit)
		}
		if !xmlNCName(spotID) || spotID == "idPackageObject" || spotID == "idSignatureTime" {
			return PartInfo{}, fmt.Errorf("%w: signing spot ID", ErrInvalid)
		}
		if trimmedID := strings.Trim(configuration.ID, " \t\r\n"); trimmedID != "" && trimmedID != spotID {
			return PartInfo{}, fmt.Errorf("%w: signing ID conflicts with SpotID", ErrInvalid)
		}
		configuration.ID = spotID
	}
	if configuration.Canonicalization == "" {
		configuration.Canonicalization = signatureCanonical
	}
	if !signatureCanonicalMethod(configuration.Canonicalization) {
		return PartInfo{}, fmt.Errorf("%w: signing canonicalization method", ErrUnsupported)
	}
	if len(configuration.InclusiveNamespaces) != 0 {
		if !signatureCanonicalExclusive(configuration.Canonicalization) {
			return PartInfo{}, fmt.Errorf("%w: InclusiveNamespaces requires exclusive canonicalization", ErrInvalid)
		}
		for _, prefix := range configuration.InclusiveNamespaces {
			if prefix != "#default" && (!xmlNCName(prefix) || prefix == "xmlns") {
				return PartInfo{}, fmt.Errorf("%w: InclusiveNamespaces prefix %q", ErrInvalid, prefix)
			}
		}
	}
	public := signer.Public()
	method, digest, pssParams, signerOpts, err := signatureSigningMethod(public, configuration.Hash, configuration.PSS)
	if err != nil {
		return PartInfo{}, err
	}
	if err := signatureKey(method, public); err != nil {
		return PartInfo{}, err
	}
	derCertificates, err := signatureSigningCertificates(certificates, public, p.limits, ctx)
	if err != nil {
		return PartInfo{}, err
	}
	q := p.signingCopy()
	reader, err := q.reader(ctx)
	if err != nil {
		return PartInfo{}, err
	}
	defer reader.Close()
	origin, err := signatureSigningOrigin(reader, ctx)
	if err == nil && spotID != "" {
		err = signatureSigningSpot(reader, spotID, ctx)
	}
	if err == nil {
		err = signatureSigningMutableXML(reader, origin, configuration.Validate, ctx)
	}
	if err != nil {
		return PartInfo{}, err
	}
	if origin == "" {
		origin, err = q.newName("/Signatures/%d.psdsor", ctx)
		if err != nil {
			return PartInfo{}, err
		}
		if err := q.store(origin, opcSignatureOriginType, nil); err != nil {
			return PartInfo{}, err
		}
		q.commitName("/Signatures/%d.psdsor", origin)
		root := slices.Clone(q.relations["/"])
		nextID := createdRelationshipIDs(append(slices.Clone(root), q.originalRels["/"]...))
		root = append(root, Relationship{ID: nextID(), Type: opcSignatureOriginRel, Target: origin, TargetMode: TargetModeInternal})
		replaced := q.dirtyRels["/"]
		if err := q.setRelationships("/", root); err != nil {
			return PartInfo{}, err
		}
		q.dirtyRels["/"] = replaced
	}
	part, err := q.newName("/Signatures/%d.xml", ctx)
	if err != nil {
		return PartInfo{}, err
	}
	if configuration.ID == "" {
		configuration.ID = "Signature" + strings.TrimSuffix(strings.TrimPrefix(part, "/Signatures/"), ".xml")
	}
	configuration.ID = strings.Trim(configuration.ID, " \t\r\n")
	if int64(len(configuration.ID)) > q.limits.MaxMetadataBytes {
		return PartInfo{}, fmt.Errorf("%w: signing root ID byte budget", ErrLimit)
	}
	if !xmlNCName(configuration.ID) || configuration.ID == "idPackageObject" || configuration.ID == "idSignatureTime" {
		return PartInfo{}, fmt.Errorf("%w: signing root ID", ErrInvalid)
	}
	if configuration.Time.IsZero() {
		configuration.Time = time.Now()
	}
	if err := q.store(part, opcSignatureType, nil); err != nil {
		return PartInfo{}, err
	}
	q.commitName("/Signatures/%d.xml", part)
	relations := slices.Clone(q.relations[strings.ToLower(origin)])
	nextID := createdRelationshipIDs(append(slices.Clone(relations), q.originalRels[strings.ToLower(origin)]...))
	relations = append(relations, Relationship{ID: nextID(), Type: opcSignatureRel, Target: part, TargetMode: TargetModeInternal})
	replaced := q.dirtyRels[strings.ToLower(origin)]
	if err := q.setRelationships(origin, relations); err != nil {
		return PartInfo{}, err
	}
	q.dirtyRels[strings.ToLower(origin)] = replaced
	var certParts []string
	if configuration.SeparateCertificate {
		certRels := make([]Relationship, 0, len(derCertificates))
		certNextID := createdRelationshipIDs(nil)
		for _, der := range derCertificates {
			certPart, err := q.newName("/Signatures/%d.cer", ctx)
			if err != nil {
				return PartInfo{}, err
			}
			if err := q.store(certPart, opcCertificateType, der); err != nil {
				return PartInfo{}, err
			}
			q.commitName("/Signatures/%d.cer", certPart)
			certParts = append(certParts, certPart)
			certRels = append(certRels, Relationship{ID: certNextID(), Type: opcCertificateRel, Target: certPart, TargetMode: TargetModeInternal})
		}
		if err := q.setRelationships(part, certRels); err != nil {
			return PartInfo{}, err
		}
	}
	if err := q.signingParts(reader, origin, part, certParts, ctx); err != nil {
		return PartInfo{}, err
	}
	if configuration.SeparateCertificate && configuration.SignCertificateParts && len(certParts) != 0 {
		configuration.Parts = append(configuration.Parts, certParts...)
	}
	references, graph, err := signatureSigningReferences(reader, configuration, ctx)
	if err != nil {
		return PartInfo{}, err
	}
	data, err := encodeDocumentSignature(configuration, derCertificates, references, graph, method, digest, pssParams, signerOpts, signer)
	if err != nil {
		return PartInfo{}, err
	}
	if err := q.store(part, opcSignatureType, data); err != nil {
		return PartInfo{}, err
	}
	createdPut(reader.pkg, part, opcSignatureType, data)
	if err := q.validateSigningResult(reader.pkg, ctx); err != nil {
		return PartInfo{}, err
	}
	p.commitSigning(q)
	return PartInfo{Name: part, ContentType: opcSignatureType, Size: int64(len(data))}, nil
}

// validateSigningResult 在已有已校验快照上校验新增签名后的内容类型表、部件数量及包字节预算，避免全包重复解析与重哈希
// 入参: pkg 已同步写入新签名及关系的私有包读取器, ctx 取消Context
// 返回: error 部件数量、内容类型、资源上限或取消错误
func (p *Package) validateSigningResult(pkg *packageReader, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	types := createdNode(opcTypesNS, "Types")
	for _, key := range slices.Sorted(maps.Keys(pkg.parts)) {
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		child := createdNode(opcTypesNS, "Override")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "PartName"}, Value: pkg.names[key]}, {Name: xml.Name{Local: "ContentType"}, Value: pkg.overrides[key]}}
		types.Children = append(types.Children, child)
	}
	typesData, err := createdMarkup(types, p.limits, ctx)
	if err != nil {
		return err
	}
	createdPut(pkg, opcTypesName, "", typesData)
	if len(pkg.parts) > p.limits.MaxPartCount {
		return fmt.Errorf("%w: generated package part count", ErrLimit)
	}
	var total int64
	for _, key := range slices.Sorted(maps.Keys(pkg.data)) {
		raw := pkg.data[key]
		if int64(len(raw)) > p.limits.MaxPartBytes {
			return fmt.Errorf("%w: generated package byte budget", ErrLimit)
		}
		if int64(len(raw)) > p.limits.MaxPackageBytes-total {
			return fmt.Errorf("%w: generated package byte budget", ErrLimit)
		}
		total += int64(len(raw))
	}
	return checkContext(ctx)
}

// signingParts 向私有快照补入待签署部件、独立证书部件与签名源关系供覆盖清单及摘要计算使用
// 入参: reader 签署前的私有快照, origin 签名源部件, part 待签名部件, certificates 独立证书部件列表, ctx 取消Context
// 返回: error 部件、关系或取消错误
func (p *Package) signingParts(reader *Reader, origin, part string, certificates []string, ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	candidates := append([]string{origin, part}, certificates...)
	for _, name := range candidates {
		value, present := p.parts[strings.ToLower(name)]
		if !present {
			return fmt.Errorf("%w: missing signing candidate part", ErrInvalid)
		}
		createdPut(reader.pkg, value.name, value.media, value.data)
	}
	wanted := []Relationship{{Type: formatNamespace(p.format) + "/fixedrepresentation", Target: p.sequence, TargetMode: TargetModeInternal}}
	if err := p.composeRelationships(reader.pkg, "/", wanted, ctx); err != nil {
		return err
	}
	if err := p.composeRelationships(reader.pkg, origin, nil, ctx); err != nil {
		return err
	}
	if len(certificates) != 0 {
		if err := p.composeRelationships(reader.pkg, part, nil, ctx); err != nil {
			return err
		}
	}
	return checkContext(ctx)
}

// signingCopy 复制候选签署状态的可变索引，资源与原始部件继续共享不可变字节，不复制整个文件
// 返回: *Package 独立候选状态
func (p *Package) signingCopy() *Package {
	return &Package{
		format: p.format, limits: p.limits, sequence: p.sequence, documents: p.documents, pageCount: p.pageCount, maxImagePixels: p.maxImagePixels,
		parts: maps.Clone(p.parts), relations: maps.Clone(p.relations), relationSizes: maps.Clone(p.relationSizes), total: p.total,
		names: maps.Clone(p.names), layout: p.layout, parents: maps.Clone(p.parents), allocated: maps.Clone(p.allocated),
		original: p.original, originalRels: p.originalRels, comment: p.comment, dirty: maps.Clone(p.dirty), dirtyRels: maps.Clone(p.dirtyRels), deleted: maps.Clone(p.deleted), protected: p.protected,
	}
}

// signatureSigningMethod 确定XML签名方法、摘要及RSA-PSS签名参数，不以未知算法替换标准选择
// 入参: public 签名器公钥, hash 摘要选择，零值按密钥类型选择, pss 可选RSA-PSS参数
// 返回: string 签名方法URI, string 摘要方法URI, *SignaturePSSParams PSS参数, crypto.SignerOpts 签名器选项, error 算法或参数错误
func signatureSigningMethod(public crypto.PublicKey, hash crypto.Hash, pss *rsa.PSSOptions) (string, string, *SignaturePSSParams, crypto.SignerOpts, error) {
	method := ""
	switch key := public.(type) {
	case *rsa.PublicKey:
		if pss != nil {
			if err := signatureKey(signatureMethodRSAPSS, key); err != nil {
				return "", "", nil, nil, err
			}
			if pss.Hash != 0 {
				if hash != 0 && hash != pss.Hash {
					return "", "", nil, nil, fmt.Errorf("%w: RSA-PSS hash conflict", ErrInvalid)
				}
				hash = pss.Hash
			}
			if hash == 0 {
				hash = crypto.SHA256
			}
			digest := ""
			switch hash {
			case crypto.SHA1:
				digest = xmlSignatureNamespace + "sha1"
			case crypto.SHA256:
				digest = "http://www.w3.org/2001/04/xmlenc#sha256"
			case crypto.SHA384:
				digest = "http://www.w3.org/2001/04/xmldsig-more#sha384"
			case crypto.SHA512:
				digest = "http://www.w3.org/2001/04/xmlenc#sha512"
			default:
				return "", "", nil, nil, fmt.Errorf("%w: RSA-PSS hash algorithm", ErrUnsupported)
			}
			saltLen := pss.SaltLength
			if saltLen == rsa.PSSSaltLengthAuto || saltLen == rsa.PSSSaltLengthEqualsHash {
				saltLen = hash.Size()
			}
			emLen := (key.N.BitLen() - 1 + 7) / 8
			if saltLen <= 0 || emLen < hash.Size()+2 || saltLen > emLen-hash.Size()-2 {
				return "", "", nil, nil, fmt.Errorf("%w: RSA-PSS salt length", ErrInvalid)
			}
			params := &SignaturePSSParams{DigestMethod: digest, MGFMethod: signatureMethodMGF1, MGFDigest: digest, SaltLength: saltLen, TrailerField: 1}
			return signatureMethodRSAPSS, digest, params, &rsa.PSSOptions{SaltLength: saltLen, Hash: hash}, nil
		}
		if hash == 0 {
			hash = crypto.SHA256
		}
		switch hash {
		case crypto.SHA1:
			method = xmlSignatureNamespace + "rsa-sha1"
		case crypto.SHA256:
			method = "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"
		case crypto.SHA384:
			method = "http://www.w3.org/2001/04/xmldsig-more#rsa-sha384"
		case crypto.SHA512:
			method = "http://www.w3.org/2001/04/xmldsig-more#rsa-sha512"
		}
	case *ecdsa.PublicKey:
		if pss != nil {
			return "", "", nil, nil, fmt.Errorf("%w: RSA-PSS options require RSA key", ErrInvalid)
		}
		if key == nil || key.Curve == nil {
			return "", "", nil, nil, fmt.Errorf("%w: ECDSA signing key", ErrInvalid)
		}
		if hash == 0 {
			switch key.Curve {
			case elliptic.P256():
				hash = crypto.SHA256
			case elliptic.P384():
				hash = crypto.SHA384
			case elliptic.P521():
				hash = crypto.SHA512
			default:
				return "", "", nil, nil, fmt.Errorf("%w: ECDSA signing curve", ErrUnsupported)
			}
		}
		switch hash {
		case crypto.SHA256:
			method = signatureMethodECDSA256
		case crypto.SHA384:
			method = signatureMethodECDSA384
		case crypto.SHA512:
			method = signatureMethodECDSA512
		}
	case *dsa.PublicKey:
		if pss != nil {
			return "", "", nil, nil, fmt.Errorf("%w: RSA-PSS options require RSA key", ErrInvalid)
		}
		if hash == 0 {
			if key != nil && key.P != nil && key.Q != nil && key.Q.BitLen() == 256 && key.P.BitLen() >= 2048 {
				hash = crypto.SHA256
			} else if key == nil || key.Q == nil || key.Q.BitLen() == 160 {
				hash = crypto.SHA1
			}
		}
		switch hash {
		case crypto.SHA1:
			method = xmlSignatureNamespace + "dsa-sha1"
		case crypto.SHA256:
			method = signatureMethodDSA256
		}
	}
	if method == "" {
		return "", "", nil, nil, fmt.Errorf("%w: document signing key or hash", ErrUnsupported)
	}
	digest, err := signatureMethodHash(method)
	return method, digest, nil, hash, err
}

// signatureSigningCertificates 复制并校验调用方证书，确认存在与签名器匹配且可用于签署的证书
// 入参: input 证书列表, public 签名器公钥, limits 资源上限, ctx 取消Context
// 返回: [][]byte 独立DER列表, error 证书、用途、匹配、资源或取消错误
func signatureSigningCertificates(input []*x509.Certificate, public crypto.PublicKey, limits Limits, ctx context.Context) ([][]byte, error) {
	if len(input) == 0 {
		return nil, fmt.Errorf("%w: signing certificate count", ErrInvalid)
	}
	if len(input) > min(signatureMaxCertificates, limits.MaxPartCount) {
		return nil, fmt.Errorf("%w: signing certificate count", ErrLimit)
	}
	var result [][]byte
	var total int64
	matched := false
	for _, value := range input {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		if value == nil || len(value.Raw) == 0 {
			return nil, fmt.Errorf("%w: missing signing certificate DER", ErrInvalid)
		}
		if int64(len(value.Raw)) > limits.MaxMetadataBytes-total {
			return nil, fmt.Errorf("%w: signing certificate byte budget", ErrLimit)
		}
		der := slices.Clone(value.Raw)
		certificate, err := x509.ParseCertificate(der)
		if err != nil {
			return nil, fmt.Errorf("%w: signing certificate DER: %w", ErrInvalid, err)
		}
		match := false
		if key, ok := certificate.PublicKey.(interface{ Equal(crypto.PublicKey) bool }); ok {
			match = key.Equal(public)
		} else if key, ok := certificate.PublicKey.(*dsa.PublicKey); ok {
			if other, ok := public.(*dsa.PublicKey); ok {
				match = key.P.Cmp(other.P) == 0 && key.Q.Cmp(other.Q) == 0 && key.G.Cmp(other.G) == 0 && key.Y.Cmp(other.Y) == 0
			}
		}
		if match {
			if err := signatureCertificateUsage(certificate); err != nil {
				return nil, err
			}
			matched = true
		}
		total += int64(len(der))
		result = append(result, der)
	}
	if !matched {
		return nil, fmt.Errorf("%w: no certificate matches signing key", ErrInvalid)
	}
	return result, nil
}

// signatureSigningSpot 校验SpotID已在当前包的固定文档SignatureDefinitions中定义
// 入参: reader 当前候选快照, spotID 已规范化的签署请求标识, ctx 取消Context
// 返回: error 请求缺失、关联、模式、资源或取消错误
func signatureSigningSpot(reader *Reader, spotID string, ctx context.Context) error {
	parts, err := reader.SignatureDefinitions(ctx)
	if err != nil {
		return err
	}
	for _, part := range parts {
		for _, definition := range part.Definitions {
			if definition.ID == spotID {
				return nil
			}
		}
	}
	return fmt.Errorf("%w: signature spot ID %q is not defined in document SignatureDefinitions", ErrInvalid, spotID)
}

// AddSignatureDefinitions 将签署请求编码为独立部件并关联至指定固定文档，自动避开已有路径并校验全局SpotID唯一
// 失败时不修改包状态，不自动创建数字签名
// 入参: ctx 取消Context，nil采用Background, docIndex 从零开始的固定文档序号, definitions 非空签署请求列表
// 返回: PartInfo 新建的签名定义部件信息，失败为零值, error 序号、模型、重复标识、资源或取消错误
func (p *Package) AddSignatureDefinitions(ctx context.Context, docIndex int, definitions []SignatureDefinition) (PartInfo, error) {
	ctx = normalizeContext(ctx)
	if err := p.lock(); err != nil {
		return PartInfo{}, err
	}
	defer p.mu.Unlock()
	if err := ctx.Err(); err != nil {
		return PartInfo{}, err
	}
	if docIndex < 0 || docIndex >= len(p.documents) || len(definitions) == 0 {
		return PartInfo{}, fmt.Errorf("%w: signature definition document index or empty requests", ErrInvalid)
	}
	var encoded bytes.Buffer
	if _, err := EncodeSignatureDefinitions(ctx, &encoded, definitions, &EncodeOptions{Format: p.format, Limits: p.limits}); err != nil {
		return PartInfo{}, err
	}
	q := p.signingCopy()
	part, err := q.newName("/Metadata/SignatureDefinitions_%d.xml", ctx)
	if err != nil {
		return PartInfo{}, err
	}
	media := fixedContentType("signaturedefinitions")
	if err := q.store(part, media, encoded.Bytes()); err != nil {
		return PartInfo{}, err
	}
	q.commitName("/Metadata/SignatureDefinitions_%d.xml", part)
	source := q.documents[docIndex].Part
	key := strings.ToLower(source)
	relations := slices.Clone(q.relations[key])
	nextID := createdRelationshipIDs(append(slices.Clone(relations), q.originalRels[key]...))
	relations = append(relations, Relationship{ID: nextID(), Type: formatNamespace(q.format) + "/signature-definitions", Target: part, TargetMode: TargetModeInternal})
	if err := q.setRelationships(source, relations); err != nil {
		return PartInfo{}, err
	}
	view, err := q.reader(ctx)
	if err != nil {
		return PartInfo{}, err
	}
	_ = view.Close()
	if err := ctx.Err(); err != nil {
		return PartInfo{}, err
	}
	p.parts, p.relations, p.relationSizes, p.total = q.parts, q.relations, q.relationSizes, q.total
	p.names, p.parents, p.allocated, p.dirty, p.dirtyRels = q.names, q.parents, q.allocated, q.dirty, q.dirtyRels
	return PartInfo{Name: part, ContentType: media, Size: int64(encoded.Len())}, nil
}

// signatureSigningOrigin 检查原有签名关联并返回唯一签名源，不改写或移除已有签名
// 入参: reader 当前候选快照, ctx 取消Context
// 返回: string 原有签名源URI，无签名源时为空, error 关联、资源或取消错误
func signatureSigningOrigin(reader *Reader, ctx context.Context) (string, error) {
	if _, err := reader.SignatureParts(ctx); err != nil {
		return "", err
	}
	for key := range reader.pkg.parts {
		if err := ctx.Err(); err != nil {
			return "", err
		}
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := reader.pkg.contentType(key)
		if err != nil {
			return "", err
		}
		if strings.EqualFold(media, opcSignatureOriginType) {
			return reader.pkg.names[key], nil
		}
	}
	return "", nil
}

// encodeDocumentSignature 编码标准包专用对象，计算原始部件、关系筛选及对象摘要后调用签名器
// 入参: options 签署选项, certificates 独立DER, references 包部件引用, graph 私有读取预算, method 签名URI, digest 摘要URI, pss 可选RSA-PSS参数, signerOpts 签名器选项, signer 外部签名器
// 返回: []byte 完整UTF-8签名XML, error 结构、摘要、签名器、资源或取消错误
func encodeDocumentSignature(options SignatureSignOptions, certificates [][]byte, references []SignatureReference, graph *signaturePartGraph, method, digest string, pss *SignaturePSSParams, signerOpts crypto.SignerOpts, signer crypto.Signer) ([]byte, error) {
	ctx, limits := graph.context, graph.pkg.limits
	root := createdNode(xmlSignatureNamespace, "Signature")
	root.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: xmlSignatureNamespace}, {Name: xml.Name{Local: "Id"}, Value: options.ID}}
	info := createdNode(xmlSignatureNamespace, "SignedInfo")
	canonicalization := signatureSigningCanonicalNode("CanonicalizationMethod", options.Canonicalization, options.InclusiveNamespaces)
	signatureMethod := signatureSigningMethodNode(method, pss)
	objectReference := signatureSigningNode("Reference", "URI", "#"+url.PathEscape("idPackageObject"))
	objectReference.Attr = append(objectReference.Attr, xml.Attr{Name: xml.Name{Local: "Type"}, Value: xmlSignatureNamespace + "Object"})
	objectReference.Children = []*xmlElement{signatureSigningTransforms([]SignatureTransform{{Algorithm: options.Canonicalization, InclusiveNamespaces: options.InclusiveNamespaces}}), signatureSigningNode("DigestMethod", "Algorithm", digest), signatureSigningText("DigestValue", "AA==")}
	info.Children = []*xmlElement{canonicalization, signatureMethod, objectReference}
	value := signatureSigningText("SignatureValue", "AA==")
	object := signatureSigningNode("Object", "Id", "idPackageObject")
	manifest := createdNode(xmlSignatureNamespace, "Manifest")
	v := signatureVerifier{graph: graph, limits: limits, work: limits.MaxPackageBytes}
	for _, reference := range references {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		reference.DigestMethod = digest
		computed, err := v.computePartDigest(reference)
		if err != nil {
			return nil, &PartError{Part: reference.Part, Err: err}
		}
		node := signatureSigningNode("Reference", "URI", reference.URI)
		if len(reference.Transforms) != 0 {
			node.Children = append(node.Children, signatureSigningTransforms(reference.Transforms))
		}
		node.Children = append(node.Children, signatureSigningNode("DigestMethod", "Algorithm", digest), signatureSigningText("DigestValue", base64.StdEncoding.EncodeToString(computed)))
		manifest.Children = append(manifest.Children, node)
	}
	properties := createdNode(xmlSignatureNamespace, "SignatureProperties")
	property := signatureSigningNode("SignatureProperty", "Id", "idSignatureTime")
	property.Attr = append(property.Attr, xml.Attr{Name: xml.Name{Local: "Target"}, Value: "#" + url.PathEscape(options.ID)})
	stamp := createdNode(opcSignatureNamespace, "SignatureTime")
	stamp.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: opcSignatureNamespace}}
	format, date := createdNode(opcSignatureNamespace, "Format"), createdNode(opcSignatureNamespace, "Value")
	format.Text, date.Text = "YYYY-MM-DDThh:mm:ssTZD", options.Time.UTC().Format("2006-01-02T15:04:05Z")
	if !signatureTimeValue(format.Text, date.Text) {
		return nil, fmt.Errorf("%w: signing time", ErrInvalid)
	}
	stamp.Children = []*xmlElement{format, date}
	property.Children = []*xmlElement{stamp}
	properties.Children = []*xmlElement{property}
	object.Children = []*xmlElement{manifest, properties}
	if options.SeparateCertificate {
		root.Children = []*xmlElement{info, value, object}
	} else {
		keyInfo := createdNode(xmlSignatureNamespace, "KeyInfo")
		x509Data := createdNode(xmlSignatureNamespace, "X509Data")
		for _, certificate := range certificates {
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			x509Data.Children = append(x509Data.Children, signatureSigningText("X509Certificate", base64.StdEncoding.EncodeToString(certificate)))
		}
		keyInfo.Children = []*xmlElement{x509Data}
		root.Children = []*xmlElement{info, value, keyInfo, object}
	}
	ancestors := []*xmlElement{root}
	canonicalOpts := canonicalXMLOptions{
		limits:    limits,
		maxBytes:  limits.MaxMetadataBytes,
		comments:  false,
		exclusive: signatureCanonicalExclusive(options.Canonicalization),
		version11: options.Canonicalization == signatureCanonical11 || options.Canonicalization == signatureComments11,
		inclusive: signatureInclusiveSet(options.InclusiveNamespaces),
		context:   ctx,
	}
	canonical, err := canonicalXMLElement(ancestors, object, canonicalOpts)
	if err != nil {
		return nil, err
	}
	if err := v.charge(int64(len(canonical))); err != nil {
		return nil, err
	}
	hasher, _, err := signatureHash(digest)
	if err != nil {
		return nil, err
	}
	if err := signatureHashBytes(ctx, hasher, canonical); err != nil {
		return nil, err
	}
	objectReference.Children[len(objectReference.Children)-1].Text = base64.StdEncoding.EncodeToString(hasher.Sum(nil))
	canonicalOpts.comments = signatureCanonicalComments(options.Canonicalization)
	canonical, err = canonicalXMLElement(ancestors, info, canonicalOpts)
	if err != nil {
		return nil, err
	}
	if err := v.charge(int64(len(canonical))); err != nil {
		return nil, err
	}
	hasher.Reset()
	if err := signatureHashBytes(ctx, hasher, canonical); err != nil {
		return nil, err
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	signed, err := signer.Sign(rand.Reader, hasher.Sum(nil), signerOpts)
	if err != nil {
		return nil, fmt.Errorf("signing provider: %w", err)
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if public, ok := signer.Public().(*ecdsa.PublicKey); ok {
		var pair struct {
			R, S *big.Int
		}
		rest, err := asn1.Unmarshal(signed, &pair)
		if err != nil || len(rest) != 0 || pair.R == nil || pair.S == nil || pair.R.Sign() <= 0 || pair.S.Sign() <= 0 || pair.R.Cmp(public.Curve.Params().N) >= 0 || pair.S.Cmp(public.Curve.Params().N) >= 0 {
			return nil, fmt.Errorf("%w: signing provider ECDSA value", ErrSignature)
		}
		nBytes := (public.Curve.Params().BitSize + 7) / 8
		encoded := make([]byte, 2*nBytes)
		pair.R.FillBytes(encoded[:nBytes])
		pair.S.FillBytes(encoded[nBytes:])
		signed = encoded
	}
	if len(signed) > signatureMaxKeyBits/8 || int64(len(signed)) > limits.MaxMetadataBytes {
		return nil, fmt.Errorf("%w: signing provider value size", ErrLimit)
	}
	if err := verifySignatureValueParams(ctx, method, pss, signer.Public(), canonical, signed); err != nil {
		return nil, err
	}
	value.Text = base64.StdEncoding.EncodeToString(signed)
	return signatureSigningMarkup(root, limits, ctx)
}

// signatureSigningCanonicalNode 创建规范化元素并在Exclusive C14N存在前缀列表时附加InclusiveNamespaces子元素
// 入参: name 元素名称, algorithm 规范化算法URI, inclusive 可选前缀列表
// 返回: *xmlElement 独立规范化元素节点
func signatureSigningCanonicalNode(name, algorithm string, inclusive []string) *xmlElement {
	node := signatureSigningNode(name, "Algorithm", algorithm)
	if signatureCanonicalExclusive(algorithm) && len(inclusive) != 0 {
		child := createdNode(signatureExcNamespace, "InclusiveNamespaces")
		child.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: signatureExcNamespace}, {Name: xml.Name{Local: "PrefixList"}, Value: strings.Join(inclusive, " ")}}
		node.Children = append(node.Children, child)
	}
	return node
}

// signatureSigningMethodNode 创建SignatureMethod元素并在RSA-PSS时编码标准RSAPSSParams参数结构
// 入参: method 签名方法URI, pss 可选RSA-PSS参数
// 返回: *xmlElement 独立签名方法节点
func signatureSigningMethodNode(method string, pss *SignaturePSSParams) *xmlElement {
	node := signatureSigningNode("SignatureMethod", "Algorithm", method)
	if method != signatureMethodRSAPSS || pss == nil {
		return node
	}
	params := createdNode(signaturePSSNamespace, "RSAPSSParams")
	params.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: signaturePSSNamespace}}
	digestNode := createdNode(xmlSignatureNamespace, "DigestMethod")
	digestNode.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: xmlSignatureNamespace}, {Name: xml.Name{Local: "Algorithm"}, Value: pss.DigestMethod}}
	mgfNode := createdNode(signaturePSSNamespace, "MaskGenerationFunction")
	mgfNode.Attr = []xml.Attr{{Name: xml.Name{Local: "Algorithm"}, Value: pss.MGFMethod}}
	mgfDigest := createdNode(xmlSignatureNamespace, "DigestMethod")
	mgfDigest.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: xmlSignatureNamespace}, {Name: xml.Name{Local: "Algorithm"}, Value: pss.MGFDigest}}
	mgfNode.Children = []*xmlElement{mgfDigest}
	saltNode := createdNode(signaturePSSNamespace, "SaltLength")
	saltNode.Text = strconv.Itoa(pss.SaltLength)
	trailerNode := createdNode(signaturePSSNamespace, "TrailerField")
	trailerNode.Text = strconv.Itoa(pss.TrailerField)
	params.Children = []*xmlElement{digestNode, mgfNode, saltNode, trailerNode}
	node.Children = []*xmlElement{params}
	return node
}

// signatureSigningMarkup 单遍紧凑编码自生成签名XML并直接闭合空元素，消除中间编码与词元回扫
// 入参: root 生成节点, limits XML及输出上限, ctx 取消Context
// 返回: []byte UTF-8签名XML, error 编码、资源或取消错误
func signatureSigningMarkup(root *xmlElement, limits Limits, ctx context.Context) ([]byte, error) {
	limit := min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes)
	var output bytes.Buffer
	counted := packageOutput{writer: &output, context: ctx, limit: limit}
	nodes := 0
	var writeNode func(*xmlElement, int) error
	writeNode = func(node *xmlElement, depth int) error {
		if err := checkContext(ctx); err != nil {
			return err
		}
		nodes++
		if nodes > limits.MaxXMLNodes || depth > limits.MaxXMLDepth {
			return fmt.Errorf("%w: generated XML complexity", ErrLimit)
		}
		if !xmlTextValid(node.Text) || len(node.Children) != 0 && !xmlWhitespace(node.Text) {
			return fmt.Errorf("%w: invalid or ambiguous generated XML text", ErrInvalid)
		}
		if _, err := io.WriteString(&counted, "<"+node.Name.Local); err != nil {
			return err
		}
		for _, attr := range node.Attr {
			if !xmlTextValid(attr.Value) {
				return fmt.Errorf("%w: invalid generated XML attribute", ErrInvalid)
			}
			if _, err := io.WriteString(&counted, " "+attr.Name.Local+`="`); err != nil {
				return err
			}
			if err := xml.EscapeText(&counted, []byte(attr.Value)); err != nil {
				return err
			}
			if _, err := io.WriteString(&counted, `"`); err != nil {
				return err
			}
		}
		if len(node.Children) == 0 && node.Text == "" {
			_, err := io.WriteString(&counted, "/>")
			return err
		}
		if _, err := io.WriteString(&counted, ">"); err != nil {
			return err
		}
		if node.Text != "" {
			if err := xml.EscapeText(&counted, []byte(node.Text)); err != nil {
				return err
			}
		}
		for _, child := range node.Children {
			if err := writeNode(child, depth+1); err != nil {
				return err
			}
		}
		_, err := io.WriteString(&counted, "</"+node.Name.Local+">")
		return err
	}
	if err := writeNode(root, 1); err != nil {
		return nil, err
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return output.Bytes(), nil
}

// signatureSigningNode 创建XML签名元素及一个无命名空间属性，不手工拼接未转义输入
// 入参: name 元素名称, attribute 属性名称, value 属性值
// 返回: *xmlElement 独立节点
func signatureSigningNode(name, attribute, value string) *xmlElement {
	node := createdNode(xmlSignatureNamespace, name)
	node.Attr = []xml.Attr{{Name: xml.Name{Local: attribute}, Value: value}}
	return node
}

// signatureSigningText 创建XML签名的标量元素，实际字符及预算由编码器检查
// 入参: name 元素名称, text 标量内容
// 返回: *xmlElement 独立节点
func signatureSigningText(name, text string) *xmlElement {
	node := createdNode(xmlSignatureNamespace, name)
	node.Text = text
	return node
}

// signatureSigningTransforms 按顺序构造关系筛选及规范化变换，不补造关系ID或目标模式
// 入参: transforms 已确定的变换
// 返回: *xmlElement 独立变换容器
func signatureSigningTransforms(transforms []SignatureTransform) *xmlElement {
	root := createdNode(xmlSignatureNamespace, "Transforms")
	for _, transform := range transforms {
		node := signatureSigningCanonicalNode("Transform", transform.Algorithm, transform.InclusiveNamespaces)
		for _, kind := range transform.RelationshipTypes {
			filter := createdNode(opcSignatureNamespace, "RelationshipsGroupReference")
			filter.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: opcSignatureNamespace}, {Name: xml.Name{Local: "SourceType"}, Value: kind}}
			node.Children = append(node.Children, filter)
		}
		for _, id := range transform.RelationshipIDs {
			filter := createdNode(opcSignatureNamespace, "RelationshipReference")
			filter.Attr = []xml.Attr{{Name: xml.Name{Local: "xmlns"}, Value: opcSignatureNamespace}, {Name: xml.Name{Local: "SourceId"}, Value: id}}
			node.Children = append(node.Children, filter)
		}
		root.Children = append(root.Children, node)
	}
	return root
}

// signatureSigningReferences 生成单次签署的完整覆盖引用清单并校验可选额外部件
// 入参: reader 候选快照, options 签署选项, ctx 取消Context
// 返回: []SignatureReference 有序引用, *signaturePartGraph 私有累计读取预算, error 策略、目标、资源或取消错误
func signatureSigningReferences(reader *Reader, options SignatureSignOptions, ctx context.Context) ([]SignatureReference, *signaturePartGraph, error) {
	g := &signaturePartGraph{context: ctx, remaining: reader.limits.MaxPackageBytes}
	pkg := *reader.pkg
	pkg.beforeRead, g.pkg = g.readAllowance, &pkg
	c := signatureCoverageGraph{
		graph: g, format: reader.format, owners: make(map[string]string), parts: make(map[string]bool), required: make(map[string]bool),
		relations: make(map[signatureCoverageKey]SignatureRelationship), modes: make(map[signatureCoverageKey]int), targets: make(map[signatureCoverageKey]string), bySource: make(map[string][]Relationship),
	}
	if err := c.collect(reader); err != nil {
		return nil, nil, err
	}
	if len(options.Parts) > reader.limits.MaxPartCount {
		return nil, nil, fmt.Errorf("%w: optional signed part count", ErrLimit)
	}
	signed := make(map[string]bool, len(c.required)+len(options.Parts))
	for key := range c.required {
		signed[key] = true
	}
	for _, part := range options.Parts {
		if err := ctx.Err(); err != nil {
			return nil, nil, err
		}
		name, err := opcPartName(part)
		if err != nil {
			return nil, nil, err
		}
		key := strings.ToLower(name)
		if !c.parts[key] {
			return nil, nil, fmt.Errorf("%w: part %s is outside document signing policy", ErrInvalid, name)
		}
		signed[key] = true
	}
	var result []SignatureReference
	for _, key := range slices.Sorted(maps.Keys(signed)) {
		media, err := pkg.contentType(key)
		if err != nil {
			return nil, nil, err
		}
		name := pkg.names[key]
		if err := signatureSigningXML(g, name, media, signatureSigningTicket(c, key), options.Validate); err != nil {
			return nil, nil, err
		}
		result = append(result, SignatureReference{URI: signatureSigningURI(name, media), Part: name, ContentType: media})
	}
	type signatureRelationGroup struct {
		source string
		typ    string
	}
	totals := make(map[signatureRelationGroup]int)
	included := make(map[signatureRelationGroup][]string)
	groupEligible := make(map[signatureRelationGroup]bool)
	for key, relationship := range c.relations {
		if err := ctx.Err(); err != nil {
			return nil, nil, err
		}
		group := signatureRelationGroup{source: key.source, typ: relationship.Relationship.Type}
		totals[group]++
		mode := c.modes[key]
		include := mode == signatureCoverageRequiredPart || mode == signatureCoverageRequiredRelationship || mode == signatureCoverageOptionalPart && signed[c.targets[key]]
		if !include && !(mode == signatureCoverageGroup && options.ProtectSignatures) {
			continue
		}
		if _, exists := groupEligible[group]; !exists {
			groupEligible[group] = true
		}
		if mode == signatureCoverageOptionalPart {
			groupEligible[group] = false
		}
		included[group] = append(included[group], relationship.Relationship.ID)
	}
	bySource := make(map[string]SignatureTransform)
	for group, ids := range included {
		if err := ctx.Err(); err != nil {
			return nil, nil, err
		}
		transform := bySource[group.source]
		transform.Algorithm = signatureRelationships
		if groupEligible[group] && len(ids) == totals[group] {
			if !slices.Contains(transform.RelationshipTypes, group.typ) {
				transform.RelationshipTypes = append(transform.RelationshipTypes, group.typ)
			}
		} else {
			transform.RelationshipIDs = append(transform.RelationshipIDs, ids...)
		}
		bySource[group.source] = transform
	}
	for _, source := range slices.Sorted(maps.Keys(bySource)) {
		name := createdRelationshipPart(source)
		name = pkg.names[strings.ToLower(name)]
		transform := bySource[source]
		slices.Sort(transform.RelationshipTypes)
		slices.Sort(transform.RelationshipIDs)
		if err := signatureSigningXML(g, name, opcRelsType, false, options.Validate); err != nil {
			return nil, nil, err
		}
		result = append(result, SignatureReference{URI: signatureSigningURI(name, opcRelsType), Part: name, ContentType: opcRelsType, Transforms: []SignatureTransform{transform, {Algorithm: options.Canonicalization, InclusiveNamespaces: slices.Clone(options.InclusiveNamespaces)}}})
	}
	if err := ctx.Err(); err != nil {
		return nil, nil, err
	}
	return result, g, nil
}

// signatureSigningURI 按OPC引用语法保留内容类型的斜杠，只转义URI所需字符而不按表单查询处理加号
// 入参: part 部件URI, media 声明内容类型
// 返回: string 含ContentType的签名引用
func signatureSigningURI(part, media string) string {
	return part + "?ContentType=" + strings.ReplaceAll(url.PathEscape(media), "%2F", "/")
}

// signatureSigningTicket 判断所选目标是否具有当前方言的票据关联或标准打印票据媒体类型，不猜测私有票据
// 入参: graph 覆盖图, part 规范化的小写部件键
// 返回: bool 是否需要调用方声明完整理解票据
func signatureSigningTicket(graph signatureCoverageGraph, part string) bool {
	for key, target := range graph.targets {
		if target == part && graph.relations[key].Relationship.Type == formatNamespace(graph.format)+"/printticket" {
			return true
		}
	}
	media, _ := graph.graph.pkg.contentType(part)
	known, capabilities := printResourceMedia(media)
	return known && !capabilities
}

// signatureSigningXML 检查XML编码及MCE存在性，需要扩展或票据理解时将独立字节交由校验器确认
// 入参: graph 私有读取预算, part 部件URI, media 内容类型, ticket 是否为票据, validate 调用方完整理解校验器
// 返回: error XML、理解策略、校验器、资源或取消错误
func signatureSigningXML(graph *signaturePartGraph, part, media string, ticket bool, validate func(context.Context, PartInfo, []byte) error) error {
	typeName, _, err := mime.ParseMediaType(media)
	if err != nil {
		return fmt.Errorf("%w: signed part media: %w", ErrInvalid, err)
	}
	xmlPart := compositionXML(typeName)
	if !xmlPart && !ticket {
		return graph.context.Err()
	}
	key := strings.ToLower(part)
	limit := signaturePartByteLimit(part, typeName, graph.pkg.limits)
	if ticket {
		limit = min(limit, graph.pkg.limits.MaxMetadataBytes)
	}
	data, err := graph.pkg.readItems(key, limit)
	if err != nil {
		return &PartError{Part: part, Err: err}
	}
	compatibility := false
	if xmlPart {
		_, err = decodeXMLVisit(data, graph.pkg.limits, func(token xml.Token, node *xmlElement) error {
			if err := graph.context.Err(); err != nil {
				return err
			}
			if _, start := token.(xml.StartElement); start {
				for _, attribute := range node.Attr {
					if (attribute.Name.Space == xmlnsNamespace || attribute.Name == (xml.Name{Local: "xmlns"})) && attribute.Value == mcNamespace {
						compatibility = true
					}
				}
			}
			return nil
		})
		if err != nil {
			return &PartError{Part: part, Err: err}
		}
	}
	if validate == nil {
		if compatibility || ticket {
			return &PartError{Part: part, Err: fmt.Errorf("%w: signing requires complete MCE or PrintTicket understanding", ErrUnsupported)}
		}
		return graph.context.Err()
	}
	if err := validate(graph.context, PartInfo{Name: part, ContentType: media, Size: int64(len(data))}, slices.Clone(data)); err != nil {
		return &PartError{Part: part, Err: err}
	}
	return graph.context.Err()
}

// signatureSigningMutableXML 在修改签名源关联前检查原始MCE，避免重建关系后漏掉理解要求
// 入参: reader 原始候选快照, origin 已有签名源URI，空值表示尚未创建, validate 原始内容校验器, ctx 取消Context
// 返回: error 理解策略、校验器、资源或取消错误
func signatureSigningMutableXML(reader *Reader, origin string, validate func(context.Context, PartInfo, []byte) error, ctx context.Context) error {
	graph := &signaturePartGraph{context: ctx, remaining: reader.limits.MaxPackageBytes}
	pkg := *reader.pkg
	pkg.beforeRead, graph.pkg = graph.readAllowance, &pkg
	parts := []string{"/_rels/.rels"}
	if origin != "" {
		name := createdRelationshipPart(origin)
		if _, exists := pkg.parts[strings.ToLower(name)]; exists {
			parts = append(parts, pkg.names[strings.ToLower(name)])
		}
	}
	for _, part := range parts {
		if err := signatureSigningXML(graph, part, opcRelsType, false, validate); err != nil {
			return err
		}
	}
	return ctx.Err()
}

// SignatureDefinitions 读取固定文档关联的签署请求，合并同一部件的引用并检查请求标识全局唯一
// 只读取固定布局关联，不把请求或相同标识视为已经验证的数字签名
// 入参: ctx 取消Context，nil采用Background
// 返回: []SignatureDefinitionPart 独立请求部件，未关联时为空, error 关联、模式、预算、关闭或取消错误
func (r *Reader) SignatureDefinitions(ctx context.Context) ([]SignatureDefinitionPart, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	g := signaturePartGraph{context: ctx, remaining: r.limits.MaxPackageBytes}
	pkg := *r.pkg
	pkg.beforeRead, g.pkg = g.readAllowance, &pkg
	return g.definitions(r.documents, r.format, r.limits)
}

// definitions 在单次操作的累计预算内读取固定文档的签署请求，不创建独立或重复的读取预算
// 入参: documents 固定文档索引, format 文档格式, limits 请求解析上限
// 返回: []SignatureDefinitionPart 独立请求部件, error 关联、模式、资源或取消错误
func (g *signaturePartGraph) definitions(documents []Document, format Format, limits Limits) ([]SignatureDefinitionPart, error) {
	pkg, ctx := g.pkg, g.context
	namespace := formatNamespace(format) + "/signature-definitions"
	seen := make(map[string]int)
	ids := make(map[string]bool)
	var result []SignatureDefinitionPart
	for _, document := range documents {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		relations, err := pkg.relationships(document.Part)
		if err != nil {
			return nil, err
		}
		for _, relation := range relations {
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			if relation.Type != namespace {
				continue
			}
			part, err := g.target(document.Part, relation, fixedContentType("signaturedefinitions"))
			if err != nil {
				return nil, err
			}
			key := strings.ToLower(part.Name)
			if index, found := seen[key]; found {
				if !strings.EqualFold(result[index].Documents[len(result[index].Documents)-1], document.Part) {
					result[index].Documents = append(result[index].Documents, document.Part)
				}
				continue
			}
			data, err := pkg.readItems(key, min(limits.MaxPartBytes, limits.MaxMetadataBytes))
			if err != nil {
				return nil, &PartError{Part: part.Name, Err: err}
			}
			definitions, err := readSignatureDefinitions(data, namespace, limits, ctx)
			if err != nil {
				return nil, &PartError{Part: part.Name, Element: "SignatureDefinitions", Err: err}
			}
			for _, definition := range definitions {
				if len(ids) >= limits.MaxXMLNodes {
					return nil, fmt.Errorf("%w: global signature definition count", ErrLimit)
				}
				if ids[definition.ID] {
					return nil, &PartError{Part: part.Name, Err: fmt.Errorf("%w: duplicate global signature spot ID %q", ErrInvalid, definition.ID)}
				}
				ids[definition.ID] = true
			}
			seen[key] = len(result)
			result = append(result, SignatureDefinitionPart{Part: part, Documents: []string{document.Part}, Definitions: definitions})
		}
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return result, nil
}

// readSignatureDefinitions 检查两套正式模式共有的顺序、标识及字段规则，不截断签署意图
// 入参: data XML字节, namespace 对应格式命名空间, limits XML上限, ctx 取消Context
// 返回: []SignatureDefinition 独立请求, error XML、模式、资源或取消错误
func readSignatureDefinitions(data []byte, namespace string, limits Limits, ctx context.Context) ([]SignatureDefinition, error) {
	if int64(len(data)) > min(limits.MaxMetadataBytes, limits.MaxPartBytes, limits.MaxPackageBytes) {
		return nil, fmt.Errorf("%w: signature definition bytes", ErrLimit)
	}
	root, content, err := decodeXMLContent(data, limits, ctx)
	if err != nil {
		return nil, err
	}
	processor := compatibilityProcessor{understood: map[string]bool{namespace: true, mcNamespace: true, xmlNamespace: true}, content: content.nodes, context: ctx}
	fragment, err := processor.element(root, compatibilityScope{})
	if err != nil {
		return nil, err
	}
	if len(fragment.elements) != 1 || !xmlWhitespace(fragment.text) {
		return nil, fmt.Errorf("%w: signature definition root", ErrInvalid)
	}
	root = fragment.elements[0]
	if root.Name != (xml.Name{Space: namespace, Local: "SignatureDefinitions"}) || len(root.Children) == 0 {
		return nil, fmt.Errorf("%w: signature definition root or empty requests", ErrInvalid)
	}
	if _, err := structureAttributes(root, namespace); err != nil {
		return nil, err
	}
	ids := make(map[string]bool)
	var result []SignatureDefinition
	for _, node := range root.Children {
		if err := checkContext(ctx); err != nil {
			return nil, err
		}
		definition, err := parseSignatureDefinition(node, namespace)
		if err != nil {
			return nil, err
		}
		if ids[definition.ID] {
			return nil, fmt.Errorf("%w: duplicate signature spot ID", ErrInvalid)
		}
		ids[definition.ID] = true
		result = append(result, definition)
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// parseSignatureDefinition 读取单个签署请求，严格区分字符串、XML标识、UTC期限与位置数值
// 入参: node 已完成MCE的请求节点, namespace 格式命名空间
// 返回: SignatureDefinition 请求, error 模式或值错误
func parseSignatureDefinition(node *xmlElement, namespace string) (SignatureDefinition, error) {
	var result SignatureDefinition
	if node.Name.Local != "SignatureDefinition" {
		return result, fmt.Errorf("%w: expected signature definition", ErrInvalid)
	}
	attrs, err := structureAttributes(node, namespace, "SpotID", "SignerName", "xml:lang")
	if err != nil {
		return result, err
	}
	result.ID = strings.Trim(attrs["SpotID"], " \t\r\n")
	if !xmlNCName(result.ID) {
		return result, fmt.Errorf("%w: signature spot XML ID", ErrInvalid)
	}
	result.SignerName = structureString(attrs, "SignerName")
	result.Language, err = structureLanguage(attrs, false)
	if err != nil {
		return result, err
	}
	order := 0
	for _, child := range node.Children {
		rank := 0
		switch child.Name.Local {
		case "SpotLocation":
			rank = 1
		case "Intent":
			rank = 2
		case "SignBy":
			rank = 3
		case "SigningLocation":
			rank = 4
		}
		if rank <= order || len(child.Children) != 0 {
			return result, fmt.Errorf("%w: signature definition child order or content", ErrInvalid)
		}
		order = rank
		if rank == 1 {
			attrs, err := structureAttributes(child, namespace, "PageURI", "StartX", "StartY")
			if err != nil {
				return result, err
			}
			page, present := attrs["PageURI"]
			pageURI := structureURI(page)
			if !present || pageURI == "" || !uriReference(pageURI) {
				return result, fmt.Errorf("%w: invalid or missing signature spot page URI", ErrInvalid)
			}
			x, err := signatureDefinitionDouble(attrs["StartX"])
			if err != nil {
				return result, err
			}
			y, err := signatureDefinitionDouble(attrs["StartY"])
			if err != nil {
				return result, err
			}
			result.Spot = &SignatureSpot{PageURI: pageURI, Start: Point{x, y}}
			continue
		}
		copy := *child
		copy.Text = ""
		if _, err := structureAttributes(&copy, namespace); err != nil {
			return result, err
		}
		value := child.Text
		switch rank {
		case 2:
			result.Intent = &value
		case 3:
			value = strings.Trim(value, " \t\r\n")
			tIndex := strings.IndexByte(value, 'T')
			if !strings.HasSuffix(value, "Z") || !xmlDateValue(value, true) || value[0] == '-' || tIndex < 10 || value[tIndex+1:tIndex+3] == "24" {
				return result, fmt.Errorf("%w: signature deadline requires UTC dateTime", ErrInvalid)
			}
			result.SignBy = &value
		case 4:
			result.SigningLocation = &value
		}
	}
	return result, nil
}

// signatureDefinitionDouble 按xs:double解析位置声明，保留特殊值和浮点范围溢出的结果
// 入参: value 数值词法
// 返回: float64 双精度值, error 非法词法错误
func signatureDefinitionDouble(value string) (float64, error) {
	value = strings.Trim(value, " \t\r\n")
	switch value {
	case "INF":
		return math.Inf(1), nil
	case "-INF":
		return math.Inf(-1), nil
	case "NaN":
		return math.NaN(), nil
	}
	if !signatureDefinitionNumber.MatchString(value) {
		return 0, fmt.Errorf("%w: signature spot double", ErrInvalid)
	}
	result, err := strconv.ParseFloat(value, 64)
	if err != nil && !errors.Is(err, strconv.ErrRange) {
		return 0, fmt.Errorf("%w: signature spot double: %w", ErrInvalid, err)
	}
	return result, nil
}

// validateSignatureDefinitionLinks 校验包内签名定义部件模式、当前方言文档关联及请求标识全局唯一性
// 入参: ctx 非nil取消Context
// 返回: error 来源、目标、模式、重复标识、资源或取消错误
func (r *Reader) validateSignatureDefinitionLinks(ctx context.Context) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	g := signaturePartGraph{context: ctx, remaining: r.limits.MaxPackageBytes}
	pkg := *r.pkg
	pkg.beforeRead, g.pkg = g.readAllowance, &pkg
	namespace := formatNamespace(r.format) + "/signature-definitions"
	ids := make(map[string]bool)
	for _, key := range slices.Sorted(maps.Keys(pkg.parts)) {
		if err := checkContext(ctx); err != nil {
			return err
		}
		if opcRelationshipName(key) {
			source := relationshipSource(pkg.names[key])
			relations, err := pkg.relationships(source)
			if err != nil {
				return err
			}
			for _, relation := range relations {
				if err := checkContext(ctx); err != nil {
					return err
				}
				if relation.Type != namespace {
					continue
				}
				media, err := pkg.contentType(source)
				if err != nil || !strings.EqualFold(media, fixedContentType("fixeddocument")) {
					return &PartError{Part: source, Err: fmt.Errorf("%w: signature definition source is not a fixed document", ErrInvalid)}
				}
				if _, err := g.target(source, relation, fixedContentType("signaturedefinitions")); err != nil {
					return &PartError{Part: source, Err: err}
				}
			}
			continue
		}
		if key == strings.ToLower(opcTypesName) {
			continue
		}
		media, err := pkg.contentType(key)
		if err != nil {
			return err
		}
		if !strings.EqualFold(media, fixedContentType("signaturedefinitions")) {
			continue
		}
		data, err := pkg.readItems(key, min(r.limits.MaxPartBytes, r.limits.MaxMetadataBytes))
		if err != nil {
			return &PartError{Part: pkg.names[key], Err: err}
		}
		definitions, err := readSignatureDefinitions(data, namespace, r.limits, ctx)
		if err != nil {
			return &PartError{Part: pkg.names[key], Element: "SignatureDefinitions", Err: err}
		}
		for _, definition := range definitions {
			if len(ids) >= r.limits.MaxXMLNodes {
				return fmt.Errorf("%w: global signature definition count", ErrLimit)
			}
			if ids[definition.ID] {
				return &PartError{Part: pkg.names[key], Err: fmt.Errorf("%w: duplicate global signature spot ID %q", ErrInvalid, definition.ID)}
			}
			ids[definition.ID] = true
		}
	}
	return checkContext(ctx)
}

// EncodeSignatureDefinitions 将签署请求编码为独立UTF-8部件，不创建数字签名或文档关联
// 模型、字符及预算校验失败不写入输出；底层写入失败可能留下部分字节
// 入参: ctx 取消Context，nil采用Background, output 输出流, definitions 请求列表，不得为空, options 编码选项，nil采用默认值
// 返回: int64 已写字节数, error 模型、资源、取消或输出错误
func EncodeSignatureDefinitions(ctx context.Context, output io.Writer, definitions []SignatureDefinition, options *EncodeOptions) (int64, error) {
	ctx = normalizeContext(ctx)
	if output == nil || len(definitions) == 0 {
		return 0, fmt.Errorf("%w: missing signature definitions or output", ErrInvalid)
	}
	configuration := EncodeOptions{Format: FormatOpenXPS, Limits: DefaultLimits()}
	if options != nil {
		if options.Format != FormatUnknown {
			configuration.Format = options.Format
		}
		configuration.Limits = mergeLimits(configuration.Limits, options.Limits)
	}
	if err := validateLimits(configuration.Limits); err != nil {
		return 0, err
	}
	namespace := formatNamespace(configuration.Format)
	if namespace == "" {
		return 0, fmt.Errorf("%w: signature definition format", ErrInvalid)
	}
	namespace += "/signature-definitions"
	limits := configuration.Limits
	limits.MaxPartBytes = min(limits.MaxPartBytes, limits.MaxMetadataBytes, limits.MaxPackageBytes)
	p := pageEncoder{ns: namespace, limits: limits, ctx: ctx, scope: map[string]string{"": namespace, "xml": xmlNamespace}}
	root, err := p.node("SignatureDefinitions", 1)
	if err != nil {
		return 0, err
	}
	for _, value := range definitions {
		node, err := p.node("SignatureDefinition", 2)
		if err != nil {
			return 0, err
		}
		if err := p.attr(node, "SpotID", strings.Trim(value.ID, " \t\r\n")); err != nil {
			return 0, err
		}
		for _, attribute := range []struct {
			name  xml.Name
			value *string
		}{{xml.Name{Local: "SignerName"}, value.SignerName}, {xml.Name{Space: xmlNamespace, Local: "lang"}, value.Language}} {
			if attribute.value != nil {
				if err := p.attribute(node, attribute.name, *attribute.value); err != nil {
					return 0, err
				}
			}
		}
		if value.Spot != nil {
			spot, err := p.node("SpotLocation", 3)
			if err != nil {
				return 0, err
			}
			for _, attribute := range []struct{ name, value string }{
				{"PageURI", value.Spot.PageURI}, {"StartX", encodeSignatureDefinitionDouble(value.Spot.Start.X)}, {"StartY", encodeSignatureDefinitionDouble(value.Spot.Start.Y)},
			} {
				if err := p.attr(spot, attribute.name, attribute.value); err != nil {
					return 0, err
				}
			}
			node.Children = append(node.Children, spot)
		}
		for _, field := range []struct {
			name  string
			value *string
		}{{"Intent", value.Intent}, {"SignBy", value.SignBy}, {"SigningLocation", value.SigningLocation}} {
			if field.value == nil {
				continue
			}
			child, err := p.node(field.name, 3)
			if err != nil {
				return 0, err
			}
			child.Text = *field.value
			if !xmlTextValid(child.Text) {
				return 0, fmt.Errorf("%w: invalid signature definition text", ErrInvalid)
			}
			size := int64(len(child.Text))
			for _, character := range child.Text {
				if err := checkContext(p.ctx); err != nil {
					return 0, err
				}
				switch character {
				case '&', '\r', '\t', '\n', '\'', '"':
					size += 4
				case '<', '>':
					size += 3
				}
			}
			if err := p.reserve(size); err != nil {
				return 0, err
			}
			node.Children = append(node.Children, child)
		}
		root.Children = append(root.Children, node)
	}
	data, err := createdMarkup(root, limits, p.ctx)
	if err != nil {
		return 0, err
	}
	if _, err := readSignatureDefinitions(data, namespace, limits, p.ctx); err != nil {
		return 0, err
	}
	counted := packageOutput{writer: output, context: p.ctx, limit: limits.MaxPartBytes}
	if _, err := counted.Write(data); err != nil {
		return counted.count, err
	}
	return counted.count, checkContext(p.ctx)
}

// encodeSignatureDefinitionDouble 输出xs:double词法，保留符号零与非有限声明
// 入参: value 位置声明
// 返回: string XML双精度数值
func encodeSignatureDefinitionDouble(value float64) string {
	if math.IsNaN(value) {
		return "NaN"
	}
	if math.IsInf(value, 1) {
		return "INF"
	}
	if math.IsInf(value, -1) {
		return "-INF"
	}
	return strconv.FormatFloat(value, 'g', -1, 64)
}
