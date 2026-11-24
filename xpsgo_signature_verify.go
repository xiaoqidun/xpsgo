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
	"crypto/rsa"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"crypto/subtle"
	"crypto/x509"
	"encoding/asn1"
	"encoding/binary"
	"encoding/xml"
	"errors"
	"fmt"
	"hash"
	"math/big"
	"mime"
	"net/url"
	"slices"
	"strconv"
	"strings"
)

// signatureMaxCertificates 限制单个签名的候选证书数量，避免无界的解析和公钥验证
const signatureMaxCertificates = 256

// signatureMinDSABits 等常量限制数字签名非对称密钥位宽范围
const (
	signatureMinDSABits = 1024
	signatureMaxKeyBits = 32768
)

const (
	// SignatureUnknown 表示尚未完成数字签名状态判断
	SignatureUnknown SignatureStatus = iota
	// SignatureIncompliant 表示签名结构或覆盖范围不合规
	SignatureIncompliant
	// SignatureBroken 表示签名摘要或密码学校验失败
	SignatureBroken
	// SignatureQuestionable 表示签名密码学通过但证书信任或扩展存在疑问
	SignatureQuestionable
	// SignatureValid 表示签名完整且通过验证
	SignatureValid
)

// ErrTrust 表示调用方信任策略未接受签名证书，不表示文档摘要或签名值已经损坏
var ErrTrust = errors.New("signer certificate is not trusted")

// ErrSignature 表示摘要或签名值不匹配，不用于表示证书信任或XPS签名覆盖状态
var ErrSignature = errors.New("signature verification failed")

// signatureVerifier 保存同一次签名读取及累计处理预算，读取与变换处理分别受包字节上限约束
type signatureVerifier struct {
	graph  *signaturePartGraph
	limits Limits
	work   int64
}

// SignatureSigner 保存公钥签名及调用方证书链策略均已验证的签名者，不表示XPS签名覆盖合规
// 所有证书及链均为独立解析结果，不共享调用方证书池中的可变证书对象
type SignatureSigner struct {
	Certificate *x509.Certificate
	Chains      [][]*x509.Certificate
}

// signatureRetrievalPart 缓存本次证书检索读取的部件及按需解析的XML标识
type signatureRetrievalPart struct {
	data        []byte
	media       string
	root        *xmlElement
	ids         map[string]*xmlElement
	certificate bool
}

// SignatureStatus 表示当前方言签名策略下的判断，零值不表示验证已经完成
type SignatureStatus uint8

// SignatureVerifyOptions 设置公钥、显式证书信任与调用方理解的MCE扩展命名空间，调用期间不得修改
// PublicKey非nil时直接用该公钥验签而不强制证书链校验；未提供Trust.Roots时不使用系统根
// Namespaces仅声明调用方扩展理解，不为本库渲染器增加对应功能
type SignatureVerifyOptions struct {
	PublicKey  crypto.PublicKey
	Trust      x509.VerifyOptions
	Namespaces []string
}

// SignatureVerification 保存单份签名的策略判定、密码学、信任及MCE证据，SignatureVerified仅在全部摘要与签名验证后为true
// Signer非nil表示显式证书链策略接受了签名者，不包含吊销或可信时间戳结论
type SignatureVerification struct {
	Part              PartInfo
	Status            SignatureStatus
	Coverage          *SignatureCoverage
	SignatureVerified bool
	Signer            *SignatureSigner
	SignatureError    error
	TrustError        error
	UnknownNamespaces []SignatureNamespace
}

// String 返回数字签名状态的可读名称
// 返回: string 状态名称
func (s SignatureStatus) String() string {
	switch s {
	case SignatureUnknown:
		return "unknown"
	case SignatureIncompliant:
		return "incompliant"
	case SignatureBroken:
		return "broken"
	case SignatureQuestionable:
		return "questionable"
	case SignatureValid:
		return "valid"
	default:
		return fmt.Sprintf("SignatureStatus(%d)", s)
	}
}

// prepare 验证所有引用摘要并生成同一次输入的SignedInfo，不执行公钥或证书信任判断
// 入参: info 已解析的声明, data 原始签名XML
// 返回: []byte 规范化SignedInfo, error 引用、摘要、变换、预算或取消错误
func (v *signatureVerifier) prepare(info *SignatureInfo, data []byte) ([]byte, error) {
	for _, reference := range info.References {
		if err := v.elementDigest(data, reference); err != nil {
			return nil, &PartError{Part: info.Part.Name, Element: "Reference", Err: err}
		}
	}
	for _, reference := range info.Parts {
		if err := v.partDigest(reference); err != nil {
			return nil, &PartError{Part: reference.Part, Element: "Reference", Err: err}
		}
	}
	canonical, err := v.canonicalExclusive(data, info.Canonicalization, info.InclusiveNamespaces, signatureCanonicalComments(info.Canonicalization), v.limits.MaxMetadataBytes, func(node *xmlElement, path []xml.Name) bool {
		return len(path) == 2 && path[0] == (xml.Name{Space: xmlSignatureNamespace, Local: "Signature"}) && node.Name == (xml.Name{Space: xmlSignatureNamespace, Local: "SignedInfo"})
	})
	if err != nil {
		return nil, err
	}
	if err := v.charge(int64(len(canonical))); err != nil {
		return nil, err
	}
	return canonical, nil
}

// charge 检查取消并累计每次变换或摘要输入的工作字节，不重复使用共享阅读器的状态
// 入参: size 待处理的字节数
// 返回: error 取消或预算错误
func (v *signatureVerifier) charge(size int64) error {
	if err := checkContext(v.graph.context); err != nil {
		return err
	}
	if size < 0 || size > v.work {
		return fmt.Errorf("%w: signature processing byte budget", ErrLimit)
	}
	v.work -= size
	return nil
}

// canonical 对原始XML或前一次字节输出执行C14N，子树选择仅用于第一次同文档引用
// 入参: data XML字节, algorithm 规范化算法, comments 是否保留当前输入中的注释, selectElement 可选子树选择
// 返回: []byte 独立规范化输出, error 规范化、预算或取消错误
func (v *signatureVerifier) canonical(data []byte, algorithm string, comments bool, selectElement func(*xmlElement, []xml.Name) bool) ([]byte, error) {
	return v.canonicalExclusive(data, algorithm, nil, comments, v.limits.MaxMetadataBytes, selectElement)
}

// canonicalExclusive 按指定字节上限与可选InclusiveNamespaces前缀列表对XML执行规范化
// 入参: data XML字节, algorithm 规范化算法, inclusive Exc-C14N前缀列表, comments 是否保留注释, maxBytes 允许输出字节上限, selectElement 可选子树选择
// 返回: []byte 独立规范化输出, error 规范化、预算或取消错误
func (v *signatureVerifier) canonicalExclusive(data []byte, algorithm string, inclusive []string, comments bool, maxBytes int64, selectElement func(*xmlElement, []xml.Name) bool) ([]byte, error) {
	if !signatureCanonicalMethod(algorithm) {
		return nil, fmt.Errorf("%w: signature canonicalization algorithm", ErrUnsupported)
	}
	if err := v.charge(int64(len(data))); err != nil {
		return nil, err
	}
	return signatureCanonicalXML(data, signatureCanonicalOptions{limits: v.limits, maxBytes: maxBytes, algorithm: algorithm, comments: comments, inclusive: signatureInclusiveSet(inclusive), context: v.graph.context, selectElement: selectElement})
}

// elementDigest 验证同文档引用，首次节点集转换遵守裸ID移除注释及完整XPointer保留注释的区别
// 入参: data 完整原始签名XML, reference 已解析引用
// 返回: error 引用、变换、摘要、预算或取消错误
func (v *signatureVerifier) elementDigest(data []byte, reference SignatureReference) error {
	id, retain, err := signatureFragment(reference.URI)
	if err != nil {
		return err
	}
	algorithm := signatureCanonical
	var inclusive []string
	if len(reference.Transforms) != 0 {
		algorithm = reference.Transforms[0].Algorithm
		inclusive = reference.Transforms[0].InclusiveNamespaces
	}
	converted, err := v.canonicalExclusive(data, algorithm, inclusive, retain && signatureCanonicalComments(algorithm), v.limits.MaxMetadataBytes, func(node *xmlElement, _ []xml.Name) bool {
		for _, attr := range node.Attr {
			if signatureIDAttribute(node, attr) && strings.Trim(attr.Value, " \t\r\n") == id {
				return true
			}
		}
		return false
	})
	if err != nil {
		return err
	}
	for _, transform := range reference.Transforms[min(1, len(reference.Transforms)):] {
		converted, err = v.canonicalExclusive(converted, transform.Algorithm, transform.InclusiveNamespaces, signatureCanonicalComments(transform.Algorithm), v.limits.MaxMetadataBytes, nil)
		if err != nil {
			return err
		}
	}
	return v.digestBytes(converted, reference)
}

// computePartDigest 计算原始部件或声明关系变换后的摘要，原始字节采用分块读取
// 入参: reference 已通过内容类型及引用校验的包部件声明
// 返回: []byte 实际摘要字节, error 读取、算法、变换、预算或取消错误
func (v *signatureVerifier) computePartDigest(reference SignatureReference) ([]byte, error) {
	if err := checkContext(v.graph.context); err != nil {
		return nil, err
	}
	h, _, err := signatureHash(reference.DigestMethod)
	if err != nil {
		return nil, err
	}
	if len(reference.Transforms) == 0 {
		size, err := v.graph.pkg.partSize(strings.ToLower(reference.Part))
		if err != nil {
			return nil, err
		}
		if size > uint64(v.work) {
			return nil, fmt.Errorf("%w: signature part digest work", ErrLimit)
		}
		if err := v.charge(int64(size)); err != nil {
			return nil, err
		}
		if err := signatureHashPart(v.graph.context, v.graph.pkg, reference.Part, h); err != nil {
			return nil, err
		}
		return h.Sum(nil), nil
	}
	media, _, err := mime.ParseMediaType(reference.ContentType)
	if err != nil {
		return nil, fmt.Errorf("%w: signed part media: %w", ErrInvalid, err)
	}
	limit := signaturePartByteLimit(reference.Part, media, v.limits)
	data, err := v.graph.pkg.readItems(strings.ToLower(reference.Part), limit)
	if err != nil {
		return nil, err
	}
	for _, transform := range reference.Transforms {
		if transform.Algorithm == signatureRelationships {
			if err = v.charge(int64(len(data))); err != nil {
				return nil, err
			}
			data, err = signatureRelationshipXML(data, transform, v.limits, v.graph.context)
		} else {
			data, err = v.canonicalExclusive(data, transform.Algorithm, transform.InclusiveNamespaces, signatureCanonicalComments(transform.Algorithm), limit, nil)
		}
		if err != nil {
			return nil, err
		}
	}
	if err := v.charge(int64(len(data))); err != nil {
		return nil, err
	}
	if err := signatureHashBytes(v.graph.context, h, data); err != nil {
		return nil, err
	}
	return h.Sum(nil), nil
}

// partDigest 验证包部件的摘要，原始字节引用采用分块读取，不把关系变换当作普通XML规范化
// 入参: reference 已通过内容类型及引用校验的包部件声明
// 返回: error 读取、变换、摘要、预算或取消错误
func (v *signatureVerifier) partDigest(reference SignatureReference) error {
	digest, err := v.computePartDigest(reference)
	if err != nil {
		return err
	}
	return signatureDigestMatch(digest, reference)
}

// digestBytes 计算有界变换输出的摘要并与声明摘要比对
// 入参: data 变换后的字节, reference 摘要声明
// 返回: error 摘要算法、匹配、预算或取消错误
func (v *signatureVerifier) digestBytes(data []byte, reference SignatureReference) error {
	if err := v.charge(int64(len(data))); err != nil {
		return err
	}
	h, _, err := signatureHash(reference.DigestMethod)
	if err != nil {
		return err
	}
	if err := signatureHashBytes(v.graph.context, h, data); err != nil {
		return err
	}
	return signatureDigestMatch(h.Sum(nil), reference)
}

// signatureDigestMatch 按固定时序比较摘要字节，错误中保留引用位置但不输出原始内容
// 入参: digest 实际摘要, reference 声明摘要及引用
// 返回: error 摘要不匹配错误
func signatureDigestMatch(digest []byte, reference SignatureReference) error {
	if subtle.ConstantTimeCompare(digest, reference.Digest) != 1 {
		return fmt.Errorf("%w: digest for %s", ErrSignature, reference.URI)
	}
	return nil
}

// SignatureCertificates 读取并去重签名的X509证书，存在内嵌证书时优先使用，不建立信任或访问远程库
// 证书读取共用包字节预算，数量上限为256且不超过MaxPartCount，失败时不返回部分证书
// 入参: ctx 取消Context，nil采用Background, part 签名部件包根URI
// 返回: []*x509.Certificate 独立证书，无证书时为空, error 关联、编码、预算、关闭或取消错误
func (r *Reader) SignatureCertificates(ctx context.Context, part string) ([]*x509.Certificate, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	info, _, graph, err := r.loadSignature(ctx, part)
	if err != nil {
		return nil, err
	}
	return loadSignatureCertificates(info, graph)
}

// signatureTrustOptions 复制调用方证书池与用途，未提供根时使用空池，不读取系统证书库
// 入参: options 信任参数，调用期间不得修改
// 返回: x509.VerifyOptions 本次验证专用参数
func signatureTrustOptions(options x509.VerifyOptions) x509.VerifyOptions {
	if options.Roots == nil {
		options.Roots = x509.NewCertPool()
	} else {
		options.Roots = options.Roots.Clone()
	}
	if options.Intermediates == nil {
		options.Intermediates = x509.NewCertPool()
	} else {
		options.Intermediates = options.Intermediates.Clone()
	}
	options.KeyUsages = slices.Clone(options.KeyUsages)
	if len(options.KeyUsages) == 0 {
		options.KeyUsages = []x509.ExtKeyUsage{x509.ExtKeyUsageAny}
	}
	return options
}

// verifySignatureSigner 共用摘要、包内证书匹配及显式信任验证，不把缺少证书当作密码学成功
// 入参: info 同次读取的声明, data 原始签名XML, graph 私有读取预算, limits 处理上限, options 独立信任参数
// 返回: *SignatureSigner 已信任签名者, bool 签名值是否曾由包内证书验证, error 数据、密码学、信任、能力、资源或取消错误
func verifySignatureSigner(info *SignatureInfo, data []byte, graph *signaturePartGraph, limits Limits, options x509.VerifyOptions) (*SignatureSigner, bool, error) {
	ctx := graph.context
	certificates, err := loadSignatureCertificates(info, graph)
	if err != nil {
		return nil, false, err
	}
	v := signatureVerifier{graph: graph, limits: limits, work: limits.MaxPackageBytes}
	canonical, err := v.prepare(info, data)
	if err != nil {
		return nil, false, err
	}
	if len(certificates) == 0 {
		var keyCapErr error
		triedKey := false
		for _, key := range info.PublicKeys {
			if err := ctx.Err(); err != nil {
				return nil, false, err
			}
			if err := signatureKey(info.Method, key); err != nil {
				if !errors.Is(err, ErrInvalid) {
					keyCapErr = err
				}
				continue
			}
			triedKey = true
			if err := verifySignatureValueParams(ctx, info.Method, info.PSS, key, canonical, info.Value); err != nil {
				if errors.Is(err, ErrSignature) {
					continue
				}
				if errors.Is(err, ErrUnsupported) || errors.Is(err, ErrLimit) {
					keyCapErr = err
					continue
				}
				return nil, false, err
			}
			return nil, true, fmt.Errorf("%w: no document signer certificates", ErrTrust)
		}
		if keyCapErr != nil {
			return nil, false, keyCapErr
		}
		if triedKey {
			return nil, false, fmt.Errorf("%w: no key value matches the signature value", ErrSignature)
		}
		return nil, false, fmt.Errorf("%w: no document signer certificates", ErrTrust)
	}
	for _, certificate := range certificates {
		options.Intermediates.AddCert(certificate)
	}
	var trustError error
	var capabilityError error
	matched := false
	for _, certificate := range certificates {
		if err := ctx.Err(); err != nil {
			return nil, false, err
		}
		if err := signatureKey(info.Method, certificate.PublicKey); err != nil {
			if errors.Is(err, ErrInvalid) {
				continue
			}
			capabilityError = err
			continue
		}
		if err := verifySignatureValueParams(ctx, info.Method, info.PSS, certificate.PublicKey, canonical, info.Value); err != nil {
			if errors.Is(err, ErrSignature) {
				continue
			}
			if errors.Is(err, ErrUnsupported) || errors.Is(err, ErrLimit) {
				capabilityError = err
				continue
			}
			return nil, false, err
		}
		matched = true
		if err := signatureCertificateUsage(certificate); err != nil {
			trustError = err
			continue
		}
		chains, err := certificate.Verify(options)
		if err != nil {
			trustError = fmt.Errorf("%w: %w", ErrTrust, err)
			continue
		}
		if err := ctx.Err(); err != nil {
			return nil, true, err
		}
		signer, err := cloneSignatureSigner(ctx, certificate, chains)
		return signer, true, err
	}
	if matched && trustError != nil {
		return nil, true, trustError
	}
	if capabilityError != nil {
		return nil, matched, capabilityError
	}
	return nil, false, fmt.Errorf("%w: no certificate matches the signature value", ErrSignature)
}

// loadSignatureCertificates 优先使用KeyInfo已指定的证书，合并重复DER，损坏证书不触发来源回退
// 入参: info 本次签名声明, graph 本次关联读取及预算
// 返回: []*x509.Certificate 独立证书, error 编码、读取、预算或取消错误
func loadSignatureCertificates(info *SignatureInfo, graph *signaturePartGraph) ([]*x509.Certificate, error) {
	limit := min(signatureMaxCertificates, graph.pkg.limits.MaxPartCount)
	data := info.Certificates
	if len(data) > limit {
		return nil, fmt.Errorf("%w: KeyInfo signer certificate count", ErrLimit)
	}
	if len(data) == 0 {
		parts, err := graph.certificates(info.Part.Name)
		if err != nil {
			return nil, err
		}
		if len(parts) > limit {
			return nil, fmt.Errorf("%w: signer certificate part count", ErrLimit)
		}
		for _, part := range parts {
			der, err := graph.pkg.readItems(strings.ToLower(part.Name), min(graph.pkg.limits.MaxMetadataBytes, graph.pkg.limits.MaxPartBytes))
			if err != nil {
				return nil, &PartError{Part: part.Name, Err: err}
			}
			data = append(data, der)
		}
	}
	seen := make(map[[32]byte]bool)
	result := make([]*x509.Certificate, 0, len(data))
	for _, der := range data {
		if err := graph.context.Err(); err != nil {
			return nil, err
		}
		if len(der) == 0 {
			return nil, fmt.Errorf("%w: empty signer certificate DER", ErrInvalid)
		}
		key := sha256.Sum256(der)
		if seen[key] {
			continue
		}
		certificate, err := x509.ParseCertificate(der)
		if err != nil {
			return nil, fmt.Errorf("%w: signer certificate DER: %w", ErrInvalid, err)
		}
		seen[key] = true
		result = append(result, certificate)
	}
	return result, nil
}

// signatureCertificateUsage 检查已声明的密钥用途，允许数字签名或内容承诺，不擅自要求证书必须有该扩展
// 入参: certificate 已解析证书
// 返回: error 证书用途不适合文档签名的信任错误
func signatureCertificateUsage(certificate *x509.Certificate) error {
	for _, extension := range certificate.Extensions {
		if extension.Id.Equal(asn1.ObjectIdentifier{2, 5, 29, 15}) && certificate.KeyUsage&(x509.KeyUsageDigitalSignature|x509.KeyUsageContentCommitment) == 0 {
			return fmt.Errorf("%w: certificate key usage forbids document signing", ErrTrust)
		}
	}
	return nil
}

// cloneSignatureSigner 重新解析返回证书及链，避免返回调用方证书池中的对象或共享DER字节
// 入参: ctx 取消Context, certificate 匹配签名的证书, chains 已验证的证书链
// 返回: *SignatureSigner 独立结果, error 解析或取消错误
func cloneSignatureSigner(ctx context.Context, certificate *x509.Certificate, chains [][]*x509.Certificate) (*SignatureSigner, error) {
	copy, err := x509.ParseCertificate(bytes.Clone(certificate.Raw))
	if err != nil {
		return nil, fmt.Errorf("%w: verified signer certificate: %w", ErrInvalid, err)
	}
	result := &SignatureSigner{Certificate: copy, Chains: make([][]*x509.Certificate, len(chains))}
	for index, chain := range chains {
		for _, certificate := range chain {
			if err := checkContext(ctx); err != nil {
				return nil, err
			}
			copy, err := x509.ParseCertificate(bytes.Clone(certificate.Raw))
			if err != nil {
				return nil, fmt.Errorf("%w: verified signer chain: %w", ErrInvalid, err)
			}
			result.Chains[index] = append(result.Chains[index], copy)
		}
	}
	if err := checkContext(ctx); err != nil {
		return nil, err
	}
	return result, nil
}

// signatureHash 按XML签名算法URI创建对应的标准摘要器
// 入参: algorithm 摘要算法URI
// 返回: hash.Hash 摘要器, crypto.Hash 算法标识, error 算法能力错误
func signatureHash(algorithm string) (hash.Hash, crypto.Hash, error) {
	switch algorithm {
	case xmlSignatureNamespace + "sha1":
		h := sha1.New()
		if _, err := h.Write(nil); err != nil {
			return nil, 0, fmt.Errorf("%w: SHA1 disabled by runtime: %w", ErrUnsupported, err)
		}
		return h, crypto.SHA1, nil
	case "http://www.w3.org/2001/04/xmlenc#sha256":
		return sha256.New(), crypto.SHA256, nil
	case "http://www.w3.org/2001/04/xmldsig-more#sha384":
		return sha512.New384(), crypto.SHA384, nil
	case "http://www.w3.org/2001/04/xmlenc#sha512":
		return sha512.New(), crypto.SHA512, nil
	default:
		return nil, 0, fmt.Errorf("%w: signature digest algorithm", ErrUnsupported)
	}
}

// signatureMethodHash 确定RSA、DSA、ECDSA或RSA-PSS签名方法的摘要URI，不以密钥类型推测签名声明
// 入参: method 签名方法URI
// 返回: string 摘要算法URI, error 算法能力错误
func signatureMethodHash(method string) (string, error) {
	switch method {
	case xmlSignatureNamespace + "rsa-sha1", xmlSignatureNamespace + "dsa-sha1":
		return xmlSignatureNamespace + "sha1", nil
	case "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256", signatureMethodECDSA256, signatureMethodPSS256, signatureMethodRSAPSS:
		return "http://www.w3.org/2001/04/xmlenc#sha256", nil
	case "http://www.w3.org/2001/04/xmldsig-more#rsa-sha384", signatureMethodECDSA384, signatureMethodPSS384:
		return "http://www.w3.org/2001/04/xmldsig-more#sha384", nil
	case "http://www.w3.org/2001/04/xmldsig-more#rsa-sha512", signatureMethodECDSA512, signatureMethodPSS512:
		return "http://www.w3.org/2001/04/xmlenc#sha512", nil
	default:
		return "", fmt.Errorf("%w: signature method", ErrUnsupported)
	}
}

// signatureMethodPSS 判断签名方法URI是否采用RSASSA-PSS填充方案
// 入参: method 签名方法URI
// 返回: bool 是否为RSA-PSS方法
func signatureMethodPSS(method string) bool {
	return method == signatureMethodRSAPSS || method == signatureMethodPSS256 || method == signatureMethodPSS384 || method == signatureMethodPSS512
}

// signatureMethodECDSA 判断签名方法URI是否采用ECDSA算法
// 入参: method 签名方法URI
// 返回: bool 是否为ECDSA方法
func signatureMethodECDSA(method string) bool {
	return method == signatureMethodECDSA256 || method == signatureMethodECDSA384 || method == signatureMethodECDSA512
}

// signatureMethodDigest 校验RSA-PSS参数或普通签名方法并返回实际摘要算法URI
// 入参: method 签名方法URI, pss 可选RSA-PSS参数
// 返回: string 摘要算法URI, error 参数或算法能力错误
func signatureMethodDigest(method string, pss *SignaturePSSParams) (string, error) {
	if !signatureMethodPSS(method) {
		return signatureMethodHash(method)
	}
	resolved := pss
	if resolved == nil {
		switch method {
		case signatureMethodRSAPSS, signatureMethodPSS256:
			resolved = &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmlenc#sha256", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmlenc#sha256", SaltLength: 32, TrailerField: 1}
		case signatureMethodPSS384:
			resolved = &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmldsig-more#sha384", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmldsig-more#sha384", SaltLength: 48, TrailerField: 1}
		default:
			resolved = &SignaturePSSParams{DigestMethod: "http://www.w3.org/2001/04/xmlenc#sha512", MGFMethod: signatureMethodMGF1, MGFDigest: "http://www.w3.org/2001/04/xmlenc#sha512", SaltLength: 64, TrailerField: 1}
		}
	}
	if _, _, err := signatureHash(resolved.DigestMethod); err != nil {
		return "", err
	}
	if resolved.MGFMethod != signatureMethodMGF1 || resolved.MGFDigest != resolved.DigestMethod || resolved.TrailerField != 1 || resolved.SaltLength < 0 {
		return "", fmt.Errorf("%w: unsupported RSA-PSS parameters", ErrUnsupported)
	}
	return resolved.DigestMethod, nil
}

// signatureKey 检查调用方公钥的必要字段及运算上限，不建立证书信任或替代密钥来源认证
// 入参: method 签名方法URI, key 调用方提供且在验证期间保持不变的公钥
// 返回: error 密钥字段、算法匹配或资源错误
func signatureKey(method string, key crypto.PublicKey) error {
	if _, err := signatureMethodHash(method); err != nil {
		return err
	}
	if method == xmlSignatureNamespace+"dsa-sha1" {
		public, ok := key.(*dsa.PublicKey)
		if !ok || public == nil || public.P == nil || public.Q == nil || public.G == nil || public.Y == nil || public.P.Sign() <= 0 || public.Q.Sign() <= 0 || public.G.Cmp(big.NewInt(1)) <= 0 || public.Y.Cmp(big.NewInt(1)) <= 0 || public.Q.Cmp(public.P) >= 0 || public.G.Cmp(public.P) >= 0 || public.Y.Cmp(public.P) >= 0 {
			return fmt.Errorf("%w: DSA verification key", ErrInvalid)
		}
		if public.P.BitLen() < signatureMinDSABits {
			return fmt.Errorf("%w: DSA verification key size", ErrInvalid)
		}
		if public.P.BitLen() > signatureMaxKeyBits {
			return fmt.Errorf("%w: DSA verification key size", ErrLimit)
		}
		if public.Q.BitLen() != 160 {
			return fmt.Errorf("%w: DSA-SHA1 subgroup size", ErrUnsupported)
		}
		return nil
	}
	if signatureMethodECDSA(method) {
		public, ok := key.(*ecdsa.PublicKey)
		if !ok || public == nil || public.Curve == nil || public.X == nil || public.Y == nil {
			return fmt.Errorf("%w: ECDSA verification key", ErrInvalid)
		}
		if public.Curve != elliptic.P256() && public.Curve != elliptic.P384() && public.Curve != elliptic.P521() {
			return fmt.Errorf("%w: ECDSA verification curve", ErrUnsupported)
		}
		if public.X.Sign() < 0 || public.Y.Sign() < 0 || public.X.Cmp(public.Curve.Params().P) >= 0 || public.Y.Cmp(public.Curve.Params().P) >= 0 || !public.Curve.IsOnCurve(public.X, public.Y) {
			return fmt.Errorf("%w: ECDSA verification key point", ErrInvalid)
		}
		return nil
	}
	public, ok := key.(*rsa.PublicKey)
	if !ok || public == nil || public.N == nil || public.N.Sign() <= 0 || public.N.Bit(0) == 0 || public.E < 3 || public.E&1 == 0 || uint64(public.E) > 1<<31-1 || public.N.Cmp(big.NewInt(int64(public.E))) <= 0 {
		return fmt.Errorf("%w: RSA verification key", ErrInvalid)
	}
	if public.N.BitLen() > signatureMaxKeyBits {
		return fmt.Errorf("%w: RSA verification key size", ErrLimit)
	}
	return nil
}

// verifySignatureValueParams 按指定算法与可选RSA-PSS参数验证签名值，DSA与ECDSA采用定长r||s编码
// 入参: ctx 取消Context, method 签名方法URI, pss 可选RSA-PSS参数, key 调用方公钥, data 规范化SignedInfo, value 解码后的签名值
// 返回: error 摘要、签名、算法、密钥、资源或取消错误
func verifySignatureValueParams(ctx context.Context, method string, pss *SignaturePSSParams, key crypto.PublicKey, data, value []byte) error {
	if err := checkContext(ctx); err != nil {
		return err
	}
	if err := signatureKey(method, key); err != nil {
		return err
	}
	algorithm, err := signatureMethodDigest(method, pss)
	if err != nil {
		return err
	}
	h, identifier, err := signatureHash(algorithm)
	if err != nil {
		return err
	}
	if err := signatureHashBytes(ctx, h, data); err != nil {
		return err
	}
	digest := h.Sum(nil)
	switch {
	case method == xmlSignatureNamespace+"dsa-sha1":
		if len(value) != 40 {
			return fmt.Errorf("%w: DSA signature size", ErrSignature)
		}
		r, s := new(big.Int).SetBytes(value[:20]), new(big.Int).SetBytes(value[20:])
		if !dsa.Verify(key.(*dsa.PublicKey), digest, r, s) {
			return fmt.Errorf("%w: DSA signature value", ErrSignature)
		}
	case signatureMethodECDSA(method):
		public := key.(*ecdsa.PublicKey)
		nBytes := (public.Curve.Params().BitSize + 7) / 8
		if len(value) != 2*nBytes {
			return fmt.Errorf("%w: ECDSA signature size", ErrSignature)
		}
		r, s := new(big.Int).SetBytes(value[:nBytes]), new(big.Int).SetBytes(value[nBytes:])
		if !ecdsa.Verify(public, digest, r, s) {
			return fmt.Errorf("%w: ECDSA signature value", ErrSignature)
		}
	case signatureMethodPSS(method):
		public := key.(*rsa.PublicKey)
		saltLength := identifier.Size()
		if pss != nil {
			saltLength = pss.SaltLength
		}
		emLen := (public.N.BitLen() - 1 + 7) / 8
		if emLen < identifier.Size()+2 || saltLength > emLen-identifier.Size()-2 {
			return fmt.Errorf("%w: RSA-PSS salt length", ErrInvalid)
		}
		if saltLength == 0 {
			if err := verifyRSAPSSZeroSalt(public, identifier, digest, value); err != nil {
				return err
			}
		} else if err := rsa.VerifyPSS(public, identifier, digest, value, &rsa.PSSOptions{SaltLength: saltLength, Hash: identifier}); err != nil {
			if errors.Is(err, rsa.ErrVerification) {
				return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
			}
			return fmt.Errorf("%w: RSA-PSS verification unavailable: %w", ErrUnsupported, err)
		}
	default:
		if err := rsa.VerifyPKCS1v15(key.(*rsa.PublicKey), identifier, digest, value); err != nil {
			if errors.Is(err, rsa.ErrVerification) {
				return fmt.Errorf("%w: RSA signature value", ErrSignature)
			}
			return fmt.Errorf("%w: RSA verification unavailable: %w", ErrUnsupported, err)
		}
	}
	return checkContext(ctx)
}

// verifyRSAPSSZeroSalt 按RFC8017第9.1.2节严格验证盐长为零的RSASSA-PSS签名，避免Go标准库将0视作自动盐长
// 入参: public RSA公钥, hashAlg 摘要算法, digest 原始消息摘要, sig 原始签名字节
// 返回: error 签名或算法错误
func verifyRSAPSSZeroSalt(public *rsa.PublicKey, hashAlg crypto.Hash, digest, sig []byte) error {
	k := (public.N.BitLen() + 7) / 8
	if len(sig) != k {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	s := new(big.Int).SetBytes(sig)
	if s.Cmp(public.N) >= 0 {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	m := new(big.Int).Exp(s, big.NewInt(int64(public.E)), public.N)
	emBits := public.N.BitLen() - 1
	emLen := (emBits + 7) / 8
	hLen := hashAlg.Size()
	if m.BitLen() > emBits {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	em := make([]byte, emLen)
	m.FillBytes(em)
	if em[emLen-1] != 0xbc {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	dbLen := emLen - hLen - 1
	maskedDB := em[:dbLen]
	h := em[dbLen : dbLen+hLen]
	unusedBits := uint(8*emLen - emBits)
	if unusedBits > 0 && maskedDB[0]&^(byte(0xff)>>unusedBits) != 0 {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	db := make([]byte, dbLen)
	copy(db, maskedDB)
	hasher := hashAlg.New()
	var counter [4]byte
	var mask []byte
	for offset, index := 0, uint32(0); offset < dbLen; index++ {
		binary.BigEndian.PutUint32(counter[:], index)
		hasher.Reset()
		hasher.Write(h)
		hasher.Write(counter[:])
		mask = hasher.Sum(mask[:0])
		for i := 0; i < len(mask) && offset < dbLen; i, offset = i+1, offset+1 {
			db[offset] ^= mask[i]
		}
	}
	if unusedBits > 0 {
		db[0] &= byte(0xff) >> unusedBits
	}
	for i := range dbLen - 1 {
		if db[i] != 0 {
			return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
		}
	}
	if db[dbLen-1] != 0x01 {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	hasher.Reset()
	var prefix [8]byte
	hasher.Write(prefix[:])
	hasher.Write(digest)
	expected := hasher.Sum(nil)
	if subtle.ConstantTimeCompare(h, expected) != 1 {
		return fmt.Errorf("%w: RSA-PSS signature value", ErrSignature)
	}
	return nil
}

// signatureHashBytes 分段计算摘要并检查取消，不复制完整输入
// 入参: ctx 取消Context, h 标准摘要器, data 输入字节
// 返回: error 取消或摘要器错误
func signatureHashBytes(ctx context.Context, h hash.Hash, data []byte) error {
	for at := 0; at < len(data); {
		if err := checkContext(ctx); err != nil {
			return err
		}
		end := at + min(len(data)-at, 32<<10)
		if _, err := h.Write(data[at:end]); err != nil {
			return err
		}
		at = end
	}
	return checkContext(ctx)
}

// retrievalCharge 累计证书解码及检索变换的工作字节，不修改共享阅读器预算
// 入参: size 本次处理字节数
// 返回: error 取消或处理上限错误
func (p *signatureXML) retrievalCharge(size int64) error {
	if err := checkContext(p.context); err != nil {
		return err
	}
	if size < 0 || size > p.work {
		return fmt.Errorf("%w: certificate retrieval processing bytes", ErrLimit)
	}
	p.work -= size
	return nil
}

// retrievalCertificates 读取KeyInfo的包内证书引用，按OPC规则仅接受C14N检索变换
// 入参: node 已通过外层结构检查的RetrievalMethod元素
// 返回: [][]byte 独立证书，非证书引用为空, bool 证书是否位于当前签名XML, error 引用、存储、变换、预算或取消错误
func (p *signatureXML) retrievalCertificates(node *xmlElement) ([][]byte, bool, error) {
	attrs, err := signatureAttributes(node, "URI", "Type")
	if err != nil {
		return nil, false, err
	}
	typ := strings.Trim(attrs["Type"], " \t\r\n")
	if typ != "" && typ != xmlSignatureNamespace+"X509Data" && typ != xmlSignatureNamespace+"rawX509Certificate" {
		return nil, false, nil
	}
	var transforms []SignatureTransform
	if len(node.Children) != 0 {
		for _, transform := range node.Children[0].Children {
			algorithm, inclusive, err := signatureCanonicalNode(transform)
			if err != nil {
				return nil, false, err
			}
			if !signatureCanonicalMethod(algorithm) {
				return nil, false, fmt.Errorf("%w: OPC M6.19 forbids KeyInfo retrieval transform %s", ErrInvalid, algorithm)
			}
			transforms = append(transforms, SignatureTransform{Algorithm: algorithm, InclusiveNamespaces: inclusive})
		}
	}
	uri := strings.Trim(attrs["URI"], " \t\r\n")
	part, target, ordinal, retain, err := p.retrievalInput(uri)
	if err != nil {
		return nil, false, err
	}
	data := part.data
	for _, transform := range transforms {
		if err := p.retrievalCharge(int64(len(data))); err != nil {
			return nil, false, err
		}
		var selectElement func(*xmlElement, []xml.Name) bool
		if target != nil && ordinal != 0 {
			remaining := ordinal
			selectElement = func(*xmlElement, []xml.Name) bool {
				remaining--
				return remaining == 0
			}
		}
		data, err = signatureCanonicalXML(data, signatureCanonicalOptions{limits: p.limits, maxBytes: min(p.limits.MaxMetadataBytes, p.limits.MaxPartBytes), algorithm: transform.Algorithm, comments: (target == nil || retain) && signatureCanonicalComments(transform.Algorithm), inclusive: signatureInclusiveSet(transform.InclusiveNamespaces), context: p.context, selectElement: selectElement})
		if err != nil {
			return nil, false, err
		}
		target, ordinal = nil, 0
	}
	if part.media == opcCertificateType {
		if typ == xmlSignatureNamespace+"X509Data" {
			return nil, false, fmt.Errorf("%w: X509Data retrieval targets raw certificate bytes", ErrInvalid)
		}
		if err := p.retrievalCharge(int64(len(data))); err != nil {
			return nil, false, err
		}
		if !part.certificate {
			if _, err := x509.ParseCertificate(data); err != nil {
				return nil, false, fmt.Errorf("%w: retrieved certificate DER: %w", ErrInvalid, err)
			}
			part.certificate = true
		}
		return [][]byte{bytes.Clone(data)}, false, nil
	}
	if typ == xmlSignatureNamespace+"rawX509Certificate" {
		return nil, false, fmt.Errorf("%w: raw certificate retrieval has XML output", ErrInvalid)
	}
	if target == nil {
		if err := p.retrievalCharge(int64(len(data))); err != nil {
			return nil, false, err
		}
		target, err = decodeXMLVisit(data, p.limits, func(xml.Token, *xmlElement) error { return checkContext(p.context) })
		if err != nil {
			return nil, false, err
		}
	}
	if target.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "X509Data"}) {
		if typ == "" {
			return nil, false, fmt.Errorf("%w: unclassified certificate retrieval output", ErrUnsupported)
		}
		return nil, false, fmt.Errorf("%w: certificate retrieval output differs from Type", ErrInvalid)
	}
	certificates, _, err := p.certificates(&xmlElement{Children: []*xmlElement{target}})
	return certificates, part.root == p.root, err
}

// retrievalInput 按部件基准URI读取包内证书或签名XML，证书部件须与当前签名关联
// 入参: uri 已校验的包内URI
// 返回: *signatureRetrievalPart 本次输入, *xmlElement 所选XML节点或nil, int 所选元素的先序位置，整文档为0, bool 是否保留注释, error 读取或引用错误
func (p *signatureXML) retrievalInput(uri string) (*signatureRetrievalPart, *xmlElement, int, bool, error) {
	path, fragment, hasFragment := strings.Cut(uri, "#")
	if strings.Contains(path, "?") {
		return nil, nil, 0, false, fmt.Errorf("%w: certificate retrieval URI query", ErrUnsupported)
	}
	name := p.source
	var err error
	if path != "" {
		if p.graph == nil {
			return nil, nil, 0, false, fmt.Errorf("%w: certificate retrieval requires a package", ErrUnsupported)
		}
		name, err = resolvePart(p.source, path)
		if err != nil {
			return nil, nil, 0, false, err
		}
	}
	part := &signatureRetrievalPart{data: p.data, media: opcSignatureType, root: p.root, ids: p.ids}
	if path != "" && !strings.EqualFold(name, p.source) {
		key := strings.ToLower(name)
		part = p.loaded[key]
		if part == nil {
			media, err := p.graph.pkg.contentType(name)
			if err != nil {
				return nil, nil, 0, false, err
			}
			if strings.EqualFold(media, opcCertificateType) {
				if err := p.retrievalCertificatePart(name); err != nil {
					return nil, nil, 0, false, err
				}
				media = opcCertificateType
			} else if !strings.EqualFold(media, opcSignatureType) {
				return nil, nil, 0, false, fmt.Errorf("%w: XPS M10.18 certificate storage content type", ErrInvalid)
			} else {
				media = opcSignatureType
			}
			data, err := p.graph.pkg.readItems(key, min(p.limits.MaxMetadataBytes, p.limits.MaxPartBytes))
			if err != nil {
				return nil, nil, 0, false, &PartError{Part: name, Err: err}
			}
			if p.loaded == nil {
				p.loaded = make(map[string]*signatureRetrievalPart)
			}
			part = &signatureRetrievalPart{data: data, media: media}
			p.loaded[key] = part
		}
	}
	if part.media == opcCertificateType {
		if hasFragment {
			return nil, nil, 0, false, fmt.Errorf("%w: certificate DER has no XML fragment", ErrInvalid)
		}
		return part, nil, 0, false, nil
	}
	if part.root == nil {
		if err := p.retrievalCharge(int64(len(part.data))); err != nil {
			return nil, nil, 0, false, err
		}
		part.root, err = decodeXMLVisit(part.data, p.limits, func(xml.Token, *xmlElement) error { return checkContext(p.context) })
		if err != nil {
			return nil, nil, 0, false, err
		}
		if part.root.Name != (xml.Name{Space: xmlSignatureNamespace, Local: "Signature"}) {
			return nil, nil, 0, false, fmt.Errorf("%w: certificate source is not signature XML", ErrInvalid)
		}
		index := signatureXML{context: p.context, ids: make(map[string]*xmlElement)}
		if err := index.identifiers(part.root); err != nil {
			return nil, nil, 0, false, err
		}
		part.ids = index.ids
	}
	if !hasFragment {
		return part, part.root, 0, path != "", nil
	}
	target, retain, err := signatureRetrievalTarget(part.root, part.ids, fragment)
	if err != nil {
		return nil, nil, 0, false, err
	}
	if target == part.root {
		return part, target, 0, retain, nil
	}
	stack := []*xmlElement{part.root}
	ordinal := 0
	for len(stack) != 0 {
		if err := p.retrievalCharge(1); err != nil {
			return nil, nil, 0, false, err
		}
		node := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		ordinal++
		if node == target {
			return part, target, ordinal, retain, nil
		}
		for index := len(node.Children) - 1; index >= 0; index-- {
			stack = append(stack, node.Children[index])
		}
	}
	return nil, nil, 0, false, fmt.Errorf("%w: unresolved certificate retrieval selection", ErrInvalid)
}

// retrievalCertificatePart 检查被检索证书是否由当前签名的证书关系定位
// 入参: name 证书部件URI
// 返回: error 缺少关联、资源或取消错误
func (p *signatureXML) retrievalCertificatePart(name string) error {
	if p.certificateParts == nil {
		parts, err := p.graph.certificates(p.source)
		if err != nil {
			return err
		}
		p.certificateParts = make(map[string]bool, len(parts))
		for _, part := range parts {
			p.certificateParts[strings.ToLower(part.Name)] = true
		}
	}
	if p.certificateParts[strings.ToLower(name)] {
		return nil
	}
	return fmt.Errorf("%w: certificate retrieval lacks its signature certificate relationship", ErrInvalid)
}

// signatureRetrievalTarget 按XPointer的裸ID、元素子序列或整文档形式选择节点，不执行XPath
// 入参: root XML根元素, ids 模式ID索引, fragment URI中的原始片段，不含井号
// 返回: *xmlElement 所选元素, bool 是否保留注释, error 语法、定位或表达式能力错误
func signatureRetrievalTarget(root *xmlElement, ids map[string]*xmlElement, fragment string) (*xmlElement, bool, error) {
	value, err := url.PathUnescape(fragment)
	if err != nil {
		return nil, false, fmt.Errorf("%w: certificate retrieval fragment encoding", ErrInvalid)
	}
	if value == "xpointer(/)" {
		return root, true, nil
	}
	if !strings.HasPrefix(value, "xpointer(") && strings.Contains(value, "/") {
		anchor, steps, _ := strings.Cut(value, "/")
		target := ids[anchor]
		if anchor == "" {
			target = &xmlElement{Children: []*xmlElement{root}}
		} else if !xmlNCName(anchor) {
			return nil, false, fmt.Errorf("%w: certificate retrieval child-sequence anchor", ErrInvalid)
		}
		for _, step := range strings.Split(steps, "/") {
			if step == "" || step[0] < '1' || step[0] > '9' {
				return nil, false, fmt.Errorf("%w: certificate retrieval child-sequence number", ErrInvalid)
			}
			for _, digit := range step {
				if digit < '0' || digit > '9' {
					return nil, false, fmt.Errorf("%w: certificate retrieval child-sequence number", ErrInvalid)
				}
			}
			position, err := strconv.ParseUint(step, 10, 64)
			if err != nil || target == nil || position > uint64(len(target.Children)) {
				return nil, false, fmt.Errorf("%w: unresolved certificate retrieval child sequence", ErrInvalid)
			}
			target = target.Children[int(position)-1]
		}
		return target, false, nil
	}
	id, retain, err := signatureFragment("#" + fragment)
	if err != nil {
		return nil, false, err
	}
	if ids[id] == nil {
		return nil, false, fmt.Errorf("%w: unresolved certificate retrieval fragment", ErrInvalid)
	}
	return ids[id], retain, nil
}

// VerifySignature 按当前方言覆盖规则、OPC密码学、公钥或显式证书信任及MCE规则综合判定单个签名
// PublicKey非nil时直接用该公钥验签而无需证书链校验；资源、取消或结构错误直接返回错误而非验证结论
// 入参: ctx 取消Context，nil采用Background, part 已关联签名部件包根URI, options 验证参数，nil不信任任何根
// 返回: *SignatureVerification 独立结论与证据，操作失败无部分结果, error 结构、能力、资源、关闭或取消错误
func (r *Reader) VerifySignature(ctx context.Context, part string, options *SignatureVerifyOptions) (*SignatureVerification, error) {
	if err := r.readLock(); err != nil {
		return nil, err
	}
	defer r.mu.RUnlock()
	ctx = normalizeContext(ctx)
	configuration := SignatureVerifyOptions{}
	if options != nil {
		configuration = *options
	}
	if err := validateSignatureVerifyOptions(ctx, configuration, r.limits); err != nil {
		return nil, err
	}
	info, data, graph, err := r.loadSignature(ctx, part)
	if err != nil {
		return nil, err
	}
	return r.verifyLoadedDocumentSignature(info, data, graph, configuration)
}

// validateSignatureVerifyOptions 校验验证配置中显式声明的扩展命名空间
// 入参: ctx 非nil取消Context, configuration 验证配置, limits 阅读器上限
// 返回: error 扩展声明、预算或取消错误
func validateSignatureVerifyOptions(ctx context.Context, configuration SignatureVerifyOptions, limits Limits) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	if len(configuration.Namespaces) > limits.MaxXMLNodes {
		return fmt.Errorf("%w: signature extension namespace count", ErrLimit)
	}
	var size int64
	for _, namespace := range configuration.Namespaces {
		if err := ctx.Err(); err != nil {
			return err
		}
		if int64(len(namespace)) > limits.MaxMetadataBytes-size {
			return fmt.Errorf("%w: signature extension namespace bytes", ErrLimit)
		}
		if namespace == "" || namespace == xmlnsNamespace || !uriReference(namespace) {
			return fmt.Errorf("%w: signature extension namespace URI", ErrInvalid)
		}
		size += int64(len(namespace))
	}
	return nil
}

// verifyLoadedDocumentSignature 复用同次读取的声明及预算判定签名，不重复获取阅读器锁
// 入参: info 已加载声明, data 原始签名XML, graph 本次私有读取图, configuration 验证配置
// 返回: *SignatureVerification 独立结论，操作失败为空, error 结构、能力、资源或取消错误
func (r *Reader) verifyLoadedDocumentSignature(info *SignatureInfo, data []byte, graph *signaturePartGraph, configuration SignatureVerifyOptions) (*SignatureVerification, error) {
	ctx := graph.context
	if configuration.PublicKey != nil {
		if err := signatureKey(info.Method, configuration.PublicKey); err != nil {
			return nil, err
		}
		if _, err := signatureMethodDigest(info.Method, info.PSS); err != nil {
			return nil, err
		}
	}
	coverage, err := r.signatureCoverage(info, graph)
	if err != nil {
		return nil, err
	}
	result := &SignatureVerification{Part: info.Part, Coverage: coverage}
	if configuration.PublicKey != nil {
		v := signatureVerifier{graph: graph, limits: r.limits, work: r.limits.MaxPackageBytes}
		canonical, err := v.prepare(info, data)
		if err == nil {
			err = verifySignatureValueParams(ctx, info.Method, info.PSS, configuration.PublicKey, canonical, info.Value)
		}
		if err != nil {
			var failure *packageReadError
			if errors.As(err, &failure) {
				return nil, err
			}
			switch {
			case errors.Is(err, ErrSignature), errors.Is(err, ErrInvalid):
				result.SignatureError = err
			default:
				return nil, err
			}
		} else {
			result.SignatureVerified = true
		}
		if len(coverage.UnexpectedParts)+len(coverage.UnexpectedRelationships)+len(coverage.UngroupedSignatures) != 0 {
			result.Status = SignatureIncompliant
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			return result, nil
		}
		if len(coverage.MissingParts)+len(coverage.MissingRelationships) != 0 {
			result.Status = SignatureBroken
			if r.format == FormatXPS {
				result.Status = SignatureIncompliant
			}
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			return result, nil
		}
		if !result.SignatureVerified {
			result.Status = SignatureBroken
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			return result, nil
		}
		result.Status = SignatureValid
		result.UnknownNamespaces, err = signatureNamespaces(info, data, graph, r.format, configuration.Namespaces)
		if err != nil {
			return nil, err
		}
		if len(result.UnknownNamespaces) != 0 {
			result.Status = SignatureQuestionable
		}
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		return result, nil
	}
	if len(coverage.UnexpectedParts)+len(coverage.UnexpectedRelationships)+len(coverage.UngroupedSignatures) != 0 {
		result.Status = SignatureIncompliant
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		return result, nil
	}
	if len(coverage.MissingParts)+len(coverage.MissingRelationships) != 0 {
		result.Status = SignatureBroken
		if r.format == FormatXPS {
			result.Status = SignatureIncompliant
		}
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		return result, nil
	}
	if _, err := signatureMethodDigest(info.Method, info.PSS); err != nil {
		return nil, err
	}
	signer, verified, err := verifySignatureSigner(info, data, graph, r.limits, signatureTrustOptions(configuration.Trust))
	result.SignatureVerified = verified
	if err != nil {
		var failure *packageReadError
		if errors.As(err, &failure) {
			return nil, err
		}
		switch {
		case errors.Is(err, ErrTrust):
			result.Status, result.TrustError = SignatureQuestionable, err
		case errors.Is(err, ErrSignature), errors.Is(err, ErrInvalid):
			result.Status, result.SignatureError = SignatureBroken, err
			if err := ctx.Err(); err != nil {
				return nil, err
			}
			return result, nil
		default:
			return nil, err
		}
	} else {
		result.Status, result.Signer = SignatureValid, signer
	}
	result.UnknownNamespaces, err = signatureNamespaces(info, data, graph, r.format, configuration.Namespaces)
	if err != nil {
		return nil, err
	}
	if len(result.UnknownNamespaces) != 0 {
		result.Status = SignatureQuestionable
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return result, nil
}
