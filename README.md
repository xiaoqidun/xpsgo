# XPSGo [![PkgGoDev](https://pkg.go.dev/badge/github.com/xiaoqidun/xpsgo)](https://pkg.go.dev/github.com/xiaoqidun/xpsgo)
首个原生、全平台、纯 Go 语言高性能 XPS 引擎

# 实施标准
- 文档标准：XPS 1.0（.xps）、OpenXPS（.oxps）
- 图像格式：PNG、JPEG、TIFF、JPEG XR（.wdp、.jxr）
- 字体格式：TrueType（.ttf、.ttc）、CFF1（.otf）、混淆字体（.odttf）

# 安装指南
```shell
go get -u github.com/xiaoqidun/xpsgo
```

# 创建文档
```go
package main

import (
	"context"
	"log"
	"os"

	"github.com/xiaoqidun/xpsgo"
)

func main() {
	ctx := context.Background()
	pkg, err := xpsgo.NewPackage(xpsgo.FormatXPS, nil)
	if err != nil {
		log.Fatal(err)
	}
	font, err := os.ReadFile("font.ttf")
	if err != nil {
		log.Fatal(err)
	}
	fontURI, err := pkg.AddFont(font)
	if err != nil {
		log.Fatal(err)
	}
	page := xpsgo.NewPage(794, 1123, "zh-CN")
	page.AddText(fontURI, xpsgo.Point{X: 76, Y: 100}, 24, "你好，XPSGo！", nil)
	if _, err := pkg.AddPage(ctx, page); err != nil {
		log.Fatal(err)
	}
	if err := pkg.WriteFile(ctx, "test.xps", nil); err != nil {
		log.Fatal(err)
	}
}
```

# 渲染页面
```go
package main

import (
	"context"
	"image/png"
	"log"
	"os"

	"github.com/xiaoqidun/xpsgo"
)

func main() {
	ctx := context.Background()
	reader, err := xpsgo.Open(ctx, "test.xps", nil)
	if err != nil {
		log.Fatal(err)
	}
	defer reader.Close()
	img, err := reader.Render(ctx, 0, nil)
	if err != nil {
		log.Fatal(err)
	}
	out, err := os.Create("test.png")
	if err != nil {
		log.Fatal(err)
	}
	defer out.Close()
	if err := png.Encode(out, img); err != nil {
		log.Fatal(err)
	}
}
```

# 授权协议
本项目使用 [Apache License 2.0](https://github.com/xiaoqidun/xpsgo/blob/main/LICENSE) 授权协议