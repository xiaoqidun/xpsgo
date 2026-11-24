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

# 渲染页面
```go
package main

import (
	"context"
	"image/color"
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
	img, err := reader.Render(ctx, 0, &xpsgo.RenderOptions{Background: color.White})
	if err != nil {
		log.Fatal(err)
	}
	out, err := os.Create("test.png")
	if err != nil {
		log.Fatal(err)
	}
	if err := png.Encode(out, img); err != nil {
		out.Close()
		log.Fatal(err)
	}
	if err := out.Close(); err != nil {
		log.Fatal(err)
	}
}
```

# 授权协议
本项目使用 [Apache License 2.0](https://github.com/xiaoqidun/xpsgo/blob/main/LICENSE) 授权协议