# Lean 函数式编程

本目录包含 _Functional Programming in Lean_ 的中文 Verso 源码。

构建本书需要先构建根目录下的 `examples` 工程。进入本目录后运行：

```sh
lake exe fp-lean --depth 2 --without-html-single --verbose
```

构建完成后，`book_zh/_out/html-multi` 包含多页 HTML 版本。
