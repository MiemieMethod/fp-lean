import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "引言" =>
%%%
htmlSplit := .never
number := false
file := "Introduction"
%%%

Lean 是一个基于依值类型论的交互式定理证明器。
Lean 最初由 Microsoft Research 开发，现在开发工作在 [Lean FRO](https://lean-fro.org) 进行。
依值类型论统一了程序与证明的世界；因此，Lean 也是一种编程语言。
Lean 严肃对待其双重性质，并被设计为适合用作通用编程语言——Lean 甚至是用自身实现的。
本书讨论如何用 Lean 编写程序。

从编程语言的角度来看，Lean 是一种具有依值类型的严格纯函数式语言。
学习用 Lean 编程，很大一部分在于学习这些属性各自如何影响程序的编写方式，以及如何像函数式程序员那样思考。
_严格性_意味着 Lean 中的函数调用方式类似于大多数语言中的函数调用：在函数体开始运行之前，参数会被完全计算。
_纯粹性_意味着 Lean 程序不能在程序类型未表明的情况下产生副作用，例如修改内存位置、发送电子邮件或删除文件。
Lean 是一种_函数式_语言，其含义是函数像其他值一样是一等值，并且其执行模型受到数学表达式求值的启发。
_依值类型_是 Lean 最不同寻常的特性，它使类型成为语言的一等组成部分，从而允许类型包含程序，也允许程序计算类型。

本书面向希望学习 Lean 的程序员，但并不要求读者此前一定使用过函数式编程语言。
不要求熟悉 Haskell、OCaml 或 F# 等函数式语言。
另一方面，本书确实假定读者了解大多数编程语言中常见的概念，例如循环、函数和数据结构。
虽然本书旨在成为一本良好的函数式编程入门书，但它并不适合作为一般编程的第一本入门书。

将 Lean 用作证明助手的数学家，很可能在某个阶段需要编写自定义的证明自动化工具。
本书也面向他们。
随着这些工具变得更复杂，它们开始类似于函数式语言中的程序，但大多数在职数学家接受的是 Python 和 Mathematica 这类语言的训练。
本书可以帮助弥合这一差距，使更多数学家能够编写可维护且可理解的证明自动化工具。

本书旨在从头到尾线性阅读。
概念会逐一引入，后续章节默认读者熟悉前面的章节。
有时，后面的章节会深入讨论先前只是简要涉及的主题。
本书的一些小节包含练习。
这些练习值得完成，以巩固你对该小节的理解。
在阅读本书时探索 Lean 也很有用，可以创造性地寻找运用所学内容的新方式。

# 获取 Lean
%%%
tag := "getting-lean"
file := "Getting-Lean"
%%%

在编写和运行用 Lean 写成的程序之前，你需要在自己的计算机上设置 Lean。
Lean 工具链包括以下内容：

 * {lit}`elan` 管理 Lean 编译器工具链，类似于 {lit}`rustup` 或 {lit}`ghcup`。
 * {lit}`lake` 构建 Lean 包及其依赖项，类似于 {lit}`cargo`、{lit}`make` 或 Gradle。
 * {lit}`lean` 对单个 Lean 文件进行类型检查和编译，并向程序员工具提供关于当前正在编写的文件的信息。
通常，{lit}`lean` 由其他工具调用，而不是由用户直接调用。
 * 用于编辑器的插件，例如 Visual Studio Code 或 Emacs；这些插件与 {lit}`lean` 通信，并以便捷方式呈现其信息。

请参阅 [Lean 手册](https://lean-lang.org/lean4/doc/quickstart.html) 以获取安装 Lean 的最新说明。

# 排版约定
%%%
tag := "typographical-conventions"
file := "Typographical-Conventions"
%%%

作为_输入_提供给 Lean 的代码示例按如下方式排版：

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

```anchorTerm add1_7
#eval add1 7
```

上面的最后一行（以 {kw}`#eval` 开头）是一条命令，它指示 Lean 计算一个答案。
Lean 的回答采用如下格式：

```anchorInfo add1_7
8
```

Lean 返回的错误消息采用如下格式：

```anchorError add1_string
Application type mismatch: The argument
  "seven"
has type
  String
but is expected to have type
  Nat
in the application
  add1 "seven"
```

警告的格式如下：

```anchorWarning add1_warn
declaration uses 'sorry'
```

# Unicode
%%%
tag := "unicode"
file := "Unicode"
%%%


惯用的 Lean 代码会使用多种不属于 ASCII 的 Unicode 字符。
例如，本书第一章中就出现了像 {lit}`α` 和 {lit}`β` 这样的希腊字母，以及箭头 {lit}`→`。
这使 Lean 代码能够更接近普通的数学记法。

在默认的 Lean 设置下，Visual Studio Code 和 Emacs 都允许通过输入反斜杠（{lit}`\`）后跟一个名称来键入这些字符。
例如，要输入 {lit}`α`，请键入 {lit}`\alpha`。
若要了解如何在 Visual Studio Code 中键入某个字符，请将鼠标指向它并查看工具提示。
在 Emacs 中，将光标置于相关字符上并使用 {lit}`C-c C-k`。



# 发布历史
%%%
tag := "release-history"
number := false
htmlSplit := .never
file := "Release-history"
%%%

## 2025 年 10 月
%%%
tag := none
file := "October___-2025"
%%%

本书已更新至最新的 Lean 稳定版本（版本 4.23.0），现在还介绍了函数归纳和 {tactic}`grind` 策略。

## 2025 年 8 月
%%%
tag := none
file := "August___-2025"
%%%

这是一个维护版本，用于解决从本书复制粘贴代码时出现的问题。

## 2025 年 7 月
%%%
tag := none
file := "July___-2025"
%%%

本书已更新至 Lean 4.21 版本。

## 2025 年 6 月
%%%
tag := none
file := "June___-2025"
%%%

本书已使用 Verso 重新排版。

## 2025 年 4 月
%%%
tag := none
file := "April___-2025"
%%%

本书已得到大幅更新，现在描述的是 Lean 版本 4.18。

## 2024 年 1 月
%%%
tag := none
file := "January___-2024"
%%%

这是一个小型缺陷修复版本，修复了一个示例程序中的回归问题。

## 2023 年 10 月
%%%
tag := none
file := "October___-2023"
%%%

在此首次维护版本中，修复了若干较小的问题，并将文本更新至 Lean 的最新版本。

## 2023 年 5 月
%%%
tag := none
file := "May___-2023"
%%%

本书现在已经完成！与四月的预发布版本相比，许多小细节得到了改进，并且修正了一些小错误。

## 2023 年 4 月
%%%
tag := none
file := "April___-2023"
%%%

此版本新增了一篇关于用策略编写证明的插曲，并新增了最后一章，将性能和成本模型的讨论与终止性和程序等价性的证明结合起来。
这是最终版本之前的最后一个版本。

## 2023 年 3 月
%%%
tag := none
file := "March___-2023"
%%%

此版本新增了一章，内容是使用依值类型和索引族进行编程。

## 2023 年 1 月
%%%
tag := none
file := "January___-2023"
%%%

此版本新增了一章关于单子转换器的内容，其中包括对 {kw}`do` 记法中可用的命令式特性的说明。

## 2022 年 12 月
%%%
tag := none
file := "December___-2022"
%%%

此版本新增了一章关于应用函子的内容，并进一步更详细地描述了结构和类型类。
同时，对单子的描述也作出了改进。
由于寒假，2022 年 12 月的发布推迟到 2023 年 1 月。

## 2022 年 11 月
%%%
tag := none
file := "November___-2022"
%%%
此版本新增了一章，内容是使用单子进行编程。此外，强制类型转换一节中使用 JSON 的示例已更新为包含完整代码。

## 2022 年 10 月
%%%
tag := none
file := "October___-2022"
%%%
此版本完成了关于类型类的一章。此外，在类型类一章之前新增了一个简短的插曲，介绍命题、证明和策略；因为对这些概念略有熟悉，有助于理解标准库中的一些类型类。

## 2022 年 9 月
%%%
tag := none
file := "September___-2022"
%%%
此版本新增了关于类型类的一章的前半部分；类型类是 Lean 用于重载运算符的机制，也是组织代码和构造库的重要手段。此外，第二章已更新，以适应 Lean 流 API 的变化。

## 2022 年 8 月
%%%
tag := none
file := "August___-2022"
%%%
第三个公开版本新增了第二章，该章介绍程序的编译与运行，以及 Lean 的副作用模型。

## 2022 年 7 月
%%%
tag := none
file := "July___-2022"
%%%
第二个公开版本完成了第一章。

## 2022 年 6 月
%%%
tag := none
file := "June___-2022"
%%%
这是首次公开发布，包含引言和第一章的一部分。


# 关于作者
%%%
tag := "about-the-author"
file := "About-the-Author"
%%%

David Thrane Christiansen 使用函数式语言已有二十年，使用依值类型已有十年。
他与 Daniel P. Friedman 合著了 [_The Little Typer_](https://thelittletyper.com/)，这是一本介绍依值类型论核心思想的入门书。
他拥有哥本哈根 IT 大学博士学位。
在求学期间，他是 Idris 语言第一个版本的主要贡献者之一。
离开学术界后，他曾在俄勒冈州波特兰的 Galois 以及丹麦哥本哈根的 Deon Digital 担任软件开发者，并曾任 Haskell Foundation 执行董事。
在撰写本文时，他受雇于 [Lean Focused Research Organization](https://lean-fro.org)，全职从事 Lean 相关工作。

# 许可证
%%%
tag := "license"
file := "License"
%%%

{creativeCommons}

本书的原始版本由 David Thrane Christiansen 受 Microsoft Corporation 委托撰写，后者慷慨地以 Creative Commons Attribution 4.0 International License 发布了该版本。
当前版本由作者在原始版本基础上修改而成，以适应较新版本 Lean 中的变化。
关于这些变化的详细说明可在本书的[源代码仓库](https://github.com/leanprover/fp-lean/)中找到。
