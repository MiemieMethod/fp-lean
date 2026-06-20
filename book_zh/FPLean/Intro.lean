import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "简介" =>
%%%
htmlSplit := .never
number := false
%%%

Lean 是一个基于依值类型论的交互式定理证明器。
它最初由 Microsoft Research 开发，现在则由 [Lean FRO](https://lean-fro.org) 继续开发。
依值类型论把程序与证明两个世界统一起来；因此，Lean 也是一门程序设计语言。
Lean 认真对待自己的这种双重性质，并且被设计成适合作为通用程序设计语言使用；Lean 甚至是用 Lean 自身实现的。
本书讨论如何用 Lean 编写程序。

从程序设计语言的角度看，Lean 是一门带有依值类型的严格纯函数式语言。
学习用 Lean 编程，在很大程度上就是学习这些性质各自如何影响程序的写法，以及如何像函数式程序员那样思考。
所谓_严格求值_，是指 Lean 中的函数调用与多数语言类似：在函数体开始运行之前，参数会被完全求值。
所谓_纯粹性_，是指如果程序的类型没有说明，Lean 程序就不能产生修改内存位置、发送邮件或删除文件等副作用。
Lean 是一门_函数式_语言，这是因为函数和其他值一样是一等值，并且其执行模型受到数学表达式求值方式的启发。
_依值类型_是 Lean 最不寻常的特性，它使类型成为语言中的一等组成部分，从而允许类型包含程序，也允许程序计算类型。

本书面向希望学习 Lean、但不一定曾经使用过函数式程序设计语言的程序员。
读者不需要熟悉 Haskell、OCaml 或 F# 等函数式语言。
另一方面，本书假定读者知道循环、函数和数据结构等大多数程序设计语言共有的概念。
本书旨在成为一本良好的函数式程序设计入门书，但并不是一本一般程序设计的入门书。

把 Lean 作为证明助手使用的数学家，迟早很可能需要编写自定义的证明自动化工具。
本书同样面向这些读者。
随着这类工具变得更加复杂，它们会开始像函数式语言中的程序；然而，多数实际工作的数学家所受的训练通常来自 Python 和 Mathematica 这样的语言。
本书可以帮助弥合这种差距，使更多数学家能够编写可维护且易于理解的证明自动化工具。

本书应当从头到尾线性阅读。
各个概念会逐一引入，后续章节会假定读者已经熟悉前面的内容。
有时，后面的章节会深入讨论前面只简要提到过的主题。
本书的一些小节包含练习。
这些练习值得完成，因为它们能够巩固你对相应小节的理解。
在阅读本书的同时探索 Lean，并创造性地寻找使用所学内容的新方法，也是很有帮助的。

# 获取 Lean
%%%
tag := "getting-lean"
%%%

在编写并运行 Lean 程序之前，你需要在自己的计算机上配置 Lean。
Lean 的工具链由以下部分组成：

 * {lit}`elan` 管理 Lean 编译器工具链，类似于 {lit}`rustup` 或 {lit}`ghcup`。
 * {lit}`lake` 构建 Lean 包及其依赖，类似于 {lit}`cargo`、{lit}`make` 或 Gradle。
 * {lit}`lean` 对单个 Lean 文件进行类型检查和编译，并向程序员工具提供正在编辑的文件的信息。
   通常，{lit}`lean` 由其他工具调用，而不是由用户直接调用。
 * Visual Studio Code 或 Emacs 等编辑器的插件会与 {lit}`lean` 通信，并以方便的形式呈现其信息。

关于安装 Lean 的最新说明，请参阅 [Lean 手册](https://lean-lang.org/lean4/doc/quickstart.html)。

# 排版约定
%%%
tag := "typographical-conventions"
%%%

作为_输入_提供给 Lean 的代码示例采用如下格式：

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

```anchorTerm add1_7
#eval add1 7
```

上面的最后一行（以 {kw}`#eval` 开头）是一条命令，它指示 Lean 计算一个结果。
Lean 的回复采用如下格式：

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

警告采用如下格式：

```anchorWarning add1_warn
declaration uses 'sorry'
```

# Unicode字符
%%%
tag := "unicode"
%%%


惯用的 Lean 代码会使用许多不属于 ASCII 的 Unicode 字符。
例如，本书第一章就会出现 {lit}`α`、{lit}`β` 这样的希腊字母以及箭头 {lit}`→`。
这使 Lean 代码能够更接近通常的数学记法。

在 Lean 的默认设置下，Visual Studio Code 和 Emacs 都允许通过反斜杠（{lit}`\`）后接名称来输入这些字符。
例如，要输入 {lit}`α`，可以键入 {lit}`\alpha`。
要在 Visual Studio Code 中了解某个字符如何输入，可以把鼠标指向它并查看工具提示。
在 Emacs 中，可以把光标置于相应字符上，然后使用 {lit}`C-c C-k`。



# 发布历史
%%%
tag := "release-history"
number := false
htmlSplit := .never
%%%

## 2025 年 10 月
%%%
tag := none
%%%

本书已更新到最新的稳定 Lean 版本（版本 4.23.0），现在描述了函数归纳和 {tactic}`grind` 策略。

## 2025 年 8 月
%%%
tag := none
%%%

这是一个维护版本，用于解决从本书中复制粘贴代码的问题。

## 2025 年 7 月
%%%
tag := none
%%%

本书已更新到 Lean 4.21 版本。

## 2025 年 6 月
%%%
tag := none
%%%

本书已用 Verso 重新排版。

## 2025 年 4 月
%%%
tag := none
%%%

本书经过了大幅更新，现在描述 Lean 4.18 版本。

## 2024 年 1 月
%%%
tag := none
%%%

这是一个小型错误修复版本，修复了某个示例程序中的回归问题。

## 2023 年 10 月
%%%
tag := none
%%%

在第一个维护版本中，若干较小问题得到了修复，文本也被更新到与 Lean 的最新发布版本一致。

## 2023 年 5 月
%%%
tag := none
%%%

本书现在已经完成！与四月的预发布版本相比，许多细节得到了改进，一些小错误也得到了修复。

## 2023 年 4 月
%%%
tag := none
%%%

此版本增加了一个关于使用策略编写证明的插曲，并增加了最后一章；该章把对性能与代价模型的讨论同终止性证明和程序等价性证明结合起来。
这是正式完成之前的最后一个发布版本。

## 2023 年 3 月
%%%
tag := none
%%%

此版本增加了一章，讨论如何用依值类型和索引族进行编程。

## 2023 年 1 月
%%%
tag := none
%%%

此版本增加了一章关于单子转换器的内容，其中包括对 {kw}`do`-记法中可用的命令式特性的说明。

## 2022 年 12 月
%%%
tag := none
%%%

此版本增加了一章关于应用函子的内容，并更详细地描述了结构体和类型类。
与此同时，关于单子的说明也得到了改进。
由于寒假，2022 年 12 月版本被推迟到 2023 年 1 月发布。

## 2022 年 11 月
%%%
tag := none
%%%
此版本增加了一章关于使用单子编程的内容。此外，强制类型转换一节中使用 JSON 的示例已更新为包含完整代码。

## 2022 年 10 月
%%%
tag := none
%%%
此版本完成了关于类型类的一章。此外，在类型类一章之前加入了一个简短的插曲，用来介绍命题、证明和策略；对这些概念有少量熟悉，有助于理解标准库中的一些类型类。

## 2022 年 9 月
%%%
tag := none
%%%
此版本增加了类型类一章的前半部分。类型类是 Lean 中重载运算符的机制，也是组织代码和构造库的重要手段。此外，第二章也已更新，以反映 Lean 流 API 的变化。

## 2022 年 8 月
%%%
tag := none
%%%
第三个公开版本增加了第二章，描述如何编译和运行程序，以及 Lean 对副作用的模型。

## 2022 年 7 月
%%%
tag := none
%%%
第二个公开版本完成了第一章。

## 2022 年 6 月
%%%
tag := none
%%%
这是第一个公开版本，包含简介和第一章的一部分。


# 关于作者
%%%
tag := "about-the-author"
%%%

David Thrane Christiansen 已经使用函数式语言二十年，使用依值类型十年。
他与 Daniel P. Friedman 合著了 [_The Little Typer_](https://thelittletyper.com/)，该书介绍依值类型论的核心思想。
他拥有哥本哈根 IT 大学的博士学位。
在学习期间，他是 Idris 语言第一个版本的主要贡献者之一。
离开学术界之后，他曾在俄勒冈州波特兰的 Galois 和丹麦哥本哈根的 Deon Digital 担任软件开发者，也曾任 Haskell 基金会执行董事。
写作本书时，他受雇于 [Lean Focused Research Organization](https://lean-fro.org)，全职从事 Lean 相关工作。

# 许可证
%%%
tag := "license"
%%%

{creativeCommons}
本书的原始版本由 David Thrane Christiansen 受微软公司委托撰写，微软公司慷慨地将其以知识共享署名 4.0 国际许可协议发布。
当前版本已由作者在原始版本的基础上进行修改，以适应 Lean 新版本的变化。
有关更改的详细说明，请参阅本书的[源代码仓库](https://github.com/leanprover/fp-lean/)。
