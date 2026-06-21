import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External


open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.HelloWorld"

#doc (Manual) "小结" =>
%%%
tag := "hello-world-summary"
file := "Summary"
%%%

# 求值与执行
%%%
tag := none
file := "Evaluation-vs-Execution"
%%%

副作用是程序执行中超出数学表达式求值范围的那些方面，例如读取文件、抛出异常或触发工业机械。
虽然大多数语言允许在求值期间发生副作用，但 Lean 并不允许。
取而代之的是，Lean 有一个名为 {moduleName}`IO` 的类型，用于表示使用副作用的程序的_描述_。
随后，这些描述由语言的运行时系统执行；运行时系统会调用 Lean 表达式求值器来完成特定计算。
类型 {moduleTerm}`IO α` 的值称为 _{moduleName}`IO` 动作_。
最简单的是 {moduleName}`pure`，它返回其参数，并且没有实际的副作用。

{moduleName}`IO` 动作也可以理解为以整个世界作为参数并返回一个新世界的函数，在这个新世界中副作用已经发生。
在幕后，{moduleName}`IO` 库确保世界绝不会被复制、创建或销毁。
虽然这种副作用模型实际上无法实现，因为整个宇宙太大，无法装入内存，但现实世界可以由一个令牌表示，该令牌在程序中被传递。

程序启动时会执行一个 {moduleName}`IO` 动作 {anchorName MainTypes}`main`。
{anchorName MainTypes}`main` 可以具有以下三种类型之一：
 * {anchorTerm MainTypes}`main : IO Unit` 用于简单程序，这类程序不能读取其命令行参数，并且总是返回退出码 {anchorTerm MainTypes}`0`，
 * {anchorTerm MainTypes}`main : IO UInt32` 用于无参数且可能报告成功或失败的程序，并且
 * {anchorTerm MainTypes}`main : List String → IO UInt32` 用于接受命令行参数并报告成功或失败的程序。


# {lit}`do` 记法
%%%
tag := none
file := "do-Notation"
%%%

Lean 标准库提供了若干基本的 {moduleName}`IO` 动作，它们表示诸如读写文件以及与标准输入和标准输出交互等效应。
这些基础 {moduleName}`IO` 动作使用 {kw}`do` 记法组合成更大的 {moduleName}`IO` 动作；{kw}`do` 记法是一种内建的领域专用语言，用于编写带有副作用的程序描述。
一个 {kw}`do` 表达式包含一系列_语句_，它们可以是：
 * 表示 {moduleName}`IO` 动作的表达式，
 * 使用 {kw}`let` 和 {lit}`:=` 的普通局部定义，其中被定义的名称指称所给表达式的值，或者
 * 使用 {kw}`let` 和 {lit}`←` 的局部定义，其中被定义的名称指称执行给定表达式的值所得的结果。

用 {kw}`do` 编写的 {moduleName}`IO` 动作会一次执行一条语句。

此外，紧接在某个 {kw}`do` 之下出现的 {kw}`if` 和 {kw}`match` 表达式，会被隐式地视为在每个分支中都有自己的 {kw}`do`。
在 {kw}`do` 表达式内部，_嵌套动作_是指在圆括号之下紧接出现左箭头的表达式。
Lean 编译器会将它们隐式提升到最近的外围 {kw}`do`，该 {kw}`do` 可能隐式地属于某个 {kw}`match` 或 {kw}`if` 表达式的分支，并为它们赋予一个唯一名称。
随后，这个唯一名称会替换嵌套动作的原始位置。


# 编译和运行程序
%%%
tag := none
file := "Compiling-and-Running-Programs"
%%%

由单个文件和一个 {moduleName}`main` 定义组成的 Lean 程序，可以使用 {lit}`lean --run FILE` 运行。
虽然这可能是开始编写简单程序的一种不错方式，但大多数程序最终都会发展为多文件项目，并且应在运行前先进行编译。

Lean 项目被组织为_包_，包是库和可执行文件的集合，并包含有关依赖项和构建配置的信息。
包使用 Lake 描述，Lake 是一个 Lean 构建工具。
使用 {lit}`lake new` 在新目录中创建 Lake 包，或使用 {lit}`lake init` 在当前目录中创建 Lake 包。
Lake 包配置是另一种领域特定语言。
使用 {lit}`lake build` 构建项目。

# 部分性
%%%
tag := none
file := "Partiality"
%%%

遵循表达式求值的数学模型的一个后果是，每个表达式都必须有一个值。
这排除了两种情况：未覆盖某个数据类型所有构造子的不完整模式匹配，以及可能陷入无限循环的程序。
Lean 确保所有 {kw}`match` 表达式都覆盖所有情况，并确保所有递归函数要么是结构递归的，要么具有显式的终止性证明。

然而，某些真实程序需要存在无限循环的可能性，因为它们要处理可能无限的数据，例如 POSIX 流。
Lean 提供了一个逃生口：定义被标记为 {kw}`partial` 的函数不要求终止。
这要付出代价。
由于类型是 Lean 语言的一等组成部分，函数可以返回类型。
然而，部分函数不会在类型检查期间被求值，因为函数中的无限循环可能导致类型检查器进入无限循环。
此外，数学证明无法检查部分函数的定义，这意味着使用它们的程序远不那么适合形式化证明。
