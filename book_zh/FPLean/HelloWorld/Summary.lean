import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External


open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.HelloWorld"

#doc (Manual) "总结" =>
%%%
tag := "hello-world-summary"
%%%

# 求值与执行
%%%
tag := none
%%%

副作用是程序执行中超出数学表达式求值范围的部分，例如读取文件、抛出异常或驱动工业机械。虽然大多数语言允许在求值期间发生副作用，但 Lean 不会。
相反，Lean 有一个名为 {moduleName}`IO` 的类型，它表示使用副作用的程序的*描述*。
这些描述然后由语言的运行时系统执行，该系统调用 Lean 表达式求值器来执行特定计算。
{moduleTerm}`IO α` 类型的值被称为 *{moduleName}`IO` 活动*。
最简单的是 {moduleName}`pure`，它返回其参数且没有实际副作用。

{moduleName}`IO` 活动也可以理解为以整个世界为参数并返回发生副作用的新世界的函数。
在幕后，{moduleName}`IO` 库确保世界永远不会被复制、创建或销毁。
虽然这种副作用模型实际上无法实现，因为整个宇宙太大而无法放入内存，但真实世界可以由通过程序传递的令牌表示。

程序启动时会执行 {moduleName}`IO` 活动 {anchorName MainTypes}`main`。
{anchorName MainTypes}`main` 可以有三种类型之一：
 * {anchorTerm MainTypes}`main : IO Unit` 用于无法读取命令行参数且始终返回退出代码 {anchorTerm MainTypes}`0` 的简单程序，
 * {anchorTerm MainTypes}`main : IO UInt32` 用于没有参数但可能发出成功或失败信号的程序，以及
 * {anchorTerm MainTypes}`main : List String → IO UInt32` 用于接受命令行参数并发出成功或失败信号的程序。


# {lit}`do` 记法
%%%
tag := none
%%%

Lean 标准库提供了许多基本的 {moduleName}`IO` 活动，这些活动表示诸如读取和写入文件以及与标准输入和标准输出交互等效果。
这些基本的 {moduleName}`IO` 活动使用 {kw}`do` 记法组合成更大的 {moduleName}`IO` 活动，
这是一种内置的领域特定语言，用于编写带副作用程序的描述。
{kw}`do` 表达式包含一系列*语句*，这些语句可能是：
 * 表示 {moduleName}`IO` 活动的表达式，
 * 使用 {kw}`let` 和 {lit}`:=` 的普通局部定义，其中定义的名称引用所提供表达式的值，或
 * 使用 {kw}`let` 和 {lit}`←` 的局部定义，其中定义的名称引用执行所提供表达式的值的结果。

使用 {kw}`do` 编写的 {moduleName}`IO` 活动一次执行一个语句。

此外，直接出现在 {kw}`do` 下的 {kw}`if` 和 {kw}`match` 表达式被隐式认为在每个分支中都有自己的 {kw}`do`。
在 {kw}`do` 表达式内部，*嵌套活动*是括号下紧跟左箭头的表达式。
Lean 编译器隐式地将它们提升到最近的封闭 {kw}`do`，这可能是 {kw}`match` 或 {kw}`if` 表达式分支的隐式部分，并给它们一个唯一的名称。
这个唯一的名称然后替换嵌套活动的原始位置。


# 编译和运行程序
%%%
tag := none
%%%

由具有 {moduleName}`main` 定义的单个文件组成的 Lean 程序可以使用 {lit}`lean --run FILE` 运行。
虽然这可能是开始简单程序的好方法，但大多数程序最终会升级到多文件项目，应该在运行之前编译。

Lean 项目组织成*包*，这些包是库和可执行文件的集合，以及有关依赖项和构建配置的信息。
包使用 Lake（一个 Lean 构建工具）来描述。
使用 {lit}`lake new` 在新目录中创建 Lake 包，或使用 {lit}`lake init` 在当前目录中创建一个。
Lake 包配置是另一种领域特定语言。
使用 {lit}`lake build` 来构建项目。

# 偏函数
%%%
tag := none
%%%

遵循表达式求值的数学模型的一个结果，就是每个表达式都必定有一个值。这排除了不完全的模式匹配（即无法覆盖数据类型的全部构造器）和可能陷入无限循环的程序。
Lean 确保所有 {kw}`match` 表达式覆盖所有情况，并且所有递归函数要么是结构递归的，要么有显式的终止证明。

然而，一些真实程序需要无限循环的可能性，因为它们处理可能无限的数据，例如 POSIX 流。
Lean 提供了一个逃生舱：定义被标记为 {kw}`partial` 的偏函数不需要终止。
这是有代价的。
由于类型是 Lean 语言的一等部分，函数可以返回类型。
然而，偏函数在类型检查期间不会被求值，因为函数中的无限循环可能会导致类型检查器进入死循环。此外，数学证明无法检查偏函数的定义，这意味着使用它们的程序更难进行形式化证明。
