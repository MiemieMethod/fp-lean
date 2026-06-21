import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers"

#doc (Manual) "小结" =>
%%%
tag := "monad-transformer-summary"
file := "Summary"
%%%

# 组合单子
%%%
tag := none
file := "Combining-Monads"
%%%

从头编写一个单子时，有一些设计模式往往能够描述每种效应被加入该单子的方式。
读取器效应通过使单子的类型成为从读取器环境出发的函数来加入；状态效应通过包含一个从初始状态到“值与最终状态组成的对”的函数来加入；失败或异常通过在返回类型中包含一个和类型来加入；日志记录或其他输出通过在返回类型中包含一个积类型来加入。
已有的单子也可以成为返回类型的一部分，从而允许将它们的效应包含在新的单子中。

通过定义_单子转换器_，这些设计模式被制成可复用软件组件的库；单子转换器会向某个基础单子添加一种效果。
单子转换器以较简单的单子类型作为参数，并返回增强后的单子类型。
至少，一个单子转换器应提供以下实例：
 1. 一个假定内部类型已经是单子的 {anchorName Summary}`Monad` 实例
 2. 一个 {anchorName Summary}`MonadLift` 实例，用于将动作从内部单子翻译到经转换的单子

单子转换器可以实现为多态结构或归纳数据类型，但它们最常实现为从底层单子类型到增强后单子类型的函数。

# 用于效应的类型类
%%%
tag := none
file := "Type-Classes-for-Effects"
%%%

一种常见的设计模式是：通过定义一个具有特定效应的单子、一个将该效应加入另一单子的单子转换器，以及一个为该效应提供通用接口的类型类，来实现该特定效应。
这允许程序只需指定它们需要哪些效应；于是调用者可以提供任何具有相应效应的单子。

有时，辅助类型信息（例如，在提供状态的单子中状态的类型，或在提供异常的单子中异常的类型）是一个输出参数，而有时则不是。
输出参数对于每种效果只使用一次的简单程序最为有用；但当给定程序中使用同一种效果的多个实例时，它会带来风险，使类型检查器过早地确定为错误的类型。
因此，通常会同时提供两个版本，其中类型类的普通参数版本具有以 {lit}`-Of` 结尾的名称。

# 单子转换器不可交换
%%%
tag := none
file := "Monad-Transformers-Don___t-Commute"
%%%

需要注意的是，改变单子中转换器的顺序可能会改变使用该单子的程序的含义。
例如，重新排序 {anchorName Summary}`StateT` 和 {anchorTerm Summary}`ExceptT` 可能导致程序在抛出异常时丢失状态修改，也可能导致程序保留这些修改。
虽然大多数命令式语言只提供后者，但单子转换器所提供的更高灵活性要求人们进行思考并仔细选择适合当前任务的种类。

# 用于单子转换器的 {kw}`do`-记号
%%%
tag := none
file := "do-Notation-for-Monad-Transformers"
%%%

Lean 的 {kw}`do` 块支持提前返回，即以某个值终止该块；支持局部可变变量、带有 {kw}`break` 和 {kw}`continue` 的 {kw}`for` 循环，以及单分支的 {kw}`if` 语句。
虽然这似乎是在引入命令式特性，从而会妨碍使用 Lean 编写证明，但事实上，这不过是某些单子转换器常见用法的一种更便利的语法。
在幕后，无论 {kw}`do` 块写在何种单子中，都会通过适当地使用 {anchorName Summary}`ExceptT` 和 {anchorName Summary}`StateT` 对其进行转换，以支持这些额外的效应。
