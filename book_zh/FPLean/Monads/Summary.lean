import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "小结" =>
%%%
tag := "monads-summary"
file := "Summary"
%%%

# 编码副作用
%%%
tag := none
file := "Encoding-Side-Effects"
%%%

Lean 是一种纯函数式语言。
这意味着它不包含可变变量、日志记录或异常等副作用。
然而，大多数副作用都可以通过函数与归纳类型或结构的组合来_编码_。
例如，可变状态可以编码为一个函数，它从初始状态映射到由最终状态和结果组成的配对；异常可以编码为一个归纳类型，其构造子分别表示成功终止和错误。

每一组被编码的效应都是一个类型。
因此，如果一个程序使用这些被编码的效应，那么这一点会在其类型中显现出来。
函数式编程并不意味着程序不能使用效应，它只是要求程序对自己使用了哪些效应保持_诚实_。
Lean 的类型签名不仅描述函数期望的参数类型以及它返回的结果类型，还描述它可能使用哪些效应。

# Monad 类型类
%%%
tag := none
file := "The-Monad-Type-Class"
%%%

在允许任意位置出现效应的语言中，也可以编写纯函数式程序。
例如，{python}`2 + 3` 是一个完全没有效应的合法 Python 程序。
类似地，组合具有效应的程序需要一种方式来说明这些效应必须发生的顺序。
毕竟，异常是在修改变量之前还是之后抛出，是有区别的。

类型类 {anchorName FakeMonad}`Monad` 刻画了这两个重要性质。
它有两个方法：{anchorName FakeMonad}`pure` 表示没有效果的程序，而 {anchorName FakeMonad}`bind` 对具有效果的程序进行顺序组合。
{anchorName FakeMonad}`Monad` 实例的约定确保 {anchorName FakeMonad}`bind` 与 {anchorName FakeMonad}`pure` 确实刻画纯计算与顺序组合。

# 单子的 {kw}`do` 记法
%%%
tag := none
file := "do-Notation-for-Monads"
%%%

{kw}`do` 记法并不限于 {moduleName}`IO`，而是适用于任意单子。
它允许使用单子的程序以一种类似面向语句语言的风格来编写，其中语句一个接一个地顺序执行。
此外，{kw}`do` 记法还支持若干额外的便捷简写，例如嵌套动作。
用 {kw}`do` 编写的程序会在幕后被翻译为对 {lit}`>>=` 的应用。

# 自定义单子
%%%
tag := none
file := "Custom-Monads"
%%%

不同语言提供不同的副作用集合。
虽然大多数语言具有可变变量和文件 I/O，但并非所有语言都有异常之类的特性。
其他语言提供少见或独特的效应，例如 Icon 基于搜索的程序执行、Scheme 和 Ruby 的续延，以及 Common Lisp 的可恢复异常。
用单子对效应进行编码的一个优点是，程序并不局限于该语言所提供的效应集合。
由于 Lean 被设计为使得使用任意单子编程都很方便，程序员可以自由地为任何给定应用精确选择有意义的副作用集合。

# {lit}`IO` 单子
%%%
tag := none
file := "The-IO-Monad"
%%%

能够影响现实世界的程序在 Lean 中被写作 {moduleName}`IO` 动作。
{moduleName}`IO` 是众多单子之一。
{moduleName}`IO` 单子编码状态和异常，其中状态用于跟踪世界的状态，而异常用于建模失败与恢复。
