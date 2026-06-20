import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "总结" =>
%%%
tag := "monads-summary"
%%%

# 编码副作用
%%%
tag := none
%%%

Lean 是一种纯函数式语言。这意味着它不包含副作用，例如可变变量、日志记录或异常。
但是，大多数副作用都可以使用函数和归纳类型或结构体的组合进行*编码*。
例如，可变状态可以编码为从初始状态到一对最终状态和结果的函数，
异常可以编码为具有成功终止构造子和错误构造子的归纳类型。

每组编码的作用都是一种类型。因此，如果程序使用这些编码作用，那么这在它的类型中是显而易见的。
函数式编程并不意味着程序不能使用作用，它只是要求它们 *诚实地* 说明它们使用的作用。
Lean 类型签名不仅描述了函数期望的参数类型和它返回的结果类型，还描述了它可能使用的作用。

# 单子类型类
%%%
tag := none
%%%

在允许在任何地方使用作用的语言中编写纯函数式程序是可能的。
例如，{python}`2 + 3` 是一个有效的 Python 程序，它没有任何作用。
类似地，组合具有作用的程序需要一种方法来说明作用必须发生的顺序。
毕竟，异常是在修改变量之前还是之后抛出是有区别的。

类型类 {anchorName FakeMonad}`Monad` 刻画了这两个重要属性。它有两个方法：{anchorName FakeMonad}`pure` 表示没有副作用的程序，
{anchorName FakeMonad}`bind` 顺序执行有副作用的程序。{anchorName FakeMonad}`Monad` 实例的约束确保了 {anchorName FakeMonad}`bind` 和 {anchorName FakeMonad}`pure` 实际上刻画了纯计算和顺序执行。

# 单子的 {kw}`do`-记法
%%%
tag := none
%%%

{kw}`do` 符号不仅限于 {moduleName}`IO`，它也适用于任何单子。
它允许使用单子的程序以类似于面向语句的语言的风格编写，语句一个接一个地顺序执行。
此外，{kw}`do`-记法还支持许多其他方便的简写，例如嵌套动作。
使用 {kw}`do` 编写的程序在幕后会被翻译为 {lit}`>>=` 的应用。

# 定制单子
%%%
tag := none
%%%

不同的语言提供不同的副作用集。虽然大多数语言都具有可变变量和文件 I/O，
但并非所有语言都具有异常等特性。其他语言提供罕见或独特的副作用，
例如 Icon 基于搜索的程序执行、Scheme 和 Ruby 的续体以及 Common Lisp 的可恢复异常。
用单子对副作用进行编码的一个优点是，程序不受语言提供的副作用集的限制。
由于 Lean 被设计为能方便地使用任何单子进行编程，
因此程序员可以自由选择最适合任何给定应用的副作用集。

# {lit}`IO` 单子
%%%
tag := none
%%%

可以在现实世界中产生影响的程序在 Lean 中被写作 {moduleName}`IO` 活动。
{moduleName}`IO` 是众多单子中的一个。{moduleName}`IO` 单子对状态和异常进行编码，其中状态用于跟踪世界的状态，
异常则对失败和恢复进行建模。
