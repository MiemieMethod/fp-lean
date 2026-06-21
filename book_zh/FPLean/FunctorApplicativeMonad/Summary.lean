import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "小结" =>
%%%
tag := "structure-applicative-monad-summary"
file := "Summary"
%%%

# 类型类与结构
%%%
tag := none
file := "Type-Classes-and-Structures"
%%%

在幕后，类型类由结构表示。
定义一个类会定义一个结构，并额外创建一张空的实例表。
定义一个实例会创建一个值：该值要么以该结构为其类型，要么是一个能够返回该结构的函数；同时还会向实例表中添加一个条目。
实例搜索由查询实例表来构造实例组成。
结构和类都可以为字段提供默认值（即方法的默认实现）。

# 结构与继承
%%%
tag := none
file := "Structures-and-Inheritance"
%%%

结构可以从其他结构继承。
在幕后，从另一个结构继承的结构会包含原结构的一个实例作为字段。
换言之，继承是用组合实现的。
使用多重继承时，为避免菱形问题，只使用额外父结构中的唯一字段；而通常用于提取父值的函数则改为组织成构造一个父值。
记录点记法会考虑结构继承。

由于类型类只是应用了某些额外自动化机制的结构，所有这些特性在类型类中都可用。
结合默认方法，这可用于创建细粒度的接口层次；然而它不会给客户端施加沉重负担，因为大型类所继承的小型类可以被自动实现。

# 应用函子
%%%
tag := none
file := "Applicative-Functors"
%%%

应用函子是带有两个额外操作的函子：
 * {anchorName Applicative}`pure`，它与用于 {anchorName Monad}`Monad` 的运算符相同
 * {anchorName Seq}`seq`，它允许在函子的语境中应用函数。

虽然单子可以表示带有控制流的任意程序，但应用函子只能从左到右运行函数参数。
由于它们能力较弱，因此为依该接口编写的程序提供的控制也较少，而方法的实现者则拥有更大的自由度。
有些有用的类型可以实现 {anchorName Applicative}`Applicative`，但不能实现 {anchorName Monad}`Monad`。

事实上，类型类 {anchorName HonestFunctor}`Functor`、{anchorName Applicative}`Applicative` 和 {anchorName Monad}`Monad` 构成了一个能力层次。
沿着层次向上，从 {anchorName HonestFunctor}`Functor` 走向 {anchorName Monad}`Monad`，可以编写能力更强的程序，但实现这些更强类型类的类型更少。
多态程序应当尽可能使用较弱的抽象来编写，而数据类型则应当获得尽可能强的实例。
这会最大化代码复用。
能力更强的类型类扩展能力较弱的类型类，这意味着 {anchorName Monad}`Monad` 的一个实现会免费提供 {anchorName HonestFunctor}`Functor` 和 {anchorName Applicative}`Applicative` 的实现。

每个类都有一组需要实现的方法，以及一个相应的约定，用以规定这些方法的附加规则。
针对这些接口编写的程序期望这些附加规则得到遵守；若不遵守，程序可能出现错误。
以 {anchorName Applicative}`Applicative` 的方法定义 {anchorName HonestFunctor}`Functor` 的方法，以及以 {anchorName Monad}`Monad` 的方法定义 {anchorName Applicative}`Applicative` 的方法所得的默认实现，将遵守这些规则。

# 宇宙
%%%
tag := none
file := "Universes"
%%%

为了使 Lean 既可用作编程语言，又可用作定理证明器，对该语言施加某些限制是必要的。
这包括对递归函数的限制，以确保它们要么全都终止，要么被标记为 {kw}`partial`，并被写成返回非空类型。
此外，必须不可能将某些种类的逻辑悖论表示为类型。

排除某些悖论的限制之一是：每个类型都被分配到一个_宇宙_。
宇宙是诸如 {anchorTerm extras}`Prop`、{anchorTerm extras}`Type`、{anchorTerm extras}`Type 1`、{anchorTerm extras}`Type 2` 等类型。
这些类型描述其他类型——正如 {anchorTerm extras}`0` 和 {anchorTerm extras}`17` 由 {anchorName extras}`Nat` 描述，{anchorName extras}`Nat` 自身由 {anchorTerm extras}`Type` 描述，而 {anchorTerm extras}`Type` 由 {anchorTerm extras}`Type 1` 描述。
以类型作为参数的函数，其类型必须位于比该参数所在宇宙更大的宇宙中。

由于每个声明的数据类型都有一个宇宙，把类型像数据一样使用的代码很快就会变得繁琐，因为每个多态类型都需要复制粘贴出可从 {anchorTerm extras}`Type 1` 接受参数的版本。
称为_宇宙多态_的特性允许 Lean 程序和数据类型把宇宙层级作为参数，正如普通多态允许程序把类型作为参数一样。
一般而言，Lean 库在实现多态操作库时应当使用宇宙多态。
