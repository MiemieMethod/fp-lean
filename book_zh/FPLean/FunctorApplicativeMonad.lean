import VersoManual
import FPLean.Examples
import FPLean.FunctorApplicativeMonad.Inheritance
import FPLean.FunctorApplicativeMonad.Applicative
import FPLean.FunctorApplicativeMonad.ApplicativeContract
import FPLean.FunctorApplicativeMonad.Alternative
import FPLean.FunctorApplicativeMonad.Universes
import FPLean.FunctorApplicativeMonad.Complete
import FPLean.FunctorApplicativeMonad.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "函子、应用函子与单子" =>
%%%
file := "Functors___-Applicative-Functors___-and-Monads"
%%%

{anchorTerm FunctorPair}`Functor` 和 {moduleName}`Monad` 都描述了针对仍在等待一个类型参数的类型的操作。
理解它们的一种方式是：{anchorTerm FunctorPair}`Functor` 描述其中所含数据可以被变换的容器，而 {moduleName}`Monad` 描述带有副作用的程序的一种编码。
然而，这种理解并不完整。
毕竟，{moduleName}`Option` 同时具有 {moduleName}`Functor` 和 {moduleName}`Monad` 的实例，并且同时表示一个可选值 _and_ 一个可能无法返回值的计算。

从数据结构的角度看，{anchorName AlternativeOption}`Option` 有些像可空类型，或像至多只能包含一个条目的列表。
从控制结构的角度看，{anchorName AlternativeOption}`Option` 表示一种可能在没有结果的情况下提前终止的计算。
通常，使用 {anchorName FunctorValidate}`Functor` 实例的程序最容易被理解为把 {anchorName AlternativeOption}`Option` 用作数据结构，而使用 {anchorName MonadExtends}`Monad` 实例的程序最容易被理解为使用 {anchorName AlternativeOption}`Option` 来允许提前失败；不过，学会熟练运用这两种视角，是精通函数式编程的重要组成部分。

函子与单子之间存在更深层的关系。
事实证明，_每个单子都是函子_。
另一种说法是，单子抽象比函子抽象更强大，因为并非每个函子都是单子。
此外，还存在一种额外的中间抽象，称为_应用函子_，它具有足够的表达能力来编写许多有趣的程序，同时又允许使用无法采用 {anchorName MonadExtends}`Monad` 接口的库。
类型类 {anchorName ApplicativeValidate}`Applicative` 提供了应用函子的可重载操作。
每个单子都是应用函子，每个应用函子都是函子，但反过来并不成立。

{include 1 FPLean.FunctorApplicativeMonad.Inheritance}

{include 1 FPLean.FunctorApplicativeMonad.Applicative}

{include 1 FPLean.FunctorApplicativeMonad.ApplicativeContract}

{include 1 FPLean.FunctorApplicativeMonad.Alternative}

{include 1 FPLean.FunctorApplicativeMonad.Universes}

{include 1 FPLean.FunctorApplicativeMonad.Complete}

{include 1 FPLean.FunctorApplicativeMonad.Summary}
