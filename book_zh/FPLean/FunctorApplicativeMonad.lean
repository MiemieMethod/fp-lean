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

#doc (Manual) "函子、应用函子和单子" =>

{anchorTerm FunctorPair}`Functor` 和 {moduleName}`Monad` 都描述了那些仍在等待类型参数的类型的操作。一种理解它们的方式是，{anchorTerm FunctorPair}`Functor` 描述了容器，其中容器内的数据可以被转换，而 {moduleName}`Monad` 描述了具有副作用的程序编码。然而，这种理解是不完整的。毕竟，{moduleName}`Option` 同时拥有 {anchorTerm FunctorPair}`Functor` 和 {moduleName}`Monad` 的实例，并且同时代表着一个可选值 *和* 一个可能无法返回值的计算。

从数据结构的角度来看，{anchorName AlternativeOption}`Option` 有点像一个可为空的类型，或者像一个最多可以包含一个条目的列表。从控制结构的角度来看，{anchorName AlternativeOption}`Option` 代表着一种可能会提前终止而没有结果的计算。通常，使用 {anchorName FunctorValidate}`Functor` 实例的程序最容易被理解为将 {anchorName AlternativeOption}`Option` 用作数据结构，而使用 {anchorName MonadExtends}`Monad` 实例的程序则更容易被理解为将 {anchorName AlternativeOption}`Option` 用于支持早期失败，但熟练地掌握这两种视角对于精通函数式编程至关重要。

函子 (Functor) 和 单子 (Monad) 之间有一个更深层次的关系。事实证明，*每个单子都是一个函子*。换句话说，单子抽象 (Monad Abstraction) 比函子抽象 (Functor Abstraction) 更强大，因为不是每个函子都是单子。此外，还有一个额外的中间抽象，被称为*应用函子* (Applicative Functors)，它有足够的能力来编写许多有趣的程序，而且还适用于那些无法使用 {anchorName MonadExtends}`Monad` 接口的库。类型类 {anchorName ApplicativeValidate}`Applicative` 提供了应用函子的可重载操作。每个单子都是一个应用函子，而每个应用函子也都是一个函子，但反之则不成立。

{include 1 FPLean.FunctorApplicativeMonad.Inheritance}

{include 1 FPLean.FunctorApplicativeMonad.Applicative}

{include 1 FPLean.FunctorApplicativeMonad.ApplicativeContract}

{include 1 FPLean.FunctorApplicativeMonad.Alternative}

{include 1 FPLean.FunctorApplicativeMonad.Universes}

{include 1 FPLean.FunctorApplicativeMonad.Complete}

{include 1 FPLean.FunctorApplicativeMonad.Summary}
