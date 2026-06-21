import VersoManual
import FPLean.Examples

import FPLean.DependentTypes.IndexedFamilies
import FPLean.DependentTypes.UniversePattern
import FPLean.DependentTypes.TypedQueries
import FPLean.DependentTypes.IndicesParametersUniverses
import FPLean.DependentTypes.Pitfalls
import FPLean.DependentTypes.Summary

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes"

#doc (Manual) "依值类型编程" =>
%%%
file := "Programming-with-Dependent-Types"
%%%

在大多数静态类型编程语言中，类型世界与程序世界之间存在一道严密的隔离。
类型和程序具有不同的语法，并且在不同的时刻被使用。
类型通常在编译时使用，用来检查程序是否遵守某些不变式。
程序在运行时使用，用来实际执行计算。
当二者发生交互时，通常表现为某种类型分情况运算符，例如 “instance-of” 检查，或某种强制转换运算符；这些运算符向类型检查器提供原本不可获得的信息，并在运行时加以验证。
换言之，这种交互由类型被插入到程序世界中构成，在那里它们获得某种有限的运行时含义。

Lean 并不强加这种严格的分离。
在 Lean 中，程序可以计算类型，而类型也可以包含程序。
将程序置于类型之中，使得程序的全部计算能力可以在编译时使用；而函数能够返回类型这一能力，则使类型成为编程过程中的一等参与者。

_依值类型_ 是包含非类型表达式的类型。
依值类型的一个常见来源是函数的具名参数。
例如，函数 {anchorName natOrStringThree}`natOrStringThree` 根据传入的是哪个 {anchorName natOrStringThree}`Bool`，返回自然数或字符串：

```anchor natOrStringThree
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

依值类型的更多例子包括：
 * {ref "polymorphism"}[关于多态性的导论性一节]包含 {anchorName posOrNegThree (module:= Examples.Intro)}`posOrNegThree`，其中函数的返回类型依赖于参数的值。
 * {ref "literal-numbers"}[{anchorName OfNat (module := Examples.Classes)}`OfNat` 类型类]依赖于所使用的具体自然数文字量。
 * {ref "validated-input"}[验证器示例中使用的 {anchorName CheckedInput (module := Examples.FunctorApplicativeMonad)}`CheckedInput` 结构] 依赖于进行验证的年份。
 * {ref "subtypes"}[子类型]包含引用特定值的命题。
 * 实质上，所有有意义的命题，包括那些判定 {ref "props-proofs-indexing"}[数组索引记法] 有效性的命题，都是包含值的类型，因而都是依值类型。

依值类型极大地增强了类型系统的能力。
返回类型能够随参数值分支，这种灵活性使得可以编写在其他类型系统中难以赋予类型的程序。
同时，依值类型允许类型签名限制函数可能返回哪些值，从而能够在编译时强制维护强不变式。

然而，使用依值类型进行编程可能相当复杂，并且需要一整套超出函数式编程本身的技能。
表达力强的规约可能很难满足，而且确实存在把自己绕进死结、无法完成程序的风险。
另一方面，这一过程也可能带来新的理解，而这种理解可以表达为一个更精细且能够被满足的类型。
虽然本章只是触及依值类型编程的表面，但它是一个深刻的主题，值得用整本书专门讨论。

{include 1 FPLean.DependentTypes.IndexedFamilies}

{include 1 FPLean.DependentTypes.UniversePattern}

{include 1 FPLean.DependentTypes.TypedQueries}

{include 1 FPLean.DependentTypes.IndicesParametersUniverses}

{include 1 FPLean.DependentTypes.Pitfalls}

{include 1 FPLean.DependentTypes.Summary}
