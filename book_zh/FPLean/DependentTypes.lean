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

#doc (Manual) "使用依值类型编程" =>

在多数静态类型程序设计语言中，类型世界与程序世界之间存在严密的隔离。
类型和程序具有不同的语法，并且在不同的阶段使用。
类型通常在编译时使用，用来检查程序是否遵守某些不变性。
程序则在运行时使用，用来实际执行计算。
二者发生交互时，通常表现为类似“instance-of”检查的类型分类运算符，或某种强制类型转换运算符；这些运算符向类型检查器提供原本无法获得、但将在运行时验证的信息。
换言之，这种交互就是把类型插入程序世界，使它们获得某种有限的运行时意义。

Lean 并不强加这种严格分离。
在 Lean 中，程序可以计算类型，类型也可以包含程序。
把程序放入类型，使程序的全部计算能力能够在编译时使用；而函数能够返回类型这一事实，则使类型成为程序设计过程中的一等参与者。

_依值类型_是包含非类型表达式的类型。
依值类型的一个常见来源是函数的具名参数。
例如，函数 {anchorName natOrStringThree}`natOrStringThree` 会根据传入的 {anchorName natOrStringThree}`Bool` 值，返回一个自然数或一个字符串：

```anchor natOrStringThree
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

更多依值类型的例子包括：
 * {ref "polymorphism"}[多态性简介] 包含 {anchorName posOrNegThree (module:= Examples.Intro)}`posOrNegThree`，其返回类型取决于参数的值。
 * {ref "literal-numbers"}[{anchorName OfNat (module := Examples.Classes)}`OfNat` 类型类] 取决于使用的特定自然数字面量。
 * {ref "validated-input"}[{anchorName CheckedInput (module := Examples.FunctorApplicativeMonad)}`CheckedInput` 结构] 中依赖于验证发生年份的验证器的例子。
 * {ref "subtypes"}[子类型] 中包含引用特定值的命题。
 * 基本上所有有趣的命题都是包含值的类型，因此是依值类型，包括决定 {ref "props-proofs-indexing"}[数组索引表示法] 有效性的命题。

依值类型极大增强了类型系统的表达能力。
返回类型能够随参数值分支，这种灵活性使我们能够编写在其他类型系统中难以赋予类型的程序。
同时，依值类型允许类型签名限制函数可以返回哪些值，从而能够在编译时强制保证很强的不变性。

然而，使用依值类型编程可能相当复杂，并且需要一整套超出函数式编程本身的技能。
富有表达力的规约可能很难满足，确实存在把自己绕进死结、最终无法完成程序的风险。
另一方面，这一过程也可能带来新的理解，而这种理解又可以表达为一个更精细且能够满足的类型。
本章只是触及依值类型编程的表层；这是一个深刻的主题，完全值得另写一本书来讨论。

{include 1 FPLean.DependentTypes.IndexedFamilies}

{include 1 FPLean.DependentTypes.UniversePattern}

{include 1 FPLean.DependentTypes.TypedQueries}

{include 1 FPLean.DependentTypes.IndicesParametersUniverses}

{include 1 FPLean.DependentTypes.Pitfalls}

{include 1 FPLean.DependentTypes.Summary}
