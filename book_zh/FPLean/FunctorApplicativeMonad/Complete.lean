import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "完整定义" =>
%%%
tag := "complete-definitions"
file := "The-Complete-Definitions"
%%%

既然所有相关语言特性都已经介绍完毕，本节将说明 Lean 标准库中 {anchorName HonestFunctor}`Functor`、{anchorName Applicative}`Applicative` 和 {anchorName Monad}`Monad` 实际出现时的完整、真实定义。
为便于理解，这里不省略任何细节。

# 函子
%%%
tag := "complete-functor-definition"
file := "Functor"
%%%


{anchorName Applicative}`Functor` 类的完整定义使用了宇宙多态性和默认方法实现：

```anchor HonestFunctor
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
```
在这个定义中，{anchorName HonestFunctor}`Function.comp` 是函数复合，通常用 {lit}`∘` 运算符书写。
{anchorName HonestFunctor}`Function.const` 是_常量函数_，它是一个二元函数，会忽略其第二个参数。
只将此函数应用于一个参数，会产生一个总是返回同一值的函数；当 API 要求一个函数而程序并不需要针对不同参数计算不同结果时，这很有用。
{anchorName HonestFunctor}`Function.const` 的一个简单版本可以写成如下形式：

```anchor simpleConst
def simpleConst  (x : α) (_ : β) : α := x
```
将它以一个参数作为传给 {anchorTerm extras}`List.map` 的函数参数来使用，可以展示它的效用：
```anchor mapConst
#eval [1, 2, 3].map (simpleConst "same")
```
```anchorInfo mapConst
["same", "same", "same"]
```
实际函数具有如下签名：
```anchorInfo FunctionConstType
Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α
```
这里，类型实参 {anchorName HonestFunctor}`β` 是一个显式实参，因此 {anchorName HonestFunctor}`mapConst` 的默认定义提供了一个 {anchorTerm HonestFunctor}`_` 实参，指示 Lean 寻找一个唯一的类型传递给 {anchorName HonestFunctor}`Function.const`，使程序能够通过类型检查。
{anchorTerm unfoldCompConst}`Function.comp map (Function.const _)` 等价于 {anchorTerm unfoldCompConst}`fun (x : α) (y : f β) => map (fun _ => x) y`。

{anchorName HonestFunctor}`Functor` 类型类居于一个宇宙中，该宇宙是 {anchorTerm HonestFunctor}`u+1` 与 {anchorTerm HonestFunctor}`v` 中较大的那个。
这里，{anchorTerm HonestFunctor}`u` 是作为参数传给 {anchorName HonestFunctor}`f` 时所接受的宇宙层级，而 {anchorTerm HonestFunctor}`v` 是 {anchorName HonestFunctor}`f` 返回的宇宙。
要理解为什么实现 {anchorName HonestFunctor}`Functor` 类型类的结构必须位于一个大于 {anchorTerm HonestFunctor}`u` 的宇宙中，可以从该类的一个简化定义开始：

```anchor FunctorSimplified
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
```
这个类型类的结构类型等价于以下归纳类型：

```anchor FunctorDatatype
inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
```
作为参数传递给 {anchorName FunctorDatatype}`mk` 的 {lit}`map` 方法的实现包含一个函数，该函数以 {anchorTerm FunctorDatatype}`Type u` 中的两个类型作为参数。
这意味着该函数本身的类型位于 {lit}`Type (u+1)` 中，因此 {anchorName FunctorDatatype}`Functor` 也必须处于至少为 {anchorTerm FunctorDatatype}`u+1` 的层级。
类似地，该函数的其他参数具有通过应用 {anchorName FunctorDatatype}`f` 构造出的类型，因此它也必须具有至少为 {anchorTerm FunctorDatatype}`v` 的层级。
本节中的所有类型类都具有这一性质。

# 应用函子
%%%
tag := "complete-applicative-definition"
file := "Applicative"
%%%

{anchorName Applicative}`Applicative` 类型类实际上由若干更小的类构成，每个类都包含一部分相关方法。
首先是 {anchorName Applicative}`Pure` 和 {anchorName Applicative}`Seq`，它们分别包含 {anchorName Applicative}`pure` 和 {anchorName Seq}`seq`：

```anchor Pure
class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α
```

```anchor Seq
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
```

除此之外，{anchorName Applicative}`Applicative` 还依赖于 {anchorName SeqRight}`SeqRight` 以及一个类似的 {anchorName SeqLeft}`SeqLeft` 类：

```anchor SeqRight
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β
```

```anchor SeqLeft
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
```

{anchorName SeqRight}`seqRight` 函数是在{ref "alternative"}[关于 alternatives 与 validation 的小节]中引入的，从效应的角度最容易理解。
{anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`E1 *> E2` 会脱糖为 {anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`SeqRight.seqRight E1 (fun () => E2)`，可理解为先执行 {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1`，然后执行 {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`，最终只得到 {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2` 的结果。
来自 {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1` 的效应可能导致 {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2` 不运行，或者运行多次。
事实上，如果 {anchorName SeqRight}`f` 有一个 {anchorName Monad}`Monad` 实例，那么 {anchorTerm seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1 *> E2` 等价于 {lit}`do let _ ← E1; E2`，但 {anchorName SeqRight}`seqRight` 可以用于像 {anchorName Validate (module:=Examples.FunctorApplicativeMonad)}`Validate` 这样不是单子的类型。

它的近亲 {anchorName SeqLeft}`seqLeft` 非常相似，只是返回最左侧表达式的值。
{anchorTerm seqLeftSugar}`E1 <* E2` 会被脱糖为 {anchorTerm seqLeftSugar}`SeqLeft.seqLeft E1 (fun () => E2)`。
{anchorTerm seqLeftType}`SeqLeft.seqLeft` 的类型为 {anchorTerm seqLeftType}`f α → (Unit → f β) → f α`，除了它返回 {anchorTerm SeqLeft}`f α` 这一点之外，该类型与 {anchorName SeqRight}`seqRight` 的类型相同。
{anchorTerm seqLeftSugar}`E1 <* E2` 可以理解为一个程序：它先执行 {anchorName seqLeftSugar}`E1`，然后执行 {anchorName seqLeftSugar}`E2`，并返回 {anchorName seqLeftSugar}`E1` 的原始结果。
如果 {anchorName SeqLeft}`f` 有一个 {anchorName Monad}`Monad` 实例，那么 {anchorTerm seqLeftSugar}`E1 <* E2` 等价于 {lit}`do let x ← E1; _ ← E2; pure x`。
一般而言，{anchorName SeqLeft}`seqLeft` 可用于在验证或类似解析器的工作流中为某个值指定额外条件，而不改变该值本身。

{anchorName Applicative}`Applicative` 的定义扩展了所有这些类，并且还扩展了 {anchorName Applicative}`Functor`：

```anchor Applicative
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
```
完整定义 {anchorName Applicative}`Applicative` 只需要为 {anchorName Applicative}`pure` 和 {anchorName Seq}`seq` 给出定义。
这是因为来自 {anchorName Applicative}`Functor`、{anchorName SeqLeft}`SeqLeft` 和 {anchorName SeqRight}`SeqRight` 的所有方法都有默认定义。
{anchorName HonestFunctor}`Functor` 的 {anchorName HonestFunctor}`mapConst` 方法有其自身基于 {anchorName Applicative}`Functor.map` 的默认实现。
只有在新函数与默认实现行为等价但效率更高时，才应覆盖这些默认实现。
这些默认实现应被看作正确性的规范，同时也是自动生成的代码。

{anchorName SeqLeft}`seqLeft` 的默认实现非常紧凑。
将其中一些名称替换为相应的语法糖或定义，可以从另一角度理解它，因此：
```anchorTerm unfoldMapConstSeqLeft
Seq.seq (Functor.map (Function.const _) a) b
```
变为
```anchorTerm unfoldMapConstSeqLeft
fun a b => Seq.seq ((fun x _ => x) <$> a) b
```
应当如何理解 {anchorTerm unfoldMapConstSeqLeft}`(fun x _ => x) <$> a`？
这里，{anchorName unfoldMapConstSeqLeft}`a` 的类型是 {anchorTerm unfoldMapConstSeqLeft}`f α`，而 {anchorName unfoldMapConstSeqLeft}`f` 是一个函子。
如果 {anchorName unfoldMapConstSeqLeft}`f` 是 {anchorName extras}`List`，那么 {anchorTerm mapConstList}`(fun x _ => x) <$> [1, 2, 3]` 求值为 {anchorTerm mapConstList}`[fun _ => 1, fun _ => 2, fun _ => 3`。
如果 {anchorName unfoldMapConstSeqLeft}`f` 是 {anchorName mapConstOption}`Option`，那么 {anchorTerm mapConstOption}`(fun x _ => x) <$> some "hello"` 求值为 {anchorTerm mapConstOption}`some (fun _ => "hello")`。
在每种情形中，函子中的值都被替换为返回原值并忽略其参数的函数。
当与 {anchorName Seq}`seq` 结合时，此函数会丢弃来自 {anchorName Seq}`seq` 的第二个参数的值。

{anchorName SeqRight}`seqRight` 的默认实现非常相似，只是 {anchorName FunctionConstType}`Function.const` 有一个额外的参数 {anchorName Applicative}`id`。
可以用类似的方式理解这个定义：先引入一些标准的语法糖，然后将某些名称替换为它们的定义：
```anchorEvalSteps unfoldMapConstSeqRight
fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
===>
fun a b => Seq.seq ((fun _ => id) <$> a) b
===>
fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
===>
fun a b => Seq.seq ((fun _ x => x) <$> a) b
```
应当如何理解 {anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a`？
例子再次很有帮助。
{anchorTerm mapConstIdList}`fun _ x => x) <$> [1, 2, 3]` 等价于 {anchorTerm mapConstIdList}`[fun x => x, fun x => x, fun x => x]`，而 {anchorTerm mapConstIdOption}`(fun _ x => x) <$> some "hello"` 等价于 {anchorTerm mapConstIdOption}`some (fun x => x)`。
换言之，{anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a` 保留了 {anchorName unfoldMapConstSeqRight}`a` 的整体形状，但每个值都被替换为恒等函数。
从效果的角度看，{anchorName unfoldMapConstSeqRight}`a` 的副作用会发生，但当它与 {anchorName Seq}`seq` 一起使用时，其值会被丢弃。

# 单子
%%%
tag := "complete-monad-definition"
file := "Monad"
%%%

正如 {anchorName Applicative}`Applicative` 的组成操作被拆分到各自的类型类中一样，{anchorName Bind}`Bind` 也有自己的类：

```anchor Bind
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β
```
{anchorName Monad}`Monad` 用 {anchorName Bind}`Bind` 扩展了 {anchorName Applicative}`Applicative`：

```anchor Monad
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
```
追踪整个层级结构中继承方法与默认方法的集合可知，一个 {anchorName Monad}`Monad` 实例只需要实现 {anchorName Bind}`bind` 和 {anchorName Pure}`pure`。
换言之，{anchorName Monad}`Monad` 实例会自动产生 {anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft`、{anchorName SeqRight}`seqRight`、{anchorName HonestFunctor}`map` 和 {anchorName HonestFunctor}`mapConst` 的实现。
从 API 边界的角度看，任何具有 {anchorName Monad}`Monad` 实例的类型都会获得 {anchorName Bind}`Bind`、{anchorName Pure}`Pure`、{anchorName Seq}`Seq`、{anchorName Applicative}`Functor`、{anchorName SeqLeft}`SeqLeft` 和 {anchorName SeqRight}`SeqRight` 的实例。


# 练习
%%%
tag := "complete-functor-applicative-monad-exercises"
file := "Exercises"
%%%

 1. 通过推演诸如 {anchorName mapConstOption}`Option` 和 {anchorName ApplicativeExcept (module:=Examples.FunctorApplicativeMonad)}`Except` 这样的例子，理解 {anchorName Monad}`Monad` 中 {anchorName HonestFunctor}`map`、{anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft` 和 {anchorName SeqRight}`seqRight` 的默认实现。换言之，将 {anchorName Bind}`bind` 和 {anchorName Pure}`pure` 的定义代入这些默认定义，并将其化简，以恢复出手写时会写出的版本 {anchorName HonestFunctor}`map`、{anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft` 和 {anchorName SeqRight}`seqRight`。
 2. 在纸上或文本文件中向自己证明，{anchorName HonestFunctor}`map` 和 {anchorName Seq}`seq` 的默认实现满足 {anchorName Applicative}`Functor` 和 {anchorName Applicative}`Applicative` 的约定。在这个论证中，你可以使用 {anchorName Monad}`Monad` 约定中的规则以及通常的表达式求值。
