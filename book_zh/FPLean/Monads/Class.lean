import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "Monad 类型类" =>
%%%
tag := "monad-type-class"
file := "The-Monad-Type-Class"
%%%

:::paragraph
不必为每个是单子的类型分别导入像 {lit}`ok` 或 {lit}`andThen` 这样的运算符，Lean 标准库包含一个类型类，允许对它们进行重载，从而同一组运算符可用于_任意_单子。
单子有两个操作，它们等价于 {lit}`ok` 和 {lit}`andThen`：

```anchor FakeMonad
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
```
这个定义略作了简化。
Lean 库中的实际定义稍微更复杂一些，并将在后文给出。
:::

:::paragraph
可以通过调整它们各自的 {lit}`andThen` 操作的定义，来创建 {anchorName MonadOptionExcept}`Option` 和 {anchorTerm MonadOptionExcept}`Except ε` 的 {anchorName MonadOptionExcept}`Monad` 实例：

```anchor MonadOptionExcept
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x
```
:::

:::paragraph
例如，{lit}`firstThirdFifthSeventh` 曾分别针对 {anchorTerm Names}`Option α` 和 {anchorTerm Names}`Except String α` 返回类型来定义。
现在，它可以针对_任何_单子以多态方式定义。
不过，它确实需要一个查找函数作为参数，因为不同的单子可能会以不同方式无法找到结果。
{anchorName FakeMonad}`bind` 的中缀版本是 {lit}`>>=`，它在示例中扮演与 {lit}`~~>` 相同的角色。

```anchor firstThirdFifthSeventhMonad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
:::

:::paragraph
给定慢速哺乳动物和快速鸟类的示例列表，{anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` 的这一实现可以与 {moduleName}`Option` 一起使用：

```anchor animals
def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]
```
```anchor noneSlow
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
```
```anchorInfo noneSlow
none
```
```anchor someFast
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
```
```anchorInfo someFast
some ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
:::

:::paragraph
在将 {anchorName getOrExcept}`Except` 的查找函数 {lit}`get` 重命名为更具体的名称之后，完全相同的 {anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` 实现也可以与 {anchorName getOrExcept}`Except` 一起使用：

```anchor getOrExcept
def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none =>
    Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x =>
    Except.ok x
```
```anchor errorSlow
#eval firstThirdFifthSeventh getOrExcept slowMammals
```
```anchorInfo errorSlow
Except.error "Index 2 not found (maximum is 1)"
```
```anchor okFast
#eval firstThirdFifthSeventh getOrExcept fastBirds
```
```anchorInfo okFast
Except.ok ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
{anchorName firstThirdFifthSeventhMonad}`m` 必须具有一个 {anchorName firstThirdFifthSeventhMonad}`Monad` 实例这一事实意味着 {lit}`>>=` 和 {anchorName firstThirdFifthSeventhMonad}`pure` 操作是可用的。
:::

# 一般的单子操作
%%%
tag := "monad-class-polymorphism"
file := "General-Monad-Operations"
%%%

:::paragraph
由于许多不同类型都是单子，对_任意_单子具有多态性的函数非常强大。
例如，函数 {anchorName mapM}`mapM` 是 {anchorName Names (show:=map)}`Functor.map` 的一个版本，它使用 {anchorName mapM}`Monad` 来顺序执行并组合函数应用所得的结果：

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
函数参数 {anchorName mapM}`f` 的返回类型决定将使用哪个 {anchorName mapM}`Monad` 实例。
换言之，{anchorName mapM}`mapM` 可用于产生日志的函数、可能失败的函数，或使用可变状态的函数。
由于 {anchorName mapM}`f` 的类型决定了可用的效果，API 设计者可以对它们进行严格控制。
:::

:::paragraph
如{ref "numbering-tree-nodes"}[本章引言]所述，{anchorTerm StateEx}`State σ α` 表示使用类型为 {anchorName StateEx}`σ` 的可变变量并返回类型为 {anchorName StateEx}`α` 的值的程序。
这些程序实际上是从初始状态到一个由值和最终状态组成的二元组的函数。
{anchorName StateMonad}`Monad` 类要求其参数期望一个单一类型参数；也就是说，它应当是一个 {anchorTerm StateEx}`Type → Type`。
这意味着 {anchorName StateMonad}`State` 的实例应提及状态类型 {anchorName StateMonad}`σ`，而该状态类型会成为该实例的一个参数：

```anchor StateMonad
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
```
这意味着，在使用 {anchorName StateMonad}`bind` 排序的对 {anchorName StateEx}`get` 和 {anchorName StateEx}`set` 的调用之间，状态的类型不能改变；对于有状态计算而言，这是一个合理的规则。
运算符 {anchorName increment}`increment` 将保存的状态增加给定的量，并返回旧值：

```anchor increment
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
```
:::

:::paragraph
将 {anchorName mapMincrementOut}`mapM` 与 {anchorName mapMincrementOut}`increment` 一起使用，会得到一个计算列表中各项之和的程序。
更具体地说，可变变量包含当前为止的和，而结果列表包含逐步累计的和。
换言之，{anchorTerm mapMincrement}`mapM increment` 的类型为 {anchorTerm mapMincrement}`List Int → State Int (List Int)`，展开 {anchorName StateMonad}`State` 的定义会得到 {anchorTerm mapMincrement2}`List Int → Int → (Int × List Int)`。
它以初始和作为参数，该参数应为 {anchorTerm mapMincrementOut}`0`：
```anchor mapMincrementOut
#eval mapM increment [1, 2, 3, 4, 5] 0
```
```anchorInfo mapMincrementOut
(15, [0, 1, 3, 6, 10])
```
:::

:::paragraph
一个 {ref "logging"}[日志效应] 可以使用 {anchorName MonadWriter}`WithLog` 表示。
就像 {anchorName StateEx}`State` 一样，它的 {anchorName MonadWriter}`Monad` 实例关于所记录数据的类型是多态的：

```anchor MonadWriter
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
```
:::

:::paragraph
{anchorName saveIfEven}`saveIfEven` 是一个记录偶数日志、但原样返回其参数的函数：

```anchor saveIfEven
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i
```
将此函数与 {anchorName mapMsaveIfEven}`mapM` 一起使用，会得到一个日志，其中包含与未改变的输入列表配对的偶数：
```anchor mapMsaveIfEven
#eval mapM saveIfEven [1, 2, 3, 4, 5]
```
```anchorInfo mapMsaveIfEven
{ log := [2, 4], val := [1, 2, 3, 4, 5] }
```
:::


# 恒等单子
%%%
tag := "Id-monad"
file := "The-Identity-Monad"
%%%

单子将带有效果的程序，例如失败、异常或日志记录，编码为由数据和函数构成的显式表示。
然而，有时 API 会为了灵活性而写成使用单子，但该 API 的客户端可能并不需要任何被编码的效果。
{deftech}_恒等单子_ 是一种没有效果的单子。
它允许纯代码与单子式 API 一起使用：

```anchor IdMonad
def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x
```
{anchorName IdMonad}`pure` 的类型应为 {anchorTerm IdMore}`α → Id α`，但 {anchorTerm IdMore}`Id α` 会约化为 {anchorTerm IdMore}`α`。
类似地，{anchorName IdMonad}`bind` 的类型应为 {anchorTerm IdMore}`α → (α → Id β) → Id β`。
因为这会约化为 {anchorTerm IdMore}`α → (α → β) → β`，所以可以将第二个参数应用于第一个参数以得到结果。

:::paragraph
使用恒等单子时，{anchorName mapMId}`mapM` 变得等价于 {anchorName Names (show:=map)}`Functor.map`
然而，若要以这种方式调用它，Lean 需要一个提示，说明预期的单子是 {anchorName mapMId}`Id`：
```anchor mapMId
def numbers := mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]
```
在类型没有提供任何关于应使用哪个单子的具体提示的上下文中使用 {anchorName mapMIdId}`mapM`，会产生一条 “instance problem is stuck” 消息：
```anchor mapMIdId
def numbers := mapM (do return · + 1) [1, 2, 3, 4, 5]
```
```anchorError mapMIdId
typeclass instance problem is stuck
  Pure ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
:::

# Monad 约定
%%%
tag := "monad-contract"
file := "The-Monad-Contract"
%%%

正如 {anchorName MonadContract}`BEq` 和 {anchorName MonadContract}`Hashable` 的每一对实例都应保证任意两个相等的值具有相同的散列值一样，{anchorName MonadContract}`Monad` 的每个实例也应遵守一个约定。
首先，{anchorName MonadContract}`pure` 应是 {anchorName MonadContract}`bind` 的左恒等元。
也就是说，{anchorTerm MonadContract}`bind (pure v) f` 应与 {anchorTerm MonadContract}`f v` 相同。
其次，{anchorName MonadContract}`pure` 应是 {anchorName MonadContract}`bind` 的右恒等元，因此 {anchorTerm MonadContract}`bind v pure` 与 {anchorName MonadContract2}`v` 相同。
最后，{anchorName MonadContract}`bind` 应满足结合律，因此 {anchorTerm MonadContract}`bind (bind v f) g` 与 {anchorTerm MonadContract}`bind v (fun x => bind (f x) g)` 相同。

这一约定更一般地规定了带有效果的程序所应满足的性质。
由于 {anchorName MonadContract}`pure` 没有效果，将它的效果与 {anchorName MonadContract}`bind` 排序不应改变结果。
{anchorName MonadContract}`bind` 的结合律基本上说明，只要保持事情发生的顺序，排序本身的簿记方式并不重要。

# 练习
%%%
tag := "monad-class-exercises"
file := "Exercises"
%%%

## 在树上进行映射
%%%
tag := none
file := "Mapping-on-a-Tree"
%%%

:::paragraph
定义一个函数 {anchorName ex1}`BinTree.mapM`。
类比于列表上的 {anchorName mapM}`mapM`，该函数应以前序遍历的方式，将一个单子函数应用到树中的每个数据项。
类型签名应为：
```anchorTerm ex1
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```
:::

## Option 单子的约定
%%%
tag := none
file := "The-Option-Monad-Contract"
%%%

:::paragraph
首先，写出一个令人信服的论证，说明 {anchorName badOptionMonad}`Option` 的 {anchorName badOptionMonad}`Monad` 实例满足单子约定。
然后，考虑以下实例：
```anchor badOptionMonad
instance : Monad Option where
  pure x := some x
  bind opt next := none
```
这两个方法都具有正确的类型。
为什么这个实例违反了单子契约？
:::
