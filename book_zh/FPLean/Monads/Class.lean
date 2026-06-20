import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "Monad类型类" =>
%%%
tag := "monad-type-class"
%%%

:::paragraph
无需为每个单子都实现 {lit}`ok` 或 {lit}`andThen` 这样的运算符，Lean标准库包含一个类型类，
允许它们被重载，以便相同的运算符可用于 *任何* 单子。
单子有两个操作，分别相当于 {lit}`ok` 和 {lit}`andThen`：

```anchor FakeMonad
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
```
这个定义略微简化了。
Lean 标准库中的实际定义更复杂一些，稍后会介绍。
:::

:::paragraph
{anchorName MonadOptionExcept}`Option` 和 {anchorTerm MonadOptionExcept}`Except ε` 的 {anchorName MonadOptionExcept}`Monad` 实例，可以通过调整它们各自的 {lit}`andThen` 操作的定义来创建：

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
例如 {lit}`firstThirdFifthSeventh` 原本对 {anchorTerm Names}`Option α` 和 {anchorTerm Names}`Except String α` 类型分别定义。
现在，它可以被定义为对 *任何* 单子都有效的多态函数。
但是，它需要接受一个参数作为查找函数，因为不同的单子可能以不同的方式找不到结果。
{anchorName FakeMonad}`bind` 的中缀运算符是 {lit}`>>=`, 它扮演与示例中 {lit}`~~>` 相同的角色。

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
给定作为示例的slowMammals和fastBirds列表，该 {anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` 实现可与 {moduleName}`Option` 一起使用：

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
在将 {anchorName getOrExcept}`Except` 的查找函数 {lit}`get` 重命名为更具体的形式后，
完全相同的 {anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` 实现也可以与 {anchorName getOrExcept}`Except` 一起使用：

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
{anchorName firstThirdFifthSeventhMonad}`m` 必须有 {anchorName firstThirdFifthSeventhMonad}`Monad` 实例，这一事实这意味着可以使用 {lit}`>>=` 和 {anchorName firstThirdFifthSeventhMonad}`pure` 运算符。
:::

# 通用的单子运算符
%%%
tag := "monad-class-polymorphism"
%%%

:::paragraph
由于许多不同类型都是单子，因此对 *任何* 单子多态的函数非常强大。
例如，函数 {anchorName mapM}`mapM` 是 {anchorName Names (show:=map)}`Functor.map` 的另一个版本，它使用 {anchorName mapM}`Monad` 将函数调用的结果按顺序连接起来：

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
函数参数 {anchorName mapM}`f` 的返回类型决定了将使用哪个 {anchorName mapM}`Monad` 实例。
换句话说，{anchorName mapM}`mapM`可用于生成日志的函数、可能失败的函数、或使用可变状态的函数。
由于 {anchorName mapM}`f` 的类型直接决定了可用的效应(Effects)，因此API设计人员可以对其进行严格控制。
*译者注：效应(Effects)是函数式编程中与 Monad 密切相关的主题，*
*实际上对效应的控制比此处原文所述更复杂一些，但超出了本文的内容。*
*另外副作用(Side Effects)也是一种效应。*
:::

:::paragraph
如[本章简介](monads.md#对树节点编号)所介绍的，{anchorTerm StateEx}`State σ α`表示使用类型为 {anchorName StateEx}`σ` 的可变变量，并返回类型为 {anchorName StateEx}`α` 的值的程序。
这些程序实际上是从起始状态到值和最终状态构成的对(pair)的函数。
{anchorName StateMonad}`Monad`类型类要求：类型参数期望另一个类型参数，即它应该是{anchorTerm StateEx}`Type → Type`。
这意味着 {anchorName StateMonad}`State` 的实例应提及状态类型{anchorName StateMonad}`σ`，使它成为实例的参数：

```anchor StateMonad
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
```
这意味着在使用 {anchorName StateMonad}`bind` 对 {anchorName StateEx}`get` 和 {anchorName StateEx}`set` 排序时，状态的类型不能更改，这是具有状态的计算的合理规则。运算符 {anchorName increment}`increment` 将保存的状态加上一定量，并返回原值：

```anchor increment
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
```
:::

:::paragraph
将 {anchorName mapMincrementOut}`mapM` 和 {anchorName mapMincrementOut}`increment` 一起使用会得到一个：计算列表元素加和的程序。
更具体地说，可变变量包含到目前为止的和，而作为结果的列表包含各个步骤前状态变量的值。
换句话说，{anchorTerm mapMincrement}`mapM increment`的类型为{anchorTerm mapMincrement}`List Int → State Int (List Int)`，展开 {anchorName StateMonad}`State` 的定义得到{anchorTerm mapMincrement2}`List Int → Int → (Int× List Int)`。
它将初始值作为参数，应为{anchorTerm mapMincrementOut}`0`：
```anchor mapMincrementOut
#eval mapM increment [1, 2, 3, 4, 5] 0
```
```anchorInfo mapMincrementOut
(15, [0, 1, 3, 6, 10])
```
:::

:::paragraph
可以使用 {anchorName MonadWriter}`WithLog` 表示[日志记录效应](monads.md#日志记录)。
就和 {anchorName StateEx}`State` 一样，它的 {anchorName MonadWriter}`Monad` 实例对于被记录数据的类型也是多态的：

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
{anchorName saveIfEven}`saveIfEven`函数记录偶数，但将参数原封不动返回：

```anchor saveIfEven
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i
```
将 {anchorName mapMsaveIfEven}`mapM` 和该函数一起使用，会生成一个记录偶数的日志、和未更改的输入列表：
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
%%%

单子将具有效应(Effects)的程序（例如失败、异常或日志记录）编码为数据和函数的显式表示。
有时API会使用单子来提高灵活性，但API的使用方可能不需要任何效应。
*恒等单子* (Identity Monad)是一个没有任何效应的单子，允许将纯(pure)代码与monadic API一起使用：

```anchor IdMonad
def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x
```
{anchorName IdMonad}`pure`的类型应为 {anchorTerm IdMore}`α → Id α`，但{anchorTerm IdMore}`Id α` *归约* 为 {anchorTerm IdMore}`α`。类似地，{anchorName IdMonad}`bind` 的类型应为{anchorTerm IdMore}`α → (α → Id β) → Id β`。
由于这 *归约* 为 {anchorTerm IdMore}`α → (α → β) → β`，因此可以将第二个参数应用于第一个参数得到结果。
> 译者注：此处 *归约* 一词原文为reduces to，实际含义为beta-reduction，请见类型论相关资料。

:::paragraph
使用恒等单子时，{anchorName mapMId}`mapM`等同于{anchorName Names (show:=map)}`Functor.map`。但是要以这种方式调用它，Lean需要额外的提示来表明目标单子是 {anchorName mapMId}`Id`：
```anchor mapMId
def numbers := mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]
```
在类型没有提供任何具体线索来说明应使用哪个单子的上下文中使用 {anchorName mapMIdId}`mapM`，会得到 “instance problem is stuck” 消息：
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

# 单子约定
%%%
tag := "monad-contract"
%%%

正如 {anchorName MonadContract}`BEq` 和 {anchorName MonadContract}`Hashable` 的每一对实例都应该确保任何两个相等的值具有相同的哈希值，有一些是固有的约定是每个 {anchorName MonadContract}`Monad` 的实例都应遵守的。
首先，{anchorName MonadContract}`pure`应为 {anchorName MonadContract}`bind` 的左单位元，即 {anchorTerm MonadContract}`bind (pure v) f` 应与 {anchorTerm MonadContract}`f v` 等价。
其次，{anchorName MonadContract}`pure`应为 {anchorName MonadContract}`bind` 的右单位元，即 {anchorTerm MonadContract}`bind v pure` 应与 {anchorName MonadContract2}`v` 等价。
最后，{anchorName MonadContract}`bind`应满足结合律，即 {anchorTerm MonadContract}`bind (bind v f) g` 应与 {anchorTerm MonadContract}`bind v (fun x => bind (f x) g)` 等价。

这些约定保证了具有效应的程序的预期属性。
由于 {anchorName MonadContract}`pure` 不导致效应，因此用 {anchorName MonadContract}`bind` 将其与其他效应接连执行不应改变结果。
{anchorName MonadContract}`bind`满足的结合律则意味着先计算哪一部分无关紧要，只要保证效应的顺序不变即可。

# 练习
%%%
tag := "monad-class-exercises"
%%%

## 映射一棵树
%%%
tag := none
%%%

:::paragraph
定义函数{anchorName ex1}`BinTree.mapM`。
通过类比列表的{anchorName mapM}`mapM`，此函数应将单子函数应用于树中的每个节点，作为前序遍历。
类型签名应为：
```anchorTerm ex1
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```
:::

## Option单子的约定
%%%
tag := none
%%%

:::paragraph
首先充分论证 {anchorName badOptionMonad}`Option` 的 {anchorName badOptionMonad}`Monad` 实例满足单子约定。
然后，考虑以下实例：
```anchor badOptionMonad
instance : Monad Option where
  pure x := some x
  bind opt next := none
```
这两个方法都有正确的类型。
但这个实例却违反了单子约定，为什么？
:::
