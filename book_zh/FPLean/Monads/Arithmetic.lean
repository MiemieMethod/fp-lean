import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "示例：单子中的算术" =>
%%%
tag := "monads-arithmetic-example"
file := "Example___-Arithmetic-in-Monads"
%%%

单子是一种将带有副作用的程序编码到一种本身没有这些副作用的语言中的方式。
很容易把这理解为一种承认：纯函数式程序缺少某种重要的东西，以至于程序员为了编写普通程序也不得不绕过重重障碍。
然而，尽管使用 {moduleName}`Monad` API 确实会给程序带来语法上的代价，它也带来了两个重要好处：
 1. 程序必须在其类型中如实说明它们使用了哪些效应。只需快速查看类型签名，就能描述程序能够做的_一切_，而不仅仅是它接受什么以及返回什么。
 2. 并非每种语言都提供相同的效应。例如，只有某些语言具有异常。另一些语言具有独特而特殊的效应，例如 [Icon 对多个值的搜索](https://www2.cs.arizona.edu/icon/) 以及 Scheme 或 Ruby 的续延。由于单子能够编码_任意_效应，程序员可以选择最适合给定应用程序的效应，而不必受限于语言开发者所提供的效应。

一个可以在多种单子中有意义的程序示例，是算术表达式的求值器。

# 算术表达式
%%%
tag := "monads-arithmetic-example-expr"
file := "Arithmetic-Expressions"
%%%

:::paragraph
一个算术表达式要么是字面量整数，要么是将一个原始二元运算符应用于两个表达式。运算符包括加法、减法、乘法和除法：

```anchor ExprArith
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div
```
:::

:::paragraph
表达式 {lit}`2 + 3` 表示如下：

```anchor twoPlusThree
open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)
```
而 {lit}`14 / (45 - 5 * 9)` 表示为：
```anchor exampleArithExpr
open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))
```
:::

# 求值表达式
%%%
tag := "monads-arithmetic-example-eval"
file := "Evaluating-Expressions"
%%%

:::paragraph
由于表达式包含除法，而除以零是未定义的，因此求值可能失败。
表示失败的一种方式是使用 {anchorName evaluateOptionCommingled}`Option`：

```anchor evaluateOptionCommingled
def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)
```
:::

:::paragraph
此定义使用 {anchorTerm MonadOptionExcept}`Monad Option` 实例来传播对二元运算符两个分支求值时产生的失败。
然而，该函数混合了两个关注点：对子表达式求值，以及将二元运算符应用于所得结果。
通过将其拆分为两个函数，可以改进它：

```anchor evaluateOptionSplit
def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

:::paragraph
运行 {anchorTerm fourteenDivOption}`#eval evaluateOption fourteenDivided` 会产生 {anchorInfo fourteenDivOption}`none`，正如预期的那样，但这并不是一条很有用的错误消息。
由于代码是使用 {lit}`>>=` 编写的，而不是显式处理 {anchorName MonadOptionExcept}`none` 构造子，因此只需很小的修改，就可以使其在失败时提供错误消息：

```anchor evaluateExcept
def applyPrim : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrim p v1 v2
```
唯一的区别在于，类型签名提到的是 {anchorTerm evaluateExcept}`Except String` 而不是 {anchorName Names}`Option`，并且失败情形使用 {anchorName evaluateExcept}`Except.error` 而不是 {anchorName evaluateM}`none`。
通过使求值器在其单子上具有多态性，并将 {anchorName evaluateM}`applyPrim` 作为参数传给它，单个求值器就能够支持这两种错误报告形式：

```anchor evaluateM
def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      none
    else pure (x / y)

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateM [Monad m]
    (applyPrim : Arith → Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

将其与 {anchorName evaluateMOption}`applyPrimOption` 一起使用的方式与第一个求值器完全相同：
```anchor evaluateMOption
#eval evaluateM applyPrimOption fourteenDivided
```
```anchorInfo evaluateMOption
none
```
类似地，将它与 {anchorName evaluateMExcept}`applyPrimExcept` 一起使用时，其行为与带错误消息的版本完全相同：
```anchor evaluateMExcept
#eval evaluateM applyPrimExcept fourteenDivided
```
```anchorInfo evaluateMExcept
Except.error "Tried to divide 14 by zero"
```

:::paragraph
代码仍然可以改进。
函数 {anchorName evaluateMOption}`applyPrimOption` 和 {anchorName evaluateMExcept}`applyPrimExcept` 只在对除法的处理上有所不同，而这一点可以提取为求值器的另一个参数：

```anchor evaluateMRefactored
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applyDiv : Int → Int → m Int) :
    Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m]
    (applyDiv : Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2
```

在这段重构后的代码中，两个代码路径只是在处理失败的方式上有所不同这一事实，已经变得完全清楚。
:::

# 进一步的效应
%%%
tag := "monads-arithmetic-example-effects"
file := "Further-Effects"
%%%

在使用求值器时，失败和异常并不是唯一可能令人关注的效应。
虽然除法的唯一副作用是失败，但向表达式加入其他原始算子使得表达其他效应成为可能。

第一步是进行一次额外的重构，从原语的数据类型中提取出除法：

```anchor PrimCanFail
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
```
名称 {anchorName PrimCanFail}`CanFail` 表明，除法引入的效应是潜在失败。

第二步是将除法处理器参数的作用范围扩展到 {anchorName evaluateMMorePoly}`evaluateM`，使其能够处理任何特殊运算符：

```anchor evaluateMMorePoly
def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2
```

## 无效果
%%%
tag := "monads-arithmetic-example-no-effects"
file := "No-Effects"
%%%

类型 {anchorName applyEmpty}`Empty` 没有构造子，因此也没有值，类似于 Scala 或 Kotlin 中的 {Kotlin}`Nothing` 类型。
在 Scala 和 Kotlin 中，{Kotlin}`Nothing` 可以表示永远不返回结果的计算，例如使程序崩溃、抛出异常，或总是陷入无限循环的函数。
类型为 {Kotlin}`Nothing` 的函数或方法参数表示死代码，因为永远不会有合适的参数值。
Lean 不支持无限循环和异常，但 {anchorName applyEmpty}`Empty` 仍然有用，它向类型系统表明某个函数不可能被调用。
当 {anchorName nomatch}`E` 是一个其类型没有构造子的表达式时，使用语法 {anchorTerm nomatch}`nomatch E` 会向 Lean 表明当前表达式不必返回结果，因为它本不可能被调用。

使用 {anchorName applyEmpty}`Empty` 作为 {anchorName PrimCanFail}`Prim` 的参数表明，除了 {anchorName evaluateMMorePoly}`Prim.plus`、{anchorName evaluateMMorePoly}`Prim.minus` 和 {anchorName evaluateMMorePoly}`Prim.times` 之外没有额外情形，因为不可能构造出类型为 {anchorName nomatch}`Empty` 的值来放入 {anchorName evaluateMMorePoly}`Prim.other` 构造子中。
由于一个把类型为 {anchorName nomatch}`Empty` 的算子应用到两个整数上的函数永远不可能被调用，它不需要返回结果。
因此，它可以用于_任意_单子中：

```anchor applyEmpty
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
```
这可以与 {anchorName evalId}`Id`（恒等单子）一起使用，以求值完全没有任何效应的表达式：
```anchor evalId
open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
```
```anchorInfo evalId
-9
```

## 非确定性搜索
%%%
tag := "nondeterministic-search"
file := "Nondeterministic-Search"
%%%

在遇到除以零时，与其只是失败，回溯并尝试不同的输入也是合理的。
给定合适的单子，同一个 {anchorName evalId}`evaluateM` 就可以对不导致失败的一_组_答案执行非确定性搜索。
除法之外，这还需要某种指定结果选择的手段。
做到这一点的一种方式，是向表达式语言中添加一个函数 {lit}`choose`，它指示求值器在搜索不会失败的结果时，选择它的任一参数。

求值器的结果现在是一个值的多重集，而不是单个值。
求值为多重集的规则如下：
 * 常量 $`n` 求值为单元素集合 $`\{n\}`。
 * 除除法以外的算术算子会在算子笛卡尔积中的每一对上被调用，因此 $`X + Y` 求值为 $`\{ x + y \mid x ∈ X, y ∈ Y \}`。
 * 除法 $`X / Y` 求值为 $`\{ x / y \mid x ∈ X, y ∈ Y, y ≠ 0\}`。换言之，$`Y` 中所有 $`0` 值都会被舍去。
 * 选择 $`\mathrm{choose}(x, y)` 求值为 $`\{ x, y \}`。

例如，$`1 + \mathrm{choose}(2, 5)` 求值为 $`\{ 3, 6 \}`，$`1 + 2 / 0` 求值为 $`\{\}`，而 $`90 / (\mathrm{choose}(-5, 5) + 5)` 求值为 $`\{ 9 \}`。
使用多重集而不是真正的集合，可以避免检查元素唯一性，从而简化代码。

:::paragraph
表示这种非确定性效果的单子，必须能够表示没有答案的情形，以及至少有一个答案并伴随任意剩余答案的情形：

```anchor Many (module := Examples.Monads.Many)
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
```
这个数据类型看起来非常像 {anchorName fromList (module:=Examples.Monads.Many)}`List`。
区别在于，{anchorName etc}`List.cons` 存储列表的其余部分，而 {anchorName Many (module:=Examples.Monads.Many)}`more` 存储一个函数，该函数应当按需计算剩余的值。
这意味着 {anchorName Many (module:=Examples.Monads.Many)}`Many` 的消费者可以在已经找到若干结果时停止搜索。
:::

:::paragraph
单个结果由一个不返回更多结果的 {anchorName Many (module:=Examples.Monads.Many)}`more` 构造子表示：

```anchor one (module := Examples.Monads.Many)
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
```
:::

:::paragraph
两个结果多重集的并集可以通过检查第一个多重集是否为空来计算。
如果为空，则第二个多重集就是并集。
如果不为空，则并集由第一个多重集的第一个元素，后接第一个多重集其余部分与第二个多重集的并集构成：

```anchor union (module := Examples.Monads.Many)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
```
:::

:::paragraph
用一个值列表开始搜索过程可能很方便。
{anchorName fromList (module:=Examples.Monads.Many)}`Many.fromList` 将列表转换为结果的多重集：

```anchor fromList (module := Examples.Monads.Many)
def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
```

类似地，一旦指定了搜索，提取若干个值或所有值都会很方便：

```anchor take (module := Examples.Monads.Many)
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll
```
:::

一个 {anchorTerm MonadMany (module:=Examples.Monads.Many)}`Monad Many` 实例需要一个 {anchorName MonadContract}`bind` 运算符。
在非确定性搜索中，将两个操作顺序组合起来，就是取第一步中的所有可能性，并在每一种可能性上运行程序的其余部分，然后取结果的并集。
换言之，如果第一步返回三个可能答案，那么第二步就需要对这三个答案全部尝试。
由于第二步可以为每个输入返回任意数量的答案，取它们的并集就表示整个搜索空间。

```anchor bind (module := Examples.Monads.Many)
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
```

{anchorName MonadMany (module:=Examples.Monads.Many)}`Many.one` 和 {anchorName MonadMany (module:=Examples.Monads.Many)}`Many.bind` 遵守单子约定。
要检查 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.one v) f` 与 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v` 相同，首先尽可能对表达式求值：
```anchorEvalSteps bindLeft (module := Examples.Monads.Many)
Many.bind (Many.one v) f
===>
Many.bind (Many.more v (fun () => Many.none)) f
===>
(f v).union (Many.bind Many.none f)
===>
(f v).union Many.none
```
空多重集是 {anchorName union (module:=Examples.Monads.Many)}`union` 的右单位元，因此答案等价于 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`。
要检查 {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` 与 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 相同，考虑 {anchorName bindOne (module:=Examples.Monads.Many)}`Many.bind` 会对 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 的每个元素应用 {anchorName one (module:=Examples.Monads.Many)}`Many.one`，并取其并集。
换言之，如果 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 具有形式 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`，那么 {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` 就是 {anchorTerm vSets (module:=Examples.Monads.Many)}`{v₁} ∪ {v₂} ∪ {v₃} ∪ … ∪ {vₙ}`，也就是 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`。

最后，为了检查 {anchorName bind (module:=Examples.Monads.Many)}`Many.bind` 是结合的，需要检查 {anchorTerm bindBindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.bind v f) g` 与 {anchorTerm bindBindRight (module:=Examples.Monads.Many)}`Many.bind v (fun x => Many.bind (f x) g)` 相同。
如果 {anchorName bindBindRight (module:=Examples.Monads.Many)}`v` 具有形式 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`，则：
```anchorEvalSteps bindUnion (module := Examples.Monads.Many)
Many.bind v f
===>
f v₁ ∪ f v₂ ∪ f v₃ ∪ … ∪ f vₙ
```
这意味着
```anchorEvalSteps bindBindLeft (module := Examples.Monads.Many)
Many.bind (Many.bind v f) g
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
类似地，
```anchorEvalSteps bindBindRight (module := Examples.Monads.Many)
Many.bind v (fun x => Many.bind (f x) g)
===>
(fun x => Many.bind (f x) g) v₁ ∪
(fun x => Many.bind (f x) g) v₂ ∪
(fun x => Many.bind (f x) g) v₃ ∪
… ∪
(fun x => Many.bind (f x) g) vₙ
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
因此，两边相等，所以 {anchorName bindAssoc (module:=Examples.Monads.Many)}`Many.bind` 是结合的。

所得的单子实例为：

```anchor MonadMany (module := Examples.Monads.Many)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
```
使用这个单子进行的一个示例搜索会找出列表中所有和为 15 的数字组合：

```anchor addsTo (module := Examples.Monads.Many)
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))
```
搜索过程在列表上递归进行。
当目标为 {anchorTerm addsTo (module:=Examples.Monads.Many)}`0` 时，空列表是一次成功的搜索；否则，它失败。
当列表非空时，有两种可能：要么列表的头部大于目标，在这种情况下它不可能参与任何成功的搜索；要么不是这样，在这种情况下它可以参与。
如果列表的头部_不是_候选项，则搜索继续处理列表的尾部。
如果头部是候选项，则有两种可能需要与 {anchorName union (module:=Examples.Monads.Many)}`Many.union` 组合：找到的解要么包含该头部，要么不包含。
不包含该头部的解通过对尾部进行递归调用得到；而包含该头部的解则通过从目标中减去该头部，然后将该头部附加到递归调用所得的解上得到。

辅助函数 {anchorName printList (module:=Examples.Monads.Many)}`printList` 确保每行显示一个结果：

```anchor printList (module := Examples.Monads.Many)
def printList [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    printList xs
```
```anchor addsToFifteen (module := Examples.Monads.Many)
#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
```
```anchorInfo addsToFifteen (module := Examples.Monads.Many)
[7, 8]
[6, 9]
[5, 10]
[4, 5, 6]
[3, 5, 7]
[3, 4, 8]
[2, 6, 7]
[2, 5, 8]
[2, 4, 9]
[2, 3, 10]
[2, 3, 4, 6]
[1, 6, 8]
[1, 5, 9]
[1, 4, 10]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
[1, 2, 3, 4, 5]
```

:::paragraph
回到产生结果多重集的算术求值器，{anchorName NeedsSearch}`choose` 运算符可以用来非确定性地选择一个值，而除以零会使先前的选择无效。

```anchor NeedsSearch
inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)
```
:::

:::paragraph
使用这些运算符，可以对前面的示例求值：

```anchor opening
open Expr Prim NeedsSearch
```
```anchor searchA
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll
```
```anchorInfo searchA
[3, 6]
```
```anchor searchB
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll
```
```anchorInfo searchB
[]
```
```anchor searchC
#eval
  (evaluateM applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll
```
```anchorInfo searchC
[9]
```
:::

## 自定义环境
%%%
tag := "custom-environments"
file := "Custom-Environments"
%%%

通过允许字符串作为算子使用，并提供从字符串到实现这些算子的函数的映射，可以使求值器能够由用户扩展。
例如，用户可以用一个取余算子，或一个返回其两个参数最大值的算子来扩展求值器。
从函数名到函数实现的映射称为一个_环境_。

环境需要在每次递归调用中传递。
起初，可能看起来 {anchorName evaluateM}`evaluateM` 需要一个额外参数来保存环境，并且该参数应当传递给每次递归调用。
然而，像这样传递参数是单子的另一种形式，因此适当的 {anchorName evaluateM}`Monad` 实例允许求值器保持不变地使用。

将函数用作单子通常称为 _reader_ 单子。
在 reader 单子中求值表达式时，使用如下规则：
 * 常量 $`n` 求值为常量函数 $`λ e . n`，
 * 算术运算符求值为会传递其参数的函数，因此 $`f + g` 求值为 $`λ e . f(e) + g(e)`，并且
 * 自定义运算符求值为将该自定义运算符应用于参数所得的结果，因此 $`f \ \mathrm{OP}\ g` 求值为
$$`
     λ e .
     \begin{cases}
     h(f(e), g(e)) & \mathrm{if}\ e\ \mathrm{contains}\ (\mathrm{OP}, h) \\
     0 & \mathrm{otherwise}
     \end{cases}
   `
   其中 $`0` 作为应用未知算子时的后备值。

:::paragraph
要在 Lean 中定义 reader 单子，第一步是定义 {anchorName Reader}`Reader` 类型以及允许用户取得环境的效应：

```anchor Reader
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env
```
按照约定，希腊字母 {anchorName Reader}`ρ`，读作“rho”，用于表示环境。
:::

:::paragraph
算术表达式中的常量会求值为常值函数，这一事实表明，对于 {anchorName Reader}`Reader`，{anchorName IdMonad}`pure` 的适当定义是一个常值函数：

```anchor ReaderPure
def Reader.pure (x : α) : Reader ρ α := fun _ => x
```
:::


另一方面，{anchorName MonadContract}`bind` 要稍微棘手一些。
它的类型是 {anchorTerm readerBindType}`Reader ρ α → (α → Reader ρ β) → Reader ρ β`。
展开 {anchorName Reader}`Reader` 的定义可以使这个类型更容易理解，展开后得到 {anchorTerm readerBindTypeEval}`(ρ → α) → (α → ρ → β) → (ρ → β)`。
它应当以一个接受环境的函数作为第一个参数，而第二个参数应当将这个接受环境的函数的结果转换为另一个接受环境的函数。
将二者组合得到的结果本身也是一个函数，正在等待一个环境。

可以交互式地使用 Lean 来获得编写此函数的帮助。
第一步是写下参数和返回类型，并尽可能显式，以便获得尽可能多的帮助，同时用一个下划线作为定义的主体：
```anchor readerbind0
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
```
Lean 会提供一条消息，描述当前作用域中有哪些变量可用，以及结果所期望的类型。
{lit}`⊢` 符号由于形似地铁入口而称为 {deftech}_turnstile_，它将局部变量与目标类型分隔开来；在这条消息中，目标类型是 {anchorTerm readerbind0}`ρ → β`：
```anchorError readerbind0
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
```

由于返回类型是一个函数，一个好的第一步是在下划线外包上一层 {kw}`fun`：
```anchor readerbind1
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => _
```
所得消息现在将该函数的实参显示为局部变量：
```anchorError readerbind1
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β
```

上下文中唯一能够产生 {anchorName readerbind2a}`β` 的东西是 {anchorName readerbind2a}`next`，而它需要两个参数才能做到这一点。
每个参数本身都可以是一个下划线：
```anchor readerbind2a
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
```
这两个下划线分别关联着以下消息：
```anchorError readerbind2a
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α
```
```anchorError readerbind2b
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```

:::paragraph
处理第一个下划线时，上下文中只有一个东西能够产生一个 {anchorName readerbind3}`α`，即 {anchorName readerbind3}`result`：
```anchor readerbind3
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result _) _
```
现在，两个下划线都有相同的错误消息：
```anchorError readerbind3
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```
:::

:::paragraph
令人高兴的是，两个下划线都可以替换为 {anchorName readerbind4}`env`，得到：

```anchor readerbind4
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
```
:::

最终版本可以通过撤销 {anchorName Readerbind}`Reader` 的展开并清理显式细节而得到：

```anchor Readerbind
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
```

并非总是能够仅仅通过“跟随类型”来写出正确的函数，而且这样做还带有不理解所得程序的风险。
然而，理解一个已经写出的程序，也可能比理解一个尚未写出的程序更容易；而填写下划线的过程也可能带来洞见。
在这个例子中，{anchorName Readerbind}`Reader.bind` 对于 {anchorName IdMonad}`Id` 的作用正如 {anchorName IdMonad}`bind` 一样，只是它接受一个额外的参数，然后将该参数向下传递给它的各个参数；这种直觉有助于理解它的工作方式。

{anchorName ReaderPure}`Reader.pure`（它生成常量函数）和 {anchorName Readerbind}`Reader.bind` 满足单子契约。
要检查 {anchorTerm ReaderMonad1}`Reader.bind (Reader.pure v) f` 与 {anchorTerm ReaderMonad1}`f v` 相同，只需不断替换定义，直到最后一步：
```anchorEvalSteps ReaderMonad1
Reader.bind (Reader.pure v) f
===>
fun env => f ((Reader.pure v) env) env
===>
fun env => f ((fun _ => v) env) env
===>
fun env => f v env
===>
f v
```
对于每个函数 {anchorName eta}`f`，{anchorTerm eta}`fun x => f x` 与 {anchorName eta}`f` 相同，因此约定的第一部分得到满足。
要检查 {anchorTerm ReaderMonad2}`Reader.bind r Reader.pure` 与 {anchorName ReaderMonad2}`r` 相同，可以使用类似的技巧：
```anchorEvalSteps ReaderMonad2
Reader.bind r Reader.pure
===>
fun env => Reader.pure (r env) env
===>
fun env => (fun _ => (r env)) env
===>
fun env => r env
```
因为 reader 动作 {anchorName ReaderMonad2}`r` 本身就是函数，这与 {anchorName ReaderMonad2}`r` 相同。
要检查结合律，可以对 {anchorEvalStep ReaderMonad3a 0}`Reader.bind (Reader.bind r f) g` 和 {anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)` 都做同样的事情：
```anchorEvalSteps ReaderMonad3a
Reader.bind (Reader.bind r f) g
===>
fun env => g ((Reader.bind r f) env) env
===>
fun env => g ((fun env' => f (r env') env') env) env
===>
fun env => g (f (r env) env) env
```

{anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)` 化简为相同的表达式：
```anchorEvalSteps ReaderMonad3b
Reader.bind r (fun x => Reader.bind (f x) g)
===>
Reader.bind r (fun x => fun env => g (f x env) env)
===>
fun env => (fun x => fun env' => g (f x env') env') (r env) env
===>
fun env => (fun env' => g (f (r env) env') env') env
===>
fun env => g (f (r env) env) env
```

因此，一个 {anchorTerm MonadReaderInst}`Monad (Reader ρ)` 实例是有根据的：

```anchor MonadReaderInst
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
```

将传递给表达式求值器的自定义环境可以表示为由对组成的列表：

```anchor Env
abbrev Env : Type := List (String × (Int → Int → Int))
```
例如，{anchorName exampleEnv}`exampleEnv` 包含最大值函数和取模函数：

```anchor exampleEnv
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
```

Lean 已经有一个函数 {anchorName etc}`List.lookup`，可在由成对元素组成的列表中查找与某个键关联的值，因此 {anchorName applyPrimReader}`applyPrimReader` 只需检查自定义函数是否存在于环境中。如果该函数未知，它返回 {anchorTerm applyPrimReader}`0`：

```anchor applyPrimReader
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
```

将 {anchorName readerEval}`evaluateM` 与 {anchorName readerEval}`applyPrimReader` 和一个表达式一起使用，会得到一个期望环境的函数。
幸运的是，{anchorName readerEval}`exampleEnv` 是可用的：
```anchor readerEval
open Expr Prim in
#eval
  evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
```
```anchorInfo readerEval
9
```

与 {anchorName Many (module:=Examples.Monads.Many)}`Many` 类似，{anchorName Reader}`Reader` 是一种在大多数语言中难以编码的效应示例，但类型类和单子使它与任何其他效应一样方便。
Common Lisp、Clojure 和 Emacs Lisp 中的动态变量或特殊变量可以像 {anchorName Reader}`Reader` 一样使用。
类似地，Scheme 和 Racket 的参数对象是一种与 {anchorName Reader}`Reader` 精确对应的效应。
Kotlin 中上下文对象的惯用法可以解决类似的问题，但它们本质上是一种自动传递函数参数的手段，因此这种惯用法更像是读者单子的编码，而不是语言中的一种效应。

## 练习
%%%
tag := "monads-arithmetic-example-exercises"
file := "Exercises"
%%%

### 检查契约
%%%
tag := none
file := "Checking-Contracts"
%%%

检查 {anchorTerm StateMonad}`State σ` 和 {anchorTerm MonadOptionExcept}`Except ε` 的单子契约。


### 带失败的读取器
%%%
tag := none
file := "Readers-with-Failure"
%%%
调整 reader 单子示例，使其在自定义算子未定义时也能指示失败，而不只是返回零。
换言之，给定这些定义：

```anchor ReaderFail
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
```
执行以下操作：
 1. 编写合适的 {lit}`pure` 和 {lit}`bind` 函数
 2. 检查这些函数满足 {anchorName evaluateM}`Monad` 约定
 3. 为 {anchorName ReaderFail}`ReaderOption` 和 {anchorName ReaderFail}`ReaderExcept` 编写 {anchorName evaluateM}`Monad` 实例
 4. 定义合适的 {anchorName evaluateM}`applyPrim` 运算符，并在一些示例表达式上用 {anchorName evaluateM}`evaluateM` 测试它们

### 带追踪的求值器
%%%
tag := "monads-arithmetic-example-exercise-trace"
file := "A-Tracing-Evaluator"
%%%

{anchorName MonadWriter}`WithLog` 类型可以与求值器一起使用，以添加对某些操作的可选跟踪。
特别地，类型 {anchorName ToTrace}`ToTrace` 可以作为跟踪给定运算符的信号：

```anchor ToTrace
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α
```
对于带跟踪的求值器，表达式应具有类型 {anchorTerm ToTraceExpr}`Expr (Prim (ToTrace (Prim Empty)))`。
这表示表达式中的运算符由加法、减法和乘法组成，并且为每一种运算符都增添了带跟踪的版本。最内层的参数是 {anchorName ToTraceExpr}`Empty`，用以表明在 {anchorName ToTrace}`trace` 内部没有更多特殊运算符，只有这三种基本运算符。

完成以下事项：
 1. 实现一个 {anchorTerm MonadWriter}`Monad (WithLog logged)` 实例
 2. 编写一个 {anchorName applyTracedType}`applyTraced` 函数，将带跟踪的运算符应用于其参数，并记录该运算符和这些参数，其类型为 {anchorTerm applyTracedType}`ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int`

如果练习已正确完成，那么
```anchor evalTraced
open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
```
应得到
```anchorInfo evalTraced
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
```

提示：类型为 {anchorTerm ToTraceExpr}`Prim Empty` 的值会出现在所得日志中。为了将它们显示为 {kw}`#eval` 的结果，需要以下实例：

```anchor ReprInstances
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
```
