import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "例子：利用单子实现算术表达式求值" =>
%%%
tag := "monads-arithmetic-example"
%%%

单子是一种将具有副作用的程序编入没有副作用的语言中的范式。
但很容易将此误解为：承认纯函数式编程缺少一些重要的东西，程序员要越过这些障碍才能编写一个普通的程序。
虽然使用 {moduleName}`Monad` API 确实给程序带来了语法上的成本，但它带来了两个重要的优点：
 1. 程序必须在类型中诚实地告知它们使用的作用。因此看一眼类型签名就可以知道程序能做的所有事情，而不只是知道它接受什么和返回什么。
 2. 并非每种语言都提供相同的作用。例如只有某些语言有异常。其他语言具有独特的新奇作用，例如 [Icon's searching over multiple values](https://www2.cs.arizona.edu/icon/) 以及 Scheme 或 Ruby 的 continuations。由于单子可以编码 _任何_ 作用，因此程序员可以选择最适合给定应用的作用，而不是局限于语言开发者提供的作用。

对许多单子都有意义的一个例子是算术表达式的求值器。

# 算术表达式
%%%
tag := "monads-arithmetic-example-expr"
%%%

:::paragraph
一条算术表达式要么是一个字面量整数，要么是应用于两个表达式的原始二元运算符。运算符包括加法、减法、乘法和除法：

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
表达式 {lit}`2 + 3` 表示为：

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

# 表达式求值
%%%
tag := "monads-arithmetic-example-eval"
%%%

:::paragraph
由于表达式包含除法，而除以零是未定义的，因此求值可能会失败。
表示失败的一种方法是使用 {anchorName evaluateOptionCommingled}`Option`：

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
此定义使用 {anchorTerm MonadOptionExcept}`Monad Option` 实例来传播从二元运算符的两个分支求值产生的失败。
然而该函数混合了两个问题：对子表达式的求值和对运算符的计算。
可以将其拆分为两个函数：

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
运行 {anchorTerm fourteenDivOption}`#eval evaluateOption fourteenDivided` 产生 {anchorInfo fourteenDivOption}`none`，与预期一样，但这个报错信息却并不十分有用。
由于代码使用 {lit}`>>=` 而非显式处理 {anchorName MonadOptionExcept}`none` 构造子，所以只需少量修改即可在失败时提供错误消息：

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
唯一区别是：类型签名提到的是 {anchorTerm evaluateExcept}`Except String` 而非 {anchorName Names}`Option`，并且失败时使用 {anchorName evaluateExcept}`Except.error` 而不是 {anchorName evaluateM}`none`。
通过让求值器对单子多态，并将 {anchorName evaluateM}`applyPrim` 作为参数传递，单个求值器就足够以两种形式报告错误：

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

将其与 {anchorName evaluateMOption}`applyPrimOption` 一起使用作用就和最初的求值器一样：
```anchor evaluateMOption
#eval evaluateM applyPrimOption fourteenDivided
```
```anchorInfo evaluateMOption
none
```
类似地，和 {anchorName evaluateMExcept}`applyPrimExcept` 函数一起使用时作用与带有错误消息的版本相同：
```anchor evaluateMExcept
#eval evaluateM applyPrimExcept fourteenDivided
```
```anchorInfo evaluateMExcept
Except.error "Tried to divide 14 by zero"
```

:::paragraph
代码仍有改进空间。
{anchorName evaluateMOption}`applyPrimOption` 和 {anchorName evaluateMExcept}`applyPrimExcept` 函数仅在除法处理上有所不同，因此可以将它提取到另一个参数中：

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

在重构后的代码中，两条路径仅在对失败情况的处理上有所不同，这一事实显而易见。
:::

# 额外的作用
%%%
tag := "monads-arithmetic-example-effects"
%%%

在考虑求值器时，失败和异常并不是唯一值得在意的作用。虽然除法的唯一副作用是失败，但若要增加其他运算符的支持，则可能需要表达对应的作用。

第一步是重构，从原始数据类型中提取除法：

```anchor PrimCanFail
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
```
名称 {anchorName PrimCanFail}`CanFail` 表明被除法引入的作用是可能发生的失败。

第二步是将除法处理器的参数扩展到 {anchorName evaluateMMorePoly}`evaluateM`，以便它可以处理任何特殊运算符：

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

## 无作用
%%%
tag := "monads-arithmetic-example-no-effects"
%%%

类型 {anchorName applyEmpty}`Empty` 没有构造子，因此没有任何取值，就像Scala或Kotlin中的 {Kotlin}`Nothing` 类型。
在Scala和Kotlin中，{Kotlin}`Nothing` 可以表示永不返回结果的计算，例如导致程序崩溃、或引发异常、或陷入无限循环的函数。
参数类型为 {Kotlin}`Nothing` 表示函数是死代码，因为我们永远无法构造出合适的参数值来调用它。
Lean 不支持无限循环和异常，但 {anchorName applyEmpty}`Empty` 仍然可作为向类型系统说明函数不可被调用的标志。
当 {anchorName nomatch}`E` 是一条表达式，但它的类型没有任何取值时，使用语法 {anchorTerm nomatch}`nomatch E` 向Lean说明当前表达式不返回结果，因为它永远不会被调用。

将 {anchorName applyEmpty}`Empty` 用作 {anchorName PrimCanFail}`Prim` 的参数，表示除了 {anchorName evaluateMMorePoly}`Prim.plus`、{anchorName evaluateMMorePoly}`Prim.minus` 和 {anchorName evaluateMMorePoly}`Prim.times` 之外没有其他情况，因为不可能找到一个类型为 {anchorName nomatch}`Empty` 的值来放在 {anchorName evaluateMMorePoly}`Prim.other` 构造子中。
由于类型为 {anchorName nomatch}`Empty` 的运算符应用于两个整数的函数永远不会被调用，所以它不需要返回结果。
因此，它可以在 _任何_ 单子中使用：

```anchor applyEmpty
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
```
这可以与恒等单子 {anchorName evalId}`Id` 一起使用，用来计算没有任何副作用的表达式：
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
%%%

遇到除以零时，除了直接失败并结束之外，还可以回溯并尝试不同的输入。
给定适当的单子，同一个 {anchorName evalId}`evaluateM` 可以对不致失败的答案 _集合_ 执行非确定性搜索。
这要求除了除法之外，还需要指定选择结果的方式。
一种方法是在表达式的语言中添加一个函数 {lit}`choose`，告诉求值器在搜索非失败结果时选择其中一个参数。

求值结果现在变成一个多重集合，而不是一个单一值。
求值到多重集合的规则如下：
 * 常量 $`n` 求值为单元素集合 $`\{n\}`。
 * 除法以外的算术运算符作用于两个参数的笛卡尔积中的每一对，所以 $`X + Y` 求值为 $`\{ x + y \mid x ∈ X, y ∈ Y \}`。
 * 除法 $`X / Y` 求值为 $`\{ x / y \mid x ∈ X, y ∈ Y, y ≠ 0\}`。换句话说，所有 $`Y` 中的 $`0` 都被丢弃。
 * 选择 $`\mathrm{choose}(x, y)` 求值为 $`\{ x, y \}`。

例如，$`1 + \mathrm{choose}(2, 5)` 求值为 $`\{ 3, 6 \}`，$`1 + 2 / 0` 求值为 $`\{\}`，并且 $`90 / (\mathrm{choose}(-5, 5) + 5)` 求值为 $`\{ 9 \}`。
使用多重集合而非集合，是为了避免处理元素重复的情况而使代码过于复杂。

:::paragraph
表示这种非确定性作用的单子必须能够处理没有答案的情况，以及至少有一个答案和其他答案的情况：

```anchor Many (module := Examples.Monads.Many)
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
```
该数据类型看起来非常像 {anchorName fromList (module:=Examples.Monads.Many)}`List`。
不同之处在于，{anchorName etc}`List.cons` 存储列表的其余部分，而 {anchorName Many (module:=Examples.Monads.Many)}`more` 存储一个函数，该函数应计算剩余的值。
这意味着 {anchorName Many (module:=Examples.Monads.Many)}`Many` 的使用者可以在找到一定数量的结果后停止搜索。
:::

:::paragraph
单个结果由 {anchorName Many (module:=Examples.Monads.Many)}`more` 构造子表示，该构造子不返回任何进一步的结果：

```anchor one (module := Examples.Monads.Many)
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
```
:::

:::paragraph
两个作为结果的多重集合的并集，可以通过检查第一个是否为空来计算。
如果第一个为空则第二个多重集合就是并集。
如果非空，则并集由第一个多重集合的第一个元素，紧跟着其余部分与第二个多重集的并集：

```anchor union (module := Examples.Monads.Many)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
```
:::

:::paragraph
对值列表搜索会比手动构造多重集合更方便。
{anchorName fromList (module:=Examples.Monads.Many)}`Many.fromList` 将列表转换为结果的多重集合：

```anchor fromList (module := Examples.Monads.Many)
def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
```

类似地，一旦搜索已经确定，就可以方便地提取固定数量的值或所有值：

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

{anchorTerm MonadMany (module:=Examples.Monads.Many)}`Monad Many` 实例需要一个 {anchorName MonadContract}`bind` 运算符。
在非确定性搜索中，对两个操作进行排序包括：从第一步中获取所有可能性，并对每种可能性都运行程序的其余部分，取结果的并集。
换句话说，如果第一步返回三个可能的答案，则需要对这三个答案分别尝试第二步。
由于第二步为每个输入都可以返回任意数量的答案，因此取它们的并集表示整个搜索空间。

```anchor bind (module := Examples.Monads.Many)
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
```

{anchorName MonadMany (module:=Examples.Monads.Many)}`Many.one` 和 {anchorName MonadMany (module:=Examples.Monads.Many)}`Many.bind` 遵循单子约定。
要检查 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.one v) f` 是否与 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v` 相同，首先应最大限度地计算表达式：
```anchorEvalSteps bindLeft (module := Examples.Monads.Many)
Many.bind (Many.one v) f
===>
Many.bind (Many.more v (fun () => Many.none)) f
===>
(f v).union (Many.bind Many.none f)
===>
(f v).union Many.none
```
空集是 {anchorName union (module:=Examples.Monads.Many)}`union` 的右单位元，因此答案等同于 {anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`。
要检查 {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` 是否与 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 相同，需要考虑 {anchorName bindOne (module:=Examples.Monads.Many)}`Many.bind` 取 {anchorName one (module:=Examples.Monads.Many)}`Many.one` 应用于 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 的每个元素的并集。
换句话说，如果 {anchorName bindOne (module:=Examples.Monads.Many)}`v` 的形式为 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`，则 {anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one` 是 {anchorTerm vSets (module:=Examples.Monads.Many)}`{v₁} ∪ {v₂} ∪ {v₃} ∪ … ∪ {vₙ}`，即 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`。

最后，要检查 {anchorName bind (module:=Examples.Monads.Many)}`Many.bind` 是否满足结合律，需要检查 {anchorTerm bindBindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.bind v f) g` 是否与 {anchorTerm bindBindRight (module:=Examples.Monads.Many)}`Many.bind v (fun x => Many.bind (f x) g)` 相同。
如果 {anchorName bindBindRight (module:=Examples.Monads.Many)}`v` 的形式为 {anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`，则：
```anchorEvalSteps bindUnion (module := Examples.Monads.Many)
Many.bind v f
===>
f v₁ ∪ f v₂ ∪ f v₃ ∪ … ∪ f vₙ
```
这意味着：
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
因此两边相等，所以 {anchorName bindAssoc (module:=Examples.Monads.Many)}`Many.bind` 满足结合律。

由此得到的单子实例为：

```anchor MonadMany (module := Examples.Monads.Many)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
```
利用此单子，下例可找到列表中所有加起来等于15的数字组合：

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
对列表进行递归搜索。
当列表为空且目标为 {anchorTerm addsTo (module:=Examples.Monads.Many)}`0` 时，返回空列表表示成功；否则，返回失败。
当列表非空时，有两种可能性：要么列表的头部大于目标，在这种情况下它不能参与任何成功的搜索，要么它不大于，在这种情况下可以参与。
如果列表的头部 _不是_ 候选者，则对列表的尾部进行递归搜索。
如果头部是候选者，则有两种用 {anchorName union (module:=Examples.Monads.Many)}`Many.union` 合并起来的可能性：找到的解含有头部，或者不含有。
不含头部的解通过递归调用尾部找到，而含有头部的解通过从目标中减去头部，然后将头部附加到递归调用的解中得到。

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
让我们回到产生多重集合的算术求值器，{anchorName NeedsSearch}`choose` 运算符可以用来非确定性地选择一个值，除以零会使之前的选择失效：

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
可以用这些运算符对前面的示例求值：

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
%%%

可以通过允许将字符串当作运算符，然后提供从字符串到它们的实现函数之间的映射，使求值器可由用户扩展。
例如，用户可以用余数运算或最大值运算来扩展求值器。
从函数名称到函数实现的映射称为 _环境_。

环境需要在每层递归调用之间传递。
因此一开始 {anchorName evaluateM}`evaluateM` 看起来需要一个额外的参数来保存环境，并且该参数需要在每次递归调用时传递。
然而，像这样传递参数是单子的另一种形式，因此一个适当的 {anchorName evaluateM}`Monad` 实例允许求值器本身保持不变。

将函数当作单子，这通常称为 _reader_ 单子。
在reader单子中对表达式求值使用以下规则：
 * 常量 $`n` 求值为常量函数 $`λ e . n`，
 * 算术运算符求值为将参数各自传递然后计算的函数，因此 $`f + g` 求值为 $`λ e . f(e) + g(e)`，并且
 * 自定义运算符求值为将自定义运算符应用于参数的结果，因此 $`f \ \mathrm{OP}\ g` 求值为
   $$`
     λ e .
     \begin{cases}
     h(f(e), g(e)) & \mathrm{if}\ e\ \mathrm{contains}\ (\mathrm{OP}, h) \\
     0 & \mathrm{otherwise}
     \end{cases}
   `
   其中 $`0` 用于运算符未知的情况。

:::paragraph
要在Lean中定义reader单子，第一步是定义 {anchorName Reader}`Reader` 类型，和用户获取环境的作用：

```anchor Reader
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env
```
按照惯例，希腊字母 {anchorName Reader}`ρ`（发音为“rho”）用于表示环境。
:::

:::paragraph
算术表达式中的常量映射为常量函数这一事实表明，{anchorName Reader}`Reader` 的 {anchorName IdMonad}`pure` 的适当定义是一个常量函数：

```anchor ReaderPure
def Reader.pure (x : α) : Reader ρ α := fun _ => x
```
:::


另一方面，{anchorName MonadContract}`bind` 则有点棘手。
它的类型是 {anchorTerm readerBindType}`Reader ρ α → (α → Reader ρ β) → Reader ρ β`。
通过展开 {anchorName Reader}`Reader` 的定义，可以更容易地理解此类型，从而产生 {anchorTerm readerBindTypeEval}`(ρ → α) → (α → ρ → β) → (ρ → β)`。
它将读取环境的函数作为第一个参数，而第二个参数将第一个参数的结果转换为另一个读取环境的函数。
组合这些结果本身就是一个读取环境的函数。

可以交互式地使用Lean，获得编写该函数的帮助。
为了获得尽可能多的帮助，第一步是非常明确地写下参数的类型和返回的类型，用下划线表示定义的主体：
```anchor readerbind0
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
```
Lean提供的消息描述了哪些变量在作用域内可用，以及结果的预期类型。
{lit}`⊢` 符号，由于它类似于地铁入口而被称为 _turnstile_，将局部变量与所需类型分开，在此消息中为 {anchorTerm readerbind0}`ρ → β`：
```anchorError readerbind0
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
```

因为返回类型是一个函数，所以第一步最好在下划线外套一层 {kw}`fun`：
```anchor readerbind1
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => _
```
产生的消息说明现在函数的参数已经成为一个局部变量：
```anchorError readerbind1
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β
```

上下文中唯一可以产生 {anchorName readerbind2a}`β` 的是 {anchorName readerbind2a}`next`， 并且它需要两个参数。
每个参数都可以用下划线表示：
```anchor readerbind2a
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
```
这两个下划线分别有如下的消息：
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
先处理第一条下划线，注意到上下文中只有一个东西可以产生 {anchorName readerbind3}`α`，即 {anchorName readerbind3}`result`：
```anchor readerbind3
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result _) _
```
现在两条下划线都有一样的报错了：
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
值得高兴的是，两条下划线都可以被 {anchorName readerbind4}`env` 替换，得到：

```anchor readerbind4
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
```
:::

要得到最后的版本，只需要把我们前面对 {anchorName Readerbind}`Reader` 的展开撤销，并且去掉过于明确的细节：

```anchor Readerbind
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
```

仅仅跟着类型信息走并不总是能写出正确的函数，并且有未能完全理解产生的程序的风险。
然而理解一个已经写出的程序比理解还没写出的要简单，而且逐步填充下划线的内容也可以提供思路。
这张情况下，{anchorName Readerbind}`Reader.bind` 和 {anchorName IdMonad}`Id` 的 {anchorName IdMonad}`bind` 很像，唯一区别在于它接受一个额外的参数并传递到其他参数中。这个直觉可以帮助理解它的原理。

{anchorName ReaderPure}`Reader.pure`（生成常量函数）和 {anchorName Readerbind}`Reader.bind` 遵循单子约定。
要检查 {anchorTerm ReaderMonad1}`Reader.bind (Reader.pure v) f` 与 {anchorTerm ReaderMonad1}`f v` 等价, 只需要不断地展开定义即可：
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
对任意函数 {anchorName eta}`f` 来说，{anchorTerm eta}`fun x => f x` 和 {anchorName eta}`f` 是等价的，所以约定的第一部分已经满足。
要检查 {anchorTerm ReaderMonad2}`Reader.bind r Reader.pure` 与 {anchorName ReaderMonad2}`r` 等价，只需要相似的技巧：
```anchorEvalSteps ReaderMonad2
Reader.bind r Reader.pure
===>
fun env => Reader.pure (r env) env
===>
fun env => (fun _ => (r env)) env
===>
fun env => r env
```
因为 reader actions {anchorName ReaderMonad2}`r` 本身是函数，所以这和 {anchorName ReaderMonad2}`r` 也是等价的。
要检查结合律，只需要对 {anchorEvalStep ReaderMonad3a 0}`Reader.bind (Reader.bind r f) g` 和 {anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)` 重复同样的步骤：
```anchorEvalSteps ReaderMonad3a
Reader.bind (Reader.bind r f) g
===>
fun env => g ((Reader.bind r f) env) env
===>
fun env => g ((fun env' => f (r env') env') env) env
===>
fun env => g (f (r env) env) env
```

{anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)` 展开为同样的表达式：
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

至此，{anchorTerm MonadReaderInst}`Monad (Reader ρ)` 实例已经得到了充分验证：

```anchor MonadReaderInst
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
```

要被传递给表达式求值器的环境可以用键值对的列表来表示：

```anchor Env
abbrev Env : Type := List (String × (Int → Int → Int))
```
例如，{anchorName exampleEnv}`exampleEnv` 包含最大值和模函数：

```anchor exampleEnv
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
```

Lean已提供函数 {anchorName etc}`List.lookup` 用来在键值对的列表中根据键寻找对应的值，所以 {anchorName applyPrimReader}`applyPrimReader` 只需要确认自定义函数是否存在于环境中即可。如果不存在则返回 {anchorTerm applyPrimReader}`0`：

```anchor applyPrimReader
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
```

将 {anchorName readerEval}`evaluateM`、{anchorName readerEval}`applyPrimReader`、和一条表达式一起使用，即得到一个接受环境的函数。
而我们前面已经准备好了 {anchorName readerEval}`exampleEnv`：
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

与 {anchorName Many (module:=Examples.Monads.Many)}`Many` 一样，{anchorName Reader}`Reader` 是难以在大多数语言中编码的作用，但类型类和单子使其与任何其他作用一样方便。
Common Lisp、Clojure和Emacs Lisp中的动态或特殊变量可以用作 {anchorName Reader}`Reader`。
类似地，Scheme和Racket的参数对象是一个与 {anchorName Reader}`Reader` 完全对应的作用。
Kotlin的上下文对象可以解决类似的问题，但根本上是一种自动传递函数参数的方式，因此更像是作为reader单子的编码，而不是语言中实现的作用。

## 练习
%%%
tag := "monads-arithmetic-example-exercises"
%%%

### 检查约定
%%%
tag := none
%%%

检查 {anchorTerm StateMonad}`State σ` 和 {anchorTerm MonadOptionExcept}`Except ε` 满足单子约定。


### 允许Reader失败
%%%
tag := none
%%%
调整例子中的reader单子，使得它可以在自定义的运算符不存在时提供错误信息而不是直接返回0。
换句话说，给定这些定义：

```anchor ReaderFail
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
```
要做的是：

### 带有跟踪信息的求值器
%%%
tag := "monads-arithmetic-example-exercise-trace"
%%%

{anchorName MonadWriter}`WithLog` 类型可以和求值器一起使用，来实现对某些运算的跟踪。
特别地，可以使用 {anchorName ToTrace}`ToTrace` 类型来追踪某个给定的运算符：

```anchor ToTrace
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α
```
对于带有跟踪信息的求值器，表达式应该具有类型 {anchorTerm ToTraceExpr}`Expr (Prim (ToTrace (Prim Empty)))`。
这说明表达式中的运算符由附加参数的加、减、乘运算组成。最内层的参数是 {anchorName ToTraceExpr}`Empty`，说明在 {anchorName ToTrace}`trace` 内部没有特殊运算符，只有三种基本运算。

要做的是：

如果练习已经正确实现，那么
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
将有如下结果
```anchorInfo evalTraced
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
```

 提示：类型为 {anchorTerm ToTraceExpr}`Prim Empty` 的值会出现在日志中。为了让它们能被 {kw}`#eval` 输出，需要下面几个实例：

```anchor ReprInstances
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
```
