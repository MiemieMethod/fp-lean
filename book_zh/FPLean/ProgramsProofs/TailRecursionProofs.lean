import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "证明等价性" =>
%%%
tag := "proving-tail-rec-equiv"
file := "Proving-Equivalence"
%%%

被改写为使用尾递归和累加器的程序，看起来可能与原程序相当不同。
原始递归函数通常更容易理解，但它有在运行时耗尽栈的风险。
在用示例测试程序的两个版本以排除简单错误之后，可以使用证明一劳永逸地表明这些程序是等价的。

# 证明 {lit}`sum` 相等
%%%
tag := "proving-sum-equal"
file := "Proving-sum-Equal"
%%%

要证明 {lit}`sum` 的两个版本相等，先写出带有占位证明的定理陈述：
```anchor sumEq0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  skip
```
正如预期，Lean 描述了一个尚未解决的目标：
```anchorError sumEq0
unsolved goals
⊢ NonTail.sum = Tail.sum
```

这里不能应用 {kw}`rfl` 策略，因为 {anchorName sumEq0}`NonTail.sum` 和 {anchorName sumEq0}`Tail.sum` 并非定义相等。
不过，函数相等的方式并不只限于定义相等。
也可以通过证明两个函数对相同输入产生相等输出来证明它们相等。
换言之，可以通过证明对所有可能输入 $`x` 都有 $`f(x) = g(x)`，来证明 $`f = g`。
这一原则称为_函数外延性_。
函数外延性正是 {anchorName sumEq0}`NonTail.sum` 等于 {anchorName sumEq0}`Tail.sum` 的原因：二者都会对数的列表求和。

在 Lean 的策略语言中，函数外延性通过使用 {anchorTerm sumEq1}`funext` 来调用，后面跟随一个名称，用作任意参数的名字。
该任意参数会作为一个假设加入上下文，而目标会变为要求证明这些函数应用于该参数后相等：
```anchor sumEq1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError sumEq1
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```

这个目标可以通过对参数 {anchorName sumEq1}`xs` 做归纳来证明。
当应用于空列表时，两个 {lit}`sum` 函数都返回 {anchorTerm TailSum}`0`，这可作为基例。
在输入列表的开头添加一个数，会使两个函数都把该数加到结果中，这可作为归纳步骤。
调用 {anchorTerm sumEq2a}`induction` 策略会产生两个目标：
```anchor sumEq2a
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
```anchorError sumEq2a
unsolved goals
case h.nil
⊢ NonTail.sum [] = Tail.sum []
```
```anchorError sumEq2b
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
```

{anchorName sumEq3}`nil` 的基本情形可以使用 {anchorTerm sumEq3}`rfl` 解决，因为当传入空列表时，两个函数都返回 {anchorTerm TailSum}`0`：
```anchor sumEq3
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```

求解归纳步骤的第一步是简化目标，要求 {anchorTerm sumEq4}`simp` 展开 {anchorName sumEq4}`NonTail.sum` 和 {anchorName sumEq4}`Tail.sum`：
```anchor sumEq4
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum]
```
```anchorError sumEq4
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)
```
展开 {anchorName sumEq5}`Tail.sum` 显示出它会立即委托给 {anchorName sumEq5}`Tail.sumHelper`，后者也应当被化简：
```anchor sumEq5
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
```
在所得目标中，{anchorName TailSum}`sumHelper` 已执行一步计算，并将 {anchorName sumEq5}`y` 加入累加器：
```anchorError sumEq5
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys
```
用归纳假设进行重写，会从目标中移除所有对 {anchorName sumEq6}`NonTail.sum` 的提及：
```anchor sumEq6
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
```
```anchorError sumEq6
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + Tail.sum ys = Tail.sumHelper y ys
```
这个新目标断言，将某个数加到一个列表的和上，等同于在 {anchorName TailSum}`sumHelper` 中把该数用作初始累加器。
为清晰起见，可以将这个新目标作为一个单独的定理来证明：
```anchor sumEqHelperBad0
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  skip
```
```anchorError sumEqHelperBad0
unsolved goals
xs : List Nat
n : Nat
⊢ n + Tail.sum xs = Tail.sumHelper n xs
```
再一次，这是一个归纳证明，其中基本情形使用 {anchorTerm sumEqHelperBad1}`rfl`：
```anchor sumEqHelperBad1
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```
```anchorError sumEqHelperBad1
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
由于这是一个归纳步骤，目标应当被简化，直到它与归纳假设 {anchorName sumEqHelperBad2}`ih` 相匹配。
使用 {anchorName sumEqHelperBad2}`Tail.sum` 和 {anchorName sumEqHelperBad2}`Tail.sumHelper` 的定义进行简化，会得到如下结果：
```anchor sumEqHelperBad2
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [Tail.sum, Tail.sumHelper]
```
```anchorError sumEqHelperBad2
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
```
理想情况下，可以使用归纳假设来替换 {lit}`Tail.sumHelper (y + n) ys`，但二者并不匹配。
归纳假设可用于 {lit}`Tail.sumHelper n ys`，而不能用于 {lit}`Tail.sumHelper (y + n) ys`。
换言之，这个证明卡住了。

# 第二次尝试
%%%
tag := "proving-sum-equal-again"
file := "A-Second-Attempt"
%%%

与其试图勉强推进这个证明，不如退后一步进行思考。
为什么该函数的尾递归版本等于非尾递归版本？
从根本上说，在列表的每一个条目处，累加器增加的量与递归结果中本应增加的量相同。
这一洞察可用于写出一个优雅的证明。
关键在于，归纳证明必须以这样的方式设定：归纳假设能够应用于_任意_累加器值。

舍弃先前的尝试后，可以将这一洞见编码为如下陈述：
```anchor nonTailEqHelper0
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  skip
```
在这个陈述中，{anchorName nonTailEqHelper0}`n` 是冒号之后的类型的一部分，这一点非常重要。
所得目标以 {lit}`∀ (n : Nat)` 开始，它是“对于所有 {lit}`n`”的简写：
```anchorError nonTailEqHelper0
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
```
使用归纳策略会产生包含这个“对所有”陈述的目标：
```anchor nonTailEqHelper1a
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
在 {anchorName nonTailEqHelper1a}`nil` 情形中，目标是：
```anchorError nonTailEqHelper1a
unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
```
对于 {anchorName nonTailEqHelper1a}`cons` 的归纳步骤，归纳假设和具体目标都包含“对所有 {lit}`n`”：
```anchorError nonTailEqHelper1b
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
换言之，目标变得更难证明了，但归纳假设也相应地更加有用。

对于一个以“对所有 $`x`”开头的陈述，其数学证明应当假设某个任意的 $`x`，并证明该陈述。
“任意”意味着不假设 $`x` 具有任何额外性质，因此所得陈述将适用于_任意_ $`x`。
在 Lean 中，“对所有”陈述是一个依值函数：无论它被应用于哪个具体值，它都会返回该命题的证据。
类似地，选取任意 $`x` 的过程与使用 {lit}`fun x => ...` 是相同的。
在策略语言中，这种选择任意 $`x` 的过程使用 {kw}`intro` 策略来执行；当策略脚本完成时，它会在幕后生成相应的函数。
应当向 {kw}`intro` 策略提供用于这个任意值的名称。

在 {anchorName nonTailEqHelper2}`nil` 情形中使用 {kw}`intro` 策略，会从目标中移除 {lit}`∀ (n : Nat),`，并添加一个假设 {lit}`n : Nat`：
```anchor nonTailEqHelper2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n
  | cons y ys ih => skip
```
```anchorError nonTailEqHelper2
unsolved goals
case nil
n : Nat
⊢ n + NonTail.sum [] = Tail.sumHelper n []
```
这个命题等式的两边按定义都等于 {anchorName nonTailEqHelper3}`n`，因此 {anchorTerm nonTailEqHelper3}`rfl` 就足够了：
```anchor nonTailEqHelper3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih => skip
```
{anchorName nonTailEqHelper3}`cons` 目标也包含一个“对所有”：
```anchorError nonTailEqHelper3
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
这提示可以使用 {kw}`intro`。
```anchor nonTailEqHelper4
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
```
```anchorError nonTailEqHelper4
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
现在，证明目标同时包含应用于 {lit}`y :: ys` 的 {anchorName nonTailEqHelper5}`NonTail.sum` 和 {anchorName nonTailEqHelper5}`Tail.sumHelper`。
化简器可以使下一步更加清楚：
```anchor nonTailEqHelper5
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
```
```anchorError nonTailEqHelper5
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
```
这个目标与归纳假设非常接近。
它有两个方面不匹配：
 * 等式的左侧是 {lit}`n + (y + NonTail.sum ys)`，但归纳假设要求左侧是某个数加上 {lit}`NonTail.sum ys`。
换言之，这个目标应当被改写为 {lit}`(n + y) + NonTail.sum ys`，这是有效的，因为自然数加法满足结合律。
 * 当左侧已被重写为 {lit}`(y + n) + NonTail.sum ys` 时，为了匹配，右侧的累加器参数应当是 {lit}`n + y`，而不是 {lit}`y + n`。
这一重写是有效的，因为加法也是可交换的。

加法的结合律和交换律已经在 Lean 的标准库中得到证明。
结合律的证明名为 {anchorTerm NatAddAssoc}`Nat.add_assoc`，其类型为 {anchorTerm NatAddAssoc}`(n m k : Nat) → (n + m) + k = n + (m + k)`；而交换律的证明名为 {anchorTerm NatAddComm}`Nat.add_comm`，其类型为 {anchorTerm NatAddComm}`(n m : Nat) → n + m = m + n`。
通常，{kw}`rw` 策略会接收一个类型为等式的表达式。
然而，如果其参数转而是一个返回类型为等式的依值函数，它就会尝试为该函数寻找一些参数，使得该等式能够匹配目标中的某些内容。
不过，只有一个应用结合律的机会；但由于 {anchorTerm NatAddAssoc}`(n + m) + k = n + (m + k)` 中等式的右侧才是与证明目标匹配的一侧，重写方向必须反过来：
```anchor nonTailEqHelper6
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
```
```anchorError nonTailEqHelper6
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
```
然而，直接用 {anchorTerm nonTailEqHelper7}`rw [Nat.add_comm]` 改写会导致错误的结果。
{kw}`rw` 策略猜错了改写的位置，从而产生了非预期的目标：
```anchor nonTailEqHelper7
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm]
```
```anchorError nonTailEqHelper7
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys
```
这可以通过显式地向 {anchorName nonTailEqHelper8}`Nat.add_comm` 提供 {anchorName nonTailEqHelper8}`y` 和 {anchorName nonTailEqHelper8}`n` 作为参数来修正：
```anchor nonTailEqHelper8
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
```
```anchorError nonTailEqHelper8
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
```
现在目标与归纳假设相匹配。
特别地，归纳假设的类型是一个依值函数类型。
将 {anchorName nonTailEqHelperDone}`ih` 应用于 {anchorTerm nonTailEqHelperDone}`n + y`，恰好得到所期望的类型。
如果 {kw}`exact` 策略的参数恰好具有所期望的类型，它就会完成一个证明目标：

```anchor nonTailEqHelperDone
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n; rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)
```

实际证明只需少量额外工作，使目标与辅助定理的类型匹配。
第一步仍然是调用函数外延性：
```anchor nonTailEqReal0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError nonTailEqReal0
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```
下一步是展开 {anchorName nonTailEqReal1}`Tail.sum`，从而暴露 {anchorName TailSum}`Tail.sumHelper`：
```anchor nonTailEqReal1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
```
```anchorError nonTailEqReal1
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sumHelper 0 xs
```
完成这一步后，类型几乎匹配。
然而，辅助定理在左侧有一个额外的加数。
换言之，证明目标是 {lit}`NonTail.sum xs = Tail.sumHelper 0 xs`，但将 {anchorName nonTailEqHelper0}`non_tail_sum_eq_helper_accum` 应用于 {anchorName nonTailEqReal2}`xs` 和 {anchorTerm NatZeroAdd}`0` 会得到类型 {lit}`0 + NonTail.sum xs = Tail.sumHelper 0 xs`。
另一个标准库证明 {anchorTerm NatZeroAdd}`Nat.zero_add` 的类型是 {anchorTerm NatZeroAdd}`(n : Nat) → 0 + n = n`。
将此函数应用于 {anchorTerm nonTailEqReal2}`NonTail.sum xs` 会得到一个类型为 {anchorTerm NatZeroAddApplied}`0 + NonTail.sum xs = NonTail.sum xs` 的表达式，因此从右到左重写便得到所需目标：
```anchor nonTailEqReal2
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
```
```anchorError nonTailEqReal2
unsolved goals
case h
xs : List Nat
⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
```
最后，可以使用该辅助定理来完成证明：

```anchor nonTailEqRealDone
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0
```

这个证明展示了一种一般模式，可用于证明以累加器传递方式编写的尾递归函数等于其非尾递归版本。
第一步是发现起始累加器参数与最终结果之间的关系。
例如，以 {anchorName accum_stmt}`n` 作为累加器开始 {anchorName TailSum}`Tail.sumHelper`，会使最终总和被加到 {anchorName accum_stmt}`n` 上；以 {anchorName accum_stmt}`ys` 作为累加器开始 {anchorName accum_stmt}`Tail.reverseHelper`，会使最终反转后的列表被前置到 {anchorName accum_stmt}`ys` 上。
第二步是将这种关系写成定理陈述，并通过归纳来证明它。
尽管在实践中累加器总是以某个中性值初始化，例如 {anchorTerm TailSum}`0` 或 {anchorTerm accum_stmt}`[]`，但为了得到足够强的归纳假设，所需要的是这个更一般的陈述，它允许起始累加器为任意值。
最后，将这个辅助定理用于实际的初始累加器值，即可得到所需的证明。
例如，在 {anchorName nonTailEqRealDone}`non_tail_sum_eq_tail_sum` 中，累加器被指定为 {anchorTerm TailSum}`0`。
这可能需要重写目标，以便使中性的初始累加器值出现在正确的位置。

# 函数归纳
%%%
tag := "fun-induction"
file := "Functional-Induction"
%%%

{anchorName nonTailEqRealDone}`non_tail_sum_eq_helper_accum` 的证明紧密遵循 {anchorName TailSum}`Tail.sumHelper` 的实现。
然而，实现与数学归纳所期望的结构之间并非完全吻合，因此有必要谨慎地管理假设 {anchorName nonTailEqHelperDone}`n`。
在 {anchorName nonTailEqHelperDone}`non_tail_sum_eq_helper_accum` 的情形中，这只需要少量工作；但对于其定义与 {tactic}`induction` 所期望的结构相距更远的函数，有关它们的证明则需要更多的簿记工作。

除了通过对某个参数进行归纳来证明关于递归函数的定理之外，Lean 还支持按照函数的递归调用结构进行归纳证明。
这种 {deftech}_函数归纳_ 会为函数控制流中不包含递归调用的每个分支产生一个基本情形，并为包含递归调用的每个分支产生归纳步骤。
通过函数归纳进行的证明应当表明：该定理对于非递归分支成立；并且如果该定理对于每个递归调用的结果成立，那么它对于递归分支的结果也成立。

:::paragraph
使用函数式归纳会简化 {anchorName nonTailEqHelperFunInd1}`non_tail_sum_eq_helper_accum`：
```anchor nonTailEqHelperFunInd1
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => skip
  | case2 n y ys ih => skip
```
证明的每个分支都与 {anchorName TailSum}`Tail.sumHelper` 的相应分支匹配：
```anchorTerm TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
```
在第一个 {anchorTerm nonTailEqHelperFunInd1}`case1` 中，等式右侧是累加器值，在证明中称为 {anchorName nonTailEqHelperFunInd1}`n`：
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case1
n : Nat
⊢ n + NonTail.sum [] = n
```
在第二个 {anchorTerm nonTailEqHelperFunInd1}`case2` 中，等式的右侧是尾递归循环中的下一步：
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case2
n y : Nat
ys : List Nat
ih : y + n + NonTail.sum ys = Tail.sumHelper (y + n) ys
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper (y + n) ys
```
:::

:::paragraph
所得证明可以更简单。
论证的基本内容，包括所使用的加法性质，都是相同的；不过，簿记工作已被移除。
不再需要手动调度累加器的值，并且归纳假设可以直接使用，而无需实例化：
```anchor nonTailEqHelperFunInd2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => simp [NonTail.sum]
  | case2 n y ys ih =>
    simp [NonTail.sum]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm n y]
    assumption
```
:::

:::paragraph
{tactic}`grind` 策略非常适合这类目标。
与 {tactic}`simp` 和 {tactic}`rw` 不同，它不是定向的；在内部，它会累积一组事实，直到要么完全证明目标，要么无法做到为止。
它已预先配置为使用关于算术的基本事实，例如加法的结合律和交换律，并且会自动使用局部假设，例如归纳假设。
使用 {tactic}`grind` 后，这个证明变得简短而切中要点：
```anchor nonTailEqHelperFunInd3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper <;> grind [NonTail.sum]
```
这个证明也符合向熟练程序员解释该证明的方式：“只需检查 {anchorName nonTailEqHelperFunInd3}`Tail.sumHelper` 的两个分支！”
:::

# 练习
%%%
tag := "tail-recursion-proof-exercises"
file := "Exercise"
%%%

## 热身
%%%
tag := none
file := "Warming-Up"
%%%

使用 {kw}`induction` 策略，为 {anchorName NatZeroAdd}`Nat.zero_add`、{anchorName NatAddAssoc}`Nat.add_assoc` 和 {anchorName NatAddComm}`Nat.add_comm` 写出你自己的证明。

## 更多累加器证明
%%%
tag := none
file := "More-Accumulator-Proofs"
%%%

### 反转列表
%%%
tag := none
file := "Reversing-Lists"
%%%

将 {anchorName NonTailSum}`sum` 的证明改写为 {anchorName NonTailReverse}`NonTail.reverse` 和 {anchorName TailReverse}`Tail.reverse` 的证明。
第一步是思考传递给 {anchorName TailReverse}`Tail.reverseHelper` 的累加器值与非尾递归 reverse 之间的关系。
正如在 {anchorName TailSum}`Tail.sumHelper` 中向累加器加上一个数等同于将其加到总和上一样，在 {anchorName TailReverse}`Tail.reverseHelper` 中使用 {anchorName names}`List.cons` 向累加器添加一个新条目，等价于对整体结果作某种改变。
请用纸笔尝试三四个不同的累加器值，直到这种关系变得清楚。
利用这一关系证明一个合适的辅助定理。
尝试分别使用对列表的归纳以及函数式归纳来证明这个辅助定理。
然后，写出整体定理。
因为 {anchorName reverseEqStart}`NonTail.reverse` 和 {anchorName TailReverse}`Tail.reverse` 是多态的，陈述它们相等时需要使用 {lit}`@`，以阻止 Lean 尝试推断 {anchorName reverseEqStart}`α` 应使用哪个类型。
一旦 {anchorName reverseEqStart}`α` 被当作普通参数处理，就应当同时以 {anchorName reverseEqStart}`α` 和 {anchorName reverseEqStart}`xs` 调用 {kw}`funext`：
```anchor reverseEqStart
theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
```
这会产生一个合适的目标：
```anchorError reverseEqStart
unsolved goals
case h.h
α : Type u_1
xs : List α
⊢ NonTail.reverse xs = Tail.reverse xs
```


### 阶乘
%%%
tag := none
file := "Factorial"
%%%


证明上一节练习中的 {anchorName NonTailFact}`NonTail.factorial` 等于你的尾递归解法：找出累加器与结果之间的关系，并证明一个合适的辅助定理。
