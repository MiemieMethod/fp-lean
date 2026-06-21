import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Induction"

#doc (Manual) "插曲：策略、归纳与证明" =>
%%%
tag := "tactics-induction-proofs"
number := false
htmlSplit := .never
file := "Interlude___-Tactics___-Induction___-and-Proofs"
%%%

# 关于证明与用户界面的说明
%%%
tag := "proofs-and-uis"
file := "A-Note-on-Proofs-and-User-Interfaces"
%%%

本书呈现编写证明的过程时，仿佛证明是一口气写成并提交给 Lean 的，而 Lean 随后以错误消息回应，说明还剩什么需要完成。
实际与 Lean 交互的过程要愉快得多。
当光标在证明中移动时，Lean 会提供关于该证明的信息，并且还有许多交互式功能使证明更加容易。
请查阅你的 Lean 开发环境的文档以获得更多信息。

本书采用的方法侧重于逐步构建证明并展示由此产生的消息；它展示了 Lean 在编写证明时提供的各种交互式反馈，尽管这比专家所采用的过程慢得多。
与此同时，观察不完整的证明逐渐演化为完整证明，是理解证明的一种有益视角。
随着你编写证明的能力提高，Lean 的反馈会越来越不像错误，而更像是对你自身思考过程的支持。
学习这种交互式方法非常重要。

# 递归与归纳
%%%
tag := "recursion-vs-induction"
file := "Recursion-and-Induction"
%%%

前一章中的函数 {anchorName plusR_succ_left (module := Examples.DependentTypes.Pitfalls)}`plusR_succ_left` 和 {anchorName plusR_zero_left_thm (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left` 可以从两个角度来看。
一方面，它们是递归函数，用来构造某个命题的证据，正如其他递归函数可能构造列表、字符串或任何其他数据结构一样。
另一方面，它们也对应于通过_数学归纳法_进行的证明。

数学归纳法是一种证明技术，用两步证明某个陈述对_所有_自然数都成立：
 1. 证明该陈述对 $`0` 成立。这称为_基本情形_。
 2. 在假设该陈述对某个任意选取的数 $`n` 成立的前提下，证明它对 $`n + 1` 也成立。这称为_归纳步骤_。该陈述对 $`n` 成立的假设称为_归纳假设_。

由于不可能对_每一个_自然数都检查该陈述，归纳法提供了一种撰写证明的手段：原则上，该证明可以展开到任意特定的自然数。
例如，如果需要针对数字 3 的具体证明，那么可以先使用基本情形，再使用三次归纳步骤来构造它，从而依次表明该陈述对 0、1、2，最后对 3 成立。
因此，它证明了该陈述对所有自然数成立。

# 归纳策略
%%%
tag := "induction-tactic"
file := "The-Induction-Tactic"
%%%

将归纳证明写成使用诸如 {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`congrArg` 之类辅助项的递归函数，并不总是能很好地表达证明背后的意图。
虽然递归函数确实具有归纳的结构，但也许应当把它们看作证明的一种_编码_。
此外，Lean 的策略系统提供了许多自动构造证明的机会，而这些机会在显式编写递归函数时并不存在。
Lean 提供了一种归纳_策略_，能够在单个策略块中完成整个归纳证明。
在幕后，Lean 会构造与使用归纳法相对应的递归函数。

要用 {kw}`induction` 策略证明 {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left`，先写出它的签名（使用 {kw}`theorem`，因为这确实是一个证明）。
然后，使用 {anchorTerm plusR_ind_zero_left_1}`by induction k` 作为定义的主体：
```anchor plusR_ind_zero_left_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
```
所得消息表明存在两个目标：
```anchorError plusR_ind_zero_left_1
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)
```
策略块是在 Lean 类型检查器处理文件时运行的程序，有点像一种强大得多的 C 预处理器宏。
策略会生成实际的程序。

在策略语言中，可以有若干个目标。
每个目标由一个类型以及若干假设组成。
这类似于使用下划线作为占位符：目标中的类型表示要证明的内容，而假设表示当前作用域内可用的内容。
对于目标 {lit}`case zero`，没有假设，且类型为 {anchorTerm others}`Nat.zero = Nat.plusR 0 Nat.zero`；这就是将 {anchorName plusR_ind_zero_left_1}`k` 替换为 {anchorTerm others}`0` 后的定理陈述。
在目标 {lit}`case succ` 中，有两个假设，分别命名为 {lit}`n✝` 和 {lit}`n_ih✝`。
在幕后，{anchorTerm plusR_ind_zero_left_1}`induction` 策略会创建一个依值模式匹配来细化整体类型，而 {lit}`n✝` 表示该模式中传给 {anchorName others}`Nat.succ` 的参数。
假设 {lit}`n_ih✝` 表示对 {lit}`n✝` 递归调用所生成函数的结果。
它的类型就是该定理的整体类型，只是将 {anchorName plusR_ind_zero_left_1}`k` 替换为 {lit}`n✝`。
作为目标 {lit}`case succ` 的一部分需要满足的类型，是将 {anchorName plusR_ind_zero_left_1}`k` 替换为 {lit}`Nat.succ n✝` 后的整体定理陈述。

使用 {anchorTerm plusR_ind_zero_left_1}`induction` 策略产生的两个目标，对应于数学归纳法描述中的基例和归纳步骤。
基例是 {lit}`case zero`。
在 {lit}`case succ` 中，{lit}`n_ih✝` 对应于归纳假设，而整个 {lit}`case succ` 则是归纳步骤。

撰写该证明的下一步，是依次关注这两个目标中的每一个。
正如 {anchorTerm others}`pure ()` 可以在 {kw}`do` 块中用来表示“什么也不做”一样，策略语言也有一个语句 {kw}`skip`，它同样什么也不做。
当 Lean 的语法要求一个策略，但尚不清楚应当使用哪一个策略时，可以使用它。
在 {kw}`induction` 语句末尾添加 {kw}`with`，会提供一种类似于模式匹配的语法：
```anchor plusR_ind_zero_left_2a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
```
两个 {kw}`skip` 陈述各自都有一条与之关联的消息。
第一条显示基例：
```anchorError plusR_ind_zero_left_2a
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
```
第二个显示归纳步骤：
```anchorError plusR_ind_zero_left_2b
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
```
在归纳步骤中，带有剑标的不可访问名称已被替换为 {lit}`succ` 之后提供的名称，即 {anchorName plusR_ind_zero_left_2a}`n` 和 {anchorName plusR_ind_zero_left_2a}`ih`。

{kw}`induction`{lit}` ...`{kw}`with` 之后的各个情形并不是模式：它们由一个目标的名称后接零个或多个名称组成。
这些名称用于目标中引入的假设；若提供的名称多于该目标所引入的名称，则会报错：
```anchor plusR_ind_zero_left_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih lots of names => skip
```
```anchorError plusR_ind_zero_left_3
Too many variable names provided at alternative `succ`: 5 provided, but 2 expected
```

聚焦于基例，{kw}`rfl` 策略在 {kw}`induction` 策略内部的作用方式与其在递归函数中的作用方式一样好：
```anchor plusR_ind_zero_left_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih => skip
```
在该证明的递归函数版本中，一个类型标注使预期类型变得更容易理解。
在策略语言中，有若干种特定方式可以变换目标，使其更容易求解。
{kw}`unfold` 策略会用已定义名称的定义来替换该名称：
```anchor plusR_ind_zero_left_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
```
现在，目标中等式的右侧已经变成 {anchorTerm others}`Nat.plusR 0 n + 1`，而不是 {anchorTerm others}`Nat.plusR 0 (Nat.succ n)`：
```anchorError plusR_ind_zero_left_5
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1
```

除了诉诸 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`congrArg` 这样的函数和 {anchorTerm appendR (module:=Examples.DependentTypes.Pitfalls)}`▸` 这样的运算符之外，还有一些策略允许使用相等性证明来变换证明目标。
其中最重要的策略之一是 {kw}`rw`，它接受一个相等性证明列表，并在目标中用右侧替换左侧。
这在 {anchorName plusR_ind_zero_left_6}`plusR_zero_left` 中几乎做了正确的事：
```anchor plusR_ind_zero_left_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [ih]
```
然而，重写的方向不正确。
用 {anchorTerm others}`Nat.plusR 0 n` 替换 {anchorName others}`n` 使目标变得更复杂，而不是更简单：
```anchorError plusR_ind_zero_left_6
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1
```
这可以通过在对 {kw}`rw` 的调用中，在 {anchorName plusR_zero_left_done}`ih` 前放置一个左箭头来补救；这会指示它用等式的左端替换右端：

```anchor plusR_zero_left_done
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]
```
此重写使等式两边完全相同，而 Lean 会自行处理 {kw}`rfl`。
证明完成。

# 策略高尔夫
%%%
tag := "tactic-golf"
file := "Tactic-Golf"
%%%

到目前为止，策略语言还没有展现出它真正的价值。
上面的证明并不比递归函数更短；它只是用一种领域专用语言写成，而不是用完整的 Lean 语言写成。
但是使用策略的证明可以更短、更容易，也更易维护。
正如在高尔夫游戏中分数越低越好，在策略高尔夫游戏中证明越短越好。

{anchorName plusR_zero_left_golf_1}`plusR_zero_left` 的归纳步骤可以使用化简策略 {tactic}`simp` 来证明。
单独使用 {tactic}`simp` 并无帮助：
```anchor plusR_zero_left_golf_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp
```
```anchorError plusR_zero_left_golf_1
`simp` made no progress
```
不过，可以配置 {tactic}`simp` 以使用一组定义。
正如 {kw}`rw` 一样，这些实参以列表形式提供。
要求 {tactic}`simp` 将 {anchorName plusR_zero_left_golf_1}`Nat.plusR` 的定义纳入考虑，会得到一个更简单的目标：
```anchor plusR_zero_left_golf_2
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
```
```anchorError plusR_zero_left_golf_2
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n = Nat.plusR 0 n
```
特别地，现在的目标与归纳假设完全相同。
除了自动证明简单的等式陈述之外，化简器还会自动将形如 {anchorTerm others}`Nat.succ A = Nat.succ B` 的目标替换为 {anchorTerm others}`A = B`。
由于归纳假设 {anchorName plusR_zero_left_golf_3}`ih` 正好具有所需的类型，{kw}`exact` 策略可以指明应当使用它：

```anchor plusR_zero_left_golf_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    exact ih
```

然而，使用 {kw}`exact` 有些脆弱。
重命名归纳假设（这在对证明进行“golfing”时可能发生）会导致此证明停止工作。
如果任意一个假设与当前目标匹配，{kw}`assumption` 策略就会解决当前目标：

```anchor plusR_zero_left_golf_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption
```

这个证明并不比先前使用展开和显式重写的证明更短。
然而，利用 {tactic}`simp` 能够解决多种目标这一事实，一系列变换可以使它短得多。
第一步是去掉 {kw}`induction` 末尾的 {kw}`with`。
对于结构化且可读的证明，{kw}`with` 语法很方便。
若有任何情形遗漏，它会报错，并且它清楚地显示归纳的结构。
但是，缩短证明往往可能需要一种更宽松的方法。

不带 {kw}`with` 使用 {kw}`induction`，只会得到一个包含两个目标的证明状态。
可以使用 {kw}`case` 策略选择其中一个目标，就像在 {kw}`induction`{lit}` ...`{kw}`with` 策略的各个分支中一样。
换言之，下面的证明等价于先前的证明：

```anchor plusR_zero_left_golf_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption
```

在只有一个目标（即 {anchorTerm plusR_zero_left_golf_6a}`k = Nat.plusR 0 k`）的上下文中，{anchorTerm plusR_zero_left_golf_5}`induction k` 策略产生两个目标。
一般而言，一个策略要么因错误而失败，要么接受一个目标并将其转换为零个或多个新目标。
每个新目标都表示仍需证明的内容。
如果结果为零个目标，则该策略成功，并且证明的这一部分已经完成。

{kw}`<;>` 运算符以两个策略作为实参，产生一个新的策略。
{lit}`T1 `{kw}`<;>`{lit}` T2` 将 {lit}`T1` 应用于当前目标，然后在由 {lit}`T1` 创建的_所有_目标中应用 {lit}`T2`。
换言之，{kw}`<;>` 使得一种能够解决多种目标的通用策略可以一次性用于多个新目标。
{tactic}`simp` 就是这样一种通用策略。

由于 {tactic}`simp` 既能完成基例的证明，又能推进归纳步骤的证明，因此将它与 {kw}`induction` 和 {kw}`<;>` 一起使用会缩短证明：
```anchor plusR_zero_left_golf_6a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR]
```
这只产生一个目标，即变换后的归纳步骤：
```anchorError plusR_zero_left_golf_6a
unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝
```
在此目标中运行 {kw}`assumption` 会完成证明：

```anchor plusR_zero_left_golf_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
```
这里无法使用 {kw}`exact`，因为 {lit}`ih` 从未被显式命名。

对于初学者而言，这个证明并不更易读。
然而，专家用户的一种常见模式是用诸如 {tactic}`simp` 这样强大的策略处理若干简单情形，使他们能够将证明文本集中于有趣的情形。
此外，面对证明中涉及的函数和数据类型的小幅改动时，这些证明往往更加稳健。
策略高尔夫这一游戏是培养撰写证明时良好品味与风格的有用组成部分。

# 对其他数据类型进行归纳
%%%
tag := "induction-other-types"
file := "Induction-on-Other-Datatypes"
%%%

数学归纳法通过为 {anchorName others}`Nat.zero` 提供一个基本情形，并为 {anchorName others}`Nat.succ` 提供一个归纳步骤，来证明关于自然数的陈述。
归纳原理也适用于其他数据类型。
没有递归参数的构造子形成基本情形，而带有递归参数的构造子形成归纳步骤。
能够通过归纳进行证明，正是它们被称为_归纳_数据类型的原因。

其中一个例子是对二叉树进行归纳。
对二叉树进行归纳是一种证明技术，其中用两个步骤证明某个陈述对_所有_二叉树成立：
 1. 该陈述被证明对 {anchorName TreeCtors}`BinTree.leaf` 成立。这称为基本情形。
 2. 在假定该陈述对某些任意选取的树 {anchorName TreeCtors}`l` 和 {anchorName TreeCtors}`r` 成立的前提下，证明它对 {anchorTerm TreeCtors}`BinTree.branch l x r` 也成立，其中 {anchorName TreeCtors}`x` 是一个任意选取的新数据点。这称为_归纳步骤_。该陈述对 {anchorName TreeCtors}`l` 和 {anchorName TreeCtors}`r` 成立的假定称为_归纳假设_。

{anchorName BinTree_count}`BinTree.count` 计算一棵树中的分支数：

```anchor BinTree_count
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
```
{ref "leading-dot-notation"}[镜像一棵树] 不会改变其中分支的数量。
这可以通过对树进行归纳来证明。
第一步是陈述该定理并调用 {kw}`induction`：
```anchor mirror_count_0a
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
```
基例陈述的是：对叶子的镜像进行计数，与对该叶子本身进行计数相同：
```anchorError mirror_count_0a
unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
```
归纳步骤允许假设：镜像左右子树不会影响它们的分支计数，并要求证明：对带有这些子树的分支进行镜像也会保持整体分支计数不变：
```anchorError mirror_count_0b
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
```


基本情形为真，因为对 {anchorName mirror_count_1}`leaf` 取镜像会得到 {anchorName mirror_count_1}`leaf`，所以左右两边在定义上相等。
这可以通过使用 {tactic}`simp` 并指示展开 {anchorName mirror_count_1}`BinTree.mirror` 来表达：
```anchor mirror_count_1
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => skip
```
在归纳步骤中，目标中没有任何内容会立即与归纳假设匹配。
使用 {anchorName mirror_count_2}`BinTree.count` 和 {anchorName mirror_count_2}`BinTree.mirror` 的定义进行化简，会揭示这种关系：
```anchor mirror_count_2
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
```
```anchorError mirror_count_2
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.mirror.count + l.mirror.count = 1 + l.count + r.count
```
两个归纳假设都可用于将目标的左侧重写为几乎与右侧相同的形式：
```anchor mirror_count_3
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
```
```anchorError mirror_count_3
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.count + l.count = 1 + l.count + r.count
```

当传入 {anchorTerm mirror_count_4}`+arith` 选项时，{tactic}`simp` 策略可以使用额外的算术恒等式。
这足以证明该目标，从而得到：

```anchor mirror_count_4
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp +arith
```

除了要展开的定义之外，还可以向简化器传入等式证明的名称，使其在简化证明目标时将这些证明用作重写。
{anchorName mirror_count_5}`BinTree.mirror_count` 也可以写作：

```anchor mirror_count_5
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
```
随着证明变得更加复杂，手工列出假设可能会变得繁琐。
此外，手动书写假设名称可能会使得对多个子目标复用证明步骤更加困难。
传给 {tactic}`simp` 或 {kw}`simp +arith` 的参数 {lit}`*` 指示它们在化简或解决目标时使用_所有_假设。
换言之，该证明也可以写成：

```anchor mirror_count_6
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, *]
```
由于两个分支都在使用简化器，该证明可以简化为：

```anchor mirror_count_7
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
```

# {lit}`grind` 策略
%%%
tag := "grind"
file := "The-grind-Tactic"
%%%

{tactic}`grind` 策略可以自动证明许多定理。
与 {tactic}`simp` 类似，它接受一个可选列表，其中包含需要纳入考虑的附加事实或需要展开的函数；不同于 {tactic}`simp`，它会自动将局部假设纳入考虑。
此外，{tactic}`grind` 对特定数学领域推理的支持远强于 {tactic}`simp` 的算术支持。
可以将 {anchorName mirror_count_8}`BinTree.mirror_count` 的证明改写为使用 {tactic}`grind`：
```anchor mirror_count_8
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> grind [BinTree.mirror, BinTree.count]
```

由于本书中的证明相当适中，其中大多数并没有机会让 {tactic}`grind` 展示其全部威力。
不过，在本书后面的一些证明中，它非常方便。

# 练习
%%%
tag := "tactics-induction-proofs-exercises"
file := "Exercises"
%%%

 * 使用 {kw}`induction`{lit}` ...`{kw}`with` 策略证明 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left`。
 * 重写 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left` 的证明，使其在单行中使用 {kw}`<;>`。
 * 通过对列表进行归纳，证明列表追加满足结合律：
   ```anchorTerm ex
   theorem List.append_assoc (xs ys zs : List α) :
       xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
   ```
