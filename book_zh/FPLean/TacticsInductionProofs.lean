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
%%%

# 一个关于证明与用户界面的说明
%%%
tag := "proofs-and-uis"
%%%

本书展现了编写证明的过程，仿佛它们是一次就写就并交付给 Lean 运行似的，接着 Lean 会报错，描述剩余任务的错误信息。
实际上，与 Lean 互动的过程要愉快得多。Lean 在光标移动时提供有关证明的信息，并且有许多互动功能使证明更容易。
请查阅您的 Lean 开发环境的文档以获取更多信息。

本书中的方法侧重于逐步构建证明并显示产生的消息，这展示了 Lean 在编写证明时提供的各种互动反馈，尽管这比专家使用的过程慢得多。
同时，看到不完整的证明逐步趋向完整是一种对证明有益的视角。随着您编写证明技能的提高，Lean 的反馈将不再感觉像错误，
而更像是对您自己思维过程的支持。学习互动方法非常重要。

# 递归和归纳
%%%
tag := "recursion-vs-induction"
%%%

上一章中的函数 {anchorName plusR_succ_left (module := Examples.DependentTypes.Pitfalls)}`plusR_succ_left` 和 {anchorName plusR_zero_left_thm (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left` 可以从两个角度看待。
从一方面看，它们是递归函数，构建了命题的证明，就像其他递归函数可能构建列表、字符串或任何其他数据结构一样。
从另一方面上看，它们也对应于 _数学归纳法 (Mathematical Induction)_ 的证明。

数学归纳是一种证明技术，通过两个步骤证明一个命题对 _所有_ 自然数成立：
 1. 证明该命题对 $`0` 成立。这称为 _基本情况(Base Case)_。
 2. 在假设命题对某个任意选择的数 $`n` 成立的前提下，证明它对 $`n + 1` 成立。这称为 _归纳步骤(Induction Step)_。假设命题对 $`n` 成立的假设称为 _归纳假设(Induction Hypothesis)_。

因为我们不可能对 _每个_ 自然数进行检查，归纳提供了一种手段来编写原则上可以扩展到任何特定自然数的证明。
例如，如果需要对数字 3 进行具体证明，那么可以首先使用基本情况，然后归纳步骤三次，分别证明命题对 0、1、2，最后对 3 成立。
因此，它证明了该命题对所有自然数成立。

# 归纳策略
%%%
tag := "induction-tactic"
%%%

通过递归函数编写归纳证明，使用诸如 {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`congrArg` 之类的辅助函数并不总是能很好地表达证明背后的意图。
虽然递归函数确实具有归纳的结构，但它们应该被视为一种证明的 _编码_。
此外，Lean 的策略系统提供了许多自动构建证明的机会，这是显式编写递归函数时无法实现的。
Lean 提供了一种归纳 _策略_，可以在单个策略块中完成整个归纳证明。
在幕后，Lean 构建了对应于归纳使用的递归函数。

要使用 {kw}`induction` 策略证明 {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left`，首先编写其签名（使用 {kw}`theorem`，因为这确实是一个证明）。
然后，使用 {anchorTerm plusR_ind_zero_left_1}`by induction k` 作为定义的主体：
```anchor plusR_ind_zero_left_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
```
产生的消息表明有两个目标：
```anchorError plusR_ind_zero_left_1
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)
```
策略块是在 Lean 类型检查器处理文件时运行的程序，有点像功能更强大的 C 预处理器宏。
策略生成实际的程序。

在策略语言中，可能有多个目标。每个目标由类型和一些假设组成。
这些类似于使用下划线作为占位符——目标中的类型表示要证明的内容，假设表示在作用域内且可以使用的内容。
在 {lit}`case zero` 的目标中，没有假设，类型是 {anchorTerm others}`Nat.zero = Nat.plusR 0 Nat.zero` ——这是定理陈述，其中 {anchorTerm others}`0` 代替 {anchorName plusR_ind_zero_left_1}`k`。
在 {lit}`case succ` 的目标中，有两个假设，分别命名为 {lit}`n✝` 和 {lit}`n_ih✝`。
在幕后，{anchorTerm plusR_ind_zero_left_1}`induction` 策略创建了一个依赖模式匹配来优化整体类型，{lit}`n✝` 表示模式中 {anchorName others}`Nat.succ` 的参数。
假设 {lit}`n_ih✝` 表示递归调用生成的函数在 {lit}`n✝` 上的结果。
其类型是定理的整体类型，只是用 {lit}`n✝` 代替 {anchorName plusR_ind_zero_left_1}`k`。
{lit}`case succ` 目标的类型是定理陈述的整体，用 {lit}`Nat.succ n✝` 代替 {anchorName plusR_ind_zero_left_1}`k`。

使用 {anchorTerm plusR_ind_zero_left_1}`induction` 策略得到的两个目标对应于数学归纳描述中的基本情况和归纳步骤。
基本情况是 {lit}`case zero`。
在 {lit}`case succ` 中，{lit}`n_ih✝` 对应于归纳假设，而整个 {lit}`case succ` 是归纳步骤。

编写证明的下一步是依次关注两个目标中的每一个。
就像在 {kw}`do` 块中使用 {anchorTerm others}`pure ()` 来表示“什么也不做”一样，策略语言有一个语句 {kw}`skip` 也什么也不做。
当 Lean 的语法需要一个策略时，但尚不清楚应该使用哪个策略时，可以使用 {kw}`skip`。
将 {kw}`with` 添加到 {kw}`induction` 语句的末尾提供了一种类似于模式匹配的语法：
```anchor plusR_ind_zero_left_2a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
```
每个 {kw}`skip` 语句都有一个与之关联的消息。
第一个显示了基本情况：
```anchorError plusR_ind_zero_left_2a
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
```
第二个显示了归纳步骤：
```anchorError plusR_ind_zero_left_2b
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
```
在归纳步骤中，不可访问的带匕首的名称已被提供的名称替换，分别为 {lit}`succ` 后的 {anchorName plusR_ind_zero_left_2a}`n` 和 {anchorName plusR_ind_zero_left_2a}`ih`。

{kw}`induction`{lit}` ...`{kw}`with` 后的 case 不是模式：它们由目标的名称和零个或多个名称组成。
名称用于在目标中引入的假设；如果提供的名称超过目标引入的名称数，则会出现错误：
```anchor plusR_ind_zero_left_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih lots of names => skip
```
```anchorError plusR_ind_zero_left_3
Too many variable names provided at alternative `succ`: 5 provided, but 2 expected
```

关注基本情况，{kw}`rfl` 策略在 {kw}`induction` 策略中与在递归函数中一样有效：
```anchor plusR_ind_zero_left_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih => skip
```
在递归函数版本的证明中，类型注释使得预期类型更容易理解。
在策略语言中，有许多具体的方法可以转换目标，使其更容易解决。
{kw}`unfold` 策略用其定义替换定义的名称：
```anchor plusR_ind_zero_left_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
```
现在，目标中等式的右侧已变为 {anchorTerm others}`Nat.plusR 0 n + 1` 而不是 {anchorTerm others}`Nat.plusR 0 (Nat.succ n)`：
```anchorError plusR_ind_zero_left_5
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1
```

代替使用诸如 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`congrArg` 之类的函数和运算符如 {anchorTerm appendR (module:=Examples.DependentTypes.Pitfalls)}`▸`，存在允许使用等式证明转换证明目标的策略。
最重要的策略之一是 {kw}`rw`，它接受等式证明列表，并在目标中用右侧替换左侧。
这几乎在 {anchorName plusR_ind_zero_left_6}`plusR_zero_left` 中完成了正确的操作：
```anchor plusR_ind_zero_left_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [ih]
```
然而，重写的方向不正确。
将 {anchorName others}`n` 替换为 {anchorTerm others}`Nat.plusR 0 n` 使得目标更复杂而不是更简单：
```anchorError plusR_ind_zero_left_6
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1
```
通过在 {kw}`rw` 调用中的 {anchorName plusR_zero_left_done}`ih` 前加一个左箭头，可以解决这个问题，指示它用左侧替换等式的右侧：

```anchor plusR_zero_left_done
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]
```
这个重写使得等式的两边相同，Lean 会自己处理 {kw}`rfl`。
证毕。

# 策略高尔夫
%%%
tag := "tactic-golf"
%%%

到目前为止，策略语言尚未显示出其真正的价值。
上面的证明并不比递归函数短，只是用特定领域的语言而不是完整的 Lean 语言编写。
但是，用策略编写的证明可以更短、更容易、更易维护。
就像高尔夫比赛中分数越低越好一样，策略高尔夫比赛中的证明越短越好。

{anchorName plusR_zero_left_golf_1}`plusR_zero_left` 的归纳步骤可以使用简化策略 {tactic}`simp` 证明。
单独使用 {tactic}`simp` 并没有帮助：
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
然而，{tactic}`simp` 可以配置为使用一组定义。
就像 {kw}`rw` 一样，这些参数在列表中提供。
要求 {tactic}`simp` 考虑 {anchorName plusR_zero_left_golf_1}`Nat.plusR` 的定义导致一个更简单的目标：
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
特别是，目标现在与归纳假设相同。
除了自动证明简单的等式外，简化器还会自动将目标如 {anchorTerm others}`Nat.succ A = Nat.succ B` 替换为 {anchorTerm others}`A = B`。
由于归纳假设 {anchorName plusR_zero_left_golf_3}`ih` 具有完全正确的类型，{kw}`exact` 策略可以指示它应该被使用：

```anchor plusR_zero_left_golf_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    exact ih
```

然而，使用 {kw}`exact` 有点脆弱。
重命名归纳假设（在“打高尔夫”证明时可能会发生）会导致此证明停止工作。
{kw}`assumption` 策略解决了当前目标，如果 _任何_ 假设与之匹配：

```anchor plusR_zero_left_golf_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption
```

这个证明并不比使用展开和显式重写的先前证明短。
然而，一系列变换可以使它更短，利用 {tactic}`simp` 可以解决许多类型的目标这一事实。
第一步是去掉 {kw}`induction` 末尾的 {kw}`with`。
对于结构化、可读的证明，{kw}`with` 语法是方便的。
如果缺少任何情况，它会抱怨，并且它清楚地显示归纳的结构。
但是缩短证明通常需要更宽松的方法。

使用不带 {kw}`with` 的 {kw}`induction` 仅会产生两个目标。
{kw}`case` 策略可以像在 {kw}`induction`{lit}` ...`{kw}`with` 策略的分支中一样选择其中一个目标。
换句话说，以下证明等同于前一个证明：

```anchor plusR_zero_left_golf_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption
```

在具有单个目标的上下文中（即 {anchorTerm plusR_zero_left_golf_6a}`k = Nat.plusR 0 k`），{anchorTerm plusR_zero_left_golf_5}`induction k` 策略产生两个目标。
通常，策略要么失败并产生错误，要么接受一个目标并将其转换为零个或多个新目标。
每个新目标表示剩下要证明的内容。
如果结果是零个目标，则策略成功，该部分证明完成。

{kw}`<;>` 运算符接受两个策略作为参数，生成一个新策略。
{lit}`T1 `{kw}`<;>`{lit}` T2` 将 {lit}`T1` 应用于当前目标，然后在 {lit}`T1` 创建的所有目标中应用 {lit}`T2`。
换句话说，{kw}`<;>` 允许通用策略一次性用于多个新目标。
一个这样的通用策略是 {tactic}`simp`。

由于 {tactic}`simp` 既能完成基础情形的证明，又能推进归纳步骤的证明，因此将它与 {kw}`induction` 和 {kw}`<;>` 一起使用可以缩短证明：
```anchor plusR_zero_left_golf_6a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR]
```
这仅产生一个目标，即转换后的归纳步骤：
```anchorError plusR_zero_left_golf_6a
unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝
```
在这个目标中运行 {kw}`assumption` 完成了证明：

```anchor plusR_zero_left_golf_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
```
在这里，{kw}`exact` 是不可能的，因为 {lit}`ih` 从未被显式命名。

对于初学者来说，这个证明并不容易阅读。
然而，专家用户的常见模式是使用像 {tactic}`simp` 这样的强大策略处理一些简单情况，使他们可以将证明的文本集中在有趣的情况下。
此外，这些证明在面对函数和数据类型的小变化时往往更稳健。
策略高尔夫游戏是培养编写证明时的良好品味和风格的有用部分。

# 其他数据类型的归纳
%%%
tag := "induction-other-types"
%%%

数学归纳通过为 {anchorName others}`Nat.zero` 提供基本情况和为 {anchorName others}`Nat.succ` 提供归纳步骤来证明自然数的命题。
归纳原则对于其他数据类型也是有效的。
没有递归参数的构造函数形成基本情况，而具有递归参数的构造函数形成归纳步骤。
进行归纳证明的能力是它们被称为 _归纳_ 数据类型的原因。

这方面的一个例子是对二叉树的归纳。
对二叉树进行归纳是一种证明技术，通过两个步骤证明一个命题对 _所有_ 二叉树成立：
 1. 证明该命题对 {anchorName TreeCtors}`BinTree.leaf` 成立。这称为基本情况。
 2. 在假设该命题对某些任意选择的树 {anchorName TreeCtors}`l` 和 {anchorName TreeCtors}`r` 成立的前提下，证明它对 {anchorTerm TreeCtors}`BinTree.branch l x r` 成立，其中 {anchorName TreeCtors}`x` 是任意选择的新数据点。这称为 _归纳步骤_。假设该命题对 {anchorName TreeCtors}`l` 和 {anchorName TreeCtors}`r` 成立的假设称为 _归纳假设_。

{anchorName BinTree_count}`BinTree.count` 计算树中分支的数量：

```anchor BinTree_count
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
```
{ref "leading-dot-notation"}[镜像树]不会改变树中的分支数量。
可以通过对树进行归纳证明这一点。
第一步是声明定理并调用 {kw}`induction`：
```anchor mirror_count_0a
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
```
基本情况表明，计算镜像叶子的数量与计算叶子相同：
```anchorError mirror_count_0a
unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
```
归纳步骤允许假设镜像左右子树不会影响其分支计数，并要求证明镜像具有这些子树的分支也保留整体分支计数：
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


基本情况成立，因为镜像 {anchorName mirror_count_1}`leaf` 结果为 {anchorName mirror_count_1}`leaf`，因此左右两边定义上相等。
这可以通过使用带有展开 {anchorName mirror_count_1}`BinTree.mirror` 指令的 {tactic}`simp` 表达：
```anchor mirror_count_1
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => skip
```
在归纳步骤中，目标中没有任何东西与归纳假设立即匹配。
使用 {anchorName mirror_count_2}`BinTree.count` 和 {anchorName mirror_count_2}`BinTree.mirror` 的定义简化显示了关系：
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
可以使用两个归纳假设重写目标的左侧，使其与右侧几乎相同：
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

{tactic}`simp` 策略在传递 {anchorTerm mirror_count_4}`+arith` 选项时可以使用额外的算术等式。
这足以证明此目标，从而得到：

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

除了要展开的定义外，简化器还可以传递等式证明的名称以在简化证明目标时用作重写。
{anchorName mirror_count_5}`BinTree.mirror_count` 还可以这样写：

```anchor mirror_count_5
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
```
随着证明变得更加复杂，手动列出假设会变得繁琐。
此外，手动编写假设名称可能会使重复使用证明步骤来处理多个子目标变得更加困难。
{tactic}`simp` 或 {kw}`simp +arith` 的参数 {lit}`*` 指示它们在简化或解决目标时使用 _所有_ 假设。
换句话说，证明也可以这样写：

```anchor mirror_count_6
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, *]
```
因为两个分支都在使用简化器，证明可以简化为：

```anchor mirror_count_7
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
```

# {lit}`grind` 策略
%%%
tag := "grind"
%%%

{tactic}`grind` 策略可以自动证明许多定理。
像 {tactic}`simp` 一样，它接受一个可选的额外事实列表以供考虑或要展开的函数；与 {tactic}`simp` 不同，它会自动考虑局部假设。
此外，{tactic}`grind` 对特定数学领域的推理支持远强于 {tactic}`simp` 的算术支持。
{anchorName mirror_count_8}`BinTree.mirror_count` 的证明可以重写为使用 {tactic}`grind`：
```anchor mirror_count_8
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> grind [BinTree.mirror, BinTree.count]
```

因为本书中的证明相当温和，大多数证明都没有提供让 {tactic}`grind` 展示其全部能力的机会。
然而，在本书后面的一些证明中，它非常方便。

# 练习
%%%
tag := "tactics-induction-proofs-exercises"
%%%

 * 使用 {kw}`induction`{lit}` ...`{kw}`with` 策略证明 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left`。
 * 重写 {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left` 的证明，使用 {kw}`<;>` 并写成一行。
 * 使用列表归纳证明列表追加是结合的：
   ```anchorTerm ex
   theorem List.append_assoc (xs ys zs : List α) :
       xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
   ```
