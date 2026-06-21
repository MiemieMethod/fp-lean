import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Inequalities"

#doc (Manual) "更多不等式" =>
%%%
tag := "more-inequalities"
file := "More-Inequalities"
%%%

Lean 内置的证明自动化足以检查 {anchorName ArrayMapHelperOk (module:=Examples.ProgramsProofs.Arrays)}`arrayMapHelper` 和 {anchorName ArrayFindHelper (module:=Examples.ProgramsProofs.Arrays)}`findHelper` 会终止。
所需要的只是提供一个表达式，其值随每次递归调用而减小。
然而，Lean 内置的自动化并非魔法，它常常需要一些帮助。

# 归并排序
%%%
tag := "merge-sort"
file := "Merge-Sort"
%%%


一个终止性证明非平凡的函数示例是 {moduleName}`List` 上的归并排序。
归并排序由两个阶段组成：首先，将列表分成两半。
每一半都使用归并排序进行排序，然后使用一个函数将结果合并，该函数把两个已排序列表组合成一个更大的已排序列表。
基本情形为空列表和单元素列表，二者都已被认为是有序的。

要合并两个已排序列表，需要考虑两个基本情形：
 1. 如果某个输入列表为空，则结果为另一个列表。
 2. 如果两个列表均非空，则应比较它们的头部。该函数的结果是两个头部中较小的那个，后接将两个列表的其余项合并所得的结果。

这在任一列表上都不是结构递归的。
递归会终止，是因为每次递归调用都会从两个列表之一中移除一个条目，但它可能是任一列表。
在幕后，Lean 利用这一事实来证明它会终止：

```anchor merge
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
```


拆分列表的一种简单方法，是将输入列表中的每一项交替加入两个输出列表：

```anchor splitList
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)
```
这个拆分函数是结构递归的。

归并排序会检查是否已经到达基本情形。
如果是，则返回输入列表。
如果不是，则拆分输入，并合并对每一半排序所得的结果：
```anchor mergeSortNoTerm
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
```
Lean 的模式匹配编译器能够判断，由测试 {anchorTerm mergeSortNoTerm}`xs.length < 2` 的 {kw}`if` 引入的假设 {anchorName mergeSortNoTerm}`h` 排除了长度超过一个条目的列表，因此不会出现“缺少情形”错误。
然而，尽管这个程序总会终止，它并不是结构递归的，Lean 无法自动发现一个递减度量：
```anchorError mergeSortNoTerm
fail to show termination for
  mergeSort
with errors
failed to infer structural recursion:
Not considering parameter α of mergeSort:
  it is unchanged in the recursive calls
Not considering parameter #2 of mergeSort:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    mergeSort halves.fst


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            xs #1
1) 70:11-31  ?  ?
2) 70:34-54  _  _

#1: xs.length

Please use `termination_by` to specify a decreasing measure.
```
它之所以终止，是因为 {anchorName mergeSortNoTerm}`splitList` 总是返回比其输入更短的列表，至少在应用于包含至少两个元素的列表时如此。
因此，{anchorTerm mergeSortNoTerm}`halves.fst` 和 {anchorTerm mergeSortNoTerm}`halves.snd` 的长度小于 {anchorName mergeSortNoTerm}`xs` 的长度。
这可以使用 {kw}`termination_by` 子句来表达：
```anchor mergeSortGottaProveIt
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
有了这个子句，错误消息会发生变化。
Lean 不再抱怨该函数不是结构递归的，而是指出它无法自动证明 {lit}`(splitList xs).fst.length < xs.length`：
```anchorError mergeSortGottaProveIt
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ (splitList xs).fst.length < xs.length
```

# 拆分列表会使其变短
%%%
tag := "splitting-shortens"
file := "Splitting-a-List-Makes-it-Shorter"
%%%

还需要证明 {lit}`(splitList xs).snd.length < xs.length`。
由于 {anchorName splitList}`splitList` 在向两个列表添加条目之间交替进行，最容易的做法是同时证明这两个陈述，使证明结构能够遵循用于实现 {anchorName splitList}`splitList` 的算法。
换言之，最容易证明的是 {anchorTerm splitList_shorter_bad_ty}`∀(lst : List α), (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length`。

遗憾的是，该陈述是假的。
具体来说，{anchorTerm splitListEmpty}`splitList []` 是 {anchorTerm splitListEmpty}`([], [])`。两个输出列表的长度都是 {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`，这并不小于输入列表的长度 {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`。
类似地，{anchorTerm splitListOne}`splitList ["basalt"]` 求值为 {anchorTerm splitListOne}`(["basalt"], [])`，而 {anchorTerm splitListOne}`["basalt"]` 并不短于 {anchorTerm splitListOne}`["basalt"]`。
然而，{anchorTerm splitListTwo}`splitList ["basalt", "granite"]` 求值为 {anchorTerm splitListTwo}`(["basalt"], ["granite"])`，并且这两个输出列表都短于输入列表。

事实证明，输出列表的长度总是小于等于输入列表的长度，但只有在输入列表至少包含两个条目时，它们才严格更短。
最容易的做法是先证明前一个陈述，然后将其扩展为后一个陈述。
从一个定理陈述开始：
```anchor splitList_shorter_le0
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  skip
```
```anchorError splitList_shorter_le0
unsolved goals
α : Type u_1
lst : List α
⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
```
由于 {anchorName splitList}`splitList` 是在列表上的结构递归，证明应使用归纳法。
{anchorName splitList}`splitList` 中的结构递归与归纳证明完全契合：归纳的基例与递归的基例相匹配，归纳步骤与递归调用相匹配。
{kw}`induction` 策略给出两个目标：
```anchor splitList_shorter_le1a
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => skip
  | cons x xs ih => skip
```
```anchorError splitList_shorter_le1a
unsolved goals
case nil
α : Type u_1
⊢ (splitList []).fst.length ≤ [].length ∧ (splitList []).snd.length ≤ [].length
```
```anchorError splitList_shorter_le1b
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList (x :: xs)).fst.length ≤ (x :: xs).length ∧ (splitList (x :: xs)).snd.length ≤ (x :: xs).length
```

对于 {anchorName splitList_shorter_le2}`nil` 情形的目标，可以通过调用简化器并指示它展开 {anchorName splitList}`splitList` 的定义来证明，因为空列表的长度小于或等于空列表的长度。
类似地，在 {anchorName splitList_shorter_le2}`cons` 情形中用 {anchorName splitList}`splitList` 进行简化，会在目标中的长度周围放置 {anchorName various}`Nat.succ`：
```anchor splitList_shorter_le2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
```
```anchorError splitList_shorter_le2
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```
这是因为对 {anchorName various}`List.length` 的调用会消耗列表 {anchorTerm splitList}`x :: xs` 的头部，并在输入列表的长度以及第一个输出列表的长度中都将其转换为一个 {anchorName various}`Nat.succ`。

在 Lean 中写 {anchorTerm various}`A ∧ B` 是 {anchorTerm various}`And A B` 的简写。
{anchorName And}`And` 是 {anchorTerm And}`Prop` 宇宙中的一个结构类型：

```anchor And
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
换言之，{anchorTerm various}`A ∧ B` 的一个证明由 {anchorName AndUse}`And.intro` 构造子应用于如下内容构成：在 {anchorName And}`left` 字段中给出的 {anchorName AndUse}`A` 的证明，以及在 {anchorName And}`right` 字段中给出的 {anchorName AndUse}`B` 的证明。

{kw}`cases` 策略允许一个证明依次考虑某个数据类型的每个构造子，或某个命题的每种可能证明。
它对应于一个没有递归的 {kw}`match` 表达式。
在结构上使用 {kw}`cases` 会使该结构被拆开，并为结构的每个字段添加一个假设，正如模式匹配表达式提取结构的字段以供程序使用一样。
由于结构只有一个构造子，在结构上使用 {kw}`cases` 不会产生额外目标。

由于 {anchorName splitList_shorter_le3}`ih` 是 {lit}`List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs` 的一个证明，使用 {anchorTerm splitList_shorter_le3}`cases ih` 会得到一个 {lit}`List.length (splitList xs).fst ≤ List.length xs` 的假设以及一个 {lit}`List.length (splitList xs).snd ≤ List.length xs` 的假设：
```anchor splitList_shorter_le3
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
```
```anchorError splitList_shorter_le3
unsolved goals
case cons.intro
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```

由于证明的目标也是一个 {anchorName AndUse}`And`，可以使用 {kw}`constructor` 策略来应用 {anchorName AndUse}`And.intro`，从而为每个参数产生一个目标：
```anchor splitList_shorter_le4
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
```
```anchorError splitList_shorter_le4
unsolved goals
case cons.intro.left
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length

case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

{anchorTerm splitList_shorter_le5}`left` 目标与 {lit}`left✝` 假设完全相同，因此 {kw}`assumption` 策略会处理它：
```anchor splitList_shorter_le5
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
```
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```


{anchorTerm splitList_shorter_le}`right` 目标类似于假设 {lit}`right✝`，区别在于目标只给输入列表的长度添加了一个 {anchorTerm le_succ_of_le}`+ 1`。
现在该证明该不等式成立了。

## 在较大的一侧加一
%%%
tag := "le-succ-of-le"
file := "Adding-One-to-the-Greater-Side"
%%%

证明 {anchorName splitList_shorter_le}`splitList_shorter_le` 所需的不等式是 {anchorTerm le_succ_of_le_statement}`∀(n m : Nat), n ≤ m → n ≤ m + 1`。
传入的假设 {anchorTerm le_succ_of_le_statement}`n ≤ m` 本质上跟踪了 {anchorName le_succ_of_le_statement}`n` 与 {anchorName le_succ_of_le_statement}`m` 在 {anchorName le_succ_of_le_apply}`Nat.le.step` 构造子数量上的差异。
因此，该证明应当在基本情形中添加一个额外的 {anchorName le_succ_of_le_apply}`Nat.le.step`。

一开始，该陈述为：
```anchor le_succ_of_le0
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  skip
```
```anchorError le_succ_of_le0
unsolved goals
n m : Nat
⊢ n ≤ m → n ≤ m + 1
```

第一步是为假设 {anchorTerm le_succ_of_le1}`n ≤ m` 引入一个名称：
```anchor le_succ_of_le1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
```
```anchorError le_succ_of_le1
unsolved goals
n m : Nat
h : n ≤ m
⊢ n ≤ m + 1
```

该证明对这一假设使用归纳法：
```anchor le_succ_of_le2a
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => skip
  | step _ ih => skip
```
在 {anchorName le_succ_of_le2a}`refl` 的情形中，其中 {lit}`n = m`，目标是证明 {lit}`n ≤ n + 1`：
```anchorError le_succ_of_le2a
unsolved goals
case refl
n m : Nat
⊢ n ≤ n + 1
```
在 {anchorName le_succ_of_le2b}`step` 的情形中，目标是在假设 {anchorTerm le_succ_of_le2b}`n ≤ m` 下证明 {anchorTerm le_succ_of_le2b}`n ≤ m + 1`：
```anchorError le_succ_of_le2b
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

对于 {anchorName le_succ_of_le3}`refl` 情形，可以应用 {anchorName le_succ_of_le3}`step` 构造子：
```anchor le_succ_of_le3
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le3
unsolved goals
case refl.a
n m : Nat
⊢ n.le n
```
在 {anchorName Nat.le_ctors}`step` 之后，可以使用 {anchorName Nat.le_ctors}`refl`，这只留下 {anchorName le_succ_of_le4}`step` 的目标：
```anchor le_succ_of_le4
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le4
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

对于递推步骤，应用 {anchorName Nat.le_ctors}`step` 构造子会将目标转换为归纳假设：
```anchor le_succ_of_le5
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => constructor
```
```anchorError le_succ_of_le5
unsolved goals
case step.a
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n.le (m✝ + 1)
```

最终证明如下：

```anchor le_succ_of_le
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step => constructor; assumption
```

为了揭示幕后发生的事情，可以使用 {kw}`apply` 和 {kw}`exact` 策略来精确指明正在应用哪个构造子。
{kw}`apply` 策略通过应用一个返回类型匹配当前目标的函数或构造子来求解当前目标，并为每个未提供的参数创建新目标；而如果需要任何新目标，{kw}`exact` 就会失败：

```anchor le_succ_of_le_apply
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih
```

该证明可以被压缩：

```anchor le_succ_of_le_golf
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  induction h <;> repeat (first | constructor | assumption)
```
在这个简短的策略脚本中，由 {kw}`induction` 引入的两个目标都用 {anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)` 处理。
策略 {lit}`first | T1 | T2 | ... | Tn` 表示按顺序尝试从 {lit}`T1` 到 {lit}`Tn`，并使用第一个成功的策略。
换言之，{anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)` 会尽可能应用构造子，然后尝试使用某个假设来求解目标。

通过使用 {tactic}`grind`，该证明还可以进一步缩短；{tactic}`grind` 包含一个线性算术求解器：

```anchor le_succ_of_le_grind
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  grind
```

最后，该证明可以写成一个递归函数：

```anchor le_succ_of_le_recursive
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)
```

每种证明风格都可能适用于不同情形。
详细的证明脚本适用于初学者可能阅读代码的情形，或证明步骤能提供某种洞见的情形。
简短且高度自动化的证明脚本通常更易维护，因为在定义和数据类型发生小幅变化时，自动化往往既灵活又稳健。
从数学证明的角度看，递归函数通常更难理解，也更难维护；但对于开始接触交互式定理证明的程序员而言，它可以是一座有用的桥梁。

## 完成证明
%%%
tag := "finishing-splitList-shorter-proof"
file := "Finishing-the-Proof"
%%%

既然两个辅助定理都已经证明，{anchorName splitList_shorter_le5}`splitList_shorter_le` 的其余部分将很快完成。
当前证明状态还剩一个目标：
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

将 {anchorName splitList_shorter_le}`Nat.le_succ_of_le` 与假设 {lit}`right✝` 一起使用即可完成证明：

```anchor splitList_shorter_le
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
    case right =>
      apply Nat.le_succ_of_le
      assumption
```

下一步是回到证明归并排序终止性所需的实际定理：只要一个列表至少有两个元素，那么将其拆分所得的两个结果都严格更短。
```anchor splitList_shorter_start
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  skip
```
```anchorError splitList_shorter_start
unsolved goals
α : Type u_1
lst : List α
x✝ : lst.length ≥ 2
⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
```
模式匹配在策略脚本中与在程序中同样有效。
由于 {anchorName splitList_shorter_1}`lst` 至少有两个条目，可以用 {kw}`match` 将它们暴露出来；这也会通过依值模式匹配细化类型：
```anchor splitList_shorter_1
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    skip
```
```anchorError splitList_shorter_1
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList (x :: y :: xs)).fst.length < (x :: y :: xs).length ∧
  (splitList (x :: y :: xs)).snd.length < (x :: y :: xs).length
```
使用 {anchorName splitList}`splitList` 进行化简会移除 {anchorName splitList_shorter_2}`x` 和 {anchorName splitList_shorter_2}`y`，其结果是列表长度的计算值各自多出一个 {anchorTerm le_succ_of_le}`+ 1`：
```anchor splitList_shorter_2
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp [splitList]
```
```anchorError splitList_shorter_2
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length < xs.length + 1 ∧ (splitList xs).snd.length < xs.length + 1
```
将 {anchorTerm splitList_shorter_2b}`simp` 替换为 {anchorTerm splitList_shorter_2b}`simp +arith` 会移除这些 {anchorTerm le_succ_of_le}`+ 1`，因为 {anchorTerm splitList_shorter_2b}`simp +arith` 利用了 {anchorTerm Nat.lt_imp}`n + 1 < m + 1` 蕴含 {anchorTerm Nat.lt_imp}`n < m` 这一事实：
```anchor splitList_shorter_2b
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
```
```anchorError splitList_shorter_2b
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
```
现在这个目标与 {anchorName splitList_shorter}`splitList_shorter_le` 匹配，因此可以用它来结束证明：

```anchor splitList_shorter
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le
```

证明 {anchorName mergeSort}`mergeSort` 终止所需的事实可以从所得的 {anchorName AndUse}`And` 中抽取出来：

```anchor splitList_shorter_sides
theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right
```

## 一个更简单的证明
%%%
tag := "splitList-shorter-le-simpler-proof"
file := "A-Simpler-Proof"
%%%


:::paragraph
不使用通常的归纳，也可以使用函数归纳来证明 {anchorName splitList_shorter_le_funInd1}`splitList_shorter_le`，从而为 {anchorName splitList}`splitList` 的每个分支得到一个情形：
```anchor splitList_shorter_le_funInd1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList with
  | case1 => skip
  | case2 x xs a b splitEq ih => skip
```
第一种情形与 {anchorName splitList}`splitList` 的基例相匹配。
{anchorName splitList}`splitList` 的_两个_应用都已被这个第一分支的结果替换：
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case1
α : Type u_1
⊢ ([], []).fst.length ≤ [].length ∧ ([], []).snd.length ≤ [].length
```
第二个情形匹配 {anchorName splitList}`splitList` 的递归分支。
除了归纳假设之外，{anchorName splitList}`splitList` 中 {anchorTerm splitList}`let` 的值也在一个假设中被跟踪：
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case2
α : Type u_1
x : α
xs a b : List α
splitEq : splitList xs = (a, b)
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (x :: b, a).fst.length ≤ (x :: xs).length ∧ (x :: b, a).snd.length ≤ (x :: xs).length
```
:::

虽然第二种情形看起来有些复杂，但完成证明所需的一切都已经具备。
事实上，{tactic}`grind` 可以立即证明两个目标：
```anchor splitList_shorter_le_funInd2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList <;> grind
```

# 归并排序会终止
%%%
tag := "merge-sort-terminates"
file := "Merge-Sort-Terminates"
%%%

归并排序有两个递归调用，分别对应由 {anchorName splitList}`splitList` 返回的每个子列表。
每个递归调用都需要一个证明，表明传递给它的列表长度短于输入列表的长度。
通常，将终止性证明写成两个步骤会比较方便：首先写下使 Lean 能够验证终止性的命题，然后证明它们。
否则，可能会在证明这些命题上投入大量精力，最后却发现它们并不完全是建立递归调用作用于更小输入所需的命题。

{lit}`sorry` 策略可以证明任何目标，甚至包括假的目标。
它并非旨在用于生产代码或最终证明，但它是预先“勾勒”证明或程序的一种方便方式。
任何使用 {lit}`sorry` 的定义或定理都会被标注一个警告。

使用 {lit}`sorry` 给出的 {anchorName mergeSortSorry}`mergeSort` 终止性论证的初始草图，可以通过把 Lean 无法证明的目标复制到 {kw}`have` 表达式中来写出。
在 Lean 中，{kw}`have` 类似于 {kw}`let`。
使用 {kw}`have` 时，名称是可选的。
通常，{kw}`let` 用于定义指向有意义的值的名称，而 {kw}`have` 用于在局部证明命题；当 Lean 搜索数组查找未越界或函数终止的证据时，可能会发现这些命题。
```anchor mergeSortSorry
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      sorry
    have : halves.snd.length < xs.length := by
      sorry
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
警告位于名称 {anchorName mergeSortSorry}`mergeSort` 上：
```anchorWarning mergeSortSorry
declaration uses 'sorry'
```
由于没有错误，所提出的命题足以确立终止性。

证明从应用辅助定理开始：
```anchor mergeSortNeedsGte
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
两个证明都会失败，因为 {anchorName mergeSortNeedsGte}`splitList_shorter_fst` 和 {anchorName mergeSortNeedsGte}`splitList_shorter_snd` 都需要一个关于 {anchorTerm mergeSortGteStarted}`xs.length ≥ 2` 的证明：
```anchorError mergeSortNeedsGte
unsolved goals
case h
α : Type ?u.80367
inst✝ : Ord α
xs : List α
h : ¬xs.length < 2
halves : List α × List α := ⋯
⊢ xs.length ≥ 2
```
要检查这是否足以完成证明，可使用 {lit}`sorry` 添加它并检查错误：
```anchor mergeSortGteStarted
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by sorry
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
再次，只有一个警告。
```anchorWarning mergeSortGteStarted
declaration uses 'sorry'
```

有一个可用且有希望的假设：{lit}`h : ¬List.length xs < 2`，它来自 {kw}`if`。
显然，如果并非 {anchorTerm mergeSort}`xs.length < 2`，那么 {anchorTerm mergeSort}`xs.length ≥ 2`。
{anchorTerm mergeSort}`grind` 策略可以解决此目标，于是程序现在完成了：

```anchor mergeSort
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      grind
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```

可以在示例上测试该函数：
```anchor mergeSortRocks
#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
```
```anchorInfo mergeSortRocks
["geode", "limestone", "mica", "soapstone"]
```
```anchor mergeSortNumbers
#eval mergeSort [5, 3, 22, 15]
```
```anchorInfo mergeSortNumbers
[3, 5, 15, 22]
```

# 作为迭代减法的除法
%%%
tag := "division-as-iterated-subtraction"
file := "Division-as-Iterated-Subtraction"
%%%

正如乘法是重复加法、幂运算是重复乘法一样，除法也可以理解为重复减法。
{ref "recursive-functions"}[本书对递归函数的最初描述] 给出了一个除法版本：当除数不为零时它会终止，但 Lean 不接受该定义。
证明除法会终止需要使用一个关于不等式的事实。

Lean 无法证明除法的这个定义会终止：
```anchor divTermination (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    1 + div (n - k) k
```

```anchorError divTermination (module := Examples.ProgramsProofs.Div)
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

这是一件好事，因为它确实不会！
当 {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`k` 为 {anchorTerm divTermination (module:=Examples.ProgramsProofs.Div)}`0` 时，{anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`n` 的值不会减小，因此该程序是一个无限循环。

:::paragraph
将该函数改写为接受 {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`k` 不是 {anchorTerm divRecursiveNeedsProof (module:=Examples.ProgramsProofs.Div)}`0` 的证据，可以使 Lean 自动证明终止性：

```anchor divRecursiveNeedsProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
```
:::

{anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`div` 的这个定义会终止，因为在每次递归调用中，第一个参数 {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`n` 都变得更小。
这可以用 {kw}`termination_by` 子句表示：


```anchor divRecursiveWithProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n
```


# 练习
%%%
tag := "inequalities-exercises"
file := "Exercises"
%%%

在不使用 {tactic}`grind` 的情况下证明以下定理：

 * 对于所有自然数 $`n`, $`0 < n + 1`。
 * 对于所有自然数 $`n`，$`0 \leq n`。
 * 对于所有自然数 $`n` 和 $`k`，$`(n + 1) - (k + 1) = n - k`
 * 对于所有自然数 $`n` 和 $`k`，如果 $`k < n`，则 $`n \neq 0`
 * 对于所有自然数 $`n`，$`n - n = 0`
 * 对于所有自然数 $`n` 和 $`k`，如果 $`n + 1 < k`，则 $`n < k`
