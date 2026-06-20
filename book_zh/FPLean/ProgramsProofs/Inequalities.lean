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
%%%

Lean 的内置证明自动化足以检查 {anchorName ArrayMapHelperOk (module:=Examples.ProgramsProofs.Arrays)}`arrayMapHelper` 和 {anchorName ArrayFindHelper (module:=Examples.ProgramsProofs.Arrays)}`findHelper` 是否停机。
所需要做的就是提供一个值随着每次递归调用而减小的表达式。
但是，Lean 的内置自动化不是万能的，它通常需要一些帮助。

# 归并排序
%%%
tag := "merge-sort"
%%%


一个停机证明非平凡的函数示例是 {moduleName}`List` 上的归并排序。归并排序包含两个阶段：
首先，将列表分成两半。使用归并排序对每一半进行排序，
然后使用一个将两个已排序列表合并为一个更大的已排序列表的函数合并结果。
基本情况是空列表和单元素列表，它们都被认为已经排序。

要合并两个已排序列表，需要考虑两个基本情况：

这在任何列表上都不是结构化递归。递归停机是因为在每次递归调用中都会从两个列表中的一个中删除一个项，
但它可能是任何一个列表。Lean 在幕后使用这个事实来证明它停机：

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


分割列表的一个简单方法是将输入列表中的每个项添加到两个交替的输出列表中：

```anchor splitList
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)
```
这个分割函数是结构化递归的。

归并排序检查是否已达到基本情况。如果是，则返回输入列表。
如果不是，则分割输入，并合并对每一半排序的结果：
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
Lean 的模式匹配编译器能够判断由测试 {anchorTerm mergeSortNoTerm}`xs.length < 2` 的 {kw}`if` 引入的前提 {anchorName mergeSortNoTerm}`h`
排除了长度超过一个条目的列表，因此没有“缺少情况”的错误。
然而，即使此程序总是停机，它也不是结构化递归的，并且 Lean 无法自动发现递减度量：
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
它能停机的原因是 {anchorName mergeSortNoTerm}`splitList` 总是返回比其输入更短的列表，至少在应用于包含至少两个元素的列表时是这样。
因此，{anchorTerm mergeSortNoTerm}`halves.fst` 和 {anchorTerm mergeSortNoTerm}`halves.snd` 的长度小于 {anchorName mergeSortNoTerm}`xs` 的长度。
这可以使用 {kw}`termination_by` 子句来表示：
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
有了这个子句，错误信息就变了。
Lean 不会抱怨函数不是结构化递归的，而是指出它无法自动证明 {lit}`(splitList xs).fst.length < xs.length`：
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

# 分割列表使其变短
%%%
tag := "splitting-shortens"
%%%

还需要证明 {lit}`(splitList xs).snd.length < xs.length`。
由于 {anchorName splitList}`splitList` 在向两个列表添加条目之间交替进行，因此最简单的方法是同时证明这两个语句，这样证明的结构就可以遵循用于实现 {anchorName splitList}`splitList` 的算法。
换句话说，最简单的方法是证明 {anchorTerm splitList_shorter_bad_ty}`∀(lst : List α), (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length`。

不幸的是，这个陈述是错误的。
特别是，{anchorTerm splitListEmpty}`splitList []` 是 {anchorTerm splitListEmpty}`([], [])`。两个输出列表的长度都是 {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`，这并不小于输入列表的长度 {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`。
类似地，{anchorTerm splitListOne}`splitList ["basalt"]` 求值为 {anchorTerm splitListOne}`(["basalt"], [])`，而 {anchorTerm splitListOne}`["basalt"]` 并不比 {anchorTerm splitListOne}`["basalt"]` 短。
然而，{anchorTerm splitListTwo}`splitList ["basalt", "granite"]` 求值为 {anchorTerm splitListTwo}`(["basalt"], ["granite"])`，这两个输出列表都比输入列表短。

事实证明，输出列表的长度始终小于或等于输入列表的长度，但仅当输入列表至少包含两个条目时，它们才严格更短。
事实证明，最容易证明前一个陈述，然后将其扩展到后一个陈述。
从定理的陈述开始：
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
由于 {anchorName splitList}`splitList` 在列表上是结构化递归的，因此证明应使用归纳法。
{anchorName splitList}`splitList` 中的结构化递归非常适合归纳证明：归纳法的基本情况与递归的基本情况匹配，
归纳步骤与递归调用匹配。{kw}`induction` 策略给出了两个目标：
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

可以通过调用简化器并指示它展开 {anchorName splitList}`splitList` 的定义来证明 {anchorName splitList_shorter_le2}`nil` 情况的目标，因为空列表的长度小于或等于空列表的长度。
类似地，在 {anchorName splitList_shorter_le2}`cons` 情况下使用 {anchorName splitList}`splitList`
简化会在目标中的长度周围放置 {anchorName various}`Nat.succ`：
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
这是因为对 {anchorName various}`List.length` 的调用消耗了列表 {anchorTerm splitList}`x :: xs` 的头部，将其转换为 {anchorName various}`Nat.succ`，既在输入列表的长度中，也在第一个输出列表的长度中。

在 Lean 中编写 {anchorTerm various}`A ∧ B` 是 {anchorTerm various}`And A B` 的缩写。
{anchorName And}`And` 是 {anchorTerm And}`Prop` 宇宙中的一个结构体类型：

```anchor And
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
换句话说，{anchorTerm various}`A ∧ B` 的证明包括应用于 {anchorName And}`left` 字段中 {anchorName AndUse}`A` 的证明和应用于 {anchorName And}`right` 字段中 {anchorName AndUse}`B` 的证明的 {anchorName AndUse}`And.intro` 构造子。

{kw}`cases` 策略允许证明依次考虑数据类型的每个构造子或命题的每个潜在证明。
它对应于没有递归的 {kw}`match` 表达式。
对结构体使用 {kw}`cases` 会导致结构体被分解，并为结构体的每个字段添加一个假设，就像模式匹配表达式提取结构体的字段以用于程序中一样。
由于结构体只有一个构造子，因此对结构体使用 {kw}`cases` 不会产生额外的目标。

由于 {anchorName splitList_shorter_le3}`ih` 是 {lit}`List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs` 的一个证明，
使用 {anchorTerm splitList_shorter_le3}`cases ih` 会产生一个 {lit}`List.length (splitList xs).fst ≤ List.length xs` 的假设和一个 {lit}`List.length (splitList xs).snd ≤ List.length xs` 的假设：
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

由于证明的目标也是一个 {anchorName AndUse}`And`，因此可以使用 {kw}`constructor` 策略应用 {anchorName AndUse}`And.intro`，
从而为每个参数生成一个目标：
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

{anchorTerm splitList_shorter_le5}`left` 目标与 {lit}`left✝` 假设非常相似，所以 {kw}`assumption` 策略将其分派：
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


同样，{anchorTerm splitList_shorter_le}`right` 目标类似于 {lit}`right✝` 假设，除了目标仅将 {anchorTerm le_succ_of_le}`+ 1` 添加到输入列表的长度。
现在是时候证明不等式成立了。

## 在较大的一侧加一
%%%
tag := "le-succ-of-le"
%%%

证明 {anchorName splitList_shorter_le}`splitList_shorter_le` 所需的不等式是 {anchorTerm le_succ_of_le_statement}`∀(n m : Nat), n ≤ m → n ≤ m + 1`。
传入的假设 {anchorTerm le_succ_of_le_statement}`n ≤ m` 本质上是在 {anchorName le_succ_of_le_apply}`Nat.le.step` 构造子的数量上跟踪 {anchorName le_succ_of_le_statement}`n` 和 {anchorName le_succ_of_le_statement}`m` 之间的差异。
因此，证明应该在基本情况中添加一个额外的 {anchorName le_succ_of_le_apply}`Nat.le.step`。

开始时，该陈述如下：
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

证明是通过对该假设进行归纳来进行的：
```anchor le_succ_of_le2a
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => skip
  | step _ ih => skip
```
在 {anchorName le_succ_of_le2a}`refl` 的情况下，其中 {lit}`n = m`，目标是证明 {lit}`n ≤ n + 1`：
```anchorError le_succ_of_le2a
unsolved goals
case refl
n m : Nat
⊢ n ≤ n + 1
```
在 {anchorName le_succ_of_le2b}`step` 的情况下，目标是在假设 {anchorTerm le_succ_of_le2b}`n ≤ m` 下证明 {anchorTerm le_succ_of_le2b}`n ≤ m + 1`：
```anchorError le_succ_of_le2b
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

对于 {anchorName le_succ_of_le3}`refl` 情况，可以应用 {anchorName le_succ_of_le3}`step` 构造子：
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
在 {anchorName Nat.le_ctors}`step` 之后，可以使用 {anchorName Nat.le_ctors}`refl`，这只留下了 {anchorName le_succ_of_le4}`step` 的目标：
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

对于 step，应用 {anchorName Nat.le_ctors}`step` 构造子将目标转换为归纳假设：
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

为了揭示幕后发生的事情，{kw}`apply` 和 {kw}`exact` 策略可用于准确指示正在应用哪个构造子。
{kw}`apply` 策略通过应用一个返回类型匹配的函数或构造子来解决当前目标，为每个未提供的参数创建新的目标，而如果需要任何新目标，{kw}`exact` 就会失败：

```anchor le_succ_of_le_apply
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih
```

证明可以简化：

```anchor le_succ_of_le_golf
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  induction h <;> repeat (first | constructor | assumption)
```
在这个简短的策略脚本中，由 {kw}`induction` 引入的两个目标都使用 {anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)` 来解决。
策略 {lit}`first | T1 | T2 | ... | Tn` 表示按顺序尝试 {lit}`T1` 到 {lit}`Tn`，然后使用第一个成功的策略。
换句话说，{anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)` 会尽可能地应用构造子，然后尝试使用假设来解决目标。

通过使用 {tactic}`grind`，证明可以进一步缩短，它包含一个线性算术求解器：

```anchor le_succ_of_le_grind
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  grind
```

最后，证明可以写成一个递归函数：

```anchor le_succ_of_le_recursive
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)
```

每种证明风格都适用于不同的情况。
详细的证明脚本在初学者阅读代码或证明步骤提供某种见解的情况下很有用。
简短、高度自动化的证明脚本通常更容易维护，因为自动化通常在面对定义和数据类型的细微更改时既灵活又健壮。
递归函数通常从数学证明的角度来看更难理解，也更难维护，但对于开始使用交互式定理证明的程序员来说，它可能是一个有用的桥梁。

## 完成证明
%%%
tag := "finishing-splitList-shorter-proof"
%%%

现在已经证明了两个辅助定理，{anchorName splitList_shorter_le5}`splitList_shorter_le` 的其余部分将很快完成。
当前的证明状态还剩下一个目标：
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

使用 {anchorName splitList_shorter_le}`Nat.le_succ_of_le` 以及 {lit}`right✝` 假设完成了证明：

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

下一步是返回到证明归并排序停机所需的实际定理：只要一个列表至少有两个条目，则分割它的两个结果都严格短于它。
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
模式匹配在策略脚本中与在程序中一样有效。
因为 {anchorName splitList_shorter_1}`lst` 至少有两个条目，所以它们可以用 {kw}`match` 暴露出来，它还通过依值模式匹配来细化类型：
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
使用 {anchorName splitList}`splitList` 简化会删除 {anchorName splitList_shorter_2}`x` 和 {anchorName splitList_shorter_2}`y`，导致列表的计算长度每个都获得 {anchorTerm le_succ_of_le}`+ 1`：
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
用 {anchorTerm splitList_shorter_2b}`simp +arith` 替换 {anchorTerm splitList_shorter_2b}`simp` 会删除这些 {anchorTerm le_succ_of_le}`+ 1`，因为 {anchorTerm splitList_shorter_2b}`simp +arith` 利用了 {anchorTerm Nat.lt_imp}`n + 1 < m + 1` 意味着 {anchorTerm Nat.lt_imp}`n < m` 的事实：
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
此目标现在匹配 {anchorName splitList_shorter}`splitList_shorter_le`，可用于结束证明：

```anchor splitList_shorter
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le
```

证明 {anchorName mergeSort}`mergeSort` 停机所需的事实可以从结果 {anchorName AndUse}`And` 中提取出来：

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
%%%


:::paragraph
除了使用普通归纳法，{anchorName splitList_shorter_le_funInd1}`splitList_shorter_le` 还可以使用函数归纳法来证明，从而为 {anchorName splitList}`splitList` 的每个分支产生一个情况：
```anchor splitList_shorter_le_funInd1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList with
  | case1 => skip
  | case2 x xs a b splitEq ih => skip
```
第一种情况匹配 {anchorName splitList}`splitList` 的基本情况。
{anchorName splitList}`splitList` 的 _两个_ 应用都被替换为第一个分支的结果：
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case1
α : Type u_1
⊢ ([], []).fst.length ≤ [].length ∧ ([], []).snd.length ≤ [].length
```
第二种情况匹配 {anchorName splitList}`splitList` 的递归分支。
除了归纳假设之外，{anchorName splitList}`splitList` 中 {anchorTerm splitList}`let` 的值也在假设中被跟踪：
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

虽然第二种情况看起来有点复杂，但完成证明所需的一切都已存在。
实际上，{tactic}`grind` 可以立即证明这两个目标：
```anchor splitList_shorter_le_funInd2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList <;> grind
```

# 归并排序停机证明
%%%
tag := "merge-sort-terminates"
%%%

归并排序有两个递归调用，一个用于 {anchorName splitList}`splitList` 返回的每个子列表。
每个递归调用都需要证明传递给它的列表的长度短于输入列表的长度。
通常分两步编写停机证明会更方便：首先，写下允许 Lean 验证停机的命题，然后证明它们。
否则，可能会投入大量精力来证明命题，却发现它们并不是所需的在更小的输入上建立递归调用的内容。

{lit}`sorry` 策略可以证明任何目标，即使是错误的目标。
它不适用于生产代码或最终证明，但它是一种便捷的方法，可以提前“勾勒出”证明或程序。
任何使用 {lit}`sorry` 的定义或定理都会附有警告。

使用 {lit}`sorry` 的 {anchorName mergeSortSorry}`mergeSort` 停机论证的初始草图可以通过将 Lean 无法证明的目标复制到 {kw}`have` 表达式中来编写。
在 Lean 中，{kw}`have` 类似于 {kw}`let`。
当使用 {kw}`have` 时，名称是可选的。
通常，{kw}`let` 用于定义引用关键值的名称，而 {kw}`have` 用于局部证明命题，当 Lean 在寻找“数组查找是否在范围内”或“函数是否停机”的证据时，可以找到这些命题。
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
因为没有错误，所以建议的命题足以建立停机证明。

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
两个证明都失败了，因为 {anchorName mergeSortNeedsGte}`splitList_shorter_fst` 和 {anchorName mergeSortNeedsGte}`splitList_shorter_snd` 都需要证明 {anchorTerm mergeSortGteStarted}`xs.length ≥ 2`：
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
要检查这是否足以完成证明，请使用 {lit}`sorry` 添加它并检查错误：
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
同样，只会有一个警告。
```anchorWarning mergeSortGteStarted
declaration uses 'sorry'
```

有一个有希望的假设可用：{lit}`h : ¬List.length xs < 2`，它来自 {kw}`if`。
显然，如果不是 {anchorTerm mergeSort}`xs.length < 2`，那么 {anchorTerm mergeSort}`xs.length ≥ 2`。
{anchorTerm mergeSort}`grind` 策略解决了这个目标，程序现在已完成：

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

该函数可以在示例上进行测试：
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

# 用减法迭代表示除法
%%%
tag := "division-as-iterated-subtraction"
%%%

正如乘法是迭代的加法，指数是迭代的乘法，除法可以理解为迭代的减法。
{ref "recursive-functions"}[本书中对递归函数的第一个描述]给出了除法的一个版本，当除数不为零时停机，但 Lean 并不接受。
证明除法终止需要使用关于不等式的事实。

Lean 无法证明除法的这个定义会停机：
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

这是一件好事，因为它确实不会停机！
当 {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`k` 为 {anchorTerm divTermination (module:=Examples.ProgramsProofs.Div)}`0` 时，{anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`n` 的值不会减小，因此程序是一个无限循环。

:::paragraph
重写该函数以获取 {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`k` 不为 {anchorTerm divRecursiveNeedsProof (module:=Examples.ProgramsProofs.Div)}`0` 的证据，允许 Lean 自动证明停机：

```anchor divRecursiveNeedsProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
```
:::

{anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`div` 的这个定义会停机，因为第一个参数 {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`n` 在每次递归调用时都更小。
这可以使用 {kw}`termination_by` 子句来表示：


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
%%%

在不使用 {tactic}`grind` 的情况下证明以下定理：

 * 对于所有自然数 $`n`，$`0 < n + 1`。
 * 对于所有自然数 $`n`，$`0 \leq n`。
 * 对于所有自然数 $`n` 和 $`k`，$`(n + 1) - (k + 1) = n - k`。
 * 对于所有自然数 $`n` 和 $`k`，如果 $`k < n` 则 $`n \neq 0`。
 * 对于所有自然数 $`n`，$`n - n = 0`。
 * 对于所有自然数 $`n` 和 $`k`，如果 $`n + 1 < k` 则 $`n < k`。
