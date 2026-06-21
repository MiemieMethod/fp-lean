import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "插入排序与数组变更" =>
%%%
tag := "insertion-sort-mutation"
file := "Insertion-Sort-and-Array-Mutation"
%%%

虽然插入排序对于排序算法而言并不具有最优的最坏情况时间复杂度，但它仍然具有若干有用的性质：
 * 它实现和理解起来都简单直接
 * 它是一种原地算法，运行时不需要额外空间
 * 它是稳定排序
 * 当输入已经几乎有序时，它很快

由于 Lean 管理内存的方式，原地算法在 Lean 中特别有用。
在某些情况下，通常会复制数组的操作可以被优化为变更。
这包括交换数组中的元素。

大多数带有自动内存管理的语言和运行时系统，包括 JavaScript、JVM 和 .NET，都使用追踪式垃圾回收。
当需要回收内存时，系统从若干_根_（例如调用栈和全局值）开始，然后通过递归追踪指针来确定哪些值可以被到达。
任何无法被到达的值都会被释放，从而腾出内存。

引用计数是追踪式垃圾回收的一种替代方案，许多语言都使用它，包括 Python、Swift 和 Lean。
在采用引用计数的系统中，内存中的每个对象都有一个字段，用来跟踪有多少个对它的引用。
当建立一个新的引用时，计数器递增。
当一个引用不复存在时，计数器递减。
当计数器达到零时，该对象会立即被释放。

与追踪式垃圾回收器相比，引用计数有一个主要缺点：循环引用可能导致内存泄漏。
如果对象 $`A` 引用对象 $`B`，并且对象 $`B` 引用对象 $`A`，那么即使程序中没有其他任何东西引用 $`A` 或 $`B`，它们也永远不会被释放。
循环引用要么源于不受控制的递归，要么源于可变引用。
由于 Lean 二者都不支持，因此不可能构造循环引用。

引用计数意味着 Lean 运行时系统中用于分配和释放数据结构的原语可以检查某个引用计数是否即将降为零，并复用现有对象，而不是分配新对象。
在处理大型数组时，这一点尤其重要。


Lean 数组的插入排序实现应满足以下准则：
 1. Lean 应当在没有 {kw}`partial` 标注的情况下接受该函数
 2. 如果传入的是一个没有其他引用指向它的数组，则应当就地修改该数组，而不是分配一个新数组

第一个判据很容易检查：如果 Lean 接受该定义，那么它就得到了满足。
然而，第二个判据需要一种测试它的方法。
Lean 提供了一个名为 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 的内置函数，其签名如下：
```anchor dbgTraceIfSharedSig
#check dbgTraceIfShared
```
```anchorInfo dbgTraceIfSharedSig
dbgTraceIfShared.{u} {α : Type u} (s : String) (a : α) : α
```
它以一个字符串和一个值作为参数，并且如果该值有多于一个引用，就向标准错误打印一条使用该字符串的消息，然后返回该值。
严格来说，这不是一个纯函数。
然而，它的预期用途仅限于开发期间检查某个函数事实上是否能够复用内存，而不是分配和复制。

学习使用 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 时，重要的是要知道 {kw}`#eval` 会报告比编译后代码中多得多的值被共享。
这可能令人困惑。
重要的是使用 {lit}`lake` 构建可执行文件，而不是在编辑器中实验。

插入排序由两个循环组成。
外层循环将一个指针从左到右移动，穿过待排序的数组。
每次迭代之后，数组中位于指针左侧的区域是已排序的，而右侧的区域可能尚未排序。
内层循环取出指针所指向的元素，并将其向左移动，直到找到适当的位置并恢复循环不变式。
换言之，每次迭代都将数组的下一个元素插入到已排序区域中的适当位置。

# 内层循环
%%%
tag := "inner-insertion-sort-loop"
file := "The-Inner-Loop"
%%%

插入排序的内层循环可以实现为一个尾递归函数，该函数以数组和正在插入的元素的索引作为参数。
正在插入的元素会反复与其左侧的元素交换，直到左侧的元素更小，或者到达数组的开头为止。
内层循环在用于索引数组的 {anchorName insertSorted}`Fin` 内部的 {anchorName insertionSortLoop}`Nat` 上是结构递归的：

```anchor insertSorted
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      grind
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by simp [*]⟩
```
如果索引 {anchorName insertSorted}`i` 是 {anchorTerm insertSorted}`0`，那么正在插入到已排序区域中的元素已经到达该区域的开头，并且是最小的。
如果该索引是 {anchorTerm insertSorted}`i' + 1`，那么应当将 {anchorName insertSorted}`i'` 处的元素与 {anchorName insertSorted}`i` 处的元素进行比较。
注意，虽然 {anchorName insertSorted}`i` 是一个 {anchorTerm insertSorted}`Fin arr.size`，但 {anchorName insertSorted}`i'` 只是一个 {anchorName insertionSortLoop}`Nat`，因为它来自 {anchorName insertSorted}`i` 的 {anchorName names}`val` 字段。
尽管如此，用于检查数组索引记法的证明自动化包含一个线性整数算术求解器，因此 {anchorName insertSorted}`i'` 可以自动用作索引。

查找并比较这两个元素。
如果左侧元素小于或等于正在插入的元素，则循环结束，并且不变式已经恢复。
如果左侧元素大于正在插入的元素，则交换这些元素，并重新开始内层循环。
{anchorName names}`Array.swap` 将它的两个索引都作为 {anchorName names}`Nat`，在幕后使用与数组索引相同的策略来确保它们在界内。

尽管如此，递归调用所使用的 {anchorName names}`Fin` 需要一个证明，说明 {anchorName insertSorted}`i'` 对交换两个元素后的结果而言在边界内。
{anchorTerm insertSorted}`simp` 策略的数据库包含这样一个事实：交换数组中的两个元素不会改变其大小；而 {anchorTerm insertSorted}`[*]` 参数指示它额外使用由 {kw}`have` 引入的假设。
省略带有 {anchorTerm insertSorted}`i' < arr.size` 的证明的 {kw}`have` 表达式，会显示如下目标：
```anchorError insertSortedNoProof
unsolved goals
α : Type ?u.7
inst✝ : Ord α
arr : Array α
i : Fin arr.size
i' : Nat
isLt✝ : i' + 1 < arr.size
⊢ i' < arr.size
```



# 外层循环
%%%
tag := "outer-insertion-sort-loop"
file := "The-Outer-Loop"
%%%

插入排序的外层循环将指针从左向右移动，在每次迭代中调用 {anchorName insertionSortLoop}`insertSorted`，以将指针处的元素插入到数组中的正确位置。
该循环的基本形式类似于 {anchorTerm etc}`Array.map` 的实现：
```anchor insertionSortLoopTermination
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
发生错误是因为不存在一个在每次递归调用中都会减小的参数：
```anchorError insertionSortLoopTermination
fail to show termination for
  insertionSortLoop
with errors
failed to infer structural recursion:
Not considering parameter α of insertionSortLoop:
  it is unchanged in the recursive calls
Not considering parameter #2 of insertionSortLoop:
  it is unchanged in the recursive calls
Cannot use parameter arr:
  the type Array α does not have a `.brecOn` recursor
Cannot use parameter i:
  failed to eliminate recursive application
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            arr i #1
1) 569:4-55   ? ?  ?

#1: arr.size - i

Please use `termination_by` to specify a decreasing measure.
```
虽然 Lean 可以证明一个在每次迭代中朝着常量界递增的 {anchorName insertionSortLoop}`Nat` 会导致函数终止，但此函数没有常量界，因为在每次迭代中，数组都会被替换为调用 {anchorName insertionSortLoop}`insertSorted` 的结果。

在构造终止性证明之前，可以方便地用 {kw}`partial` 修饰符测试该定义，以确保它返回预期答案：

```anchor partialInsertionSortLoop
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
```anchor insertionSortPartialOne
#eval insertionSortLoop #[5, 17, 3, 8] 0
```
```anchorInfo insertionSortPartialOne
#[3, 5, 8, 17]
```
```anchor insertionSortPartialTwo
#eval insertionSortLoop #["metamorphic", "igneous", "sedimentary"] 0
```
```anchorInfo insertionSortPartialTwo
#["igneous", "metamorphic", "sedimentary"]
```

## 终止性
%%%
tag := "insertionSortLoop-termination"
file := "Termination"
%%%

同样，该函数会终止，因为正在处理的索引与数组大小之间的差在每次递归调用中都会减小。
然而，这一次 Lean 不接受该 {kw}`termination_by`：
```anchor insertionSortLoopProof1
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorError insertionSortLoopProof1
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h : i < arr.size
⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
```
问题在于，Lean 无法知道 {anchorName insertionSortLoop}`insertSorted` 返回的数组与传给它的数组大小相同。
为了证明 {anchorName insertionSortLoop}`insertionSortLoop` 会终止，必须首先证明 {anchorName insertionSortLoop}`insertSorted` 不会改变数组的大小。
从错误消息中复制未证明的终止性条件到函数中，并用 {anchorTerm insertionSortLoopSorry}`sorry` “证明”它，可以让该函数暂时被接受：
```anchor insertionSortLoopSorry
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      sorry
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorWarning insertionSortLoopSorry
declaration uses 'sorry'
```

由于 {anchorName insertionSortLoop}`insertSorted` 在正在插入的元素的索引上是结构递归的，因此证明应当对该索引进行归纳。
在基本情形中，数组原样返回，因此其长度当然不会改变。
对于归纳步骤，归纳假设是：对下一个更小索引进行的递归调用不会改变数组的长度。
有两种情形需要考虑：要么该元素已经完全插入到已排序区域中，并且数组原样返回，在这种情况下长度也不变；要么该元素在递归调用之前与下一个元素交换。
然而，交换数组中的两个元素不会改变数组的大小，而归纳假设表明，以相邻索引进行的递归调用会返回一个与其参数大小相同的数组。
因此，大小保持不变。

将这个英语定理陈述翻译为 Lean，并使用本章中的技术继续推进，足以证明基例，并在归纳步骤中取得进展：
```anchor insert_sorted_size_eq_0
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
```
在归纳步骤中使用 {anchorName insert_sorted_size_eq_0}`insertSorted` 进行的化简揭示了 {anchorName insert_sorted_size_eq_0}`insertSorted` 中的模式匹配：
```anchorError insert_sorted_size_eq_0
unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
```
当面对包含 {kw}`if` 或 {kw}`match` 的目标时，{anchorTerm insert_sorted_size_eq_1}`split` 策略（不要与归并排序定义中使用的 {anchorName splitList (module := Examples.ProgramsProofs.Inequalities)}`splitList` 函数混淆）会将该目标替换为每条控制流路径各对应的一个新目标：
```anchor insert_sorted_size_eq_1
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split
```
因为通常重要的不是一个陈述是_如何_被证明的，而只是它_已经_被证明，所以 Lean 输出中的证明通常会被 {lit}`⋯` 替代。
此外，每个新目标都有一个假设，用来指出是哪一个分支导向该目标；在此情形中，它名为 {lit}`heq✝`：
```anchorError insert_sorted_size_eq_1
unsolved goals
case h_1
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.lt
⊢ arr.size = arr.size

case h_2
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.eq
⊢ arr.size = arr.size

case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```
与其为两个简单情形都编写证明，不如在 {anchorTerm insert_sorted_size_eq_2}`split` 之后添加 {anchorTerm insert_sorted_size_eq_2}`<;> try rfl`，这会使这两个直接情形立即消失，只留下一个目标：
```anchor insert_sorted_size_eq_2
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
```anchorError insert_sorted_size_eq_2
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

遗憾的是，归纳假设不够强，无法证明此目标。
归纳假设表明，在 {anchorName insert_sorted_size_eq_3}`arr` 上调用 {anchorName insert_sorted_size_eq_3}`insertSorted` 会保持大小不变，但证明目标是表明，以交换后的结果作为参数进行递归调用，其结果也会保持大小不变。
要成功完成证明，需要一个适用于传给 {anchorName insert_sorted_size_eq_3}`insertSorted` 的_任意_数组以及作为参数传入的较小索引的归纳假设

可以通过对 {anchorTerm insert_sorted_size_eq_3}`induction` 策略使用 {anchorTerm insert_sorted_size_eq_3}`generalizing` 选项来获得更强的归纳假设。
该选项会把上下文中的额外假设引入到用于生成基例、归纳假设以及归纳步骤中待证明目标的陈述中。
对 {anchorName insert_sorted_size_eq_3}`arr` 进行泛化会得到更强的假设：
```anchor insert_sorted_size_eq_3
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j generalizing arr with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
在所得目标中，{anchorName insert_sorted_size_eq_3}`arr` 现在是归纳假设中“对于所有”语句的一部分：
```anchorError insert_sorted_size_eq_3
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
j' : Nat
ih : ∀ (arr : Array α) (i : Fin arr.size) (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
arr : Array α
i : Fin arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

:::paragraph
然而，整个证明已经开始变得难以管理。
下一步将是引入一个变量表示交换结果的长度，证明它等于 {anchorTerm insert_sorted_size_eq_3}`arr.size`，然后再证明该变量也等于递归调用所得数组的长度。
随后可以将这些等式陈述串接起来以证明目标。
不过，使用函数归纳要容易得多：
```anchor insert_sorted_size_eq_funInd1
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted with
  | case1 arr isLt => skip
  | case2 arr i isLt this isLt => skip
  | case3 arr i isLt this isEq => skip
  | case4 arr i isLt this isGt ih => skip
```
第一个目标是索引 {anchorTerm insertSorted}`0` 的情形。
在这里，数组未被修改，因此证明其大小未被修改不需要任何复杂步骤：
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case1
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
isLt : 0 < arr.size
⊢ arr.size = arr.size
```
接下来的两个目标相同，并覆盖元素比较中的 {anchorName insertSorted}`.lt` 和 {anchorName insertSorted}`.eq` 情形。
局部假设 {anchorName insert_sorted_size_eq_funInd1}`isLt` 和 {anchorName insert_sorted_size_eq_funInd1}`isEq` 将允许选择 {anchorTerm insertSorted}`match` 的正确分支：
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case2
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt✝ : i + 1 < arr.size
this : i < arr.size
isLt : compare arr[i] arr[⟨i.succ, isLt✝⟩] = Ordering.lt
⊢ (match compare arr[i] arr[⟨i.succ, isLt✝⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt✝⟩) this ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case3
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt : i + 1 < arr.size
this : i < arr.size
isEq : compare arr[i] arr[⟨i.succ, isLt⟩] = Ordering.eq
⊢ (match compare arr[i] arr[⟨i.succ, isLt⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
在最后一种情形中，一旦 {anchorTerm insertSorted}`match` 被化简，仍需做一些工作来证明插入的下一步保持数组大小不变。
特别地，归纳假设表明，下一步的大小等于交换结果的大小，但期望的结论是它等于原数组的大小：
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case4
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt : i + 1 < arr.size
this : i < arr.size
isGt : compare arr[i] arr[⟨i.succ, isLt⟩] = Ordering.gt
ih : (insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size = (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯).size
⊢ (match compare arr[i] arr[⟨i.succ, isLt⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
:::

:::paragraph
Lean 库包含定理 {anchorName insert_sorted_size_eq_funInd}`Array.size_swap`，它表明交换数组的两个元素不会改变数组大小。
默认情况下，{tactic}`grind` 不使用这一事实；但一旦指示它这样做，它就可以处理全部四种情况：
```anchor insert_sorted_size_eq_funInd
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted <;> grind [Array.size_swap]
```
:::

:::paragraph
现在可以使用这个证明来替换 {anchorName insertionSortLoopSorry}`insertionSortLoop` 中的 {anchorTerm insertionSortLoopSorry}`sorry`。
特别地，这个定理使 {anchorTerm insertionSortLoop}`grind` 能够成功：
```anchor insertionSortLoop
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      grind [insert_sorted_size_eq]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
:::


# 驱动函数
%%%
tag := "insertion-sort-driver-function"
file := "The-Driver-Function"
%%%

插入排序本身调用 {anchorName insertionSort}`insertionSortLoop`，并将用于划分数组中已排序区域与未排序区域的索引初始化为 {anchorTerm insertionSort}`0`：

```anchor insertionSort
def insertionSort [Ord α] (arr : Array α) : Array α :=
   insertionSortLoop arr 0
```

几个快速测试表明，该函数至少并非明显错误：
```anchor insertionSortNums
#eval insertionSort #[3, 1, 7, 4]
```
```anchorInfo insertionSortNums
#[1, 3, 4, 7]
```
```anchor insertionSortStrings
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
```
```anchorInfo insertionSortStrings
#["granite", "hematite", "marble", "quartz"]
```

# 这真的是插入排序吗？
%%%
tag := "insertion-sort-in-place"
file := "Is-This-Really-Insertion-Sort___"
%%%


插入排序按其_定义_就是一种原地排序算法。
尽管其最坏情形运行时间是二次的，它之所以有用，是因为它是一种稳定的排序算法，不分配额外空间，并且能高效处理几乎已排序的数据。
如果内层循环的每次迭代都分配一个新数组，那么该算法就并不_真正_是插入排序。

Lean 的数组操作，例如 {anchorName names}`Array.set` 和 {anchorName names}`Array.swap`，会检查相关数组的引用计数是否大于一。
如果是，那么该数组对代码的多个部分可见，这意味着必须复制它。
否则，Lean 就不再是纯函数式语言。
然而，当引用计数恰好为一时，该值不存在其他潜在观察者。
在这些情况下，数组原语会原地修改该数组。
程序的其他部分不知道的事情不会伤害它们。

Lean 的证明逻辑工作在纯函数式程序的层面，而不是底层实现的层面。
这意味着，发现程序是否不必要地复制数据的最佳方式是对其进行测试。
在每个希望发生变异的位置添加对 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 的调用，会使得当相关值具有多于一个引用时，将所提供的消息打印到 {lit}`stderr`。

插入排序中恰好有一处存在复制而非变更的风险：对 {anchorName names}`Array.swap` 的调用。
将 {anchorTerm insertSorted}`arr.swap i' i` 替换为 {anchorTerm InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`(dbgTraceIfShared "array to swap" arr).swap i' i` 会使程序在无法变更数组时发出 {lit}`shared RC array to swap`。
然而，对程序的这一修改也会改变证明，因为现在存在对一个额外函数的调用。
添加一个局部假设，说明 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 保持其参数的长度不变，并将该假设加入若干对 {anchorTerm InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`simp` 的调用中，就足以修复程序和证明。

插入排序的完整插桩代码如下：
```anchor InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      have : (dbgTraceIfShared "array to swap" arr).size = arr.size := by
        simp [dbgTraceIfShared]
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap i' i)
        ⟨i', by simp [*]⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted, dbgTraceIfShared]
    split <;> simp [*]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      omega
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0
```

需要一点技巧来检查插桩是否确实有效。
首先，当函数的所有参数在编译时均已知时，Lean 编译器会积极地优化掉函数调用。
仅仅编写一个将 {anchorName InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort` 应用于大型数组的程序并不足够，因为所得的编译代码可能只包含作为常量的已排序数组。
确保编译器不会优化掉排序例程的最简单方法，是从 {anchorName getLines (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`stdin` 读取数组。
其次，编译器会执行死代码消除。
向程序添加额外的 {kw}`let` 未必会在运行代码中产生更多引用，如果由 {kw}`let` 绑定的变量从未被使用。
为了确保额外引用不会被完全消除，重要的是要确保该额外引用以某种方式被使用。

测试检测代码的第一步是编写 {anchorName getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`getLines`，它从标准输入读取一个由行组成的数组：
```anchor getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
     -- Drop trailing newline:
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines
```
{anchorName various (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`IO.FS.Stream.getLine` 返回一整行文本，包括末尾的换行符。
当已经到达文件结束标记时，它返回 {anchorTerm mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`""`。

接下来，需要两个独立的 {anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main` 例程。
二者都从标准输入读取待排序数组，以确保对 {anchorName mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort` 的调用不会在编译时被替换为其返回值。
二者随后都向控制台打印，以确保对 {anchorName insertionSort}`insertionSort` 的调用不会被完全优化掉。
其中一个只打印排序后的数组，而另一个同时打印排序后的数组和原始数组。
第二个函数应当触发一条警告，说明 {anchorName names}`Array.swap` 必须分配一个新数组：
```anchor mains (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def mainUnique : IO Unit := do
  let lines ← getLines
  for line in insertionSort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort lines do
    IO.println line

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line
```

实际的 {anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main` 只是根据给定的命令行参数在两个主要动作中选择其一：
```anchor main (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    pure 1
```

不带参数运行它会产生预期的用法信息：
```commands «sort-sharing» "sort-demo"
$ sort || true # sort
Expected single argument, either "--shared" or "--unique"
```

文件 {lit}`test-data` 包含以下 rocks：
```file «sort-sharing» "sort-demo/test-data"
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
```

在这些岩石上使用带检测的插入排序，会使它们按字母顺序打印出来：
```commands «sort-sharing» "sort-demo"
$ sort --unique < test-data
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale
```

然而，在保留对原始数组的引用的版本中，第一次调用 {anchorName names}`Array.swap` 会在 {lit}`stderr` 上产生一条通知（即 {lit}`shared RC array to swap`）：
```commands «sort-sharing» "sort-demo"
$ sort --shared < test-data
--- Sorted lines: ---
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale

--- Original data: ---
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
shared RC array to swap
```
只出现一条 {lit}`shared RC` 通知这一事实意味着数组只被复制了一次。
这是因为由调用 {anchorName names}`Array.swap` 产生的副本本身是唯一的，因此无需再进行更多复制。
在命令式语言中，如果在按引用传递数组之前忘记显式复制它，可能会导致微妙的错误。
运行 {lit}`sort --shared` 时，会按需要复制数组，以保持 Lean 程序的纯函数式含义，但不会做更多复制。


# 其他变更机会
%%%
tag := none
file := "Other-Opportunities-for-Mutation"
%%%

当引用唯一时，使用变更而非复制并不限于数组更新运算符。
Lean 还会尝试“回收”引用计数即将降为零的构造子，复用它们而不是分配新数据。
这意味着，例如，{anchorName names}`List.map` 将原地变更一个链表，至少在没有人可能察觉的情况下如此。
优化 Lean 代码中的热点循环时，最重要的步骤之一就是确保被修改的数据不会从多个位置被引用。

# 练习
%%%
tag := "insertion-sort-exercises"
file := "Exercises"
%%%


 * 编写一个反转数组的函数。测试：如果输入数组的引用计数为一，那么你的函数不会分配新数组。

 * 为数组实现归并排序或快速排序。证明你的实现会终止，并测试它不会分配比预期更多的数组。这是一个有挑战性的练习！
