import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Arrays"

#doc (Manual) "数组与停机性" =>
%%%
tag := "array-termination"
%%%

为了编写高效的代码，选择合适的数据结构非常重要。链表有它的用途：在某些应用程序中，
共享列表的尾部非常重要。但是，大多数可变长有序数据集合的用例都能由数组更好地提供服务，
数组既有较少的内存开销，又有更好的局部性。

然而，数组相对于列表来说有两个缺点：

高效地使用数组需要知道如何向 Lean 证明数组索引在范围内，
以及如何证明接近数组大小的数组索引也会使程序停机。这两个都使用不等式命题，而非命题等式表示。

# 不等式
%%%
tag := "inequality"
%%%

由于不同的类型有不同的序概念，不等式需要由两个类来控制，分别称为 {anchorName ordSugarClasses (module := Examples.Classes)}`LE` 和 {anchorName ordSugarClasses (module := Examples.Classes)}`LT`。
{ref "equality-and-ordering"}[标准类型类] 一节中的表格描述了这些类与语法的关系：

:::table +header
*
  * 表达式
  * 脱糖形式
  * 类名

*
  * {anchorTerm ltDesugar (module := Examples.Classes)}`x < y`
  * {anchorTerm ltDesugar (module := Examples.Classes)}`LT.lt x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm leDesugar (module := Examples.Classes)}`x ≤ y`
  * {anchorTerm leDesugar (module := Examples.Classes)}`LE.le x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

*
  * {anchorTerm gtDesugar (module := Examples.Classes)}`x > y`
  * {anchorTerm gtDesugar (module := Examples.Classes)}`LT.lt y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm geDesugar (module := Examples.Classes)}`x ≥ y`
  * {anchorTerm geDesugar (module := Examples.Classes)}`LE.le y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

:::

换句话说，一个类型可以定制 {anchorTerm ltDesugar (module:=Examples.Classes)}`<` 和 {anchorTerm leDesugar (module:=Examples.Classes)}`≤` 运算符的含义，而 {anchorTerm gtDesugar (module:=Examples.Classes)}`>` 和 {anchorTerm geDesugar (module:=Examples.Classes)}`≥` 可以从 {anchorTerm ltDesugar (module:=Examples.Classes)}`<` 和 {anchorTerm leDesugar (module:=Examples.Classes)}`≤` 中派生它们的含义。
{anchorName ordSugarClasses (module := Examples.Classes)}`LT` 和 {anchorName ordSugarClasses (module := Examples.Classes)}`LE` 类具有返回命题而非 {anchorName CoeBoolProp (module:=Examples.Classes)}`Bool` 的方法：

```anchor less
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
```

{anchorName LENat}`Nat` 的 {anchorName LENat}`LE` 实例会委托给 {anchorName LENat}`Nat.le`：

```anchor LENat
instance : LE Nat where
  le := Nat.le
```
定义 {anchorName LENat}`Nat.le` 需要 Lean 中尚未介绍的一个特性：它是一个归纳定义的关系。

## 归纳定义的命题、谓词和关系
%%%
tag := "inductive-props"
%%%

{anchorName LENat}`Nat.le` 是一个 *归纳定义的关系*。
就像 {kw}`inductive` 可以用来创建新的数据类型一样，它也可以用来创建新的命题。
当一个命题接受一个参数时，它被称为 *谓词*，它可能对某些（但不是所有）潜在参数为真。
接受多个参数的命题称为 *关系*。

归纳定义命题的每个构造函数都是证明它的一种方法。
换句话说，命题的声明描述了它为真的不同形式的证据。
一个没有参数且只有一个构造函数的命题很容易证明：

```anchor EasyToProve
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
```
证明包括使用其构造子：

```anchor fairlyEasy
theorem fairlyEasy : EasyToProve := by
  constructor
```
实际上，命题 {anchorName True}`True` 应该总是很容易证明，它的定义就像 {anchorName EasyToProve}`EasyToProve`：

```anchor True
inductive True : Prop where
  | intro : True
```

不带参数的归纳定义命题远不如归纳定义的数据类型有趣。
这是因为数据本身很有趣——自然数 {anchorTerm IsThree}`3` 不同于数字 {lit}`35`，而订购了 3 个披萨的人如果
30 分钟后收到 35 个披萨会很沮丧。命题的构造子描述了命题可以为真的方式，
但一旦命题被证明，就不需要知道它使用了 *哪些* 底层构造子。
这就是为什么 {anchorTerm IsThree}`Prop` 宇宙中最有趣的归纳定义类型带参数的原因。

:::paragraph
归纳定义谓词 {anchorName IsThree}`IsThree` 陈述其参数为 3：

```anchor IsThree
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
```
这里使用的机制就像 {ref "column-pointers"}[索引族，如 {moduleName (module := Examples.DependentTypes.DB)}`HasCol`]，
只不过结果类型是一个可以被证明的命题，而非可以被使用的数据。
:::

使用此谓词，可以证明三确实等于三：

```anchor threeIsThree
theorem three_is_three : IsThree 3 := by
  constructor
```
类似地，{anchorName IsFive}`IsFive` 是一个谓词，它陈述了其参数为 {anchorTerm IsFive}`5`：

```anchor IsFive
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
```

如果一个数字是三，那么将它加二的结果应该是五。这可以表示为定理陈述：
```anchor threePlusTwoFive0
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  skip
```
结果目标具有函数类型：
```anchorError threePlusTwoFive0
unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)
```
因此，可以使用 {anchorTerm threePlusTwoFive1}`intro` 策略将参数转换为假设：
```anchor threePlusTwoFive1
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
```
```anchorError threePlusTwoFive1
unsolved goals
n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
给定假设 {anchorName threePlusTwoFive1a}`n` 是三，应该可以使用 {anchorName threePlusTwoFive1a}`IsFive` 的构造子来完成证明：
```anchor threePlusTwoFive1a
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  constructor
```
然而，这会产生一个错误：
```anchorError threePlusTwoFive1a
Tactic `constructor` failed: no applicable constructor found

n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
出现此错误是因为 {anchorTerm threePlusTwoFive2}`n + 2` 与 {anchorTerm IsFive}`5` 在定义上不相等。
在普通的函数定义中，可以对假设 {anchorName threePlusTwoFive2}`three` 使用依值模式匹配来将 {anchorName threePlusTwoFive2}`n` 细化为 {anchorTerm threeIsThree}`3`。
依值模式匹配的策略等价为 {anchorTerm threePlusTwoFive2}`cases`，其语法类似于 {kw}`induction`：
```anchor threePlusTwoFive2
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => skip
```
在剩余情况下，{anchorName threePlusTwoFive2}`n` 已细化为 {anchorTerm IsThree}`3`：
```anchorError threePlusTwoFive2
unsolved goals
case isThree
⊢ IsFive (3 + 2)
```
由于 {anchorTerm various}`3 + 2` 在定义上等于 {anchorTerm IsFive}`5`，因此构造子现在适用了：

```anchor threePlusTwoFive3
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
```

标准假命题 {anchorName various}`False` 没有构造子，因此无法提供直接证据。
为 {anchorName various}`False` 提供证据的唯一方法是假设本身不可能，类似于用 {kw}`nomatch`
来标记类型系统认为无法访问的代码。如 {ref "connectives"}[插曲中的证明一节]
所述，否定 {anchorTerm various}`Not A` 是 {anchorTerm various}`A → False` 的缩写。{anchorTerm various}`Not A` 也可以写成 {anchorTerm various}`¬A`。

四不是三：
```anchor fourNotThree0
theorem four_is_not_three : ¬ IsThree 4 := by
  skip
```
初始证明目标包含 {anchorName fourNotThree1}`Not`：
```anchorError fourNotThree0
unsolved goals
⊢ ¬IsThree 4
```
它实际上是一个函数类型的事实可以使用 {anchorTerm fourNotThree1}`unfold` 来揭示：
```anchor fourNotThree1
theorem four_is_not_three : ¬ IsThree 4 := by
  unfold Not
```
```anchorError fourNotThree1
unsolved goals
⊢ IsThree 4 → False
```
因为目标是函数类型，所以可以使用 {anchorTerm fourNotThree2}`intro` 将参数转换为假设。
不需要保留 {anchorTerm fourNotThree1}`unfold`，因为 {anchorTerm fourNotThree2}`intro` 本身可以展开 {anchorName fourNotThree1}`Not` 的定义：
```anchor fourNotThree2
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
```
```anchorError fourNotThree2
unsolved goals
h : IsThree 4
⊢ False
```
在此证明中，{anchorTerm fourNotThreeDone}`cases` 策略直接解决了目标：

```anchor fourNotThreeDone
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
```
就像对 {anchorTerm otherEx (module:=Examples.DependentTypes)}`Vect String 2` 的模式匹配不需要包含 {anchorName otherEx (module:=Examples.DependentTypes)}`Vect.nil` 的情况一样，
对 {anchorTerm fourNotThreeDone}`IsThree 4` 的情况证明不需要包含 {anchorName IsThree}`isThree` 的情况。

## 自然数不等式
%%%
tag := "inequality-of-natural-numbers"
%%%

{anchorName NatLe}`Nat.le` 的定义有一个参数和一个索引：

```anchor NatLe
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
```
参数 {anchorName NatLe}`n` 应该是较小的数字，而索引应该是大于或等于 {anchorName NatLe}`n` 的数字。
当两个数字相等时使用 {anchorName NatLe}`refl` 构造子，而当索引大于 {anchorName NatLe}`n` 时使用 {anchorName NatLe}`step` 构造子。

从证据的视角来看，证明 $`n \leq k` 需要找到一些数字 $`d` 使得 $`n + d = m`。
在 Lean 中，证明由 $`d` 个 {anchorName leNames}`Nat.le.step` 实例包裹的 {anchorName leNames}`Nat.le.refl` 构造子组成。
每个 {anchorName NatLe}`step` 构造子将其索引参数加一，因此 $`d` 个 {anchorName NatLe}`step` 构造子将 $`d` 加到较大的数字上。
例如，证明四小于或等于七由 {anchorName NatLe}`refl` 周围的三个 {anchorName NatLe}`step` 组成：

```anchor four_le_seven
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
```

严格小于关系通过在左侧数字上加一来定义：

```anchor NatLt
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
```
证明四严格小于七由 {anchorName four_lt_seven}`refl` 周围的两个 {anchorName four_lt_seven}`step` 组成：

```anchor four_lt_seven
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
```
这是因为 {anchorTerm four_lt_seven}`4 < 7` 等价于 {anchorTerm four_lt_seven_alt}`5 ≤ 7`。

# 证明停机性
%%%
tag := "proving-termination"
%%%

函数 {anchorName ArrayMap}`Array.map` 使用一个函数转换数组，返回一个新数组，其中包含将该函数应用于输入数组的每个元素的结果。
将其编写为尾递归函数遵循通常的模式，即委托给一个在累加器中传递输出数组的函数。
累加器初始化为空数组。
传递累加器的辅助函数还接受一个参数来跟踪数组中的当前索引，该索引从 {anchorTerm ArrayMap}`0` 开始：

```anchor ArrayMap
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
```

辅助函数应在每次迭代时检查索引是否仍在范围内。
如果是，它应该再次循环，将转换后的元素添加到累加器的末尾，并将索引增加 {anchorTerm mapHelperIndexIssue}`1`。
如果不是，那么它应该终止并返回累加器。
此代码的初始实现失败，因为 Lean 无法证明数组索引有效：
```anchor mapHelperIndexIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
```anchorError mapHelperIndexIssue
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.1811
β : Type ?u.1814
f : α → β
arr : Array α
soFar : Array β
i : Nat
⊢ i < arr.size
```
然而，条件表达式已经检查了有效数组索引所要求的精确条件（即 {anchorTerm arrayMapHelperTermIssue}`i < arr.size`）。
为 {kw}`if` 添加一个名称可以解决此问题，因为它添加了一个前提供数组索引策略使用：

```anchor arrayMapHelperTermIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
Lean 接受修改后的程序，即使递归调用不是针对输入构造子之一的参数进行的。
实际上，累加器和索引都在增长，而非缩小。

在幕后，Lean 的证明自动化构建了一个停机性证明。
重建这个证明可以更容易地理解 Lean 无法自动识别的情况。

为什么 {anchorName arrayMapHelperTermIssue}`arrayMapHelper` 会停机？
每次迭代都会检查索引 {anchorName arrayMapHelperTermIssue}`i` 是否仍在数组 {anchorName arrayMapHelperTermIssue}`arr` 的范围内。
如果是，{anchorName arrayMapHelperTermIssue}`i` 增加，循环重复。
如果不是，程序终止。
因为 {anchorTerm arrayMapHelperTermIssue}`arr.size` 是一个有限的数字，{anchorName arrayMapHelperTermIssue}`i` 只能增加有限次。
即使每次调用时函数的参数都没有减少，{anchorTerm ArrayMapHelperOk}`arr.size - i` 也会向零减少。

每次递归调用时减小的值称为 *度量（Measure）*。
可以通过在定义末尾提供 {kw}`termination_by` 子句来指示 Lean 使用特定表达式作为停机度量。
对于 {anchorName ArrayMapHelperOk}`arrayMapHelper`，显式度量如下所示：

```anchor ArrayMapHelperOk
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
```

类似的停机证明可用于编写 {anchorName ArrayFind}`Array.find`，该函数查找数组中满足布尔函数的第一个元素，并返回该元素及其索引：

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
```
同样，辅助函数会停机，因为随着 {lit}`i` 的增加，{lit}`arr.size - i` 会减少：

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
```

给 {kw}`termination_by` 加上问号（即使用 {kw}`termination_by?`）会使 Lean 显式建议它所选择的度量。
点击 {lit}`[apply]` 会用建议的度量替换 {kw}`termination_by?`：
```anchor ArrayFindHelperSugg
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by?
```
```anchorInfo ArrayFindHelperSugg
Try this:
  [apply] termination_by arr.size - i
```

并非所有的停机论证都像这个这么简单。
然而，基于函数参数识别出某个在每次调用中都会减小的表达式，这种基本结构出现在所有停机证明中。
有时，需要创造力才能弄清楚函数为何停机，有时 Lean 需要额外的证明才能接受度量实际上在减小。



# 练习
%%%
tag := "array-termination-exercises"
%%%

 * 使用尾递归累加器传递函数和 {kw}`termination_by` 子句在数组上实现 {anchorTerm ForMArr}`ForM m (Array α)` 实例。
 * 在恒等单子中使用 {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` 循环重新实现 {anchorName ArrayMap}`Array.map`、{anchorName ArrayFind}`Array.find` 和 {anchorName ForMArr}`ForM` 实例，并比较生成的代码。
 * 在恒等单子中使用 {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` 循环重新实现数组反转。将其与尾递归函数进行比较。
