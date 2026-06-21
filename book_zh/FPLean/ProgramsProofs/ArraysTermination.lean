import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Arrays"

#doc (Manual) "数组与终止性" =>
%%%
tag := "array-termination"
file := "Arrays-and-Termination"
%%%

为了编写高效代码，选择合适的数据结构十分重要。
链表有其用武之地：在某些应用中，共享列表尾部的能力非常重要。
然而，对于可变长度的数据序列集合的大多数用例，数组都能提供更好的支持，因为数组既有更少的内存开销，也有更好的局部性。

然而，相对于列表，数组有两个缺点：
 1. 数组通过索引访问，而不是通过模式匹配访问；为了保持安全性，这会施加 {ref "props-proofs-indexing"}[证明义务]。
 2. 从左到右处理整个数组的循环是一个尾递归函数，但它没有在每次调用时递减的参数。

要有效使用数组，需要知道如何向 Lean 证明某个数组索引在界内，以及如何证明一个趋近于数组大小的数组索引也会使程序终止。
这二者都是用不等式命题来表达的，而不是用命题等式来表达。

# 不等式
%%%
tag := "inequality"
file := "Inequality"
%%%

由于不同类型具有不同的序关系概念，不等式由两个类型类支配，称为 {anchorName ordSugarClasses (module := Examples.Classes)}`LE` 和 {anchorName ordSugarClasses (module := Examples.Classes)}`LT`。
关于 {ref "equality-and-ordering"}[标准类型类] 的一节中的表格说明了这些类如何与语法相关联：

:::table +header
*
  * 表达式
  * 脱糖
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

换言之，一个类型可以自定义 {anchorTerm ltDesugar (module:=Examples.Classes)}`<` 和 {anchorTerm leDesugar (module:=Examples.Classes)}`≤` 运算符的含义，而 {anchorTerm gtDesugar (module:=Examples.Classes)}`>` 和 {anchorTerm geDesugar (module:=Examples.Classes)}`≥` 的含义则由 {anchorTerm ltDesugar (module:=Examples.Classes)}`<` 和 {anchorTerm leDesugar (module:=Examples.Classes)}`≤` 派生而来。
类 {anchorName ordSugarClasses (module := Examples.Classes)}`LT` 和 {anchorName ordSugarClasses (module := Examples.Classes)}`LE` 具有返回命题而非 {anchorName CoeBoolProp (module:=Examples.Classes)}`Bool` 的方法：

```anchor less
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
```

{anchorName LENat}`Nat` 的 {anchorName LENat}`LE` 实例委托给 {anchorName LENat}`Nat.le`：

```anchor LENat
instance : LE Nat where
  le := Nat.le
```
定义 {anchorName LENat}`Nat.le` 需要 Lean 的一个尚未介绍的特性：它是一个归纳定义的关系。

## 归纳定义的命题、谓词与关系
%%%
tag := "inductive-props"
file := "Inductively-Defined-Propositions___-Predicates___-and-Relations"
%%%

{anchorName LENat}`Nat.le` 是一个_归纳定义的关系_。
正如 {kw}`inductive` 可用于创建新的数据类型一样，它也可用于创建新的命题。
当一个命题接受一个参数时，它被称为一个_谓词_，它可能对某些潜在参数为真，但不一定对所有潜在参数都为真。
接受多个参数的命题称为_关系_。

一个归纳定义的命题的每个构造子都是证明该命题的一种方式。
换言之，该命题的声明描述了表明它为真的各种证据形式。
一个没有参数且只有单个构造子的命题可能相当容易证明：

```anchor EasyToProve
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
```
该证明由使用其构造子组成：

```anchor fairlyEasy
theorem fairlyEasy : EasyToProve := by
  constructor
```
事实上，命题 {anchorName True}`True` 应当总是容易证明的，它的定义正如 {anchorName EasyToProve}`EasyToProve`：

```anchor True
inductive True : Prop where
  | intro : True
```

不带参数的归纳定义命题远不如归纳定义的数据类型有趣。
这是因为数据本身就很有意义——自然数 {anchorTerm IsThree}`3` 不同于数 {lit}`35`，而订购了 3 个披萨的人，如果 30 分钟后送到门口的是 35 个披萨，就会感到不满。
命题的构造子描述了该命题可以为真的方式，但一旦一个命题已经被证明，就没有必要知道底层使用了_哪些_构造子。
这就是为什么 {anchorTerm IsThree}`Prop` 宇宙中大多数有趣的归纳定义类型都带有参数。

:::paragraph
归纳定义的谓词 {anchorName IsThree}`IsThree` 表明其参数是三：

```anchor IsThree
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
```
这里使用的机制正如 {ref "column-pointers"}[诸如 {moduleName (module := Examples.DependentTypes.DB)}`HasCol` 这样的索引族]，只是所得类型是可以被证明的命题，而不是可以被使用的数据。
:::

使用这个谓词，可以证明三确实是三：

```anchor threeIsThree
theorem three_is_three : IsThree 3 := by
  constructor
```
类似地，{anchorName IsFive}`IsFive` 是一个谓词，表示其参数是 {anchorTerm IsFive}`5`：

```anchor IsFive
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
```

如果一个数是三，那么给它加二的结果应当是五。
这可以表达为一个定理陈述：
```anchor threePlusTwoFive0
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  skip
```
所得目标具有函数类型：
```anchorError threePlusTwoFive0
unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)
```
因此，{anchorTerm threePlusTwoFive1}`intro` 策略可用于把该参数转换为一个假设：
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
给定 {anchorName threePlusTwoFive1a}`n` 为三这一假设，应当可以使用 {anchorName threePlusTwoFive1a}`IsFive` 的构造子来完成证明：
```anchor threePlusTwoFive1a
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  constructor
```
然而，这会导致一个错误：
```anchorError threePlusTwoFive1a
Tactic `constructor` failed: no applicable constructor found

n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
这个错误发生的原因是 {anchorTerm threePlusTwoFive2}`n + 2` 与 {anchorTerm IsFive}`5` 并非定义相等。
在普通的函数定义中，可以对假设 {anchorName threePlusTwoFive2}`three` 进行依值模式匹配，从而将 {anchorName threePlusTwoFive2}`n` 精化为 {anchorTerm threeIsThree}`3`。
与依值模式匹配对应的策略是 {anchorTerm threePlusTwoFive2}`cases`，其语法类似于 {kw}`induction`：
```anchor threePlusTwoFive2
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => skip
```
在剩余情形中，{anchorName threePlusTwoFive2}`n` 已被细化为 {anchorTerm IsThree}`3`：
```anchorError threePlusTwoFive2
unsolved goals
case isThree
⊢ IsFive (3 + 2)
```
由于 {anchorTerm various}`3 + 2` 按定义等于 {anchorTerm IsFive}`5`，该构造子现在可以应用：

```anchor threePlusTwoFive3
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
```

标准的假命题 {anchorName various}`False` 没有构造子，因此不可能为其提供直接证据。
为 {anchorName various}`False` 提供证据的唯一方式是某个假设本身不可能成立，这类似于 {kw}`nomatch` 可用于标记类型系统能够看出不可达的代码。
如 {ref "connectives"}[关于证明的最初插曲] 中所述，否定 {anchorTerm various}`Not A` 是 {anchorTerm various}`A → False` 的缩写。
{anchorTerm various}`Not A` 也可以写作 {anchorTerm various}`¬A`。

四并不是三：
```anchor fourNotThree0
theorem four_is_not_three : ¬ IsThree 4 := by
  skip
```
初始证明目标包含 {anchorName fourNotThree1}`Not`：
```anchorError fourNotThree0
unsolved goals
⊢ ¬IsThree 4
```
它实际上是函数类型这一事实可以用 {anchorTerm fourNotThree1}`unfold` 暴露出来：
```anchor fourNotThree1
theorem four_is_not_three : ¬ IsThree 4 := by
  unfold Not
```
```anchorError fourNotThree1
unsolved goals
⊢ IsThree 4 → False
```
由于目标是函数类型，可以使用 {anchorTerm fourNotThree2}`intro` 将参数转换为一个假设。
没有必要保留 {anchorTerm fourNotThree1}`unfold`，因为 {anchorTerm fourNotThree2}`intro` 本身可以展开 {anchorName fourNotThree1}`Not` 的定义：
```anchor fourNotThree2
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
```
```anchorError fourNotThree2
unsolved goals
h : IsThree 4
⊢ False
```
在这个证明中，{anchorTerm fourNotThreeDone}`cases` 策略会立即解决目标：

```anchor fourNotThreeDone
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
```
正如对 {anchorTerm otherEx (module:=Examples.DependentTypes)}`Vect String 2` 进行模式匹配时不需要包含 {anchorName otherEx (module:=Examples.DependentTypes)}`Vect.nil` 的情况一样，对 {anchorTerm fourNotThreeDone}`IsThree 4` 进行按情况证明时也不需要包含 {anchorName IsThree}`isThree` 的情况。

## 自然数的不等式
%%%
tag := "inequality-of-natural-numbers"
file := "Inequality-of-Natural-Numbers"
%%%

{anchorName NatLe}`Nat.le` 的定义有一个参数和一个索引：

```anchor NatLe
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
```
参数 {anchorName NatLe}`n` 是应当较小的数，而索引是应当大于或等于 {anchorName NatLe}`n` 的数。
当两个数相等时使用 {anchorName NatLe}`refl` 构造子；当索引大于 {anchorName NatLe}`n` 时使用 {anchorName NatLe}`step` 构造子。

从证据的角度看，对 $`n \leq k` 的证明由寻找某个数 $`d`，使得 $`n + d = m` 成立所组成。
在 Lean 中，该证明于是由一个 {anchorName leNames}`Nat.le.refl` 构造子组成，并由 $`d` 个 {anchorName leNames}`Nat.le.step` 实例包裹。
每个 {anchorName NatLe}`step` 构造子都会给其索引参数加一，因此 $`d` 个 {anchorName NatLe}`step` 构造子会给较大的数加上 $`d`。
例如，四小于等于七的证据由三个围绕一个 {anchorName NatLe}`refl` 的 {anchorName NatLe}`step` 组成：

```anchor four_le_seven
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
```

严格小于关系通过给左侧的数加一来定义：

```anchor NatLt
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
```
四严格小于七的证据由包围着一个 {anchorName four_lt_seven}`refl` 的两个 {anchorName four_lt_seven}`step` 组成：

```anchor four_lt_seven
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
```
这是因为 {anchorTerm four_lt_seven}`4 < 7` 等价于 {anchorTerm four_lt_seven_alt}`5 ≤ 7`。

# 证明终止性
%%%
tag := "proving-termination"
file := "Proving-Termination"
%%%

函数 {anchorName ArrayMap}`Array.map` 用一个函数变换数组，返回一个新数组，其中包含将该函数应用于输入数组每个元素所得的结果。
将它写成尾递归函数遵循通常的模式：委托给一个把输出数组作为累加器传递的函数。
该累加器初始化为空数组。
这个传递累加器的辅助函数还接受一个参数，用以跟踪数组中的当前索引；该索引从 {anchorTerm ArrayMap}`0` 开始：

```anchor ArrayMap
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
```

该辅助函数应当在每次迭代时检查索引是否仍在界内。
若在界内，它应当将变换后的元素添加到累加器末尾，并将索引增加 {anchorTerm mapHelperIndexIssue}`1`，然后再次循环。
若不在界内，则它应当终止并返回累加器。
这段代码的初始实现会失败，因为 Lean 无法证明数组索引是有效的：
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
然而，条件表达式已经检查了数组索引的有效性所要求的精确条件（即 {anchorTerm arrayMapHelperTermIssue}`i < arr.size`）。
给 {kw}`if` 添加一个名称可以解决该问题，因为它添加了一个可供数组索引策略使用的假设：

```anchor arrayMapHelperTermIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
Lean 接受这个修改后的程序，尽管递归调用并不是在某个输入构造子的参数上进行的。
事实上，累加器和索引都在增长，而不是缩小。

在幕后，Lean 的证明自动化会构造一个终止性证明。
重构这个证明可以使那些 Lean 无法自动识别的情形更容易理解。

为什么 {anchorName arrayMapHelperTermIssue}`arrayMapHelper` 会终止？
每次迭代都会检查索引 {anchorName arrayMapHelperTermIssue}`i` 是否仍在数组 {anchorName arrayMapHelperTermIssue}`arr` 的边界内。
如果在边界内，则 {anchorName arrayMapHelperTermIssue}`i` 递增并重复循环。
如果不在边界内，则程序终止。
因为 {anchorTerm arrayMapHelperTermIssue}`arr.size` 是一个有限数，所以 {anchorName arrayMapHelperTermIssue}`i` 只能递增有限多次。
尽管该函数没有任何参数在每次调用时递减，{anchorTerm ArrayMapHelperOk}`arr.size - i` 却朝着零递减。

在每次递归调用中递减的值称为_度量_。
可以通过在定义末尾提供 {kw}`termination_by` 子句，指示 Lean 使用某个特定表达式作为终止性的度量。
对于 {anchorName ArrayMapHelperOk}`arrayMapHelper`，显式的度量如下所示：

```anchor ArrayMapHelperOk
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
```

可以使用类似的终止性证明来编写 {anchorName ArrayFind}`Array.find`，这是一个函数，它在数组中寻找第一个满足某个布尔函数的元素，并返回该元素及其索引：

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
```
同样，辅助函数会终止，因为随着 {lit}`i` 增大，{lit}`arr.size - i` 会减小：

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

给 {kw}`termination_by` 添加一个问号（也就是说，使用 {kw}`termination_by?`）会使 Lean 明确建议它所选择的度量。
点击 {lit}`[apply]` 会将 {kw}`termination_by?` 替换为所建议的度量：
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

并非所有终止性论证都像这个一样简单。
然而，在所有终止性证明中，都会出现这样一种基本结构：基于函数的参数识别某个表达式，并使它在每次调用中减小。
有时，为了弄清楚一个函数究竟为什么会终止，可能需要创造性；有时，Lean 需要额外的证明才能接受该度量确实会减小。



# 练习
%%%
tag := "array-termination-exercises"
file := "Exercises"
%%%

 * 使用尾递归的传递累加器函数和 {kw}`termination_by` 子句，为数组实现一个 {anchorTerm ForMArr}`ForM m (Array α)` 实例。
 * 使用恒等单子中的 {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` 循环重新实现 {anchorName ArrayMap}`Array.map`、{anchorName ArrayFind}`Array.find` 以及 {anchorName ForMArr}`ForM` 实例，并比较所得代码。
 * 在恒等单子中使用 {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` 循环重新实现数组反转。将它与尾递归函数进行比较。
