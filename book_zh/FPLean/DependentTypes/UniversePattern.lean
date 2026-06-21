import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.Finite"

#doc (Manual) "宇宙设计模式" =>
%%%
tag := "universe-pattern"
file := "The-Universe-Design-Pattern"
%%%

在 Lean 中，像 {anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3` 和 {anchorTerm sundries}`Prop` 这样对其他类型进行分类的类型称为宇宙。
然而，术语 _universe_ 也用于一种设计模式：其中用一个数据类型来表示 Lean 的类型的某个子集，并由一个函数把该数据类型的构造子转换为实际的类型。
这个数据类型的值称为其对应类型的_代码_。

正如 Lean 的内建宇宙一样，用这种模式实现的宇宙也是一些类型，它们描述某个可用类型的集合，尽管完成这一点的机制有所不同。
在 Lean 中，存在诸如 {anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3` 和 {anchorTerm sundries}`Prop` 这样的类型，它们直接描述其他类型。
这种安排称为 {deftech}_Russell 风格的宇宙_。
本节所描述的用户定义宇宙将其所有类型都表示为_数据_，并包含一个显式函数，用于将这些编码解释为真正的实际类型。
这种安排称为 {deftech}_Tarski 风格的宇宙_。
虽然像 Lean 这样基于依值类型论的语言几乎总是使用 Russell 风格的宇宙，但 Tarski 风格的宇宙是在这些语言中定义 API 的一种有用模式。

定义一个自定义宇宙，使得可以划分出一个能与某个 API 一同使用的封闭类型集合。
由于该类型集合是封闭的，对编码进行递归便允许程序作用于该宇宙中的_任意_类型。
一个自定义宇宙的例子包含编码 {anchorName NatOrBool}`nat`（代表 {anchorName NatOrBool}`Nat`）和 {anchorName NatOrBool}`bool`（代表 {anchorName NatOrBool}`Bool`）：

```anchor NatOrBool
inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
```
对一个编码进行模式匹配会使类型得到细化，正如对 {moduleName (module := Examples.DependentTypes)}`Vect` 的构造子进行模式匹配会使期望的长度得到细化一样。
例如，可以如下编写一个程序，将这个宇宙中的类型从字符串反序列化出来：

```anchor decode
def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none
```
对 {anchorName decode}`t` 进行依值模式匹配，使得期望的结果类型 {anchorTerm decode}`t.asType` 能够分别被精化为 {anchorTerm natOrBoolExamples}`NatOrBool.nat.asType` 和 {anchorTerm natOrBoolExamples}`NatOrBool.bool.asType`，而它们会计算为实际类型 {anchorName NatOrBool}`Nat` 和 {anchorName NatOrBool}`Bool`。

与任何其他数据一样，编码也可以是递归的。
类型 {anchorName NestedPairs}`NestedPairs` 为 pair 类型与自然数类型的任意可能嵌套提供编码：

```anchor NestedPairs
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
```
在这种情况下，解释函数 {anchorName NestedPairs}`NestedPairs.asType` 是递归的。
这意味着，为了给该宇宙实现 {anchorName NestedPairsbeq}`BEq`，需要对代码进行递归：

```anchor NestedPairsbeq
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y
```

尽管 {anchorName beqNoCases}`NestedPairs` 宇宙中的每个类型已经都有一个 {anchorName beqNoCases}`BEq` 实例，类型类搜索并不会在一个实例声明中自动检查某个数据类型的每一种可能情形，因为这样的情形可能有无限多个，例如 {anchorName beqNoCases}`NestedPairs`。
如果试图直接诉诸 {anchorName beqNoCases}`BEq` 实例，而不是向 Lean 说明如何通过对编码递归来找到它们，就会导致错误：
```anchor beqNoCases
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
```
```anchorError beqNoCases
failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
错误消息中的 {anchorName beqNoCases}`t` 表示类型为 {anchorName beqNoCases}`NestedPairs` 的未知值。

# 类型类与宇宙
%%%
tag := "type-classes-vs-universe-pattern"
file := "Type-Classes-vs-Universes"
%%%

类型类允许一个开放式的类型集合与某个 API 一同使用，只要这些类型具有必要接口的实现即可。
在多数情况下，这更为可取。
很难预先预测某个 API 的所有使用情形，而类型类是一种便捷方式，使库代码能够用于比原作者预期更多的类型。

另一方面，Tarski 风格的宇宙将 API 限制为只能用于预先确定的一组类型。
这在若干情形中很有用：
 * 当一个函数应当根据传入的类型而表现得非常不同时——无法对类型本身进行模式匹配，但允许对类型的代码进行模式匹配
 * 当外部系统本质上限制了可提供数据的类型，并且不希望有额外灵活性时
 * 当除了某些操作的实现之外，还要求类型具有额外性质时

类型类在许多与 Java 或 C# 中的接口相同的场景中很有用，而 Tarski 式宇宙则可用于可能会使用密封类、但普通归纳数据类型不可用的情形。

# 有限类型的宇宙
%%%
tag := "finite-type-universe"
file := "A-Universe-of-Finite-Types"
%%%

将可与某个 API 一同使用的类型限制为预先确定的一组类型，可以支持对于开放式 API 而言不可能实现的操作。
例如，函数通常不能比较相等性。
当函数把相同输入映射到相同输出时，应当认为这些函数相等。
检查这一点可能需要无限多的时间，因为比较两个类型为 {anchorTerm sundries}`Nat → Bool` 的函数，需要检查对于每一个 {anchorName sundries}`Nat`，这些函数都返回相同的 {anchorName sundries}`Bool`。

换言之，从无限类型出发的函数本身也是无限的。
函数可以看作表，而一个参数类型为无限类型的函数需要无限多行来表示每一种情况。
但是，从有限类型出发的函数在其表中只需要有限多行，因此它们是有限的。
两个参数类型为有限类型的函数，可以通过枚举所有可能的参数、分别用每个参数调用这些函数、然后比较结果来检查其相等性。
检查高阶函数的相等性需要生成给定类型的所有可能函数；这还要求返回类型是有限的，以便参数类型的每个元素都能映射到返回类型的每个元素。
这并不是一种_快速_的方法，但它确实会在有限时间内完成。

表示有限类型的一种方式是使用宇宙：

```anchor Finite
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr dom cod => asType dom → asType cod
```
在这个宇宙中，构造子 {anchorName Finite}`arr` 代表函数类型，它用一个 {anchorName Finite}`arr`头来书写。

:::paragraph
比较来自这个宇宙的两个值是否相等，几乎与在 {anchorName NestedPairs}`NestedPairs` 宇宙中的做法相同。
唯一重要的差别是增加了 {anchorName Finite}`arr` 的情形；该情形使用一个名为 {anchorName FiniteAll}`Finite.enumerate` 的辅助函数，生成由 {anchorName FiniteBeq}`dom` 所编码的类型中的每一个值，并检查这两个函数对于每一个可能输入都返回相等的结果：

```anchor FiniteBeq
def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => beq cod (x arg) (y arg)
```
标准库函数 {anchorName sundries}`List.all` 检查所给函数是否在列表的每个条目上都返回 {anchorName sundries}`true`。
此函数可用于比较布尔值上的函数是否相等：
```anchor arrBoolBoolEq
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
```
```anchorInfo arrBoolBoolEq
true
```
它也可以用于比较标准库中的函数：
```anchor arrBoolBoolEq2
#eval Finite.beq (.arr .bool .bool) (fun _ => true) not
```
```anchorInfo arrBoolBoolEq2
false
```
它甚至能够比较使用函数复合等工具构造出的函数：
```anchor arrBoolBoolEq3
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)
```
```anchorInfo arrBoolBoolEq3
true
```
这是因为 {anchorName Finite}`Finite` 宇宙编码的是 Lean 的_实际_函数类型，而不是库所创建的某种特殊类似物。
:::

{anchorName FiniteAll}`enumerate` 的实现同样是通过对来自 {anchorName FiniteAll}`Finite` 的编码进行递归而给出的。
```anchor FiniteAll
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr dom cod => dom.functions cod.enumerate
```
在 {anchorName Finite}`Unit` 的情形中，只有一个值。
在 {anchorName Finite}`Bool` 的情形中，有两个值要返回（{anchorName sundries}`true` 和 {anchorName sundries}`false`）。
在积类型的情形中，结果应当是由 {anchorName FiniteAll}`t1` 所编码的类型的值与由 {anchorName FiniteAll}`t2` 所编码的类型的值的笛卡尔积。
换言之，来自 {anchorName FiniteAll}`dom` 的每一个值都应当与来自 {anchorName FiniteAll}`cod` 的每一个值配对。
辅助函数 {anchorName ListProduct}`List.product` 当然可以用普通递归函数编写，但这里它是在恒等单子中使用 {kw}`for` 定义的：

```anchor ListProduct
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse
```
最后，函数情形下的 {anchorName FiniteAll}`Finite.enumerate` 委托给一个名为 {anchorName FiniteFunctionSigStart}`Finite.functions` 的辅助函数，该辅助函数以所有要作为目标的返回值组成的列表为参数。

一般而言，生成从某个有限类型到一组结果值的所有函数，可以看作是在生成这些函数的表。
每个函数都为每个输入指定一个输出，这意味着当存在 $`k` 个可能的参数时，给定函数的表中有 $`k` 行。
由于表中的每一行都可以从 $`n` 个可能输出中任选一个，因此有 $`n ^ k` 个潜在函数需要生成。

同样，从一个有限类型生成到某个值列表的函数，是在描述该有限类型的代码上递归的：
```anchor FiniteFunctionSigStart
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
```

从 {anchorName Finite}`Unit` 出发的函数表包含一行，因为该函数不能根据提供给它的是哪一个输入来选择不同结果。
这意味着会为每个潜在输入生成一个函数。
```anchor FiniteFunctionUnit
| .unit =>
  results.map fun r =>
    fun () => r
```
当结果值有 $`n` 个时，从 {anchorName sundries}`Bool` 出发的函数有 $`n^2` 个，因为类型为 {anchorTerm sundries}`Bool → α` 的每个单独函数都使用 {anchorName sundries}`Bool` 在两个特定的 {anchorName sundries}`α` 之间进行选择：
```anchor FiniteFunctionBool
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
```
生成来自积类型的函数可以通过利用柯里化来实现。
一个以积为输入的函数可以转换为一个函数：它接收该积的第一个元素，并返回一个正在等待该积第二个元素的函数。
这样做使得在此情形中可以递归地使用 {anchorName FiniteFunctionSigStart}`Finite.functions`：
```anchor FiniteFunctionPair
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
```

生成高阶函数稍微有些费脑。
每个高阶函数都以一个函数作为其参数。
这个作为参数的函数，可以根据其输入/输出行为而与其他函数区分开来。
一般而言，高阶函数可以将参数函数应用于每一个可能的参数，然后它可以基于应用参数函数所得的结果执行任何可能的行为。
这提示了一种构造这些高阶函数的方法：
 * 从作为参数的那个函数的所有可能实参所组成的列表开始。
 * 对于每个可能的参数，构造所有可能的行为，这些行为可能来自观察把参数函数应用于该可能参数所得的结果。这可以使用 {anchorName FiniteFunctionSigStart}`Finite.functions` 以及对其余可能参数的递归来完成，因为递归结果表示的是基于对其余可能参数的观察所得的函数。{anchorName FiniteFunctionSigStart}`Finite.functions` 则基于当前参数的观察，构造实现这些结果的所有方式。
 * 对于响应这些观察的潜在行为，构造一个高阶函数，将参数函数应用于当前可能的参数。其结果随后传递给观察行为。
 * 递归的基例是一个高阶函数：对于每个结果值，它不观察任何内容——它忽略作为参数的函数，并且只返回该结果值。

直接定义这个递归函数会使 Lean 无法证明整个函数会终止。
然而，可以使用一种更简单的递归形式，称为_右折叠_，以便向终止性检查器清楚表明该函数会终止。
右折叠接受三个参数：一个将列表头与对尾部递归所得结果组合起来的步进函数，一个在列表为空时返回的默认值，以及正在处理的列表。
然后它分析该列表，本质上是将列表中的每个 {lit}`::` 替换为对步进函数的一次调用，并将 {lit}`[]` 替换为默认值：

```anchor foldr
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
```
求列表中各个 {anchorName sundries}`Nat` 的和可以用 {anchorName foldrSum}`foldr` 完成：
```anchorEvalSteps foldrSum
[1, 2, 3, 4, 5].foldr (· + ·) 0
===>
(1 :: 2 :: 3 :: 4 :: 5 :: []).foldr (· + ·) 0
===>
(1 + 2 + 3 + 4 + 5 + 0)
===>
15
```

借助 {anchorName foldrSum}`foldr`，可以如下创建高阶函数：
```anchor FiniteFunctionArr
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
```
{anchorName FiniteFunctions}`Finite.functions` 的完整定义是：
```anchor FiniteFunctions
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
| .unit =>
  results.map fun r =>
    fun () => r
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
```



由于 {anchorName MutualStart}`Finite.enumerate` 和 {anchorName FiniteFunctions}`Finite.functions` 相互调用，它们必须在一个 {kw}`mutual` 块中定义。
换言之，紧接在 {anchorName MutualStart}`Finite.enumerate` 的定义之前的是 {kw}`mutual` 关键字：
```anchor MutualStart
mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
```
而在 {anchorName FiniteFunctions}`Finite.functions` 的定义之后紧接着的是 {kw}`end` 关键字：
```anchor MutualEnd
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
end
```

这个比较函数的算法并不特别实用。
需要检查的情形数量呈指数增长；即便像 {anchorTerm lots}`((Bool × Bool) → Bool) → Bool` 这样简单的类型，也描述了 {anchorInfoText nestedFunLength}`65536` 个不同的函数。
为什么会有这么多？
根据上面的推理，并用 $`\left| T \right|` 表示类型 $`T` 所描述的值的数量，我们应当预期
$$`\left| \left( \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right|`
为
$$`\left|\mathrm{Bool}\right|^{\left| \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right| },`
也就是
$$`2^{2^{\left| \mathtt{Bool} \times \mathtt{Bool} \right| }},`
也就是
$$`2^{2^4}`
即 65536。
嵌套指数增长得很快，而且存在许多高阶函数。


# 练习
%%%
tag := "universe-exercises"
file := "Exercises"
%%%

 * 编写一个函数，将由 {anchorName Finite}`Finite` 编码的类型中的任意值转换为字符串。函数应当表示为其表。
 * 将空类型 {anchorName sundries}`Empty` 添加到 {anchorName Finite}`Finite` 和 {anchorName FiniteBeq}`Finite.beq` 中。
 * 将 {anchorName sundries}`Option` 添加到 {anchorName Finite}`Finite` 和 {anchorName FiniteBeq}`Finite.beq`。
