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
%%%

在 Lean 中，用于分类其他类型的类型被称为宇宙，如 {anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3` 和 {anchorTerm sundries}`Prop` 等。
然而，*宇宙（universe）* 也用于表示一种设计模式：使用数据类型来表示 Lean 类型的子集，并通过一个解释函数将数据类型的构造子映射为实际类型。
这种数据类型的值被称为其映射到的类型的 *编码（codes）*。

尽管实现方式不同。使用这种设计模式实现的宇宙是一组类型的类型，与 Lean 内置的宇宙具有相同的含义。
在 Lean 中，{anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3` 和 {anchorTerm sundries}`Prop` 等类型直接描述其他类型的类型。
这种方式被称为 {deftech}*Russell 风格的宇宙（universes à la Russell）*。
本节中描述的用户定义的宇宙将所有其包含的类型表示为 *数据*，并用一个显式的函数将这些编码映射到实际的类型。
这种方式被称为 {deftech}*Tarski 风格的宇宙（universes à la Tarski）*。
基于依值类型理论的语言（如 Lean）几乎总是使用 Russell 风格的宇宙，而 Tarski 风格的宇宙是这些语言中定义 API 的有用模式。

自定义宇宙使得我们可以划分出一组可以与 API 一起使用的类型的封闭集合。
因为这个集合是封闭的，因此只需要对编码的递归就能使程序适用于该宇宙中的 *任何* 类型。
下面是一个自定义宇宙的例子。它包括具有编码 {anchorName NatOrBool}`nat`（代表 {anchorName NatOrBool}`Nat`）和 {anchorName NatOrBool}`bool`（代表 {anchorName NatOrBool}`Bool`）的数据类型：

```anchor NatOrBool
inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
```
对编码进行模式匹配允许类型被细化，就像对 {moduleName (module := Examples.DependentTypes)}`Vect` 的构造子进行模式匹配会细化其长度一样。
例如，一个从字符串反序列化此宇宙中的类型的值的程序如下：

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
对 {anchorName decode}`t` 进行依值模式匹配允许将期望的结果类型 {anchorTerm decode}`t.asType` 分别细化为 {anchorTerm natOrBoolExamples}`NatOrBool.nat.asType` 和 {anchorTerm natOrBoolExamples}`NatOrBool.bool.asType`，并且这些计算为实际的类型 {anchorName NatOrBool}`Nat` 和 {anchorName NatOrBool}`Bool`。

与任何其他数据一样，编码可能是递归的。
类型 {anchorName NestedPairs}`NestedPairs` 编码了任意嵌套的自然数有序对：

```anchor NestedPairs
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
```
在这种情况下，解释函数 {anchorName NestedPairs}`NestedPairs.asType` 是递归定义的。
这意味着需要对编码进行递归才能实现该宇宙的 {anchorName NestedPairsbeq}`BEq`：

```anchor NestedPairsbeq
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y
```

尽管 {anchorName beqNoCases}`NestedPairs` 宇宙中的每种类型已经有一个 {anchorName beqNoCases}`BEq` 实例，但类型类的搜索不会在实例声明中自动检查数据类型的所有情形，因为这样的情形可能有无限多种，就像 {anchorName beqNoCases}`NestedPairs` 一样。
试图直接诉诸 {anchorName beqNoCases}`BEq` 实例，而不是通过对编码进行递归来向 Lean 解释如何找到它们，会导致错误：
```anchor beqNoCases
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
```
```anchorError beqNoCases
failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
错误信息中的 {anchorName beqNoCases}`t` 代表类型 {anchorName beqNoCases}`NestedPairs` 的未知值。

# 类型类与宇宙
%%%
tag := "type-classes-vs-universe-pattern"
%%%

类型类使得 API 可以被用在任何类型上，只要这些类型实现了必要的接口。
在大多数情况下，这是更合适的做法，因为很难提前预测 API 的所有用例。
类型类允许库代码被原始作者预期之外的更多类型使用。

Tarski 风格的宇宙使得 API 仅能用在实现决定好的一组类型上。在一些情况下，这是有用的：
 * 当一个函数应该根据传递的类型不同而有非常不同的表现时—无法对类型本身进行模式匹配，但可以对类型的编码进行模式匹配；
 * 当外部系统本身就限制了可能提供的数据类型，并且不需要额外的灵活性；
 * 当实现某些操作需要类型的一些额外属性时。

类型类在类似 Java 或 C# 中适合使用接口的场景下更加有用，而 Tarski 风格的宇宙则在类似适合使用封闭类（sealed class）的场景下，且一般的归纳定义数据类型无法使用的情况下更加有用。

# 一个有限类型的宇宙
%%%
tag := "finite-type-universe"
%%%

将 API 限制为只能用于给定的类型允许 API 实现通常情况下不可能的操作。
例如，比较函数是否相等。两个函数相等定义为它们总是将相同的输入映射到相同的输出时。
检查这一点可能需要无限长的时间，例如比较两个类型为 {anchorTerm sundries}`Nat → Bool` 的函数需要检查函数对每个 {anchorName sundries}`Nat` 返回相同的 {anchorName sundries}`Bool`。

换句话说，参数类型为无限类型的函数本身也是无限类型。
函数可以被视为表格，参数类型为无限类型的函数需要无限多行来描述每种情形。
但参数类型为有限类型的函数只需要有限行，意味着该函数类型也是有限类型。
如果两个函数的参数类型均为有限类型，则可以通过枚举参数所有的可能性，然后比较它们在所有这些输入下的输出结果来检查它们是否相等。
检查高阶函数是否相等需要生成给定类型的所有可能函数，此外还需要返回类型是有限的，以便将参数类型的每个元素映射到返回类型的每个元素。
这不是一种 *快速* 的方法，但它确实在有限时间内完成。

表示有限类型的一种方法是定义一个宇宙：

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
在这个宇宙中，构造子 {anchorName Finite}`arr` 表示函数类型（因为函数的箭头符号叫做 {anchorName Finite}`arr` ow）。

:::paragraph
比较这个宇宙中的两个值是否相等与 {anchorName NestedPairs}`NestedPairs` 宇宙中几乎相同。
唯一重要的区别是增加了 {anchorName Finite}`arr` 的情形，它使用一个名为 {anchorName FiniteAll}`Finite.enumerate` 的辅助函数来生成由 {anchorName FiniteBeq}`dom` 编码的类型的每个值，然后检查两个函数对每个可能的输入返回相同的结果：

```anchor FiniteBeq
def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => beq cod (x arg) (y arg)
```
标准库函数 {anchorName sundries}`List.all` 检查提供的函数在列表的每个条目上返回 {anchorName sundries}`true`。
这个函数可以用来比较布尔值上的函数是否相等：
```anchor arrBoolBoolEq
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
```
```anchorInfo arrBoolBoolEq
true
```
它也可以用来比较标准库中的函数：
```anchor arrBoolBoolEq2
#eval Finite.beq (.arr .bool .bool) (fun _ => true) not
```
```anchorInfo arrBoolBoolEq2
false
```
它甚至可以比较使用函数复合等工具构建的函数：
```anchor arrBoolBoolEq3
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)
```
```anchorInfo arrBoolBoolEq3
true
```
这是因为 {anchorName Finite}`Finite` 宇宙编码了 Lean 的 *实际* 函数类型，而非某些特殊的近似。
:::

{anchorName FiniteAll}`enumerate` 的实现也是通过对 {anchorName FiniteAll}`Finite` 的编码进行递归。
```anchor FiniteAll
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr dom cod => dom.functions cod.enumerate
```
{anchorName Finite}`Unit` 只有一个值。{anchorName Finite}`Bool` 有两个值（{anchorName sundries}`true` 和 {anchorName sundries}`false`）。
有序对的值则是 {anchorName FiniteAll}`t1` 编码的类型的值和 {anchorName FiniteAll}`t2` 编码的类型的值的笛卡尔积。
换句话说，{anchorName FiniteAll}`dom` 的每个值都应该与 {anchorName FiniteAll}`cod` 的每个值配对。
辅助函数 {anchorName ListProduct}`List.product` 可以用普通的递归函数编写，但这里在恒等单子中定义 {kw}`for` 实现：

```anchor ListProduct
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse
```
最后，{anchorName FiniteAll}`Finite.enumerate` 将对函数的情形的处理委托给一个名为 {anchorName FiniteFunctionSigStart}`Finite.functions` 的辅助函数，该函数将返回类型的所有值的列表作为参数。

简单来说，生成从某个有限类型到结果的值的所有函数可以被认为是生成函数的表格。
每个函数将一个输出分配给每个输入，这意味着当有 $`k` 个可能的参数时，给定函数的表格有 $`k` 行。
因为表格的每一行都可以选择 $`n` 个可能的输出中的任何一个，所以有 $`n ^ k` 个潜在的函数要生成。

与之前类似，生成从有限类型到一些值列表的函数是通过对描述有限类型的编码进行递归完成的：
```anchor FiniteFunctionSigStart
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
```

{anchorName Finite}`Unit` 的函数表格包含一行，因为函数不能根据提供的输入选择不同的结果。
这意味着为每个潜在的输入生成一个函数。
```anchor FiniteFunctionUnit
| .unit =>
  results.map fun r =>
    fun () => r
```
从 {anchorName sundries}`Bool` 到 $`n` 个结果值时，有 $`n^2` 个函数，因为类型 {anchorTerm sundries}`Bool → α` 的每个函数根据 {anchorName sundries}`Bool` 选择两个特定的 {anchorName sundries}`α` ：
```anchor FiniteFunctionBool
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
```
从有序对中生成函数可以通过利用柯里化来实现：把这个函数转化为一个接受有序对的第一个元素并返回一个等待有序对的第二个元素的函数。
这样做允许在这种情形下递归使用 {anchorName FiniteFunctionSigStart}`Finite.functions`：
```anchor FiniteFunctionPair
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
```

生成高阶函数有点烧脑。
一个函数可以根据其输入/输出行为与其他函数区分开来。
高阶函数的输入行为则又依赖于其函数参数的输入/输出行为：
因此高阶函数的所有行为可以表示为将函数参数应用于所有它所有可能的输入值，然后根据该函数应用的结果的不同产生不同的行为。
这提供了一种构造高阶函数的方法：
 * 从自己也是参数的函数的所有可能参数的列表开始。
 * 对于每个可能的值，构造可以由应用参数函数到可能的参数的观察结果产生的所有可能行为。这可以使用 {anchorName FiniteFunctionSigStart}`Finite.functions` 和对其余参数的递归来完成，因为递归的结果表示基于其余可能参数的观察的函数。{anchorName FiniteFunctionSigStart}`Finite.functions` 根据当前对参数的观察构造所有实现这些方式的方法。
 * 对基于每个观察结果的潜在行为，构造一个将函数参数应用于当前可能参数的高阶函数。然后将此结果传递给观察行为。
 * 递归的基情形是对每个结果值观察无事可做的高阶函数——它忽略函数参数，只是返回结果值。

直接定义这个递归函数导致 Lean 无法证明整个函数终止。
然而，一种更简单的递归形式，*右折叠（right fold）*，可以让终止检查器明确地知道函数终止。
右折叠接受三个参数：（1）步骤函数，它将列表的头与对尾部的递归得到的结果组合在一起；（2）列表为空时的默认值；（3）需要处理的列表。
这个函数会分析列表，将列表中的每个 {lit}`::` 替换为对步骤函数的调用，并将 {lit}`[]` 替换为默认值：

```anchor foldr
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
```
可以使用 {anchorName foldrSum}`foldr` 求出列表中 {anchorName sundries}`Nat` 的和：
```anchorEvalSteps foldrSum
[1, 2, 3, 4, 5].foldr (· + ·) 0
===>
(1 :: 2 :: 3 :: 4 :: 5 :: []).foldr (· + ·) 0
===>
(1 + 2 + 3 + 4 + 5 + 0)
===>
15
```

使用 {anchorName foldrSum}`foldr`，可以创建如下的高阶函数：
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



因为 {anchorName MutualStart}`Finite.enumerate` 和 {anchorName FiniteFunctions}`Finite.functions` 互相调用，它们必须在一个 {kw}`mutual` 块中定义。
换句话说，在 {anchorName MutualStart}`Finite.enumerate` 的定义前需要加入 {kw}`mutual` 关键字：
```anchor MutualStart
mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
```
在 {anchorName FiniteFunctions}`Finite.functions` 的定义后需要加入 {kw}`end` 关键字：
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

这种比较函数的算法并不特别实用。
要检查的情形数量呈指数增长；即使是一个简单的类型，如 {anchorTerm lots}`((Bool × Bool) → Bool) → Bool`，也描述了 {anchorInfoText nestedFunLength}`65536` 个不同的函数。
为什么会有这么多？
根据上面的推理，并使用 $`\left| T \right|` 表示类型 $`T` 描述的值的数量，那么上述函数的值的数量应该为
$$`\left| \left( \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right|`
这个值可以一步步化简为
$$`\left|\mathrm{Bool}\right|^{\left| \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right| },`
$$`2^{2^{\left| \mathtt{Bool} \times \mathtt{Bool} \right| }},`
$$`2^{2^4}`
65536
指数的嵌套会很快地增长。这样的高阶函数还有很多。


# 练习
%%%
tag := "universe-exercises"
%%%

 * 编写一个函数，将由 {anchorName Finite}`Finite` 编码的类型的值转换为字符串。函数应该以表格的方式表示。
 * 将空类型 {anchorName sundries}`Empty` 添加到 {anchorName Finite}`Finite` 和 {anchorName FiniteBeq}`Finite.beq`。
 * 将 {anchorName sundries}`Option` 添加到 {anchorName Finite}`Finite` 和 {anchorName FiniteBeq}`Finite.beq`。
