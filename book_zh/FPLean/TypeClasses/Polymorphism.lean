import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true



#doc (Manual) "类型类与多态性" =>
%%%
tag := "tc-polymorphism"
file := "Type-Classes-and-Polymorphism"
%%%

编写适用于给定函数的_任意_重载的函数可能很有用。
例如，{anchorTerm printlnType}`IO.println` 适用于任何具有 {anchorTerm printlnType}`ToString` 实例的类型。
这通过在所需实例外加方括号来表示：{anchorTerm printlnType}`IO.println` 的类型是 {anchorTerm printlnType}`{α : Type} → [ToString α] → α → IO Unit`。
这个类型表示，{anchorTerm printlnType}`IO.println` 接受一个类型为 {anchorTerm printlnType}`α` 的参数，该类型应由 Lean 自动确定，并且必须存在一个可用于 {anchorTerm printlnType}`α` 的 {anchorTerm printlnType}`ToString` 实例。
它返回一个 {anchorTerm printlnType}`IO` 动作。


# 检查多态函数的类型
%%%
tag := "checking-polymorphic-types"
file := "Checking-Polymorphic-Functions___-Types"
%%%

检查一个接受隐式实参或使用类型类的函数的类型，需要使用一些额外语法。
仅仅写出
```anchor printlnMetas
#check (IO.println)
```
产生一个带有元变量的类型：
```anchorInfo printlnMetas
IO.println : ?m.2620 → IO Unit
```
这是因为 Lean 会尽力发现隐式参数，而元变量的出现表明它尚未发现足够的类型信息来做到这一点。
为了理解函数的签名，可以在函数名之前加上 at 符号（{anchorTerm printlnNoMetas}`@`）来抑制这一特性：
```anchor printlnNoMetas
#check @IO.println
```
```anchorInfo printlnNoMetas
@IO.println : {α : Type u_1} → [ToString α] → α → IO Unit
```
在 {lit}`Type` 之后有一个 {lit}`u_1`，它使用了 Lean 中尚未介绍的一个特性。
目前，请忽略 {lit}`Type` 的这些参数。

# 用实例隐式参数定义多态函数
%%%
tag := "defining-polymorphic-functions-with-instance-implicits"
file := "Defining-Polymorphic-Functions-with-Instance-Implicits"
%%%

:::paragraph
一个对列表中所有项求和的函数需要两个实例：{moduleName}`Add` 允许这些项相加，而用于 {anchorTerm ListSum}`0` 的 {moduleName}`OfNat` 实例提供了一个适合作为空列表返回值的值：

```anchor ListSum
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
此函数也可以用 {anchorTerm ListSumZ}`Zero α` 要求来定义，而不是用 {anchorTerm ListSum}`OfNat α 0`。
二者等价，但 {anchorTerm ListSumZ}`Zero α` 可能更易读：

```anchor ListSumZ
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
:::

:::paragraph

此函数可用于一个由 {anchorTerm fourNats}`Nat` 构成的列表：

```anchor fourNats
def fourNats : List Nat := [1, 2, 3, 4]
```
```anchor fourNatsSum
#eval fourNats.sumOfContents
```
```anchorInfo fourNatsSum
10
```
但不适用于 {anchorTerm fourPos}`Pos` 数的列表：

```anchor fourPos
def fourPos : List Pos := [1, 2, 3, 4]
```
```anchor fourPosSum
#eval fourPos.sumOfContents
```
```anchorError fourPosSum
failed to synthesize
  Zero Pos

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
Lean 标准库包含此函数，在其中它被称为 {moduleName}`List.sum`。

:::

用方括号给出的所需实例说明称为_实例隐式参数_。
在幕后，每个类型类都会定义一个结构，其中每个重载操作对应一个字段。
实例是该结构类型的值，每个字段都包含一个实现。
在调用点，Lean 负责为每个实例隐式参数寻找要传递的实例值。
普通隐式参数与实例隐式参数之间最重要的区别在于 Lean 用来寻找参数值的策略。
对于普通隐式参数，Lean 使用一种称为_合一_的技术，寻找一个唯一的参数值，使程序能够通过类型检查器。
这一过程只依赖于函数定义和调用点中涉及的具体类型。
对于实例隐式参数，Lean 则会查询一个内建的实例值表。

正如用于 {anchorName OfNatPos}`Pos` 的 {anchorTerm OfNatPos}`OfNat` 实例以自然数 {anchorName OfNatPos}`n` 作为自动隐式参数一样，实例本身也可以接受实例隐式参数。
{ref "polymorphism"}[关于多态性的章节]介绍了一个多态的点类型：

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```
点的加法应当将底层的 {anchorName PPoint}`x` 和 {anchorName PPoint}`y` 字段相加。
因此，{anchorName AddPPoint}`PPoint` 的 {anchorName AddPPoint}`Add` 实例要求这些字段所具有的任意类型都有一个 {anchorName AddPPoint}`Add` 实例。
换言之，{anchorName AddPPoint}`PPoint` 的 {anchorName AddPPoint}`Add` 实例还要求 {anchorName AddPPoint}`α` 有一个进一步的 {anchorName AddPPoint}`Add` 实例：

```anchor AddPPoint
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
```
当 Lean 遇到两个点相加时，它会搜索并找到这个实例。
随后它会进一步搜索 {anchorTerm AddPPoint}`Add α` 实例。

以这种方式构造的实例值是该类型类的结构类型的值。
一次成功的递归实例搜索会产生一个结构值，其中包含对另一个结构值的引用。
{anchorTerm AddPPointNat}`Add (PPoint Nat)` 的实例包含对已找到的 {anchorTerm AddPPointNat}`Add Nat` 实例的引用。

这种递归搜索过程意味着，类型类提供的能力显著强于普通的重载函数。
多态实例库是一组代码构件；只要给定所期望的类型，编译器就会自行将它们组装起来。
接受实例参数的多态函数，是对类型类机制的潜在请求，要求其在幕后组装辅助函数。
API 的客户端因此无需手工把所有必要部分连接在一起。


# 方法与隐式参数
%%%
tag := "method-implicit-params"
file := "Methods-and-Implicit-Arguments"
%%%

{anchorTerm ofNatType}`OfNat.ofNat` 的类型可能令人意外。
它是 {anchorTerm ofNatType}`: {α : Type} → (n : Nat) → [OfNat α n] → α`，其中 {anchorTerm ofNatType}`Nat` 参数 {anchorTerm ofNatType}`n` 作为显式函数参数出现。
然而，在该方法的声明中，{anchorName OfNat}`ofNat` 仅具有类型 {anchorName ofNatType}`α`。
这种表面上的差异是因为声明一个类型类实际上会得到如下内容：

 * 一种结构类型，用于包含每个重载操作的实现
 * 一个与该类同名的命名空间
 * 对于每个方法，类的命名空间中都有一个函数，用于从实例中取回该方法的实现

这类似于声明一个新结构也会声明访问器函数的方式。
主要区别在于，结构的访问器以结构值作为显式参数，而类型类方法以实例值作为实例隐式参数，由 Lean 自动查找。

为了使 Lean 能够找到一个实例，该实例的参数必须可用。
这意味着类型类的每个参数都必须是方法的一个参数，并且出现在该实例之前。
当这些参数是隐式参数时最为方便，因为 Lean 会完成发现其值的工作。
例如，{anchorTerm addType}`Add.add` 的类型是 {anchorTerm addType}`{α : Type} → [Add α] → α → α → α`。
在这种情况下，类型参数 {anchorTerm addType}`α` 可以是隐式的，因为传给 {anchorTerm addType}`Add.add` 的参数提供了关于用户意图使用哪种类型的信息。
随后可用这个类型来搜索 {anchorTerm addType}`Add` 实例。

然而，在 {anchorName ofNatType}`OfNat.ofNat` 的情形中，要解码的特定 {moduleName}`Nat` 字面量并不作为任何其他参数类型的一部分出现。
这意味着 Lean 在试图确定隐式参数 {anchorName ofNatType}`n` 时将没有可用的信息。
其结果会是一个非常不便的 API。
因此，在这些情形下，Lean 对类的方法使用显式参数。



# 练习
%%%
tag := "type-class-polymorphism-exercises"
file := "Exercises"
%%%

## 偶数数字字面量
%%%
tag := none
file := "Even-Number-Literals"
%%%


为 {ref "even-numbers-ex"}[上一节练习]中的偶数数据类型编写一个 {anchorName ofNatType}`OfNat` 实例，该实例使用递归实例搜索。

## 递归实例搜索深度
%%%
tag := none
file := "Recursive-Instance-Search-Depth"
%%%

Lean 编译器尝试递归实例搜索的次数有一个上限。
这会限制上一练习中定义的偶数数字字面量的大小。
请通过实验确定这个上限。
