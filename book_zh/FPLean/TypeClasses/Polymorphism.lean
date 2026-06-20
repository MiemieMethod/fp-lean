import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true



#doc (Manual) "类型类与多态" =>
%%%
tag := "tc-polymorphism"
%%%

编写适用于给定函数*任何*重载的函数可能很有用。
例如，{anchorTerm printlnType}`IO.println` 适用于任何具有 {anchorTerm printlnType}`ToString` 实例的类型。
这通过在所需实例周围使用方括号来表示：{anchorTerm printlnType}`IO.println` 的类型是 {anchorTerm printlnType}`{α : Type} → [ToString α] → α → IO Unit`。
该类型表示 {anchorTerm printlnType}`IO.println` 接受一个类型为 {anchorTerm printlnType}`α` 的参数，Lean 应该自动确定该参数，并且必须有一个可用于 {anchorTerm printlnType}`α` 的 {anchorTerm printlnType}`ToString` 实例。
它返回一个 {anchorTerm printlnType}`IO` 操作。


# 检查多态函数的类型
%%%
tag := "checking-polymorphic-types"
%%%

对接受隐式参数，或使用了类型类的函数进行类型检查时，我们需要用到一些额外的语法。简单地写
```anchor printlnMetas
#check (IO.println)
```
会产生一个带有元变量的类型：
```anchorInfo printlnMetas
IO.println : ?m.2620 → IO Unit
```
这里显示出了元变量是因为即使 Lean 尽全力去寻找隐式参数，但还是没有找到足够的类型信息来做到这一点。要理解函数的签名，可以在函数名之前加上一个 at 符号 ({anchorTerm printlnNoMetas}`@`) 来抑制此功能：
```anchor printlnNoMetas
#check @IO.println
```
```anchorInfo printlnNoMetas
@IO.println : {α : Type u_1} → [ToString α] → α → IO Unit
```
{anchorTerm chapterIntro}`Type` 后面有一个 {lit}`u_1`，这里使用了目前尚未介绍的 Lean 的特性。我们可以暂时忽略 {anchorTerm chapterIntro}`Type` 的这些参数。

# 定义含隐式实例的多态函数
%%%
tag := "defining-polymorphic-functions-with-instance-implicits"
%%%

:::paragraph
一个对列表中所有条目求和的函数需要两个实例：{moduleName}`Add` 允许对条目进行加法运算，而 {anchorTerm ListSum}`0` 的 {moduleName}`OfNat` 实例为返回空列表提供了一个合理的值：

```anchor ListSum
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
该函数也可以使用 {anchorTerm ListSumZ}`Zero α` 要求而不是 {anchorTerm ListSum}`OfNat α 0` 来定义。
两者是等效的，但 {anchorTerm ListSumZ}`Zero α` 更易于阅读：

```anchor ListSumZ
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
:::

:::paragraph

该函数可用于 {anchorTerm fourNats}`Nat` 列表：

```anchor fourNats
def fourNats : List Nat := [1, 2, 3, 4]
```
```anchor fourNatsSum
#eval fourNats.sumOfContents
```
```anchorInfo fourNatsSum
10
```
但不能用于 {anchorTerm fourPos}`Pos` 数字列表：

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
Lean 标准库包含此函数，称为 {moduleName}`List.sum`。

:::

方括号中所需实例的规范称为*隐式实例（Instance implicits）*。
在幕后，每个类型类都定义了一个结构，该结构具有每个重载操作的字段。实例是该结构类型的值，每个字段包含一个实现。
在调用时，Lean负责为每个隐式实例参数找到一个实例值传递。普通的隐式参数和隐式实例最重要的不同就是 Lean 寻找参数值的策略。
对于普通的隐式参数，Lean使用一种称为*归一化（unification）*的技术来找到一个唯一的能使程序通过类型检查的参数值。
这个过程只依赖于函数定义中和调用时的具体类型。对于隐式实例，Lean 会查阅内置的实例值表。

就像 {anchorName OfNatPos}`Pos` 的 {anchorTerm OfNatPos}`OfNat` 实例将自然数 {anchorName OfNatPos}`n` 作为自动隐式参数一样，实例本身也可以接受实例隐式参数。
{ref "polymorphism"}[关于多态性的部分] 介绍了一种多态点类型：

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```
点的加法应该将底层的 {anchorName PPoint}`x` 和 {anchorName PPoint}`y` 字段相加。
因此，{anchorName AddPPoint}`PPoint` 的 {anchorName AddPPoint}`Add` 实例需要这些字段具有的任何类型的 {anchorName AddPPoint}`Add` 实例。
换句话说，{anchorName AddPPoint}`PPoint` 的 {anchorName AddPPoint}`Add` 实例需要 {anchorName AddPPoint}`α` 的另一个 {anchorName AddPPoint}`Add` 实例：

```anchor AddPPoint
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
```
当 Lean 遇到两个点的加法时，它会搜索并找到此实例。然后它会进一步搜索 {anchorTerm AddPPoint}`Add α` 实例。

以这种方式构造的实例值是类型类的结构体类型的值。成功的递归实例搜索会产生一个结构体值，该结构体值引用另一个结构体值。
{anchorTerm AddPPointNat}`Add (PPoint Nat)` 的实例包含对找到的 {anchorTerm AddPPointNat}`Add Nat` 实例的引用。

这种递归搜索过程意味着类型类比普通的重载函数提供了更强大的功能。
多态实例库是一组代码构建块，编译器将根据所需的类型自行组装。
接受实例参数的多态函数是对类型类机制的潜在请求，以在幕后组装辅助函数。
API 的客户端无需手动将所有必要的部件连接在一起。


# 方法和隐式参数
%%%
tag := "method-implicit-params"
%%%

{anchorTerm ofNatType}`OfNat.ofNat` 的类型可能令人惊讶。
它是 {anchorTerm ofNatType}`: {α : Type} → (n : Nat) → [OfNat α n] → α`，其中 {anchorTerm ofNatType}`Nat` 参数 {anchorTerm ofNatType}`n` 作为显式函数参数出现。
然而，在方法的声明中，{anchorName OfNat}`ofNat` 的类型仅为 {anchorName ofNatType}`α`。
这种看似的差异是因为声明一个类型类实际上会产生以下结果：

 * 声明一个包含了每个重载操作的实现的结构体类型
 * 声明一个与类同名的命名空间
 * 对于每个方法，会在类的命名空间中声明一个函数，该函数从实例中获取其实现。

这类似于声明新结构也声明访问器函数的方式。主要区别在于结构的访问器函数将结构值作为显式参数，而类型类方法将实例值作为隐式实例，由 Lean 自动查找。

为了让 Lean 找到一个实例，它的参数必须是可用的。这意味着类型类的每个参数都必须是出现在实例之前的方法的参数。
当这些参数是隐式的时最方便，因为 Lean 会完成发现它们的值的工作。
例如，{anchorTerm addType}`Add.add` 的类型为 {anchorTerm addType}`{α : Type} → [Add α] → α → α → α`。
在这种情况下，类型参数 {anchorTerm addType}`α` 可以是隐式的，因为 {anchorTerm addType}`Add.add` 的参数提供了有关用户预期类型的信息。
然后可以使用此类型来搜索 {anchorTerm addType}`Add` 实例。

然而，在 {anchorName ofNatType}`OfNat.ofNat` 的情况下，要解码的特定 {moduleName}`Nat` 字面量不作为任何其他参数类型的一部分出现。
这意味着 Lean 在尝试找出隐式参数 {anchorName ofNatType}`n` 时将没有任何信息可供使用。结果将是一个非常不方便的 API。
因此，在这些情况下，Lean 选择为类方法提供一个显式参数。



# 练习
%%%
tag := "type-class-polymorphism-exercises"
%%%

## 偶数字面量
%%%
tag := none
%%%


为 {ref "even-numbers-ex"}[上一节练习] 中的偶数数据类型编写一个使用递归实例搜索的 {anchorName ofNatType}`OfNat` 实例。

## 递归实例搜索深度
%%%
tag := none
%%%

Lean 编译器尝试进行递归实例搜素的次数是有限的。这限制了前面的练习中定义的偶数字面量的尺寸。通过实验确定这个上限是多少。
