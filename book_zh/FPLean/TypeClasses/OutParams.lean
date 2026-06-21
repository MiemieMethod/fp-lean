import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "控制实例搜索" =>
%%%
tag := "out-params"
file := "Controlling-Instance-Search"
%%%

{moduleName}`Add` 类的一个实例足以允许两个类型为 {moduleName}`Pos` 的表达式被方便地相加，并产生另一个 {moduleName}`Pos`。
然而，在许多情况下，更加灵活并允许_异质_运算符重载可能很有用，其中实参可以具有不同类型。
例如，将一个 {moduleName}`Nat` 加到一个 {moduleName}`Pos` 上，或将一个 {moduleName}`Pos` 加到一个 {moduleName}`Nat` 上，总会产生一个 {moduleName}`Pos`：

```anchor addNatPos
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
```
这些函数允许将自然数加到正数上，但它们不能与 {moduleName}`Add` 类型类一起使用，因为该类型类要求 {moduleName}`add` 的两个参数具有相同类型。

# 异构重载
%%%
tag := "heterogeneous-operators"
file := "Heterogeneous-Overloadings"
%%%

如关于 {ref "overloaded-addition"}[重载加法] 的一节所述，Lean 提供了一个名为 {anchorName chapterIntro}`HAdd` 的类型类，用于异构地重载加法。
{anchorName chapterIntro}`HAdd` 类接受三个类型参数：两个参数类型和返回类型。
{anchorTerm haddInsts}`HAdd Nat Pos Pos` 和 {anchorTerm haddInsts}`HAdd Pos Nat Pos` 的实例允许使用普通的加法记号来混合这些类型：

```anchor haddInsts
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
```
给定上述两个实例，以下示例可以工作：
```anchor posNatEx
#eval (3 : Pos) + (5 : Nat)
```
```anchorInfo posNatEx
8
```
```anchor natPosEx
#eval (3 : Nat) + (5 : Pos)
```
```anchorInfo natPosEx
8
```

:::paragraph
{anchorName chapterIntro}`HAdd` 类型类的定义非常类似于下面 {moduleName}`HPlus` 的定义及其相应实例：

```anchor HPlus
class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
```

```anchor HPlusInstances
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
```
然而，{moduleName}`HPlus` 的实例明显不如 {anchorName chapterIntro}`HAdd` 的实例有用。
当试图将这些实例与 {kw}`#eval` 一起使用时，会发生错误：
```anchor hPlusOops
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
```
```anchorError hPlusOops
typeclass instance problem is stuck
  HPlus Pos Nat ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the third type argument to `HPlus` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
该消息表明，这是因为类型中存在一个元变量，而 Lean 没有办法求解它。
:::

正如在 {ref "polymorphism"}[对多态性的初始描述]中所讨论的，元变量表示程序中无法被推断出的未知部分。
当在 {kw}`#eval` 之后书写一个表达式时，Lean 会尝试自动确定其类型。
在这个例子中，它无法做到这一点。
由于 {anchorName HPlusInstances}`HPlus` 的第三个类型参数未知，Lean 无法执行类型类实例搜索；但实例搜索又是 Lean 能够确定该表达式类型的唯一方式。
也就是说，{anchorTerm HPlusInstances}`HPlus Pos Nat Pos` 实例只有在该表达式应当具有类型 {moduleName}`Pos` 时才能适用，但程序中除了该实例本身之外，没有任何内容表明它应当具有这个类型。

该问题的一种解决方案是通过给整个表达式添加类型标注，确保三个类型全部可用：
```anchor hPlusLotsaTypes
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
```
```anchorInfo hPlusLotsaTypes
8
```
然而，对于正数库的用户来说，此解决方案并不十分方便。


# 输出参数
%%%
tag := "output-parameters"
file := "Output-Parameters"
%%%

也可以通过将 {anchorName HPlus}`γ` 声明为_输出参数_来解决此问题。
大多数类型类参数是搜索算法的输入：它们用于选择实例。
例如，在一个 {moduleName}`OfNat` 实例中，类型和自然数都用于选择对自然数文字的某种特定解释。
然而，在某些情况下，即使某些类型参数尚未知晓，也可以方便地启动搜索过程，并使用搜索中发现的实例来确定元变量的值。
启动实例搜索时不需要的参数是该过程的输出，这用 {moduleName}`outParam` 修饰符声明：

```anchor HPlusOut
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
```

有了这个输出参数，类型类实例搜索就能够在预先不知道 {anchorName HPlusOut}`γ` 的情况下选择实例。
例如：
```anchor hPlusWorks
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
```
```anchorInfo hPlusWorks
8
```

将输出参数理解为定义了某种函数，可能会有所帮助。
某个具有一个或多个输出参数的类型类的任意给定实例，都会向 Lean 提供根据输入确定输出的指令。
搜索实例的过程，可能以递归方式进行，最终会比单纯的重载更强大。
输出参数可以确定程序中的其他类型，而实例搜索可以把一组底层实例组装成一个具有此类型的程序。

# 默认实例
%%%
tag := "default-instances"
file := "Default-Instances"
%%%

判定一个参数是输入还是输出，会控制 Lean 在何种情形下发起类型类搜索。
特别地，在所有输入均已知之前，不会发生类型类搜索。
然而，在某些情况下，输出参数还不够；即使某些输入未知，也应当发生实例搜索。
这有点像 Python 或 Kotlin 中可选函数参数的默认值，只不过这里被选择的是默认_类型_。

_默认实例_是这样的实例：即使并非其所有输入都已知，它们也可用于实例搜索。
当这些实例之一可以使用时，就会使用它。
这可以使程序成功通过类型检查，而不是因未知类型和元变量相关的错误而失败。
另一方面，默认实例会使实例选择更难预测。
特别是，如果选中了不期望的默认实例，那么表达式的类型可能不同于预期，从而可能在程序的其他位置引发令人困惑的类型错误。
请谨慎选择使用默认实例的位置！

默认实例可能有用的一个例子是可以从 {moduleName}`Add` 实例派生出的 {anchorName HPlusOut}`HPlus` 实例。
换言之，普通加法是异质加法的一个特例，其中三个类型恰好相同。
这可以使用以下实例实现：

```anchor notDefaultAdd
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
有了这个实例，{anchorName notDefaultAdd}`hPlus` 可以用于任何可加类型，例如 {moduleName}`Nat`：
```anchor hPlusNatNat
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
```
```anchorInfo hPlusNatNat
8
```

然而，此实例只会在两个参数的类型都已知的情形中使用。
例如，
```anchor plusFiveThree
#check HPlus.hPlus (5 : Nat) (3 : Nat)
```
产生类型
```anchorInfo plusFiveThree
HPlus.hPlus 5 3 : Nat
```
如预期那样，但
```anchor plusFiveMeta
#check HPlus.hPlus (5 : Nat)
```
产生一个包含两个元变量的类型，一个对应于剩余参数，另一个对应于返回类型：
```anchorInfo plusFiveMeta
HPlus.hPlus 5 : ?m.15752 → ?m.15754
```

在绝大多数情况下，当某人为加法提供一个实参时，另一个实参将具有相同类型。
要把此实例变成默认实例，请应用 {anchorTerm defaultAdd}`default_instance` 属性：

```anchor defaultAdd
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
有了这个默认实例，该示例具有一个更有用的类型：
```anchor plusFive
#check HPlus.hPlus (5 : Nat)
```
产生
```anchorInfo plusFive
HPlus.hPlus 5 : Nat → Nat
```

每个同时存在可重载的异构版本和同构版本的运算符，都遵循一种默认实例的模式，使同构版本能够在期望异构版本的上下文中使用。
中缀运算符会被替换为对异构版本的调用，并且在可能时选择同构的默认实例。

类似地，仅仅写下 {anchorTerm fiveType}`5` 会得到一个 {anchorTerm fiveType}`Nat`，而不是得到一个带有元变量、并等待更多信息以选择 {moduleName}`OfNat` 实例的类型。
这是因为 {moduleName}`Nat` 的 {moduleName}`OfNat` 实例是一个默认实例。

默认实例还可以被赋予_优先级_，这些优先级会影响在多个实例都可能适用的情形下选择哪一个。
关于默认实例优先级的更多信息，请参阅 Lean 手册。


# 练习
%%%
tag := "out-params-exercises"
file := "Exercises"
%%%

定义一个 {anchorTerm MulPPoint}`HMul (PPoint α) α (PPoint α)` 实例，使其将两个投影都乘以该标量。
它应适用于任何存在 {anchorTerm MulPPoint}`Mul α` 实例的类型 {anchorName MulPPoint}`α`。
例如，
```anchor HMulPPoint
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
```
应当产生
```anchorInfo HMulPPoint
{ x := 5.000000, y := 7.400000 }
```
