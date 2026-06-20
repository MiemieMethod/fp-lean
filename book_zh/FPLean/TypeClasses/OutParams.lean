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
%%%

要方便地相加两个 {moduleName}`Pos` 类型，并产生另一个 {moduleName}`Pos`，一个 {moduleName}`Add` 类的的实例就足够了。但是，在许多情况下，参数可能有不同的类型，重载一个灵活的 *异质* 运算符是更为有用的。例如，让 {moduleName}`Nat` 和 {moduleName}`Pos`，或 {moduleName}`Pos` 和 {moduleName}`Nat` 相加总会是一个 {moduleName}`Pos`：

```anchor addNatPos
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
```
这些函数允许自然数与正数相加，但它们不能与 {moduleName}`Add` 类型类一起使用，该类型类要求 {moduleName}`add` 的两个参数具有相同的类型。

# 异质重载
%%%
tag := "heterogeneous-operators"
%%%

如 {ref "overloaded-addition"}[重载加法] 一节所述，Lean 提供了一个名为 {anchorName chapterIntro}`HAdd` 的类型类来重载异质加法。
{anchorName chapterIntro}`HAdd` 类接受三个类型参数：两个参数类型和返回类型。
{anchorTerm haddInsts}`HAdd Nat Pos Pos` 和 {anchorTerm haddInsts}`HAdd Pos Nat Pos` 的实例允许使用普通的加法表示法来混合类型：

```anchor haddInsts
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
```
有了上面两个实例，就有了下面的例子：
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
{anchorName chapterIntro}`HAdd` 类型类的定义与以下 {moduleName}`HPlus` 的定义及其相应实例非常相似：

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
然而，{moduleName}`HPlus` 的实例远不如 {anchorName chapterIntro}`HAdd` 的实例有用。
当尝试将这些实例与 {kw}`#eval` 一起使用时，会发生错误：
```anchor hPlusOops
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
```
```anchorError hPlusOops
typeclass instance problem is stuck
  HPlus Pos Nat ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the third type argument to `HPlus` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
这条消息表明，发生这种情况是因为类型中存在一个元变量，而 Lean 没有办法求解它。
:::

如 {ref "polymorphism"}[多态性的初步描述] 中所述，元变量表示程序中无法推断的未知部分。
当一个表达式被写在 {kw}`#eval` 之后时，Lean 会尝试自动确定其类型。在这种情况下，它无法做到自动确定类型。
因为 {anchorName HPlusInstances}`HPlus` 的第三个类型参数是未知的，所以 Lean 无法执行类型类实例搜索，但实例搜索是 Lean 确定表达式类型的唯一方法。
也就是说，只有当表达式应具有类型 {moduleName}`Pos` 时，{anchorTerm HPlusInstances}`HPlus Pos Nat Pos` 实例才能应用，但程序中除了实例本身之外没有任何东西表明它应具有此类型。

解决该问题的一种方法是通过向整个表达式添加类型注释来确保所有三种类型都可用：
```anchor hPlusLotsaTypes
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
```
```anchorInfo hPlusLotsaTypes
8
```
然而，对于正数库的用户来说，这个解决方案不是很方便。


# 输出参数
%%%
tag := "output-parameters"
%%%

这个问题也可以通过将 {anchorName HPlus}`γ` 声明为*输出参数*来解决。
多数类型类参数是作为搜索算法的输入：它们被用于选取一个实例。
例如，在 {moduleName}`OfNat` 实例中，类型和自然数都用于选择自然数字面量的特定解释。
然而，在一些情况下，在尽管有些类型参数仍然处于未知状态时就开始进行搜索是更方便的。这样就能使用在搜索中发现的实例来决定元变量的值。
在开始搜索实例时不需要用到的参数就是这个过程的结果，该参数使用 {moduleName}`outParam` 修饰符声明：

```anchor HPlusOut
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
```

有了这个输出参数，类型类实例搜索就能够在不预先知道 {anchorName HPlusOut}`γ` 的情况下选择一个实例。例如：
```anchor hPlusWorks
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
```
```anchorInfo hPlusWorks
8
```

认为输出参数相当于是定义某种函数在思考时可能会有帮助。任意给定的，类型类的实例都有一个或更多输出参数提供给 Lean。
这能指导 Lean 通过输入（的类型参数）来确定输出（的类型）。一个可能是递归的实例搜索过程，最终会比简单的重载更为强大。
输出参数能够决定程序中的其他类型，实例搜索能够将一族附属实例组合成具有这种类型的程序。

# 默认实例
%%%
tag := "default-instances"
%%%

确定一个参数是否是一个输入或输出参数控制了 Lean 会在何时启动类型类搜索。具体而言，直到所有输入都变为已知，类型类搜索才会开始。然而，在一些情况下，输出参数是不足的。此时，即使一些输入参数仍然处于未知状态，实例搜索也应该开始。这有点像是 Python 或 Kotlin 中可选函数参数的默认值，但在这里是默认*类型*。

*默认实例* 是当 *并不是全部输入均为已知时* 可用的实例。当一个默认实例能被使用时，它就将会被使用。这能帮助程序成功通过类型检查，而不是因为关于未知类型和元变量的错误而失败。但另一方面，默认类型会让实例选取变得不那么可预测。具体而言，如果一个不合适的实例被选取了，那么表达式将可能具有和预期不同的类型。这会导致令人困惑的类型错误发生在程序中。明智地选择要使用默认实例的地方！

默认实例可以发挥作用的一个例子是，可以从 {moduleName}`Add` 实例派生出的 {anchorName HPlusOut}`HPlus` 实例。
换句话说，普通加法是异质加法的一种特殊情况，其中所有三种类型恰好相同。
这可以使用以下实例来实现：

```anchor notDefaultAdd
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
有了这个实例，{anchorName notDefaultAdd}`hPlus` 就可以用于任何可加类型，比如 {moduleName}`Nat`：
```anchor hPlusNatNat
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
```
```anchorInfo hPlusNatNat
8
```

然而，这个实例只会在两个参数的类型都已知的情况下使用。
例如，
```anchor plusFiveThree
#check HPlus.hPlus (5 : Nat) (3 : Nat)
```
产生类型
```anchorInfo plusFiveThree
HPlus.hPlus 5 3 : Nat
```
正如预期的那样，但是
```anchor plusFiveMeta
#check HPlus.hPlus (5 : Nat)
```
产生一个包含两个元变量的类型，一个用于剩余参数，一个用于返回类型：
```anchorInfo plusFiveMeta
HPlus.hPlus 5 : ?m.15752 → ?m.15754
```

在绝大多数情况下，当有人为加法提供一个参数时，另一个参数将具有相同的类型。
要将此实例设为默认实例，请应用 {anchorTerm defaultAdd}`default_instance` 属性：

```anchor defaultAdd
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
有了这个默认实例，这个例子就有了一个更有用的类型：
```anchor plusFive
#check HPlus.hPlus (5 : Nat)
```
结果为：
```anchorInfo plusFive
HPlus.hPlus 5 : Nat → Nat
```

每个存在于可重载异质和同构版本中的运算符都遵循默认实例的模式，该模式允许在需要异质的上下文中使用同构版本。
中缀运算符被替换为对异质版本的调用，并在可能的情况下选择同构默认实例。

同样，简单地写 {anchorTerm fiveType}`5` 会得到一个 {anchorTerm fiveType}`Nat`，而不是一个带有元变量的类型，该元变量正在等待更多信息以选择 {moduleName}`OfNat` 实例。
这是因为 {moduleName}`Nat` 的 {moduleName}`OfNat` 实例是默认实例。

默认实例也可以被分配*优先级*，这会影响在多个实例可能适用的情况下选择哪个实例。
有关默认实例优先级的更多信息，请参阅 Lean 手册。


# 练习
%%%
tag := "out-params-exercises"
%%%

定义一个 {anchorTerm MulPPoint}`HMul (PPoint α) α (PPoint α)` 的实例，该实例将两个投影都乘以标量。
它应该适用于任何存在 {anchorTerm MulPPoint}`Mul α` 实例的类型 {anchorName MulPPoint}`α`。
例如，
```anchor HMulPPoint
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
```
应该产生
```anchorInfo HMulPPoint
{ x := 5.000000, y := 7.400000 }
```
