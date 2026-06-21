import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "函数与定义" =>
%%%
tag := "functions-and-definitions"
file := "Functions-and-Definitions"
%%%

:::paragraph
在 Lean 中，定义使用 {kw}`def` 关键字引入。
例如，若要定义名称 {anchorTerm helloNameVal}`hello` 以指代字符串 {anchorTerm helloNameVal}`"Hello"`，可写作：

```anchor hello
def hello := "Hello"
```

在 Lean 中，新名称使用冒号等号运算符 {anchorTerm hello}`:=` 来定义，而不是使用 {anchorTerm helloNameVal}`=`。
这是因为 {anchorTerm helloNameVal}`=` 用于描述已有表达式之间的等式，而使用两个不同的运算符有助于避免混淆。
:::

:::paragraph
在 {anchorTerm helloNameVal}`hello` 的定义中，表达式 {anchorTerm helloNameVal}`"Hello"` 足够简单，因此 Lean 能够自动确定该定义的类型。
然而，大多数定义并不如此简单，所以通常需要添加类型。
这是通过在被定义的名称后使用冒号来完成的：

```anchor lean
def lean : String := "Lean"
```

:::

:::paragraph
既然这些名称已经定义，就可以使用它们，因此

```anchor helloLean
#eval String.append hello (String.append " " lean)
```

输出

```anchorInfo helloLean
"Hello Lean"
```

在 Lean 中，已定义的名称只能在其定义之后使用。
:::

在许多语言中，函数的定义与其他值的定义使用不同的语法。
例如，Python 的函数定义以 {kw}`def` 关键字开头，而其他定义则用等号来定义。
在 Lean 中，函数与其他值一样，使用相同的 {kw}`def` 关键字来定义。
不过，诸如 {anchorTerm helloNameVal}`hello` 这样的定义所引入的名称是_直接_指向其值，而不是指向每次被调用时都返回等价结果的零参数函数。

# 定义函数
%%%
tag := "defining-functions"
file := "Defining-Functions"
%%%

:::paragraph
在 Lean 中定义函数有多种方式。最简单的方式是将函数的参数放在定义的类型之前，并用空格分隔。例如，一个给其参数加一的函数可以写作：

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

用 {kw}`#eval` 测试此函数会得到预期的 {anchorInfo add1_7}`8`：

```anchor add1_7
#eval add1 7
```

:::

:::paragraph
正如通过在各个实参之间写空格来将函数应用于多个实参一样，接受多个实参的函数也是通过在各参数的名称与类型之间写空格来定义的。函数 {anchorName maximum}`maximum` 的结果等于其两个实参中的较大者；它接受两个 {anchorName maximum}`Nat` 实参 {anchorName Nat}`n` 和 {anchorName maximum}`k`，并返回一个 {anchorName maximum}`Nat`。

```anchor maximum
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
```

类似地，函数 {anchorName spaceBetween}`spaceBetween` 将两个字符串用一个空格连接起来。

```anchor spaceBetween
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
```

:::

:::paragraph
当像 {anchorName maximum_eval}`maximum` 这样已定义的函数获得其参数后，其结果通过如下方式确定：首先在函数体中用所提供的值替换参数名，然后对所得函数体求值。例如：

```anchorEvalSteps maximum_eval
maximum (5 + 8) (2 * 7)
===>
maximum 13 14
===>
if 13 < 14 then 14 else 13
===>
14
```

:::

求值结果为自然数、整数和字符串的表达式具有说明这一点的类型（分别为 {anchorName Nat}`Nat`、{anchorName Positivity}`Int` 和 {anchorName Book}`String`）。
函数也是如此。
一个接受 {anchorName Nat}`Nat` 并返回 {anchorName Bool}`Bool` 的函数具有类型 {anchorTerm evenFancy}`Nat → Bool`，而一个接受两个 {anchorName Nat}`Nat` 并返回 {anchorName Nat}`Nat` 的函数具有类型 {anchorTerm currying}`Nat → Nat → Nat`。

作为一种特殊情形，当函数名直接与 {kw}`#check` 一起使用时，Lean 会返回该函数的签名。
输入 {anchorTerm add1sig}`#check add1` 会得到 {anchorInfo add1sig}`add1 (n : Nat) : Nat`。
然而，可以通过将函数名写在括号中来“诱使” Lean 显示该函数的类型；这会使该函数被当作普通表达式处理，因此 {anchorTerm add1type}`#check (add1)` 会得到 {anchorInfo add1type}`add1 : Nat → Nat`，而 {anchorTerm maximumType}`#check (maximum)` 会得到 {anchorInfo maximumType}`maximum : Nat → Nat → Nat`。
这个箭头也可以用 ASCII 替代箭头 {anchorTerm add1typeASCII}`->` 来书写，因此前述函数类型可分别写作 {anchorTerm add1typeASCII}`example : Nat -> Nat := add1` 和 {anchorTerm maximumTypeASCII}`example : Nat -> Nat -> Nat := maximum`。

在幕后，所有函数实际上都精确地期望一个参数。
像 {anchorName maximum3Type}`maximum` 这样看起来接受多个参数的函数，事实上是接受一个参数然后返回一个新函数的函数。
这个新函数接受下一个参数，如此过程持续下去，直到不再期望更多参数。
向一个多参数函数提供一个参数即可看出这一点：{anchorTerm maximum3Type}`#check maximum 3` 得到 {anchorInfo maximum3Type}`maximum 3 : Nat → Nat`，而 {anchorTerm stringAppendHelloType}`#check spaceBetween "Hello "` 得到 {anchorInfo stringAppendHelloType}`spaceBetween "Hello " : String → String`。
用返回函数的函数来实现多参数函数，称为_柯里化_，这一名称来自数学家 Haskell Curry。
函数箭头向右结合，这意味着 {anchorTerm currying}`Nat → Nat → Nat` 应当加括号为 {anchorTerm currying}`Nat → (Nat → Nat)`。

## 练习
%%%
tag := "function-definition-exercises"
file := "Exercises"
%%%

 * 定义类型为 {anchorTerm joinStringsWith}`String → String → String → String` 的函数 {anchorName joinStringsWithEx}`joinStringsWith`，它通过把第一个参数放在第二个参数和第三个参数之间来创建一个新字符串。{anchorEvalStep joinStringsWithEx 0}`joinStringsWith ", " "one" "and another"` 应求值为 {anchorEvalStep joinStringsWithEx 1}`"one, and another"`。
 * {anchorTerm joinStringsWith}`joinStringsWith ": "` 的类型是什么？请用 Lean 检查你的答案。
 * 定义一个类型为 {anchorTerm volume}`Nat → Nat → Nat → Nat` 的函数 {anchorName volume}`volume`，用于计算具有给定高度、宽度和深度的长方体的体积。

# 定义类型
%%%
tag := "defining-types"
file := "Defining-Types"
%%%

大多数带类型的编程语言都有某种为类型定义别名的手段，例如 C 的 {c}`typedef`。
然而，在 Lean 中，类型是语言的一等组成部分——它们像其他任何事物一样是表达式。
这意味着定义既可以引用类型，也可以引用其他值。

:::paragraph
例如，如果 {anchorName StringTypeDef}`String` 输入起来过于繁琐，可以定义一个较短的缩写 {anchorName StringTypeDef}`Str`：

```anchor StringTypeDef
def Str : Type := String
```

于是可以使用 {anchorName aStr}`Str` 作为定义的类型，而不是使用 {anchorName StringTypeDef}`String`：

```anchor aStr
def aStr : Str := "This is a string."
```

:::

这一点之所以成立，是因为类型遵循与 Lean 其余部分相同的规则。
类型是表达式，而在表达式中，已定义的名称可以用其定义替换。
由于 {anchorName aStr}`Str` 已被定义为表示 {anchorName Book}`String`，因此 {anchorName aStr}`aStr` 的定义是有意义的。

## 你可能遇到的消息
%%%
tag := "abbrev-vs-def"
file := "Messages-You-May-Meet"
%%%

:::paragraph
由于 Lean 支持重载的整数字面量，用定义来表示类型的实验会因此变得更复杂。
如果 {anchorName NaturalNumberTypeDef}`Nat` 太短，可以定义一个更长的名称 {anchorName NaturalNumberTypeDef}`NaturalNumber`：

```anchor NaturalNumberTypeDef
def NaturalNumber : Type := Nat
```

然而，使用 {anchorName NaturalNumberTypeDef}`NaturalNumber` 作为定义的类型而不是 {anchorName NaturalNumberTypeDef}`Nat`，并不会产生预期的效果。
特别地，以下定义：

```anchor thirtyEight
def thirtyEight : NaturalNumber := 38
```

导致以下错误：

```anchorError thirtyEight
failed to synthesize
  OfNat NaturalNumber 38
numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::

这个错误发生是因为 Lean 允许数值字面量被_重载_。
在有意义时，自然数字面量可以用于新类型，就好像这些类型是系统内建的一样。
这是 Lean 使命的一部分，即让表示数学变得方便；而数学的不同分支会出于非常不同的目的使用数字记号。
允许这种重载的具体功能在查找重载之前，并不会把所有已定义名称替换为它们的定义，这正是导致上述错误消息的原因。

:::paragraph
绕过这一限制的一种方法是在定义右侧给出类型 {anchorName thirtyEightFixed}`Nat`，从而使 {anchorName thirtyEightFixed}`Nat` 的重载规则被用于 {anchorTerm thirtyEightFixed}`38`：

```anchor thirtyEightFixed
def thirtyEight : NaturalNumber := (38 : Nat)
```

该定义仍然是类型正确的，因为 {anchorEvalStep NaturalNumberDef 0}`NaturalNumber` 与 {anchorEvalStep NaturalNumberDef 1}`Nat` 是同一个类型——根据定义即如此！
:::

另一种解决方案是为 {anchorName NaturalNumberDef}`NaturalNumber` 定义一个重载，使其工作方式等同于 {anchorName NaturalNumberDef}`Nat` 的重载。
不过，这需要 Lean 的更高级特性。

:::paragraph
最后，使用 {kw}`abbrev` 而不是 {kw}`def` 为 {anchorName NaturalNumberDef}`Nat` 定义新名称，使得重载解析能够用该名称的定义替换被定义的名称。
使用 {kw}`abbrev` 写出的定义总是会被展开。
例如，

```anchor NTypeDef
abbrev N : Type := Nat
```

以及

```anchor thirtyNine
def thirtyNine : N := 39
```

会被顺利接受。
:::

在幕后，有些定义在内部被标记为可在重载解析期间展开，而另一些则不是。
将要被展开的定义称为_可约的_。
对可约性的控制对于使 Lean 能够扩展至关重要：完全展开所有定义可能产生非常大的类型，机器处理起来很慢，用户也难以理解。
用 {kw}`abbrev` 产生的定义会被标记为可约。
