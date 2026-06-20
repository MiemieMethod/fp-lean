import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "函数和定义" =>
%%%
tag := "functions-and-definitions"
%%%

:::paragraph
在 Lean 中，定义使用 {kw}`def` 关键字引入。例如，要定义名称 {anchorTerm helloNameVal}`hello` 来引用字符串 {anchorTerm helloNameVal}`"Hello"`，请编写：

```anchor hello
def hello := "Hello"
```

在 Lean 中，新名称使用冒号加等号运算符 {anchorTerm hello}`:=` 而非 {anchorTerm helloNameVal}`=` 定义。这是因为 {anchorTerm helloNameVal}`=` 用于描述现有表达式之间的相等性，而使用两个不同的运算符有助于避免混淆。
:::

:::paragraph
在 {anchorTerm helloNameVal}`hello` 的定义中，表达式 {anchorTerm helloNameVal}`"Hello"` 足够简单，Lean 能够自动确定定义的类型。然而，大多数定义并不那么简单，因此通常需要添加类型。这可以通过在要定义的名称后使用冒号来完成：

```anchor lean
def lean : String := "Lean"
```

:::

:::paragraph
现在名称已经定义，它们可以使用了，因此

```anchor helloLean
#eval String.append hello (String.append " " lean)
```

输出

```anchorInfo helloLean
"Hello Lean"
```

在 Lean 中，定义的名称只能在其定义之后使用。
:::

在很多语言中，函数定义的语法与其他值的不同。例如，Python 函数定义以 {kw}`def` 关键字开头，而其他定义则以等号定义。在 Lean 中，函数使用与其他值相同的 {kw}`def` 关键字定义。尽管如此，像 {anchorTerm helloNameVal}`hello` 这类的定义引入的名字会 _直接_ 引用其值，而非每次调用一个零参函数返回等价的值。

# 定义函数
%%%
tag := "defining-functions"
%%%

:::paragraph
在 Lean 中有多种方法可以定义函数，最简单的方法是在定义的类型之前放置函数的参数，并用空格分隔。例如，可以编写一个将其参数加 1 的函数：

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

使用 {kw}`#eval` 测试此函数会得到 {anchorInfo add1_7}`8`，符合预期：

```anchor add1_7
#eval add1 7
```

:::

:::paragraph
就像将函数应用于多个参数会用空格分隔一样，接受多个参数的函数定义也是在参数名与类型之间加上空格。函数 {anchorName maximum}`maximum` 的结果等于其两个参数中最大的一个，它接受两个 {anchorName maximum}`Nat` 参数 {anchorName Nat}`n` 和 {anchorName maximum}`k`，并返回一个 {anchorName maximum}`Nat`。

```anchor maximum
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
```

类似地，函数 {anchorName spaceBetween}`spaceBetween` 用空格连接两个字符串。

```anchor spaceBetween
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
```

:::

:::paragraph
当向 {anchorName maximum_eval}`maximum` 这样的已定义函数提供参数时，其结果会首先用提供的值替换函数体中对应的参数名称，然后对产生的函数体求值。例如：

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

求值为自然数、整数和字符串的表达式具有表明其类型的类型（分别为 {anchorName Nat}`Nat`、{anchorName Positivity}`Int` 和 {anchorName Book}`String`）。函数也是如此。一个接受 {anchorName Nat}`Nat` 并返回 {anchorName Bool}`Bool` 的函数类型为 {anchorTerm evenFancy}`Nat → Bool`，而一个接受两个 {anchorName Nat}`Nat` 并返回一个 {anchorName Nat}`Nat` 的函数类型为 {anchorTerm currying}`Nat → Nat → Nat`。

作为特例，当函数的名称直接与 {kw}`#check` 一起使用时，Lean 会返回函数的签名。输入 {anchorTerm add1sig}`#check add1` 会得到 {anchorInfo add1sig}`add1 (n : Nat) : Nat`。然而，Lean 可以通过将函数名称写在括号中来“欺骗”它显示函数的类型，这会导致函数被视为普通表达式，因此 {anchorTerm add1type}`#check (add1)` 会得到 {anchorInfo add1type}`add1 : Nat → Nat`，而 {anchorTerm maximumType}`#check (maximum)` 会得到 {anchorInfo maximumType}`maximum : Nat → Nat → Nat`。这个箭头也可以用 ASCII 替代箭头 {anchorTerm add1typeASCII}`->` 来写，因此前面的函数类型可以分别写成 {anchorTerm add1typeASCII}`example : Nat -> Nat := add1` 和 {anchorTerm maximumTypeASCII}`example : Nat -> Nat -> Nat := maximum`。

在幕后，所有函数实际上都只接受一个参数。像 {anchorName maximum3Type}`maximum` 这样看起来接受多个参数的函数，实际上是接受一个参数然后返回一个新函数。这个新函数接受下一个参数，并且这个过程会一直持续到不再需要更多参数为止。这可以通过向多参数函数提供一个参数来观察：{anchorTerm maximum3Type}`#check maximum 3` 会得到 {anchorInfo maximum3Type}`maximum 3 : Nat → Nat`，而 {anchorTerm stringAppendHelloType}`#check spaceBetween "Hello "` 会得到 {anchorInfo stringAppendHelloType}`spaceBetween "Hello " : String → String`。使用返回函数的函数来实现多参数函数被称为 _柯里化_，以数学家 Haskell Curry 命名。函数箭头是右结合的，这意味着 {anchorTerm currying}`Nat → Nat → Nat` 应该用括号括起来写成 {anchorTerm currying}`Nat → (Nat → Nat)`。

## 练习
%%%
tag := "function-definition-exercises"
%%%

 * 定义一个函数 {anchorName joinStringsWithEx}`joinStringsWith`，类型为 {anchorTerm joinStringsWith}`String → String → String → String`，它通过将第一个参数放在第二个和第三个参数之间创建一个新的字符串。{anchorEvalStep joinStringsWithEx 0}`joinStringsWith ", " "one" "and another"` 应该求值为 {anchorEvalStep joinStringsWithEx 1}`"one, and another"`。
 * {anchorTerm joinStringsWith}`joinStringsWith ": "` 的类型是什么？用 Lean 检查你的答案。
 * 定义一个函数 {anchorName volume}`volume`，类型为 {anchorTerm volume}`Nat → Nat → Nat → Nat`，它计算给定高度、宽度和深度的长方体的体积。

# 定义类型
%%%
tag := "defining-types"
%%%

大多数类型化编程语言都有某种定义类型别名的方法，例如 C 语言的 {c}`typedef`。然而，在 Lean 中，类型是语言的一等公民——它们像任何其他表达式一样。这意味着定义可以引用类型，就像它们可以引用其他值一样。

:::paragraph
例如，如果 {anchorName StringTypeDef}`String` 太长，可以定义一个更短的缩写 {anchorName StringTypeDef}`Str`：

```anchor StringTypeDef
def Str : Type := String
```

然后可以使用 {anchorName aStr}`Str` 作为定义的类型，而不是 {anchorName StringTypeDef}`String`：

```anchor aStr
def aStr : Str := "This is a string."
```

:::

这之所以有效，是因为类型遵循 Lean 的其余规则。类型是表达式，在表达式中，定义的名称可以替换为其定义。因为 {anchorName aStr}`Str` 被定义为 {anchorName Book}`String`，所以 {anchorName aStr}`aStr` 的定义是有意义的。

## 你可能遇到的消息
%%%
tag := "abbrev-vs-def"
%%%

:::paragraph
由于 Lean 支持重载整数文字的方式，尝试使用类型定义变得更加复杂。如果 {anchorName NaturalNumberTypeDef}`Nat` 太短，可以定义一个更长的名称 {anchorName NaturalNumberTypeDef}`NaturalNumber`：

```anchor NaturalNumberTypeDef
def NaturalNumber : Type := Nat
```

然而，使用 {anchorName NaturalNumberTypeDef}`NaturalNumber` 作为定义的类型而不是 {anchorName NaturalNumberTypeDef}`Nat` 并不会产生预期的效果。特别是，定义：

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

此错误发生是因为 Lean 允许数字字面量被 _重载_。当有意义时，自然数字面量可以用于新类型，就像这些类型是内置到系统中一样。这是 Lean 使数学表示方便的使命的一部分，而数学的不同分支使用数字表示法用于非常不同的目的。允许这种重载的特定功能在查找重载之前不会用它们的定义替换所有定义的名称，这就是导致上述错误消息的原因。

:::paragraph
解决此限制的一种方法是在定义的右侧提供类型 {anchorName thirtyEightFixed}`Nat`，从而使 {anchorName thirtyEightFixed}`Nat` 的重载规则用于 {anchorTerm thirtyEightFixed}`38`：

```anchor thirtyEightFixed
def thirtyEight : NaturalNumber := (38 : Nat)
```

该定义仍然是类型正确的，因为 {anchorEvalStep NaturalNumberDef 0}`NaturalNumber` 与 {anchorEvalStep NaturalNumberDef 1}`Nat` 是相同的类型——根据定义！
:::

另一种解决方案是为 {anchorName NaturalNumberDef}`NaturalNumber` 定义一个重载，其工作方式与 {anchorName NaturalNumberDef}`Nat` 的重载等效。然而，这需要 Lean 更高级的功能。

:::paragraph
最后，使用 {kw}`abbrev` 而非 {kw}`def` 为 {anchorName NaturalNumberDef}`Nat` 定义新名称，允许重载解析用其定义替换定义的名称。使用 {kw}`abbrev` 编写的定义总是展开的。例如，

```anchor NTypeDef
abbrev N : Type := Nat
```

和

```anchor thirtyNine
def thirtyNine : N := 39
```

被接受，没有问题。
:::

在幕后，一些定义在重载解析期间被内部标记为可展开，而另一些则不被标记。要展开的定义称为 _可归约的_。对可归约性的控制对于 Lean 的扩展至关重要：完全展开所有定义可能导致非常大的类型，这些类型机器处理起来很慢，用户也难以理解。使用 {kw}`abbrev` 生成的定义被标记为可归约的。
