import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "类型" =>
%%%
tag := "getting-to-know-types"
file := "Types"
%%%

类型根据程序能够计算出的值对程序进行分类。类型在程序中承担多种作用：

 1. 它们允许编译器对值在内存中的表示作出决策。

 2. 它们有助于程序员向他人传达自己的意图，充当关于函数输入与输出的轻量级规约。
编译器确保程序遵守这一规范。

 3. 它们防止各种潜在错误，例如将数字与字符串相加，从而减少程序所需的测试数量。

 4. 它们帮助 Lean 编译器自动生成辅助代码，从而节省样板代码。

Lean 的类型系统具有不同寻常的表达能力。
类型可以编码强规格说明，例如“这个排序函数返回其输入的一个排列”，也可以编码灵活规格说明，例如“这个函数具有不同的返回类型，具体取决于其参数的值”。
类型系统甚至可以用作成熟的逻辑系统来证明数学定理。
然而，这种前沿的表达能力并不使较简单的类型变得不必要；理解这些较简单的类型是使用更高级特性的前提。

:::paragraph
Lean 中的每个程序都必须有一个类型。特别地，每个
表达式在被求值之前都必须有一个类型。在到目前为止的
示例中，Lean 已经能够自行发现类型，但有时
需要提供一个类型。这可以通过在圆括号内使用冒号
运算符来完成：

```anchor onePlusTwoEval
#eval (1 + 2 : Nat)
```


这里，{anchorName onePlusTwoEval}`Nat` 是_自然数_的类型，即任意精度的无符号整数。
在 Lean 中，{anchorName onePlusTwoEval}`Nat` 是非负整数字面量的默认类型。
这种默认类型并不总是最佳选择。
在 C 中，当减法本会产生小于零的结果时，无符号整数会下溢到可表示的最大数。
然而，{anchorName onePlusTwoEval}`Nat` 可以表示任意大的无符号数，因此不存在可下溢到的最大数。
因此，当结果本会为负时，{anchorName onePlusTwoEval}`Nat` 上的减法返回 {anchorName Nat}`zero`。
例如，

```anchor oneMinusTwoEval
#eval (1 - 2 : Nat)
```

求值为 {anchorInfo oneMinusTwoEval}`0` 而不是 {lit}`-1`。
若要使用一种能够表示负整数的类型，请直接提供它：

```anchor oneMinusTwoIntEval
#eval (1 - 2 : Int)
```

使用这个类型，结果如预期为 {anchorInfo oneMinusTwoIntEval}`-1`。
:::

:::paragraph
要检查一个表达式的类型而不对其求值，请使用 {kw}`#check` 而不是 {kw}`#eval`。例如：

```anchor oneMinusTwoIntType
#check (1 - 2 : Int)
```

报告 {anchorInfo oneMinusTwoIntType}`1 - 2 : Int`，而并不实际执行减法。
:::

:::paragraph
当一个程序无法被赋予类型时，{kw}`#check` 和 {kw}`#eval` 都会返回错误。例如：

```anchor stringAppendList
#check String.append ["hello", " "] "world"
```

输出

```anchorError stringAppendList
Application type mismatch: The argument
  ["hello", " "]
has type
  List String
but is expected to have type
  String
in the application
  String.append ["hello", " "]
```

因为 {anchorName stringAppendList}`String.append` 的第一个参数预期是一个字符串，但实际提供的是一个字符串列表。
:::
