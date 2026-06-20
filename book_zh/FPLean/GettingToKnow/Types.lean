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
%%%

类型根据它们可以计算的值对程序进行分类。类型在程序中扮演着多种角色：

 1. 它们允许编译器对值的内存表示做出决策。

 2. 它们帮助程序员向他人传达他们的意图，作为函数输入和输出的轻量级规范。
    编译器确保程序遵守此规范。

 3. 它们防止各种潜在的错误，例如将数字添加到字符串，从而减少程序所需的测试数量。

 4. 它们帮助 Lean 编译器自动化生成可以节省样板代码的辅助代码。

Lean 的类型系统异常富有表现力。
类型可以编码强规范，例如“此排序函数返回其输入的排列”，以及灵活规范，例如“此函数具有不同的返回类型，具体取决于其参数的值”。
类型系统甚至可以用作证明数学定理的完整逻辑。
然而，这种尖端表达能力并不会使更简单的类型变得不必要，理解这些更简单的类型是使用更高级功能的前提。

:::paragraph
Lean 中的每个程序都必须有一个类型。特别是，每个表达式在求值之前都必须有一个类型。
到目前为止的示例中，Lean 能够自行发现类型，但有时需要提供一个。
这通过在括号内使用冒号运算符来完成：

```anchor onePlusTwoEval
#eval (1 + 2 : Nat)
```


这里，{anchorName onePlusTwoEval}`Nat` 是 *自然数* 的类型，它们是任意精度的无符号整数。
在 Lean 中，{anchorName onePlusTwoEval}`Nat` 是非负整数文字的默认类型。
此默认类型并非总是最佳选择。
在 C 语言中，当减法结果小于零时，无符号整数会下溢到最大可表示数。
然而，{anchorName onePlusTwoEval}`Nat` 可以表示任意大的无符号数，因此没有最大数可以下溢。
因此，当答案本应为负数时，{anchorName onePlusTwoEval}`Nat` 上的减法返回 {anchorName Nat}`zero`。
例如，

```anchor oneMinusTwoEval
#eval (1 - 2 : Nat)
```

求值为 {anchorInfo oneMinusTwoEval}`0` 而不是 {lit}`-1`。
要使用可以表示负整数的类型，请直接提供它：

```anchor oneMinusTwoIntEval
#eval (1 - 2 : Int)
```

有了这个类型，结果是 {anchorInfo oneMinusTwoIntEval}`-1`，符合预期。
:::

:::paragraph
要检查表达式的类型而不对其求值，请使用 {kw}`#check` 而不是 {kw}`#eval`。
例如：

```anchor oneMinusTwoIntType
#check (1 - 2 : Int)
```

报告 {anchorInfo oneMinusTwoIntType}`1 - 2 : Int`，而无需实际执行减法。
:::

:::paragraph
当程序无法获得类型时，{kw}`#check` 和 {kw}`#eval` 都会返回错误。
例如：

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

因为 {anchorName stringAppendList}`String.append` 的第一个参数预期是字符串，但却提供了一个字符串列表。
:::
