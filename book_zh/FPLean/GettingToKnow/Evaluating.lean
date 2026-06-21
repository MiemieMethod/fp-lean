import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "求值表达式" =>
%%%
tag := "evaluating"
file := "Evaluating-Expressions"
%%%


对学习 Lean 的程序员而言，最重要的是理解求值如何工作。
求值是寻找表达式的值的过程，正如在算术中所做的那样。
例如，$`15 - 6` 的值是 $`9`，而 $`2 × (3 + 1)` 的值是 $`8`。
为了求后一个表达式的值，首先将 $`3 + 1` 替换为 $`4`，得到 $`2 × 4`，它本身又可化简为 $`8`。
有时，数学表达式包含变量：在知道 $`x` 的值之前，无法计算 $`x + 1` 的值。
在 Lean 中，程序首先是表达式，而思考计算的主要方式就是对表达式求值以找出其值。

大多数编程语言都是_命令式_的，其中程序由一系列语句组成，这些语句应按顺序执行以得到程序的结果。
程序可以访问可变内存，因此变量所指称的值会随时间改变。
除可变状态之外，程序还可能具有其他副作用，例如删除文件、建立外发网络连接、
抛出或捕获异常，以及从数据库读取数据。
“副作用”本质上是一个总括性术语，用来描述程序中可能发生的、但不符合数学表达式求值模型的事情。

然而，在 Lean 中，程序的工作方式与数学表达式相同。
一旦给定了值，变量就不能被重新赋值。对表达式求值不能产生副作用。
如果两个表达式具有相同的值，那么用其中一个替换另一个不会使程序计算出不同的结果。
这并不意味着 Lean 不能用于向控制台写入 {lit}`Hello, world!`，但以同样的方式，执行 I/O 并不是使用 Lean 体验的核心部分。
因此，本章聚焦于如何用 Lean 交互式地求值表达式，而下一章将描述如何编写、编译并运行 {lit}`Hello, world!` 程序。

:::paragraph
要请求 Lean 对一个表达式求值，请在编辑器中在它前面写上 {kw}`#eval`，编辑器随后会报告结果。
通常，通过将光标或鼠标指针悬停在 {kw}`#eval` 上即可看到结果。
例如，

```anchor threeEval
#eval 1 + 2
```

产生值

```anchorInfo threeEval
3
```

:::

:::paragraph
Lean 遵循算术运算符通常的优先级和结合性规则。也就是说，

```anchor orderOfOperations
#eval 1 + 2 * 5
```

产生值 {anchorInfo orderOfOperations}`11`，而不是 {anchorInfo orderOfOperationsWrong}`15`。

:::

:::paragraph
虽然普通数学记法和大多数编程语言都使用圆括号（例如 {lit}`f(x)`）将函数应用于其参数，但 Lean 只是把函数写在其参数旁边（例如 {lit}`f x`）。
函数应用是最常见的操作之一，因此保持其简洁是值得的。
与其写成

```
#eval String.append("Hello, ", "Lean!")
```

要计算 {anchorInfo stringAppendHello}`"Hello, Lean!"`，则应写作

```anchor stringAppendHello
#eval String.append "Hello, " "Lean!"
```

其中，该函数的两个实参只是用空格写在它后面。
:::


:::paragraph
正如算术的运算顺序规则要求在表达式 {anchorTerm orderOfOperationsWrong}`(1 + 2) * 5` 中使用括号一样，当函数的参数要通过另一次函数调用来计算时，也需要使用括号。
例如，在下面的表达式中需要括号

```anchor stringAppendNested
#eval String.append "great " (String.append "oak " "tree")
```

因为否则第二个 {moduleTerm (anchor := stringAppendNested)}`String.append` 会被解释为第一个 {moduleTerm (anchor := stringAppendNested)}`String.append` 的参数，而不是被传入 {moduleTerm (anchor := stringAppendNested)}`"oak "` 和 {moduleTerm (anchor := stringAppendNested)}`"tree"` 作为参数的函数。
必须先求出内部 {anchorTerm stringAppendNested}`String.append` 调用的值，然后才能将其追加到 {moduleTerm (anchor := stringAppendNested)}`"great "`，从而得到最终值 {anchorInfo stringAppendNested}`"great oak tree"`。
:::

:::paragraph
命令式语言通常有两种条件构造：一种是条件_语句_，它根据一个 Boolean 值决定执行哪些指令；另一种是条件_表达式_，它根据一个 Boolean 值决定对两个表达式中的哪一个求值。
例如，在 C 和 C++ 中，条件语句使用 {c}`if` 和 {c}`else` 来书写，而条件表达式则使用三元运算符书写，其中 {c}`?` 和 {c}`:` 将条件与分支分隔开。
在 Python 中，条件语句以 {python}`if` 开始，而条件表达式将 {python}`if` 置于中间。
由于 Lean 是一种面向表达式的函数式语言，因此没有条件语句，只有条件表达式。
它们使用 {kw}`if`、{kw}`then` 和 {kw}`else` 来书写。
例如，

```anchorEvalStep stringAppend 0
String.append "it is " (if 1 > 2 then "yes" else "no")
```

求值为

```anchorEvalStep stringAppend 1
String.append "it is " (if false then "yes" else "no")
```

其求值结果为

```anchorEvalStep stringAppend 2
String.append "it is " "no"
```

它最终求值为 {anchorEvalStep stringAppend 3}`"it is no"`。


:::


:::paragraph
为简洁起见，像这样的一系列求值步骤有时会用箭头写在它们之间：

```anchorEvalSteps stringAppend
String.append "it is " (if 1 > 2 then "yes" else "no")
===>
String.append "it is " (if false then "yes" else "no")
===>
String.append "it is " "no"
===>
"it is no"
```
:::


# 你可能遇到的消息
%%%
tag := "evaluating-messages"
file := "Messages-You-May-Meet"
%%%

:::paragraph
要求 Lean 对一个缺少实参的函数应用求值会导致错误消息。
特别地，示例

```anchor stringAppendReprFunction
#eval String.append "it is "
```

会产生一条相当长的错误消息：

```anchorError stringAppendReprFunction
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  String → String
```

:::

出现此消息是因为，Lean 中只应用于其部分参数的函数会返回新的函数，而这些新函数正在等待其余参数。
Lean 无法向用户显示函数，因此在被要求这样做时会返回错误。


# 练习
%%%
tag := "evaluating-exercises"
file := "Exercises"
%%%

以下表达式的值是什么？请先手工算出它们，
然后将它们输入 Lean 以检查你的结果。

 * {anchorTerm evalEx}`42 + 19`
 * {anchorTerm evalEx}`String.append "A" (String.append "B" "C")`
 * {anchorTerm evalEx}`String.append (String.append "A" "B") "C"`
 * {anchorTerm evalEx}`if 3 == 3 then 5 else 7`
 * {anchorTerm evalEx}`if 3 == 4 then "equal" else "not equal"`
