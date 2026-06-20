import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "HelloName"

example_module Hello

#doc (Manual) "运行程序" =>
%%%
tag := "running-a-program"
%%%

:::paragraph
运行 Lean 程序最简单的方法是使用 Lean 可执行文件的 {lit}`--run` 选项。
创建一个名为 {lit}`Hello.lean` 的文件并输入以下内容：

```module (module:=Hello)
def main : IO Unit := IO.println "Hello, world!"
```
:::

:::paragraph
然后，从命令行运行：

{command hello "simple-hello" "lean --run Hello.lean"}

程序显示 {commandOut hello}`lean --run Hello.lean` 并退出。
:::



# 问候语的剖析
%%%
tag := "hello-world-parts"
%%%

当使用 {lit}`--run` 选项调用 Lean 时，它会调用程序的 {lit}`main` 定义。
对于不从命令行接受参数的程序，{moduleName (module := Hello)}`main` 的类型应该是 {moduleTerm}`IO Unit`。
这意味着 {moduleName (module := Hello)}`main` 不是一个函数，因为它的类型中没有箭头 ({lit}`→`)。
{moduleTerm}`main` 不是一个具有副作用的函数，而是由要执行的效果的描述组成。

正如 {ref "polymorphism"}[前一章] 所讨论的，{moduleTerm}`Unit` 是最简单的归纳类型。
它有一个名为 {moduleTerm}`unit` 的构造器，不接受任何参数。
C 语言传统中的语言有一个 {CSharp}`void` 函数的概念，它不返回任何值。
在 Lean 中，所有函数都接受一个参数并返回一个值，而使用 {moduleTerm}`Unit` 类型可以表示没什么参数或返回值。
如果 {moduleTerm}`Bool` 表示一比特信息，那么 {moduleTerm}`Unit` 表示零比特信息。

{moduleTerm}`IO α` 是一个程序类型，当执行时，它会抛出异常或返回 {moduleTerm}`α` 类型的值。
在执行期间，该程序可能具有副作用。这些程序被称为 {moduleTerm}`IO` *活动（Action）*。
Lean 区分表达式的 *求值（Evaluation）*（严格遵循用变量值替换值和无副作用地归约子表达式的数学模型）和 {anchorTerm sig}`IO` 活动的 *执行（Execution）*（依赖外部系统与世界交互）。
{moduleTerm}`IO.println` 是一个从字符串到 {moduleTerm}`IO` 活动的函数，当执行时，它会将给定字符串写入标准输出。
因为此活动在发出字符串的过程中不读取环境中任何有趣的信息，所以 {moduleTerm}`IO.println` 的类型是 {moduleTerm}`String → IO Unit`。
如果它确实返回了有趣的东西，那么 {moduleTerm}`IO` 活动的类型将不是 {moduleTerm}`Unit`。



# 函数式编程与副作用
%%%
tag := "fp-effects"
%%%

Lean 的计算模型基于数学表达式的求值，其中变量被赋予一个不随时间变化的值。
求值表达式的结果不会改变，再次求值相同的表达式总是会产生相同的结果。

另一方面，有用的程序必须与世界交互。
一个既不执行输入也不执行输出的程序无法向用户请求数据、在磁盘上创建文件或打开网络连接。
Lean 是用 Lean 本身编写的，Lean 编译器当然会读取文件、创建文件并与文本编辑器交互。
一个总是产生相同结果的语言如何支持读取磁盘文件的程序，而这些文件的内容可能会随时间变化呢？

这种明显的矛盾可以通过对副作用的不同思考方式来解决。
想象一家出售咖啡和三明治的咖啡馆。
这家咖啡馆有两名员工：一名厨师负责完成订单，一名柜台工作人员负责与顾客互动并下订单。
厨师是一个脾气暴躁的人，他真的不喜欢与外界接触，但他非常擅长始终如一地提供咖啡馆闻名的食物和饮料。
然而，为了做到这一点，厨师需要安静，不能被打扰交谈。
柜台工作人员很友好，但在厨房里完全无能。
顾客与柜台工作人员互动，柜台工作人员将所有实际烹饪委托给厨师。
如果厨师对顾客有疑问，例如澄清过敏，他们会给柜台工作人员发一张小纸条，柜台工作人员与顾客互动并将结果传回给厨师。

在这个类比中，厨师就是 Lean 语言。
当收到订单时，厨师忠实而一致地提供所需的东西。
柜台工作人员是周围的运行时系统，它与世界交互，可以接受付款、分发食物并与顾客交谈。
两位员工共同承担餐厅的所有职能，但他们的职责是分开的，每个人都执行他们最擅长的任务。
正如让顾客远离可以使厨师专注于制作真正出色的咖啡和三明治一样，Lean 缺乏副作用使得程序可以作为形式数学证明的一部分使用。
它还有助于程序员理解程序的各个部分，因为没有隐藏的状态变化会在组件之间产生微妙的耦合。
厨师的笔记代表通过评估 Lean 表达式产生的 {moduleTerm}`IO` 活动，而柜台工作人员的回复是从效果中传回的值。

这种副作用模型与 Lean 语言、其编译器和运行时系统 (Run-Time System，RTS) 的整体聚合工作方式非常相似。
运行时系统中的原语（Primitive，用 C 语言编写）实现了所有基本副作用。
当运行程序时，RTS 调用 {moduleTerm}`main` 活动，该活动将新的 {moduleTerm}`IO` 活动返回给 RTS 执行。
RTS 执行这些活动，委托用户 Lean 代码执行计算。
从 Lean 的内部角度来看，程序没有副作用，{moduleTerm}`IO` 活动只是要执行的任务的描述。
从程序用户的外部角度来看，存在一个副作用层，它为程序的核心逻辑创建了一个接口。


# 真实世界的函数式编程
%%%
tag := "fp-world-passing"
%%%


考虑 Lean 中副作用的另一种方式，就是将 {moduleTerm}`IO` 活动看做一个函数，它将整个世界作为参数输入，并返回一个值和一个新的世界。
在这种情况下，从标准输入读取一行文本是一个*纯（Pure）*函数，因为每次都提供一个不同的世界作为参数。
将一行文本写入标准输出也是一个纯函数，因为函数返回的世界与它开始时的世界不同。
程序确实需要小心，永远不要重复使用世界，也不要未能返回一个新世界——毕竟，这相当于时间旅行或世界末日。
谨小慎微的抽象边界可以使这种编程风格变得安全。
如果每个原语 {moduleTerm}`IO` 活动都接受一个世界并返回一个新世界，并且它们只能与保持此不变性的工具结合使用，那么问题就不会发生。

当然，这种模型无法真正实现，毕竟整个世界无法变成 Lean 的值放入内存中。然而，可以实现一个此模型的变体，它带有代表世界的抽象标识。当程序启动时，它会提供一个世界标识。然后将此标识传递给 {moduleTerm}`IO` 原语，之后它们的返回标识同样地传递到下一步。在程序结束时，标识将返回给操作系统。

这种副作用模型很好地描述了 {moduleTerm}`IO` 活动作为 RTS 执行任务的描述在 Lean 内部是如何表示的。
用于转换现实世界的实际函数隐藏在抽象屏障之后。但实际的程序通常不只有一个作用，而是由一系列作用组成。
为了使程序能够使用多个作用，Lean 中有一种名为 {kw}`do` -表示法的子语言，它允许这些原始 {moduleTerm}`IO` 活动安全地组合成一个更大、更有用的程序。

# 组合 {anchorName all}`IO` 活动
%%%
tag := "combining-io-actions"
%%%

大多数有用的程序除了产生输出外，还接受输入。
此外，它们可能会根据输入做出决策，将输入数据作为计算的一部分。
以下程序名为 {lit}`HelloName.lean`，它会询问用户的姓名，然后向他们问好：

```module (anchor:=all)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy

  stdout.putStrLn s!"Hello, {name}!"
```

在此程序中，{anchorName all}`main` 活动由一个 {kw}`do` 块组成。
该块包含一系列 *语句（Statement）*，这些语句既可以是局部变量（使用 {kw}`let` 引入），也可以是要执行的活动。
正如 SQL 可以被认为是与数据库交互的专用语言一样，{kw}`do` 语法可以被认为是 Lean 中专门用于建模命令式程序的专用子语言。
使用 {kw}`do` 块构建的 {anchorName all}`IO` 活动通过按顺序执行语句来执行。

该程序可以像之前的程序一样运行：

{command helloName "hello-name" "expect -f ./run" (show := "lean --run HelloName.lean")}

如果用户回复 {lit}`David`，则与程序交互的会话会读取回应：

```commandOut helloName "expect -f ./run"
How would you like to be addressed?
David
Hello, David!
```

类型签名行与 {lit}`Hello.lean` 的类型签名行相同：
```module (anchor:=sig)
def main : IO Unit := do
```
唯一的区别是它以关键字 {moduleTerm}`do` 结尾，这会启动一系列命令。
{kw}`do` 关键字后面的每个缩进行都是同一系列命令的一部分。

前两行，读取：
```module (anchor:=setup)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
```

通过执行库活动 {moduleTerm (anchor := setup)}`IO.getStdin` 和 {moduleTerm (anchor := setup)}`IO.getStdout`，分别检索 {moduleTerm (anchor := setup)}`stdin` 和 {moduleTerm (anchor := setup)}`stdout` 句柄（Handle）。
在 {moduleTerm}`do` 块中，{moduleTerm}`let` 的含义与普通表达式略有不同。
通常，{moduleTerm}`let` 中的局部定义只能在一个表达式中使用，该表达式紧跟在局部定义之后。
在 {moduleTerm}`do` 块中，由 {moduleTerm}`let` 引入的局部绑定在 {moduleTerm}`do` 块的其余所有语句中都可用，而不仅仅是下一个语句。
此外，{moduleTerm}`let` 通常使用 {lit}`:=` 将被定义的名称与其定义连接起来，而 {moduleTerm}`do` 中的某些 {moduleTerm}`let` 绑定则使用左箭头 ({lit}`←` 或 {lit}`<-`)。
使用箭头意味着表达式的值是一个 {moduleTerm}`IO` 活动，该活动应该被执行，其结果保存在局部变量中。
换句话说，如果箭头右侧的表达式类型为 {moduleTerm}`IO α`，那么在 {moduleTerm}`do` 块的其余部分中，该变量的类型为 {moduleTerm}`α`。
{moduleTerm (anchor := setup)}`IO.getStdin` 和 {moduleTerm (anchor := setup)}`IO.getStdout` 是 {moduleTerm (anchor := sig)}`IO` 活动，以便允许在程序中局部覆盖 {moduleTerm (anchor := setup)}`stdin` 和 {moduleTerm (anchor := setup)}`stdout`，这很方便。
如果它们像 C 语言中的全局变量一样，那么就不存在有意义的方法来覆盖它们，但 {moduleName}`IO` 活动每次执行时都可以返回不同的值。

{moduleTerm}`do` 块的下一部分负责询问用户的姓名：

```module (anchor:=question)
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
```

第一行将问题写入 {moduleTerm (anchor := setup)}`stdout`，第二行从 {moduleTerm (anchor := setup)}`stdin` 请求输入，第三行从输入行中删除尾随换行符（以及任何其他尾随空格）。
{moduleTerm (anchor := question)}`name` 的定义使用 {lit}`:=`，而不是 {lit}`←`，因为 {moduleTerm (anchor := question)}`trimAsciiEnd` 与 {moduleTerm (anchor := question)}`copy` 是普通的字符串处理函数，而不是 {moduleTerm (anchor := sig)}`IO` 活动。

最后，程序的最后一行是：
```module (anchor:=answer)
  stdout.putStrLn s!"Hello, {name}!"
```

它使用 {ref "string-interpolation"}[字符串插值] 将提供的名称插入到问候字符串中，并将结果写入 {moduleTerm (anchor := setup)}`stdout`。
