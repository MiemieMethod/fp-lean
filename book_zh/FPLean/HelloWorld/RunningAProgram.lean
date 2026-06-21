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
file := "Running-a-Program"
%%%

:::paragraph
运行 Lean 程序的最简单方式是对 Lean 可执行文件使用 {lit}`--run` 选项。
创建一个名为 {lit}`Hello.lean` 的文件，并输入以下内容：

```module (module:=Hello)
def main : IO Unit := IO.println "Hello, world!"
```
:::

:::paragraph
然后，在命令行中运行：

{command hello "simple-hello" "lean --run Hello.lean"}

该程序显示 {commandOut hello}`lean --run Hello.lean` 并退出。
:::



# 问候的剖析
%%%
tag := "hello-world-parts"
file := "Anatomy-of-a-Greeting"
%%%

当使用 {lit}`--run` 选项调用 Lean 时，它会调用程序的 {lit}`main` 定义。
在不接受命令行参数的程序中，{moduleName (module := Hello)}`main` 应具有类型 {moduleTerm}`IO Unit`。
这意味着 {moduleName (module := Hello)}`main` 不是一个函数，因为它的类型中没有箭头（{lit}`→`）。
{moduleTerm}`main` 不是一个具有副作用的函数，而是由一份待执行效果的描述构成。

如{ref "polymorphism"}[前一章]所讨论，{moduleTerm}`Unit` 是最简单的归纳类型。
它只有一个名为 {moduleTerm}`unit` 的构造子，该构造子不接受任何参数。
C 传统中的语言有一种 {CSharp}`void` 函数的概念，它完全不返回任何值。
在 Lean 中，所有函数都接受一个参数并返回一个值；若不存在有意义的参数或返回值，则可以改用 {moduleTerm}`Unit` 类型来表示。
如果 {moduleTerm}`Bool` 表示一位信息，那么 {moduleTerm}`Unit` 表示零位信息。

{moduleTerm}`IO α` 是一种程序的类型：该程序在执行时，要么抛出异常，要么返回一个类型为 {moduleTerm}`α` 的值。
在执行期间，该程序可能具有副作用。
这些程序称为 {moduleTerm}`IO` _动作_。
Lean 区分表达式的_求值_与 {anchorTerm sig}`IO` 动作的_执行_：前者严格遵循数学模型，即以值替换变量并化简子表达式，且不产生副作用；后者依赖外部系统与现实世界交互。
{moduleTerm}`IO.println` 是一个从字符串到 {moduleTerm}`IO` 动作的函数；这些动作在执行时会将给定字符串写入标准输出。
由于该动作在输出字符串的过程中不会从环境读取任何有意义的信息，{moduleTerm}`IO.println` 的类型为 {moduleTerm}`String → IO Unit`。
如果它确实返回某种有意义的内容，那么这将通过 {moduleTerm}`IO` 动作具有不同于 {moduleTerm}`Unit` 的类型来表示。



# 函数式编程与效应
%%%
tag := "fp-effects"
file := "Functional-Programming-vs-Effects"
%%%

Lean 的计算模型基于对数学表达式的求值，在其中变量被赋予恰好一个值，并且该值不会随时间改变。
对一个表达式求值所得的结果不会改变，再次对同一表达式求值总会得到相同的结果。

另一方面，有用的程序必须与外部世界交互。
一个既不执行输入也不执行输出的程序，无法向用户请求数据、在磁盘上创建文件，或打开网络连接。
Lean 是用 Lean 自身编写的，而 Lean 编译器当然会读取文件、创建文件，并与文本编辑器交互。
在一种同一表达式总是产生同一结果的语言中，如何支持从磁盘读取文件的程序，尤其是这些文件的内容可能会随时间变化？

通过稍微换一种方式思考副作用，可以化解这个表面上的矛盾。
设想一家出售咖啡和三明治的咖啡馆。
这家咖啡馆有两名员工：一名负责完成订单的厨师，以及一名在柜台与顾客交互并提交订单单据的员工。
厨师性格乖戾，确实不愿与外界有任何接触，但非常擅长稳定地交付这家咖啡馆赖以成名的食物和饮品。
然而，为了做到这一点，厨师需要安静和不受打扰，不能被谈话干扰。
柜台员工很友善，但在厨房里完全不称职。
顾客与柜台员工交互，而柜台员工把所有实际的烹饪工作委托给厨师。
如果厨师有问题要问顾客，例如澄清某种过敏情况，他们会给柜台员工递一张小纸条；柜台员工再与顾客交互，并把带有结果的纸条传回给厨师。

在这个类比中，厨师就是 Lean 语言。
当给出一份点单时，厨师会忠实且一致地交付所请求的内容。
柜台工作人员则是周围的运行时系统，它与外部世界交互，能够收款、分发食物并与顾客交谈。
两名员工协同工作，承担餐馆的全部功能，但他们的职责是分开的，各自执行其最擅长的任务。
正如让顾客远离厨师可以使厨师专注于制作真正出色的咖啡和三明治一样，Lean 缺乏副作用这一点使程序能够作为形式化数学证明的一部分使用。
这也有助于程序员彼此独立地理解程序的各个部分，因为不存在隐藏的状态变化会在组件之间造成微妙的耦合。
厨师的便条表示通过求值 Lean 表达式而产生的 {moduleTerm}`IO` 动作，而柜台工作人员的回应则是从效应传回的值。

这种副作用模型与 Lean 语言整体、其编译器以及其运行时系统（RTS）的工作方式相当类似。
运行时系统中的原语用 C 编写，实现所有基本效应。
运行程序时，RTS 调用 {moduleTerm}`main` 动作，该动作向 RTS 返回新的 {moduleTerm}`IO` 动作以供执行。
RTS 执行这些动作，并委托用户的 Lean 代码完成计算。
从 Lean 的内部视角看，程序没有副作用，而 {moduleTerm}`IO` 动作只是对待执行任务的描述。
从程序用户的外部视角看，存在一层副作用，它为程序的核心逻辑创建了一个接口。


# 现实世界中的函数式编程
%%%
tag := "fp-world-passing"
file := "Real-World-Functional-Programming"
%%%


理解 Lean 中副作用的另一种有用方式，是把 {moduleTerm}`IO` 动作看作以整个世界为参数，并返回一个值以及一个新世界的函数。
在这种情况下，从标准输入读取一行文本_是_一个纯函数，因为每次都会提供一个不同的世界作为参数。
向标准输出写入一行文本也是一个纯函数，因为该函数返回的世界不同于它开始时的世界。
程序确实需要小心，绝不能重用世界，也不能未能返回一个新世界——毕竟，这将等同于时间旅行或世界的终结。
谨慎的抽象边界可以使这种编程风格变得安全。
如果每个原始 {moduleTerm}`IO` 动作都接受一个世界并返回一个新的世界，并且它们只能用保持这一不变式的工具组合，那么这个问题就不会发生。

这个模型无法实现。
毕竟，整个宇宙不可能被转换为一个 Lean 值并放入内存。
不过，可以用一个代表世界的抽象令牌来实现该模型的一个变体。
当程序启动时，会向它提供一个世界令牌。
随后这个令牌被传递给 IO 原语，而这些原语返回的令牌也同样被传递给下一步。
在程序结束时，该令牌被返回给操作系统。

这种副作用模型很好地描述了 Lean 内部如何表示 {moduleTerm}`IO` 动作：它们是由 RTS 执行的任务描述。
实际转换真实世界的函数位于抽象屏障之后。
但真实程序通常由一系列效果组成，而不只是一个效果。
为了使程序能够使用多个效果，Lean 中有一种称为 {kw}`do` 记法的子语言，它允许将这些原始的 {moduleTerm}`IO` 动作安全地组合成更大的、有用的程序。

# 组合 {anchorName all}`IO` 动作
%%%
tag := "combining-io-actions"
file := "Combining-IO-Actions"
%%%

大多数有用的程序除了产生输出之外还接受输入。
此外，它们可能基于输入作出决策，将输入数据作为计算的一部分。
下面这个名为 {lit}`HelloName.lean` 的程序会询问用户的姓名，然后向用户问候：

```module (anchor:=all)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy

  stdout.putStrLn s!"Hello, {name}!"
```

在这个程序中，{anchorName all}`main` 动作由一个 {kw}`do` 块组成。
该块包含一系列_语句_，它们既可以是局部变量（使用 {kw}`let` 引入），也可以是将要执行的动作。
正如 SQL 可以被看作一种用于与数据库交互的专用语言一样，{kw}`do` 语法也可以被看作 Lean 内部的一种专用子语言，专门用于建模命令式程序。
用 {kw}`do` 块构造的 {anchorName all}`IO` 动作通过按顺序执行其中的语句来执行。

这个程序可以用与前一个程序相同的方式运行；这里用管道输入模拟用户键入的名字：

{command helloName "hello-name" "printf 'David\n' | lean --run HelloName.lean" (show := "lean --run HelloName.lean") (shell := true)}

如果用户以 {lit}`David` 作答，则与该程序的一次交互会读作：

```commandOut helloName "printf 'David\n' | lean --run HelloName.lean"
How would you like to be addressed?
Hello, David!
```

类型签名这一行与 {lit}`Hello.lean` 的类型签名一样：
```module (anchor:=sig)
def main : IO Unit := do
```
唯一的区别在于，它以关键字 {moduleTerm}`do` 结尾，而该关键字会启动一系列命令。
关键字 {kw}`do` 之后的每个缩进行都属于同一命令序列。

前两行如下：
```module (anchor:=setup)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
```

分别通过执行库动作 {moduleTerm (anchor := setup)}`IO.getStdin` 和 {moduleTerm (anchor := setup)}`IO.getStdout` 来取得 {moduleTerm (anchor := setup)}`stdin` 和 {moduleTerm (anchor := setup)}`stdout` 句柄。
在 {moduleTerm}`do` 块中，{moduleTerm}`let` 的含义与其在普通表达式中的含义略有不同。
通常，{moduleTerm}`let` 中的局部定义只能在紧随该局部定义之后的一个表达式中使用。
在 {moduleTerm}`do` 块中，由 {moduleTerm}`let` 引入的局部绑定可用于 {moduleTerm}`do` 块剩余部分中的所有语句，而不只是下一条语句。
此外，{moduleTerm}`let` 通常使用 {lit}`:=` 将被定义的名称与其定义连接起来，而 {moduleTerm}`do` 中的一些 {moduleTerm}`let` 绑定则使用左箭头（{lit}`←` 或 {lit}`<-`）。
使用箭头意味着箭头右侧表达式的值是一个应当执行的 {moduleTerm}`IO` 动作，并将该动作的结果保存在局部变量中。
换言之，如果箭头右侧的表达式具有类型 {moduleTerm}`IO α`，那么在 {moduleTerm}`do` 块的剩余部分中，该变量具有类型 {moduleTerm}`α`。
{moduleTerm (anchor := setup)}`IO.getStdin` 和 {moduleTerm (anchor := setup)}`IO.getStdout` 是 {moduleTerm (anchor := sig)}`IO` 动作，这是为了允许在程序中对 {moduleTerm (anchor := setup)}`stdin` 和 {moduleTerm (anchor := setup)}`stdout` 进行局部覆盖，这可能很方便。
如果它们像 C 中那样是全局变量，那么就不存在有意义的方式来覆盖它们；但 {moduleName}`IO` 动作每次执行时都可以返回不同的值。

{moduleTerm}`do` 块的下一部分负责询问用户的姓名：

```module (anchor:=question)
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
```

第一行将问题写入 {moduleTerm (anchor := setup)}`stdout`，第二行从 {moduleTerm (anchor := setup)}`stdin` 请求输入，第三行从输入行中移除末尾的换行符（以及任何其他末尾空白）。
{moduleTerm (anchor := question)}`name` 的定义使用 {lit}`:=`，而不是 {lit}`←`，因为 {lit}`toSlice`、{lit}`trimAsciiEnd` 与 {lit}`copy` 组合成的是普通的字符串计算，而不是一个 {moduleTerm (anchor := sig)}`IO` 动作。

最后，程序中的最后一行是：
```module (anchor:=answer)
  stdout.putStrLn s!"Hello, {name}!"
```

它使用{ref "string-interpolation"}[字符串插值]将给定的名称插入问候字符串，并将结果写入 {moduleTerm (anchor := setup)}`stdout`。
