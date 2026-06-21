import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "HelloName"

example_module Examples.HelloWorld



#doc (Manual) "逐步执行" =>
%%%
tag := "step-by-step"
file := "Step-By-Step"
%%%

:::paragraph
{moduleTerm}`do` 块可以逐行执行。
从上一节的程序开始：

```anchor block1
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```
:::

# 标准 IO
%%%
tag := "stdio"
file := "Standard-IO"
%%%

:::paragraph
第一行是 {anchor line1}`let stdin ← IO.getStdin`，而其余部分是：
```anchor block2
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```
:::

要执行一个使用 {anchorTerm block2}`←` 的 {kw}`let` 语句，首先对箭头右侧的表达式求值（在本例中为 {moduleTerm}`IO.getStdin`）。
由于该表达式只是一个变量，因此会查找其值。
所得的值是一个内建的原语 {moduleTerm}`IO` 动作。
下一步是执行这个 {moduleTerm}`IO` 动作，得到一个表示标准输入流的值，其类型为 {moduleTerm}`IO.FS.Stream`。
随后，在 {moduleTerm}`do` 块的剩余部分中，标准输入与箭头左侧的名称（此处为 {anchorTerm line1}`stdin`）关联起来。

执行第二行 {anchor line2}`let stdout ← IO.getStdout` 的过程类似。
首先，对表达式 {moduleTerm}`IO.getStdout` 求值，得到一个将返回标准输出的 {moduleTerm}`IO` 动作。
接着，执行该动作，实际返回标准输出。
最后，在 {moduleTerm}`do` 块的其余部分中，将这个值与名称 {anchorTerm line2}`stdout` 关联。

# 提出问题
%%%
tag := "asking-a-question"
file := "Asking-a-Question"
%%%

:::paragraph
既然已经找到了 {anchorTerm line1}`stdin` 和 {anchorTerm line2}`stdout`，该块的其余部分便由一个问题和一个回答组成：
```anchor block3
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```
:::

块中的第一条语句 {anchor line3}`stdout.putStrLn "How would you like to be addressed?"` 由一个表达式构成。
要执行一个表达式，首先要对其求值。
在此情形中，{moduleTerm}`IO.FS.Stream.putStrLn` 的类型是 {moduleTerm}`IO.FS.Stream → String → IO Unit`。
这意味着它是一个函数，接受一个流和一个字符串，并返回一个 {moduleTerm}`IO` 动作。
该表达式使用 {ref "behind-the-scenes"}[访问器记法]来进行函数调用。
这个函数被应用于两个参数：标准输出流和一个字符串。
该表达式的值是一个 {moduleTerm}`IO` 动作，它会把该字符串和一个换行字符写入输出流。
得到这个值之后，下一步就是执行它，这会使该字符串和换行符实际写入 {anchorTerm setup}`stdout`。
仅由表达式构成的语句不会引入任何新变量。

该块中的下一条语句是 {anchor line4}`let input ← stdin.getLine`。
{moduleTerm}`IO.FS.Stream.getLine` 的类型为 {moduleTerm}`IO.FS.Stream → IO String`，这意味着它是一个从流到 {moduleTerm}`IO` 动作的函数，而该动作将返回一个字符串。
这同样是访问器记法的一个例子。
执行这个 {moduleTerm}`IO` 动作后，程序会等待，直到用户键入一整行输入。
假设用户写入“{lit}`David`”。
所得的行（{lit}`"David\n"`）与 {anchorTerm block5}`input` 相关联，其中转义序列 {lit}`\n` 表示换行字符。

```anchor block5
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```

:::paragraph
下一行 {anchor line5}`let name := input.toSlice.trimAsciiEnd.copy` 是一个 {kw}`let` 语句。
与此程序中的其他 {kw}`let` 语句不同，它使用 {anchorTerm block5}`:=` 而不是 {anchorTerm line4}`←`。
这意味着该表达式将被求值，但所得的值不必是一个 {moduleTerm}`IO` 动作，也不会被执行。
在此情形中，{lit}`toSlice` 先把字符串转换为切片，{lit}`trimAsciiEnd` 移除其末尾的 ASCII 空白字符，最后 {lit}`copy` 将所得切片复制回新的字符串。
例如，

```anchorTerm dropBang (module := Examples.HelloWorld)
#eval "Hello!!!".toSlice.dropEndWhile (· == '!') |>.copy
```

产生

```anchorInfo dropBang (module := Examples.HelloWorld)
"Hello"
```

以及

```anchorTerm dropNonLetter (module := Examples.HelloWorld)
#eval "Hello...   ".toSlice.dropEndWhile (fun (c : Char) => not (c.isAlphanum)) |>.copy
```

得到

```anchorInfo dropNonLetter (module := Examples.HelloWorld)
"Hello"
```

其中字符串右侧的所有非字母数字字符都已被移除。
在程序的当前行中，空白字符（包括换行符）会从输入字符串的右侧被移除，得到 {moduleTerm (module := Examples.HelloWorld)}`"David"`，它在该代码块的其余部分中与 {anchorTerm block5}`name` 关联。
:::

# 问候用户
%%%
tag := "greeting"
file := "Greeting-the-User"
%%%

:::paragraph
在 {moduleTerm}`do` 块中剩下要执行的全部内容是一个单独的语句：
```anchor line6
  stdout.putStrLn s!"Hello, {name}!"
```
:::

传给 {anchorTerm line6}`putStrLn` 的字符串实参通过字符串插值构造，得到字符串 {moduleTerm (module := Examples.HelloWorld)}`"Hello, David!"`。
由于这条语句是一个表达式，它会被求值，得到一个 {moduleTerm}`IO` 动作；该动作会把这个字符串连同换行符打印到标准输出。
一旦表达式求值完成，所得的 {moduleTerm}`IO` 动作就会被执行，从而产生问候语。

# 作为值的 {lit}`IO` 动作
%%%
tag := "actions-as-values"
file := "IO-Actions-as-Values"
%%%


在上述描述中，可能很难看出为什么有必要区分表达式求值与 {moduleTerm}`IO` 动作执行。
毕竟，每个动作一经产生就立即执行。
为什么不直接在求值过程中执行这些效应，就像其他语言所做的那样呢？

答案有两个方面。
首先，将求值与执行分离，意味着程序必须明确指出哪些函数可能具有副作用。
程序中没有效应的部分更适合进行数学推理，无论这种推理是在程序员头脑中进行，还是使用 Lean 的形式化证明设施进行；因此，这种分离可以使避免缺陷变得更容易。
其次，并非所有 {moduleTerm}`IO` 动作都需要在它们产生时就被执行。
能够提及一个动作而不实际实施它，使得普通函数可以被用作控制结构。

:::paragraph
例如，函数 {anchorName twice (module:=Examples.HelloWorld)}`twice` 以一个 {moduleTerm}`IO` 动作为参数，返回一个新动作；该新动作会将作为参数的动作执行两次。

```anchor twice (module := Examples.HelloWorld)
def twice (action : IO Unit) : IO Unit := do
  action
  action
```

执行

```anchorTerm twiceShy (module := Examples.HelloWorld)
twice (IO.println "shy")
```

结果为

```anchorInfo twiceShy (module := Examples.HelloWorld)
shy
shy
```

被打印出来。
这可以推广为一个版本，使其可运行底层动作任意多次：

```anchor nTimes (module := Examples.HelloWorld)
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
```
:::

:::paragraph
在 {moduleTerm (module := Examples.HelloWorld)}`Nat.zero` 的基本情形中，结果是 {moduleTerm (module := Examples.HelloWorld)}`pure ()`。
函数 {moduleTerm (module := Examples.HelloWorld)}`pure` 创建一个没有副作用的 {moduleTerm (module := Examples.HelloWorld)}`IO` 动作，但返回 {moduleTerm (module := Examples.HelloWorld)}`pure` 的实参；在此处，该实参是 {moduleTerm (module := Examples.HelloWorld)}`Unit` 的构造子。
作为一个什么也不做且不返回任何有意义内容的动作，{moduleTerm (module := Examples.HelloWorld)}`pure ()` 同时极其乏味又非常有用。
在递归步骤中，使用 {moduleTerm (module := Examples.HelloWorld)}`do` 块创建一个动作，该动作先执行 {moduleTerm (module := Examples.HelloWorld)}`action`，然后执行递归调用的结果。
执行 {anchor nTimes3 (module := Examples.HelloWorld)}`#eval nTimes (IO.println "Hello") 3` 会产生如下输出：

```anchorInfo nTimes3 (module := Examples.HelloWorld)
Hello
Hello
Hello
```

:::

:::paragraph
除了将函数用作控制结构之外，{moduleTerm (module := Examples.HelloWorld)}`IO` 动作是一等值这一事实还意味着它们可以保存在数据结构中以供稍后执行。
例如，函数 {moduleName (module := Examples.HelloWorld)}`countdown` 接受一个 {moduleTerm (module := Examples.HelloWorld)}`Nat`，并返回一个尚未执行的 {moduleTerm (module := Examples.HelloWorld)}`IO` 动作列表，其中每个 {moduleTerm (module := Examples.HelloWorld)}`Nat` 对应一个动作：

```anchor countdown (module := Examples.HelloWorld)
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
```

此函数没有副作用，也不会打印任何内容。
例如，可以将它应用于一个参数，并检查所得动作列表的长度：

```anchor from5  (module := Examples.HelloWorld)
def from5 : List (IO Unit) := countdown 5
```

此列表包含六个元素（每个数字一个，另加一个用于零的 {moduleTerm (module := Examples.HelloWorld)}`"Blast off!"` 动作）：

```anchorTerm from5length (module := Examples.HelloWorld)
#eval from5.length
```

```anchorInfo from5length (module := Examples.HelloWorld)
6
```

:::

:::paragraph
函数 {moduleTerm (module := Examples.HelloWorld)}`runActions` 接受一个动作列表，并构造一个按顺序运行所有这些动作的单一动作：

```anchor runActions (module := Examples.HelloWorld)
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions
```

其结构本质上与 {moduleName (module := Examples.HelloWorld)}`nTimes` 的结构相同，只不过不再是对每个 {moduleName (module := Examples.HelloWorld)}`Nat.succ` 执行一个动作，而是执行每个 {moduleName (module := Examples.HelloWorld)}`List.cons` 下的动作。
类似地，{moduleName (module := Examples.HelloWorld)}`runActions` 本身并不运行这些动作。
它会创建一个将运行这些动作的新动作，而该动作必须被放置在某个位置，使其作为 {moduleName (module := Examples.HelloWorld)}`main` 的一部分被执行：

```anchor main (module := Examples.HelloWorld)
def main : IO Unit := runActions from5
```

运行该程序会得到如下输出：

```commands countdownFromFive ""
$ countdown
5
4
3
2
1
Blast off!
```

:::

:::paragraph
运行这个程序时会发生什么？
第一步是对 {moduleName (module := Examples.HelloWorld)}`main` 求值。其过程如下：

```anchorEvalSteps evalMain  (module := Examples.HelloWorld)
main
===>
runActions from5
===>
runActions (countdown 5)
===>
runActions
  [IO.println "5",
   IO.println "4",
   IO.println "3",
   IO.println "2",
   IO.println "1",
   IO.println "Blast off!"]
===>
do IO.println "5"
   IO.println "4"
   IO.println "3"
   IO.println "2"
   IO.println "1"
   IO.println "Blast off!"
   pure ()
```

所得的 {moduleTerm (module := Examples.HelloWorld)}`IO` 动作是一个 {moduleTerm (module := Examples.HelloWorld)}`do` 块。
随后，{moduleTerm (module := Examples.HelloWorld)}`do` 块的每一步会逐一执行，从而产生预期的输出。
最后一步 {moduleTerm (module := Examples.HelloWorld)}`pure ()` 没有任何效果；它之所以存在，仅仅是因为 {moduleTerm (module := Examples.HelloWorld)}`runActions` 的定义需要一个基例。
:::

# 练习
%%%
tag := "step-by-step-exercise"
file := "Exercise"
%%%

:::paragraph
请在纸上逐步推演以下程序的执行过程：

```anchor ExMain (module := Examples.HelloWorld)
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
```

在逐步跟踪程序执行时，请识别何时正在对表达式求值，以及何时正在执行一个 {moduleTerm (module := Examples.HelloWorld)}`IO` 动作。
当执行一个 {moduleTerm (module := Examples.HelloWorld)}`IO` 动作导致副作用时，请将其记录下来。
完成此操作后，用 Lean 运行该程序，并再次检查你关于副作用的预测是否正确。
:::
