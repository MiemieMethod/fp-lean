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
%%%

:::paragraph
{moduleTerm}`do` 块可以逐行执行。从前一节的程序开始：

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

要执行使用 {anchorTerm block2}`←` 的 {kw}`let` 语句，首先求值箭头右侧的表达式（本例中是 {moduleTerm}`IO.getStdin`）。
因为这个表达式只是一个变量，所以查找其值。得到的值是内置的原语 {moduleTerm}`IO` 活动。
下一步是执行这个 {moduleTerm}`IO` 活动，得到一个表示标准输入流的值，其类型为 {moduleTerm}`IO.FS.Stream`。
然后在 {moduleTerm}`do` 块的其余部分中，标准输入与箭头左侧的名称（这里是 {anchorTerm line1}`stdin`）关联。

执行第二行 {anchor line2}`let stdout ← IO.getStdout` 的过程类似。
首先，求值表达式 {moduleTerm}`IO.getStdout`，产生一个将返回标准输出的 {moduleTerm}`IO` 活动。
接下来，执行这个活动，实际返回标准输出。
最后，将此值与 {moduleTerm}`do` 块的其余部分关联起来，并命名为 {anchorTerm line2}`stdout`。

# 提问
%%%
tag := "asking-a-question"
%%%

:::paragraph
现在已经有了 {anchorTerm line1}`stdin` 和 {anchorTerm line2}`stdout`，该代码块的其余部分包括一个问题和一个答案：
```anchor block3
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```
:::

块中的第一个语句 {anchor line3}`stdout.putStrLn "How would you like to be addressed?"` 由一个表达式组成。
要执行表达式，首先要对其求值。
在这种情况下，{moduleTerm}`IO.FS.Stream.putStrLn` 的类型是 {moduleTerm}`IO.FS.Stream → String → IO Unit`。
这意味着它是一个接受流和字符串的函数，返回一个 {moduleTerm}`IO` 活动。
表达式使用 {ref "behind-the-scenes"}[访问器记法] 进行函数调用。
此函数应用于两个参数：标准输出流和字符串。
表达式的值是一个 {moduleTerm}`IO` 活动，它将把字符串和换行符写入输出流。
找到这个值后，下一步是执行它，这会导致字符串和换行符实际写入 {anchorTerm setup}`stdout`。
仅由表达式组成的语句不引入任何新变量。

代码块中的下一个语句是 {anchor line4}`let input ← stdin.getLine`。
{moduleTerm}`IO.FS.Stream.getLine` 的类型是 {moduleTerm}`IO.FS.Stream → IO String`，这意味着它是从流到将返回字符串的 {moduleTerm}`IO` 活动的函数。
这又是访问器记法的一个例子。
执行这个 {moduleTerm}`IO` 活动，程序等待用户输入完整的一行。
假设用户写入 “{lit}`David`”。
得到的行（{lit}`"David\n"`）与 {anchorTerm block5}`input` 关联，其中转义序列 {lit}`\n` 表示换行符。

```anchor block5
  let name := input.toSlice.trimAsciiEnd.copy
  stdout.putStrLn s!"Hello, {name}!"
```

:::paragraph
下一行 {anchor line5}`let name := input.toSlice.trimAsciiEnd.copy` 是一个 {kw}`let` 语句。
与该程序中的其他 {kw}`let` 语句不同，它使用 {anchorTerm block5}`:=` 而不是 {anchorTerm line4}`←`。
这意味着表达式将被求值，但结果值不需要是 {moduleTerm}`IO` 活动，也不会被执行。
在这种情况下，{anchorTerm line5}`trimAsciiEnd` 返回一个切片，其中字符串末尾的空白字符都已被删除；随后 {anchorTerm line5}`copy` 将该切片复制为新的字符串。
例如，

```anchorTerm dropBang (module := Examples.HelloWorld)
#eval "Hello!!!".toSlice.dropEndWhile (· == '!') |>.copy
```

会产生

```anchorInfo dropBang (module := Examples.HelloWorld)
"Hello"
```

以及

```anchorTerm dropNonLetter (module := Examples.HelloWorld)
#eval "Hello...   ".toSlice.dropEndWhile (fun (c : Char) => not (c.isAlphanum)) |>.copy
```

产生

```anchorInfo dropNonLetter (module := Examples.HelloWorld)
"Hello"
```

其中所有非字母数字字符都从字符串的右侧被删除。
在程序的当前行中，空白字符（包括换行符）从输入字符串的右侧被删除，得到 {moduleTerm (module := Examples.HelloWorld)}`"David"`，它与 {anchorTerm block5}`name` 关联，用于块的其余部分。
:::

# 问候用户
%%%
tag := "greeting"
%%%

:::paragraph
{moduleTerm}`do` 块中剩下要执行的只有一个语句：
```anchor line6
  stdout.putStrLn s!"Hello, {name}!"
```
:::

传递给 {anchorTerm line6}`putStrLn` 的字符串参数通过字符串插值构造，产生字符串 {moduleTerm (module := Examples.HelloWorld)}`"Hello, David!"`。
由于这个语句是一个表达式，它被求值以产生一个 {moduleTerm}`IO` 活动，该活动将把这个字符串和换行符打印到标准输出。
一旦表达式被求值，生成的 {moduleTerm}`IO` 活动就被执行，产生问候语。

# {lit}`IO` 活动作为值
%%%
tag := "actions-as-values"
%%%


在上面的描述中，可能很难看出为什么求值表达式和执行 {moduleTerm}`IO` 活动之间的区别是必要的。
毕竟，每个活动都在产生后立即执行。
为什么不像其他语言那样在求值期间简单地执行副作用呢？

答案有两个。首先，将求值与执行分开意味着程序必须明确说明哪些函数可以产生副作用。由于没有副作用的程序部分更适合数学推理，无论是在程序员的头脑中还是使用 Lean 的形式化证明工具，这种分离可以更容易地避免错误。
其次，并非所有的 {moduleTerm}`IO` 活动都需要在产生时立即执行。在不执行活动的情况下提及活动的能力允许普通函数用作控制结构。

:::paragraph
例如，函数 {anchorName twice (module:=Examples.HelloWorld)}`twice` 接受一个 {moduleTerm}`IO` 活动作为其参数，返回一个将执行参数活动两次的新活动。

```anchor twice (module := Examples.HelloWorld)
def twice (action : IO Unit) : IO Unit := do
  action
  action
```

执行

```anchorTerm twiceShy (module := Examples.HelloWorld)
twice (IO.println "shy")
```

会打印出

```anchorInfo twiceShy (module := Examples.HelloWorld)
shy
shy
```

这可以推广为运行底层活动任意次数的版本：

```anchor nTimes (module := Examples.HelloWorld)
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
```
:::

:::paragraph
在 {moduleTerm (module := Examples.HelloWorld)}`Nat.zero` 的基本情况中，结果是 {moduleTerm (module := Examples.HelloWorld)}`pure ()`。
函数 {moduleTerm (module := Examples.HelloWorld)}`pure` 创建一个没有副作用的 {moduleTerm (module := Examples.HelloWorld)}`IO` 活动，但返回 {moduleTerm (module := Examples.HelloWorld)}`pure` 的参数，在本例中是 {moduleTerm (module := Examples.HelloWorld)}`Unit` 的构造器。
作为一个什么也不做且不返回任何有趣内容的活动，{moduleTerm (module := Examples.HelloWorld)}`pure ()` 既非常无聊又非常有用。
在递归步骤中，使用 {moduleTerm (module := Examples.HelloWorld)}`do` 块创建一个活动，该活动首先执行 {moduleTerm (module := Examples.HelloWorld)}`action`，然后执行递归调用的结果。
执行 {anchor nTimes3 (module := Examples.HelloWorld)}`#eval nTimes (IO.println "Hello") 3` 会产生以下输出：

```anchorInfo nTimes3 (module := Examples.HelloWorld)
Hello
Hello
Hello
```

:::

:::paragraph
除了将函数用作控制结构外，{moduleTerm (module := Examples.HelloWorld)}`IO` 活动是一等值的事实意味着它们可以保存在数据结构中以供以后执行。
例如，函数 {moduleName (module := Examples.HelloWorld)}`countdown` 接受一个 {moduleTerm (module := Examples.HelloWorld)}`Nat` 并返回未执行的 {moduleTerm (module := Examples.HelloWorld)}`IO` 活动列表，每个 {moduleTerm (module := Examples.HelloWorld)}`Nat` 对应一个：

```anchor countdown (module := Examples.HelloWorld)
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
```

这个函数没有副作用，不打印任何东西。
例如，它可以应用于一个参数，并且可以检查结果活动列表的长度：

```anchor from5  (module := Examples.HelloWorld)
def from5 : List (IO Unit) := countdown 5
```

这个列表包含六个元素（每个数字一个，加上零对应的 {moduleTerm (module := Examples.HelloWorld)}`"Blast off!"` 活动）：

```anchorTerm from5length (module := Examples.HelloWorld)
#eval from5.length
```

```anchorInfo from5length (module := Examples.HelloWorld)
6
```

:::

:::paragraph
函数 {moduleTerm (module := Examples.HelloWorld)}`runActions` 接受活动列表并构造一个按顺序运行所有活动的单个活动：

```anchor runActions (module := Examples.HelloWorld)
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions
```

其结构本质上与 {moduleName (module := Examples.HelloWorld)}`nTimes` 相同，除了不是为每个 {moduleName (module := Examples.HelloWorld)}`Nat.succ` 执行一个活动，而是要执行每个 {moduleName (module := Examples.HelloWorld)}`List.cons` 下的活动。
类似地，{moduleName (module := Examples.HelloWorld)}`runActions` 本身不运行活动。
它创建一个将运行它们的新活动，该活动必须放在作为 {moduleName (module := Examples.HelloWorld)}`main` 一部分执行的位置：

```anchor main (module := Examples.HelloWorld)
def main : IO Unit := runActions from5
```

运行这个程序会产生以下输出：

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
第一步是求值 {moduleName (module := Examples.HelloWorld)}`main`。这按如下方式进行：

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

得到的 {moduleTerm (module := Examples.HelloWorld)}`IO` 活动是一个 {moduleTerm (module := Examples.HelloWorld)}`do` 块。
然后一次执行 {moduleTerm (module := Examples.HelloWorld)}`do` 块的每个步骤，产生预期的输出。
最后一步 {moduleTerm (module := Examples.HelloWorld)}`pure ()` 没有任何效果，它的存在只是因为 {moduleTerm (module := Examples.HelloWorld)}`runActions` 的定义需要一个基本情况。
:::

# 练习
%%%
tag := "step-by-step-exercise"
%%%

:::paragraph
在纸上逐步执行以下程序：

```anchor ExMain (module := Examples.HelloWorld)
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
```

在逐步执行程序时，识别何时求值表达式以及何时执行 {moduleTerm (module := Examples.HelloWorld)}`IO` 活动。
当执行 {moduleTerm (module := Examples.HelloWorld)}`IO` 活动导致副作用时，写下来。
完成后，用 Lean 运行程序并仔细检查您对副作用的预测是否正确。
:::
