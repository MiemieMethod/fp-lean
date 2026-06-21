import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Conveniences"

#doc (Manual) "额外便利" =>
%%%
tag := "monad-transformer-conveniences"
file := "Additional-Conveniences"
%%%

# 管道运算符
%%%
tag := "pipe-operators"
file := "Pipe-Operators"
%%%

函数通常写在其参数之前。
从左到右阅读程序时，这会促进一种视角，其中函数的_输出_至关重要——函数有一个要达成的目标（也就是要计算的值），并接收参数来在这一过程中支持它。
但是，有些程序更容易按如下方式理解：输入被逐步细化以产生输出。
对于这些情形，Lean 提供了一个_管道_运算符，它类似于 F# 提供的管道运算符。
管道运算符在与 Clojure 的线程宏相同的情形中很有用。

管道 {anchorTerm pipelineShort}`E₁ |> E₂` 是 {anchorTerm pipelineShort}`E₂ E₁` 的简写。
例如，对下列内容求值：
```anchor some5
#eval some 5 |> toString
```
得到：
```anchorInfo some5
"(some 5)"
```
虽然这种重点的改变可以使某些程序更便于阅读，但当管道包含许多组成部分时，它们才真正展现出自身的优势。

给定如下定义：

```anchor times3
def times3 (n : Nat) : Nat := n * 3
```
下面的管道：
```anchor itIsFive
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
```
产生：
```anchorInfo itIsFive
"It is 15"
```
更一般地，一系列管道 {anchorTerm pipeline}`E₁ |> E₂ |> E₃ |> E₄` 是嵌套函数应用 {anchorTerm pipeline}`E₄ (E₃ (E₂ E₁))` 的简写。

管道也可以反向书写。
在这种情况下，它们不会把数据变换的对象放在首位；然而，当大量嵌套括号给读者造成困难时，它们可以使应用的步骤更加清晰。
前面的例子可以等价地写成：
```anchor itIsAlsoFive
#eval ("It is " ++ ·) <| toString <| times3 <| 5
```
这是下列写法的缩写：
```anchor itIsAlsoFiveParens
#eval ("It is " ++ ·) (toString (times3 5))
```

Lean 的方法点记号使用点号前的类型名称来解析点号后运算符的命名空间，其作用与管道类似。
即使没有管道运算符，也可以写作 {anchorTerm listReverse}`[1, 2, 3].reverse`，而不是 {anchorTerm listReverse}`List.reverse [1, 2, 3]`。
然而，在使用许多带点函数时，管道运算符也很有用。
{anchorTerm listReverseDropReverse}`([1, 2, 3].reverse.drop 1).reverse` 也可以写作 {anchorTerm listReverseDropReverse}`[1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse`。
这个版本避免了仅仅因为表达式接受实参就必须给它们加括号，并且恢复了 Kotlin 或 C# 等语言中方法调用链的便利性。
然而，它仍然要求手动提供命名空间。
作为最后一项便利，Lean 提供了“管道点”运算符；它像管道一样对函数进行分组，但使用类型名称来解析命名空间。
使用“管道点”，该例子可以改写为 {anchorTerm listReverseDropReversePipe}`[1, 2, 3] |>.reverse |>.drop 1 |>.reverse`。

# 无限循环
%%%
tag := "infinite-loops"
file := "Infinite-Loops"
%%%

在 {kw}`do` 块内，{kw}`repeat` 关键字引入一个无限循环。
例如，一个不断发送字符串 {anchorTerm spam}`"Spam!"` 的程序可以使用它：

```anchor spam
def spam : IO Unit := do
  repeat IO.println "Spam!"
```
{kw}`repeat` 循环支持 {kw}`break` 和 {kw}`continue`，就像 {kw}`for` 循环一样。

来自 {ref "streams"}[{lit}`feline` 的实现]的 {anchorName dump (module := FelineLib)}`dump` 函数使用一个递归函数来永远运行：
```anchor dump (module := FelineLib)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```
使用 {kw}`repeat` 可以大幅缩短此函数：

```anchor dump
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf
```

{anchorName spam}`spam` 和 {anchorName dump}`dump` 都不需要声明为 {kw}`partial`，因为它们自身并不是无限递归的。
相反，{kw}`repeat` 使用了一种类型，其 {anchorTerm names}`ForM` 实例是 {kw}`partial`。
部分性不会“感染”调用函数。

# While 循环
%%%
tag := "while-loops"
file := "While-Loops"
%%%

在使用局部可变性编程时，{kw}`while` 循环可以作为 {kw}`repeat` 加上由 {kw}`if` 守卫的 {kw}`break` 的便捷替代：

```anchor dumpWhile
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
```
在幕后，{kw}`while` 只是 {kw}`repeat` 的一种更简单的记法。
