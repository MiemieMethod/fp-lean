import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "FelineLib"

example_module Examples.Cat

#doc (Manual) "完整示例：{lit}`cat`" =>
%%%
tag := "example-cat"
file := "Worked-Example___-cat"
%%%

标准 Unix 实用程序 {lit}`cat` 接受若干命令行选项，随后是零个或多个输入文件。
如果没有提供文件，或者其中某个文件是短横线（{lit}`-`），那么它会将标准输入作为相应的输入，而不是读取文件。
这些输入的内容会依次写入标准输出。
如果某个指定的输入文件不存在，这一点会在标准错误上说明，但 {lit}`cat` 会继续连接其余输入。
如果任一输入文件不存在，则返回非零退出码。

本节描述 {lit}`cat` 的一个简化版本，称为 {lit}`feline`。
不同于常用版本的 {lit}`cat`，{lit}`feline` 没有用于诸如给行编号、标示非打印字符或显示帮助文本等功能的命令行选项。
此外，它不能从与终端设备相关联的标准输入中读取超过一次。

为了从本节获得最大收益，请亲自跟着操作。
复制粘贴代码示例是可以的，但更好的做法是手动输入它们。
这会使学习输入代码、从错误中恢复以及解释编译器反馈这些机械过程变得更容易。

# 入门
%%%
tag := "example-cat-start"
file := "Getting-Started"
%%%

实现 {lit}`feline` 的第一步是创建一个包，并决定如何组织代码。
在本例中，由于程序非常简单，所有代码都将放在 {lit}`Main.lean` 中。
第一步是运行 {lit}`lake new feline`。
编辑 Lakefile 以移除库，并删除生成的库代码以及 {lit}`Main.lean` 中对它的引用。
完成之后，{lit}`lakefile.toml` 应包含：

```plainFile "feline/1/lakefile.toml"
name = "feline"
version = "0.1.0"
defaultTargets = ["feline"]

[[lean_exe]]
name = "feline"
root = "Main"
```

并且 {lit}`Main.lean` 应包含类似如下的内容：
```plainFile "feline/1/Main.lean"
def main : IO Unit :=
  IO.println s!"Hello, cats!"
```
或者，运行 {lit}`lake new feline exe` 会指示 {lit}`lake` 使用一个不包含库部分的模板，从而无需编辑该文件。

通过运行 {command feline1 "feline/1"}`lake build` 来确保代码能够构建。


# 连接流
%%%
tag := "example-cat-streams"
file := "Concatenating-Streams"
%%%

既然程序的基本骨架已经构建完成，现在是实际输入代码的时候了。
{lit}`cat` 的正确实现可以用于无限 IO 流，例如 {lit}`/dev/random`，这意味着它不能在输出之前将其输入读入内存。
此外，它不应一次处理一个字符，因为这会导致令人沮丧的低性能。
相反，更好的做法是一次性读取连续的数据块，并将数据逐块定向到标准输出。

第一步是决定读取多大的块。
为简单起见，本实现使用保守的 20 千字节块。
{anchorName bufsize}`USize` 类似于 C 中的 {c}`size_t`——它是一种无符号整数类型，其大小足以表示所有有效的数组大小。
```module (anchor:=bufsize)
def bufsize : USize := 20 * 1024
```


## 流
%%%
tag := "streams"
file := "Streams"
%%%

{lit}`feline` 的主要工作由 {anchorName dump}`dump` 完成；它一次读取一个输入块，并将结果输出到标准输出，直到到达输入末尾。
输入末尾由 {anchorName dump}`read` 返回一个空字节数组来表示：
```module (anchor:=dump)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

函数 {anchorName dump}`dump` 被声明为 {anchorTerm dump}`partial`，因为它在并非立即小于某个参数的输入上递归调用自身。
当一个函数被声明为部分函数时，Lean 不要求证明它会终止。
另一方面，部分函数也更难用于正确性证明，因为在 Lean 的逻辑中允许无限循环会使其不可靠。
然而，没有办法证明 {anchorName dump}`dump` 会终止，因为无限输入（例如来自 {lit}`/dev/random` 的输入）意味着它事实上不会终止。
在这种情况下，除了将该函数声明为 {anchorTerm dump}`partial` 之外别无选择。

类型 {anchorName dump}`IO.FS.Stream` 表示一个 POSIX 流。
在幕后，它被表示为一个结构，该结构为每个 POSIX 流操作各有一个字段。
每个操作都表示为一个提供相应操作的 IO 动作：

```anchor Stream (module := Examples.Cat)
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
```

类型 {anchorName Stream (module:=Examples.Cat)}`BaseIO` 是 {anchorName Stream (module:=Examples.Cat)}`IO` 的一种变体，它排除了运行时错误。
Lean 编译器包含 {anchorName Stream (module:=Examples.Cat)}`IO` 动作（例如 {anchorName dump}`IO.getStdout`，它在 {anchorName dump}`dump` 中被调用），用于获取表示标准输入、标准输出和标准错误的流。
这些是 {anchorName Stream (module:=Examples.Cat)}`IO` 动作，而不是普通定义，因为 Lean 允许在进程中替换这些标准 POSIX 流，这使得诸如通过编写自定义 {anchorName dump}`IO.FS.Stream` 将程序输出捕获到字符串中这样的事情更容易完成。

{anchorName dump}`dump` 中的控制流本质上是一个 {lit}`while` 循环。
调用 {anchorName dump}`dump` 时，如果流已经到达文件末尾，{anchorTerm dump}`pure ()` 就通过返回 {anchorName dump}`Unit` 的构造子来终止函数。
如果流尚未到达文件末尾，则读取一个块，并将其内容写入 {anchorName dump}`stdout`，随后 {anchorName dump}`dump` 直接调用自身。
递归调用会持续进行，直到 {anchorTerm dump}`stream.read` 返回一个空字节数组，这表示文件结束。

当 {kw}`if` 表达式在 {kw}`do` 中作为语句出现时，如 {anchorName dump}`dump` 中那样，{kw}`if` 的每个分支都会被隐式提供一个 {kw}`do`。
换言之，跟在 {kw}`else` 后面的一系列步骤会被视为一系列要执行的 {anchorName dump}`IO` 动作，就像它们开头有一个 {kw}`do` 一样。
在 {kw}`if` 的分支中用 {kw}`let` 引入的名称只在其各自的分支中可见，在 {kw}`if` 外不在作用域内。

调用 {anchorName dump}`dump` 时不存在耗尽栈空间的危险，因为递归调用发生在函数的最后一步，并且其结果被直接返回，而不是再被操作或参与计算。
这种递归称为_尾递归_，本书{ref "tail-recursion"}[后文]将更详细地描述它。
由于编译后的代码不需要保留任何状态，Lean 编译器可以将递归调用编译为一次跳转。

如果 {lit}`feline` 只是将标准输入重定向到标准输出，那么 {anchorName dump}`dump` 就足够了。
然而，它还需要能够打开作为命令行参数提供的文件并输出其内容。
当它的参数是一个存在的文件名时，{anchorName fileStream}`fileStream` 返回一个读取该文件内容的流。
当该参数不是文件时，{anchorName fileStream}`fileStream` 会发出错误并返回 {anchorName fileStream}`none`。
```module (anchor:=fileStream)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

将文件作为流打开需要两个步骤。
首先，通过以读取模式打开文件来创建一个文件句柄。
Lean 文件句柄跟踪一个底层文件描述符。
当不存在对该文件句柄值的引用时，终结器会关闭该文件描述符。
其次，使用 {anchorName fileStream}`IO.FS.Stream.ofHandle` 为该文件句柄赋予与 POSIX 流相同的接口；{anchorName fileStream}`IO.FS.Stream.ofHandle` 会用对应的、作用于文件句柄的 {anchorName fileStream}`IO` 动作填充 {anchorName Names}`Stream` 结构的每个字段。

## 处理输入
%%%
tag := "handling-input"
file := "Handling-Input"
%%%

{lit}`feline` 的主循环是另一个尾递归函数，称为 {anchorName process}`process`。
为了在任一输入无法读取时返回非零退出码，{anchorName process}`process` 接受一个参数 {anchorName process}`exitCode`，它表示整个程序当前的退出码。
此外，它还接受一个待处理输入文件的列表。
```module (anchor:=process)
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args
```

正如 {kw}`if` 的情形一样，当 {kw}`match` 的每个分支在 {kw}`do` 中作为语句使用时，都会被隐式提供其自己的 {kw}`do`。

存在三种可能性。
一种是没有剩余文件需要处理，在这种情况下 {anchorName process}`process` 原样返回错误码。
另一种是指定的文件名为 {anchorTerm process}`"-"`，在这种情况下 {anchorName process}`process` 输出标准输入的内容，然后处理剩余的文件名。
最后一种可能性是指定了一个实际的文件名。
在这种情况下，使用 {anchorName process}`fileStream` 尝试将该文件作为 POSIX 流打开。
它的参数被包在 {lit}`⟨ ... ⟩` 中，因为 {anchorName Names}`FilePath` 是一个包含字符串的单字段结构。
如果文件无法打开，则跳过它，并且对 {anchorName process}`process` 的递归调用将退出码设置为 {anchorTerm process}`1`。
如果能够打开，则输出其内容，并且对 {anchorName process}`process` 的递归调用保持退出码不变。

{anchorName process}`process` 不需要标记为 {kw}`partial`，因为它是结构递归的。
每次递归调用都以输入列表的尾部作为参数，而所有 Lean 列表都是有限的。
因此，{anchorName process}`process` 不会引入任何非终止性。

## Main
%%%
tag := "example-cat-main"
file := "Main"
%%%

最后一步是编写 {anchorName main}`main` 动作。
与先前的示例不同，{lit}`feline` 中的 {anchorName main}`main` 是一个函数。
在 Lean 中，{anchorName main}`main` 可以具有以下三种类型之一：
 * {anchorTerm Names}`main : IO Unit` 对应于那些不能读取其命令行参数、并且总是以退出码 {anchorTerm Names}`0` 表示成功的程序，
 * 对于没有参数且返回退出码的程序，{anchorTerm Names}`main : IO UInt32` 对应于 C 中的 {c}`int main(void)`，并且
 * 对于接受参数并用成功或失败作为信号的程序，{anchorTerm Names}`main : List String → IO UInt32` 对应于 C 中的 {c}`int main(int argc, char **argv)`。

如果没有提供任何参数，{lit}`feline` 应当从标准输入读取，就好像它是以单个 {anchorTerm main}`"-"` 参数调用的一样。
否则，应当依次处理这些参数。
```module (anchor:=main)
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
```

# Meow!
%%%
tag := "example-cat-running"
file := "Meow___"
%%%

:::paragraph
要检查 {lit}`feline` 是否工作，第一步是用 {command feline2 "feline/2"}`lake build` 构建它。
首先，当不带参数调用时，它应当输出从标准输入接收到的内容。
检查
```command feline2 "feline/2" (shell := true)
echo "It works!" | lake exe feline
```
发出 {commandOut feline2}`echo "It works!" | lake exe feline`。
:::

:::paragraph
其次，当以文件作为参数调用它时，它应打印这些文件。
如果文件 {lit}`test1.txt` 包含
```plainFile "feline/2/test1.txt"
It's time to find a warm spot
```

并且 {lit}`test2.txt` 包含
```plainFile "feline/2/test2.txt"
and curl up!
```

则命令

{command feline2 "feline/2" "lake exe feline test1.txt test2.txt"}

应当输出
```commandOut feline2 "lake exe feline test1.txt test2.txt"
It's time to find a warm spot
and curl up!
```
:::

最后，应当适当地处理 {lit}`-` 参数。
```command feline2 "feline/2" (shell := true)
echo "and purr" | lake exe feline test1.txt - test2.txt
```

应产生
```commandOut feline2 "echo \"and purr\" | lake exe feline test1.txt - test2.txt"
It's time to find a warm spot
and purr
and curl up!
```


# 练习
%%%
tag := "example-cat-exercise"
file := "Exercise"
%%%

扩展 {lit}`feline`，使其支持用法信息。
扩展后的版本应接受命令行参数 {lit}`--help`，该参数会使关于可用命令行选项的文档被写入标准输出。
