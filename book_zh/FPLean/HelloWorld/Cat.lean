import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "FelineLib"

example_module Examples.Cat

#doc (Manual) "实例：{lit}`cat`" =>
%%%
tag := "example-cat"
%%%

标准的 Unix 实用程序 {lit}`cat` 接受多个命令行选项，后跟零个或多个输入文件。
如果没有提供文件，或者其中一个是横线（{lit}`-`），那么它将标准输入作为相应的输入，而不是读取文件。
输入的内容会一个接一个地写入标准输出。
如果指定的输入文件不存在，这会在标准错误上注明，但 {lit}`cat` 会继续连接剩余的输入。
如果任何输入文件不存在，则返回非零退出代码。

本节描述了 {lit}`cat` 的简化版本，称为 {lit}`feline`。
与常用的 {lit}`cat` 版本不同，{lit}`feline` 没有用于编号行、指示非打印字符或显示帮助文本等功能的命令行选项。
此外，它无法从与终端设备关联的标准输入中读取多次。

要充分学习本节内容，请自己动手操作。复制粘贴代码示例是可以的，但最好手动输入它们。这使得学习输入代码、从错误中恢复以及解释编译器反馈的机械过程变得更加容易。

# 开始
%%%
tag := "example-cat-start"
%%%

实现 {lit}`feline` 的第一步是创建一个包并决定如何组织代码。
在这种情况下，因为程序非常简单，所有代码都将放在 {lit}`Main.lean` 中。
第一步是运行 {lit}`lake new feline`。
编辑 Lakefile 以删除库，并删除生成的库代码和从 {lit}`Main.lean` 中对它的引用。
完成这些后，{lit}`lakefile.toml` 应该包含：

```plainFile "feline/1/lakefile.toml"
name = "feline"
version = "0.1.0"
defaultTargets = ["feline"]

[[lean_exe]]
name = "feline"
root = "Main"
```

{lit}`Main.lean` 应该包含类似的内容：
```plainFile "feline/1/Main.lean"
def main : IO Unit :=
  IO.println s!"Hello, cats!"
```
或者，运行 {lit}`lake new feline exe` 指示 {lit}`lake` 使用不包含库部分的模板，使得无需编辑文件。

通过运行 {command feline1 "feline/1"}`lake build` 确保可以构建代码。


# 连接流
%%%
tag := "example-cat-streams"
%%%

现在已经构建了程序的基本骨架，是时候实际输入代码了。
{lit}`cat` 的正确实现可以用于无限的 IO 流，例如 {lit}`/dev/random`，这意味着它不能在输出之前将其输入读入内存。
此外，它不应一次处理一个字符，因为这会导致性能变差。相反，最好一次读取连续的数据块，一次将数据定向到标准输出。

第一步是决定要读取多大的块。
为了简单起见，这个实现使用保守的 20 KB 块。
{anchorName bufsize}`USize` 类似于 C 中的 {c}`size_t`——它是一个无符号整数类型，足够大以表示所有有效的数组大小。
```module (anchor:=bufsize)
def bufsize : USize := 20 * 1024
```


## 流
%%%
tag := "streams"
%%%

{lit}`feline` 的主要工作由 {anchorName dump}`dump` 完成，它一次读取一个块的输入，将结果转储到标准输出，直到抵达输入的末尾。
输入的结束由 {anchorName dump}`read` 返回空字节数组表示：
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

{anchorName dump}`dump` 函数被声明为偏函数 {anchorTerm dump}`partial`，因为它在不是立即小于参数的输入上递归调用自身。
当函数被声明为偏函数时，Lean 不要求证明它终止。
另一方面，偏函数也远不如正确性证明那样易于处理，因为在 Lean 的逻辑中允许无限循环会使其不健全。
然而，没有办法证明 {anchorName dump}`dump` 终止，因为无限输入（例如来自 {lit}`/dev/random`）意味着它实际上不会终止。
在这种情况下，没有其他选择只能将函数声明为 {anchorTerm dump}`partial`。

类型 {anchorName dump}`IO.FS.Stream` 表示 POSIX 流。
在幕后，它表示为一个结构体，该结构为每个 POSIX 流操作都有一个字段。
每个操作都表示为提供相应操作的 IO 活动：

```anchor Stream (module := Examples.Cat)
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
```

类型 {anchorName Stream (module:=Examples.Cat)}`BaseIO` 是 {anchorName Stream (module:=Examples.Cat)}`IO` 的变体，排除了运行时错误。
Lean 编译器包含 {anchorName Stream (module:=Examples.Cat)}`IO` 活动（例如在 {anchorName dump}`dump` 中调用的 {anchorName dump}`IO.getStdout`）来获取表示标准输入、标准输出和标准错误的流。
这些是 {anchorName Stream (module:=Examples.Cat)}`IO` 活动而不是普通定义，因为 Lean 允许在进程中替换这些标准 POSIX 流，这使得通过编写自定义的 {anchorName dump}`IO.FS.Stream` 来捕获程序输出到字符串等操作变得更容易。

{anchorName dump}`dump` 中的控制流本质上是一个 {lit}`while` 循环。
当调用 {anchorName dump}`dump` 时，如果流已到达文件末尾，{anchorTerm dump}`pure ()` 通过返回 {anchorName dump}`Unit` 的构造函数来终止函数。
如果流尚未到达文件末尾，则读取一个块，其内容被写入 {anchorName dump}`stdout`，之后 {anchorName dump}`dump` 直接调用自身。
递归调用继续，直到 {anchorTerm dump}`stream.read` 返回空字节数组，这表示文件结束。

当 {kw}`if` 表达式作为 {kw}`do` 中的语句出现时，如在 {anchorName dump}`dump` 中，{kw}`if` 的每个分支都被隐式提供一个 {kw}`do`。
换句话说，{kw}`else` 后面的步骤序列被视为要执行的 {anchorName dump}`IO` 活动序列，就像它们在开头有一个 {kw}`do` 一样。
在 {kw}`if` 分支中用 {kw}`let` 引入的名称只在其自己的分支中可见，在 {kw}`if` 外部不在作用域内。

调用 {anchorName dump}`dump` 时不会有耗尽堆栈空间的危险，因为递归调用作为函数的最后一步发生，其结果直接返回而不是被操作或计算。
这种递归被称为*尾递归*，在 {ref "tail-recursion"}[本书后面] 有更详细的描述。
由于编译的代码不需要保留任何状态，Lean 编译器可以将递归调用编译为跳转。

如果 {lit}`feline` 只是将标准输入重定向到标准输出，那么 {anchorName dump}`dump` 就足够了。
但是，它还需要能够打开作为命令行参数提供的文件并输出其内容。
当其参数是存在的文件名时，{anchorName fileStream}`fileStream` 返回读取文件内容的流。
当参数不是文件时，{anchorName fileStream}`fileStream` 发出错误并返回 {anchorName fileStream}`none`。
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
首先，通过在读取模式下打开文件来创建文件句柄。
Lean 文件句柄跟踪底层文件描述符。
当没有对文件句柄值的引用时，终结器会关闭文件描述符。
其次，使用 {anchorName fileStream}`IO.FS.Stream.ofHandle` 给文件句柄提供与 POSIX 流相同的接口，它用在文件句柄上工作的相应 {anchorName fileStream}`IO` 活动填充 {anchorName Names}`Stream` 结构的每个字段。

## 处理输入
%%%
tag := "handling-input"
%%%

{lit}`feline` 的主循环是另一个尾递归函数，称为 {anchorName process}`process`。
为了在任何输入无法读取时返回非零退出代码，{anchorName process}`process` 接受一个参数 {anchorName process}`exitCode`，它表示整个程序的当前退出代码。
此外，它还接受要处理的输入文件列表。
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

就像 {kw}`if` 一样，用作 {kw}`do` 中语句的 {kw}`match` 的每个分支都被隐式提供其自己的 {kw}`do`。

有三种可能性。
一种是没有更多文件需要处理，在这种情况下 {anchorName process}`process` 返回错误代码不变。
另一种是指定的文件名是 {anchorTerm process}`"-"`，在这种情况下 {anchorName process}`process` 转储标准输入的内容，然后处理剩余的文件名。
最后一种可能性是指定了实际的文件名。
在这种情况下，使用 {anchorName process}`fileStream` 尝试将文件作为 POSIX 流打开。
其参数被封装在 {lit}`⟨ ... ⟩` 中，因为 {anchorName Names}`FilePath` 是包含字符串的单字段结构。
如果文件无法打开，它会被跳过，对 {anchorName process}`process` 的递归调用将退出代码设置为 {anchorTerm process}`1`。
如果可以，则转储它，对 {anchorName process}`process` 的递归调用保持退出代码不变。

{anchorName process}`process` 不需要标记为 {kw}`partial`，因为它是结构递归的。
每个递归调用都提供输入列表的尾部，所有 Lean 列表都是有限的。
因此，{anchorName process}`process` 不会引入任何非终止性。

## main 函数
%%%
tag := "example-cat-main"
%%%

最后一步是编写 {anchorName main}`main` 活动。
与先前的示例不同，{lit}`feline` 中的 {anchorName main}`main` 是一个函数。
在 Lean 中，{anchorName main}`main` 可以有三种类型之一：
 * {anchorTerm Names}`main : IO Unit` 对应于无法读取命令行参数且始终以退出代码 {anchorTerm Names}`0` 表示成功的程序，
 * {anchorTerm Names}`main : IO UInt32` 对应于 C 中的 {c}`int main(void)`，用于没有参数但返回退出代码的程序，以及
 * {anchorTerm Names}`main : List String → IO UInt32` 对应于 C 中的 {c}`int main(int argc, char **argv)`，用于接受参数并发出成功或失败信号的程序。

如果没有提供参数，{lit}`feline` 应该从标准输入读取，就像使用单个 {anchorTerm main}`"-"` 参数调用一样。
否则，参数应该一个接一个地处理。
```module (anchor:=main)
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
```

# 喵！
%%%
tag := "example-cat-running"
%%%

:::paragraph
要检查 {lit}`feline` 是否工作，第一步是使用 {command feline2 "feline/2"}`lake build` 构建它。
首先，当不带参数调用时，它应该输出从标准输入接收的内容。
检查
```command feline2 "feline/2" (shell := true)
echo "It works!" | lake exe feline
```
输出 {commandOut feline2}`echo "It works!" | lake exe feline`。
:::

:::paragraph
其次，当使用文件作为参数调用时，它应该打印它们。
如果文件 {lit}`test1.txt` 包含
```plainFile "feline/2/test1.txt"
It's time to find a warm spot
```

{lit}`test2.txt` 包含
```plainFile "feline/2/test2.txt"
and curl up!
```

那么命令

{command feline2 "feline/2" "lake exe feline test1.txt test2.txt"}

应该输出
```commandOut feline2 "lake exe feline test1.txt test2.txt"
It's time to find a warm spot
and curl up!
```
:::

最后，{lit}`-` 参数应该被适当处理。
```command feline2 "feline/2" (shell := true)
echo "and purr" | lake exe feline test1.txt - test2.txt
```

应该产生
```commandOut feline2 "echo \"and purr\" | lake exe feline test1.txt - test2.txt"
It's time to find a warm spot
and purr
and curl up!
```


# 练习
%%%
tag := "example-cat-exercise"
%%%

扩展 {lit}`feline` 使其支持用法信息。扩展版本应接受命令行参数 {lit}`--help`，产生关于可用命令行选项的文档并写入到标准输出。
