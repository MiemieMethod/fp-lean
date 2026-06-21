import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "FelineLib"


#doc (Manual) "附加便利功能" =>
%%%
tag := "hello-world-conveniences"
file := "Additional-Conveniences"
%%%

# 嵌套动作
%%%
tag := "nested-actions"
file := "Nested-Actions"
%%%

:::paragraph
{lit}`feline` 中的许多函数都表现出一种重复模式：为某个 {anchorName dump}`IO` 动作的结果命名，然后立即且仅使用一次。
例如，在 {moduleName}`dump` 中：
```anchor dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

该模式出现在 {moduleName (anchor:=stdoutBind)}`stdout` 中：
```anchor stdoutBind
    let stdout ← IO.getStdout
    stdout.write buf
```

类似地，{moduleName}`fileStream` 包含以下片段：
```anchor fileExistsBind
  let fileExists ← filename.pathExists
  if not fileExists then
```
:::

:::paragraph
当 Lean 编译一个 {moduleTerm}`do` 块时，由紧接在圆括号之下的左箭头构成的表达式会被提升到最近的外层 {moduleTerm}`do`，并且其结果会被绑定到一个唯一名称。
这个唯一名称会替代表达式原来的位置。
这意味着 {moduleName (module := Examples.Cat)}`dump` 也可以写成如下形式：

```anchor dump (module:=Examples.Cat)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream
```

这个版本的 {anchorName dump (module := Examples.Cat)}`dump` 避免引入只使用一次的名称，这可以极大地简化程序。
Lean 从嵌套表达式上下文中提升出来的 {moduleName (module := Examples.Cat)}`IO` 动作称为_嵌套动作_。
:::

:::paragraph
{moduleName (module := Examples.Cat)}`fileStream` 可以用同样的技术加以简化：

```anchor fileStream (module := Examples.Cat)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

在这种情况下，也可以使用嵌套动作来消除 {anchorName fileStream (module := Examples.Cat)}`handle` 的局部名称，但所得表达式会很长且复杂。
尽管使用嵌套动作通常是良好的风格，有时为中间结果命名仍然可能有所帮助。
:::

然而，重要的是要记住，嵌套动作只是出现在外围 {moduleTerm (module := Examples.Cat)}`do` 块中的 {moduleName (module := Examples.Cat)}`IO` 动作的一种较短记法。
执行它们所涉及的副作用仍然按相同的顺序发生，并且副作用的执行不会与表达式求值交错进行。
因此，嵌套动作不能从 {kw}`if` 的分支中提升出来。

举一个可能令人困惑的例子，请考虑以下辅助定义：它们在向外界宣告自己已被执行之后返回数据。

```anchor getNumA (module := Examples.Cat)
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5
```

```anchor getNumB (module := Examples.Cat)
def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7
```

这些定义旨在替代更复杂的 {anchorName getNumB (module:=Examples.Cat)}`IO` 代码；这种代码可能会验证用户输入、读取数据库，或打开文件。

一个在数字 A 为五时打印 {moduleTerm (module := Examples.Cat)}`0`、否则打印数字 B 的程序，可以写成如下形式：

```anchor testEffects (module := Examples.Cat)
def test : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

这个程序等价于：

```anchor testEffectsExpanded (module := Examples.Cat)
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

它会运行 {moduleName (module := Examples.Cat)}`getNumB`，而不管 {moduleName (module := Examples.Cat)}`getNumA` 的结果是否等于 {moduleTerm (module := Examples.Cat)}`5`。
为防止这种混淆，不允许在并非自身就是 {moduleTerm (module := Examples.Cat)}`do` 中一行的 {kw}`if` 内使用嵌套动作，并会产生以下错误消息：

```anchorError testEffects (module := Examples.Cat)
invalid use of `(<- ...)`, must be nested inside a 'do' expression
```


# {lit}`do` 的灵活布局
%%%
tag := "do-layout-syntax"
file := "Flexible-Layouts-for-do"
%%%

在 Lean 中，{moduleTerm (module := Examples.Cat)}`do` 表达式对空白敏感。
{moduleTerm (module := Examples.Cat)}`do` 中的每个 {moduleName (module := Examples.Cat)}`IO` 动作或局部绑定都应从独立的一行开始，并且它们都应具有相同的缩进。
几乎所有 {moduleTerm (module := Examples.Cat)}`do` 的用法都应以这种方式书写。
然而，在某些少见的上下文中，可能需要手动控制空白和缩进，或者将多个小动作放在同一行会更方便。
在这些情况下，可以用分号替代换行，并用花括号替代缩进。

例如，以下所有程序都是等价的：

```anchor helloOne (module := Examples.Cat)
-- This version uses only whitespace-sensitive layout
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
```

```anchor helloTwo (module := Examples.Cat)
-- This version is as explicit as possible
def main : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trim;
  stdout.putStrLn s!"Hello, {name}!"
}
```

```anchor helloThree (module := Examples.Cat)
-- This version uses a semicolon to put two actions on the same line
def main : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"
```


惯用的 Lean 代码很少将花括号与 {moduleTerm (module := Examples.Cat)}`do` 一起使用。

# 使用 {kw}`#eval` 运行 {lit}`IO` 动作
%%%
tag := "eval-io"
file := "Running-IO-Actions-With-___eval"
%%%

Lean 的 {moduleTerm (module := Examples.Cat)}`#eval` 命令可用于执行 {moduleName (module := Examples.Cat)}`IO` 动作，而不只是对它们求值。
通常，在 Lean 文件中添加 {moduleTerm (module := Examples.Cat)}`#eval` 命令会使 Lean 对所给表达式求值，将所得值转换为字符串，并将该字符串作为工具提示以及在信息窗口中提供。
{moduleTerm (module := Examples.Cat)}`#eval` 不会因为 {moduleName (module := Examples.Cat)}`IO` 动作无法转换为字符串而失败，而是会执行它们，实施其副作用。
如果执行结果是 {moduleName (module := Examples.Cat)}`Unit` 值 {moduleTerm (module := Examples.Cat)}`()`，则不会显示结果字符串；但如果它是可以转换为字符串的类型，那么 Lean 会显示所得值。

:::paragraph
这意味着，在给定 {moduleName (module := Examples.HelloWorld)}`countdown` 和 {moduleName (module := Examples.HelloWorld)}`runActions` 先前定义的情况下，

```anchor evalDoesIO (module := Examples.HelloWorld)
#eval runActions (countdown 3)
```

显示

```anchorInfo evalDoesIO (module := Examples.HelloWorld)
3
2
1
Blast off!
```
:::

这是运行 {moduleName (module := Examples.HelloWorld)}`IO` 动作所产生的输出，而不是该动作本身的某种不透明表示。
换言之，对于 {moduleName (module := Examples.HelloWorld)}`IO` 动作，{moduleTerm (module := Examples.HelloWorld)}`#eval` 既会_求值_所提供的表达式，也会_执行_所得的动作值。

用 {moduleTerm (module := Examples.HelloWorld)}`#eval` 快速测试 {moduleName (module := Examples.HelloWorld)}`IO` 动作，可能比编译并运行整个程序方便得多。
然而，这也有一些限制。
例如，从标准输入读取只会返回空输入。
此外，每当 Lean 需要更新其提供给用户的诊断信息时，{moduleName (module := Examples.HelloWorld)}`IO` 动作都会被重新执行，而这可能发生在不可预测的时刻。
例如，一个读写文件的动作可能会出乎意料地这样做。
