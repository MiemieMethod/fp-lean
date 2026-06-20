import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "FelineLib"


#doc (Manual) "额外的便利功能" =>
%%%
tag := "hello-world-conveniences"
%%%

# 嵌套活动
%%%
tag := "nested-actions"
%%%

:::paragraph
{lit}`feline` 中的许多函数都表现出一种重复模式，其中 {anchorName dump}`IO` 活动的结果被赋予一个名称，然后立即且仅使用一次。
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

模式出现在 {moduleName (anchor:=stdoutBind)}`stdout` 中：
```anchor stdoutBind
    let stdout ← IO.getStdout
    stdout.write buf
```

类似地，{moduleName}`fileStream` 包含以下代码片段：
```anchor fileExistsBind
  let fileExists ← filename.pathExists
  if not fileExists then
```
:::

:::paragraph
当 Lean 编译 {moduleTerm}`do` 块时，由括号下紧跟左箭头组成的表达式被提升到最近的封闭 {moduleTerm}`do`，它们的结果被绑定到唯一的名称。
这个唯一的名称替换表达式的原始位置。
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

这个版本的 {anchorName dump (module := Examples.Cat)}`dump` 避免了引入只使用一次的名称，这可以大大简化程序。
Lean 从嵌套表达式上下文中提升的 {moduleName (module := Examples.Cat)}`IO` 活动称为*嵌套活动*。
:::

:::paragraph
{moduleName (module := Examples.Cat)}`fileStream` 可以使用相同的技术来简化：

```anchor fileStream (module := Examples.Cat)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

在这种情况下，{anchorName fileStream (module := Examples.Cat)}`handle` 的局部名称也可以使用嵌套活动来消除，但生成的表达式会很长且复杂。
尽管使用嵌套活动通常是好的风格，但有时命名中间结果仍然是有帮助的。
:::

然而，重要的是要记住，嵌套活动只是在周围的 {moduleTerm (module := Examples.Cat)}`do` 块中出现的 {moduleName (module := Examples.Cat)}`IO` 活动的简短记法。
执行它们所涉及的副作用仍然以相同的顺序发生，副作用的执行不与表达式的求值交织在一起。
因此，嵌套活动不能从 {kw}`if` 的分支中提升。

作为这可能令人困惑的示例，考虑以下辅助定义，它们在向世界宣布已被执行后返回数据：

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

这些定义旨在替代更复杂的 {anchorName getNumB (module:=Examples.Cat)}`IO` 代码，这些代码可能验证用户输入、读取数据库或打开文件。

当数字 A 为五时打印 {moduleTerm (module := Examples.Cat)}`0`，否则打印数字 B 的程序可能如下所示：

```anchor testEffects (module := Examples.Cat)
def test : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

这个程序等效于：

```anchor testEffectsExpanded (module := Examples.Cat)
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

它无论 {moduleName (module := Examples.Cat)}`getNumA` 的结果是否等于 {moduleTerm (module := Examples.Cat)}`5` 都会运行 {moduleName (module := Examples.Cat)}`getNumB`。
为了防止这种混淆，嵌套活动不允许在不是 {moduleTerm (module := Examples.Cat)}`do` 中的行的 {kw}`if` 中使用，并产生以下错误消息：

```anchorError testEffects (module := Examples.Cat)
invalid use of `(<- ...)`, must be nested inside a 'do' expression
```


# {lit}`do` 的灵活布局
%%%
tag := "do-layout-syntax"
%%%

在 Lean 中，{moduleTerm (module := Examples.Cat)}`do` 表达式对空白敏感。
{moduleTerm (module := Examples.Cat)}`do` 中的每个 {moduleName (module := Examples.Cat)}`IO` 活动或局部绑定都应该在自己的行上开始，并且它们都应该有相同的缩进。
几乎所有的 {moduleTerm (module := Examples.Cat)}`do` 使用都应该这样写。
然而，在一些罕见的情况下，可能需要手动控制空白和缩进，或者在单行上有多个小活动可能会很方便。
在这些情况下，换行符可以用分号替换，缩进可以用大括号替换。

例如，以下所有程序都是等效的：

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


地道的 Lean 代码很少在 {moduleTerm (module := Examples.Cat)}`do` 中使用大括号。

# 使用 {kw}`#eval` 运行 {lit}`IO` 活动
%%%
tag := "eval-io"
%%%

Lean 的 {moduleTerm (module := Examples.Cat)}`#eval` 命令可以用来执行 {moduleName (module := Examples.Cat)}`IO` 活动，而不仅仅是求值它们。
通常，向 Lean 文件添加 {moduleTerm (module := Examples.Cat)}`#eval` 命令会使 Lean 求值提供的表达式，将结果值转换为字符串，并在工具提示和信息窗口中提供该字符串。
与因为 {moduleName (module := Examples.Cat)}`IO` 活动无法转换为字符串而失败不同，{moduleTerm (module := Examples.Cat)}`#eval` 执行它们，执行它们的副作用。
如果执行的结果是 {moduleName (module := Examples.Cat)}`Unit` 值 {moduleTerm (module := Examples.Cat)}`()`，则不显示结果字符串，但如果它是可以转换为字符串的类型，则 Lean 显示结果值。

:::paragraph
这意味着，给定 {moduleName (module := Examples.HelloWorld)}`countdown` 和 {moduleName (module := Examples.HelloWorld)}`runActions` 的先前定义，

```anchor evalDoesIO (module := Examples.HelloWorld)
#eval runActions (countdown 3)
```

会显示

```anchorInfo evalDoesIO (module := Examples.HelloWorld)
3
2
1
Blast off!
```
:::

这是运行 {moduleName (module := Examples.HelloWorld)}`IO` 活动产生的输出，而不是活动本身的某种不透明表示。
换句话说，对于 {moduleName (module := Examples.HelloWorld)}`IO` 活动，{moduleTerm (module := Examples.HelloWorld)}`#eval` 既*求值*提供的表达式又*执行*结果活动值。

使用 {moduleTerm (module := Examples.HelloWorld)}`#eval` 快速测试 {moduleName (module := Examples.HelloWorld)}`IO` 活动比编译和运行整个程序要方便得多。
然而，存在一些限制。
例如，从标准输入读取只是返回空输入。
此外，每当 Lean 需要更新它提供给用户的诊断信息时，{moduleName (module := Examples.HelloWorld)}`IO` 活动就会重新执行，这可能在不可预测的时间发生。
例如，读取和写入文件的活动可能会意外地这样做。
