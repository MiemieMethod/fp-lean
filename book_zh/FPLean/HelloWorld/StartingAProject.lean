import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples/second-lake/greeting"
set_option verso.exampleModule "Main"

#doc (Manual) "开始一个项目" =>
%%%
tag := "starting-a-project"
file := "Starting-a-Project"
%%%

随着用 Lean 编写的程序变得更加严肃，基于预先编译器并生成可执行文件的工作流会变得更有吸引力。
与其他语言一样，Lean 也有用于构建多文件包和管理依赖项的工具。
标准的 Lean 构建工具称为 Lake（“Lean Make”的缩写）。
Lake 通常使用 TOML 文件进行配置，该文件以声明式方式指定依赖项并描述要构建的内容。
对于高级用例，Lake 也可以用 Lean 本身进行配置。

# 最初步骤
%%%
tag := "lake-new"
file := "First-steps"
%%%


要开始一个使用 Lake 的项目，请在一个尚未包含名为 {lit}`greeting` 的文件或目录的目录中使用命令 {command lake "first-lake"}`lake new greeting`。
这会创建一个名为 {lit}`greeting` 的目录，其中包含以下文件：

 * {lit}`Main.lean` 是 Lean 编译器将在其中查找 {lit}`main` 动作的文件。
 * {lit}`Greeting.lean` 和 {lit}`Greeting/Basic.lean` 是该程序的支持库的脚手架。
 * {lit}`lakefile.toml` 包含 {lit}`lake` 构建该应用程序所需的配置。
 * {lit}`lean-toolchain` 包含用于该项目的特定 Lean 版本的标识符。

此外，{lit}`lake new` 会将项目初始化为一个 Git 仓库，并配置其 {lit}`.gitignore` 文件以忽略中间构建产物。
通常，应用程序逻辑的大部分会位于该程序的一组库中，而 {lit}`Main.lean` 会包含围绕这些部分的一个小包装器，用来完成解析命令行和执行核心应用程序逻辑等事情。
若要在一个已经存在的目录中创建项目，请运行 {lit}`lake init` 而不是 {lit}`lake new`。

默认情况下，库文件 {lit}`Greeting/Basic.lean` 包含一个单一定义：
```file lake "first-lake/greeting/Greeting/Basic.lean" "Greeting/Basic.lean"
def hello := "world"
```

库文件 {lit}`Greeting.lean` 导入 {lit}`Greeting/Basic.lean`：
```file lake "first-lake/greeting/Greeting.lean" "Greeting.lean"
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

这意味着，{lit}`Greeting/Basic.lean` 中定义的所有内容也可用于导入 {lit}`Greeting.lean` 的文件。
在 {kw}`import` 语句中，点号被解释为磁盘上的目录。

可执行文件源代码 {lit}`Main.lean` 包含：
```file lake "first-lake/greeting/Main.lean" "Main.lean"
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

因为 {lit}`Main.lean` 导入 {lit}`Greeting.lean`，而 {lit}`Greeting.lean` 导入 {lit}`Greeting/Basic.lean`，所以 {lit}`hello` 的定义在 {lit}`main` 中可用。

要构建该包，请运行命令 {command lake "first-lake/greeting"}`lake build`。
在若干构建命令滚动显示之后，生成的二进制文件已被放置在 {lit}`.lake/build/bin` 中。
运行 {command lake "first-lake/greeting" (shell := true)}`./.lake/build/bin/greeting` 会得到 {commandOut lake}`./.lake/build/bin/greeting`。
除了直接运行该二进制文件之外，还可以使用命令 {lit}`lake exe` 在必要时构建该二进制文件并随后运行它。
运行 {lit}`lake exe greeting` 也会得到 {commandOut lake}`./.lake/build/bin/greeting`。


# Lakefile
%%%
tag := "lakefiles"
file := "Lakefiles"
%%%

{lit}`lakefile.toml` 描述一个_包_，即用于分发的一组协调一致的 Lean 代码，类似于 {lit}`npm` 或 {lit}`nuget` 包，或 Rust crate。
一个包可以包含任意数量的库或可执行文件。
[Lake 文档](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml)描述了 Lake 配置中可用的选项。
生成的 {lit}`lakefile.toml` 包含以下内容：
```file lake "first-lake/greeting/lakefile.toml" "lakefile.toml"
name = "greeting"
version = "0.1.0"
defaultTargets = ["greeting"]

[[lean_lib]]
name = "Greeting"

[[lean_exe]]
name = "greeting"
root = "Main"
```


这个初始的 Lake 配置由三项组成：
 * 文件顶部的 _package_ 设置，
 * 一个名为 {lit}`Greeting` 的_库_声明，以及
 * 一个名为 {lit}`greeting` 的_可执行文件_。

每个 Lake 配置文件都将恰好包含一个包，但可以包含任意数量的依赖项、库或可执行文件。
按照惯例，包名和可执行文件名以小写字母开头，而库名以大写字母开头。
依赖项是对其他 Lean 包的声明（这些包可以位于本地，也可以来自远程 Git 仓库）。
Lake 配置文件中的条目允许配置诸如源文件位置、模块层次结构和编译器标志等内容。
然而，一般来说，默认设置是合理的。
用 Lean 格式编写的 Lake 配置文件还可以包含_外部库_，即不是用 Lean 编写、但要与生成的可执行文件静态链接的库；_自定义目标_，即不能自然归入库/可执行文件分类的构建目标；以及_脚本_，它们本质上是 {moduleName}`IO` 动作（类似于 {moduleName}`main`），但还额外能够访问关于包配置的元数据。

库、可执行文件和自定义目标都称为_目标_。
默认情况下，{lit}`lake build` 构建 {lit}`defaultTargets` 列表中指定的那些目标。
若要构建不是默认目标的目标，请在 {lit}`lake build` 之后将该目标的名称指定为参数。

# 库与导入
%%%
tag := "libraries-and-imports"
file := "Libraries-and-Imports"
%%%

Lean 库由一组按层次组织的源文件构成，可以从这些源文件中导入名称；这些源文件称为_模块_。
默认情况下，一个库有一个与其名称相匹配的根文件。
在本例中，库 {lit}`Greeting` 的根文件是 {lit}`Greeting.lean`。
{lit}`Main.lean` 的第一行，即 {moduleTerm}`import Greeting`，使 {lit}`Greeting.lean` 的内容可在 {lit}`Main.lean` 中使用。

可以通过创建名为 {lit}`Greeting` 的目录并将模块文件放入其中，向库中添加其他模块文件。
这些名称可以通过将目录分隔符替换为点来导入。
例如，创建文件 {lit}`Greeting/Smile.lean`，其内容为：
```file lake "second-lake/greeting/Greeting/Smile.lean" "Greeting/Smile.lean"
def Expression.happy : String := "a big smile"
```

意味着 {lit}`Main.lean` 可以如下使用该定义：
```file lake "second-lake/greeting/Main.lean" "Main.lean"
import Greeting
import Greeting.Smile

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```


模块名称层次结构与命名空间层次结构是解耦的。
在 Lean 中，模块是代码分发的单位，而命名空间是代码组织的单位。
也就是说，在模块 {lit}`Greeting.Smile` 中定义的名称并不会自动位于相应的命名空间 {lit}`Greeting.Smile` 中。
特别地，{moduleName (module:=Greeting.Smile) (show:=happy)}`Expression.happy` 位于 {lit}`Expression` 命名空间中。
模块可以按自己的意愿将名称放入任何命名空间，而导入它们的代码可以选择是否 {kw}`open` 该命名空间。
{kw}`import` 用于使源文件的内容可用，而 {kw}`open` 则使来自某个命名空间的名称在当前上下文中无需前缀即可使用。

{moduleTerm}`open Expression` 这一行使名称 {moduleName (module:=Greeting.Smile)}`Expression.happy` 在 {moduleName}`main` 中可作为 {moduleName}`happy` 访问。
命名空间也可以被_选择性地_打开，使其中只有一部分名称无需显式前缀即可使用。
这是通过把所需名称写在圆括号中来完成的。
例如，{moduleTerm (module:=Aux)}`Nat.toFloat` 将一个自然数转换为 {moduleTerm (module:=Aux)}`Float`。
可以使用 {moduleTerm (module:=Aux)}`open Nat (toFloat)` 使其可作为 {moduleName (module:=Aux)}`toFloat` 使用。
