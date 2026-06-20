import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples/second-lake/greeting"
set_option verso.exampleModule "Main"

#doc (Manual) "创建项目" =>
%%%
tag := "starting-a-project"
%%%

随着 Lean 中编写的程序变得越来越复杂，基于提前编译器（Ahead-of-Time，AoT）的工作流变得更具吸引力，
因为它可以生成可执行文件。与其他语言类似，Lean 具有构建多文件包和管理依赖项的工具。
标准的 Lean 构建工具称为 Lake（「Lean Make」的缩写）。
Lake 通常使用 TOML 文件进行配置，该文件声明性地指定依赖项并描述要构建的内容。
对于高级用例，Lake 也可以在 Lean 本身中进行配置。

# 入门
%%%
tag := "lake-new"
%%%


要创建一个使用 Lake 的项目，请在一个不包含名为 {lit}`greeting` 的文件或目录的目录下执行命令 {command lake "first-lake"}`lake new greeting`。
这将创建一个名为 {lit}`greeting` 的目录，其中包含以下文件：

 * {lit}`Main.lean` 是 Lean 编译器将查找 {lit}`main` 活动的文件。
 * {lit}`Greeting.lean` 和 {lit}`Greeting/Basic.lean` 是程序支持库的脚手架。
 * {lit}`lakefile.toml` 包含 {lit}`lake` 构建应用程序所需的配置。
 * {lit}`lean-toolchain` 包含项目使用的特定版本 Lean 的标识符。

此外，{lit}`lake new` 将项目初始化为 Git 存储库，并配置其 {lit}`.gitignore` 文件以忽略中间构建产物。
通常，应用程序逻辑的大部分将位于程序的库集合中，而 {lit}`Main.lean` 将包含围绕这些部分的小包装器，
执行诸如解析命令行和执行核心应用程序逻辑之类的操作。
要在已存在的目录中创建项目，请运行 {lit}`lake init` 而不是 {lit}`lake new`。

默认情况下，库文件 {lit}`Greeting/Basic.lean` 包含一个单独的定义：
```file lake "first-lake/greeting/Greeting/Basic.lean" "Greeting/Basic.lean"
def hello := "world"
```

库文件 {lit}`Greeting.lean` 导入 {lit}`Greeting/Basic.lean`：
```file lake "first-lake/greeting/Greeting.lean" "Greeting.lean"
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

这意味着在 {lit}`Greeting/Basic.lean` 中定义的所有内容也可用于导入 {lit}`Greeting.lean` 的文件。
在 {kw}`import` 语句中，点号被解释为磁盘上的目录。

可执行源文件 {lit}`Main.lean` 包含：
```file lake "first-lake/greeting/Main.lean" "Main.lean"
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

因为 {lit}`Main.lean` 导入 {lit}`Greeting.lean` 而 {lit}`Greeting.lean` 导入 {lit}`Greeting/Basic.lean`，
所以 {lit}`hello` 的定义在 {lit}`main` 中可用。

要构建这个包，请运行命令 {command lake "first-lake/greeting"}`lake build`。
若干构建命令滚动显示之后，生成的二进制文件会被放在 {lit}`.lake/build/bin` 中。
运行 {command lake "first-lake/greeting"}`./.lake/build/bin/greeting` 会得到 {commandOut lake}`./.lake/build/bin/greeting`。
除了直接运行二进制文件，也可以使用命令 {lit}`lake exe` 在必要时先构建二进制文件，然后运行它。
运行 {command lake "first-lake/greeting"}`lake exe greeting` 同样会得到 {commandOut lake}`lake exe greeting`。


# Lakefile 文件
%%%
tag := "lakefiles"
%%%

{lit}`lakefile.toml` 描述了一个*包*，它是用于分发的 Lean 代码的有条理集合，类似于 {lit}`npm` 或 {lit}`nuget` 包或 Rust crate。
包可以包含任意数量的库或可执行文件。
[Lake 的文档](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml)描述了 Lake 配置中的可用选项。
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


此初始的 Lake 配置包含三个项：
 * *包*配置，位于文件顶部，
 * 一个 *库* 声明，名为 {lit}`Greeting`，
 * 一个 *可执行文件*，名为 {lit}`greeting`。

每个 Lake 配置文件都将包含一个包，但可以有任意数量的依赖项、库或可执行文件。
按照惯例，包和可执行文件名以小写字母开头，而库名以大写字母开头。
依赖项是其他 Lean 包的声明（无论是本地的还是来自远程 Git 存储库的）
Lake 配置文件中的项目允许配置诸如源文件位置、模块层次结构和编译器标志等内容。
不过一般来说，默认值就够用了。
用 Lean 格式编写的 Lake 配置文件还可以包含*外部库*，这些是非 Lean 编写的库，要与生成的可执行文件静态链接；
*自定义目标*，这些是不适合库/可执行文件分类的构建目标；
以及*脚本*，它们本质上是 {moduleName}`IO` 动作（类似于 {moduleName}`main`），但另外还可以访问有关包配置的元数据。

库、可执行文件和自定义目标都称为 *目标（Target）*。
默认情况下，{lit}`lake build` 构建在 {lit}`defaultTargets` 列表中指定的目标。
要构建非默认目标，请在 {lit}`lake build` 后将目标名称指定为参数。

# 库和导入
%%%
tag := "libraries-and-imports"
%%%

Lean 库由分层组织的源文件集合组成，可以从中导入名称，称为*模块*。
默认情况下，库有一个与其名称匹配的单个根文件。
在这种情况下，库 {lit}`Greeting` 的根文件是 {lit}`Greeting.lean`。
{lit}`Main.lean` 的第一行 {moduleTerm}`import Greeting` 使 {lit}`Greeting.lean` 的内容在 {lit}`Main.lean` 中可用。

可以通过创建名为 {lit}`Greeting` 的目录并将其放在其中来向库添加其他模块文件。
可以通过将目录分隔符替换为点来导入这些名称。
例如，创建文件 {lit}`Greeting/Smile.lean` 并包含以下内容：
```file lake "second-lake/greeting/Greeting/Smile.lean" "Greeting/Smile.lean"
def Expression.happy : String := "a big smile"
```

这意味着 {lit}`Main.lean` 可以按如下方式使用定义：
```file lake "second-lake/greeting/Main.lean" "Main.lean"
import Greeting
import Greeting.Smile

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```


模块名称层次结构与命名空间层次结构分离。
在 Lean 中，模块是代码的分发单元，而命名空间是代码的组织单元。
也就是说，在模块 {lit}`Greeting.Smile` 中定义的名称不会自动位于相应的命名空间 {lit}`Greeting.Smile` 中。
特别是，{moduleName (module:=Greeting.Smile) (show:=happy)}`Expression.happy` 位于 {lit}`Expression` 命名空间中。
模块可以将名称放入任何它们喜欢的命名空间中，导入它们的代码可以 {kw}`open` 命名空间，也可以不这样做。
{kw}`import` 用于使源文件的内容可用，而 {kw}`open` 使命名空间中的名称在当前上下文中无需前缀即可使用。

{moduleTerm}`open Expression` 行使名称 {moduleName (module:=Greeting.Smile)}`Expression.happy` 在 {moduleName}`main` 中可以作为 {moduleName}`happy` 访问。
命名空间也可以*选择性地*打开，只让其中一些名称无需显式前缀即可使用。
这是通过将所需的名称写在括号中来完成的。
例如，{moduleTerm (module:=Aux)}`Nat.toFloat` 将自然数转换为 {moduleTerm (module:=Aux)}`Float`。
可以使用 {moduleTerm (module:=Aux)}`open Nat (toFloat)` 使其作为 {moduleName (module:=Aux)}`toFloat` 可用。
