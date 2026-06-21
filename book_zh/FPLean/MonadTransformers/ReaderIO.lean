import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "DirTree"

#doc (Manual) "组合 IO 与 Reader" =>
%%%
tag := "io-reader"
file := "Combining-IO-and-Reader"
%%%

读者单子可能有用的一种情形是：应用程序存在某种“当前配置”的概念，并且该配置会在许多递归调用中传递。
这类程序的一个例子是 {lit}`tree`，它递归地打印当前目录及其子目录中的文件，并使用字符表示它们的树状结构。
本章中的 {lit}`tree` 版本称为 {lit}`doug`；这个名称源自装点北美西海岸的雄伟道格拉斯冷杉。它在表示目录结构时，可以选择使用 Unicode 制表符，也可以选择使用其 ASCII 等价形式。


例如，以下命令会在名为 {lit}`doug-demo` 的目录中创建一个目录结构和一些空文件：
```commands doug "doug-demo"
$$ cd doug-demo
$ mkdir -p a/b/c
$ mkdir -p a/d
$ mkdir -p a/e/f
$ touch a/b/hello
$ touch a/d/another-file
$ touch a/e/still-another-file-again
```
运行 {lit}`doug` 会得到如下结果：
```commands doug "doug-demo"
$ doug
├── doug-demo/
│   ├── a/
│   │   ├── b/
│   │   │   ├── c/
│   │   │   ├── hello
│   │   ├── d/
│   │   │   ├── another-file
│   │   ├── e/
│   │   │   ├── f/
│   │   │   ├── still-another-file-again
```

# 实现
%%%
tag := "reader-io-implementation"
file := "Implementation"
%%%

在内部，{lit}`doug` 在递归遍历目录结构时向下传递一个配置值。
此配置包含两个字段：{anchorName Config}`useASCII` 决定是使用 Unicode 盒绘制字符，还是使用 ASCII 竖线和短横线字符来表示结构；{anchorName Config}`currentPrefix` 包含一个要添加到每一行输出前面的字符串。
随着当前目录逐渐加深，前缀字符串会累积表示处于某个目录中的标记。
该配置是一个结构：

```anchor Config
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
```
这个结构为两个字段都提供了默认定义。
默认的 {anchorName Config}`Config` 使用 Unicode 显示，并且不带前缀。

:::paragraph
调用 {lit}`doug` 的用户需要能够提供命令行参数。
用法信息如下：

```anchor usage
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
```
因此，可以通过检查命令行参数列表来构造配置：

```anchor configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
```
:::

函数 {anchorName OldMain}`main` 是对一个内部工作函数的包装，该工作函数名为 {anchorName OldMain}`dirTree`，它使用某个配置显示目录内容。
在调用 {anchorName OldMain}`dirTree` 之前，{anchorName OldMain}`main` 负责处理命令行参数。
它还必须向操作系统返回适当的退出码：

```anchor OldMain
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
```
{anchorName OldMain}`IO.eprintln` 是 {anchorName OldShowFile}`IO.println` 的一个版本，它输出到标准错误。

并非所有路径都应显示在目录树中。
特别地，名为 {lit}`.` 或 {lit}`..` 的文件应当被跳过，因为它们实际上是用于导航的特性，而不是文件_本身_。
在那些应当显示的文件中，有两类：普通文件和目录：

```anchor Entry
inductive Entry where
  | file : String → Entry
  | dir : String → Entry
```
为了确定是否应显示某个文件，以及它属于哪一种条目，{lit}`doug` 使用 {anchorName toEntry}`toEntry`：

```anchor toEntry
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))
```
{anchorName names}`System.FilePath.components` 将路径转换为路径组成部分的列表，即在目录分隔符处分割名称。
如果没有最后一个组成部分，那么该路径就是根目录。
如果最后一个组成部分是特殊的导航文件（{lit}`.` 或 {lit}`..`），那么该文件应被排除。
否则，目录和文件会被包装在相应的构造子中。

Lean 的逻辑无法知道目录树是有限的。
事实上，有些系统允许构造循环的目录结构。
因此，{anchorName OldDirTree}`dirTree` 被声明为 {kw}`partial`：

```anchor OldDirTree
partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName cfg name
  | some (.dir name) =>
    showDirName cfg name
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList (contents.qsort dirLT).toList fun d =>
      dirTree newConfig d.path
```
对 {anchorName OldDirTree}`toEntry` 的调用是一个 {ref "nested-actions"}[嵌套动作]——在箭头不可能有其他含义的位置，括号是可选的，例如 {kw}`match`。
当文件名不对应于树中的条目时（例如因为它是 {lit}`..`），{anchorName OldDirTree}`dirTree` 不做任何事情。
当文件名指向普通文件时，{anchorName OldDirTree}`dirTree` 调用一个辅助函数，用当前配置显示它。
当文件名指向目录时，它会用一个辅助函数显示该目录，然后在一个新配置中递归显示其内容；在这个新配置中，前缀已被扩展以反映进入了一个新目录。
目录内容会被排序以使输出具有确定性，比较依据为 {anchorName compareEntries'}`dirLT`。
```anchor compareEntries'
def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
```

显示文件和目录的名称是通过 {anchorName OldShowFile}`showFileName` 和 {anchorName OldShowFile}`showDirName` 实现的：

```anchor OldShowFile
def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println (cfg.dirName dir)
```
这两个辅助函数都委托给 {anchorName filenames}`Config` 上的函数，后者会考虑 ASCII 与 Unicode 的设置：

```anchor filenames
def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
```
类似地，{anchorName inDirectory}`Config.inDirectory` 会用目录标记扩展前缀：

```anchor inDirectory
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
```

使用 {anchorName doList}`doList` 可以在目录内容列表上迭代一个 IO 动作。
由于 {anchorName doList}`doList` 会执行列表中的所有动作，并且不根据任何动作返回的值作出控制流决策，因此并不需要 {anchorName ConfigIO}`Monad` 的全部能力；它可用于任意 {anchorName doList}`Applicative`：

```anchor doList
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action
```


# 使用自定义单子
%%%
tag := "reader-io-custom-monad"
file := "Using-a-Custom-Monad"
%%%

虽然 {lit}`doug` 的这个实现能够工作，但手动传递配置既冗长又容易出错。
例如，如果向下传递了错误的配置，类型系统不会捕获这一点。
读取器效果确保同一配置会传递给所有递归调用，除非手动覆盖它，并且它有助于使代码不那么冗长。

要创建一个同时也是 {anchorName ConfigIO}`Config` 的读取器的 {anchorName ConfigIO}`IO` 版本，首先按照 {ref "custom-environments"}[求值器示例] 中的步骤定义类型及其 {anchorName ConfigIO}`Monad` 实例：

```anchor ConfigIO
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg
```
这个 {anchorName ConfigIO}`Monad` 实例与 {anchorName Reader (module := Examples.Monads.Class)}`Reader` 的实例之间的区别在于，此实例使用 {anchorName ConfigIO}`IO` 单子中的 {kw}`do`-记号作为 {anchorName ConfigIO}`bind` 返回的函数体，而不是将 {anchorName ConfigIO}`next` 直接应用于从 {anchorName ConfigIO}`result` 返回的值。
{anchorName ConfigIO}`result` 所执行的任何 {anchorName ConfigIO}`IO` 效应都必须在调用 {anchorName ConfigIO}`next` 之前发生，这由 {anchorName ConfigIO}`IO` 单子的 {anchorName ConfigIO}`bind` 运算符保证。
{anchorName ConfigIO}`ConfigIO` 不是宇宙多态的，因为其底层的 {anchorName ConfigIO}`IO` 类型也不是宇宙多态的。

运行一个 {anchorName ConfigIO}`ConfigIO` 动作，需要通过向其提供一个配置，将它转换为一个 {anchorName ConfigIO}`IO` 动作：

```anchor ConfigIORun
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
```
这个函数并非真正必要，因为调用者可以直接提供配置。
然而，为该操作命名可以使人更容易看出代码的哪些部分意图在哪个单子中运行。

下一步是定义一种在 {anchorName ConfigIO}`ConfigIO` 中访问当前配置的方法：

```anchor currentConfig
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
```
这与 {ref "custom-environments"}[求值器示例] 中的 {anchorName Reader (module := Examples.Monads.Class)}`read` 完全类似，只是它使用 {anchorName ConfigIO}`IO` 的 {anchorName ConfigIO}`pure` 来返回其值，而不是直接返回。
由于进入目录会在递归调用的作用域内修改当前配置，因此需要一种覆盖配置的方法：

```anchor locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
```

{lit}`doug` 中使用的大部分代码都不需要配置，而 {lit}`doug` 调用的是标准库中的普通 Lean {anchorName ConfigIO}`IO` 动作，它们当然不需要 {anchorName ConfigIO}`Config`。
普通的 {anchorName ConfigIO}`IO` 动作可以使用 {anchorName runIO}`runIO` 运行，后者会忽略配置参数：

```anchor runIO
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action
```

有了这些组件，{anchorName MedShowFileDir}`showFileName` 和 {anchorName MedShowFileDir}`showDirName` 就可以更新为通过 {anchorName ConfigIO}`ConfigIO` 单子隐式地获取其配置参数。
它们使用 {ref "nested-actions"}[嵌套动作] 来取得配置，并使用 {anchorName runIO}`runIO` 来实际执行对 {anchorName MedShowFileDir}`IO.println` 的调用：

```anchor MedShowFileDir
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
```

在 {anchorName MedDirTree}`dirTree` 的新版本中，对 {anchorName MedDirTree}`toEntry` 和 {anchorName MedDirTree}`readDir` 的调用被包装在 {anchorName runIO}`runIO` 中。
此外，它并不是先构造一个新的配置，再要求程序员跟踪应将哪一个配置传给递归调用，而是使用 {anchorName MedDirTree}`locally` 将被修改的配置自然地限定在程序的一个小区域内，在该区域中它是_唯一_有效的配置：

```anchor MedDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← runIO path.readDir
      locally (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```

新版 {anchorName MedMain}`main` 使用 {anchorName ConfigIORun}`ConfigIO.run` 以初始配置调用 {anchorName MedMain}`dirTree`：

```anchor MedMain
def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
```

与手动传递配置相比，这个自定义单子有许多优点：

 1. 更容易确保配置在向下传递时保持不变，除非确实需要进行更改
 2. 将继续传递配置这一关注点，与打印目录内容这一关注点更清晰地分离开来
 3. 随着程序增长，会出现越来越多的中间层；这些层除了传播配置之外不对配置做任何事情，并且当配置逻辑发生变化时，这些层无需重写

然而，这也有一些明显的缺点：

 1. 随着程序演化并且单子需要更多特性，每个基本运算符（例如 {anchorName locally}`locally` 和 {anchorName currentConfig}`currentConfig`）都需要更新
 2. 将普通的 {anchorName ConfigIO}`IO` 动作包装在 {anchorName runIO}`runIO` 中显得冗杂，并会分散对程序流程的注意力
 3. 手写单子实例是重复性的工作，而向另一个单子添加读取器效果的技术是一种设计模式，需要文档和沟通成本

使用一种称为_单子转换器_的技术，可以解决所有这些缺点。
单子转换器接受一个单子作为参数，并返回一个新的单子。
单子转换器由以下部分组成：
 1. 转换器本身的定义，它通常是一个从类型到类型的函数
 2. 一个 {anchorName ConfigIO}`Monad` 实例，它假定内部类型已经是一个单子
 3. 一个用于将动作从内层单子“提升”到变换后的单子的运算符，类似于 {anchorName runIO}`runIO`

# 向任意单子添加 Reader
%%%
tag := "ReaderT"
file := "Adding-a-Reader-to-Any-Monad"
%%%

在 {anchorName ConfigIO}`ConfigIO` 中向 {anchorName ConfigIO}`IO` 添加读取器效果，是通过把 {anchorTerm ConfigIO}`IO α` 包装在一个函数类型中完成的。
Lean 标准库包含一个名为 {anchorName MyReaderT}`ReaderT` 的函数，它可以对_任意_多态类型执行此操作：

```anchor MyReaderT
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
```
其参数如下：
 * {anchorName MyReaderT}`ρ` 是 reader 可访问的环境
 * {anchorName MyReaderT}`m` 是正在被转换的单子，例如 {anchorName ConfigIO}`IO`
 * {anchorName MyReaderT}`α` 是单子式计算所返回的值的类型
{anchorName MyReaderT}`α` 和 {anchorName MyReaderT}`ρ` 位于同一个宇宙中，因为在该单子中取回环境的算子将具有类型 {anchorTerm MyReaderTread}`m ρ`。

:::paragraph
有了 {anchorName MyReaderT}`ReaderT`，{anchorName ConfigIO}`ConfigIO` 变为：

```anchor ReaderTConfigIO
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α
```
它是一个 {kw}`abbrev`，因为 {anchorName ReaderTConfigIO}`ReaderT` 在标准库中定义了许多有用特性，而非可约定义会隐藏这些特性。
与其负责让这些特性直接对 {anchorName ConfigIO}`ConfigIO` 起作用，不如简单地让 {anchorName ReaderTConfigIO}`ConfigIO` 的行为与 {anchorTerm ReaderTConfigIO}`ReaderT Config IO` 完全相同。
:::

:::paragraph
手写的 {anchorName currentConfig}`currentConfig` 从 reader 中取得环境。
这一效应可以以泛型形式为 {anchorName MyReaderTread}`ReaderT` 的所有用法定义，名称为 {anchorName MonadReader}`read`：

```anchor MyReaderTread
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
```
然而，并非每个提供 reader 效应的单子都是用 {anchorName MyReaderT}`ReaderT` 构造的。
类型类 {anchorName MonadReader}`MonadReader` 允许任意单子提供一个 {anchorName MonadReader}`read` 运算符：

```anchor MonadReader
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u + 1) v) where
  read : m ρ

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

export MonadReader (read)
```
类型 {anchorName MonadReader}`ρ` 是一个输出参数，因为任意给定的单子通常只通过读取器提供单一类型的环境，所以当单子已知时自动选择该环境，会使程序编写更加方便。
:::

{anchorName MyReaderT}`ReaderT` 的 {anchorName ConfigIO}`Monad` 实例本质上与 {anchorName ConfigIO}`ConfigIO` 的 {anchorName ConfigIO}`Monad` 实例相同，只是 {anchorName ConfigIO}`IO` 被某个任意的单子参数 {anchorName MonadMyReaderT}`m` 替换了：

```anchor MonadMyReaderT
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env
```


下一步是消除对 {anchorName runIO}`runIO` 的使用。
当 Lean 遇到单子类型不匹配时，它会自动尝试使用一个名为 {anchorName MyMonadLift}`MonadLift` 的类型类，将实际单子转换为期望的单子。
这一过程类似于强制类型转换的使用。
{anchorName MyMonadLift}`MonadLift` 定义如下：

```anchor MyMonadLift
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
```
方法 {anchorName MyMonadLift}`monadLift` 将单子 {anchorName MyMonadLift}`m` 翻译到单子 {anchorName MyMonadLift}`n`。
这一过程称为“提升”，因为它取嵌入单子中的一个动作，并将其变为外围单子中的一个动作。
在这里，它将用于从 {anchorName ConfigIO}`IO` “提升”到 {anchorTerm ReaderTConfigIO}`ReaderT Config IO`，不过该实例适用于_任意_内部单子 {anchorName MonadLiftReaderT}`m`：

```anchor MonadLiftReaderT
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action
```
{anchorName MonadLiftReaderT}`monadLift` 的实现与 {anchorName runIO}`runIO` 的实现非常相似。
事实上，不使用 {anchorName runIO}`runIO` 而定义 {anchorName showFileAndDir}`showFileName` 和 {anchorName showFileAndDir}`showDirName` 就足够了：

```anchor showFileAndDir
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"
```

原始 {anchorName ConfigIO}`ConfigIO` 中还剩下最后一个操作需要翻译为对 {anchorName MyReaderT}`ReaderT` 的使用：{anchorName locally}`locally`。
该定义可以直接翻译为 {anchorName MyReaderT}`ReaderT`，但 Lean 标准库提供了一个更一般的版本。
标准版本称为 {anchorName MyMonadWithReader}`withReader`，它是名为 {anchorName MyMonadWithReader}`MonadWithReader` 的类型类的一部分：

```anchor MyMonadWithReader
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α
```
正如在 {anchorName MonadReader}`MonadReader` 中一样，环境 {anchorName MyMonadWithReader}`ρ` 是一个 {anchorName MyMonadWithReader}`outParam`。
{anchorName exportWithReader}`withReader` 操作被导出，因此不需要在它前面写出类型类名称：

```anchor exportWithReader
export MonadWithReader (withReader)
```
{anchorName ReaderTWithReader}`ReaderT` 的实例本质上与 {anchorName locally}`locally` 的定义相同：

```anchor ReaderTWithReader
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)
```

有了这些定义后，可以写出 {anchorName readerTDirTree}`dirTree` 的新版本：

```anchor readerTDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      withReader (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```
除了将 {anchorName locally}`locally` 替换为 {anchorName readerTDirTree}`withReader` 之外，它与之前相同。


在本节中，用 {anchorName MonadMyReaderT}`ReaderT` 替换自定义的 {anchorName ConfigIO}`ConfigIO` 类型并没有节省大量代码行。
然而，使用标准库中的组件重写代码确实具有长期收益。
首先，了解 {anchorName MyReaderT}`ReaderT` 的读者无需花时间理解 {anchorName ConfigIO}`ConfigIO` 的 {anchorName ConfigIO}`Monad` 实例，并由此反向推导单子本身的含义。
相反，他们可以确信自己的初始理解。
其次，向单子添加更多效应（例如添加一个状态效应来统计每个目录中的文件，并在末尾显示计数）需要对代码做出的修改少得多，因为库中提供的单子转换器和 {anchorName MonadLiftReaderT}`MonadLift` 实例能够良好协同。
最后，使用标准库中包含的一组类型类，可以编写多态代码，使其能够适用于多种单子，而不必关心诸如单子转换器应用顺序这样的细节。
正如有些函数可以在任意单子中工作，另一些函数也可以在提供某种状态或某种异常的任意单子中工作，而不必专门描述某个具体单子提供该状态或异常的_方式_。

# 练习
%%%
tag := "reader-io-exercises"
file := "Exercises"
%%%

## 控制点文件的显示
%%%
tag := none
file := "Controlling-the-Display-of-Dotfiles"
%%%

名称以点字符（{lit}`'.'`）开头的文件通常表示通常应当隐藏的文件，例如源代码控制元数据和配置文件。
修改 {lit}`doug`，添加一个选项，用于显示或隐藏名称以点开头的文件名。
该选项应由一个 {lit}`-a` 命令行选项控制。

## 作为参数的起始目录
%%%
tag := none
file := "Starting-Directory-as-Argument"
%%%

修改 {lit}`doug`，使其把起始目录作为一个额外的命令行参数。
