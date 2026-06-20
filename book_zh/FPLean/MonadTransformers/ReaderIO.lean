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
%%%

当应用程序存在类似“当前配置”的数据需要通过多次递归调用传递时，读取器单子（Reader Monad）就会派上用场。
这种程序有一个例子是 {lit}`tree`，它递归地打印当前目录及其子目录中的文件，并用字符表示它们的树形结构。
本章中的 {lit}`tree` 版本名为 {lit}`doug` ，取自北美西海岸的道格拉斯冷杉，在显示目录结构时，它提供了 Unicode 框画字符或其 ASCII 对应字符选项。


例如，以下命令将在名为 {lit}`doug-demo` 的目录中创建一个目录结构和一些空文件：
```commands doug "doug-demo"
$$ cd doug-demo
$ mkdir -p a/b/c
$ mkdir -p a/d
$ mkdir -p a/e/f
$ touch a/b/hello
$ touch a/d/another-file
$ touch a/e/still-another-file-again
```
运行 {lit}`doug` 的结果如下：
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
%%%

在内部，{lit}`doug` 在递归遍历目录结构时会向下传递一个配置值。
该配置包含两个字段： {anchorName Config}`useASCII` 决定是否使用 Unicode 框画字符或 ASCII 垂直线和破折号字符来表示结构，而 {anchorName Config}`currentPrefix` 字段包含了一个字符串，用于在每行输出前添加。
随着当前目录的深入，前缀字符串会不断积累目录中的指标。
配置是一个结构体：

```anchor Config
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
```
该结构体的两个字段都有默认定义。
默认的 {anchorName Config}`Config` 使用 Unicode 显示，不带前缀。

:::paragraph
调用 {lit}`doug` 的用户需要提供命令行参数。
用法如下：

```anchor usage
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
```
据此，可以通过查看命令行参数列表来构建配置：

```anchor configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
```
:::

{anchorName OldMain}`main` 函数是一个名为 {anchorName OldMain}`dirTree` 的内部函数的包装，它根据一个配置来显示目录的内容。
在调用 {anchorName OldMain}`dirTree` 之前，{anchorName OldMain}`main` 需要处理命令行参数。
它还必须向操作系统返回适当的退出状态码：

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
特别是名为 {lit}`.` 或 {lit}`..` 的文件，因为它们实际上是用于导航的特殊标记，而不是文件本身。
应该显示的文件有两种：普通文件和目录：

```anchor Entry
inductive Entry where
  | file : String → Entry
  | dir : String → Entry
```
为了确定是否要显示某个文件以及它是哪种条目，{lit}`doug` 依赖 {anchorName toEntry}`toEntry` 函数 ：

```anchor toEntry
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))
```
{anchorName names}`System.FilePath.components` 在目录分隔符处分割路径名，并将路径转换为路径组件的列表。
如果没有最后一个组件，那么该路径就是根目录。
如果最后一个组件是一个特殊的导航文件（{lit}`.` 或 {lit}`..`），则应排除该文件。
否则，目录和文件将被包装在相应的构造函数中。

Lean 的逻辑无法确定目录树是否有限。
事实上，有些系统允许构建循环目录结构。
因此，{anchorName OldDirTree}`dirTree` 函数必须被声明为 {kw}`partial`：

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
对 {anchorName OldDirTree}`toEntry` 的调用是一个 {ref "nested-actions"}[嵌套操作] —— 在箭头没有其他含义的位置，如 {kw}`match`，括号是可以省略的。
当文件名与树中的条目不对应时（例如，因为它是 {lit}`..`），{anchorName OldDirTree}`dirTree` 什么也不做。
当文件名指向一个普通文件时，{anchorName OldDirTree}`dirTree` 会调用一个辅助函数，以当前配置来显示该文件。
当文件名指向一个目录时，将通过一个辅助函数来显示该目录，然后其内容将递归地显示在一个新的配置中，其中的前缀已被扩写，以说明它位于一个新的目录中。
目录的内容按顺序排序，以便使输出具有确定性，比较依据是 {anchorName compareEntries'}`dirLT`。
```anchor compareEntries'
def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
```

文件和目录的名称通过 {anchorName OldShowFile}`showFileName` 和 {anchorName OldShowFile}`showDirName` 函数来显示：

```anchor OldShowFile
def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println (cfg.dirName dir)
```
这两个辅助函数都委托给了将 ASCII 与 Unicode 设置考虑在内的 {anchorName filenames}`Config` 上的函数：

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
同样，{anchorName inDirectory}`Config.inDirectory` 用目录标记扩写了前缀：

```anchor inDirectory
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
```

{anchorName doList}`doList` 函数可以在目录内容的列表中迭代 IO 操作。
由于 {anchorName doList}`doList` 只执行列表中的所有操作，并不根据任何操作返回的值来决定控制流，因此不需要使用 {anchorName ConfigIO}`Monad` 的全部功能，它适用于任何 {anchorName doList}`Applicative` 应用程序：

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
%%%

虽然这种 {lit}`doug` 实现可以正常工作，但手动传递配置不仅费事还容易出错。
例如，类型系统无法捕获向下传递的错误配置。
读取器作用不仅可以确保在所有递归调用中都传递相同的配置，而且有助于优化冗长的代码。

要创建一个同时也是 {anchorName ConfigIO}`Config` 读取器的 {anchorName ConfigIO}`IO` ，首先要按照{ref "custom-environments"}[求值器示例]中的方法定义类型及其 {anchorName ConfigIO}`Monad` 实例：

```anchor ConfigIO
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg
```
这个 {anchorName ConfigIO}`Monad` 实例与 {anchorName Reader (module := Examples.Monads.Class)}`Reader` 实例的区别在于，它使用 {anchorName ConfigIO}`IO` 单子中的 {kw}`do` 标记 作为 {anchorName ConfigIO}`bind` 返回函数的主体，而不是直接将 {anchorName ConfigIO}`next` 应用于 {anchorName ConfigIO}`result` 返回的值。
由 {anchorName ConfigIO}`result` 执行的任何 {anchorName ConfigIO}`IO` 作用都必须在调用 {anchorName ConfigIO}`next` 之前发生，这一点由 {anchorName ConfigIO}`IO` 单子的 {anchorName ConfigIO}`bind` 操作符来保证。
{anchorName ConfigIO}`ConfigIO` 不是宇宙多态的，因为底层的 {anchorName ConfigIO}`IO` 类型也不是宇宙多态的。

运行 {anchorName ConfigIO}`ConfigIO` 操作需要向其提供一个配置，从而将其转换为 {anchorName ConfigIO}`IO` 操作：

```anchor ConfigIORun
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
```
这个函数其实并无必要，因为调用者只需直接提供配置即可。
不过，给操作命名可以让我们更容易看出代码的各部分会在哪个单子中运行。

下一步是定义访问当前配置的方法，作为 {anchorName ConfigIO}`ConfigIO` 的一部分：

```anchor currentConfig
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
```
这与{ref "custom-environments"}[求值器示例]中的 {anchorName Reader (module := Examples.Monads.Class)}`read` 相同，只是它使用了 {anchorName ConfigIO}`IO` 的 {anchorName ConfigIO}`pure` 来返回其值，而不是直接返回。
因为进入一个目录会修改递归调用范围内的当前配置，因此有必要提供一种修改配置的方法：

```anchor locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
```

{lit}`doug` 中的大部分代码都不需要配置，因此 {lit}`doug` 会从标准库中调用普通的 Lean {anchorName ConfigIO}`IO` 操作，这些操作当然也不需要 {anchorName ConfigIO}`Config`。
普通的 {anchorName ConfigIO}`IO` 操作可以使用 {anchorName runIO}`runIO` 运行，它会忽略配置参数：

```anchor runIO
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action
```

有了这些组件，{anchorName MedShowFileDir}`showFileName` 和 {anchorName MedShowFileDir}`showDirName` 可以修改为使用 {anchorName ConfigIO}`ConfigIO` 单子来隐式获取配置参数。
它们使用 {ref "nested-actions"}[嵌套动作] 来获取配置，并使用 {anchorName runIO}`runIO` 来实际执行对 {anchorName MedShowFileDir}`IO.println` 的调用：

```anchor MedShowFileDir
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
```

在新版的 {anchorName MedDirTree}`dirTree` 中，对 {anchorName MedDirTree}`toEntry` 和 {anchorName MedDirTree}`readDir` 的调用被封装在 {anchorName runIO}`runIO` 中。
此外，它不再构建一个新的配置，然后要求程序员跟踪将哪个配置传递给递归调用，而是使用 {anchorName MedDirTree}`locally` 自然地将修改后的配置限定在程序的一小块区域内，在该区域内，它是 _唯一_ 有效的配置：

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

新版本的 {anchorName MedMain}`main` 使用 {anchorName ConfigIORun}`ConfigIO.run` 来调用带有初始配置的 {anchorName MedMain}`dirTree`：

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

 1. 除了确实希望修改配置的地方以外，更容易保证配置在向下传递时保持不变。
 2. 继续传递配置这一关注点，与打印目录内容这一关注点之间的分离更加清晰。
 3. 随着程序增长，会出现越来越多只传播配置而不对其做任何其他事情的中间层；当配置逻辑改变时，这些层不需要重写。

然而，这种做法也有一些明显缺点：

 1. 随着程序演化、单子需要更多功能，每个基本运算符（例如 {anchorName locally}`locally` 和 {anchorName currentConfig}`currentConfig`）都需要更新。
 2. 用 {anchorName runIO}`runIO` 包装普通 {anchorName ConfigIO}`IO` 动作会产生噪声，分散对程序流程的注意。
 3. 手写单子实例是重复性的工作，而为另一个单子添加读取器作用的技术是一种设计模式，需要文档和沟通成本。

使用一种称为_单子转换器_的技术，可以解决所有这些缺点。
单子转换器把一个单子作为参数，并返回一个新的单子。
单子转换器由以下部分组成：
 1. 转换器本身的定义，通常是一个从类型到类型的函数。
 2. 一个 {anchorName ConfigIO}`Monad` 实例，它假设内部类型已经是单子。
 3. 一个把内部单子中的动作“提升”到转换后单子中的运算符，类似于 {anchorName runIO}`runIO`。

# 将读取器添加到任意单子
%%%
tag := "ReaderT"
%%%

在 {anchorName ConfigIO}`ConfigIO`中，通过将 {anchorTerm ConfigIO}`IO α` 包装成一个函数类型，为 {anchorName ConfigIO}`IO` 添加了读取器作用。
Lean 的标准库有一个函数，可以对 _任意_ 多态类型执行此操作，称为 {anchorName MyReaderT}`ReaderT`：

```anchor MyReaderT
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
```
它的参数如下:
 * {anchorName MyReaderT}`ρ` 是读取器可以访问的环境
 * {anchorName MyReaderT}`m` 是被转换的单子，例如 {anchorName ConfigIO}`IO`
 * {anchorName MyReaderT}`α` 是单子计算返回值的类型
{anchorName MyReaderT}`α` 和 {anchorName MyReaderT}`ρ` 都在同一个宇宙中，因为在单子中检索环境的算子将具有 {anchorTerm MyReaderTread}`m ρ` 类型。

:::paragraph
有了 {anchorName MyReaderT}`ReaderT`，{anchorName ConfigIO}`ConfigIO` 就变成了:

```anchor ReaderTConfigIO
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α
```
它是一个 {kw}`abbrev`，因为在标准库中定义了许多关于 {anchorName ReaderTConfigIO}`ReaderT` 的有用功能，而不可归约的定义会隐藏这些功能。
与其让 {anchorName ConfigIO}`ConfigIO` 直接使用这些功能，不如让 {anchorName ReaderTConfigIO}`ConfigIO` 的行为与 {anchorTerm ReaderTConfigIO}`ReaderT Config IO` 保持一致。
:::

:::paragraph
手动编写的 {anchorName currentConfig}`currentConfig` 从读取器中获取了环境。
这种作用可以以通用形式定义，适用于 {anchorName MyReaderTread}`ReaderT` 的所有用途，名为 {anchorName MonadReader}`read`：

```anchor MyReaderTread
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
```
然而，并不是每个提供读取器作用的单子都是用 {anchorName MyReaderT}`ReaderT` 构建的。
类型类 {anchorName MonadReader}`MonadReader` 允许任何单子提供 {anchorName MonadReader}`read` 操作符：

```anchor MonadReader
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u + 1) v) where
  read : m ρ

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

export MonadReader (read)
```
类型 {anchorName MonadReader}`ρ` 是一个输出参数，因为任何给定的单子通常只通过读取器提供单一类型的环境，所以在已知单子时自动选择它可以使程序编写更方便。
:::

{anchorName MyReaderT}`ReaderT` 的 {anchorName ConfigIO}`Monad` 实例与 {anchorName ConfigIO}`ConfigIO` 的 {anchorName ConfigIO}`Monad` 实例基本相同，只是 {anchorName ConfigIO}`IO` 被某个表示任意单子的参数 {anchorName MonadMyReaderT}`m` 所取代:

```anchor MonadMyReaderT
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env
```


下一步是消除对 {anchorName runIO}`runIO` 的使用。
当 Lean 遇到单子类型不匹配时，它会自动尝试使用名为 {anchorName MyMonadLift}`MonadLift` 的类型类，将实际的单子转换为预期单子。
这一过程与使用强制转换相似。
{anchorName MyMonadLift}`MonadLift` 的定义如下：

```anchor MyMonadLift
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
```
方法 {anchorName MyMonadLift}`monadLift` 可以将单子 {anchorName MyMonadLift}`m` 转换为单子 {anchorName MyMonadLift}`n`。
这个过程被称为“提升”，因为它将嵌入到单子中的动作转换成周围单子中的动作。
在本例中，它将用于把 {anchorName ConfigIO}`IO` “提升”到 {anchorTerm ReaderTConfigIO}`ReaderT Config IO`，尽管该实例适用于 _任何_ 内部单子 {anchorName MonadLiftReaderT}`m`：

```anchor MonadLiftReaderT
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action
```
{anchorName MonadLiftReaderT}`monadLift` 的实现与 {anchorName runIO}`runIO` 非常相似。
事实上，只需定义 {anchorName showFileAndDir}`showFileName` 和 {anchorName showFileAndDir}`showDirName` 即可，无需使用 {anchorName runIO}`runIO`：

```anchor showFileAndDir
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"
```

原版 {anchorName ConfigIO}`ConfigIO` 中的最后一个操作还需要翻译成 {anchorName MyReaderT}`ReaderT` 的形式：{anchorName locally}`locally`。
该定义可以直接翻译为 {anchorName MyReaderT}`ReaderT`，但 Lean 标准库提供了一个更通用的版本。
标准版本被称为 {anchorName MyMonadWithReader}`withReader`，它是名为 {anchorName MyMonadWithReader}`MonadWithReader` 的类型类的一部分：

```anchor MyMonadWithReader
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α
```
正如在 {anchorName MonadReader}`MonadReader` 中一样，环境 {anchorName MyMonadWithReader}`ρ` 是一个 {anchorName MyMonadWithReader}`outParam`。
{anchorName exportWithReader}`withReader` 操作是被导出的，所以在编写时不需要在前面加上类型类名：

```anchor exportWithReader
export MonadWithReader (withReader)
```
{anchorName ReaderTWithReader}`ReaderT` 的实例与 {anchorName locally}`locally` 的定义基本相同：

```anchor ReaderTWithReader
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)
```

有了这些定义,我们便可以定义新版本的 {anchorName readerTDirTree}`dirTree`:

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
除了用 {anchorName readerTDirTree}`withReader` 替换 {anchorName locally}`locally` 外，其他内容保持不变。


在本节中，用 {anchorName MonadMyReaderT}`ReaderT` 代替自定义的 {anchorName ConfigIO}`ConfigIO` 类型并没有节省大量代码行数。
不过，使用标准库中的组件重写代码确实有长远的好处。
首先，了解 {anchorName MyReaderT}`ReaderT` 的读者不需要花时间去理解 {anchorName ConfigIO}`ConfigIO` 的 {anchorName ConfigIO}`Monad` 实例，也不需要逆向理解单子本身的含义。
相反，他们可以沿用自己的初步理解。
接下来，给单子添加更多的作用（例如计算每个目录中的文件并在最后显示计数的状态作用）所需的代码改动要少得多，因为库中提供的单子转换器和 {anchorName MonadLiftReaderT}`MonadLift` 实例配合得很好。
最后，使用标准库中包含的一组类型类，多态代码的编写方式可以使其适用于各种单子，而无需关心单子转换器的应用顺序等细节。
正如某些函数可以在任何单子中工作一样，另一些函数也可以在任何提供特定类型状态或特定类型异常的单子中工作，而不必特别描述特定的具体单子提供状态或异常的 _方式_。

# 练习
%%%
tag := "reader-io-exercises"
%%%

## 控制点文件的显示
%%%
tag := none
%%%

文件名以点字符 ({lit}`'.'`) 开头的文件通常代表隐藏文件，如源代码管理的元数据和配置文件。
修改 {lit}`doug` 并加入一个选项，以显示或隐藏以点开头的文件名。
应使用命令行选项 {lit}`-a` 来控制该选项。

## 起始目录作为参数
%%%
tag := none
%%%

修改 {lit}`doug` ，使其可以将起始目录作为额外的命令行参数。
