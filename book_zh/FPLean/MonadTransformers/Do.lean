import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Do"


#doc (Manual) "更多 do 的特性" =>
%%%
tag := "more-do-features"
%%%

Lean 的 {kw}`do`-标记为使用单子编写程序提供了一种类似命令式编程语言的语法。
除了为使用单子的程序提供方便的语法外，{kw}`do`-标记还提供了使用某些单子转换器的语法。

# 单分支 {kw}`if`
%%%
tag := "single-branched-if"
%%%

在单子中工作时，一种常见的模式是只有当某些条件为真时才执行副作用。
例如，{anchorName countLettersModify (module := Examples.MonadTransformers.Defs)}`countLetters` 包含对元音或辅音的检查，而两者都不是的字母对状态没有影响。
通过将 {kw}`else` 分支设置为 {anchorTerm countLettersModify (module := Examples.MonadTransformers.Defs)}`pure ()`，可以达成这一目的，因为它不会产生任何影响：

```anchor countLettersModify (module := Examples.MonadTransformers.Defs)
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```

如果 {kw}`if` 是一个 {kw}`do` 块中的语句，而不是一个表达式，那么 {anchorTerm countLettersModify (module:=Examples.MonadTransformers.Defs)}`else pure ()` 可以直接省略，Lean 会自动插入它。
下面的 {anchorName countLettersNoElse}`countLetters` 定义完全等价：

```anchor countLettersNoElse
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
使用状态单子计算列表中满足某种单子检查的条目的程序，可以写成下面这样：

```anchor count
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
```

同样，{lit}`if not E1 then STMT...` 可以写成 {lit}`unless E1 do STMT...` 。
{anchorName count}`count` 的相反（计算不满足单子检查的条目），的可以用 {kw}`unless` 代替 {kw}`if`：

```anchor countNot
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
```

理解单分支的 {kw}`if` 和 {kw}`unless` 不需要考虑单子转换器。
它们只需用 {anchorTerm count}`pure ()` 替换缺失的分支。
然而，本节中的其余扩展要求 Lean 自动重写 {kw}`do` 块，以便在写入 {kw}`do` 块的单子上添加一个局部转换器。

# 提前返回
%%%
tag := "early-return"
%%%

标准库中有一个函数 {anchorName findHuh}`List.find?`，用于返回列表中满足某些检查条件的第一个条目。
一个简单的实现并没有利用 {anchorName findHuh}`Option` 是一个单子的事实，而是使用一个递归函数在列表中循环，并使用 {kw}`if` 在找到所需条目时停止循环：

```anchor findHuhSimple
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
```

命令式语言通常会使用 {kw}`return` 关键字来终止函数的执行，并立即将某个值返回给调用者。
在 Lean 中，这个关键字在 {kw}`do`-标记中可用，{kw}`return` 停止了一个 {kw}`do` 块的执行，且 {kw}`return` 的参数是从单子返回的值。
换句话说，{anchorName findHuhFancy}`List.find?` 可以这样写：

```anchor findHuhFancy
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs
```

在命令式语言中，提前返回有点像异常，只能导致当前堆栈帧被释放。
提前返回和异常都会终止代码块的执行，实际上是用抛出的值替换周围的代码。
在幕后，Lean 中的提前返回是使用 {anchorName runCatch}`ExceptT` 的一个版本实现的。
每个使用提前返回的 {kw}`do` 块都被包裹在一个异常处理程序中（在函数 {anchorName MonadExcept (module:=Examples.MonadTransformers.Defs)}`tryCatch` 的意义上）。
提前返回被转换为将值作为异常抛出，处理程序捕获抛出的值并立即返回。
换句话说，{kw}`do` 块的原始返回值类型也被用作异常类型。

具体来说，当异常类型和返回类型相同时，辅助函数 {anchorName runCatch}`runCatch` 会从单子转换器堆栈的顶部剥离一层 {anchorName runCatch}`ExceptT`：

```anchor runCatch
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
```
{anchorName findHuh}`List.find?` 中使用提前返回的 {kw}`do` 块被转换为不使用提前返回的 {kw}`do` 块，方法是将其包裹在 {anchorName desugaredFindHuh}`runCatch` 的使用中，并用 {anchorName desugaredFindHuh}`throw` 替换提前返回：

```anchor desugaredFindHuh
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
```

另一种提前返回很有用的情况是命令行应用程序，如果参数或输入不正确，程序会提前终止。
许多程序在进入程序主体之前，都会先验证参数和输入。
下面这个版本的 {ref "running-a-program"}[问候程序 {lit}`hello-name`] 检查是否提供了命令行参数：
```anchor main (module := EarlyReturn)
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).toSlice.trimAscii.copy
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0
```
不带参数运行它并输入名字 {lit}`David` 会产生与前一个版本相同的结果：
```commands «early-return» "early-return"
$ expect -f ./run # lean --run EarlyReturn.lean
How would you like to be addressed?
David
Hello, David!
```

将名字作为命令行参数而不是回答提供会导致错误：
```commands «early-return» "early-return"
$ expect -f ./too-many-args # lean --run EarlyReturn.lean David
Expected no arguments, but got 1
```

不提供名字会导致另一个错误：
```commands «early-return» "early-return"
$ expect -f ./no-name # lean --run EarlyReturn.lean
How would you like to be addressed?

No name provided
```

使用提前返回的程序避免了嵌套控制流，而不使用提前返回的版本则需要这样做：
```anchor nestedmain (module := EarlyReturn)
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).toSlice.trimAscii.copy
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0
```

Lean 中的提前返回与命令式语言中的提前返回的一个重要区别是，Lean 的提前返回仅适用于当前的 {kw}`do` 块。
当函数的整个定义都在同一个 {kw}`do` 块中时，这种区别并不重要。
但是，如果 {kw}`do` 出现在其他结构之下，那么这种区别就会变得很明显。
例如，给定以下 {anchorName greet}`greet` 的定义：

```anchor greet
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
```
表达式 {anchorTerm greetDavid}`greet "David"` 的求值结果为 {anchorTerm greetDavid}`"Hello, David"`，而不仅仅是 {anchorTerm greetDavid}`"David"`。

# 循环
%%%
tag := "loops"
%%%

就像每个具有可变状态的程序都可以重写为将状态作为参数传递的程序一样，每个循环都可以重写为递归函数。
从一个角度来看，{anchorName findHuh}`List.find?` 作为递归函数最为清晰。
毕竟，它的定义反映了列表的结构：如果头部通过检查，则应将其返回；否则在尾部查找。
当没有更多条目时，答案是 {anchorName findHuhSimple}`none`。
从另一个角度来看，{anchorName findHuh}`List.find?` 作为循环最为清晰。
毕竟，程序按顺序查询条目，直到找到满意的条目，此时它终止。
如果循环终止而没有返回，则答案是 {anchorName findHuhSimple}`none`。

## 使用 ForM 循环
%%%
tag := "looping-with-forM"
%%%

Lean 包含一个类型类，用于描述在某个单子中循环遍历容器类型。
这个类称为 {anchorName ForM}`ForM`：

```anchor ForM
class ForM (m : Type u → Type v) (γ : Type w₁)
    (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit
```
这个类非常通用。
参数 {anchorName ForM}`m` 是具有某些所需效果的单子，{anchorName ForM}`γ` 是要循环遍历的集合，{anchorName ForM}`α` 是集合中元素的类型。
通常，{anchorName ForM}`m` 可以是任何单子，但也可能存在例如仅支持在 {anchorName printArray}`IO` 中循环的数据结构。
方法 {anchorName ForM}`forM` 接受一个集合和一个单子操作，该操作将针对集合中的每个元素运行以产生效果，然后负责运行这些操作。

{anchorName ListForM}`List` 的实例允许 {anchorName ListForM}`m` 是任何单子，它将 {anchorName ForM}`γ` 设置为 {anchorTerm ListForM}`List α`，并将类的 {anchorName ForM}`α` 设置为列表中找到的相同 {anchorName ListForM}`α`：

```anchor ListForM
def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action

instance : ForM m (List α) α where
  forM := List.forM
```
{ref "reader-io-implementation"}[{lit}`doug` 中的函数 {anchorName doList (module := DirTree)}`doList`] 是列表的 {anchorName ForM}`forM`。
因为 {anchorName countLettersForM}`forM` 旨在用于 {kw}`do` 块中，所以它使用 {anchorName ForM}`Monad` 而不是 {anchorName OptionTExec}`Applicative`。
{anchorName ForM}`forM` 可用于使 {anchorName countLettersForM}`countLetters` 更短：

```anchor countLettersForM
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)
```


{anchorName ManyForM}`Many` 的实例非常相似：

```anchor ManyForM
def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do
    action first
    forM (rest ()) action

instance : ForM m (Many α) α where
  forM := Many.forM
```

因为 {anchorName ForM}`γ` 可以是任何类型，所以 {anchorName ForM}`ForM` 可以支持非多态集合。
一个非常简单的集合是小于某个给定数字的自然数，按相反顺序排列：

```anchor AllLessThan
structure AllLessThan where
  num : Nat
```
它的 {anchorName ForM}`ForM` 运算符将提供的操作应用于每个较小的 {anchorName ListCount}`Nat`：

```anchor AllLessThanForM
def AllLessThan.forM [Monad m]
    (coll : AllLessThan) (action : Nat → m Unit) :
    m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance : ForM m AllLessThan Nat where
  forM := AllLessThan.forM
```
使用 {anchorName ForM}`ForM` 可以对小于 5 的每个数字运行 {anchorName AllLessThanForMRun}`IO.println`：
```anchor AllLessThanForMRun
#eval forM { num := 5 : AllLessThan } IO.println
```
```anchorInfo AllLessThanForMRun
4
3
2
1
0
```

仅在特定单子中工作的 {anchorName ForM}`ForM` 实例的一个示例是循环遍历从 IO 流（例如标准输入）读取的行：
```anchor LinesOf (module := ForMIO)
structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM
    (readFrom : LinesOf) (action : String → IO Unit) :
    IO Unit := do
  let line ← readFrom.stream.getLine
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM
```
{anchorName ForM}`ForM` 的定义被标记为 {kw}`partial`，因为不能保证流是有限的。
在这种情况下，{anchorName ranges}`IO.FS.Stream.getLine` 仅在 {anchorName countToThree}`IO` 单子中工作，因此不能使用其他单子进行循环。

此示例程序使用此循环结构过滤掉不包含字母的行：
```anchor main (module := ForMIO)
def main (argv : List String) : IO UInt32 := do
  if argv != [] then
    IO.eprintln "Unexpected arguments"
    return 1

  forM (LinesOf.mk (← IO.getStdin)) fun line => do
    if line.any (·.isAlpha) then
      IO.print line

  return 0
```
```commands formio "formio" (show := false)
$ ls
expected
test-data
$ cp ../ForMIO.lean .
$ ls
ForMIO.lean
expected
test-data
```
文件 {lit}`test-data` 包含：
```file formio "formio/test-data"
Hello!
!!!!!
12345
abc123

Ok
```
调用此程序（存储在 {lit}`ForMIO.lean` 中）会产生以下输出：
```commands formio "formio"
$ lean --run ForMIO.lean < test-data
Hello!
abc123
Ok
```

## 停止迭代
%%%
tag := "break"
%%%

使用 {anchorName ForM}`ForM` 很难提前终止循环。
编写一个函数，在 {anchorName AllLessThan}`AllLessThan` 中的 {anchorName AllLessThan}`Nat` 上迭代，直到达到 {anchorTerm OptionTcountToThree}`3`，这需要一种中途停止循环的方法。
实现这一点的一种方法是将 {anchorName ForM}`ForM` 与 {anchorName OptionTExec}`OptionT` 单子转换器一起使用。
第一步是定义 {anchorName OptionTExec}`OptionT.exec`，它会丢弃有关返回值以及转换后的计算是否成功的信息：

```anchor OptionTExec
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
```
然后，可以使用 {anchorName AlternativeOptionT (module:=Examples.MonadTransformers.Defs)}`Alternative` 的 {anchorName OptionTExec}`OptionT` 实例中的 failure 来提前终止循环：

```anchor OptionTcountToThree
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
```
一个快速测试表明该解决方案有效：
```anchor optionTCountSeven
#eval countToThree 7
```
```anchorInfo optionTCountSeven
6
5
4
3
```

然而，这段代码并不容易阅读。
提前终止循环是一项常见任务，Lean 提供了更多的语法糖来简化此操作。
同一个函数也可以写成如下形式：

```anchor countToThree
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
```
测试表明它的工作方式与之前的版本完全相同：
```anchor countSevenFor
#eval countToThree 7
```
```anchorInfo countSevenFor
6
5
4
3
```

{kw}`for`{lit}` ...`{kw}`in`{lit}` ...`{kw}`do`{lit}` ...` 语法脱糖为使用名为 {anchorName ForInIOAllLessThan}`ForIn` 的类型类，它是 {anchorName ForM}`ForM` 的一个稍微复杂一点的版本，用于跟踪状态和提前终止。
标准库提供了一个适配器，可以将 {anchorName ForM}`ForM` 实例转换为 {anchorName ForInIOAllLessThan}`ForIn` 实例，称为 {anchorName ForInIOAllLessThan}`ForM.forIn`。
要启用基于 {anchorName ForM}`ForM` 实例的 {kw}`for` 循环，请添加类似以下内容，并适当替换 {anchorName AllLessThan}`AllLessThan` 和 {anchorName AllLessThan}`Nat`：

```anchor ForInIOAllLessThan
instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
```
但是请注意，此适配器仅适用于保持单子不受约束的 {anchorName ForM}`ForM` 实例，大多数实例都是如此。
这是因为适配器使用 {anchorName SomeMonads (module:=Examples.MonadTransformers.Defs)}`StateT` 和 {anchorName SomeMonads (module:=Examples.MonadTransformers.Defs)}`ExceptT`，而不是底层单子。

{kw}`for` 循环支持提前返回。
将带有提前返回的 {kw}`do` 块转换为使用异常单子转换器，同样适用于 {anchorName ForM}`ForM` 之下，就像前面使用 {anchorName OptionTExec}`OptionT` 停止迭代一样。
此版本的 {anchorName findHuh}`List.find?` 同时使用了这两者：

```anchor findHuh
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
```

除了 {kw}`break` 之外，{kw}`for` 循环还支持 {kw}`continue` 以跳过迭代中循环体的其余部分。
{anchorName findHuhCont}`List.find?` 的另一种（但令人困惑的）表述跳过了不满足检查的元素：

```anchor findHuhCont
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
```

{anchorName ranges}`Std.Range` 是一个由起始数字、结束数字和步长组成的结构。
它们表示一系列自然数，从起始数字到结束数字，每次增加步长。
Lean 具有构造范围的特殊语法，由方括号、数字和冒号组成，有四种变体。
必须始终提供停止点，而起始点和步长是可选的，分别默认为 {anchorTerm ranges}`0` 和 {anchorTerm ranges}`1`：

:::table +header
*
 *  表达式
 *  起点
 *  终点
 *  步长
 *  作为列表

*
 *  {anchorTerm rangeStopContents}`[:10]`
 *  {anchorTerm ranges}`0`
 *  {anchorTerm rangeStop}`10`
 *  {anchorTerm ranges}`1`
 *  {anchorInfo rangeStopContents}`[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]`

*
 *  {anchorTerm rangeStartStopContents}`[2:10]`
 *  {anchorTerm rangeStartStopContents}`2`
 *  {anchorTerm rangeStartStopContents}`10`
 *  {anchorTerm ranges}`1`
 *  {anchorInfo rangeStartStopContents}`[2, 3, 4, 5, 6, 7, 8, 9]`

*
 *  {anchorTerm rangeStopStepContents}`[:10:3]`
 *  {anchorTerm ranges}`0`
 *  {anchorTerm rangeStartStopContents}`10`
 *  {anchorTerm rangeStopStepContents}`3`
 *  {anchorInfo rangeStopStepContents}`[0, 3, 6, 9]`

*
 *  {anchorTerm rangeStartStopStepContents}`[2:10:3]`
 *  {anchorTerm rangeStartStopStepContents}`2`
 *  {anchorTerm rangeStartStopStepContents}`10`
 *  {anchorTerm rangeStartStopStepContents}`3`
 *  {anchorInfo rangeStartStopStepContents}`[2, 5, 8]`

:::

请注意，起始数字 _包含_ 在范围内，而停止数字不包含。
所有三个参数都是 {anchorName three}`Nat`，这意味着范围不能倒数——起始数字大于或等于停止数字的范围根本不包含任何数字。

范围可以与 {kw}`for` 循环一起使用，以从范围中提取数字。
此程序计算从 4 到 8 的偶数：

```anchor fourToEight
def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i
```
运行它会产生：
```anchorInfo fourToEightOut
4
6
8
```


最后，{kw}`for` 循环支持通过用逗号分隔 {kw}`in` 子句来并行迭代多个集合。
当第一个集合用完元素时，循环停止，因此声明：

```anchor parallelLoop
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4:8] do
    IO.println (x, y)
```
产生三行输出：
```anchor parallelLoopOut
#eval parallelLoop
```
```anchorInfo parallelLoopOut
(currant, 4)
(gooseberry, 5)
(rowan, 6)
```

许多数据结构实现了 {anchorName ForInIOAllLessThan}`ForIn` 类型类的增强版本，该版本向循环体添加了元素是从集合中提取的证据。
可以通过在元素名称之前提供证据名称来使用这些证据。
此函数打印数组的所有元素及其索引，并且编译器能够确定数组查找都是安全的，因为有证据 {anchorName printArray}`h`：

```anchor printArray
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in [0:xs.size] do
    IO.println s!"{i}:\t{xs[i]}"
```
在此示例中，{anchorName printArray}`h` 是 {lit}`i ∈ [0:xs.size]` 的证据，并且检查 {anchorTerm printArray}`xs[i]` 是否安全的策略能够将其转换为 {lit}`i < xs.size` 的证据。

# 可变变量
%%%
tag := "let-mut"
%%%

除了提前 {kw}`return`、无 {kw}`else` 的 {kw}`if` 和 {kw}`for` 循环之外，Lean 还支持 {kw}`do` 块内的局部可变变量。
在幕后，这些可变变量脱糖为等效于 {anchorName twoStateT}`StateT` 的代码，而不是由真正的可变变量实现。
再一次，函数式编程被用来模拟命令式编程。

局部可变变量是用 {kw}`let mut` 而不是普通的 {kw}`let` 引入的。
定义 {anchorName two}`two` 使用恒等单子 {anchorName sameBlock}`Id` 来启用 {kw}`do` 语法而不引入任何效果，它计数到 {anchorTerm ranges}`2`：

```anchor two
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
```
此代码等效于使用 {anchorName twoStateT}`StateT` 将 {anchorTerm twoStateT}`1` 加两次的定义：

```anchor twoStateT
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
```

局部可变变量与 {kw}`do`-标记的所有其他特性配合良好，这些特性为单子转换器提供了方便的语法。
定义 {anchorName three}`three` 计算三条目列表中的条目数：

```anchor three
def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
```
同样，{anchorName six}`six` 将列表中的条目相加：

```anchor six
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
```

{anchorName ListCount}`List.count` 计算列表中满足某些检查的条目数：

```anchor ListCount
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
```

局部可变变量比显式局部使用 {anchorName twoStateT}`StateT` 使用起来更方便，也更容易阅读。
但是，它们没有命令式语言中不受限制的可变变量的全部功能。
特别是，它们只能在引入它们的 {kw}`do` 块中进行修改。
这意味着，例如，{kw}`for` 循环不能被其他等效的递归辅助函数替换。
此版本的 {anchorName nonLocalMut}`List.count`：
```anchor nonLocalMut
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then found := found + 1
      go ys
  return found
```
在尝试修改 {anchorName nonLocalMut}`found` 时产生以下错误：
```anchorError nonLocalMut
`found` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `found`, consider using `let found` instead
```
这是因为递归函数是用恒等单子编写的，只有引入变量的 {kw}`do` 块的单子才会用 {anchorName twoStateT}`StateT` 进行转换。

# 什么是 {kw}`do` 块？
%%%
tag := "do-block-boundaries"
%%%

{kw}`do`-标记的许多特性仅适用于单个 {kw}`do` 块。
提前返回终止当前块，可变变量只能在定义它们的块中进行修改。
为了有效地使用它们，了解什么算作“同一个块”非常重要。

一般来说，{kw}`do` 关键字后面的缩进块算作一个块，其下方的直接语句序列是该块的一部分。
独立块中的语句虽然包含在一个块中，但不被视为该块的一部分。
但是，控制什么算作同一个块的规则稍微有些微妙，因此需要举一些例子。
可以通过设置一个带有可变变量的程序并查看允许修改的位置来测试规则的确切性质。
此程序的修改显然与可变变量在同一个块中：

```anchor sameBlock
example : Id Unit := do
  let mut x := 0
  x := x + 1
```

当修改发生在作为使用 {lit}`:=` 定义名称的 {kw}`let` 语句的一部分的 {kw}`do` 块中时，它不被视为该块的一部分：
```anchor letBodyNotBlock
example : Id Unit := do
  let mut x := 0
  let other := do
    x := x + 1
  other
```
```anchorError letBodyNotBlock
`x` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `x`, consider using `let x` instead
```
但是，出现在使用 {lit}`←` 定义名称的 {kw}`let` 语句下的 {kw}`do` 块被视为周围块的一部分。
以下程序被接受：

```anchor letBodyArrBlock
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other
```

类似地，作为函数参数出现的 {kw}`do` 块也独立于其外围块。
下面的程序不会被接受：
```anchor funArgNotBlock
example : Id Unit := do
  let mut x := 0
  let addFour (y : Id Nat) := Id.run y + 4
  addFour do
    x := 5
```
```anchorError funArgNotBlock
`x` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `x`, consider using `let x` instead
```

如果 {kw}`do` 关键字完全是多余的，那么它不会引入新的块。
此程序被接受，并且等效于本节中的第一个程序：

```anchor collapsedBlock
example : Id Unit := do
  let mut x := 0
  do x := x + 1
```

{kw}`do` 下的分支内容（例如由 {kw}`match` 或 {kw}`if` 引入的内容）被视为周围块的一部分，无论是否添加了多余的 {kw}`do`。
以下程序都被接受：

```anchor ifDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then
    x := x + 1
```

```anchor ifDoDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then do
    x := x + 1
```

```anchor matchDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => x := x + 1
  | false => x := 17
```

```anchor matchDoDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => do
    x := x + 1
  | false => do
    x := 17
```
同样，作为 {kw}`for` 和 {kw}`unless` 语法的一部分出现的 {kw}`do` 只是其语法的一部分，不会引入新的 {kw}`do` 块。
这些程序也被接受：

```anchor doForSame
example : Id Unit := do
  let mut x := 0
  for y in [1:5] do
   x := x + y
```

```anchor doUnlessSame
example : Id Unit := do
  let mut x := 0
  unless 1 < 5 do
    x := x + 1
```


# 命令式还是函数式编程？
%%%
tag := none
%%%

Lean 的 {kw}`do`-标记提供的命令式特性使得许多程序非常类似于 Rust、Java 或 C# 等语言中的对应程序。
这种相似性在将命令式算法转换为 Lean 时非常方便，而且有些任务最自然地被认为是命令式的。
单子和单子转换器的引入使得命令式程序可以用纯函数式语言编写，而 {kw}`do`-标记作为单子（可能经过局部转换）的专用语法，允许函数式程序员两全其美：不可变性提供的强大推理原则和通过类型系统对可用效果的严格控制，与允许使用效果的程序看起来熟悉且易于阅读的语法和库相结合。
单子和单子转换器使得函数式编程与命令式编程成为一个视角问题。


# 练习
%%%
tag := "monad-transformer-do-exercises"
%%%

 * 重写 {lit}`doug` 以使用 {kw}`for` 而不是 {anchorName doList (module:=DirTree)}`doList` 函数。
 * 是否还有其他机会使用本节介绍的特性来改进代码？如果有，请使用它们！
