import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Do"


#doc (Manual) "更多 do 特性" =>
%%%
tag := "more-do-features"
file := "More-do-Features"
%%%

Lean 的 {kw}`do`-记法提供了一种语法，用于编写带有单子的程序，其形式类似于命令式编程语言。
除了为带有单子的程序提供便利语法之外，{kw}`do`-记法还提供了使用某些单子转换器的语法。

# 单分支 {kw}`if`
%%%
tag := "single-branched-if"
file := "Single-Branched-if"
%%%

在单子中工作时，一种常见模式是仅当某个条件为真时才执行副作用。
例如，{anchorName countLettersModify (module := Examples.MonadTransformers.Defs)}`countLetters` 包含对元音或辅音的检查，而既非元音也非辅音的字母不会对状态产生影响。
这是通过使 {kw}`else` 分支求值为 {anchorTerm countLettersModify (module := Examples.MonadTransformers.Defs)}`pure ()` 来表达的，后者没有任何效果：

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

当 {kw}`if` 是 {kw}`do` 块中的一条语句，而不是一个表达式时，可以简单地省略 {anchorTerm countLettersModify (module:=Examples.MonadTransformers.Defs)}`else pure ()`，Lean 会自动插入它。
下面的 {anchorName countLettersNoElse}`countLetters` 定义是完全等价的：

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
使用状态单子来统计列表中满足某个单子式检查的项数的程序，可以写成如下形式：

```anchor count
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
```

类似地，{lit}`if not E1 then STMT...` 也可以改写为 {lit}`unless E1 do STMT...`。
{anchorName count}`count` 的相反情形，即统计不满足单子检查的条目，可以通过将 {kw}`if` 替换为 {kw}`unless` 来写成：

```anchor countNot
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
```

理解单分支的 {kw}`if` 和 {kw}`unless` 并不需要考虑单子转换器。
它们只是用 {anchorTerm count}`pure ()` 替换缺失的分支。
然而，本节中其余的扩展要求 Lean 自动重写 {kw}`do`-块，以便在写有 {kw}`do`-块的那个单子之上添加一个局部转换器。

# 提前返回
%%%
tag := "early-return"
file := "Early-Return"
%%%

标准库包含一个函数 {anchorName findHuh}`List.find?`，它返回列表中第一个满足某个检查的条目。
一个简单的实现不利用 {anchorName findHuh}`Option` 是单子这一事实，而是使用递归函数遍历列表，并用一个 {kw}`if` 在找到所需条目时停止循环：

```anchor findHuhSimple
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
```

命令式语言通常具有 {kw}`return` 关键字，它会中止函数的执行，并立即向调用者返回某个值。
在 Lean 中，这可用于 {kw}`do` 记法中，并且 {kw}`return` 会停止一个 {kw}`do` 块的执行，其中 {kw}`return` 的参数就是从单子返回的值。
换言之，{anchorName findHuhFancy}`List.find?` 本可以这样写：

```anchor findHuhFancy
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs
```

命令式语言中的提前返回有点像一种只能导致当前栈帧被展开的异常。
提前返回和异常都会终止一个代码块的执行，实际上是用被抛出的值替换周围的代码。
在幕后，Lean 中的提前返回是使用 {anchorName runCatch}`ExceptT` 的一个版本实现的。
每个使用提前返回的 {kw}`do`-块都会被包裹在异常处理器中（就函数 {anchorName MonadExcept (module:=Examples.MonadTransformers.Defs)}`tryCatch` 的意义而言）。
提前返回会被翻译为将该值作为异常抛出，而处理器会捕获被抛出的值并立即返回它。
换言之，{kw}`do`-块原本的返回值类型也被用作异常类型。

更具体地说，当异常类型和返回类型相同时，辅助函数 {anchorName runCatch}`runCatch` 会从单子转换器栈的顶层剥去一层 {anchorName runCatch}`ExceptT`：

```anchor runCatch
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
```
在 {anchorName findHuh}`List.find?` 中使用提前返回的 {kw}`do`-块，会通过用 {anchorName desugaredFindHuh}`runCatch` 包裹并将提前返回替换为 {anchorName desugaredFindHuh}`throw`，被翻译为一个不使用提前返回的 {kw}`do`-块：

```anchor desugaredFindHuh
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
```

提前返回有用的另一种情形是：当命令行应用程序的参数或输入不正确时提前终止。
许多程序在进入程序主体之前，都会以一段验证参数和输入的代码开始。
下面这个 {ref "running-a-program"}[问候程序 {lit}`hello-name`] 的版本检查是否未提供任何命令行参数：
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
不带参数运行它并输入名称 {lit}`David`，会得到与前一个版本相同的结果：
```commands «early-return» "early-return"
$ printf 'David\n' | lean --run EarlyReturn.lean # lean --run EarlyReturn.lean
How would you like to be addressed?
Hello, David!
```

把名字作为命令行参数而不是作为回答提供，会导致错误：
```commands «early-return» "early-return"
$ lean --run EarlyReturn.lean David || true # lean --run EarlyReturn.lean David
Expected no arguments, but got 1
```

而不提供名称则会导致另一个错误：
```commands «early-return» "early-return"
$ printf '\n' | lean --run EarlyReturn.lean || true # lean --run EarlyReturn.lean
How would you like to be addressed?
No name provided
```

使用提前返回的程序避免了嵌套控制流的需要，如同下面这个不使用提前返回的版本中所做的那样：
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

Lean 中的提前返回与命令式语言中的提前返回之间有一个重要区别：Lean 的提前返回只作用于当前的 {kw}`do`-块。
当一个函数的整个定义都位于同一个 {kw}`do` 块中时，这一区别并不重要。
但是，如果 {kw}`do` 出现在某些其他结构之下，那么这一区别就会变得明显。
例如，给定 {anchorName greet}`greet` 的如下定义：

```anchor greet
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
```
表达式 {anchorTerm greetDavid}`greet "David"` 求值为 {anchorTerm greetDavid}`"Hello, David"`，而不仅仅是 {anchorTerm greetDavid}`"David"`。

# 循环
%%%
tag := "loops"
file := "Loops"
%%%

正如每个带有可变状态的程序都可以改写为一个把状态作为参数传递的程序，每个循环也都可以改写为一个递归函数。
从一个角度看，{anchorName findHuh}`List.find?` 作为递归函数最为清晰。
毕竟，它的定义反映了列表的结构：如果头部通过检查，那么就应返回它；否则就在尾部中查找。
当不再剩有条目时，答案是 {anchorName findHuhSimple}`none`。
从另一个角度看，{anchorName findHuh}`List.find?` 作为循环最为清晰。
毕竟，该程序按顺序查看各条目，直到找到一个令人满意的条目为止，此时它终止。
如果循环终止而没有返回，答案就是 {anchorName findHuhSimple}`none`。

## 使用 ForM 循环
%%%
tag := "looping-with-forM"
file := "Looping-with-ForM"
%%%

Lean 包含一个类型类，用于描述在某个单子中对容器类型进行循环。
这个类称为 {anchorName ForM}`ForM`：

```anchor ForM
class ForM (m : Type u → Type v) (γ : Type w₁)
    (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit
```
这个类相当一般。
参数 {anchorName ForM}`m` 是带有某些所需效果的单子，{anchorName ForM}`γ` 是要遍历的集合，{anchorName ForM}`α` 是集合中元素的类型。
通常，允许 {anchorName ForM}`m` 是任意单子，但也可能存在某种数据结构，例如只支持在 {anchorName printArray}`IO` 中进行循环。
方法 {anchorName ForM}`forM` 接受一个集合、一个要对集合中每个元素运行以产生其效果的单子动作，并负责运行这些动作。

{anchorName ListForM}`List` 的实例允许 {anchorName ListForM}`m` 是任意单子，它将 {anchorName ForM}`γ` 设为 {anchorTerm ListForM}`List α`，并将该类的 {anchorName ForM}`α` 设为列表中出现的同一个 {anchorName ListForM}`α`：

```anchor ListForM
def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action

instance : ForM m (List α) α where
  forM := List.forM
```
{ref "reader-io-implementation"}[来自 {lit}`doug` 的函数 {anchorName doList (module := DirTree)}`doList`] 对列表而言是 {anchorName ForM}`forM`。
由于 {anchorName countLettersForM}`forM` 旨在用于 {kw}`do` 块，因此它使用 {anchorName ForM}`Monad` 而不是 {anchorName OptionTExec}`Applicative`。
{anchorName ForM}`forM` 可用于使 {anchorName countLettersForM}`countLetters` 短得多：

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

由于 {anchorName ForM}`γ` 可以是任意类型，{anchorName ForM}`ForM` 可以支持非多态集合。
一个非常简单的集合是小于某个给定数的自然数，并按逆序排列：

```anchor AllLessThan
structure AllLessThan where
  num : Nat
```
其 {anchorName ForM}`ForM` 运算符会将给定的动作应用于每个较小的 {anchorName ListCount}`Nat`：

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
可以使用 {anchorName ForM}`ForM` 在每个小于五的数上运行 {anchorName AllLessThanForMRun}`IO.println`：
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

一个只在特定单子中工作的 {anchorName ForM}`ForM` 实例，是对从 IO 流（例如标准输入）读取的各行进行循环的实例：
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
{anchorName ForM}`ForM` 的定义被标记为 {kw}`partial`，因为不能保证该流是有限的。
在此情况下，{anchorName ranges}`IO.FS.Stream.getLine` 只在 {anchorName countToThree}`IO` 单子中工作，因此不能使用其他单子进行循环。

这个示例程序使用这种循环构造来过滤掉不包含字母的行：
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
调用这个存储在 {lit}`ForMIO.lean` 中的程序，会产生如下输出：
```commands formio "formio"
$ lean --run ForMIO.lean < test-data
Hello!
abc123
Ok
```

## 停止迭代
%%%
tag := "break"
file := "Stopping-Iteration"
%%%

使用 {anchorName ForM}`ForM` 很难提前终止循环。
编写一个函数，使其只在达到 {anchorTerm OptionTcountToThree}`3` 之前迭代 {anchorName AllLessThan}`AllLessThan` 中的 {anchorName AllLessThan}`Nat`，需要一种在循环中途停止的方法。
实现这一点的一种方式是将 {anchorName ForM}`ForM` 与 {anchorName OptionTExec}`OptionT` 单子转换器结合使用。
第一步是定义 {anchorName OptionTExec}`OptionT.exec`，它丢弃关于返回值以及被转换的计算是否成功的两方面信息：

```anchor OptionTExec
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
```
于是，{anchorName AlternativeOptionT (module:=Examples.MonadTransformers.Defs)}`Alternative` 的 {anchorName OptionTExec}`OptionT` 实例中的失败可以用来提前终止循环：

```anchor OptionTcountToThree
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
```
一个快速测试表明此解法有效：
```anchor optionTCountSeven
#eval countToThree 7
```
```anchorInfo optionTCountSeven
6
5
4
3
```

然而，这段代码不太容易阅读。
提前终止循环是一项常见任务，Lean 提供了更多语法糖来使其更容易。
同一个函数也可以写成如下形式：

```anchor countToThree
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
```
对它进行测试表明，它的工作方式与先前版本完全相同：
```anchor countSevenFor
#eval countToThree 7
```
```anchorInfo countSevenFor
6
5
4
3
```

{kw}`for`{lit}` ...`{kw}`in`{lit}` ...`{kw}`do`{lit}` ...` 语法会脱糖为对一个名为 {anchorName ForInIOAllLessThan}`ForIn` 的类型类的使用；它是 {anchorName ForM}`ForM` 的一个稍微更复杂的版本，会跟踪状态和提前终止。
标准库提供了一个适配器，称为 {anchorName ForInIOAllLessThan}`ForM.forIn`，它把 {anchorName ForM}`ForM` 实例转换为 {anchorName ForInIOAllLessThan}`ForIn` 实例。
若要启用基于 {anchorName ForM}`ForM` 实例的 {kw}`for` 循环，请添加如下内容，并用适当的内容替换 {anchorName AllLessThan}`AllLessThan` 和 {anchorName AllLessThan}`Nat`：

```anchor ForInIOAllLessThan
instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
```
然而请注意，此适配器只适用于那些保持单子不受约束的 {anchorName ForM}`ForM` 实例，而大多数实例确实如此。
这是因为该适配器使用的是 {anchorName SomeMonads (module:=Examples.MonadTransformers.Defs)}`StateT` 和 {anchorName SomeMonads (module:=Examples.MonadTransformers.Defs)}`ExceptT`，而不是底层单子。

{kw}`for` 循环支持提前返回。
将带有提前返回的 {kw}`do` 块翻译为对异常单子转换器的使用，在 {anchorName ForM}`ForM` 之下同样适用，正如先前使用 {anchorName OptionTExec}`OptionT` 来停止迭代一样。
这个 {anchorName findHuh}`List.find?` 版本同时使用了二者：

```anchor findHuh
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
```

除了 {kw}`break` 之外，{kw}`for` 循环还支持 {kw}`continue`，以便在一次迭代中跳过循环体的其余部分。
{anchorName findHuhCont}`List.find?` 的一种替代（但令人困惑的）表述会跳过不满足检查的元素：

```anchor findHuhCont
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
```

{anchorName ranges}`Std.Range` 是一个由起始数、结束数和步长组成的结构。
它们表示一个自然数序列，从起始数到结束数，每次按步长递增。
Lean 有专门的语法来构造范围，该语法由方括号、数字和冒号组成，共有四种形式。
终止点必须始终提供，而起点和步长是可选的，分别默认为 {anchorTerm ranges}`0` 和 {anchorTerm ranges}`1`：

:::table +header
*
 *  表达式
 *  起点
 *  停止
 *  步骤
 *  作为 List

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

注意，起始数_会_包含在范围中，而停止数不会。
三个参数全都是 {anchorName three}`Nat`，这意味着范围不能倒数；若某个范围的起始数大于或等于停止数，则该范围根本不包含任何数。

范围可以与 {kw}`for` 循环一起使用，以从范围中取出数字。
该程序统计从四到八之间的偶数个数：

```anchor fourToEight
def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i
```
运行它会得到：
```anchorInfo fourToEightOut
4
6
8
```


最后，{kw}`for` 循环支持并行地遍历多个集合，方法是用逗号分隔 {kw}`in` 子句。
当第一个集合耗尽元素时，循环停止，因此以下声明：

```anchor parallelLoop
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4:8] do
    IO.println (x, y)
```
会产生三行输出：
```anchor parallelLoopOut
#eval parallelLoop
```
```anchorInfo parallelLoopOut
(currant, 4)
(gooseberry, 5)
(rowan, 6)
```

许多数据结构实现了 {anchorName ForInIOAllLessThan}`ForIn` 类型类的增强版本，它会向循环体添加元素来自该集合的证据。
可以通过在元素名称之前为该证据提供一个名称来使用这些版本。
此函数会打印数组的所有元素及其索引，并且由于证据 {anchorName printArray}`h`，编译器能够确定这些数组查找都是安全的：

```anchor printArray
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in [0:xs.size] do
    IO.println s!"{i}:\t{xs[i]}"
```
在这个例子中，{anchorName printArray}`h` 是表明 {lit}`i ∈ [0:xs.size]` 的证据，而检查 {anchorTerm printArray}`xs[i]` 是否安全的策略能够将其转换为表明 {lit}`i < xs.size` 的证据。

# 可变变量
%%%
tag := "let-mut"
file := "Mutable-Variables"
%%%

除了提前 {kw}`return`、无 {kw}`else` 的 {kw}`if` 以及 {kw}`for` 循环之外，Lean 还支持在 {kw}`do` 块内使用局部可变变量。
在幕后，这些可变变量会被脱糖为等价于 {anchorName twoStateT}`StateT` 的代码，而不是通过真正的可变变量来实现。
函数式编程再次被用来模拟命令式编程。

局部可变变量用 {kw}`let mut` 引入，而不是用普通的 {kw}`let`。
定义 {anchorName two}`two` 使用恒等单子 {anchorName sameBlock}`Id` 来启用 {kw}`do` 语法而不引入任何效应，它计数到 {anchorTerm ranges}`2`：

```anchor two
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
```
这段代码等价于一个使用 {anchorName twoStateT}`StateT` 两次添加 {anchorTerm twoStateT}`1` 的定义：

```anchor twoStateT
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
```

局部可变变量可以很好地配合 {kw}`do` 记法的所有其他特性，这些特性为单子转换器提供了方便的语法。
定义 {anchorName three}`three` 会计算一个含有三个条目的列表中的条目数量：

```anchor three
def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
```
类似地，{anchorName six}`six` 会把列表中的项相加：

```anchor six
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
```

{anchorName ListCount}`List.count` 统计列表中满足某个检查的条目数：

```anchor ListCount
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
```

与显式地局部使用 {anchorName twoStateT}`StateT` 相比，局部可变变量使用起来可能更方便，也更易读。
然而，它们不具备命令式语言中不受限制的可变变量的全部能力。
特别地，它们只能在引入它们的 {kw}`do` 块中被修改。
这意味着，例如，{kw}`for` 循环不能被其他方面等价的递归辅助函数替代。
这个 {anchorName nonLocalMut}`List.count` 版本：
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
在尝试修改 {anchorName nonLocalMut}`found` 时会产生以下错误：
```anchorError nonLocalMut
`found` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `found`, consider using `let found` instead
```
这是因为递归函数是在恒等单子中编写的，只有引入该变量的 {kw}`do`-块的单子才会通过 {anchorName twoStateT}`StateT` 转换。

# 什么算作一个 {kw}`do` 块？
%%%
tag := "do-block-boundaries"
file := "What-counts-as-a-do-block___"
%%%

{kw}`do`-记法的许多特性只作用于单个 {kw}`do`-块。
提前返回会终止当前块，而可变变量只能在定义它们的块中被改变。
为了有效使用这些特性，重要的是要知道什么算作“同一个块”。

一般而言，紧随 {kw}`do` 关键字之后的缩进代码块算作一个块，而其下方紧接着的一系列语句是该块的一部分。
处于独立块中的语句，即使这些独立块仍然包含在某个块之内，也不被视为该块的一部分。
然而，支配究竟什么算作同一个块的规则略为微妙，因此有必要给出一些例子。
可以通过构造一个带有可变变量的程序，并观察哪些位置允许进行变更，来检验这些规则的精确性质。
此程序中的一次变更显然与该可变变量位于同一个块中：

```anchor sameBlock
example : Id Unit := do
  let mut x := 0
  x := x + 1
```

当一次变更发生在某个 {kw}`do` 块中，而该块属于一个使用 {lit}`:=` 定义名称的 {kw}`let` 语句时，那么它不被认为是该块的一部分：
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
然而，出现在使用 {lit}`←` 定义名称的 {kw}`let` 语句之下的 {kw}`do` 块，会被视为外围块的一部分。
以下程序会被接受：

```anchor letBodyArrBlock
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other
```

类似地，作为函数实参出现的 {kw}`do`-块独立于其周围的块。
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

如果 {kw}`do` 关键字完全是冗余的，那么它不会引入新的块。
这个程序会被接受，并且等价于本节中的第一个程序：

```anchor collapsedBlock
example : Id Unit := do
  let mut x := 0
  do x := x + 1
```

{kw}`do` 下各分支的内容（例如由 {kw}`match` 或 {kw}`if` 引入的分支）被视为外围块的一部分，无论是否添加了冗余的 {kw}`do`。
以下程序都会被接受：

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
类似地，作为 {kw}`for` 和 {kw}`unless` 语法一部分出现的 {kw}`do` 只是它们语法的一部分，并不会引入一个新的 {kw}`do` 块。
这些程序也会被接受：

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


# 命令式编程还是函数式编程？
%%%
tag := none
file := "Imperative-or-Functional-Programming___"
%%%

Lean 的 {kw}`do` 记法所提供的命令式特性，使许多程序能够非常接近其在 Rust、Java 或 C# 等语言中的对应程序。
在将命令式算法翻译到 Lean 中时，这种相似性非常方便；并且有些任务本来就最自然地以命令式方式来思考。
单子和单子转换器的引入，使得命令式程序能够在纯函数式语言中编写；而 {kw}`do` 记法作为单子（可能经过局部转换）的专门语法，使函数式程序员能够兼得两全：不可变性所赋予的强大推理原则，以及通过类型系统对可用效应的严格控制，与使使用效应的程序看起来熟悉且易于阅读的语法和库结合在一起。
单子和单子转换器使函数式编程与命令式编程之分成为视角问题。


# 练习
%%%
tag := "monad-transformer-do-exercises"
file := "Exercises"
%%%

 * 将 {lit}`doug` 改写为使用 {kw}`for`，而不是使用 {anchorName doList (module:=DirTree)}`doList` 函数。
 * 是否还有其他机会使用本节引入的特性来改进代码？如果有，请使用它们！
