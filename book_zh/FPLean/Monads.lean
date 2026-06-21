import VersoManual
import FPLean.Examples

import FPLean.Monads.Class
import FPLean.Monads.Arithmetic
import FPLean.Monads.Do
import FPLean.Monads.IO
import FPLean.Monads.Conveniences
import FPLean.Monads.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "单子" =>
%%%
tag := "monads"
file := "Monads"
%%%

在 C# 和 Kotlin 中，{CSharp}`?.` 运算符是一种在可能为空的值上查找属性或调用方法的方式。
如果接收者是 {CSharp}`null`，则整个表达式为空。
否则，底层的非 {CSharp}`null` 值接收该调用。
{CSharp}`?.` 的使用可以串联起来；在这种情况下，第一个 {Kotlin}`null` 结果会终止这一查找链。
像这样串联空值检查，比编写和维护深层嵌套的 {kw}`if` 要方便得多。

类似地，异常比手动检查并传播错误码方便得多。
同时，日志记录最容易通过专门的日志框架来实现，而不是让每个函数同时返回其日志结果和返回值。
链式空值检查和异常通常要求语言设计者预先考虑这种用例，而日志框架通常利用副作用，将记录日志的代码与日志的累积解耦。

# 一个 API，多种应用
%%%
tag := "monad-api-examples"
file := "One-API___-Many-Applications"
%%%

所有这些特性以及更多特性都可以作为名为 {moduleName}`Monad` 的公共 API 的实例，在库代码中实现。
Lean 提供了专门的语法，使这个 API 使用起来很方便，但也可能妨碍理解幕后究竟发生了什么。
本章从手动嵌套空值检查这种细节层面的呈现开始，并在此基础上逐步构建到方便而通用的 API。
在此期间，请暂时搁置你的怀疑。

## 检查 {lit}`none`：不要重复自己
%%%
tag := "example-option-monad"
file := "Checking-for-none___-Don___t-Repeat-Yourself"
%%%

:::paragraph
在 Lean 中，模式匹配可用于串联空值检查。
从列表中取得第一个条目可以直接使用可选索引记法：

```anchor first
def first (xs : List α) : Option α :=
  xs[0]?
```
:::

:::paragraph
结果必须是 {anchorName first}`Option`，因为空列表没有第一个条目。
提取第一个和第三个条目需要检查每一个都不是 {moduleName}`none`：

```anchor firstThird
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)
```
类似地，提取第一、第三和第五个条目需要进行更多检查，以确保这些值不是 {moduleName}`none`：

```anchor firstThirdFifth
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)
```
而向这个序列添加第七个条目开始变得相当难以管理：

```anchor firstThirdFifthSeventh
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)
```
:::

:::paragraph
这段代码的根本问题在于它处理了两个关注点：提取这些数字，以及检查它们是否全部存在。
第二个关注点是通过复制并粘贴处理 {moduleName}`none` 情形的代码来解决的。
通常，将重复的片段提升为辅助函数是一种良好的风格：

```anchor andThenOption
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
```
这个辅助函数的用法类似于 C# 和 Kotlin 中的 {CSharp}`?.`，它负责传播 {moduleName}`none` 值。
它接受两个参数：一个可选值，以及一个在该值不是 {moduleName}`none` 时应用的函数。
如果第一个参数是 {moduleName}`none`，则该辅助函数返回 {moduleName}`none`。
如果第一个参数不是 {moduleName}`none`，则将该函数应用于 {moduleName}`some` 构造子的内容。
:::

:::paragraph
现在，{anchorName firstThirdandThen}`firstThird` 可以改写为使用 {anchorName firstThirdandThen}`andThen` 而不是模式匹配：

```anchor firstThirdandThen
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
```
在 Lean 中，函数作为参数传递时不需要用括号括起来。
下面这个等价定义使用了更多括号，并缩进了函数体：

```anchor firstThirdandThenExpl
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
```
{anchorName firstThirdandThenExpl}`andThen` 辅助函数提供了一种让值流经其中的“管道”，而带有略显不同寻常缩进的版本更能暗示这一点。
改进用于编写 {anchorName firstThirdandThenExpl}`andThen` 的语法，可以使这些计算更易理解。
:::

### 中缀运算符
%%%
tag := "defining-infix-operators"
file := "Infix-Operators"
%%%


在 Lean 中，可以使用 {kw}`infix`、{kw}`infixl` 和 {kw}`infixr` 命令声明中缀运算符，它们分别创建非结合、左结合和右结合的运算符。
当连续多次使用时，{deftech}_左结合_运算符会把左括号堆叠在表达式的左侧。
加法运算符 {lit}`+` 是左结合的，因此 {anchorTerm plusFixity}`w + x + y + z` 等价于 {anchorTerm plusFixity}`(((w + x) + y) + z)`。
指数运算符 {lit}`^` 是右结合的，因此 {anchorTerm powFixity}`w ^ x ^ y ^ z` 等价于 {anchorTerm powFixity}`w ^ (x ^ (y ^ z))`。
诸如 {lit}`<` 这样的比较运算符是非结合的，因此 {lit}`x < y < z` 是语法错误，需要手动添加括号。

:::paragraph
以下声明将 {anchorName andThenOptArr}`andThen` 变成一个中缀运算符：

```anchor andThenOptArr
infixl:55 " ~~> " => andThen
```
冒号后面的数字声明新中缀运算符的 {deftech}_优先级_。
在通常的数学记法中，{anchorTerm plusTimesPrec}`x + y * z` 等价于 {anchorTerm plusTimesPrec}`x + (y * z)`，尽管 {lit}`+` 和 {lit}`*` 都是左结合的。
在 Lean 中，{lit}`+` 的优先级为 65，{lit}`*` 的优先级为 70。
高优先级运算符先于低优先级运算符应用。
根据 {lit}`~~>` 的声明，{lit}`+` 和 {lit}`*` 都具有更高的优先级，因此会先被应用。
通常，为一组运算符确定最方便的优先级需要一些实验和大量示例。
:::

紧随新的中缀运算符之后的是双箭头 {lit}`=>`，它指定要用于该中缀运算符的具名函数。
Lean 的标准库使用此功能将 {lit}`+` 和 {lit}`*` 定义为分别指向 {moduleName}`HAdd.hAdd` 和 {moduleName}`HMul.hMul` 的中缀运算符，从而允许使用类型类来重载这些中缀运算符。
然而在这里，{anchorName firstThirdandThen}`andThen` 只是一个普通函数。

:::paragraph
为 {anchorName andThenOptArr}`andThen` 定义了中缀运算符之后，可以用一种将 {moduleName}`none`-检查的“管道”感觉置于核心位置的方式重写 {anchorName firstThirdInfix (show := firstThird)}`firstThirdInfix`：

```anchor firstThirdInfix
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
```
在编写较大的函数时，这种风格要简洁得多：
```anchor firstThirdFifthSeventInfix
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
```
:::

## 传播错误消息
%%%
tag := "example-except-monad"
file := "Propagating-Error-Messages"
%%%

像 Lean 这样的纯函数式语言没有用于错误处理的内置异常机制，因为抛出或捕获异常超出了表达式逐步求值模型的范围。
然而，函数式程序当然需要处理错误。
在 {anchorName firstThirdFifthSeventInfix}`firstThirdFifthSeventh` 的情形中，用户很可能需要知道列表到底有多长，以及查找是在何处失败的。

:::paragraph
这通常通过定义一种既可以是错误也可以是结果的数据类型，并将带异常的函数翻译为返回该数据类型的函数来完成：

```anchor Except
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr
```
类型变量 {anchorName Except}`ε` 表示该函数可能产生的错误的类型。
调用者应当同时处理错误和成功，这使得类型变量 {anchorName Except}`ε` 所起的作用有点类似于 Java 中受检异常列表的作用。
:::

:::paragraph
与 {anchorName first}`Option` 类似，{anchorName Except}`Except` 可以用来表示未能在列表中找到某个条目。
在这种情况下，错误类型是 {moduleName}`String`：

```anchor getExcept
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
```
查找一个在界内的值会得到一个 {anchorName ExceptExtra}`Except.ok`：
```anchor ediblePlants
def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
```
```anchor success
#eval get ediblePlants 2
```
```anchorInfo success
Except.ok "sea buckthorn"
```
查找越界值会产生一个 {anchorName ExceptExtra}`Except.error`：
```anchor failure
#eval get ediblePlants 4
```
```anchorInfo failure
Except.error "Index 4 not found (maximum is 3)"
```
:::

:::paragraph
一次列表查找可以方便地返回一个值或一个错误：
```anchor firstExcept
def first (xs : List α) : Except String α :=
  get xs 0
```
然而，执行两次列表查找需要处理潜在的失败：
```anchor firstThirdExcept
def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)
```
向该函数添加另一次列表查找需要更多的错误处理：
```anchor firstThirdFifthExcept
def firstThirdFifth (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)
```
再增加一次列表查找后，情况开始变得相当难以管理：
```anchor firstThirdFifthSeventhExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)
```
:::

:::paragraph
再一次，可以将一种常见模式分解出来作为辅助函数。
函数中的每一步都会检查是否有错误，并且只有当结果为成功时，才继续进行其余计算。
可以为 {anchorName andThenExcept}`Except` 定义 {anchorName andThenExcept}`andThen` 的一个新版本：

```anchor andThenExcept
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
```
正如 {anchorName first}`Option` 的情形一样，这个 {anchorName andThenExcept}`andThen` 版本允许对 {anchorName firstThirdAndThenExcept}`firstThird'` 作出更简洁的定义：

```anchor firstThirdAndThenExcept
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
```
:::

:::paragraph
在 {anchorName first}`Option` 和 {anchorName andThenExcept}`Except` 两种情形中，都有两个重复出现的模式：一是在每一步检查中间结果，这已经被分解到 {anchorName andThenExcept}`andThen` 中；二是最终的成功结果，分别是 {moduleName}`some` 或 {anchorName andThenExcept}`Except.ok`。
为方便起见，可以将成功分解到一个名为 {anchorName okExcept}`ok` 的辅助函数中：

```anchor okExcept
def ok (x : α) : Except ε α := Except.ok x
```
类似地，失败可以被分解到一个名为 {anchorName failExcept}`fail` 的辅助函数中：

```anchor failExcept
def fail (err : ε) : Except ε α := Except.error err
```
使用 {anchorName okExcept}`ok` 和 {anchorName failExcept}`fail` 会使 {anchorName getExceptEffects}`get` 稍微更易读：

```anchor getExceptEffects
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
```
:::

:::paragraph
添加 {anchorName andThenExceptInfix}`andThen` 的中缀声明后，{anchorName firstThirdInfixExcept}`firstThird` 可以像返回 {anchorName first}`Option` 的版本一样简洁：

```anchor andThenExceptInfix
infixl:55 " ~~> " => andThen
```

```anchor firstThirdInfixExcept
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
```
这种技术同样可以扩展到更大的函数：

```anchor firstThirdFifthSeventInfixExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
```

:::

## 日志记录
%%%
tag := "logging"
file := "Logging"
%%%

:::paragraph
如果一个数除以 2 后没有余数，则它是偶数：
```anchor isEven
def isEven (i : Int) : Bool :=
  i % 2 == 0
```
函数 {anchorName sumAndFindEvensDirect}`sumAndFindEvens` 在计算列表之和的同时，记住过程中遇到的偶数：
```anchor sumAndFindEvensDirect
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)
```
:::

:::paragraph
此函数是一个常见模式的简化示例。
许多程序需要遍历一次数据结构，同时既计算一个主要结果，又累积某种第三类附加结果。
日志记录就是一个例子：作为 {moduleName}`IO` 动作的程序总是可以记录到磁盘上的文件中，但由于磁盘处于 Lean 函数的数学世界之外，基于 {moduleName}`IO` 证明关于日志的性质就会困难得多。
另一个例子是这样一个函数：它通过中序遍历计算一棵树中所有节点的和，同时记录访问过的每个节点：

```anchor inorderSum
def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited,
     leftSum + hereSum + rightSum)
```
:::

{anchorName sumAndFindEvensDirect}`sumAndFindEvens` 和 {anchorName inorderSum}`inorderSum` 都具有共同的重复结构。
每一步计算都会返回一个对偶，其中包含一个已保存数据的列表以及主要结果。
随后将这些列表追加起来，并计算主要结果，再将其与追加后的列表配对。
通过对 {anchorName sumAndFindEvensDirectish}`sumAndFindEvens` 作一个小的重写，将保存偶数和计算总和这两个关注点更清晰地分离开来，这种共同结构会变得更加明显：

```anchor sumAndFindEvensDirectish
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)
```

为清晰起见，可以给由一个累积结果和一个值组成的对赋予自己的名称：

```anchor WithLog
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
```
类似地，在把一个值传递给计算的下一步时保存累计结果列表的过程，也可以再次分解到一个名为 {anchorName andThenWithLog}`andThen` 的辅助函数中：

```anchor andThenWithLog
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
```
在错误的情形中，{anchorName okWithLog}`ok` 表示一个总是成功的操作。
然而在这里，它是一个只返回值而不记录任何日志的操作：

```anchor okWithLog
def ok (x : β) : WithLog α β := {log := [], val := x}
```
正如 {anchorName Except}`Except` 提供 {anchorName failExcept}`fail` 作为一种可能性一样，{anchorName WithLog}`WithLog` 应允许向日志中添加条目。
这没有与之相关的有意义返回值，因此它返回 {anchorName save}`Unit`：

```anchor save
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}
```

{anchorName WithLog}`WithLog`、{anchorName andThenWithLog}`andThen`、{anchorName okWithLog}`ok` 和 {anchorName save}`save` 可用于在这两个程序中将日志记录关注点与求和关注点分离：

```anchor sumAndFindEvensAndThen
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThen (if isEven i then save i else ok ()) fun () =>
    andThen (sumAndFindEvens is) fun sum =>
    ok (i + sum)
```

```anchor inorderSumAndThen
def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSum l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSum r) fun rightSum =>
    ok (leftSum + x + rightSum)
```
并且，再一次，中缀运算符有助于把注意力集中在正确的步骤上：

```anchor infixAndThenLog
infixl:55 " ~~> " => andThen
```

```anchor withInfixLogging
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
```

## 为树节点编号
%%%
tag := "numbering-tree-nodes"
file := "Numbering-Tree-Nodes"
%%%

树的{deftech}_中序编号_会把树中的每个数据点与它在该树的中序遍历中被访问的步骤关联起来。
例如，考虑 {anchorName aTree}`aTree`：

```anchor aTree
open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)
```
它的中序编号为：
```anchorInfo numberATree
BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.branch (BinTree.leaf) (1, "b") (BinTree.leaf)))
    (2, "c")
    (BinTree.leaf))
  (3, "d")
  (BinTree.branch (BinTree.leaf) (4, "e") (BinTree.leaf))
```

:::paragraph
树最自然地用递归函数处理，但通常的树递归模式使得计算中序编号变得困难。
这是因为左子树中任意位置所分配的最大编号既用于确定某个节点数据值的编号，又再次用于确定右子树编号的起点。
在命令式语言中，可以通过使用一个包含下一个待分配编号的可变变量来绕过这个问题。
下面的 Python 程序使用可变变量计算中序编号：
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := code)
class Branch:
    def __init__(self, value, left=None, right=None):
        self.left = left
        self.value = value
        self.right = right
    def __repr__(self):
        return f'Branch({self.value!r}, left={self.left!r}, right={self.right!r})'

def number(tree):
    num = 0
    def helper(t):
        nonlocal num
        if t is None:
            return None
        else:
            new_left = helper(t.left)
            new_value = (num, t.value)
            num += 1
            new_right = helper(t.right)
            return Branch(left=new_left, value=new_value, right=new_right)

    return helper(tree)
```
与 {anchorName aTree}`aTree` 等价的 Python 程序的编号为：
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := a_tree)
a_tree = Branch("d",
                left=Branch("c",
                            left=Branch("a", left=None, right=Branch("b")),
                            right=None),
                right=Branch("e"))
```
而它的编号为：
```command inorderpy "inorder_python" (prompt := ">>> ") (show := "number(a_tree)")
python3 inordernumbering.py
```
```commandOut inorderpy "python3 inordernumbering.py"
Branch((3, 'd'), left=Branch((2, 'c'), left=Branch((0, 'a'), left=None, right=Branch((1, 'b'), left=None, right=None)), right=None), right=Branch((4, 'e'), left=None, right=None))
```
:::


尽管 Lean 没有可变变量，但存在一种变通方法。
从外部世界其余部分的角度来看，可变变量可以被认为有两个相关方面：函数被调用时它的值，以及函数返回时它的值。
换言之，使用可变变量的函数可以看作这样一个函数：它把该可变变量的起始值作为参数，并返回由该变量的最终值和函数结果组成的对。
然后，这个最终值可以作为参数传递给下一步。

:::paragraph
正如 Python 示例使用一个外层函数来建立可变变量，并使用一个内层辅助函数来改变该变量一样，这个函数的 Lean 版本使用一个外层函数来提供该变量的起始值，并显式返回函数的结果；同时使用一个内层辅助函数，在计算已编号树的过程中穿引该变量的值：

```anchor numberDirect
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd
```
这段代码与传播 {moduleName}`none` 的 {anchorName first}`Option` 代码、传播 {anchorName exceptNames (show := error)}`Except.error` 的 {anchorName exceptNames}`Except` 代码以及累积日志的 {moduleName}`WithLog` 代码一样，混合了两个关注点：传播计数器的值，以及实际遍历树来寻找结果。
正如在那些情形中一样，可以定义一个 {anchorName andThenState}`andThen` 辅助函数，将状态从计算的一步传播到下一步。
第一步是为这样一种模式命名：以输入状态作为参数，并返回输出状态以及一个值：

```anchor State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
```
:::

:::paragraph
在 {anchorName State}`State` 的情况下，{anchorName okState}`ok` 是一个函数，它返回未改变的输入状态，并同时返回给定的值：
```anchor okState
def ok (x : α) : State σ α :=
  fun s => (s, x)
```
:::

:::paragraph
处理可变变量时，有两个基本操作：读取其值，以及用一个新值替换它。
读取当前值是通过一个函数完成的，该函数将输入状态不加修改地放入输出状态，同时也将其放入值字段：
```anchor get
def get : State σ σ :=
  fun s => (s, s)
```
写入一个新值包括忽略输入状态，并将所提供的新值放入输出状态中：
```anchor set
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
```
:::

:::paragraph
最后，可以将两个使用状态的计算按顺序组合：先求出第一个函数的输出状态和返回值，然后将二者都传入下一个函数：

```anchor andThenState
def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
```
:::

:::paragraph
使用 {anchorName State}`State` 及其辅助函数，可以模拟局部可变状态：

```anchor numberMonadicish
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
因为 {anchorName State}`State` 只模拟一个局部变量，所以 {anchorName get}`get` 和 {anchorName set}`set` 不需要引用任何特定的变量名。
:::

## 单子：一种函数式设计模式
%%%
tag := "monad-as-design-pattern"
file := "Monads___-A-Functional-Design-Pattern"
%%%

这些示例中的每一个都包含：
 * 一个多态类型，例如 {anchorName first}`Option`、{anchorTerm okExcept}`Except ε`、{anchorTerm save}`WithLog α` 或 {anchorTerm andThenState}`State σ`
 * 一个运算符 {lit}`andThen`，用于处理具有此类型的程序在顺序组合时某些重复性的方面
 * 一个运算符 {lit}`ok`，它（在某种意义上）是使用该类型的最无趣方式
 * 一组其他操作，例如 {moduleName}`none`、{anchorName failExcept}`fail`、{anchorName save}`save` 和 {anchorName get}`get`，它们为使用该类型的方式命名

这种风格的 API 称为{deftech}_单子_。
虽然单子的思想源自数学的一个分支，称为范畴论，但为了在编程中使用单子，并不需要理解范畴论。
单子的核心思想是：每个单子都使用纯函数式语言 Lean 所提供的工具，编码某一种特定的副作用。
例如，{anchorName first}`Option` 表示可能通过返回 {moduleName}`none` 而失败的程序，{moduleName}`Except` 表示可能抛出异常的程序，{moduleName}`WithLog` 表示运行时累积日志的程序，而 {anchorName State}`State` 表示带有单个可变变量的程序。

{include 1 FPLean.Monads.Class}

{include 1 FPLean.Monads.Arithmetic}

{include 1 FPLean.Monads.Do}

{include 1 FPLean.Monads.IO}

{include 1 FPLean.Monads.Conveniences}

{include 1 FPLean.Monads.Summary}
