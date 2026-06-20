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
%%%

在C#和Kotlin中，{CSharp}`?.`运算符是一种在可能为null的值上查找属性或调用方法的方式。如果接收到{CSharp}`null`，则整个表达式为null。否则，该非{CSharp}`null`值会被用于调用。多个{CSharp}`?.`可以链接起来，在这种情况下，第一个{Kotlin}`null`结果将终止查找链。像这样链接null检查比编写和维护深层嵌套的{kw}`if`方便得多。

类似地，异常机制比手动检查和传递错误码方便得多。同时，通过使用专用日志记录框架（而不是让每个函数同时返回其日志结果和返回值）可以轻松地完成日志记录。链接的空检查和异常通常要求语言设计者预料到这种用法，而日志记录框架通常利用副作用将记录日志的代码与日志的累积解耦。

# 一个API，多种应用
%%%
tag := "monad-api-examples"
%%%

所有这些功能以及更多功能都可以作为通用 API —— {moduleName}`Monad` 的实例在库代码中实现。Lean 提供了专门的语法，使此 API 易于使用，但也会妨碍理解幕后发生的事情。本章从手动嵌套空检查的细节介绍开始，并由此构建到方便、通用的 API。在此期间，请暂时搁置你的怀疑。

## 检查{lit}`none`：避免重复代码
%%%
tag := "example-option-monad"
%%%

:::paragraph
在Lean中，模式匹配可用于链接空检查。
从列表中获取第一个项可通过可选的索引记号：

```anchor first
def first (xs : List α) : Option α :=
  xs[0]?
```
:::

:::paragraph
结果必须是{anchorName first}`Option`，因为空列表没有第一个项。
提取第一个和第三个项需要检查每个项都不为{moduleName}`none`：

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
类似地，提取第一个、第三个和第五个项需要更多检查，以确保这些值不是{moduleName}`none`：

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
而将第七个项添加到此序列中则开始变得相当难以管理：

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
这段代码有两个问题：提取数字和检查它们是否全部存在，但第二个问题是通过复制粘贴处理{moduleName}`none`情况的代码来解决的。
通常鼓励将重复的片段提取到辅助函数中：

```anchor andThenOption
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
```
该辅助函数类似于C#和Kotlin中的{CSharp}`?.`，用于处理{moduleName}`none`值。
它接受两个参数：一个可选值和一个在该值非{moduleName}`none`时应用的函数。
如果第一个参数是{moduleName}`none`，则辅助函数返回{moduleName}`none`。
如果第一个参数不是{moduleName}`none`，则该函数将应用于{moduleName}`some`构造器的内容。
:::

:::paragraph
现在，{anchorName firstThirdandThen}`firstThird`可以使用{anchorName firstThirdandThen}`andThen`重写：

```anchor firstThirdandThen
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
```
在Lean中，作为参数传递时，函数不需要用括号括起来。
以下等价定义使用了更多括号并缩进了函数体：

```anchor firstThirdandThenExpl
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
```
{anchorName firstThirdandThenExpl}`andThen`辅助函数提供了一种让值流过的“管道”，具有特殊缩进的版本更能说明这一事实。
改进{anchorName firstThirdandThenExpl}`andThen`的语法可以使其更容易阅读和理解。
:::

### 中缀运算符
%%%
tag := "defining-infix-operators"
%%%


在 Lean 中，可以使用{kw}`infix`、{kw}`infixl`和{kw}`infixr`命令声明中缀运算符，分别用于非结合、左结合和右结合的情况。
当连续多次使用时，{deftech}_左结合_运算符会将（开）括号堆叠在表达式的左侧。
加法运算符{lit}`+`是左结合的，因此{anchorTerm plusFixity}`w + x + y + z`等价于{anchorTerm plusFixity}`(((w + x) + y) + z)`。
指数运算符{lit}`^`是右结合的，因此{anchorTerm powFixity}`w ^ x ^ y ^ z`等价于{anchorTerm powFixity}`(w ^ (x ^ (y ^ z)))`。
比较运算符（如{lit}`<`）是非结合的，因此{lit}`x < y < z`是一个语法错误，需要手动添加括号。

:::paragraph
以下声明将{anchorName andThenOptArr}`andThen`声明为中缀运算符：

```anchor andThenOptArr
infixl:55 " ~~> " => andThen
```
冒号后面的数字声明了新中缀运算符的{deftech}_优先级_。
在一般的数学记号中，{anchorTerm plusTimesPrec}`x + y * z`等价于{anchorTerm plusTimesPrec}`x + (y * z)`，即使{lit}`+`和{lit}`*`都是左结合的。
在 Lean 中，{lit}`+`的优先级为 65，{lit}`*`的优先级为 70。
优先级更高的运算符应用于优先级较低的运算符之前。
根据{lit}`~~>`的声明，{lit}`+`和{lit}`*`都具有更高的优先级，因此会被首先计算。
通常来说，找出最适合一组运算符的优先级需要一些实验和大量的示例。
:::

在新的中缀运算符后面是一个双箭头{lit}`=>`，指定中缀运算符使用的命名的函数。
Lean的标准库使用此功能将{lit}`+`和{lit}`*`定义为指向{moduleName}`HAdd.hAdd`和{moduleName}`HMul.hMul`的中缀运算符，从而允许将类型类用于重载中缀运算符。
不过这里的{anchorName firstThirdandThen}`andThen`只是一个普通函数。

:::paragraph
通过为{anchorName andThenOptArr}`andThen`定义一个中缀运算符，{anchorName firstThirdInfix (show := firstThird)}`firstThirdInfix`可以被改写成一种，显化{moduleName}`none`检查的“管道”风格的方式：

```anchor firstThirdInfix
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
```
这种风格在编写较长的函数时更加精炼：
```anchor firstThirdFifthSeventInfix
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
```
:::

## 错误消息的传递
%%%
tag := "example-except-monad"
%%%

像Lean这样的纯函数式语言并没有用于错误处理的内置异常机制，因为抛出或捕获异常超出了表达式逐步求值模型考虑的范围。
然而函数式程序肯定需要处理错误。
在{anchorName firstThirdFifthSeventInfix}`firstThirdFifthSeventh`的情况下，用户很可能需要知道列表有多长以及查找失败发生的位置。

:::paragraph
这通常通过定义一个——错误或结果——的数据类型，并让带有异常的函数返回此类型来实现：

```anchor Except
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr
```
类型变量{anchorName Except}`ε`表示函数可能产生的错误类型。
调用者需要处理错误和成功两种情况，因此类型变量{anchorName Except}`ε`有点类似Java中需要检查的异常列表。
:::

:::paragraph
类似于{anchorName first}`Option`，{anchorName Except}`Except`可用于指示在列表中找不到项的情况。
此时，错误的类型为{moduleName}`String`：

```anchor getExcept
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
```
查找没有越界的值会得到{anchorName ExceptExtra}`Except.ok`：
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
查找越界的值将产生{anchorName ExceptExtra}`Except.error`：
```anchor failure
#eval get ediblePlants 4
```
```anchorInfo failure
Except.error "Index 4 not found (maximum is 3)"
```
:::

:::paragraph
单个列表查找可以方便地返回一个值或错误：
```anchor firstExcept
def first (xs : List α) : Except String α :=
  get xs 0
```
然而，连续的两次列表查找则需要处理可能发生的失败情况：
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
向函数中添加另一个列表查找需要额外的错误处理：
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
再继续添加一个列表查找则开始变得相当难以管理：
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
同样，一个通用的模式可以提取为一个辅助函数。
函数中的每一步都会检查错误，并只有在成功的情况下才进行之后的计算。
可以为{anchorName andThenExcept}`Except`定义{anchorName andThenExcept}`andThen`的新版本：

```anchor andThenExcept
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
```
与{anchorName first}`Option`一样，该{anchorName andThenExcept}`andThen`允许更简洁地定义{anchorName firstThirdAndThenExcept}`firstThird'`：

```anchor firstThirdAndThenExcept
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
```
:::

:::paragraph
在{anchorName first}`Option`和{anchorName andThenExcept}`Except`情况下，都有两个重复的模式：每一步都有对中间结果的检查，并已提取为{anchorName andThenExcept}`andThen`；有最终的成功结果，分别是{moduleName}`some`或{anchorName andThenExcept}`Except.ok`。
为了方便起见，成功的情况可提取为辅助函数{anchorName okExcept}`ok`：

```anchor okExcept
def ok (x : α) : Except ε α := Except.ok x
```
类似地，失败的情况可提取为辅助函数{anchorName failExcept}`fail`：

```anchor failExcept
def fail (err : ε) : Except ε α := Except.error err
```
{anchorName okExcept}`ok`和{anchorName failExcept}`fail`使得{anchorName getExceptEffects}`get`可读性更好：

```anchor getExceptEffects
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
```
:::

:::paragraph
在为{anchorName andThenExceptInfix}`andThen`添加中缀运算符后，{anchorName firstThirdInfixExcept}`firstThird`可以和返回{anchorName first}`Option`的版本一样简洁：

```anchor andThenExceptInfix
infixl:55 " ~~> " => andThen
```

```anchor firstThirdInfixExcept
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
```
该技术同样适用于更长的函数：

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
%%%

:::paragraph
当一个数字除以2时没有余数则称它为偶数：
```anchor isEven
def isEven (i : Int) : Bool :=
  i % 2 == 0
```
函数{anchorName sumAndFindEvensDirect}`sumAndFindEvens`计算列表所有元素的加和，同时记录沿途遇到的偶数：
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
许多程序需要遍历一次数据结构，计算一个主要结果的同时累积某种额外的结果。
一个例子是日志记录：一个类型为{moduleName}`IO`的程序会将日志输出到磁盘上的文件中，但是由于磁盘在 Lean 函数的数学世界之外，因此对基于{moduleName}`IO`的日志相关的证明变得十分困难。
另一个例子是同时计算树的中序遍历和所有节点的加和的函数，它必须记录每个访问的节点：

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

{anchorName sumAndFindEvensDirect}`sumAndFindEvens`和{anchorName inorderSum}`inorderSum`都具有共同的重复结构。
计算的每一步都返回一个对(pair)，由由数据列表和主要结果组成。
在下一步中列表会被附加新的元素，计算新的主要结果并与附加的列表再次配对。
通过对{anchorName sumAndFindEvensDirectish}`sumAndFindEvens`稍微改写，保存偶数和计算加和的关注点则更加清晰地分离，共同的结构变得更加明显：

```anchor sumAndFindEvensDirectish
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)
```

为了清晰起见，可以给由累积结果和值组成的对(pair)起一个专有的名字：

```anchor WithLog
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
```
同样，保存累积结果列表的同时传递一个值到下一步的过程，可以提取为一个辅助函数，再次命名为{anchorName andThenWithLog}`andThen`：

```anchor andThenWithLog
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
```
在可能发生错误的语境下，{anchorName okWithLog}`ok`表示一个总是成功的操作。然而在这里，它仅简单地返回一个值而不产生任何日志：

```anchor okWithLog
def ok (x : β) : WithLog α β := {log := [], val := x}
```
正如{anchorName Except}`Except`提供{anchorName failExcept}`fail`作为一种可能性，{anchorName WithLog}`WithLog`应该允许将项添加到日志中。
它不需要返回任何有意义的结果，所以返回类型为{anchorName save}`Unit`：

```anchor save
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}
```

{anchorName WithLog}`WithLog`、{anchorName andThenWithLog}`andThen`、{anchorName okWithLog}`ok`和{anchorName save}`save`可以将两个程序中的，日志记录与求和问题分开：

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
同样地，中缀运算符有助于专注于正确的过程：

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

## 对树节点编号
%%%
tag := "numbering-tree-nodes"
%%%

树的每个节点的{deftech}_中序编号_指的是：在中序遍历中被访问的次序。例如，考虑如下{anchorName aTree}`aTree`：

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
树用递归函数来处理最为自然，但树的常见的递归模式并不适合计算中序编号。
这是因为左子树中分配的最大编号将用于确定当前节点的编号，然后用于确定右子树编号的起点。
在命令式语言中，可以使用持有下一个被分配编号的可变变量来解决此问题。
以下Python程序使用可变变量计算中序编号：
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
{anchorName aTree}`aTree`在Python中等价定义是：
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := a_tree)
a_tree = Branch("d",
                left=Branch("c",
                            left=Branch("a", left=None, right=Branch("b")),
                            right=None),
                right=Branch("e"))
```
并且它的编号是：
```command inorderpy "inorder_python" (prompt := ">>> ") (show := "number(a_tree)")
python3 inordernumbering.py
```
```commandOut inorderpy "python3 inordernumbering.py"
Branch((3, 'd'), left=Branch((2, 'c'), left=Branch((0, 'a'), left=None, right=Branch((1, 'b'), left=None, right=None)), right=None), right=Branch((4, 'e'), left=None, right=None))
```
:::


尽管Lean没有可变变量，但有另外一种解决方法。
可变变量可以认为具有两个相关方面：函数调用时的值和函数返回时的值。
换句话说，使用可变变量的函数可以看作：将变量的起始值作为参数、返回变量的最终值和结果构成的元组的函数。
然后可以将此最终值作为参数传递给下一步。

:::paragraph
正如Python示例中定义可变变量的外部函数和更改变量的内部辅助函数一样，Lean版本使用：提供变量初值并明确返回结果的外部函数，以及计算编号树的同时传递变量值的内部辅助函数：

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
此代码与传递{moduleName}`none`的{anchorName first}`Option`代码、传递{anchorName exceptNames (show := error)}`Except.error`的{anchorName exceptNames}`Except`代码、以及累积日志的{moduleName}`WithLog`代码一样，混杂了两个问题：传递计数器的值，以及实际遍历树以查找结果。
与那些情况一样，可以定义一个{anchorName andThenState}`andThen`辅助函数，将状态在计算的步骤之间传递。
第一步是为以下模式命名：将输入状态作为参数并返回输出状态和值：

```anchor State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
```
:::

:::paragraph
在{anchorName State}`State`的情况下，{anchorName okState}`ok`函数原封不动地传递输入状态、以及输入的值：
```anchor okState
def ok (x : α) : State σ α :=
  fun s => (s, x)
```
:::

:::paragraph
在使用可变变量时，有两个基本操作：读取和新值替换旧值。
读取当前值意味着——记录输入状态、将其放入输出状态，然后直接返回记录的输入状态：
```anchor get
def get : State σ σ :=
  fun s => (s, s)
```
写入新值意味着——忽略输入状态，并将提供的新值直接放入输出状态：
```anchor set
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
```
:::

:::paragraph
最后，可以将 first 函数的输出状态和返回值传递到 next 函数中，以此实现这两个函数的先后调用：

```anchor andThenState
def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
```
:::

:::paragraph
通过{anchorName State}`State`和它的辅助函数，可以模拟局部可变状态：

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
因为{anchorName State}`State`只模拟一个局部变量，所以{anchorName get}`get`和{anchorName set}`set`不需要任何特定的变量名。
:::

## 单子：一种函数式设计模式
%%%
tag := "monad-as-design-pattern"
%%%

以上的每个示例都包含下述结构：
 * 一个多态类型，例如{anchorName first}`Option`、{anchorTerm okExcept}`Except ε`、{anchorTerm save}`WithLog α`或{anchorTerm andThenState}`State σ`
 * 一个运算符{lit}`andThen`，用来处理连续、重复、具有此类型的程序序列
 * 一个运算符{lit}`ok`，它（在某种意义上）是使用该类型最无聊的方式
 * 一系列其他操作，例如{moduleName}`none`、{anchorName failExcept}`fail`、{anchorName save}`save`和{anchorName get}`get`，指出了使用对应类型的方式

这种风格的API统称为{deftech}_单子_(Monad)。
虽然单子的思想源自于一门称为范畴论的数学分支，但为了将它们用于编程，并不需要理解范畴论。
单子的关键思想是，每个单子都使用纯函数式语言Lean提供的工具对特定类型的副作用进行编码。
例如{anchorName first}`Option`表示可能通过返回{moduleName}`none`而失败的程序，{moduleName}`Except`表示可能抛出异常的程序，{moduleName}`WithLog`表示在运行过程中累积日志的程序，{anchorName State}`State`表示具有单个可变变量的程序。

{include 1 FPLean.Monads.Class}

{include 1 FPLean.Monads.Arithmetic}

{include 1 FPLean.Monads.Do}

{include 1 FPLean.Monads.IO}

{include 1 FPLean.Monads.Conveniences}

{include 1 FPLean.Monads.Summary}
