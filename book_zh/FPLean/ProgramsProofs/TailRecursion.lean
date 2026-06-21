import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "尾递归" =>
%%%
tag := "tail-recursion"
file := "Tail-Recursion"
%%%

虽然 Lean 的 {kw}`do` 记法使得可以使用诸如 {kw}`for` 和 {kw}`while` 这样的传统循环语法，但这些构造在幕后会被翻译为对递归函数的调用。
在大多数编程语言中，相对于循环，递归函数有一个关键劣势：循环不消耗栈上的空间，而递归函数消耗的栈空间与递归调用次数成正比。
栈空间通常是有限的，因此常常需要将那些自然地表示为递归函数的算法，改写为循环并配合一个显式的、可变的、堆分配的栈。

在函数式编程中，通常情况相反。
自然表示为可变循环的程序可能会消耗栈空间，而将它们改写为递归函数则可能使它们运行得很快。
这是由于函数式编程语言的一个关键方面：_尾调用消除_。
尾调用是从一个函数到另一个函数的调用，它可以被编译为普通跳转，用新的调用替代当前栈帧而不是压入新的栈帧；尾调用消除就是实现这种变换的过程。

尾调用消除并不仅仅是一项可选优化。
它的存在是能够编写高效函数式代码的基本组成部分。
为了使其有用，它必须是可靠的。
程序员必须能够可靠地识别尾调用，并且必须能够信任编译器会消除它们。

函数 {anchorName NonTailSum}`NonTail.sum` 会将一个由 {anchorName NonTailSum}`Nat` 组成的列表中的内容相加：

```anchor NonTailSum
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
```
将此函数应用于列表 {anchorTerm NonTailSumOneTwoThree}`[1, 2, 3]` 会产生如下求值步骤序列：
```anchorEvalSteps NonTailSumOneTwoThree
NonTail.sum [1, 2, 3]
===>
1 + (NonTail.sum [2, 3])
===>
1 + (2 + (NonTail.sum [3]))
===>
1 + (2 + (3 + (NonTail.sum [])))
===>
1 + (2 + (3 + 0))
===>
1 + (2 + 3)
===>
1 + 5
===>
6
```
在求值步骤中，括号表示对 {anchorName NonTailSumOneTwoThree}`NonTail.sum` 的递归调用。
换言之，为了把这三个数相加，程序必须首先检查列表是否非空。
要把列表的头部（{anchorTerm NonTailSumOneTwoThree}`1`）加到列表尾部的和上，首先必须计算列表尾部的和：
```anchorEvalStep NonTailSumOneTwoThree 1
1 + (NonTail.sum [2, 3])
```
但是，要计算列表尾部的和，程序必须检查它是否为空。
它并非为空——该尾部本身是一个以 {anchorTerm NonTailSumOneTwoThree}`2` 为头部的列表。
得到的步骤正在等待 {anchorTerm NonTailSumOneTwoThree}`NonTail.sum [3]` 返回：
```anchorEvalStep NonTailSumOneTwoThree 2
1 + (2 + (NonTail.sum [3]))
```
运行时调用栈的全部目的，就是跟踪值 {anchorTerm NonTailSumOneTwoThree}`1`、{anchorTerm NonTailSumOneTwoThree}`2` 和 {anchorTerm NonTailSumOneTwoThree}`3`，以及将它们加到递归调用结果上的指令。
随着递归调用完成，控制返回到发起该调用的栈帧，因此每一步加法都会被执行。
存储列表的头部以及将它们相加的指令并非没有代价；它需要与列表长度成正比的空间。

函数 {anchorName TailSum}`Tail.sum` 也会将一个由 {anchorName TailSum}`Nat` 构成的列表中的内容相加：

```anchor TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
```
将其应用于列表 {anchorTerm TailSumOneTwoThree}`[1, 2, 3]` 会得到如下求值步骤序列：
```anchorEvalSteps TailSumOneTwoThree
Tail.sum [1, 2, 3]
===>
Tail.sumHelper 0 [1, 2, 3]
===>
Tail.sumHelper (0 + 1) [2, 3]
===>
Tail.sumHelper 1 [2, 3]
===>
Tail.sumHelper (1 + 2) [3]
===>
Tail.sumHelper 3 [3]
===>
Tail.sumHelper (3 + 3) []
===>
Tail.sumHelper 6 []
===>
6
```
内部辅助函数递归地调用自身，但其调用方式使得为了计算最终结果无需记住任何内容。
当 {anchorName TailSum}`Tail.sumHelper` 到达其基例时，控制可以直接返回给 {anchorName TailSum}`Tail.sum`，因为 {anchorName TailSum}`Tail.sumHelper` 的中间调用只是原封不动地返回其递归调用的结果。
换言之，每次对 {anchorName TailSum}`Tail.sumHelper` 的递归调用都可以复用同一个栈帧。
尾调用消除正是这种对栈帧的复用，而 {anchorName TailSum}`Tail.sumHelper` 被称为一个_尾递归函数_。

传给 {anchorName TailSum}`Tail.sumHelper` 的第一个参数包含了原本需要在调用栈中跟踪的全部信息，即到目前为止所遇到的数之和。
在每次递归调用中，这个参数都会用新信息更新，而不是把新信息加入调用栈。
像 {anchorName TailSum}`soFar` 这样替代来自调用栈的信息的参数称为_累加器_。

在撰写本文时，并且在作者的计算机上，当传入含有 216,856 个或更多项的列表时，{anchorName NonTailSum}`NonTail.sum` 会因栈溢出而崩溃。
另一方面，{anchorName TailSum}`Tail.sum` 可以对含有 100,000,000 个元素的列表求和而不发生栈溢出。
由于运行 {anchorName TailSum}`Tail.sum` 时不需要压入新的栈帧，它完全等价于一个带有可变变量的 {kw}`while` 循环，该变量保存当前列表。
在每次递归调用时，栈上的函数参数只是被替换为列表的下一个节点。


# 尾位置与非尾位置
%%%
tag := "tail-positions"
file := "Tail-and-Non-Tail-Positions"
%%%

{anchorName TailSum}`Tail.sumHelper` 是尾递归的原因在于，递归调用处于_尾位置_。
非正式地说，当调用者不需要以任何方式修改返回值，而只是直接将其返回时，函数调用就处于尾位置。
更形式化地说，可以针对表达式显式定义尾位置。

如果一个 {kw}`match` 表达式处于尾位置，那么它的每个分支也都处于尾位置。
一旦 {kw}`match` 选择了某个分支，控制流就会立即进入该分支。
类似地，如果 {kw}`if` 表达式本身处于尾位置，那么 {kw}`if` 表达式的两个分支也都处于尾位置。
最后，如果一个 {kw}`let` 表达式处于尾位置，那么它的主体也同样处于尾位置。

所有其他位置都不是尾位置。
函数或构造子的实参不在尾位置，因为求值必须跟踪将要应用于该实参值的函数或构造子。
内部函数的函数体不在尾位置，因为控制甚至可能不会传递到它：函数体在函数被调用之前不会被求值。
类似地，函数类型的主体也不在尾位置。
为了在 {lit}`(x : α) → E` 中求值 {lit}`E`，必须跟踪所得类型需要被 {lit}`(x : α) → ...` 包裹。

在 {anchorName NonTailSum}`NonTail.sum` 中，递归调用不在尾位置，因为它是 {anchorTerm NonTailSum}`+` 的一个参数。
在 {anchorName TailSum}`Tail.sumHelper` 中，递归调用在尾位置，因为它直接位于一个模式匹配之下，而该模式匹配本身就是函数体。

在撰写本文时，Lean 只会消除递归函数中的直接尾调用。
这意味着，在 {lit}`f` 的定义中对 {lit}`f` 的尾调用会被消除，但对某个其他函数 {lit}`g` 的尾调用不会被消除。
虽然消除对某个其他函数的尾调用、从而节省一个栈帧当然是可能的，但 Lean 尚未实现这一点。

# 反转列表
%%%
tag := "reversing-lists-tail-recursively"
file := "Reversing-Lists"
%%%

函数 {anchorName NonTailReverse}`NonTail.reverse` 通过把每个子列表的头部追加到结果末尾来反转列表：

```anchor NonTailReverse
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]
```
使用它来反转 {anchorTerm NonTailReverseSteps}`[1, 2, 3]` 会产生如下步骤序列：
```anchorEvalSteps NonTailReverseSteps
NonTail.reverse [1, 2, 3]
===>
(NonTail.reverse [2, 3]) ++ [1]
===>
((NonTail.reverse [3]) ++ [2]) ++ [1]
===>
(((NonTail.reverse []) ++ [3]) ++ [2]) ++ [1]
===>
(([] ++ [3]) ++ [2]) ++ [1]
===>
([3] ++ [2]) ++ [1]
===>
[3, 2] ++ [1]
===>
[3, 2, 1]
```

尾递归版本在每一步对累加器使用 {lit}`x :: ·`，而不是 {lit}`· ++ [x]`：

```anchor TailReverse
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
```
这是因为，在用 {anchorName NonTailReverse}`NonTail.reverse` 计算时保存在每个栈帧中的上下文，是从基本情形开始被应用的。
每一段“记住的”上下文都按后进先出的顺序执行。
另一方面，传递累加器的版本是从列表中的第一个条目开始修改累加器，而不是从原来的基本情形开始；这一点可以在如下规约步骤序列中看出：
```anchorEvalSteps TailReverseSteps
Tail.reverse [1, 2, 3]
===>
Tail.reverseHelper [] [1, 2, 3]
===>
Tail.reverseHelper [1] [2, 3]
===>
Tail.reverseHelper [2, 1] [3]
===>
Tail.reverseHelper [3, 2, 1] []
===>
[3, 2, 1]
```
换言之，非尾递归版本从基例开始，沿列表从右到左修改递归的结果。
列表中的条目以先进先出的顺序影响累加器。
带有累加器的尾递归版本从列表头开始，沿列表从左到右修改一个初始累加器值。

由于加法满足交换律，因此在 {anchorName TailSum}`Tail.sum` 中无需为此做任何处理。
列表追加并不满足交换律，所以必须谨慎地寻找一种在相反方向运行时具有相同效果的操作。
在 {anchorName NonTailReverse}`NonTail.reverse` 中递归结果之后追加 {anchorTerm NonTailReverse}`[x]`，类似于当结果按相反顺序构造时，将 {anchorName NonTailReverse}`x` 加到列表开头。

# 多个递归调用
%%%
tag := "multiple-call-tail-recursion"
file := "Multiple-Recursive-Calls"
%%%

在 {anchorName mirrorNew (module := Examples.Monads.Conveniences)}`BinTree.mirror` 的定义中，有两个递归调用：

```anchor mirrorNew (module := Examples.Monads.Conveniences)
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```
正如命令式语言通常会对 {anchorName NonTailReverse}`reverse` 和 {anchorName NonTailSum}`sum` 这样的函数使用 while 循环一样，它们通常会对此类遍历使用递归函数。
这个函数无法直接用传递累加器的风格改写为尾递归形式，至少不能使用本书中介绍的技术来做到这一点。

通常，如果每个递归步骤都需要多于一次递归调用，那么使用累加器传递风格将会比较困难。
这种困难类似于将递归函数改写为使用循环和显式数据结构时遇到的困难，并且还额外需要使 Lean 确信该函数会终止。
然而，如 {anchorName mirrorNew (module:=Examples.Monads.Conveniences)}`BinTree.mirror` 中所示，多次递归调用往往表明某个数据结构具有一个构造子，其中包含该结构自身的多个递归出现。
在这些情况下，该结构的深度相对于其总体大小通常是对数级的，这使得栈与堆之间的取舍不那么尖锐。
有一些系统性的技术可用于使这些函数成为尾递归，例如使用_续延传递风格_和_去函数化_，但它们超出了本书的范围。

# 练习
%%%
tag := "tail-recursion-exercises"
file := "Exercises"
%%%

将下列每个非尾递归函数翻译为采用累加器传递风格的尾递归函数：


```anchor NonTailLength
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
```


```anchor NonTailFact
def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)
```

对 {anchorName NonTailFilter}`NonTail.filter` 的翻译应当得到一个程序：它通过尾递归占用常量栈空间，并且运行时间相对于输入列表的长度是线性的。
相对于原始程序，常数因子的开销是可以接受的：

```anchor NonTailFilter
def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
```
