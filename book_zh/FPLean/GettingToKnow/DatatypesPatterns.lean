import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "数据类型与模式" =>
%%%
tag := "datatypes-and-patterns"
file := "Datatypes-and-Patterns"
%%%

结构使得多个相互独立的数据片段能够组合成一个连贯的整体，并由一个全新的类型来表示。
像结构这样把一组值组合在一起的类型称为_积类型_。
然而，许多领域概念无法自然地表示为结构。
例如，一个应用程序可能需要跟踪用户权限，其中一些用户是文档所有者，一些用户可以编辑文档，而另一些用户只能读取文档。
计算器具有若干二元运算符，例如加法、减法和乘法。
结构并不提供一种简便方式来编码多种选择。

类似地，虽然结构体是跟踪固定字段集合的绝佳方式，但许多应用需要可能包含任意数量元素的数据。
多数经典数据结构，如树和列表，都具有递归结构：列表的尾部本身是一个列表，或者二叉树的左右分支本身也是二叉树。
在前述计算器中，表达式自身的结构是递归的。
例如，加法表达式中的各个加数本身可能是乘法表达式。

允许选择的数据类型称为_和类型_，而能够包含其自身实例的数据类型称为_递归数据类型_。
递归和类型称为_归纳数据类型_，因为可以使用数学归纳法来证明关于它们的陈述。
在编程时，归纳数据类型通过模式匹配和递归函数来使用。

:::paragraph
许多内建类型实际上是标准库中的归纳数据类型。
例如，{anchorName Bool}`Bool` 是一个归纳数据类型：

```anchor Bool
inductive Bool where
  | false : Bool
  | true : Bool
```

此定义有两个主要部分。
第一行给出了新类型的名称（{anchorName Bool}`Bool`），而其余各行分别描述一个构造子。
与结构的构造子一样，归纳数据类型的构造子只是惰性的接收者和其他数据的容器，而不是插入任意初始化和验证代码的位置。
不同于结构，归纳数据类型可以有多个构造子。
这里有两个构造子，{anchorName Bool}`true` 和 {anchorName Bool}`false`，且二者都不接受任何实参。
正如结构声明会把其名称放入一个以所声明类型命名的命名空间中，归纳数据类型也会把其构造子的名称放入一个命名空间中。
在 Lean 标准库中，{anchorName BoolNames}`true` 和 {anchorName BoolNames}`false` 从此命名空间重新导出，因此它们可以单独书写，而不必分别写作 {anchorName BoolNames}`Bool.true` 和 {anchorName BoolNames}`Bool.false`。
:::

:::paragraph
从数据建模的角度看，归纳数据类型用于许多与其他语言中密封抽象类类似的场景。
在 C# 或 Java 这样的语言中，可以写出类似的 {anchorName Bool}`Bool` 定义：
```CSharp
abstract class Bool {}
class True : Bool {}
class False : Bool {}
```
然而，这些表示的具体细节相当不同。特别是，每个非抽象类都会同时创建一个新类型和分配数据的新方式。在面向对象的例子中，{CSharp}`True` 和 {CSharp}`False` 都是比 {CSharp}`Bool` 更具体的类型，而 Lean 的定义只引入了新类型 {anchorName Bool}`Bool`。
:::

非负整数类型 {anchorName Nat}`Nat` 是一种归纳数据类型：

```anchor Nat
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

这里，{anchorName NatNames}`zero` 表示 0，而 {anchorName NatNames}`succ` 表示某个其他数的后继。
在 {anchorName NatNames}`succ` 的声明中提到的 {anchorName Nat}`Nat` 正是正在被定义的类型 {anchorName Nat}`Nat` 本身。
_后继_的意思是“比……大一”，因此五的后继是六，32,185 的后继是 32,186。
使用这个定义，{anchorEvalStep four 1}`4` 表示为 {anchorEvalStep four 0}`Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))`。
这个定义几乎就像 {anchorName even}`Bool` 的定义，只是名称略有不同。
唯一真正的区别是 {anchorName NatNames}`succ` 后面跟着 {anchorTerm Nat}`(n : Nat)`，它指定构造子 {anchorName NatNames}`succ` 接受一个类型为 {anchorName Nat}`Nat` 的参数，而该参数恰好命名为 {anchorName Nat}`n`。
名称 {anchorName NatNames}`zero` 和 {anchorName NatNames}`succ` 位于一个以其类型命名的命名空间中，因此必须分别以 {anchorName NatNames}`Nat.zero` 和 {anchorName NatNames}`Nat.succ` 引用它们。

参数名称（例如 {anchorName Nat}`n`）可能出现在 Lean 的错误消息中，也可能出现在编写数学证明时提供的反馈中。
Lean 还提供了一种可选语法，用于按名称提供参数。
不过，一般而言，参数名称的选择不如结构字段名称的选择重要，因为它并不构成 API 的那么大一部分。

在 C# 或 Java 中，{CSharp}`Nat` 可以定义如下：
```CSharp
abstract class Nat {}
class Zero : Nat {}
class Succ : Nat {
    public Nat n;
    public Succ(Nat pred) {
        n = pred;
    }
}
```
正如上面的 {anchorName Bool}`Bool` 示例一样，这定义的类型比 Lean 中的对应物更多。
此外，这个示例凸显出：Lean 数据类型的构造子更像抽象类的子类，而不像 C# 或 Java 中的构造函数，因为这里展示的构造函数包含要执行的初始化代码。

和类型也类似于在 TypeScript 中使用字符串标签来编码可辨识联合。
在 TypeScript 中，{typescript}`Nat` 可以如下定义：
```typescript
interface Zero {
    tag: "zero";
}

interface Succ {
    tag: "succ";
    predecessor: Nat;
}

type Nat = Zero | Succ;
```
就像 C# 和 Java 一样，这种编码最终得到的类型比 Lean 中更多，因为 {typescript}`Zero` 和 {typescript}`Succ` 各自都是独立的类型。
它还说明，Lean 的构造子对应于 JavaScript 或 TypeScript 中包含标签的对象，该标签用于标识其内容。

# 模式匹配
%%%
tag := "pattern-matching"
file := "Pattern-Matching"
%%%

在许多语言中，使用这类数据时，首先用 instance-of 运算符检查收到的是哪个子类，然后读取该给定子类中可用字段的值。
instance-of 检查决定运行哪段代码，从而确保该代码所需的数据可用，而字段本身则提供这些数据。
在 Lean 中，这两个目的由_模式匹配_同时实现。

使用模式匹配的函数示例之一是 {anchorName isZero}`isZero`，它是一个函数：当其实参为 {anchorName isZero}`Nat.zero` 时返回 {anchorName isZero}`true`，否则返回 false。

```anchor isZero
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
```

{kw}`match` 表达式获得函数的参数 {anchorName isZero}`n` 以进行解构。
如果 {anchorName isZero}`n` 是由 {anchorName isZero}`Nat.zero` 构造的，那么将采用模式匹配的第一个分支，结果为 {anchorName isZero}`true`。
如果 {anchorName isZero}`n` 是由 {anchorName isZero}`Nat.succ` 构造的，那么将采用第二个分支，结果为 {anchorName isZero}`false`。

:::paragraph
逐步来看，{anchorEvalStep isZeroZeroSteps 0}`isZero Nat.zero` 的求值过程如下：

```anchorEvalSteps  isZeroZeroSteps
isZero Nat.zero
===>
match Nat.zero with
| Nat.zero => true
| Nat.succ k => false
===>
true
```
:::

:::paragraph
{anchorEvalStep isZeroFiveSteps 0}`isZero 5` 的求值过程类似：

```anchorEvalSteps  isZeroFiveSteps
isZero 5
===>
isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
===>
match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
| Nat.zero => true
| Nat.succ k => false
===>
false
```
:::

{anchorName isZero}`isZero` 中模式第二个分支里的 {anchorName isZero}`k` 并非装饰性的。
它使作为 {anchorName isZero}`Nat.succ` 的参数的 {anchorName isZero}`Nat` 以给定名称变得可见。
随后可以使用这个较小的数来计算表达式的最终结果。


:::paragraph
正如某个数 $`n` 的后继比 $`n` 大一（即 $`n + 1`）一样，一个数的前驱比它小一。
如果 {anchorName pred}`pred` 是求 {anchorName pred}`Nat` 的前驱的函数，那么下面的示例应当得到预期结果：

```anchor  predFive
#eval pred 5
```

```anchorInfo predFive
4
```

```anchor predBig
#eval pred 839
```

```anchorInfo predBig
838
```
:::

:::paragraph
因为 {anchorName Nat}`Nat` 不能表示负数，{anchorName NatNames}`Nat.zero` 有些令人困惑。
通常，在使用 {anchorName Nat}`Nat` 时，原本会产生负数的运算符会被重新定义为产生 {anchorName NatNames}`zero` 本身：

```anchor predZero
#eval pred 0
```
```anchorInfo predZero
0
```
:::


要寻找 {anchorName pred}`Nat` 的前驱，第一步是检查用哪个构造子创建了它。
如果它是 {anchorName pred}`Nat.zero`，那么结果是 {anchorName pred}`Nat.zero`。
如果它是 {anchorName pred}`Nat.succ`，那么名称 {anchorName pred}`k` 用来指称其下方的 {anchorName plus}`Nat`。
而这个 {anchorName pred}`Nat` 正是所需的前驱，因此 {anchorName pred}`Nat.succ` 分支的结果是 {anchorName pred}`k`。

```anchor pred
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
```

:::paragraph
将此函数应用于 {anchorTerm predFiveSteps}`5` 会产生以下步骤：

```anchorEvalSteps  predFiveSteps
pred 5
===>
pred (Nat.succ 4)
===>
match Nat.succ 4 with
| Nat.zero => Nat.zero
| Nat.succ k => k
===>
4
```
:::

:::paragraph
模式匹配既可用于结构体，也可用于和类型。
例如，一个从 {anchorName depth}`Point3D` 中提取第三个维度的函数可以写作如下：

```anchor depth
def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d
```

在这种情况下，直接使用 {anchorName fragments}`Point3D.z` 访问器本来要简单得多，但结构模式有时是编写函数的最简单方式。
:::

# 递归函数
%%%
tag := "recursive-functions"
file := "Recursive-Functions"
%%%

引用正在被定义的名称的定义称为_递归定义_。
归纳数据类型允许递归；事实上，{anchorName Nat}`Nat` 就是这种数据类型的一个例子，因为 {anchorName Nat}`succ` 要求另一个 {anchorName Nat}`Nat`。
递归数据类型可以表示任意大的数据，只受可用内存等技术因素限制。
正如不可能在数据类型定义中为每个自然数写出一个构造子，也不可能为每一种可能性写出一个模式匹配分支。

:::paragraph
递归数据类型与递归函数相辅相成。
一个关于 {anchorName even}`Nat` 的简单递归函数会检查其参数是否为偶数。
在此情形中，{anchorName even}`Nat.zero` 是偶数。
像这样的非递归代码分支称为_基本情形_。
奇数的后继是偶数，偶数的后继是奇数。
这意味着，用 {anchorName even}`Nat.succ` 构造出的数为偶数，当且仅当它的参数不是偶数。

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

:::


这种思考模式是为 {anchorName even}`Nat` 编写递归函数时的典型方式。
首先，确定对 {anchorName even}`Nat.zero` 应当做什么。
然后，确定如何把任意 {anchorName even}`Nat` 的结果转换为其后继的结果，并将这个转换应用于递归调用的结果。
这种模式称为_结构递归_。

:::paragraph
与许多语言不同，Lean 默认确保每个递归函数最终都会到达一个基本情形。
从编程角度看，这排除了意外的无限循环。
但在证明定理时，这一特性尤其重要，因为无限循环会造成重大困难。
其结果是，Lean 不会接受试图在原始数上递归调用自身的 {anchorName even}`even` 版本：

```anchor evenLoops
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
```
该错误消息的重要部分在于，Lean 无法判定这个递归函数总是会到达一个基本情形（因为它并不会）。

```anchorError evenLoops
fail to show termination for
  evenLoops
with errors
failed to infer structural recursion:
Not considering parameter n of evenLoops:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, `evenLoops` does not take any (non-fixed) arguments
```

:::

:::paragraph
尽管加法接受两个参数，但只需要检查其中一个。
要把零加到一个数 $`n` 上，只需返回 $`n`。
要把 $`k` 的后继加到 $`n` 上，则取将 $`k` 加到 $`n` 的结果的后继。

```anchor plus
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
```

:::

:::paragraph
在 {anchorName plus}`plus` 的定义中，选择名称 {anchorName plus}`k'` 是为了表明它与实参 {anchorName plus}`k` 有关联，但并不相同。
例如，逐步考察 {anchorEvalStep plusThreeTwo 0}`plus 3 2` 的求值过程，会得到以下步骤：

```anchorEvalSteps  plusThreeTwo
plus 3 2
===>
plus 3 (Nat.succ (Nat.succ Nat.zero))
===>
match Nat.succ (Nat.succ Nat.zero) with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')
===>
Nat.succ (plus 3 (Nat.succ Nat.zero))
===>
Nat.succ (match Nat.succ Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k'))
===>
Nat.succ (Nat.succ (plus 3 Nat.zero))
===>
Nat.succ (Nat.succ (match Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')))
===>
Nat.succ (Nat.succ 3)
===>
5
```
:::

:::paragraph
理解加法的一种方式是：$`n + k` 将 {anchorName times}`Nat.succ` 作用 $`k` 次于 $`n`。
类似地，乘法 $`n × k` 将 $`n` 与自身相加 $`k` 次，而减法 $`n - k` 取 $`n` 的前驱 $`k` 次。

```anchor times
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
```

```anchor minus
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
```

:::

:::paragraph
并非每个函数都能容易地用结构递归来编写。
把加法理解为反复进行 {anchorName plus}`Nat.succ`，把乘法理解为反复进行加法，把减法理解为反复进行前驱，这些理解提示我们可将除法实现为反复进行减法。
在这种情况下，如果被除数小于除数，则结果为零。
否则，结果就是用被除数减去除数后再除以除数所得结果的后继。

```anchor div
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
```
:::

:::paragraph
只要第二个参数不是 {anchorTerm div}`0`，该程序就会终止，因为它总是朝着基本情形取得进展。
然而，它并不是结构递归的，因为它并不遵循先为零寻找结果、再将较小 {anchorName div}`Nat` 的结果转换为其后继的结果这一模式。
特别地，该函数的递归调用被应用于另一个函数调用的结果，而不是应用于输入构造子的参数。
因此，Lean 用以下消息拒绝它：

```anchorError div
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

这条消息意味着 {anchorName div}`div` 需要一个手工的终止性证明。
这一主题将在 {ref "division-as-iterated-subtraction"}[最后一章]中探讨。
:::
