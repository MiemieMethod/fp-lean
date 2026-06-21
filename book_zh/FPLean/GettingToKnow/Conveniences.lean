import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "附加便利功能" =>
%%%
tag := "getting-to-know-conveniences"
file := "Additional-Conveniences"
%%%

Lean 包含若干便利特性，使程序能够更加简洁。

# 自动隐式参数
%%%
tag := "automatic-implicit-parameters"
file := "Automatic-Implicit-Parameters"
%%%

:::paragraph
在 Lean 中编写多态函数时，通常不必列出所有隐式参数。
相反，只需提及它们即可。
如果 Lean 能够确定它们的类型，那么它们会被自动插入为隐式参数。
换言之，先前对 {anchorName lengthImp}`length` 的定义：

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

可以不使用 {anchorTerm lengthImp}`{α : Type}` 来写成：

```anchor lengthImpAuto
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

这可以极大地简化带有许多隐式参数的高度多态定义。

:::

# 模式匹配定义
%%%
tag := "pattern-matching-definitions"
file := "Pattern-Matching-Definitions"
%%%

在使用 {kw}`def` 定义函数时，经常会先命名一个参数，然后立即对它进行模式匹配。
例如，在 {anchorName lengthImpAuto}`length` 中，参数 {anchorName lengthImpAuto}`xs` 只在 {kw}`match` 中使用。
在这些情况下，可以直接写出 {kw}`match` 表达式的各个情形，而完全不必命名该参数。

:::paragraph
第一步是将参数的类型移到冒号右侧，使返回类型成为一个函数类型。
例如，{anchorName lengthMatchDef}`length` 的类型是 {anchorTerm lengthMatchDef}`List α → Nat`。
然后，用模式匹配的每一种情况替换 {lit}`:=`：

```anchor lengthMatchDef
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

这种语法也可以用于定义接受多个参数的函数。
在这种情况下，它们的模式以逗号分隔。
例如，{anchorName drop}`drop` 接受一个数 $`n` 和一个列表，并在移除前 $`n` 个条目后返回该列表。

```anchor drop
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
```

:::

:::paragraph

命名参数和模式也可以在同一个定义中使用。
例如，一个接受默认值和可选值，并在可选值为 {anchorName fromOption}`none` 时返回默认值的函数，可以写成：

```anchor fromOption
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
```

此函数在标准库中称为 {anchorTerm fragments}`Option.getD`，并且可以用点记法调用：

```anchor getD
#eval (some "salmonberry").getD ""
```


```anchorInfo getD
"salmonberry"
```


```anchor getDNone
#eval none.getD ""
```


```anchorInfo getDNone
""
```

:::

# 局部定义
%%%
tag := "local-definitions"
file := "Local-Definitions"
%%%

为计算中的中间步骤命名通常很有用。
在许多情况下，中间值本身就表示有用的概念，显式地为它们命名可以使程序更易读。
在另一些情况下，中间值会被使用多次。
与大多数其他语言一样，在 Lean 中把同一段代码写两次会导致它被计算两次，而将结果保存在变量中则会使计算结果被保存并复用。

:::paragraph

例如，{anchorName unzipBad}`unzip` 是一个将由对组成的列表转换为由列表组成的对的函数。
当由对组成的列表为空时，{anchorName unzipBad}`unzip` 的结果是一对空列表。
当由对组成的列表的头部有一个对时，该对的两个字段会被加入到对列表其余部分进行 unzip 后的结果中。
{anchorName unzipBad}`unzip` 的这个定义正是遵循这一描述：

```anchor unzipBad
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
```

遗憾的是，这里有一个问题：这段代码比必要的要慢。
列表中的每个序对条目都会导致两次递归调用，这使得该函数花费指数时间。
然而，两次递归调用会得到相同的结果，因此没有理由进行两次递归调用。
:::

:::paragraph
在 Lean 中，可以使用 {kw}`let` 为递归调用的结果命名，从而将其保存下来。
带有 {kw}`let` 的局部定义类似于带有 {kw}`def` 的顶层定义：它接受一个要在局部定义的名称、需要时给出参数、一个类型签名，然后在 {lit}`:=` 之后给出主体。
在局部定义之后，可以使用该局部定义的表达式（称为 {kw}`let` 表达式的_主体_）必须位于新的一行，并且在文件中从小于或等于 {kw}`let` 关键字所在列的位置开始。
在 {anchorName unzip}`unzip` 中使用 {kw}`let` 的局部定义如下所示：

```anchor unzip
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

若要在单行中使用 {kw}`let`，请用分号将局部定义与主体分隔开。
:::

:::paragraph
使用 {kw}`let` 的局部定义，在一个模式足以匹配某个数据类型的所有情形时，也可以使用模式匹配。
在 {anchorName unzip}`unzip` 的情形中，递归调用的结果是一个二元组。
因为二元组只有一个构造子，名称 {anchorName unzip}`unzipped` 可以替换为一个二元组模式：

```anchor unzipPat
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
```

与手工编写访问器调用相比，审慎地将模式与 {kw}`let` 配合使用可以使代码更易读。
:::

:::paragraph
{kw}`let` 与 {kw}`def` 之间最大的区别在于，递归的 {kw}`let` 定义必须通过写出 {kw}`let rec` 来显式标明。
例如，反转列表的一种方式涉及一个递归辅助函数，如下面这个定义所示：

```anchor reverse
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
```

该辅助函数沿着输入列表向下遍历，每次将一个条目移至 {anchorName reverse}`soFar`。
当它到达输入列表的末尾时，{anchorName reverse}`soFar` 包含该输入的一个反转版本。
:::

# 类型推断
%%%
tag := "type-inference"
file := "Type-Inference"
%%%

:::paragraph
在许多情况下，Lean 可以自动确定表达式的类型。
在这些情况下，顶层定义（使用 {kw}`def`）和局部定义（使用 {kw}`let`）中的显式类型都可以省略。
例如，对 {anchorName unzipNT}`unzip` 的递归调用不需要标注：

```anchor unzipNT
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

作为经验法则，省略字面值（如字符串和数字）的类型通常可行，尽管 Lean 可能会为数字字面值选择一个比预期类型更具体的类型。
Lean 通常能够确定函数应用的类型，因为它已经知道实参类型和返回类型。
省略函数定义的返回类型通常可行，但函数参数通常需要标注。
不是函数的定义，例如示例中的 {anchorName unzipNT}`unzipped`，如果其主体不需要类型标注，则它们也不需要类型标注；而此定义的主体是一个函数应用。

:::paragraph
在使用显式的 {kw}`match` 表达式时，可以省略 {anchorName unzipNRT}`unzip` 的返回类型：

```anchor unzipNRT
def unzip (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

:::paragraph

一般而言，类型标注宁可过多，也不要过少，这是一个好主意。
首先，显式类型向读者传达关于代码的假设。
即使 Lean 能自行确定类型，不必反复向 Lean 查询类型信息也仍然可以使代码更易读。
其次，显式类型有助于定位错误。
一个程序对其类型说明得越显式，错误消息就可能越有信息量。
这在 Lean 这样具有非常强表达能力的类型系统的语言中尤其重要。
第三，显式类型使一开始编写程序变得更容易。
类型是一种规范，编译器的反馈可以成为编写满足该规范的程序时的有用工具。
最后，Lean 的类型推断是一种尽力而为的系统。
由于 Lean 的类型系统表达能力如此之强，并不存在对所有表达式都要找到的“最佳”或最一般类型。
这意味着，即使你得到了一个类型，也不能保证它就是给定应用所需的_正确_类型。
例如，{anchorTerm fourteenNat}`14` 可以是一个 {anchorName length1}`Nat` 或一个 {anchorName fourteenInt}`Int`：

```anchor fourteenNat
#check 14
```


```anchorInfo fourteenNat
14 : Nat
```


```anchor fourteenInt
#check (14 : Int)
```

```anchorInfo fourteenInt
14 : Int
```

:::

:::paragraph
缺少类型标注可能会产生令人困惑的错误消息。
从 {anchorName unzipNoTypesAtAll}`unzip` 的定义中省略所有类型：

```anchor unzipNoTypesAtAll
def unzip pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

会产生一条关于 {kw}`match` 表达式的消息：

```anchorError unzipNoTypesAtAll
Invalid match expression: This pattern contains metavariables:
  []
```

这是因为 {kw}`match` 需要知道被检查的值的类型，但该类型不可获得。
“元变量”是程序中的未知部分，在错误消息中写作 {lit}`?m.XYZ`——它们在{ref "polymorphism"}[关于多态的章节]中说明。
在此程序中，参数上的类型标注是必需的。
:::

:::paragraph
即使某些非常简单的程序也需要类型标注。
例如，恒等函数只是返回传给它的任意实参。
带有参数和类型标注时，它如下所示：

```anchor idA
def id (x : α) : α := x
```

Lean 能够自行确定返回类型：

```anchor idB
def id (x : α) := x
```

然而，省略参数类型会导致错误：

```anchor identNoTypes
def id x := x
```


```anchorError identNoTypes
Failed to infer type of binder `x`
```
:::

一般而言，类似于“failed to infer”的消息，或提到元变量的消息，通常表明需要更多类型标注。
特别是在仍在学习 Lean 时，显式给出大多数类型是有益的。

# 同时匹配
%%%
tag := "simultaneous-matching"
file := "Simultaneous-Matching"
%%%

:::paragraph

模式匹配表达式与模式匹配定义一样，可以一次匹配多个值。
待检查的表达式以及与之匹配的模式都用逗号分隔书写，类似于定义所用的语法。
下面是使用同时匹配的 {anchorName dropMatch}`drop` 版本：

```anchor dropMatch
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
```

:::

:::paragraph

同时匹配类似于对二元组进行匹配，但二者有一个重要区别。
Lean 会跟踪被匹配表达式与模式之间的联系，并且这些信息会用于多种目的，包括检查终止性和传播静态类型信息。
因此，对二元组进行匹配的 {anchorName sameLengthPair}`sameLength` 版本会被终止性检查器拒绝，因为 {anchorName sameLengthPair}`xs` 与 {anchorTerm sameLengthPair}`x :: xs'` 之间的联系被中间的二元组遮蔽了：

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

```anchorError sameLengthPair
fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1748:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

同时匹配两个列表是被接受的：

```anchor sameLengthOk2
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
```

:::

# 自然数模式
%%%
tag := "natural-number-patterns"
file := "Natural-Number-Patterns"
%%%

:::paragraph

在关于 {ref "datatypes-and-patterns"}[数据类型与模式] 的一节中，{anchorName even}`even` 是这样定义的：

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

正如有特殊语法使列表模式比直接使用 {anchorName length1}`List.cons` 和 {anchorName length1}`List.nil` 更可读一样，自然数也可以使用数字字面量和 {anchorTerm evenFancy}`+` 来匹配。
例如，{anchorName evenFancy}`even` 也可以这样定义：

```anchor evenFancy
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
```

在此记法中，{anchorTerm evenFancy}`+` 模式的各个参数承担不同的角色。
在幕后，左参数（上面的 {anchorName evenFancy}`n`）会成为若干个 {anchorName even}`Nat.succ` 模式的参数，而右参数（上面的 {anchorTerm evenFancy}`1`）决定要在该模式外包裹多少个 {anchorName even}`Nat.succ`。
{anchorName explicitHalve}`halve` 中的显式模式，它将一个 {anchorName explicitHalve}`Nat` 除以二并舍去余数：

```anchor explicitHalve
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
```

可以替换为数字字面值和 {anchorTerm halve}`+`：

```anchor halve
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
```

在幕后，这两个定义完全等价。
请记住：{anchorTerm halve}`halve n + 1` 等价于 {anchorTerm halveParens}`(halve n) + 1`，而不是 {anchorTerm halveParens}`halve (n + 1)`。

:::

:::paragraph

使用这种语法时，{anchorTerm halveFlippedPat}`+` 的第二个参数应始终是一个字面量 {anchorName halveFlippedPat}`Nat`。
尽管加法是可交换的，但在模式中交换参数可能导致如下错误：

```anchor halveFlippedPat
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve n + 1
```

```anchorError halveFlippedPat
Invalid pattern(s): `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 2 n)
```

这一限制使 Lean 能够将模式中 {anchorTerm halveFlippedPat}`+` 记法的所有使用转换为对底层 {anchorName even}`Nat.succ` 的使用，从而在幕后保持语言更为简单。

:::

# 匿名函数
%%%
tag := "anonymous-functions"
file := "Anonymous-Functions"
%%%

:::paragraph

Lean 中的函数不必在顶层定义。
作为表达式，函数由 {kw}`fun` 语法产生。
函数表达式以关键字 {kw}`fun` 开始，后跟一个或多个参数，并使用 {lit}`=>` 将这些参数与返回表达式分隔开。
例如，将一个数加一的函数可以写作：

```anchor incr
#check fun x => x + 1
```

```anchorInfo incr
fun x => x + 1 : Nat → Nat
```

类型标注的写法与在 {kw}`def` 上相同，使用圆括号和冒号：

```anchor incrInt
#check fun (x : Int) => x + 1
```


```anchorInfo incrInt
fun x => x + 1 : Int → Int
```

类似地，隐式参数可以用花括号书写：

```anchor identLambda
#check fun {α : Type} (x : α) => x
```

```anchorInfo identLambda
fun {α} x => x : {α : Type} → α → α
```

这种匿名函数表达式的风格通常称为 _lambda 表达式_，因为在编程语言的数学描述中使用的典型记号，会在 Lean 使用关键字 {kw}`fun` 的位置使用希腊字母 λ（lambda）。
尽管 Lean 的确允许使用 {kw}`λ` 来代替 {kw}`fun`，但最常见的写法是 {kw}`fun`。

:::

:::paragraph

匿名函数也支持 {kw}`def` 中使用的多模式风格。
例如，一个在自然数的前驱存在时返回其前驱的函数可以写作：

```anchor predHuh
#check fun
  | 0 => none
  | n + 1 => some n
```


```anchorInfo predHuh
fun x =>
  match x with
  | 0 => none
  | n.succ => some n : Nat → Option Nat
```

注意，Lean 自己对该函数的描述包含一个命名参数和一个 {kw}`match` 表达式。
Lean 的许多便利语法缩写都会在幕后展开为更简单的语法，而这种抽象有时会泄漏。

:::

:::paragraph

使用 {kw}`def` 且带有参数的定义可以改写为函数表达式。
例如，将其参数加倍的函数可以写成如下形式：

```anchor doubleLambda
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
```


当匿名函数非常简单时，例如 {anchorEvalStep incrSteps 0}`fun x => x + 1`，创建该函数的语法可能相当冗长。
在这个特定示例中，引入函数使用了六个非空白字符，而其主体只有三个非空白字符。
对于这些简单情形，Lean 提供了一种简写。
在由圆括号包围的表达式中，居中的点字符 {anchorTerm incrSteps}`·` 可以代表一个参数，而圆括号内的表达式则成为该函数的主体。
这个特定函数也可以写作 {anchorEvalStep incrSteps 1}`(· + 1)`。
:::

:::paragraph

居中的点总是从_最近的_外围括号组创建一个函数。
例如，{anchorEvalStep funPair 0}`(· + 5, 3)` 是一个返回一对数字的函数，而 {anchorEvalStep pairFun 0}`((· + 5), 3)` 是由一个函数和一个数字组成的对。
如果使用多个点，那么它们会从左到右成为参数：

```anchorEvalSteps twoDots
(· , ·) 1 2
===>
(1, ·) 2
===>
(1, 2)
```

匿名函数可以用与使用 {kw}`def` 或 {kw}`let` 定义的函数完全相同的方式来应用。
命令 {anchor applyLambda}`#eval (fun x => x + x) 5` 得到：

```anchorInfo applyLambda
10
```

而 {anchor applyCdot}`#eval (· * 2) 5` 得到：

```anchorInfo applyCdot
10
```

:::

# 命名空间
%%%
tag := "namespaces"
file := "Namespaces"
%%%

Lean 中的每个名称都位于一个_命名空间_中，命名空间是一组名称的集合。
名称使用 {lit}`.` 放置在命名空间中，因此 {anchorName fragments}`List.map` 是 {lit}`List` 命名空间中的名称 {anchorName fragments}`map`。
不同命名空间中的名称彼此不冲突，即使它们在其他方面完全相同。
这意味着 {anchorName fragments}`List.map` 和 {anchorName fragments}`Array.map` 是不同的名称。
命名空间可以嵌套，因此 {lit}`Project.Frontend.User.loginTime` 是嵌套命名空间 {lit}`Project.Frontend.User` 中的名称 {lit}`loginTime`。

:::paragraph
名称可以直接在命名空间内定义。
例如，名称 {anchorName fragments}`double` 可以在 {anchorName even}`Nat` 命名空间中定义：

```anchor NatDouble
def Nat.double (x : Nat) : Nat := x + x
```

由于 {anchorName even}`Nat` 也是一个类型的名称，因此可以使用点记法，在类型为 {anchorName even}`Nat` 的表达式上调用 {anchorName fragments}`Nat.double`：

```anchor NatDoubleFour
#eval (4 : Nat).double
```

```anchorInfo NatDoubleFour
8
```

:::

:::paragraph

除了直接在命名空间中定义名称之外，还可以使用 {kw}`namespace` 和 {kw}`end` 命令将一系列声明放入一个命名空间中。
例如，下面在命名空间 {lit}`NewNamespace` 中定义了 {anchorName NewNamespace}`triple` 和 {anchorName NewNamespace}`quadruple`：

```anchor NewNamespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
```

要引用它们，请在其名称前加上 {lit}`NewNamespace.`：

```anchor tripleNamespace
#check NewNamespace.triple
```

```anchorInfo tripleNamespace
NewNamespace.triple (x : Nat) : Nat
```


```anchor quadrupleNamespace
#check NewNamespace.quadruple
```

```anchorInfo quadrupleNamespace
NewNamespace.quadruple (x : Nat) : Nat
```

:::

:::paragraph
命名空间可以被_打开_，这使得其中的名称无需显式限定即可使用。
在表达式之前写 {kw}`open` {lit}`MyNamespace `{kw}`in` 会使 {lit}`MyNamespace` 的内容在该表达式中可用。
例如，{anchorName quadrupleOpenDef}`timesTwelve` 在打开 {anchorTerm NewNamespace}`NewNamespace` 后同时使用了 {anchorName quadrupleOpenDef}`quadruple` 和 {anchorName quadrupleOpenDef}`triple`：

```anchor quadrupleOpenDef
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
```

:::

:::paragraph
命名空间也可以在命令之前打开。
这允许命令的所有部分引用该命名空间的内容，而不仅仅是单个表达式。
为此，请将 {kw}`open`﻿{lit}` ... `{kw}`in` 置于命令之前。

```anchor quadrupleNamespaceOpen
open NewNamespace in
#check quadruple
```

```anchorInfo quadrupleNamespaceOpen
NewNamespace.quadruple (x : Nat) : Nat
```

函数签名会显示名称的完整命名空间。
此外，也可以为文件其余部分的_所有_后续命令打开命名空间。
为此，只需在顶层使用 {kw}`open` 时省略 {kw}`in`。

:::

# {lit}`if let`
%%%
tag := "if-let"
file := "if-let"
%%%

:::paragraph
在消费具有和类型的值时，常常只有一个构造子是关心的对象。
例如，给定如下类型，它表示 Markdown 行内元素的一个子集：

```anchor Inline
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline
```

一个识别字符串元素并提取其内容的函数可以写作：

```anchor inlineStringHuhMatch
def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none
```

:::

:::paragraph
编写这个函数主体的另一种方式是将 {kw}`if` 与 {kw}`let` 一起使用：

```anchor inlineStringHuh
def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none
```

这非常类似于模式匹配的 {kw}`let` 语法。
区别在于它可以用于和类型，因为在 {kw}`else` 情形中提供了后备分支。
在某些上下文中，使用 {kw}`if let` 而不是 {kw}`match` 可以使代码更易读。

:::

# 按位置给出的结构参数
%%%
tag := "positional-structure-arguments"
file := "Positional-Structure-Arguments"
%%%

{ref "structures"}[关于结构的一节]给出了构造结构的两种方式：
 1. 可以直接调用该构造子，如 {anchorTerm pointCtor}`Point.mk 1 2`。
 2. 可以使用花括号记法，如 {anchorTerm pointBraces}`{ x := 1, y := 2 }` 中所示。

在某些语境中，按位置而非按名称传递参数会很方便，但又不必直接写出构造子的名称。
例如，定义多种相似的结构类型有助于将领域概念彼此分离，但阅读代码时的自然方式可能会把它们中的每一个实质上都视为一个元组。
在这些语境中，参数可以括在尖括号 {lit}`⟨` 和 {lit}`⟩` 中。
一个 {anchorName pointBraces}`Point` 可以写作 {anchorTerm pointPos}`⟨1, 2⟩`。
请注意！
尽管它们看起来像小于号 {lit}`<` 和大于号 {lit}`>`，但这些括号是不同的。
它们可以分别用 {lit}`\<` 和 {lit}`\>` 输入。

:::paragraph
正如具名构造子参数的花括号记法一样，这种位置语法只能在 Lean 能够确定结构类型的上下文中使用；这种确定可以来自类型标注，也可以来自程序中的其他类型信息。
例如，{anchorTerm pointPosEvalNoType}`#eval ⟨1, 2⟩` 会产生如下错误：

```anchorError pointPosEvalNoType
Invalid `⟨...⟩` notation: The expected type of this term could not be determined
```

出现此错误是因为没有可用的类型信息。
添加一个标注，例如 {anchorTerm pointPosWithType}`#eval (⟨1, 2⟩ : Point)` 中那样，即可解决该问题：

```anchorInfo pointPosWithType
{ x := 1.000000, y := 2.000000 }
```

:::

# 字符串插值
%%%
tag := "string-interpolation"
file := "String-Interpolation"
%%%

:::paragraph
在 Lean 中，在字符串前加上 {kw}`s!` 会触发_插值_，其中字符串内部花括号中的表达式会被替换为它们的值。
这类似于 Python 中的 {python}`f`-字符串以及 C# 中带 {CSharp}`$` 前缀的字符串。
例如，

```anchor interpolation
#eval s!"three fives is {NewNamespace.triple 5}"
```

产生输出

```anchorInfo interpolation
"three fives is 15"
```

:::

:::paragraph
并非所有表达式都可以插值到字符串中。
例如，试图插值一个函数会导致错误。

```anchor interpolationOops
#check s!"three fives is {NewNamespace.triple}"
```

产生错误

```anchorError interpolationOops
failed to synthesize
  ToString (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

这是因为不存在将函数转换为字符串的标准方式。
正如编译器维护一张表，用于描述如何显示对各种类型的表达式求值所得的结果，它也维护一张表，用于描述如何将各种类型的值转换为字符串。
消息 {lit}`failed to synthesize instance` 表示 Lean 编译器没有在这张表中找到给定类型对应的条目。
关于 {ref "type-classes"}[类型类] 的章节会更详细地描述这一机制，包括向该表添加新条目的方法。
:::
