import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "附加语法" =>
%%%
tag := "getting-to-know-conveniences"
%%%

Lean 包含若干便利特性，可以使程序更加简洁。

# 自动隐式参数
%%%
tag := "automatic-implicit-parameters"
%%%

:::paragraph
在 Lean 中编写多态函数时，通常不需要列出所有隐式参数。
相反，可以简单地提到它们。
如果 Lean 能够确定它们的类型，那么它们会自动插入为隐式参数。
换句话说，之前的 {anchorName lengthImp}`length` 定义：

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

可以不写 {anchorTerm lengthImp}`{α : Type}`：

```anchor lengthImpAuto
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

这可以大大简化接受许多隐式参数的高度多态定义。

:::

# 模式匹配定义
%%%
tag := "pattern-matching-definitions"
%%%

使用 {kw}`def` 定义函数时，命名参数然后立即用模式匹配使用它是很常见的。
例如，在 {anchorName lengthImpAuto}`length` 中，参数 {anchorName lengthImpAuto}`xs` 仅在 {kw}`match` 中使用。
在这些情况下，{kw}`match` 表达式的情况可以直接编写，根本不需要命名参数。

:::paragraph
第一步是将参数类型移到冒号右侧，使返回类型成为函数类型。
例如，{anchorName lengthMatchDef}`length` 的类型是 {anchorTerm lengthMatchDef}`List α → Nat`。
然后，用模式匹配的每个情况替换 {lit}`:=`：

```anchor lengthMatchDef
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

这种语法也可以用来定义接受多个参数的函数。
在这种情况下，它们的模式用逗号分隔。
例如，{anchorName drop}`drop` 接受一个数字 $`n` 和一个列表，并返回删除前 $`n` 个条目后的列表。

```anchor drop
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
```

:::

:::paragraph

命名参数和模式也可以在同一个定义中使用。
例如，一个接受默认值和可选值的函数，当可选值为 {anchorName fromOption}`none` 时返回默认值，可以写成：

```anchor fromOption
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
```

这个函数在标准库中称为 {anchorTerm fragments}`Option.getD`，可以用点符号调用：

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
%%%

在计算中命名中间步骤通常很有用。
在许多情况下，中间值本身就代表有用的概念，明确命名它们可以使程序更易读。
在其他情况下，中间值被多次使用。
与大多数其他语言一样，在 Lean 中写两次相同的代码会导致计算两次，而将结果保存在变量中会导致计算结果被保存和重用。

:::paragraph

例如，{anchorName unzipBad}`unzip` 是一个将对列表转换为列表对的函数。
当对列表为空时，{anchorName unzipBad}`unzip` 的结果是一对空列表。
当对列表的头部有一个对时，该对的两个字段被添加到拆分列表其余部分的结果中。
{anchorName unzipBad}`unzip` 的这个定义完全遵循了这个描述：

```anchor unzipBad
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
```

不幸的是，有一个问题：这段代码比需要的更慢。
对列表中的每个条目都会导致两次递归调用，这使得这个函数的时间复杂度是指数级的。
然而，两次递归调用会有相同的结果，所以没有理由进行两次递归调用。
:::

:::paragraph
在 Lean 中，递归调用的结果可以使用 {kw}`let` 命名并保存。
使用 {kw}`let` 的局部定义类似于使用 {kw}`def` 的顶层定义：它需要一个要局部定义的名称、如果需要的话可以有参数、一个类型签名，然后是跟在 {lit}`:=` 后面的主体。
在局部定义之后，局部定义可用的表达式（称为 {kw}`let` 表达式的 *主体*）必须在新行上，从文件中小于或等于 {kw}`let` 关键字列的位置开始。
在 {anchorName unzip}`unzip` 中使用 {kw}`let` 的局部定义如下：

```anchor unzip
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

要在单行中使用 {kw}`let`，用分号将局部定义与主体分开。
:::

:::paragraph
当一个模式足以匹配数据类型的所有情况时，使用 {kw}`let` 的局部定义也可以使用模式匹配。
在 {anchorName unzip}`unzip` 的情况下，递归调用的结果是一个对。
因为对只有一个构造函数，名称 {anchorName unzip}`unzipped` 可以被对模式替换：

```anchor unzipPat
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
```

与手动编写访问器调用相比，明智地使用 {kw}`let` 的模式可以使代码更易读。
:::

:::paragraph
{kw}`let` 和 {kw}`def` 之间最大的区别是递归 {kw}`let` 定义必须通过写 {kw}`let rec` 明确表示。
例如，反转列表的一种方法涉及一个递归辅助函数，如下定义：

```anchor reverse
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
```

辅助函数遍历输入列表，每次将一个条目移动到 {anchorName reverse}`soFar`。
当它到达输入列表的末尾时，{anchorName reverse}`soFar` 包含输入的反转版本。
:::

# 类型推断
%%%
tag := "type-inference"
%%%

:::paragraph
在许多情况下，Lean 可以自动确定表达式的类型。
在这些情况下，可以从顶层定义（使用 {kw}`def`）和局部定义（使用 {kw}`let`）中省略显式类型。
例如，对 {anchorName unzipNT}`unzip` 的递归调用不需要注解：

```anchor unzipNT
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

作为经验法则，省略字面值（如字符串和数字）的类型通常有效，尽管 Lean 可能为字面数字选择比预期类型更具体的类型。
Lean 通常可以确定函数应用的类型，因为它已经知道参数类型和返回类型。
省略函数定义的返回类型通常有效，但函数参数通常需要注解。
不是函数的定义，如示例中的 {anchorName unzipNT}`unzipped`，如果它们的主体不需要类型注解，则不需要类型注解，这个定义的主体是一个函数应用。

:::paragraph
当使用显式 {kw}`match` 表达式时，可以省略 {anchorName unzipNRT}`unzip` 的返回类型：

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

一般来说，宁可类型注解过多，也不要过少，这是一个好主意。
首先，显式类型向读者传达关于代码的假设。
即使 Lean 可以自己确定类型，不必重复查询 Lean 的类型信息仍然可以使代码更易读。
其次，显式类型有助于定位错误。
程序对其类型越明确，错误消息就越有信息量。
这在像 Lean 这样具有非常表达力的类型系统的语言中尤其重要。
第三，显式类型使得首先编写程序更容易。
类型是一个规范，编译器的反馈可以是编写满足规范的程序的有用工具。
最后，Lean 的类型推断是一个尽力而为的系统。
因为 Lean 的类型系统如此有表达力，所以没有"最佳"或最通用的类型来为所有表达式找到。
这意味着即使你得到了一个类型，也不能保证它是给定应用的 *正确* 类型：
例如，{anchorTerm fourteenNat}`14` 可以是 {anchorName length1}`Nat` 或 {anchorName fourteenInt}`Int`：

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
缺少类型注解可能会给出令人困惑的错误消息。
从 {anchorName unzipNoTypesAtAll}`unzip` 的定义中省略所有类型：

```anchor unzipNoTypesAtAll
def unzip pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

会导致关于 {kw}`match` 表达式的消息：

```anchorError unzipNoTypesAtAll
Invalid match expression: This pattern contains metavariables:
  []
```

这是因为 {kw}`match` 需要知道被检查的值的类型，但该类型不可用。
"元变量"是程序的未知部分，在错误消息中写作 {lit}`?m.XYZ`——它们在{ref "polymorphism"}[多态性章节]中有描述。
在这个程序中，参数上的类型注解是必需的。
:::

:::paragraph
即使一些非常简单的程序也需要类型注解。
例如，恒等函数只是返回传递给它的任何参数。
带有参数和类型注解，它看起来像这样：

```anchor idA
def id (x : α) : α := x
```

Lean 能够自己确定返回类型：

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

一般来说，说“推断失败”或提到元变量的消息通常表明需要更多的类型注解。
特别是在学习 Lean 时，明确提供大多数类型是有用的。

# 同时匹配
%%%
tag := "simultaneous-matching"
%%%

:::paragraph

模式匹配表达式，就像模式匹配定义一样，可以同时匹配多个值。
要检查的表达式和它们匹配的模式都用逗号分隔，类似于定义中使用的语法。
这是一个使用同时匹配的 {anchorName dropMatch}`drop` 版本：

```anchor dropMatch
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
```

:::

:::paragraph

同时匹配类似于匹配对，但有一个重要区别。
Lean 跟踪被匹配的表达式和模式之间的连接，这些信息用于包括检查终止性和传播静态类型信息等目的。
结果，匹配对的 {anchorName sameLengthPair}`sameLength` 版本被终止检查器拒绝，因为 {anchorName sameLengthPair}`xs` 和 {anchorTerm sameLengthPair}`x :: xs'` 之间的连接被中间的对遮蔽了：

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
%%%

:::paragraph

在{ref "datatypes-and-patterns"}[数据类型和模式]章节中，{anchorName even}`even` 的定义如下：

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

就像有特殊语法使列表模式比直接使用 {anchorName length1}`List.cons` 和 {anchorName length1}`List.nil` 更易读一样，自然数可以使用字面数字和 {anchorTerm evenFancy}`+` 进行匹配。
例如，{anchorName evenFancy}`even` 也可以这样定义：

```anchor evenFancy
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
```

在这种记法中，{anchorTerm evenFancy}`+` 模式的参数起不同的作用。
在幕后，左参数（上面的 {anchorName evenFancy}`n`）成为一些 {anchorName even}`Nat.succ` 模式的参数，右参数（上面的 {anchorTerm evenFancy}`1`）确定要在模式周围包装多少个 {anchorName even}`Nat.succ`。
{anchorName explicitHalve}`halve` 中的显式模式，它将 {anchorName explicitHalve}`Nat` 除以二并丢弃余数：

```anchor explicitHalve
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
```

可以被数字字面值和 {anchorTerm halve}`+` 替换：

```anchor halve
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
```

在幕后，两个定义完全等价。
记住：{anchorTerm halve}`halve n + 1` 等价于 {anchorTerm halveParens}`(halve n) + 1`，而不是 {anchorTerm halveParens}`halve (n + 1)`。

:::

:::paragraph

使用这种语法时，{anchorTerm halveFlippedPat}`+` 的第二个参数应该总是一个字面 {anchorName halveFlippedPat}`Nat`。
尽管加法是可交换的，但在模式中翻转参数可能会导致如下错误：

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

这个限制使 Lean 能够将模式中 {anchorTerm halveFlippedPat}`+` 记法的所有使用转换为底层 {anchorName even}`Nat.succ` 的使用，在幕后保持语言更简单。

:::

# 匿名函数
%%%
tag := "anonymous-functions"
%%%

:::paragraph

Lean 中的函数不必在顶层定义。
作为表达式，函数使用 {kw}`fun` 语法产生。
函数表达式以关键字 {kw}`fun` 开始，后跟一个或多个参数，使用 {lit}`=>` 与返回表达式分开。
例如，一个给数字加一的函数可以写成：

```anchor incr
#check fun x => x + 1
```

```anchorInfo incr
fun x => x + 1 : Nat → Nat
```

类型注解的写法与 {kw}`def` 相同，使用括号和冒号：

```anchor incrInt
#check fun (x : Int) => x + 1
```


```anchorInfo incrInt
fun x => x + 1 : Int → Int
```

类似地，隐式参数可以用花括号写：

```anchor identLambda
#check fun {α : Type} (x : α) => x
```

```anchorInfo identLambda
fun {α} x => x : {α : Type} → α → α
```

这种匿名函数表达式的风格通常被称为 *lambda 表达式*，因为在编程语言的数学描述中使用的典型记法使用希腊字母 λ（lambda），而 Lean 有关键字 {kw}`fun`。
尽管 Lean 确实允许使用 {kw}`λ` 代替 {kw}`fun`，但最常见的是写 {kw}`fun`。

:::

:::paragraph

匿名函数也支持 {kw}`def` 中使用的多模式风格。
例如，一个返回自然数前驱（如果存在）的函数可以写成：

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

注意 Lean 对函数的描述有一个命名参数和一个 {kw}`match` 表达式。
Lean 的许多便利语法简写在幕后展开为更简单的语法，抽象有时会泄漏。

:::

:::paragraph

使用 {kw}`def` 接受参数的定义可以重写为函数表达式。
例如，一个将其参数加倍的函数可以写成如下：

```anchor doubleLambda
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
```


当匿名函数非常简单时，如 {anchorEvalStep incrSteps 0}`fun x => x + 1`，创建函数的语法可能相当冗长。
在那个特定的例子中，六个非空白字符用于引入函数，其主体只包含三个非空白字符。
对于这些简单情况，Lean 提供了简写。
在被括号包围的表达式中，居中点字符 {anchorTerm incrSteps}`·` 可以代表一个参数，括号内的表达式成为函数的主体。
那个特定的函数也可以写成 {anchorEvalStep incrSteps 1}`(· + 1)`。
:::

:::paragraph

居中点总是从 *最接近* 的周围括号集合创建一个函数。
例如，{anchorEvalStep funPair 0}`(· + 5, 3)` 是一个返回数字对的函数，而 {anchorEvalStep pairFun 0}`((· + 5), 3)` 是一个函数和数字的对。
如果使用多个点，那么它们从左到右成为参数：

```anchorEvalSteps twoDots
(· , ·) 1 2
===>
(1, ·) 2
===>
(1, 2)
```

匿名函数可以以与使用 {kw}`def` 或 {kw}`let` 定义的函数完全相同的方式应用。
命令 {anchor applyLambda}`#eval (fun x => x + x) 5` 的结果是：

```anchorInfo applyLambda
10
```

而 {anchor applyCdot}`#eval (· * 2) 5` 的结果是：

```anchorInfo applyCdot
10
```

:::

# 命名空间
%%%
tag := "namespaces"
%%%

Lean 中的每个名称都出现在一个 *命名空间* 中，这是一个名称集合。
名称使用 {lit}`.` 放置在命名空间中，所以 {anchorName fragments}`List.map` 是 {lit}`List` 命名空间中的名称 {anchorName fragments}`map`。
不同命名空间中的名称不会相互冲突，即使它们在其他方面相同。
这意味着 {anchorName fragments}`List.map` 和 {anchorName fragments}`Array.map` 是不同的名称。
命名空间可以嵌套，所以 {lit}`Project.Frontend.User.loginTime` 是嵌套命名空间 {lit}`Project.Frontend.User` 中的名称 {lit}`loginTime`。

:::paragraph
名称可以直接在命名空间内定义。
例如，名称 {anchorName fragments}`double` 可以在 {anchorName even}`Nat` 命名空间中定义：

```anchor NatDouble
def Nat.double (x : Nat) : Nat := x + x
```

因为 {anchorName even}`Nat` 也是一个类型的名称，所以点符号可用于在类型为 {anchorName even}`Nat` 的表达式上调用 {anchorName fragments}`Nat.double`：

```anchor NatDoubleFour
#eval (4 : Nat).double
```

```anchorInfo NatDoubleFour
8
```

:::

:::paragraph

除了直接在命名空间中定义名称外，还可以使用 {kw}`namespace` 和 {kw}`end` 命令将一系列声明放在命名空间中。
例如，这在命名空间 {lit}`NewNamespace` 中定义了 {anchorName NewNamespace}`triple` 和 {anchorName NewNamespace}`quadruple`：

```anchor NewNamespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
```

要引用它们，在它们的名称前加上 {lit}`NewNamespace.`：

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
命名空间可以被 *打开*，这允许其中的名称在不明确限定的情况下使用。
在表达式前写 {kw}`open` {lit}`MyNamespace` {kw}`in` 会使 {lit}`MyNamespace` 的内容在表达式中可用。
例如，{anchorName quadrupleOpenDef}`timesTwelve` 在打开 {anchorTerm NewNamespace}`NewNamespace` 后使用 {anchorName quadrupleOpenDef}`quadruple` 和 {anchorName quadrupleOpenDef}`triple`：

```anchor quadrupleOpenDef
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
```

:::

:::paragraph
命名空间也可以在命令之前打开。
这允许命令的所有部分引用命名空间的内容，而不仅仅是单个表达式。
为此，在命令前放置 {kw}`open`{lit}` ... `{kw}`in`。

```anchor quadrupleNamespaceOpen
open NewNamespace in
#check quadruple
```

```anchorInfo quadrupleNamespaceOpen
NewNamespace.quadruple (x : Nat) : Nat
```

函数签名显示名称的完整命名空间。
命名空间还可以为文件其余部分的 *所有* 后续命令打开。
为此，只需从顶层使用的 {kw}`open` 中省略 {kw}`in`。

:::

# {lit}`if let`
%%%
tag := "if-let"
%%%

:::paragraph
当消费具有和类型的值时，通常只有一个构造函数是感兴趣的。
例如，给定这个表示 Markdown 内联元素子集的类型：

```anchor Inline
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline
```

一个识别字符串元素并提取其内容的函数可以写成：

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

这非常像模式匹配 {kw}`let` 语法。
区别在于它可以与和类型一起使用，因为在 {kw}`else` 情况下提供了回退。
在某些上下文中，使用 {kw}`if let` 而不是 {kw}`match` 可以使代码更易读。

:::

# 位置结构参数
%%%
tag := "positional-structure-arguments"
%%%

{ref "structures"}[结构章节]展示了两种构造结构的方式：
1. 可以直接调用构造函数，如 {anchorTerm pointCtor}`Point.mk 1 2`。
2. 可以使用大括号记法，如 {anchorTerm pointBraces}`{ x := 1, y := 2 }`。

在某些上下文中，位置传递参数而不是按名称传递参数可能很方便，但不直接命名构造函数。
例如，定义各种类似的结构类型可以帮助保持领域概念分离，但阅读代码的自然方式可能将它们中的每一个基本上视为元组。
在这些上下文中，参数可以用尖括号 {lit}`⟨` 和 {lit}`⟩` 括起来。
{anchorName pointBraces}`Point` 可以写成 {anchorTerm pointPos}`⟨1, 2⟩`。
小心！
尽管它们看起来像小于号 {lit}`<` 和大于号 {lit}`>`，但这些括号是不同的。
它们可以分别使用 {lit}`\<` 和 {lit}`\>` 输入。

:::paragraph
就像命名构造函数参数的大括号记法一样，这种位置语法只能在 Lean 可以确定结构类型的上下文中使用，要么从类型注解，要么从程序中的其他类型信息。
例如，{anchorTerm pointPosEvalNoType}`#eval ⟨1, 2⟩` 产生以下错误：

```anchorError pointPosEvalNoType
Invalid `⟨...⟩` notation: The expected type of this term could not be determined
```

错误声称没有可用的类型信息。
添加注解，如 {anchorTerm pointPosWithType}`#eval (⟨1, 2⟩ : Point)` 中，解决了问题：

```anchorInfo pointPosWithType
{ x := 1.000000, y := 2.000000 }
```

:::

# 字符串插值
%%%
tag := "string-interpolation"
%%%

:::paragraph
在 Lean 中，用 {kw}`s!` 作为字符串前缀会触发 *插值*，其中字符串内花括号中包含的表达式被替换为它们的值。
这类似于 Python 中的 {python}`f`-字符串和 C# 中的 {CSharp}`$`-前缀字符串。
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
不是所有表达式都可以插值到字符串中。
例如，尝试插值一个函数会导致错误。

```anchor interpolationOops
#check s!"three fives is {NewNamespace.triple}"
```

产生错误

```anchorError interpolationOops
failed to synthesize
  ToString (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

这是因为没有将函数转换为字符串的标准方法。
正如 Lean 编译器维护一个表，描述如何显示各种类型的表达式求值结果，它维护一个表，描述如何将各种类型的值转换为字符串。
消息 {lit}`failed to synthesize instance` 意味着 Lean 编译器没有在此表中找到给定类型的条目。
{ref "type-classes"}[类型类章节]更详细地描述了这种机制，包括添加新条目的方法。
:::
