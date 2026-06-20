import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "多态性" =>
%%%
tag := "polymorphism"
%%%

就像大多数语言一样，Lean 中的类型可以接受参数。
例如，类型 {anchorTerm fragments}`List Nat` 描述自然数列表，{anchorTerm fragments}`List String` 描述字符串列表，{anchorTerm fragments}`List (List Point)` 描述点列表的列表。
这与 C# 或 Java 等语言中的 {CSharp}`List<Nat>`、{CSharp}`List<String>` 或 {CSharp}`List<List<Point>>` 非常相似。
正如 Lean 使用空格向函数传递参数一样，它使用空格向类型传递参数。

在函数式编程中，术语 *多态性（Polymorphism）* 通常指接受类型作为参数的数据类型和定义。
这与面向对象编程社区不同，在那里这个术语通常指可能覆盖其超类某些行为的子类。
在本书中，“多态性”始终指该词的第一种含义。
这些类型参数可以在数据类型或定义中使用，这允许相同的数据类型或定义与通过用其他类型替换参数名称而产生的任何类型一起使用。

:::paragraph
{anchorName Point}`Point` 结构体要求 {anchorName Point}`x` 和 {anchorName Point}`y` 字段都是 {anchorName Point}`Float`。
然而，关于点没有什么需要为每个坐标使用特定表示的要求。
{anchorName Point}`Point` 的多态版本，称为 {anchorName PPoint}`PPoint`，可以接受一个类型作为参数，然后将该类型用于两个字段：

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```

:::

就像函数定义的参数紧跟在被定义的名称之后一样，结构的参数紧跟在结构名称之后。
在 Lean 中，当没有更具体的名称时，习惯上使用希腊字母来命名类型参数。
{anchorTerm PPoint}`Type` 是一个描述其他类型的类型，所以 {anchorName Nat}`Nat`、{anchorTerm fragments}`List String` 和 {anchorTerm fragments}`PPoint Int` 都具有类型 {anchorTerm PPoint}`Type`。

:::paragraph
就像 {anchorName fragments}`List` 一样，{anchorName PPoint}`PPoint` 可以通过提供特定类型作为其参数来使用：

```anchor natPoint
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
```

在这个例子中，两个字段都被期望是 {anchorName natPoint}`Nat`。
正如通过用参数值替换参数变量来调用函数一样，向 {anchorName PPoint}`PPoint` 提供类型 {anchorName fragments}`Nat` 作为参数会产生一个结构，其中字段 {anchorName PPoint}`x` 和 {anchorName PPoint}`y` 具有类型 {anchorName fragments}`Nat`，因为参数名 {anchorName PPoint}`α` 已被参数类型 {anchorName fragments}`Nat` 替换。
类型是 Lean 中的普通表达式，所以将参数传递给多态类型（如 {anchorName PPoint}`PPoint`）不需要任何特殊语法。
:::

:::paragraph
定义也可能接受类型作为参数，这使它们具有多态性。
函数 {anchorName replaceX}`replaceX` 用新值替换 {anchorName replaceX}`PPoint` 的 {anchorName replaceX}`x` 字段。
为了让 {anchorName replaceX}`replaceX` 能够与 *任何* 多态点一起工作，它本身必须是多态的。
这通过将其第一个参数作为点字段的类型来实现，后续参数引用第一个参数的名称。

```anchor replaceX
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

换句话说，当参数 {anchorName replaceX}`point` 和 {anchorName replaceX}`newX` 的类型提到 {anchorName replaceX}`α` 时，它们指的是 *作为第一个参数提供的任何类型*。
这类似于函数参数名称在函数体中出现时引用所提供的值的方式。
:::

:::paragraph

这可以通过询问 Lean 检查 {anchorName replaceX}`replaceX` 的类型，然后询问它检查 {anchorTerm replaceXNatOriginFiveT}`replaceX Nat` 的类型来看出。

```anchorTerm replaceXT
#check (replaceX)
```

```anchorInfo replaceXT
replaceX : (α : Type) → PPoint α → α → PPoint α
```

这个函数类型包括第一个参数的 *名称*，类型中的后续参数引用这个名称。
正如函数应用的值是通过在函数体中用提供的参数值替换参数名称来找到的一样，函数应用的类型是通过在函数返回类型中用提供的值替换参数名称来找到的。
提供第一个参数 {anchorName replaceXNatT}`Nat` 会导致类型其余部分中 {anchorName replaceX}`α` 的所有出现都被替换为 {anchorName replaceXNatT}`Nat`：

```anchorTerm replaceXNatT
#check replaceX Nat
```

```anchorInfo replaceXNatT
replaceX Nat : PPoint Nat → Nat → PPoint Nat
```

因为其余参数没有明确命名，所以在提供更多参数时不会发生进一步的替换：

```anchorTerm replaceXNatOriginT
#check replaceX Nat natOrigin
```

```anchorInfo replaceXNatOriginT
replaceX Nat natOrigin : Nat → PPoint Nat
```

```anchorTerm replaceXNatOriginFiveT
#check replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveT
replaceX Nat natOrigin 5 : PPoint Nat
```

:::

:::paragraph
通过将类型作为参数传递来确定整个函数应用表达式的类型这一事实对求值能力没有影响。

```anchorTerm replaceXNatOriginFiveV
#eval replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveV
{ x := 5, y := 0 }
```

:::

:::paragraph
多态函数通过接受命名类型参数并让后续类型引用参数名称来工作。
然而，类型参数本身没有什么特殊之处允许它们被命名。
给定一个表示正号或负号的数据类型：

```anchor Sign
inductive Sign where
  | pos
  | neg
```

:::

:::paragraph
可以编写一个以符号为参数的函数。
如果参数是正数，函数返回一个 {anchorName posOrNegThree}`Nat`，如果是负数，则返回一个 {anchorName posOrNegThree}`Int`：

```anchor posOrNegThree
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
```

因为类型是第一类的，可以使用 Lean 语言的普通规则来计算，所以它们可以通过对数据类型进行模式匹配来计算。
当 Lean 检查这个函数时，它使用函数体中的 {kw}`match` 表达式对应于类型中的 {kw}`match` 表达式这一事实，使 {anchorName posOrNegThree}`Nat` 成为 {anchorName Sign}`pos` 情况的预期类型，使 {anchorName posOrNegThree}`Int` 成为 {anchorName Sign}`neg` 情况的预期类型。

:::

:::paragraph
将 {anchorName posOrNegThree}`posOrNegThree` 应用于 {anchorName Sign}`pos` 会导致函数体和返回类型中的参数名 {anchorName posOrNegThree}`s` 都被替换为 {anchorName Sign}`pos`。
求值可以在表达式及其类型中发生：

```anchorEvalSteps posOrNegThreePos
(posOrNegThree Sign.pos :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((match Sign.pos with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)) :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((3 : Nat) : Nat)
===>
3
```

:::

# 链表
%%%
tag := "linked-lists"
%%%

:::paragraph
Lean 的标准库包含一个规范的链表数据类型，称为 {anchorName fragments}`List`，以及使其更便于使用的特殊语法。
列表用方括号编写。
例如，包含小于 10 的质数的列表可以写成：

```anchor primesUnder10
def primesUnder10 : List Nat := [2, 3, 5, 7]
```

:::

:::paragraph
在幕后，{anchorName List}`List` 是一个归纳数据类型，定义如下：

```anchor List
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

标准库中的实际定义略有不同，因为它使用了尚未介绍的功能，但本质上是相似的。
这个定义说 {anchorName List}`List` 接受单个类型作为其参数，就像 {anchorName PPoint}`PPoint` 一样。
这个类型是存储在列表中的条目的类型。
根据构造器，{anchorTerm List}`List α` 可以用 {anchorName List}`nil` 或 {anchorName List}`cons` 构建。
构造器 {anchorName List}`nil` 表示空列表，构造器 {anchorName List}`cons` 用于非空列表。
{anchorName List}`cons` 的第一个参数是列表的头部，第二个参数是它的尾部。
包含 $`n` 个条目的列表包含 $`n` 个 {anchorName List}`cons` 构造器，其中最后一个以 {anchorName List}`nil` 作为其尾部。

:::

:::paragraph
{anchorName primesUnder10}`primesUnder10` 示例可以通过直接使用 {anchorName List}`List` 的构造器更明确地编写：

```anchor explicitPrimesUnder10
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
```

这两个定义完全等价，但 {anchorName primesUnder10}`primesUnder10` 比 {anchorName explicitPrimesUnder10}`explicitPrimesUnder10` 更容易阅读。
:::

:::paragraph
使用 {anchorName List}`List` 的函数可以用与使用 {anchorName Nat}`Nat` 的函数大致相同的方式定义。
实际上，将链表视为每个 {anchorName Nat}`succ` 构造器都悬挂着额外数据字段的 {anchorName Nat}`Nat` 是一种思考方式。
从这个角度来看，计算列表长度的过程就是将每个 {anchorName List}`cons` 替换为 {anchorName Nat}`succ`，将最后的 {anchorName List}`nil` 替换为 {anchorName Nat}`zero`。
正如 {anchorName replaceX}`replaceX` 将点字段的类型作为参数一样，{anchorName length1EvalSummary}`length` 接受列表条目的类型。
例如，如果列表包含字符串，那么第一个参数是 {anchorName length1EvalSummary}`String`：{anchorEvalStep length1EvalSummary 0}`length String ["Sourdough", "bread"]`。
它应该像这样计算：

```anchorEvalSteps length1EvalSummary
length String ["Sourdough", "bread"]
===>
length String (List.cons "Sourdough" (List.cons "bread" List.nil))
===>
Nat.succ (length String (List.cons "bread" List.nil))
===>
Nat.succ (Nat.succ (length String List.nil))
===>
Nat.succ (Nat.succ Nat.zero)
===>
2
```

:::

:::paragraph

{anchorName length1}`length` 的定义既是多态的（因为它将列表条目类型作为参数），也是递归的（因为它引用自身）。
通常，函数遵循数据的形状：递归数据类型导致递归函数，多态数据类型导致多态函数。

```anchor length1
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
```

:::

诸如 {lit}`xs` 和 {lit}`ys` 之类的名称通常用来表示未知值的列表。
名称中的 {lit}`s` 表示它们是复数，所以它们读作"exes"和"whys"而不是"x s"和"y s"。

:::paragraph
为了更容易阅读列表上的函数，方括号记法 {anchorTerm length2}`[]` 可以用来对 {anchorName List}`nil` 进行模式匹配，中缀 {anchorTerm length2}`::` 可以用来代替 {anchorName List}`cons`：

```anchor length2
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)
```

:::

# 隐式参数
%%%
tag := "implicit-parameters"
%%%

:::paragraph
{anchorName replaceX}`replaceX` 和 {anchorName length1}`length` 使用起来都有些繁琐，因为类型参数通常由后续值唯一确定。
实际上，在大多数语言中，编译器完全能够自行确定类型参数，只是偶尔需要用户的帮助。
Lean 也是如此。
在定义函数时，可以通过将参数包装在花括号而不是圆括号中来声明参数为 *隐式的*。
例如，具有隐式类型参数的 {anchorName replaceXImp}`replaceX` 版本如下所示：

```anchor replaceXImp
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

它可以与 {anchorName replaceXImpNat}`natOrigin` 一起使用而无需明确提供 {anchorName NatDoubleFour}`Nat`，因为 Lean 可以从后续参数中 *推断* {anchorName replaceXImp}`α` 的值：

```anchor replaceXImpNat
#eval replaceX natOrigin 5
```

```anchorInfo replaceXImpNat
{ x := 5, y := 0 }
```

:::

:::paragraph

类似地，{anchorName lengthImp}`length` 可以重新定义为隐式接受条目类型：

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

这个 {anchorName lengthImp}`length` 函数可以直接应用于 {anchorName lengthImpPrimes}`primesUnder10`：

```anchor lengthImpPrimes
#eval length primesUnder10
```

```anchorInfo lengthImpPrimes
4
```

:::

:::paragraph
在标准库中，Lean 将此函数称为 {anchorName lengthExpNat}`List.length`，这意味着用于结构字段访问的点语法也可以用来查找列表的长度：

```anchor lengthDotPrimes
#eval primesUnder10.length
```

```anchorInfo lengthDotPrimes
4
```

:::

:::paragraph
正如 C# 和 Java 有时需要明确提供类型参数一样，Lean 并不总是能够找到隐式参数。
在这些情况下，可以使用它们的名称来提供它们。
例如，只适用于整数列表的 {anchorName lengthExpNat}`List.length` 版本可以通过将 {anchorTerm lengthExpNat}`α` 设置为 {anchorName lengthExpNat}`Int` 来指定：

```anchor lengthExpNat
#check List.length (α := Int)
```

```anchorInfo lengthExpNat
List.length : List Int → Nat
```

:::

# 更多内置数据类型
%%%
tag := "more-built-in-types"
%%%

除了列表之外，Lean 的标准库还包含许多其他结构体和归纳数据类型，可用于各种场景。

## {lit}`Option` 可空类型
%%%
tag := "Option"
%%%
并非每个列表都有第一个条目：有些列表是空的。
许多集合操作都可能找不到所寻找的对象。
例如，寻找列表第一个条目的函数可能找不到任何条目。
因此，它必须有办法表示不存在第一个条目。

许多语言都有一个 {CSharp}`null` 值，用来表示值的缺失。
Lean 并不为已有类型配备一个特殊的 {CSharp}`null` 值，而是提供一个名为 {anchorName Option}`Option` 的数据类型，用来给其他类型配备一个缺失值标记。
例如，可空的 {anchorName fragments}`Int` 表示为 {anchorTerm nullOne}`Option Int`，而可空的字符串列表表示为类型 {anchorTerm fragments}`Option (List String)`。
引入一个新类型来表示可空性，意味着类型系统能够保证不会忘记检查 {CSharp}`null`，因为 {anchorTerm nullOne}`Option Int` 不能用于期望 {anchorName nullOne}`Int` 的上下文。

:::paragraph
{anchorName Option}`Option` 有两个构造器，分别称为 {anchorName Option}`some` 和 {anchorName Option}`none`，分别表示底层类型的非空和空版本。非空构造器 {anchorName Option}`some` 包含基础值，而 {anchorName Option}`none` 不接受任何参数：

```anchor Option
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
```

:::

{anchorName Option}`Option` 类型非常类似于 C# 和 Kotlin 中的可空类型，但并不完全相同。在这些语言中，如果一个类型（例如 {CSharp}`Boolean`）总是引用该类型的实际值（{CSharp}`true` 和 {CSharp}`false`），则类型 {CSharp}`Boolean?` 或 {CSharp}`Nullable<Boolean>` 还额外允许 {CSharp}`null` 值。在类型系统中跟踪这一点非常有用：类型检查器和其他工具可以帮助程序员记住检查 {CSharp}`null`，并且通过类型签名显式描述可空性的 API 比不描述的可空性 API 更有信息量。然而，这些可空类型与 Lean 的 {anchorName Option}`Option` 有一个非常重要的区别，那就是它们不允许多层可空性。{anchorTerm nullThree}`Option (Option Int)` 可以通过 {anchorTerm nullOne}`none`、{anchorTerm nullTwo}`some none` 或 {anchorTerm nullThree}`some (some 360)` 构造。另一方面，Kotlin 将 {Kotlin}`T??` 视为与 {Kotlin}`T?` 等价。这种微妙的差异在实践中很少相关，但有时可能很重要。

:::paragraph
要查找列表中的第一个条目（如果存在），使用 {anchorName headHuh}`List.head?`。问号是名称的一部分，与在 C# 或 Kotlin 中使用问号表示可空类型无关。在 {anchorName headHuh}`List.head?` 的定义中，下划线用于表示列表的尾部。在模式匹配中，下划线匹配任何东西，但不会引入变量来引用匹配的数据。使用下划线而不是名称是向读者清楚地传达输入的一部分被忽略的一种方式。

```anchor headHuh
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
```

:::

Lean 的命名约定是使用后缀 {lit}`?` 定义可能失败的组操作的版本，该版本返回一个 {anchorName Option}`Option`；使用后缀 {lit}`!` 定义版本，当提供无效输入时崩溃；使用后缀 {lit}`D` 定义版本，当操作本应失败时返回默认值。按照这个模式，{anchorName fragments}`List.head` 要求调用者提供数学证据证明列表不为空，{anchorName fragments}`List.head?` 返回一个 {anchorName Option}`Option`，{anchorName fragments}`List.head!` 当传递空列表时崩溃，{anchorName fragments}`List.headD` 接收一个默认值，在列表为空时返回。问号和感叹号是名称的一部分，而不是特殊语法，因为 Lean 的命名规则比许多语言更宽松。

:::paragraph

因为 {anchorName fragments}`head?` 定义在 {lit}`List` 命名空间中，它可以使用访问器表示法：

```anchor headSome
#eval primesUnder10.head?
```

```anchorInfo headSome
some 2
```

然而，在空列表上测试它会导致两个错误：

```anchor headNoneBad
#eval [].head?
```

```anchorError headNoneBad
don't know how to synthesize implicit argument `α`
  @List.nil ?m.3
context:
⊢ Type ?u.71462
```

```anchorError headNoneBad
don't know how to synthesize implicit argument `α`
  @_root_.List.head? ?m.3 []
context:
⊢ Type ?u.71462
```

:::

:::paragraph
这是因为 Lean 无法完全确定表达式的类型。特别是，它既找不到 {anchorName fragments}`List.head?` 的隐式类型参数，也找不到 {anchorName fragments}`List.nil` 的隐式类型参数。在 Lean 的输出中，{lit}`?m.XYZ` 表示一个无法推断的部分程序。这些未知部分称为 *元变量*，它们出现在一些错误消息中。为了评估表达式，Lean 需要能够找到它的类型，而类型不可用是因为空列表没有可以从其中找到类型的条目。显式提供类型允许 Lean 继续执行：

```anchor headNone
#eval [].head? (α := Int)
```

```anchorInfo headNone
none
```

类型也可以通过类型标注提供：

```anchor headNoneTwo
#eval ([] : List Int).head?
```

```anchorInfo headNoneTwo
none
```

错误消息提供了一个有用的线索。两个消息都使用 *相同的* 元变量来描述缺失的隐式参数，这意味着 Lean 已经确定两个缺失的部分将共享一个解决方案，即使它无法确定实际值。

:::

## {lit}`Prod` 积类型
%%%
tag := "prod"
%%%

{anchorName Prod}`Prod` 结构体是 “Product” 的缩写，是一种把两个值合在一起的通用方式。
例如，{anchorTerm fragments}`Prod Nat String` 包含一个 {anchorName fragments}`Nat` 和一个 {anchorName fragments}`String`。
换言之，{anchorTerm natPoint}`PPoint Nat` 可以替换为 {anchorTerm fragments}`Prod Nat Nat`。
{anchorName fragments}`Prod` 很像 C# 中的元组、Kotlin 中的 {Kotlin}`Pair` 和 {Kotlin}`Triple` 类型，以及 C++ 中的 {cpp}`tuple`。
在许多应用中，即使是 {anchorName Point}`Point` 这样简单的情形，最好也定义自己的结构体，因为使用领域术语可以使代码更易读。
此外，定义结构体类型也有助于发现更多错误，因为它会把不同领域概念赋予不同类型，防止它们被混淆。

另一方面，在某些情况下，定义新类型所需的开销并不值得。
此外，有些库足够通用，以至于不存在比“偶对”更具体的概念。
最后，标准库包含多种便利函数，使内置偶对类型更易使用。

:::paragraph
结构体 {anchorName Prod}`Prod` 使用两个类型参数定义：

```anchor Prod
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
```

:::

:::paragraph
列表使用非常频繁，因此有特殊的语法使其更易读。出于同样的原因，积类型和其构造器都有特殊的语法。类型 {anchorTerm ProdSugar}`Prod α β` 通常写为 {anchorTerm ProdSugar}`α × β`，模仿集合的笛卡尔积的通常表示法。类似地，{anchorName ProdSugar}`Prod` 可以使用通常的数学表示法表示偶对。换句话说，不必写：

```anchor fivesStruct
def fives : String × Int := { fst := "five", snd := 5 }
```

只需写：

```anchor fives
def fives : String × Int := ("five", 5)
```

:::

:::paragraph

两种表示法都是右结合的。这意味着以下定义是等价的：

```anchor sevens
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
```

```anchor sevensNested
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
```

换句话说，所有大于两个类型的积类型及其对应的构造器实际上是嵌套的积类型和嵌套的偶对。

:::


## {anchorName Sum}`Sum` 和类型
%%%
tag := "Sum"
%%%

{anchorName Sum}`Sum` 数据类型是一种通用方式，用来允许在两个不同类型的值之间作选择。
例如，{anchorTerm fragments}`Sum String Int` 要么是一个 {anchorName fragments}`String`，要么是一个 {anchorName fragments}`Int`。
与 {anchorName Prod}`Prod` 类似，{anchorName Sum}`Sum` 应用于编写非常通用的代码、某段很小且没有合理领域专用类型的代码，或标准库包含有用函数的情形。
在大多数情况下，使用自定义归纳类型会更加可读且更易维护。

:::paragraph
类型为 {anchorTerm Sumαβ}`Sum α β` 的值要么是构造器 {anchorName Sum}`inl` 应用于类型为 {anchorName Sum}`α` 的值，要么是构造器 {anchorName Sum}`inr` 应用于类型为 {anchorName Sum}`β` 的值：

```anchor Sum
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
```

这些名字分别是“左注入”（left injection）和“右注入”（right injection）的缩写。正如笛卡尔积表示法用于 {anchorName Prod}`Prod`，“圆加”表示法用于 {anchorName SumSugar}`Sum`，所以 {anchorTerm SumSugar}`α ⊕ β` 是另一种写法 {anchorTerm SumSugar}`Sum α β`。对于 {anchorName FakeSum}`Sum.inl` 和 {anchorName FakeSum}`Sum.inr` 没有特殊的语法。

:::

:::paragraph
例如，如果宠物名字可以是狗名字或猫名字，那么可以引入一个字符串的和类型：

```anchor PetName
def PetName : Type := String ⊕ String
```

在实际程序中，最好自定义一个归纳数据类型，用于此目的，并使用有意义的构造器名字。这里，{anchorName animals}`Sum.inl` 用于狗名字，{anchorName animals}`Sum.inr` 用于猫名字。这些构造器可以用于编写动物名字的列表：

```anchor animals
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]
```

:::

:::paragraph
模式匹配可以用于区分两个构造器。例如，一个计算动物名字列表中狗数量的函数（即 {anchorName howManyDogs}`Sum.inl` 构造器的数量）看起来像这样：

```anchor howManyDogs
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
```

函数调用在中缀运算符之前求值，所以 {anchorTerm howManyDogsAdd}`howManyDogs morePets + 1` 与 {anchorTerm howManyDogsAdd}`(howManyDogs morePets) + 1` 相同。正如预期的那样，{anchor dogCount}`#eval howManyDogs animals` 得到 {anchorInfo dogCount}`3`。
:::

## {anchorName Unit}`Unit` 单元类型
%%%
tag := "Unit"
%%%

:::paragraph
{anchorName Unit}`Unit` 是一个只有一个无参数构造器的类型，称为 {anchorName Unit}`unit`。换句话说，它只描述一个值，该值由该构造器应用于没有任何参数。{anchorName Unit}`Unit` 定义如下：

```anchor Unit
inductive Unit : Type where
  | unit : Unit
```

:::

:::paragraph
在自身，{anchorName Unit}`Unit` 并不是特别有用。然而，在多态代码中，它可以用于表示缺失数据的占位符。例如，以下归纳数据类型表示算术表达式：

```anchor ArithExpr
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
```

类型参数 {anchorName ArithExpr}`ann` 表示标注，每个构造器都标注了。来自解析器的表达式可能带有源位置标注，所以返回类型 {anchorTerm ArithExprEx}`ArithExpr SourcePos` 确保解析器在每个子表达式中放置一个 {anchorName ArithExprEx}`SourcePos`。然而，来自解析器的表达式不会带有源位置，所以它们的类型可以是 {anchorTerm ArithExprEx}`ArithExpr Unit`。

:::

此外，因为所有 Lean 函数都有参数，其他语言中的零参数函数可以表示为接受 {anchorName ArithExprEx}`Unit` 参数的函数。在返回位置，{anchorName ArithExprEx}`Unit` 类型类似于 C 语言派生语言中的 {CSharp}`void`。在 C 家族中，返回 {CSharp}`void` 的函数将控制权返回给它的调用者，但不会返回任何有趣的价值。通过成为故意无趣的价值，{anchorName ArithExprEx}`Unit` 允许这种情况被表达，而无需在类型系统中要求特殊用途的 {CSharp}`void` 功能。{anchorName ArithExprEx}`Unit` 的构造器可以写为空括号：{anchorTerm unitParens}`() : Unit`。

## {lit}`Empty` 空类型
%%%
tag := "Empty"
%%%

{anchorName fragments}`Empty` 数据类型完全没有构造子。
因此，它表示不可达代码，因为不存在任何调用序列能够以类型 {anchorName fragments}`Empty` 的值终止。

{anchorName fragments}`Empty` 的使用频率远不如 {anchorName fragments}`Unit`。
不过，它在某些专门情境中很有用。
许多多态数据类型并不会在所有构造子中使用自己的全部类型参数。
例如，{anchorName animals}`Sum.inl` 和 {anchorName animals}`Sum.inr` 各自只使用 {anchorName fragments}`Sum` 的一个类型参数。
把 {anchorName fragments}`Empty` 作为 {anchorName fragments}`Sum` 的一个类型参数，可以在程序的某个特定位置排除其中一个构造子。
这使通用代码能够用于带有额外限制的上下文。

## 命名：和类型，积类型与单元类型
%%%
tag := "sum-products-units"
%%%

一般来说，提供多个构造器的类型称为*和类型*，而单个构造器接受多个参数的类型称为{deftech}*积类型*。这些术语与普通算术中使用的和与积有关。当涉及的类型包含有限数量的值时，这种关系最容易看到。如果 {anchorName SumProd}`α` 和 {anchorName SumProd}`β` 是分别包含 $`n` 和 $`k` 个不同值的类型，那么 {anchorTerm SumProd}`α ⊕ β` 包含 $`n + k` 个不同值，而 {anchorTerm SumProd}`α × β` 包含 $`n \times k` 个不同值。例如，{anchorName fragments}`Bool` 有两个值：{anchorName BoolNames}`true` 和 {anchorName BoolNames}`false`，而 {anchorName Unit}`Unit` 有一个值：{anchorName BooloUnit}`Unit.unit`。积 {anchorTerm fragments}`Bool × Unit` 有两个值：{anchorTerm BoolxUnit}`(true, Unit.unit)` 和 {anchorTerm BoolxUnit}`(false, Unit.unit)`，而和 {anchorTerm fragments}`Bool ⊕ Unit` 有三个值：{anchorTerm BooloUnit}`Sum.inl true`，{anchorTerm BooloUnit}`Sum.inl false`，和 {anchorTerm BooloUnit}`Sum.inr Unit.unit`。同样，$`2 \times 1 = 2`，和 $`2 + 1 = 3`。

# 你可能遇到的消息
%%%
tag := "polymorphism-messages"
%%%

:::paragraph
并非所有可定义的结构或归纳类型都可以具有类型 {anchorTerm Prod}`Type`。
特别是，如果构造器将任意类型作为参数，那么归纳类型必须具有不同的类型。
这些错误通常会说一些关于"宇宙层级"的内容。
例如，对于这个归纳类型：

```anchor TypeInType
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
```

Lean 给出以下错误：

```anchorError TypeInType
Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```

后面的章节描述了为什么会这样，以及如何修改定义使其工作。
现在，尝试将类型作为整个归纳类型的参数，而不是构造器的参数。
:::

:::paragraph
类似地，如果构造器的参数是一个以正在定义的数据类型为参数的函数，那么定义会被拒绝。
例如：

```anchor Positivity
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
```

产生消息：

```anchorError Positivity
(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
```

出于技术原因，允许这些数据类型可能会破坏 Lean 的内部逻辑，使其不适合用作定理证明器。
:::

:::paragraph
接受两个参数的递归函数不应该对对进行匹配，而应该独立地匹配每个参数。
否则，Lean 中检查递归调用是否在较小值上进行的机制无法看到输入值与递归调用中的参数之间的连接。
例如，这个确定两个列表是否具有相同长度的函数被拒绝：

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

错误消息是：

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
1) 1760:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

问题可以通过嵌套模式匹配来解决：

```anchor sameLengthOk1
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | x :: xs' =>
    match ys with
    | y :: ys' => sameLength xs' ys'
    | _ => false
```

下一节描述的{ref "simultaneous-matching"}[同时匹配]是解决问题的另一种方式，通常更优雅。
:::

:::paragraph
忘记归纳类型的参数也会产生令人困惑的消息。
例如，当参数 {anchorName MissingTypeArg}`α` 没有在 {anchorTerm MissingTypeArg}`ctor` 的类型中传递给 {anchorName MissingTypeArg}`MyType` 时：

```anchor MissingTypeArg
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
```

Lean 用以下错误回复：

```anchorError MissingTypeArg
type expected, got
  (MyType : Type → Type)
```

错误消息是说 {anchorName MissingTypeArg}`MyType` 的类型，即 {anchorTerm MissingTypeArgT}`Type → Type`，本身并不描述类型。
{anchorName MissingTypeArg}`MyType` 需要一个参数才能成为真正的类型。

:::

:::paragraph
当在其他上下文中省略类型参数时，可能出现相同的消息，比如在定义的类型签名中：

```anchor MyTypeDef
inductive MyType (α : Type) : Type where
  | ctor : α → MyType α
```

```anchor MissingTypeArg2
def ofFive : MyType := ctor 5
```

```anchorError MissingTypeArg2
type expected, got
  (MyType : Type → Type)
```

:::

:::paragraph
评估使用多态类型的表达式可能会触发 Lean 无法显示值的情况。
{anchorTerm evalAxe}`#eval` 命令评估提供的表达式，使用表达式的类型来确定如何显示结果。
对于某些类型，例如函数，此过程失败，但 Lean 完全能够自动生成大多数其他类型的显示代码。
例如，不需要为 {anchorName WoodSplittingTool}`WoodSplittingTool` 提供任何特定的显示代码：
```anchor WoodSplittingTool
inductive WoodSplittingTool where
  | axe
  | maul
  | froe
```
```anchor evalAxe
#eval WoodSplittingTool.axe
```
```anchorInfo evalAxe
WoodSplittingTool.axe
```
Lean 在这里使用的自动化存在限制。
{anchorName allTools}`allTools` 是所有三个工具的列表：
```anchor allTools
def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]
```
评估它会导致错误：
```anchor evalAllTools
#eval allTools
```
```anchorError evalAllTools
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  List WoodSplittingTool
```
这是因为 Lean 试图使用内置表中的代码来显示列表，但此代码要求 {anchorName WoodSplittingTool}`WoodSplittingTool` 的显示代码已经存在。
可以通过指示 Lean 在定义数据类型时生成此显示代码，而不是在 {anchorTerm evalAllTools}`#eval` 的最后时刻作为一部分来解决此错误，方法是向其定义添加 {anchorTerm Firewood}`deriving Repr`：
```anchor Firewood
inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr
```
评估 {anchorName Firewood}`Firewood` 列表成功：
```anchor allFirewood
def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]
```
```anchor evalAllFirewood
#eval allFirewood
```
```anchorInfo evalAllFirewood
[Firewood.birch, Firewood.pine, Firewood.beech]
```
:::

# 练习
%%%
tag := "polymorphism-exercises"
%%%

 * 编写一个函数来查找列表中的最后一个条目。它应该返回一个 {anchorName fragments}`Option`。
 * 编写一个函数，查找列表中满足给定谓词的第一个条目。从 {anchorTerm List.findFirst?Ex}`def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …` 开始定义。
 * 编写一个函数 {anchorName Prod.switchEx}`Prod.switch`，它交换偶对中的两个字段。从 {anchor Prod.switchEx}`def Prod.switch {α β : Type} (pair : α × β) : β × α := …` 开始定义。
 * 使用自定义数据类型重写 {anchorName PetName}`PetName` 示例，并将其与使用 {anchorName Sum}`Sum` 的版本进行比较。
 * 编写一个函数 {anchorName zipEx}`zip`，将两个列表合并为一个列表对。结果列表的长度应与最短输入列表的长度相同。从 {anchor zipEx}`def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …` 开始定义。
 * 编写一个多态函数 {anchorName takeOne}`take`，返回列表中的前 $`n` 个条目，其中 $`n` 是一个 {anchorName fragments}`Nat`。如果列表包含少于 $`n` 个条目，则结果列表应为整个输入列表。{anchorTerm takeThree}`#eval take 3 ["bolete", "oyster"]` 应该产生 {anchorInfo takeThree}`["bolete", "oyster"]`，而 {anchor takeOne}`#eval take 1 ["bolete", "oyster"]` 应该产生 {anchorInfo takeOne}`["bolete"]`。
 * 使用类型和算术之间的类比，编写一个函数，将乘法分配到和上。换句话说，它应该具有类型 {anchorTerm distr}`α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`。
 * 使用类型和算术之间的类比，编写一个函数，将乘法分配到和上。换句话说，它应该具有类型 {anchorTerm distr}`Bool × α → α ⊕ α`。
