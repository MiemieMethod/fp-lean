import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "多态" =>
%%%
tag := "polymorphism"
file := "Polymorphism"
%%%

正如在大多数语言中一样，Lean 中的类型可以接受参数。
例如，类型 {anchorTerm fragments}`List Nat` 描述自然数列表，{anchorTerm fragments}`List String` 描述字符串列表，而 {anchorTerm fragments}`List (List Point)` 描述点的列表的列表。
这与 C# 或 Java 等语言中的 {CSharp}`List<Nat>`、{CSharp}`List<String>` 或 {CSharp}`List<List<Point>>` 非常相似。
正如 Lean 使用空格向函数传递参数一样，它也使用空格向类型传递参数。

在函数式编程中，术语_多态_通常指以类型作为参数的数据类型和定义。
这不同于面向对象编程社群中的用法，在那里该术语通常指可以重写其超类某些行为的子类。
在本书中，“多态”始终指该词的第一种含义。
这些类型参数可以在数据类型或定义中使用，这使得同一个数据类型或定义可以与任何类型一起使用，只要将参数名称替换为其他某些类型即可得到这些类型。

:::paragraph
{anchorName Point}`Point` 结构体要求 {anchorName Point}`x` 和 {anchorName Point}`y` 字段都是 {anchorName Point}`Float`。
然而，点本身并不要求每个坐标必须采用某种特定表示。
{anchorName Point}`Point` 的一个多态版本称为 {anchorName PPoint}`PPoint`，它可以接受一个类型作为实参，然后将该类型用于两个字段：

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```

:::

正如函数定义的参数紧跟在被定义的名称之后书写一样，结构的参数也紧跟在结构的名称之后书写。
在 Lean 中，当没有更具体的名称自然出现时，通常使用希腊字母来命名类型参数。
{anchorTerm PPoint}`Type` 是一个描述其他类型的类型，因此 {anchorName Nat}`Nat`、{anchorTerm fragments}`List String` 和 {anchorTerm fragments}`PPoint Int` 都具有类型 {anchorTerm PPoint}`Type`。

:::paragraph
与 {anchorName fragments}`List` 一样，{anchorName PPoint}`PPoint` 可以通过提供一个具体类型作为其参数来使用：

```anchor natPoint
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
```

在此示例中，两个字段都应为 {anchorName natPoint}`Nat`。
正如调用函数时会用其实参值替换其形参变量一样，将类型 {anchorName fragments}`Nat` 作为实参提供给 {anchorName PPoint}`PPoint`，会得到一个结构，其中字段 {anchorName PPoint}`x` 和 {anchorName PPoint}`y` 具有类型 {anchorName fragments}`Nat`，因为实参名称 {anchorName PPoint}`α` 已被实参类型 {anchorName fragments}`Nat` 替换。
在 Lean 中，类型是普通表达式，因此向多态类型（如 {anchorName PPoint}`PPoint`）传递实参不需要任何特殊语法。
:::

:::paragraph
定义也可以把类型作为参数，这会使它们成为多态的。
函数 {anchorName replaceX}`replaceX` 将一个 {anchorName replaceX}`PPoint` 的 {anchorName replaceX}`x` 字段替换为一个新值。
为了允许 {anchorName replaceX}`replaceX` 适用于_任意_多态点，它自身也必须是多态的。
这是通过使它的第一个参数成为点的字段的类型，并让后续参数回指第一个参数的名称来实现的。

```anchor replaceX
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

换言之，当参数 {anchorName replaceX}`point` 和 {anchorName replaceX}`newX` 的类型提到 {anchorName replaceX}`α` 时，它们指的是_作为第一个参数提供的任何类型_。
这类似于函数参数名称在函数体中出现时，指代调用时提供的值的方式。
:::

:::paragraph

这一点可以通过请求 Lean 检查 {anchorName replaceX}`replaceX` 的类型，然后再请求它检查 {anchorTerm replaceXNatOriginFiveT}`replaceX Nat` 的类型来看到。

```anchorTerm replaceXT
#check (replaceX)
```

```anchorInfo replaceXT
replaceX : (α : Type) → PPoint α → α → PPoint α
```

这个函数类型包含第一个参数的_名称_，并且类型中后面的参数会回指这个名称。
正如函数应用的值是通过在函数体中用所提供的参数值替换参数名而得到的，函数应用的类型也是通过在函数的返回类型中用所提供的值替换该参数的名称而得到的。
提供第一个参数 {anchorName replaceXNatT}`Nat` 会使类型其余部分中 {anchorName replaceX}`α` 的所有出现都被替换为 {anchorName replaceXNatT}`Nat`：

```anchorTerm replaceXNatT
#check replaceX Nat
```

```anchorInfo replaceXNatT
replaceX Nat : PPoint Nat → Nat → PPoint Nat
```

由于其余参数没有被显式命名，因此随着提供更多参数，不会发生进一步的替换：

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
整个函数应用表达式的类型是通过将一个类型作为实参传入而确定的，这一事实并不影响对它求值的能力。

```anchorTerm replaceXNatOriginFiveV
#eval replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveV
{ x := 5, y := 0 }
```

:::

:::paragraph
多态函数的工作方式是接受一个具名类型参数，并让后续类型引用该参数的名称。
然而，类型参数之所以能被命名，并没有什么特殊之处。
给定一个表示正号或负号的数据类型：

```anchor Sign
inductive Sign where
  | pos
  | neg
```

:::

:::paragraph
可以编写一个其参数为符号的函数。
如果参数为正，该函数返回一个 {anchorName posOrNegThree}`Nat`；而如果参数为负，则返回一个 {anchorName posOrNegThree}`Int`：

```anchor posOrNegThree
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
```

由于类型是一等对象，并且可以使用 Lean 语言的普通规则进行计算，因此它们可以通过对数据类型进行模式匹配来计算。
当 Lean 检查这个函数时，它利用函数体中的 {kw}`match` 表达式与类型中的 {kw}`match` 表达式相对应这一事实，使 {anchorName posOrNegThree}`Nat` 成为 {anchorName Sign}`pos` 情形的期望类型，并使 {anchorName posOrNegThree}`Int` 成为 {anchorName Sign}`neg` 情形的期望类型。

:::

:::paragraph
将 {anchorName posOrNegThree}`posOrNegThree` 应用于 {anchorName Sign}`pos` 会导致函数体及其返回类型中的参数名 {anchorName posOrNegThree}`s` 都被 {anchorName Sign}`pos` 替换。
求值既可以发生在表达式中，也可以发生在其类型中：

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
file := "Linked-Lists"
%%%

:::paragraph
Lean 的标准库包含一个规范的链表数据类型，称为 {anchorName fragments}`List`，并提供了使其使用更方便的特殊语法。
列表写在方括号中。
例如，一个包含小于 10 的素数的列表可以写作：

```anchor primesUnder10
def primesUnder10 : List Nat := [2, 3, 5, 7]
```

:::

:::paragraph
在幕后，{anchorName List}`List` 是一个归纳数据类型，其定义如下：

```anchor List
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

标准库中的实际定义略有不同，因为它使用了尚未介绍的特性，但二者在实质上是相似的。
这个定义说明，{anchorName List}`List` 与 {anchorName PPoint}`PPoint` 一样，以单个类型作为其参数。
这个类型就是列表中所存储条目的类型。
根据这些构造子，可以用 {anchorName List}`nil` 或 {anchorName List}`cons` 构造一个 {anchorTerm List}`List α`。
构造子 {anchorName List}`nil` 表示空列表，而构造子 {anchorName List}`cons` 用于非空列表。
{anchorName List}`cons` 的第一个参数是列表的头部，第二个参数是其尾部。
一个包含 $`n` 个条目的列表包含 $`n` 个 {anchorName List}`cons` 构造子，其中最后一个以 {anchorName List}`nil` 作为其尾部。

:::

:::paragraph
{anchorName primesUnder10}`primesUnder10` 示例可以通过直接使用 {anchorName List}`List` 的构造子写得更显式：

```anchor explicitPrimesUnder10
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
```

这两个定义完全等价，但 {anchorName primesUnder10}`primesUnder10` 比 {anchorName explicitPrimesUnder10}`explicitPrimesUnder10` 容易读得多。
:::

:::paragraph
消费 {anchorName List}`List` 的函数可以用与消费 {anchorName Nat}`Nat` 的函数大致相同的方式来定义。
事实上，理解链表的一种方式是把它看作一个 {anchorName Nat}`Nat`，其中每个 {anchorName Nat}`succ` 构造子上都悬挂着一个额外的数据字段。
从这个角度看，计算列表长度的过程就是把每个 {anchorName List}`cons` 替换为一个 {anchorName Nat}`succ`，并把最后的 {anchorName List}`nil` 替换为一个 {anchorName Nat}`zero`。
正如 {anchorName replaceX}`replaceX` 以点的字段类型作为参数一样，{anchorName length1EvalSummary}`length` 以列表条目的类型作为参数。
例如，如果列表包含字符串，那么第一个参数就是 {anchorName length1EvalSummary}`String`：{anchorEvalStep length1EvalSummary 0}`length String ["Sourdough", "bread"]`。
它应当像这样计算：

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

{anchorName length1}`length` 的定义既是多态的（因为它将列表元素类型作为实参），也是递归的（因为它引用自身）。
一般而言，函数遵循数据的形状：递归数据类型导向递归函数，多态数据类型导向多态函数。

```anchor length1
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
```

:::

按照惯例，诸如 {lit}`xs` 和 {lit}`ys` 这样的名称用于表示未知值的列表。
名称中的 {lit}`s` 表明它们是复数，因此读作 “exes” 和 “whys”，而不是 “x s” 和 “y s”。

:::paragraph
为了使列表上的函数更易读，可以使用方括号记法 {anchorTerm length2}`[]` 来对 {anchorName List}`nil` 进行模式匹配，并且可以用中缀 {anchorTerm length2}`::` 来代替 {anchorName List}`cons`：

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
file := "Implicit-Arguments"
%%%

:::paragraph
{anchorName replaceX}`replaceX` 和 {anchorName length1}`length` 使用起来都有些繁琐，因为类型参数通常由后面的值唯一确定。
事实上，在大多数语言中，编译器完全能够自行确定类型参数，只是偶尔需要用户提供帮助。
在 Lean 中也是如此。
定义函数时，可以通过用花括号而非圆括号包住参数来将参数声明为_隐式_。
例如，带有隐式类型参数的 {anchorName replaceXImp}`replaceX` 版本如下所示：

```anchor replaceXImp
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

它可以与 {anchorName replaceXImpNat}`natOrigin` 一起使用，而无需显式提供 {anchorName NatDoubleFour}`Nat`，因为 Lean 可以从后续参数中_推断_出 {anchorName replaceXImp}`α` 的值：

```anchor replaceXImpNat
#eval replaceX natOrigin 5
```

```anchorInfo replaceXImpNat
{ x := 5, y := 0 }
```

:::

:::paragraph

类似地，{anchorName lengthImp}`length` 可以重新定义为隐式地接受元素类型：

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
在标准库中，Lean 将这个函数称为 {anchorName lengthExpNat}`List.length`，这意味着用于访问结构字段的点语法也可以用来求列表的长度：

```anchor lengthDotPrimes
#eval primesUnder10.length
```

```anchorInfo lengthDotPrimes
4
```

:::

:::paragraph
正如 C# 和 Java 有时要求显式提供类型实参一样，Lean 并不总是能够找到隐式参数。
在这些情况下，可以使用它们的名称来提供它们。
例如，可以通过将 {anchorTerm lengthExpNat}`α` 设为 {anchorName lengthExpNat}`Int`，来指定一个只适用于整数列表的 {anchorName lengthExpNat}`List.length` 版本：

```anchor lengthExpNat
#check List.length (α := Int)
```

```anchorInfo lengthExpNat
List.length : List Int → Nat
```

:::

# 更多内建数据类型
%%%
tag := "more-built-in-types"
file := "More-Built-In-Datatypes"
%%%

除列表外，Lean 的标准库还包含许多其他结构和归纳数据类型，它们可以用于各种语境。

## {lit}`Option`
%%%
tag := "Option"
file := "Option"
%%%
并非每个列表都有第一个条目——有些列表是空的。
许多关于集合的操作可能无法找到它们正在寻找的对象。
例如，一个查找列表中第一个条目的函数可能找不到任何这样的条目。
因此，它必须有一种方式来表示不存在第一个条目。

许多语言都有一个表示值缺失的 {CSharp}`null` 值。
Lean 并不是给已有类型配备一个特殊的 {CSharp}`null` 值，而是提供了一个名为 {anchorName Option}`Option` 的数据类型，它为某个其他类型配备一个表示缺失值的指示器。
例如，可空的 {anchorName fragments}`Int` 由 {anchorTerm nullOne}`Option Int` 表示，而可空的字符串列表由类型 {anchorTerm fragments}`Option (List String)` 表示。
引入一个新类型来表示可空性，意味着类型系统会确保不会忘记对 {CSharp}`null` 的检查，因为 {anchorTerm nullOne}`Option Int` 不能在期望 {anchorName nullOne}`Int` 的上下文中使用。

:::paragraph
{anchorName Option}`Option` 有两个构造子，称为 {anchorName Option}`some` 和 {anchorName Option}`none`，它们分别表示底层类型的非空版本和空版本。
非空构造子 {anchorName Option}`some` 包含底层值，而 {anchorName Option}`none` 不接受任何参数：

```anchor Option
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
```

:::

{anchorName Option}`Option` 类型与 C# 和 Kotlin 等语言中的可空类型非常相似，但并不完全相同。
在这些语言中，如果某个类型（例如 {CSharp}`Boolean`）总是指称该类型的实际值（{CSharp}`true` 和 {CSharp}`false`），则类型 {CSharp}`Boolean?` 或 {CSharp}`Nullable<Boolean>` 还额外允许 {CSharp}`null` 值。
在类型系统中跟踪这一点非常有用：类型检查器和其他工具可以帮助程序员记得检查 {CSharp}`null`，而且通过类型签名显式描述可空性的 API 比不这样做的 API 提供的信息更多。
然而，这些可空类型与 Lean 的 {anchorName Option}`Option` 有一个非常重要的区别，即它们不允许多层可选性。
{anchorTerm nullThree}`Option (Option Int)` 可以用 {anchorTerm nullOne}`none`、{anchorTerm nullTwo}`some none` 或 {anchorTerm nullThree}`some (some 360)` 构造。
另一方面，Kotlin 将 {Kotlin}`T??` 视为等价于 {Kotlin}`T?`。
这种细微差别在实践中很少相关，但偶尔也会产生影响。

:::paragraph
若要查找列表中的第一个条目（如果存在），请使用 {anchorName headHuh}`List.head?`。
问号是名称的一部分，与 C# 或 Kotlin 中用问号表示可空类型的用法无关。
在 {anchorName headHuh}`List.head?` 的定义中，下划线用于表示列表的尾部。
在模式中，下划线可以匹配任何内容，但不会引入用于指代所匹配数据的变量。
使用下划线而不是名称，是一种向读者清楚传达输入中某部分被忽略的方式。

```anchor headHuh
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
```

:::

Lean 的一个命名惯例是：对于可能失败的操作，按组定义它们，并使用后缀 {lit}`?` 表示返回 {anchorName Option}`Option` 的版本，使用 {lit}`!` 表示在给定无效输入时使程序崩溃的版本，使用 {lit}`D` 表示在操作本会失败时返回默认值的版本。
遵循这一模式，{anchorName fragments}`List.head` 要求调用者提供列表非空的数学证据，{anchorName fragments}`List.head?` 返回一个 {anchorName Option}`Option`，{anchorName fragments}`List.head!` 在传入空列表时使程序崩溃，而 {anchorName fragments}`List.headD` 接受一个默认值，以便在列表为空时返回。
问号和感叹号是名称的一部分，而不是特殊语法，因为 Lean 的命名规则比许多语言更宽松。

:::paragraph

因为 {anchorName fragments}`head?` 定义在 {lit}`List` 命名空间中，所以它可以与访问器记法一起使用：

```anchor headSome
#eval primesUnder10.head?
```

```anchorInfo headSome
some 2
```

然而，尝试在空列表上测试它会导致两个错误：

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
这是因为 Lean 无法完全确定该表达式的类型。
具体而言，它既无法找到 {anchorName fragments}`List.head?` 的隐式类型实参，也无法找到 {anchorName fragments}`List.nil` 的隐式类型实参。
在 Lean 的输出中，{lit}`?m.XYZ` 表示程序中无法推断的一部分。
这些未知部分称为_元变量_，它们会出现在某些错误消息中。
为了对表达式求值，Lean 需要能够找到其类型；而由于空列表没有任何可供确定类型的条目，因此类型不可得。
显式提供一个类型即可使 Lean 继续进行：

```anchor headNone
#eval [].head? (α := Int)
```

```anchorInfo headNone
none
```

也可以用类型标注来提供该类型：

```anchor headNoneTwo
#eval ([] : List Int).head?
```

```anchorInfo headNoneTwo
none
```

错误消息提供了有用的线索。
两条消息都使用_同一个_元变量来描述缺失的隐式参数，这意味着 Lean 已经判定这两个缺失部分将共享同一个解，尽管它无法确定该解的实际值。

:::

## {lit}`Prod`
%%%
tag := "prod"
file := "Prod"
%%%

{anchorName Prod}`Prod` 结构是 “Product” 的缩写，是一种将两个值组合在一起的泛型方式。
例如，一个 {anchorTerm fragments}`Prod Nat String` 包含一个 {anchorName fragments}`Nat` 和一个 {anchorName fragments}`String`。
换言之，{anchorTerm natPoint}`PPoint Nat` 可以替换为 {anchorTerm fragments}`Prod Nat Nat`。
{anchorName fragments}`Prod` 非常类似于 C# 的元组、Kotlin 中的 {Kotlin}`Pair` 和 {Kotlin}`Triple` 类型，以及 C++ 中的 {cpp}`tuple`。
在许多应用中，即使对于像 {anchorName Point}`Point` 这样简单的情形，最好也定义自己的结构，因为使用领域术语可以使代码更易读。
此外，定义结构类型通过为不同的领域概念赋予不同类型，有助于捕获更多错误，防止它们被混淆。

另一方面，在某些情况下，定义新类型所带来的开销并不值得。
此外，一些库足够泛型，以至于并不存在比“对”更具体的概念。
最后，标准库包含多种便利函数，使得使用内置的对类型更加容易。

:::paragraph
结构体 {anchorName Prod}`Prod` 是用两个类型实参定义的：

```anchor Prod
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
```

:::

:::paragraph
列表使用得如此频繁，以至于有专门的语法使其更易读。
出于同样的原因，积类型及其构造子也都有专门的语法。
类型 {anchorTerm ProdSugar}`Prod α β` 通常写作 {anchorTerm ProdSugar}`α × β`，这与集合笛卡尔积的通常记号相呼应。
类似地，通常的数学有序对记号也可用于 {anchorName ProdSugar}`Prod`。
换言之，不必写成：

```anchor fivesStruct
def fives : String × Int := { fst := "five", snd := 5 }
```

只需写作：

```anchor fives
def fives : String × Int := ("five", 5)
```

:::

:::paragraph

这两种记号都是右结合的。
这意味着以下定义是等价的：

```anchor sevens
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
```

```anchor sevensNested
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
```

换言之，所有超过两个类型的积及其相应构造子，在幕后实际上都是嵌套积和嵌套对。

:::


## {anchorName Sum}`Sum`
%%%
tag := "Sum"
file := "Sum"
%%%

{anchorName Sum}`Sum` 数据类型是一种通用方式，用于允许在两个不同类型的值之间作出选择。
例如，一个 {anchorTerm fragments}`Sum String Int` 要么是 {anchorName fragments}`String`，要么是 {anchorName fragments}`Int`。
与 {anchorName Prod}`Prod` 一样，{anchorName Sum}`Sum` 应当用于编写非常通用的代码时、用于一小段不存在合理领域专用类型的代码时，或在标准库包含有用函数时。
在大多数情况下，使用自定义归纳类型会更易读且更易维护。

:::paragraph
类型 {anchorTerm Sumαβ}`Sum α β` 的值要么是构造子 {anchorName Sum}`inl` 应用于一个类型为 {anchorName Sum}`α` 的值，要么是构造子 {anchorName Sum}`inr` 应用于一个类型为 {anchorName Sum}`β` 的值：

```anchor Sum
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
```

这些名称分别是“左注入”和“右注入”的缩写。
正如笛卡尔积记号用于 {anchorName Prod}`Prod` 一样，“带圈加号”记号用于 {anchorName SumSugar}`Sum`，因此 {anchorTerm SumSugar}`α ⊕ β` 是 {anchorTerm SumSugar}`Sum α β` 的另一种写法。
{anchorName FakeSum}`Sum.inl` 和 {anchorName FakeSum}`Sum.inr` 没有特殊语法。

:::

:::paragraph
举例来说，如果宠物名可以是狗名或猫名，那么可将其类型作为字符串的和来引入：

```anchor PetName
def PetName : Type := String ⊕ String
```

在真实程序中，通常最好为此目的定义一个自定义归纳数据类型，并使用信息充分的构造子名称。
这里，{anchorName animals}`Sum.inl` 用于狗名，而 {anchorName animals}`Sum.inr` 用于猫名。
这些构造子可以用来写出一个动物名称列表：

```anchor animals
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]
```

:::

:::paragraph
可以使用模式匹配来区分这两个构造子。
例如，一个统计动物名称列表中狗的数量（也就是 {anchorName howManyDogs}`Sum.inl` 构造子的数量）的函数如下所示：

```anchor howManyDogs
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
```

函数调用先于中缀运算符求值，因此 {anchorTerm howManyDogsAdd}`howManyDogs morePets + 1` 与 {anchorTerm howManyDogsAdd}`(howManyDogs morePets) + 1` 相同。
如预期，{anchor dogCount}`#eval howManyDogs animals` 产生 {anchorInfo dogCount}`3`。
:::

## {anchorName Unit}`Unit`
%%%
tag := "Unit"
file := "Unit"
%%%

:::paragraph
{anchorName Unit}`Unit` 是一个只有一个无参数构造子的类型，该构造子称为 {anchorName Unit}`unit`。
换言之，它只描述单个值，而该值由所述构造子在完全不应用任何参数的情况下构成。
{anchorName Unit}`Unit` 定义如下：

```anchor Unit
inductive Unit : Type where
  | unit : Unit
```

:::

:::paragraph
就其自身而言，{anchorName Unit}`Unit` 并没有特别大的用处。
然而，在多态代码中，它可以用作缺失数据的占位符。
例如，下面的归纳数据类型表示算术表达式：

```anchor ArithExpr
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
```

类型参数 {anchorName ArithExpr}`ann` 表示标注，并且每个构造子都带有标注。
来自解析器的表达式可能带有源位置标注，因此返回类型 {anchorTerm ArithExprEx}`ArithExpr SourcePos` 确保解析器在每个子表达式处放置了一个 {anchorName ArithExprEx}`SourcePos`。
然而，不来自解析器的表达式将没有源位置，因此它们的类型可以是 {anchorTerm ArithExprEx}`ArithExpr Unit`。

:::

此外，因为所有 Lean 函数都有参数，其他语言中的零参数函数可以表示为接受一个 {anchorName ArithExprEx}`Unit` 参数的函数。
在返回位置上，{anchorName ArithExprEx}`Unit` 类型类似于 C 派生语言中的 {CSharp}`void`。
在 C 语言家族中，返回 {CSharp}`void` 的函数会将控制权返回给其调用者，但不会返回任何有意义的值。
作为一个有意设计为无意义的值，{anchorName ArithExprEx}`Unit` 使得这一点可以被表达，而无需在类型系统中要求一种专门用途的 {CSharp}`void` 特性。
Unit 的构造子可以写作空括号：{anchorTerm unitParens}`() : Unit`。

## {lit}`Empty`
%%%
tag := "Empty"
file := "Empty"
%%%

{anchorName fragments}`Empty` 数据类型完全没有构造子。
因此，它表示不可达代码，因为任何调用序列都不可能以一个类型为 {anchorName fragments}`Empty` 的值终止。

{anchorName fragments}`Empty` 的使用频率远不如 {anchorName fragments}`Unit`。
不过，它在某些专门语境中很有用。
许多多态数据类型并不会在其所有构造子中使用全部类型参数。
例如，{anchorName animals}`Sum.inl` 和 {anchorName animals}`Sum.inr` 各自只使用 {anchorName fragments}`Sum` 的一个类型参数。
将 {anchorName fragments}`Empty` 用作 {anchorName fragments}`Sum` 的一个类型参数，可以在程序中的某个特定位置排除其中一个构造子。
这可以使泛型代码用于带有额外限制的语境。

## 命名：和、积与单位
%%%
tag := "sum-products-units"
file := "Naming___-Sums___-Products___-and-Units"
%%%

一般而言，提供多个构造子的类型称为_和类型_，而其单个构造子接受多个参数的类型称为 {deftech}_积类型_。
这些术语与普通算术中使用的和与积有关。
当所涉及的类型包含有限个值时，这种关系最容易看出。
如果 {anchorName SumProd}`α` 和 {anchorName SumProd}`β` 分别是包含 $`n` 和 $`k` 个不同值的类型，那么 {anchorTerm SumProd}`α ⊕ β` 包含 $`n + k` 个不同值，而 {anchorTerm SumProd}`α × β` 包含 $`n \times k` 个不同值。
例如，{anchorName fragments}`Bool` 有两个值：{anchorName BoolNames}`true` 和 {anchorName BoolNames}`false`，而 {anchorName Unit}`Unit` 有一个值：{anchorName BooloUnit}`Unit.unit`。
积 {anchorTerm fragments}`Bool × Unit` 有两个值 {anchorTerm BoolxUnit}`(true, Unit.unit)` 和 {anchorTerm BoolxUnit}`(false, Unit.unit)`，而和 {anchorTerm fragments}`Bool ⊕ Unit` 有三个值 {anchorTerm BooloUnit}`Sum.inl true`、{anchorTerm BooloUnit}`Sum.inl false` 和 {anchorTerm BooloUnit}`Sum.inr Unit.unit`。
类似地，$`2 \times 1 = 2`，且 $`2 + 1 = 3`。

# 你可能遇到的消息
%%%
tag := "polymorphism-messages"
file := "Messages-You-May-Meet"
%%%

:::paragraph
并非所有可定义的结构或归纳类型都能具有类型 {anchorTerm Prod}`Type`。
特别地，如果某个构造子以任意类型作为参数，那么该归纳类型必须具有不同的类型。
这些错误通常会说明一些关于“宇宙层级”的内容。
例如，对于这个归纳类型：

```anchor TypeInType
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
```

Lean 给出如下错误：

```anchorError TypeInType
Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```

后面的章节会说明为什么会这样，以及如何修改定义以使其工作。
目前，请尝试把该类型作为整个归纳类型的参数，而不是作为构造子的参数。
:::

:::paragraph
类似地，如果某个构造子的实参是一个以正在定义的数据类型作为实参的函数，那么该定义会被拒绝。
例如：

```anchor Positivity
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
```

会产生消息：

```anchorError Positivity
(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
```

出于技术原因，允许这些数据类型可能会使 Lean 的内部逻辑受到破坏，从而使其不适合用作定理证明器。
:::

:::paragraph
接受两个参数的递归函数不应对参数对进行匹配，而应分别独立地匹配每个参数。
否则，Lean 中用于检查递归调用是否作用于更小值的机制，无法看出输入值与递归调用中的实参之间的联系。
例如，下面这个判断两个列表是否具有相同长度的函数会被拒绝：

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

错误消息为：

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

这个问题可以通过嵌套模式匹配来修正：

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

{ref "simultaneous-matching"}[同时匹配] 将在下一节介绍，它是解决该问题的另一种方式，而且通常更为优雅。
:::

:::paragraph
忘记给归纳类型传递参数也可能产生令人困惑的消息。
例如，当在 {anchorTerm MissingTypeArg}`ctor` 的类型中没有将参数 {anchorName MissingTypeArg}`α` 传递给 {anchorName MissingTypeArg}`MyType` 时：

```anchor MissingTypeArg
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
```

Lean 给出如下错误：

```anchorError MissingTypeArg
type expected, got
  (MyType : Type → Type)
```

错误消息是在说明，{anchorName MissingTypeArg}`MyType` 的类型，即 {anchorTerm MissingTypeArgT}`Type → Type`，其本身并不描述类型。
{anchorName MissingTypeArg}`MyType` 需要一个参数才能成为一个真正的类型。

:::

:::paragraph
当在其他上下文中省略类型参数时，也可能出现同样的消息，例如在某个定义的类型签名中：

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
对使用多态类型的表达式求值时，可能会触发 Lean 无法显示某个值的情形。
{anchorTerm evalAxe}`#eval` 命令会对所提供的表达式求值，并使用该表达式的类型来确定如何显示结果。
对于某些类型（例如函数），这一过程会失败，但对于大多数其他类型，Lean 完全能够自动生成显示代码。
例如，不需要为 {anchorName WoodSplittingTool}`WoodSplittingTool` 向 Lean 提供任何特定的显示代码：
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
不过，Lean 在这里使用的自动化是有限度的。
{anchorName allTools}`allTools` 是包含全部三个工具的列表：
```anchor allTools
def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]
```
对它求值会导致错误：
```anchor evalAllTools
#eval allTools
```
```anchorError evalAllTools
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  List WoodSplittingTool
```
这是因为 Lean 试图使用内置表中的代码来显示一个列表，但这段代码要求 {anchorName WoodSplittingTool}`WoodSplittingTool` 的显示代码已经存在。
可以通过指示 Lean 在定义数据类型时生成这段显示代码，而不是在作为 {anchorTerm evalAllTools}`#eval` 的一部分的最后时刻才生成，来绕过这个错误；方法是在其定义中添加 {anchorTerm Firewood}`deriving Repr`：
```anchor Firewood
inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr
```
对 {anchorName Firewood}`Firewood` 的列表求值会成功：
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
file := "Exercises"
%%%

 * 编写一个函数，用于查找列表中的最后一个条目。它应返回一个 {anchorName fragments}`Option`。
 * 编写一个函数，找出列表中第一个满足给定谓词的元素。以 {anchorTerm List.findFirst?Ex}`def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …` 开始该定义。
 * 编写一个函数 {anchorName Prod.switchEx}`Prod.switch`，将一个对中的两个字段彼此交换。以 {anchor Prod.switchEx}`def Prod.switch {α β : Type} (pair : α × β) : β × α := …` 开始该定义。
 * 将 {anchorName PetName}`PetName` 示例改写为使用自定义数据类型，并将其与使用 {anchorName Sum}`Sum` 的版本进行比较。
 * 编写一个函数 {anchorName zipEx}`zip`，将两个列表组合成一个由配对组成的列表。所得列表的长度应与较短的输入列表相同。以 {anchor zipEx}`def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …` 开始该定义。
 * 编写一个多态函数 {anchorName takeOne}`take`，返回列表中的前 $`n` 个条目，其中 $`n` 是一个 {anchorName fragments}`Nat`。如果该列表包含的条目少于 $`n` 个，则结果列表应为整个输入列表。{anchorTerm takeThree}`#eval take 3 ["bolete", "oyster"]` 应产生 {anchorInfo takeThree}`["bolete", "oyster"]`，而 {anchor takeOne}`#eval take 1 ["bolete", "oyster"]` 应产生 {anchorInfo takeOne}`["bolete"]`。
 * 利用类型与算术之间的类比，编写一个将积对和作分配的函数。换言之，它应具有类型 {anchorTerm distr}`α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`。
 * 利用类型与算术之间的类比，编写一个函数，将乘以二转换为和。换言之，它应具有类型 {anchorTerm distr}`Bool × α → α ⊕ α`。
