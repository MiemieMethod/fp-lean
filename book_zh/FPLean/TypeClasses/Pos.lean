import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "正数" =>
%%%
tag := "positive-numbers"
file := "Positive-Numbers"
%%%

在某些应用中，只有正数才有意义。
例如，编译器和解释器通常对源代码位置使用从一开始计数的行号和列号，而表示非空列表的数据类型永远不会报告长度为零。
与其依赖自然数，并在代码中到处加入该数不为零的断言，不如设计一种只表示正数的数据类型。

表示正数的一种方式与 {anchorTerm chapterIntro}`Nat` 非常相似，只是以 {anchorTerm Pos}`one` 作为基本情形，而不是 {anchorTerm Nat.zero}`zero`：

```anchor Pos
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
```
此数据类型精确地表示了预期的值集合，但使用起来并不十分方便。
例如，数值字面量会被拒绝：
```anchor sevenOops
def seven : Pos := 7
```
```anchorError sevenOops
failed to synthesize
  OfNat Pos 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
相反，必须直接使用构造子：
```anchor seven
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
```

类似地，加法和乘法也不容易使用：
```anchor fourteenOops
def fourteen : Pos := seven + seven
```
```anchorError fourteenOops
failed to synthesize
  HAdd Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```anchor fortyNineOops
def fortyNine : Pos := seven * seven
```
```anchorError fortyNineOops
failed to synthesize
  HMul Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

这些错误消息中的每一条都以 {lit}`failed to synthesize` 开头。
这表明错误是由尚未实现的重载操作导致的，并且它描述了必须实现的类型类。

# 类与实例
%%%
tag := "classes-and-instances"
file := "Classes-and-Instances"
%%%

类型类由一个名称、若干参数以及一组 {deftech}_方法_ 组成。
这些参数描述正在为哪些类型定义可重载操作，而方法则是这些可重载操作的名称和类型签名。
这里再次出现了与面向对象语言的术语冲突。
在面向对象编程中，方法本质上是一个与内存中特定对象相连接的函数，并且能够特殊地访问该对象的私有状态。
对象通过其方法进行交互。
在 Lean 中，“方法”一词指的是一个已声明为可重载的操作，它与对象、值或私有字段没有特殊联系。

重载加法的一种方式是定义一个名为 {anchorName Plus}`Plus` 的类型类，其中包含一个名为 {anchorName Plus}`plus` 的加法方法。
一旦为 {anchorTerm chapterIntro}`Nat` 定义了 {anchorTerm Plus}`Plus` 的实例，就可以使用 {anchorName plusNatFiveThree}`Plus.plus` 将两个 {anchorTerm chapterIntro}`Nat` 相加：
```anchor plusNatFiveThree
#eval Plus.plus 5 3
```
```anchorInfo plusNatFiveThree
8
```
添加更多实例会使 {anchorName plusNatFiveThree}`Plus.plus` 能够接受更多类型的参数。

在下面的类型类声明中，{anchorName Plus}`Plus` 是类名，{anchorTerm Plus}`α : Type` 是唯一的参数，{anchorTerm Plus}`plus : α → α → α` 是唯一的方法：

```anchor Plus
class Plus (α : Type) where
  plus : α → α → α
```
这个声明表示存在一个类型类 {anchorName Plus}`Plus`，它针对类型 {anchorName Plus}`α` 对操作进行重载。
特别地，其中有一个名为 {anchorName Plus}`plus` 的重载操作，它接受两个 {anchorName Plus}`α` 并返回一个 {anchorName Plus}`α`。

类型类是一等的，正如类型是一等的一样。
特别地，类型类是另一种类型。
{anchorTerm PlusType}`Plus` 的类型是 {anchorTerm PlusType}`Type → Type`，因为它接受一个类型作为实参（{anchorName Plus}`α`），并产生一个新的类型，该类型描述了 {anchorName Plus}`α` 上 {anchorName Plus}`Plus` 操作的重载。


要为某个特定类型重载 {anchorName PlusNat}`plus`，请编写一个实例：

```anchor PlusNat
instance : Plus Nat where
  plus := Nat.add
```
{anchorTerm PlusNat}`instance` 后面的冒号表明 {anchorTerm PlusNat}`Plus Nat` 确实是一个类型。
类 {anchorName Plus}`Plus` 的每个方法都应当使用 {anchorTerm PlusNat}`:=` 赋予一个值。
在此例中，只有一个方法：{anchorName PlusNat}`plus`。

默认情况下，类型类方法定义在与该类型类同名的命名空间中。
对该命名空间执行 {anchorTerm openPlus}`open` 可能很方便，这样用户就不需要先键入类名。
{kw}`open` 命令中的圆括号表示只使该命名空间中所指明的名称可访问：

```anchor openPlus
open Plus (plus)
```
```anchor plusNatFiveThreeAgain
#eval plus 5 3
```
```anchorInfo plusNatFiveThreeAgain
8
```

为 {anchorName PlusPos}`Pos` 定义一个加法函数并定义一个 {anchorTerm PlusPos}`Plus Pos` 实例，就允许使用 {anchorName PlusPos}`plus` 来同时对 {anchorName PlusPos}`Pos` 和 {anchorTerm chapterIntro}`Nat` 值做加法：

```anchor PlusPos
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
```

因为尚不存在 {anchorTerm PlusFloat}`Plus Float` 的实例，试图用 {anchorName plusFloatFail}`plus` 将两个浮点数相加会失败，并给出熟悉的消息：
```anchor plusFloatFail
#eval plus 5.2 917.25861
```
```anchorError plusFloatFail
failed to synthesize
  Plus Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
这些错误表示 Lean 无法为给定的类型类找到实例。

# 重载加法
%%%
tag := "overloaded-addition"
file := "Overloaded-Addition"
%%%

Lean 内建的加法运算符是一个名为 {anchorName chapterIntro}`HAdd` 的类型类的语法糖；该类型类灵活地允许加法的各个参数具有不同类型。
{anchorName chapterIntro}`HAdd` 是 _heterogeneous addition_（异质加法）的缩写。
例如，可以编写一个 {anchorName chapterIntro}`HAdd` 实例，使得一个 {anchorName chapterIntro}`Nat` 能够与一个 {anchorName fiveZeros}`Float` 相加，从而得到一个新的 {anchorName fiveZeros}`Float`。
当程序员写下 {anchorTerm plusDesugar}`x + y` 时，它会被解释为表示 {anchorTerm plusDesugar}`HAdd.hAdd x y`。

尽管要理解 {anchorName chapterIntro}`HAdd` 的完全一般性，需要依赖于 {ref "out-params"}[本章另一节] 中讨论的特性，但有一个更简单的类型类 {anchorName AddPos}`Add`，它不允许混合参数的类型。
Lean 库被设置为：当搜索一个两个参数具有相同类型的 {anchorName chapterIntro}`HAdd` 实例时，会找到一个 {anchorName AddPos}`Add` 实例。

定义一个 {anchorTerm AddPos}`Add Pos` 实例允许 {anchorTerm AddPos}`Pos` 值使用通常的加法语法：

```anchor AddPos
instance : Add Pos where
  add := Pos.plus
```
```anchor betterFourteen
def fourteen : Pos := seven + seven
```

# 转换为字符串
%%%
tag := "conversion-to-strings"
file := "Conversion-to-Strings"
%%%

另一个有用的内建类称为 {anchorName UglyToStringPos}`ToString`。
{anchorName UglyToStringPos}`ToString` 的实例提供了一种标准方式，用于将给定类型的值转换为字符串。
例如，当一个值出现在插值字符串中时，会使用 {anchorName UglyToStringPos}`ToString` 实例；它还决定了在 {ref "running-a-program"}[{anchorName readFile}`IO` 的描述开头]使用的 {anchorName printlnType}`IO.println` 函数将如何显示一个值。

例如，将 {anchorName Pos}`Pos` 转换为 {anchorName readFile}`String` 的一种方式是揭示其内部结构。
函数 {anchorName posToStringStructure}`posToString` 接受一个 {anchorName posToStringStructure}`Bool`，该参数决定是否为 {anchorName posToStringStructure}`Pos.succ` 的使用加上括号；在对该函数的初始调用中它应为 {anchorName CoeBoolProp}`true`，而在所有递归调用中应为 {anchorName posToStringStructure}`false`。

```anchor posToStringStructure
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
```
将此函数用于一个 {anchorName UglyToStringPos}`ToString` 实例：

```anchor UglyToStringPos
instance : ToString Pos where
  toString := posToString true
```
会得到信息丰富但令人难以招架的输出：
```anchor sevenLong
#eval s!"There are {seven}"
```
```anchorInfo sevenLong
"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"
```

另一方面，每个正数都有一个对应的 {anchorTerm chapterIntro}`Nat`。
将它转换为一个 {anchorTerm chapterIntro}`Nat`，然后使用 {anchorTerm chapterIntro}`ToString Nat` 实例（也就是 {anchorTerm chapterIntro}`Nat` 上 {anchorName UglyToStringPos}`ToString` 的重载），是一种快速生成短得多的输出的方法：

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
```anchor PosToStringNat
instance : ToString Pos where
  toString x := toString (x.toNat)
```
```anchor sevenShort
#eval s!"There are {seven}"
```
```anchorInfo sevenShort
"There are 7"
```
当定义了多个实例时，最近定义的实例具有优先权。
此外，如果一个类型具有 {anchorName UglyToStringPos}`ToString` 实例，那么它就可用于显示 {kw}`#eval` 的结果，因此 {anchorTerm sevenEvalStr}`#eval seven` 输出 {anchorInfo sevenEvalStr}`7`。

# 重载乘法
%%%
tag := "overloaded-multiplication"
file := "Overloaded-Multiplication"
%%%

对于乘法，有一个名为 {anchorName MulPPoint}`HMul` 的类型类，它像 {anchorName chapterIntro}`HAdd` 一样允许混合参数类型。
正如 {anchorTerm plusDesugar}`x + y` 被解释为 {anchorTerm plusDesugar}[`HAdd.hAdd x y`]，{anchorTerm timesDesugar}`x * y` 被解释为 {anchorTerm timesDesugar}`HMul.hMul x y`。
对于两个参数类型相同的乘法这一常见情形，一个 {anchorName PosMul}`Mul` 实例就足够了。

{anchorTerm PosMul}`Mul` 的一个实例允许对 {anchorName PosMul}`Pos` 使用通常的乘法语法：

```anchor PosMul
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
```
有了这个实例，乘法会按预期工作：
```anchor muls
#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]
```
```anchorInfo muls
[7, 49, 14]
```

# 数字字面量
%%%
tag := "literal-numbers"
file := "Literal-Numbers"
%%%

为正数写出一串构造子相当不便。
解决这个问题的一种方法是提供一个函数，将 {anchorTerm chapterIntro}`Nat` 转换为 {anchorName Pos}`Pos`。
然而，这种方法有其缺点。
首先，由于 {anchorName PosMul}`Pos` 不能表示 {anchorTerm nats}`0`，所得函数要么会把一个 {anchorTerm chapterIntro}`Nat` 转换为更大的数，要么会返回 {anchorTerm PosStuff}`Option Pos`。
这两种方式对用户来说都并不特别方便。
其次，必须显式调用该函数，会使使用正数的程序比使用 {anchorTerm chapterIntro}`Nat` 的程序书写起来不方便得多。
精确类型与便利 API 之间存在取舍，意味着精确类型会变得不那么有用。

有三个类型类用于重载数值字面量：{anchorName Zero}`Zero`、{anchorName One}`One` 和 {anchorName OfNat}`OfNat`。
由于许多类型都有一些自然地用 {anchorTerm nats}`0` 书写的值，{anchorName Zero}`Zero` 类允许重写这些特定的值。
它定义如下：

```anchor Zero
class Zero (α : Type) where
  zero : α
```
因为 {anchorTerm nats}`0` 不是正数，所以不应存在 {anchorTerm PosStuff}`Zero Pos` 的实例。

类似地，许多类型具有自然地用 {anchorTerm nats}`1` 书写的值。
{anchorName One}`One` 类允许重写这些表示：
```anchor One
class One (α : Type) where
  one : α
```
{anchorTerm OnePos}`One Pos` 的一个实例完全合理：
```anchor OnePos
instance : One Pos where
  one := Pos.one
```
有了这个实例，{anchorTerm onePos}`1` 就可以用于 {anchorTerm OnePos}`Pos.one`：
```anchor onePos
#eval (1 : Pos)
```
```anchorInfo onePos
1
```

在 Lean 中，自然数字面量通过一个名为 {anchorName OfNat}`OfNat` 的类型类来解释：

```anchor OfNat
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
```
这个类型类接受两个参数：{anchorTerm OfNat}`α` 是对自然数进行重载的目标类型，而未命名的 {anchorTerm chapterIntro}`Nat` 参数是在程序中实际遇到的字面量数字。
随后，方法 {anchorName OfNat}`ofNat` 被用作该数值字面量的值。
由于该类包含 {anchorTerm chapterIntro}`Nat` 参数，因此可以只为那些数字有意义的值定义实例。

{anchorTerm OfNat}`OfNat` 表明，类型类的参数不必是类型。
由于 Lean 中的类型是该语言中的一等参与者，可以作为参数传递给函数，也可以用 {kw}`def` 和 {kw}`abbrev` 给出定义，因此不存在任何障碍会阻止在某些位置使用非类型参数；在灵活性较低的语言中，这些位置可能不允许这样的参数。
这种灵活性使得可以为特定值以及特定类型提供重载运算。
此外，它还使 Lean 标准库能够安排在存在 {anchorTerm ListSum}`OfNat α 0` 实例时也存在 {anchorTerm ListSumZ}`Zero α` 实例，反之亦然。
类似地，{anchorTerm OneExamples}`One α` 的实例蕴含 {anchorTerm OneExamples}`OfNat α 1` 的实例，正如 {anchorTerm OneExamples}`OfNat α 1` 的实例蕴含 {anchorTerm OneExamples}`One α` 的实例一样。

表示小于四的自然数的和类型可以定义如下：

```anchor LT4
inductive LT4 where
  | zero
  | one
  | two
  | three
```
虽然允许_任意_数字字面量用于此类型并不合理，但小于四的数字显然是合理的：

```anchor LT4ofNat
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
```
有了这些实例，下面的例子可以工作：
```anchor LT4three
#eval (3 : LT4)
```
```anchorInfo LT4three
LT4.three
```
```anchor LT4zero
#eval (0 : LT4)
```
```anchorInfo LT4zero
LT4.zero
```
另一方面，越界字面量仍然是不允许的：
```anchor LT4four
#eval (4 : LT4)
```
```anchorError LT4four
failed to synthesize
  OfNat LT4 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  LT4
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

对于 {anchorName PosMul}`Pos`，{anchorTerm OfNat}`OfNat` 实例应当适用于除 {anchorName PosStuff}`Nat.zero` 之外的_任意_ {anchorTerm chapterIntro}`Nat`。
另一种表述方式是：对于所有自然数 {anchorTerm posrec}`n`，该实例应当适用于 {anchorTerm posrec}`n + 1`。
正如像 {anchorTerm posrec}`α` 这样的名称会自动成为由 Lean 自行填充的函数隐式参数一样，实例也可以接受自动隐式参数。
在这个实例中，参数 {anchorTerm OfNatPos}`n` 代表任意 {anchorTerm chapterIntro}`Nat`，而该实例是为大一的 {anchorTerm chapterIntro}`Nat` 定义的：

```anchor OfNatPos
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
```
由于 {anchorTerm OfNatPos}`n` 表示比用户所写的数小一的 {anchorTerm chapterIntro}`Nat`，辅助函数 {anchorName OfNatPos}`natPlusOne` 返回一个比其参数大一的 {anchorName OfNatPos}`Pos`。
这使得可以将自然数文字用于正数，但不能用于零：

```anchor eight
def eight : Pos := 8
```
```anchor zeroBad
def zero : Pos := 0
```
```anchorError zeroBad
failed to synthesize
  OfNat Pos 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

# 练习
%%%
tag := "positive-numbers-exercises"
file := "Exercises"
%%%

## 另一种表示
%%%
tag := "positive-numbers-another-representation"
file := "Another-Representation"
%%%

表示正数的另一种方式是把它表示为某个 {anchorTerm chapterIntro}`Nat` 的后继。
请将 {anchorName PosStuff}`Pos` 的定义替换为一个结构，其构造子名为 {anchorName AltPos}`succ`，并包含一个 {anchorTerm chapterIntro}`Nat`：

```anchor AltPos
structure Pos where
  succ ::
  pred : Nat
```
定义 {moduleName}`Add`、{moduleName}`Mul`、{anchorName UglyToStringPos}`ToString` 和 {moduleName}`OfNat` 的实例，使得这个版本的 {anchorName AltPos}`Pos` 能够方便地使用。

## 偶数
%%%
tag := "even-numbers-ex"
file := "Even-Numbers"
%%%

定义一个只表示偶数的数据类型。定义 {moduleName}`Add`、{moduleName}`Mul` 和 {anchorName UglyToStringPos}`ToString` 的实例，使其能够被方便地使用。
{moduleName}`OfNat` 需要 {ref "tc-polymorphism"}[下一节] 中引入的特性。

## HTTP 请求
%%%
tag := "http-request-ex"
file := "HTTP-Requests"
%%%

一个 HTTP 请求以标识 HTTP 方法开始，例如 {lit}`GET` 或 {lit}`POST`，并伴随一个 URI 和一个 HTTP 版本。
定义一个归纳类型来表示 HTTP 方法中一个有意义的子集，并定义一个结构来表示 HTTP 响应。
响应应当具有一个 {anchorName UglyToStringPos}`ToString` 实例，使其能够被调试。
使用一个类型类将不同的 {moduleName}`IO` 动作与每个 HTTP 方法关联起来，并编写一个作为 {moduleName}`IO` 动作的测试框架，调用每个方法并打印结果。
