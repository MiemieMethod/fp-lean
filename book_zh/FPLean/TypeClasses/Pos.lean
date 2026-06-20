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
%%%

在某些应用中，只有正数才是有意义的。
例如，编译器和解释器通常对源代码位置使用从一开始计数的行号和列号，而只表示非空列表的数据类型永远不会报告长度为零。
与其依赖自然数并在代码中到处散布“该数不为零”的断言，不如设计一种只表示正数的数据类型，这往往更有用。

表示正数的一种方式与 {anchorTerm chapterIntro}`Nat` 非常相似，只不过它以 {anchorTerm Pos}`one` 而不是 {anchorTerm Nat.zero}`zero` 作为基本情形：

```anchor Pos
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
```
这个数据类型很好的代表了我们期望的值的集合，但是它用起来并不是很方便。比如说，无法使用数字字面量。
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
而是必须要直接使用构造器。
```anchor seven
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
```

类似地，加法和乘法用起来也很费劲。
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

这些错误消息都以 {lit}`failed to synthesize` 开头。这意味着这个错误是因为使用的操作符重载还没有被实现，并且指出了应该实现的类型类。

# 类和实例
%%%
tag := "classes-and-instances"
%%%

一个类型类是由名称，一些参数，和一族 {deftech}*方法（Method）* 组成。参数定义了可重载运算符的类型，而方法则是可重载运算符的名称和类型签名。这里再次出现了与面向对象语言之间的术语冲突。在面向对象编程中，一个方法本质上是一个与内存中的一个特定对象有关联的函数，并且具有访问该对象的私有状态的特权。我们通过方法与对象进行交互。在 Lean 中，“方法”这个词项指的是一个被声明为可重载的运算符，与对象、值或是私有字段并无特殊关联。

一种重载加法的方法是定义一个名为 {anchorName Plus}`Plus` 的类型类，其加法方法名为 {anchorName Plus}`plus`。
一旦为 {anchorTerm chapterIntro}`Nat` 定义了 {anchorTerm Plus}`Plus` 的实例，就可以使用 {anchorName plusNatFiveThree}`Plus.plus` 将两个 {anchorTerm chapterIntro}`Nat` 相加：
```anchor plusNatFiveThree
#eval Plus.plus 5 3
```
```anchorInfo plusNatFiveThree
8
```
添加更多实例可以使 {anchorName plusNatFiveThree}`Plus.plus` 接受更多类型的参数。

在以下类型类声明中，{anchorName Plus}`Plus` 是类的名称，{anchorTerm Plus}`α : Type` 是唯一的参数，{anchorTerm Plus}`plus : α → α → α` 是唯一的方法：

```anchor Plus
class Plus (α : Type) where
  plus : α → α → α
```
该声明表示存在一个类型类 {anchorName Plus}`Plus`，它重载了关于类型 {anchorName Plus}`α` 的操作。
具体到这段代码，存在一个名为 {anchorName Plus}`plus` 的重载操作，它接受两个 {anchorName Plus}`α` 并返回一个 {anchorName Plus}`α`。

类型类是一等公民，就像类型是一等公民一样。我们其实可以说，类型类是另一种类型。
{anchorTerm PlusType}`Plus` 的类型是 {anchorTerm PlusType}`Type → Type`，因为它接受一个类型作为参数 ({anchorName Plus}`α`) 并产生一个新类型，该类型描述了 {anchorName Plus}`Plus` 的运算符对 {anchorName Plus}`α` 的重载。


写一个实例来为特定类型重载 {anchorName PlusNat}`plus` ：

```anchor PlusNat
instance : Plus Nat where
  plus := Nat.add
```
{anchorTerm PlusNat}`instance` 后面的冒号表示 {anchorTerm PlusNat}`Plus Nat` 确实是一个类型。
类 {anchorName Plus}`Plus` 的每个方法都应使用 {anchorTerm PlusNat}`:=` 赋值。
在这种情况下，只有一个方法：{anchorName PlusNat}`plus`。

默认情况下，类型类方法定义在与类型类同名的命名空间中。
如果将该命名空间打开（使用 {anchorTerm openPlus}`open` 指令）会使该方法使用起来十分方便——这样用户就不用先输入类名了。
{kw}`open` 指令后跟的括号表示只有括号内指定的名称才可以被访问。

```anchor openPlus
open Plus (plus)
```
```anchor plusNatFiveThreeAgain
#eval plus 5 3
```
```anchorInfo plusNatFiveThreeAgain
8
```

为 {anchorName PlusPos}`Pos` 定义加法函数和 {anchorTerm PlusPos}`Plus Pos` 的实例允许 {anchorName PlusPos}`plus` 用于将 {anchorName PlusPos}`Pos` 和 {anchorTerm chapterIntro}`Nat` 值相加：

```anchor PlusPos
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
```

因为还没有 {anchorTerm PlusFloat}`Plus Float` 的实例，所以尝试用 {anchorName plusFloatFail}`plus` 将两个浮点数相加会失败，并显示一条熟悉的消息：
```anchor plusFloatFail
#eval plus 5.2 917.25861
```
```anchorError plusFloatFail
failed to synthesize
  Plus Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
这些错误意味着 Lean 无法为给定的类型类找到实例。

# 重载加法
%%%
tag := "overloaded-addition"
%%%

Lean 的内置加法运算符是名为 {anchorName chapterIntro}`HAdd` 的类型类的语法糖，它灵活地允许加法参数具有不同的类型。
{anchorName chapterIntro}`HAdd` 是*异构加法*的缩写。
例如，可以编写一个 {anchorName chapterIntro}`HAdd` 实例，以允许将 {anchorName chapterIntro}`Nat` 添加到 {anchorName fiveZeros}`Float` 中，从而产生一个新的 {anchorName fiveZeros}`Float`。
当程序员编写 {anchorTerm plusDesugar}`x + y` 时，它被解释为 {anchorTerm plusDesugar}`HAdd.hAdd x y`。

虽然对 {anchorName chapterIntro}`HAdd` 的完全通用性的理解依赖于 {ref "out-params"}[本章另一节] 中讨论的功能，但有一个更简单的类型类称为 {anchorName AddPos}`Add`，它不允许混合参数的类型。
Lean 库的设置使得在搜索两个参数具有相同类型的 {anchorName chapterIntro}`HAdd` 实例时，会找到 {anchorName AddPos}`Add` 的实例。

定义 {anchorTerm AddPos}`Add Pos` 的实例允许 {anchorTerm AddPos}`Pos` 值使用普通的加法语法：

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
%%%

另一个有用的内置类称为 {anchorName UglyToStringPos}`ToString`。
{anchorName UglyToStringPos}`ToString` 的实例提供了一种将值从给定类型转换为字符串的标准方法。
例如，当一个值出现在插值字符串中时，会使用 {anchorName UglyToStringPos}`ToString` 实例，它决定了在 {ref "running-a-program"}[{anchorName readFile}`IO` 描述的开头] 使用的 {anchorName printlnType}`IO.println` 函数将如何显示一个值。

例如，将 {anchorName Pos}`Pos` 转换为 {anchorName readFile}`String` 的一种方法是揭示其内部结构。
函数 {anchorName posToStringStructure}`posToString` 接受一个 {anchorName posToStringStructure}`Bool`，它决定是否对 {anchorName posToStringStructure}`Pos.succ` 的使用进行括号括起来，在对函数的初始调用中应为 {anchorName CoeBoolProp}`true`，在所有递归调用中应为 {anchorName posToStringStructure}`false`。

```anchor posToStringStructure
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
```
将此函数用于 {anchorName UglyToStringPos}`ToString` 实例：

```anchor UglyToStringPos
instance : ToString Pos where
  toString := posToString true
```
结果是信息丰富但又但可能过于冗长的输出：
```anchor sevenLong
#eval s!"There are {seven}"
```
```anchorInfo sevenLong
"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"
```

另一方面，每个正数都有一个对应的 {anchorTerm chapterIntro}`Nat`。
将其转换为 {anchorTerm chapterIntro}`Nat`，然后使用 {anchorTerm chapterIntro}`ToString Nat` 实例（即 {anchorName UglyToStringPos}`ToString` 对 {anchorTerm chapterIntro}`Nat` 的重载）是生成更短输出的快捷方法：

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
当定义了多个实例时，最新的实例优先。
此外，如果一个类型具有 {anchorName UglyToStringPos}`ToString` 实例，那么它也可以用于显示 {kw}`#eval` 的结果，因此 {anchorTerm sevenEvalStr}`#eval seven` 输出 {anchorInfo sevenEvalStr}`7`。

# 重载乘法
%%%
tag := "overloaded-multiplication"
%%%

对于乘法，有一个名为 {anchorName MulPPoint}`HMul` 的类型类，它允许混合参数类型，就像 {anchorName chapterIntro}`HAdd` 一样。
就像 {anchorTerm plusDesugar}`x + y` 被解释为 {anchorTerm plusDesugar}[`HAdd.hAdd x y`] 一样，{anchorTerm timesDesugar}`x * y` 被解释为 {anchorTerm timesDesugar}`HMul.hMul x y`。
对于两个相同类型参数相乘的常见情况，一个 {anchorName PosMul}`Mul` 实例就足够了。

{anchorTerm PosMul}`Mul` 的实例允许将普通乘法语法与 {anchorName PosMul}`Pos` 一起使用：

```anchor PosMul
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
```
有了这个实例，乘法就可以正常工作了：
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
%%%

写一串构造器来表示正数是非常不方便的。一种解决问题的方法是提供一个将 {anchorTerm chapterIntro}`Nat` 转换为 {anchorName Pos}`Pos` 的函数。
然而，这种方法也有缺点。
首先，因为  {anchorName PosMul}`Pos` 不能表示 {anchorTerm nats}`0`，所以生成的函数要么将 {anchorTerm chapterIntro}`Nat` 转换为更大的数字，要么返回 {anchorTerm PosStuff}`Option Pos`。
这两种方法对用户来说都不是特别方便。其次，需要显式调用函数会让使用正数的程序不如使用 {anchorTerm chapterIntro}`Nat` 的程序那么方便。
在精确的类型和方便的 API 之间权衡一下后，精确的类型还是没那么有用。

有三个类型类用于重载数字字面量：{anchorName Zero}`Zero`，{anchorName One}`One`，和 {anchorName OfNat}`OfNat`。
因为许多类型的值很自然地写作 {anchorTerm nats}`0` ，所以 {anchorName Zero}`Zero` 类允许重写这些特定值。
它的定义如下：

```anchor Zero
class Zero (α : Type) where
  zero : α
```
因为 {anchorTerm nats}`0` 不是正数，所以不应该有 {anchorTerm PosStuff}`Zero Pos` 的实例。

类似地，许多类型的值很自然地写作 {anchorTerm nats}`1` 。所以 {anchorName One}`One` 类允许重写这些特定值：
```anchor One
class One (α : Type) where
  one : α
```
{anchorTerm OnePos}`One Pos` 的实例很有意义：
```anchor OnePos
instance : One Pos where
  one := Pos.one
```
有了这个实例，{anchorTerm onePos}`1` 可以用于 {anchorTerm OnePos}`Pos.one`：
```anchor onePos
#eval (1 : Pos)
```
```anchorInfo onePos
1
```

在 Lean 中，自然数字面量使用名为 {anchorName OfNat}`OfNat` 的类型类来解释：

```anchor OfNat
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
```
该类型类接受两个参数：{anchorTerm OfNat}`α` 是为其重载自然数的类型，未命名的 {anchorTerm chapterIntro}`Nat` 参数是程序中遇到的实际字面量数字。
然后，方法 {anchorName OfNat}`ofNat` 用作数字字面量的值。
因为该类包含 {anchorTerm chapterIntro}`Nat` 参数，所以可以只为那些数字有意义的值定义实例。

{anchorTerm OfNat}`OfNat` 表明类型类的参数不必是类型。
因为 Lean 中的类型是语言的一等公民，可以作为参数传递给函数，并使用 {kw}`def` 和 {kw}`abbrev` 进行定义，所以在灵活性较差的语言无法允许的位置，没有障碍阻止非类型参数。
这种灵活性允许为特定值和特定类型提供重载操作。
此外，它还允许 Lean 标准库安排在存在 {anchorTerm ListSum}`OfNat α 0` 实例时存在 {anchorTerm ListSumZ}`Zero α` 实例，反之亦然。
类似地，{anchorTerm OneExamples}`One α` 的实例意味着 {anchorTerm OneExamples}`OfNat α 1` 的实例，就像 {anchorTerm OneExamples}`OfNat α 1` 的实例意味着 {anchorTerm OneExamples}`One α` 的实例一样。

表示小于 4 的自然数的和类型可以定义如下：

```anchor LT4
inductive LT4 where
  | zero
  | one
  | two
  | three
```
虽然允许将*任何*字面量数字用于此类型没有意义，但小于 4 的数字显然有意义：

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
有了这些实例，以下示例就可以工作了：
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
另一方面，仍然不允许使用越界字面量：
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

对于 {anchorName PosMul}`Pos`，{anchorTerm OfNat}`OfNat` 实例应该适用于除 {anchorName PosStuff}`Nat.zero` 之外的*任何* {anchorTerm chapterIntro}`Nat`。
另一种说法是，对于所有自然数 {anchorTerm posrec}`n`，实例应该适用于 {anchorTerm posrec}`n + 1`。
就像 {anchorTerm posrec}`α` 这样的名称自动成为 Lean 自己填充的函数的隐式参数一样，实例也可以接受自动隐式参数。
在这种情况下，参数 {anchorTerm OfNatPos}`n` 代表任何 {anchorTerm chapterIntro}`Nat`，并且实例是为一个比它大一的 {anchorTerm chapterIntro}`Nat` 定义的：

```anchor OfNatPos
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
```
因为 {anchorTerm OfNatPos}`n` 代表比用户写的少一的 {anchorTerm chapterIntro}`Nat`，所以辅助函数 {anchorName OfNatPos}`natPlusOne` 返回一个比其参数大一的 {anchorName OfNatPos}`Pos`。
这使得可以对正数使用自然数字面量，但不能对零使用：

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
%%%

## 另一种表示法
%%%
tag := "positive-numbers-another-representation"
%%%

表示正数的另一种方法是作为某个 {anchorTerm chapterIntro}`Nat` 的后继。
将 {anchorName PosStuff}`Pos` 的定义替换为一个结构，其构造函数名为 {anchorName AltPos}`succ`，其中包含一个 {anchorTerm chapterIntro}`Nat`：

```anchor AltPos
structure Pos where
  succ ::
  pred : Nat
```
定义 {moduleName}`Add`、{moduleName}`Mul`、{anchorName UglyToStringPos}`ToString` 和 {moduleName}`OfNat` 的实例，以方便地使用此版本的 {anchorName AltPos}`Pos`。

## 偶数
%%%
tag := "even-numbers-ex"
%%%

定义一个只表示偶数的数据类型。定义 {moduleName}`Add`、{moduleName}`Mul` 和 {anchorName UglyToStringPos}`ToString` 的实例，以方便地使用它。
{moduleName}`OfNat` 需要在 {ref "tc-polymorphism"}[下一节] 中介绍的功能。

## HTTP 请求
%%%
tag := "http-request-ex"
%%%

HTTP 请求以 HTTP 方法的标识（例如 {lit}`GET` 或 {lit}`POST`）、URI 和 HTTP 版本开头。
定义一个表示 HTTP 方法的有趣子集的归纳类型，以及一个表示 HTTP 响应的结构。
响应应该有一个 {anchorName UglyToStringPos}`ToString` 实例，以便可以调试它们。
使用类型类将不同的 {moduleName}`IO` 操作与每个 HTTP 方法相关联，并编写一个测试工具作为 {moduleName}`IO` 操作，该操作调用每个方法并打印结果。
