import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "强制类型转换" =>
%%%
tag := "coercions"
file := "Coercions"
%%%


在数学中，常常在不同语境下用同一个符号表示某个对象的不同方面。
例如，如果在期望一个集合的语境中提到一个环，那么通常理解为所指的是该环的底层集合。
在编程语言中，常常有一些规则用于把一种类型的值自动转换为另一种类型的值。
Java 允许将 {java}`byte` 自动提升为 {java}`int`，而 Kotlin 允许在期望某类型的可空版本的语境中使用该类型的非空版本。

在 Lean 中，这两个目的都由一种称为 {deftech}_强制类型转换_的机制来实现。
当 Lean 在期望某一类型的上下文中遇到另一类型的表达式时，它会先尝试对该表达式进行强制类型转换，然后才报告类型错误。
不同于 Java、C 和 Kotlin，强制类型转换可以通过定义类型类的实例来扩展。

# 字符串与路径
%%%
tag := "string-path-coercion"
file := "Strings-and-Paths"
%%%

在 {ref "handling-input"}[{lit}`feline` 的源代码]中，使用匿名构造子语法将 {moduleName}`String` 转换为 {moduleName}`FilePath`。
事实上，这并不是必需的：Lean 定义了从 {moduleName}`String` 到 {moduleName}`FilePath` 的强制类型转换，因此可以在期望路径的位置使用字符串。
尽管函数 {anchorTerm readFile}`IO.FS.readFile` 的类型是 {anchorTerm readFile}`System.FilePath → IO String`，下面的代码仍会被 Lean 接受：

```anchor fileDumper
def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trim
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f)
```
{moduleName}`String.trim` 会从字符串中移除开头和结尾的空白字符。
在 {anchorName fileDumper}`fileDumper` 的最后一行中，从 {moduleName}`String` 到 {moduleName}`FilePath` 的强制类型转换会自动转换 {anchorName fileDumper}`f`，因此不必写成 {lit}`IO.FS.readFile ⟨f⟩`。

# 正数
%%%
tag := "positive-number-coercion"
file := "Positive-Numbers"
%%%

每个正数都对应一个自然数。
先前定义的函数 {anchorName posToNat}`Pos.toNat` 将一个 {moduleName}`Pos` 转换为相应的 {moduleName}`Nat`：

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
函数 {anchorName drop}`List.drop` 的类型为 {anchorTerm drop}`{α : Type} → Nat → List α → List α`，它会移除列表的一个前缀。
然而，将 {anchorName drop}`List.drop` 应用于一个 {moduleName}`Pos` 会导致类型错误：
```anchorTerm dropPos
[1, 2, 3, 4].drop (2 : Pos)
```
```anchorError dropPos
Application type mismatch: The argument
  2
has type
  Pos
but is expected to have type
  Nat
in the application
  List.drop 2
```
由于 {anchorName drop}`List.drop` 的作者没有将其做成类型类的方法，它不能通过定义新实例来被覆盖。

:::paragraph
类型类 {moduleName}`Coe` 描述了从一种类型强制类型转换到另一种类型的重载方式：

```anchor Coe
class Coe (α : Type) (β : Type) where
  coe : α → β
```
一个 {anchorTerm CoePosNat}`Coe Pos Nat` 实例就足以使先前的代码能够工作：

```anchor CoePosNat
instance : Coe Pos Nat where
  coe x := x.toNat
```
```anchor dropPosCoe
#eval [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo dropPosCoe
[3, 4]
```
使用 {kw}`#check` 会显示幕后所用实例搜索的结果：
```anchor checkDropPosCoe
#check [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo checkDropPosCoe
List.drop (Pos.toNat 2) [1, 2, 3, 4] : List Nat
```
:::

# 链接强制类型转换
%%%
tag := "chaining-coercions"
file := "Chaining-Coercions"
%%%

在搜索强制类型转换时，Lean 会尝试由一串较小的强制类型转换组装出一个强制类型转换。
例如，已经存在从 {anchorName chapterIntro}`Nat` 到 {anchorName chapterIntro}`Int` 的强制类型转换。
由于该实例与 {anchorTerm CoePosNat}`Coe Pos Nat` 实例相结合，下面的代码会被接受：

```anchor posInt
def oneInt : Int := Pos.one
```
此定义使用了两个强制类型转换：从 {anchorTerm CoePosNat}`Pos` 到 {anchorTerm CoePosNat}`Nat`，然后从 {anchorTerm CoePosNat}`Nat` 到 {anchorTerm chapterIntro}`Int`。

Lean 编译器不会因为存在循环强制类型转换而陷入停滞。
例如，即使两个类型 {anchorName CoercionCycle}`A` 和 {anchorName CoercionCycle}`B` 可以相互强制类型转换，它们的相互强制类型转换也可用于找到一条路径：

```anchor CoercionCycle
inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
```
请记住：双括号 {anchorTerm CoercionCycle}`()` 是构造子 {anchorName chapterIntro}`Unit.unit` 的简写。
用 {anchorTerm ReprB}`deriving instance Repr for B` 派生出一个 {anchorTerm ReprBTm}`Repr B` 实例之后，
```anchor coercedToBEval
#eval coercedToB
```
得到：
```anchorInfo coercedToBEval
B.b
```

:::paragraph
{anchorName CoeOption}`Option` 类型可以以类似于 C# 和 Kotlin 中可空类型的方式使用：{anchorName NEListGetHuh}`none` 构造子表示值的缺失。
Lean 标准库定义了一个从任意类型 {anchorName CoeOption}`α` 到 {anchorTerm CoeOption}`Option α` 的强制类型转换，它会将值包裹在 {anchorName CoeOption}`some` 中。
这使得选项类型可以以一种甚至更接近可空类型的方式使用，因为可以省略 {anchorName CoeOption}`some`。
例如，寻找列表中最后一个条目的函数 {anchorName lastHuh}`List.last?` 可以在返回值 {anchorName lastHuh}`x` 周围不写 {anchorName CoeOption}`some`：

```anchor lastHuh
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)
```
实例搜索会找到该强制类型转换，并插入一次对 {anchorName Coe}`coe` 的调用，从而将参数包装在 {anchorName CoeOption}`some` 中。
这些强制类型转换可以串联，因此嵌套使用 {anchorName CoeOption}`Option` 不需要嵌套的 {anchorName CoeOption}`some` 构造子：

```anchor perhapsPerhapsPerhaps
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"
```
:::

:::paragraph
只有当 Lean 遇到推断出的类型与程序其余部分施加的类型之间不匹配时，强制类型转换才会被自动激活。
在存在其他错误的情况下，强制类型转换不会被激活。
例如，如果错误是缺少实例，则不会使用强制类型转换：
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::

:::paragraph
可以通过手动指明 {moduleName}`OfNat` 所需使用的目标类型来绕过这一问题：

```anchor perhapsPerhapsPerhapsNat
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)
```
此外，还可以使用向上箭头手动插入强制类型转换：

```anchor perhapsPerhapsPerhapsNatUp
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)
```
在某些情况下，这可用于确保 Lean 找到正确的实例。
它还可以使程序员的意图更加清晰。
:::

# 非空列表与依值强制类型转换
%%%
tag := "CoeDep"
file := "Non-Empty-Lists-and-Dependent-Coercions"
%%%

当类型 {anchorName chapterIntro}`β` 中有一个值能够表示来自类型 {anchorName chapterIntro}`α` 的每个值时，{anchorTerm chapterIntro}`Coe α β` 的实例就是有意义的。
从 {moduleName}`Nat` 强制类型转换到 {moduleName}`Int` 是有意义的，因为类型 {moduleName}`Int` 包含所有自然数；但是，从 {moduleName}`Int` 到 {moduleName}`Nat` 的强制类型转换并不是一个好主意，因为 {moduleName}`Nat` 不包含负数。
类似地，从非空列表到普通列表的强制类型转换是有意义的，因为 {moduleName}`List` 类型能够表示每一个非空列表：

```anchor CoeNEList
instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs
```
这使得非空列表能够与整个 {moduleName}`List` API 一起使用。

另一方面，无法写出 {anchorTerm coeNope}`Coe (List α) (NonEmptyList α)` 的实例，因为不存在能够表示空列表的非空列表。
可以通过使用另一种版本的强制类型转换来绕过这一限制；这种转换称为_依值强制类型转换_。
当从一种类型强制转换到另一种类型的能力取决于正在被强制转换的具体值时，可以使用依值强制类型转换。
正如 {anchorName OfNat}`OfNat` 类型类将正在被重载的具体 {moduleName}`Nat` 作为参数一样，依值强制类型转换将正在被强制转换的值作为参数：

```anchor CoeDep
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β
```
这是一个只选择某些值的机会，可以通过对该值施加进一步的类型类约束，或直接写出某些构造子来实现。
例如，任何实际上非空的 {moduleName}`List` 都可以被强制类型转换为 {moduleName}`NonEmptyList`：

```anchor CoeDepListNEList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
```

# 强制转换到类型
%%%
tag := "CoeSort"
file := "Coercing-to-Types"
%%%

在数学中，常常有这样一种概念：它由一个集合以及该集合上配备的附加结构组成。
例如，一个幺半群是某个集合 $`S`、$`S` 的一个元素 $`s`，以及 $`S` 上的一个结合的二元运算，并且 $`s` 是该运算的左、右单位元。
$`S` 称为该幺半群的“载体集”。
自然数连同零和加法构成一个幺半群，因为加法满足结合律，并且把零加到任意数上都得到该数本身。
类似地，自然数连同一和乘法也构成一个幺半群。
幺半群在函数式编程中也被广泛使用：列表、空列表和追加运算构成一个幺半群，字符串、空字符串和字符串追加也构成一个幺半群：

```anchor Monoid
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }
```
给定一个幺半群，就可以编写 {anchorName firstFoldMap}`foldMap` 函数，使其在一次遍历中将列表中的各项转换为该幺半群的载体集中的元素，然后使用该幺半群的运算符将它们组合起来。
由于幺半群具有中性元，当列表为空时有一个自然的结果可以返回；又由于运算符满足结合律，该函数的客户不必关心递归函数是从左到右还是从右到左组合元素。

```anchor firstFoldMap
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

尽管一个幺半群由三项彼此独立的信息组成，但通常会直接用该幺半群的名称来指称它的集合。
通常不说“设 A 为一个幺半群，且设 _x_ 和 _y_ 为其载体集合的元素”，而是说“设 _A_ 为一个幺半群，且设 _x_ 和 _y_ 为 _A_ 的元素”。
这种做法可以通过在 Lean 中定义一种新的强制类型转换来编码，即从幺半群到其载体集合的强制类型转换。

{anchorName CoeMonoid}`CoeSort` 类与 {anchorName CoePosNat}`Coe` 类很相似，区别在于强制类型转换的目标必须是一个_sort_，即 {anchorTerm chapterIntro}`Type` 或 {anchorTerm chapterIntro}`Prop`。
Lean 中的术语_sort_指的是这些对其他类型进行分类的类型——{anchorTerm Coe}`Type` 对那些自身对数据进行分类的类型进行分类，而 {anchorTerm chapterIntro}`Prop` 对那些自身对其真值证据进行分类的命题进行分类。
正如发生类型不匹配时会检查 {anchorName CoePosNat}`Coe` 一样，当在预期为 sort 的上下文中提供了某个并非 sort 的对象时，会使用 {anchorName CoeMonoid}`CoeSort`。

从幺半群到其载体集合的强制类型转换会提取该载体：

```anchor CoeMonoid
instance : CoeSort Monoid Type where
  coe m := m.Carrier
```
有了这个强制类型转换，类型签名就不那么繁琐了：

```anchor foldMap
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

{anchorName CoeMonoid}`CoeSort` 的另一个有用示例用于弥合 {anchorName types}`Bool` 与 {anchorTerm chapterIntro}`Prop` 之间的差距。
正如在 {ref "equality-and-ordering"}[关于排序与相等性的章节]中所讨论的，Lean 的 {kw}`if` 表达式期望其条件是一个可判定命题，而不是 {anchorName types}`Bool`。
然而，程序通常需要能够基于布尔值进行分支。
Lean 标准库没有设置两种 {kw}`if` 表达式，而是定义了一个从 {anchorName types}`Bool` 到命题的强制类型转换，该命题断言所讨论的 {anchorName types}`Bool` 等于 {anchorName types}`true`：

```anchor CoeBoolProp
instance : CoeSort Bool Prop where
  coe b := b = true
```
在这种情况下，所讨论的 sort 是 {anchorTerm chapterIntro}`Prop`，而不是 {anchorTerm chapterIntro}`Type`。

# 强制转换到函数
%%%
tag := "CoeFun"
file := "Coercing-to-Functions"
%%%

编程中经常出现的许多数据类型由一个函数以及关于该函数的一些额外信息组成。
例如，一个函数可能附带一个用于在日志中显示的名称，或者附带一些配置数据。
此外，类似于 {anchorName Monoid}`Monoid` 示例，将一个类型放入结构体的字段中，在存在多种方式来实现某个操作、并且需要比类型类所允许的更多手动控制的上下文中，可能是有意义的。
例如，JSON 序列化器所发出值的具体细节可能很重要，因为另一个应用程序期望某种特定格式。
有时，函数本身可能仅由配置数据推导出来。

名为 {anchorName CoeFun}`CoeFun` 的类型类可以把非函数类型的值转换为函数类型。
{anchorName CoeFun}`CoeFun` 有两个参数：第一个是其值应被转换为函数的类型，第二个是输出参数，用于精确决定目标函数类型。

```anchor CoeFun
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
```
第二个参数本身是一个计算类型的函数。
在 Lean 中，类型是一等对象，可以像其他任何东西一样传递给函数或由函数返回。

例如，一个向其参数加上某个常量的函数，可以表示为对待加数量的包装，而不必定义一个实际的函数：

```anchor Adder
structure Adder where
  howMuch : Nat
```
一个将其参数加五的函数，在 {anchorName Adder}`howMuch` 字段中有一个 {anchorTerm add5}`5`：

```anchor add5
def add5 : Adder := ⟨5⟩
```
此 {anchorName Adder}`Adder` 类型不是函数，将它应用于一个参数会导致错误：
```anchor add5notfun
#eval add5 3
```
```anchorError add5notfun
Function expected at
  add5
but this term has type
  Adder

Note: Expected a function because this term is being applied to the argument
  3
```
定义一个 {anchorName CoeFunAdder}`CoeFun` 实例会使 Lean 将加法器转换为类型为 {anchorTerm CoeFunAdder}`Nat → Nat` 的函数：

```anchor CoeFunAdder
instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)
```
```anchor add53
#eval add5 3
```
```anchorInfo add53
8
```
因为所有 {anchorName CoeFunAdder}`Adder` 都应被转换为 {anchorTerm CoeFunAdder}`Nat → Nat` 函数，所以传给 {anchorName CoeFunAdder}`CoeFun` 的第二个参数的实参被忽略了。

:::paragraph
当需要由值本身来确定正确的函数类型时，{anchorName CoeFunAdder}`CoeFun` 的第二个参数就不再被忽略。
例如，给定如下 JSON 值表示：

```anchor JSON
inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
```
JSON 序列化器是一个结构，它记录自身知道如何序列化的类型，并同时包含序列化代码本身：

```anchor Serializer
structure Serializer where
  Contents : Type
  serialize : Contents → JSON
```
字符串的序列化器只需将给定字符串包装在 {anchorName StrSer}`JSON.string` 构造子中：

```anchor StrSer
def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }
```
:::

:::paragraph
将 JSON 序列化器视为对其参数进行序列化的函数，需要提取可序列化数据的内部类型：

```anchor CoeFunSer
instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize
```
给定此实例，序列化器可以直接应用于一个参数：

```anchor buildResponse
def buildResponse (title : String) (R : Serializer)
    (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]
```
可以将序列化器直接传给 {anchorName buildResponseOut}`buildResponse`：
```anchor buildResponseOut
#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"
```
```anchorInfo buildResponseOut
JSON.object
  [("title", JSON.string "Functional Programming in Lean"),
   ("status", JSON.number 200.000000),
   ("record", JSON.string "Programming is fun!")]
```
:::

## 旁注：作为字符串的 JSON
%%%
tag := "json-string"
file := "Aside___-JSON-as-a-String"
%%%

当 JSON 被编码为 Lean 对象时，理解起来可能有些困难。
为了帮助确认序列化后的响应符合预期，编写一个从 {anchorName JSON}`JSON` 到 {anchorName dropDecimals}`String` 的简单转换器会很方便。
第一步是简化数字的显示。
{anchorName JSON}`JSON` 不区分整数和浮点数，并且类型 {anchorName JSON}`Float` 用于表示二者。
在 Lean 中，{anchorName chapterIntro}`Float.toString` 会包含若干尾随零：
```anchor fiveZeros
#eval (5 : Float).toString
```
```anchorInfo fiveZeros
"5.000000"
```
解决方法是编写一个小函数来整理显示形式：先删除所有尾随的零，然后删除尾随的小数点：

```anchor dropDecimals
def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString
```
有了此定义，{anchorTerm dropDecimalExample}`dropDecimals (5 : Float).toString` 产生 {anchorTerm dropDecimalExample}`5`，而 {anchorTerm dropDecimalExample2}`dropDecimals (5.2 : Float).toString` 产生 {anchorTerm dropDecimalExample2}`5.2`。

下一步是定义一个辅助函数，用于把一个字符串列表追加起来，并在它们之间插入分隔符：

```anchor Stringseparate
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))
```
此函数可用于处理 JSON 数组和对象中以逗号分隔的元素。
{anchorTerm sep2ex}`", ".separate ["1", "2"]` 产生 {anchorInfo sep2ex}`"1, 2"`，{anchorTerm sep1ex}`", ".separate ["1"]` 产生 {anchorInfo sep1ex}`"1"`，而 {anchorTerm sep0ex}`", ".separate []` 产生 {anchorInfo sep0ex}`""`。
在 Lean 标准库中，此函数称为 {anchorName chapterIntro}`String.intercalate`。

最后，JSON 字符串需要一个字符串转义过程，以便包含 {anchorTerm chapterIntro}`"Hello!"` 的 Lean 字符串能够作为 {anchorTerm escapeQuotes}`"\"Hello!\""` 输出。
幸运的是，Lean 编译器已经包含一个用于转义 JSON 字符串的内部函数，名为 {anchorName escapeQuotes}`Lean.Json.escape`。
要访问此函数，请将 {lit}`import Lean` 添加到文件开头。

从 {anchorName JSONasString}`JSON` 值生成字符串的函数被声明为 {kw}`partial`，因为 Lean 无法看出它会终止。
这是因为对 {anchorName JSONasString}`asString` 的递归调用出现在由 {anchorName chapterIntro}`List.map` 所应用的函数中，而这种递归模式复杂到足以使 Lean 无法看出这些递归调用实际上是在更小的值上执行的。
在一个只需要生成 JSON 字符串、而不需要对该过程进行数学推理的应用中，将该函数设为 {kw}`partial` 不太可能造成问题。

```anchor JSONasString
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"
```
有了这个定义，序列化的输出更易于阅读：
```anchor buildResponseStr
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
```
```anchorInfo buildResponseStr
"{\"title\": \"Functional Programming in Lean\", \"status\": 200, \"record\": \"Programming is fun!\"}"
```


# 你可能遇到的消息
%%%
tag := "coercion-messages"
file := "Messages-You-May-Meet"
%%%

自然数文本字面量通过 {anchorName OfNat}`OfNat` 类型类进行重载。
由于强制类型转换是在类型不匹配的情况下触发的，而不是在缺少实例的情况下触发的，因此某个类型缺少 {anchorName OfNat}`OfNat` 实例并不会导致应用从 {moduleName}`Nat` 出发的强制类型转换：
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

# 设计考量
%%%
tag := "coercion-design-considerations"
file := "Design-Considerations"
%%%

强制类型转换是一种强大的工具，应当负责任地使用。
一方面，它们可以使 API 自然地遵循所建模领域的日常规则。
这可能正是由手工转换函数构成的繁琐混乱与清晰程序之间的差别。
正如 Abelson 和 Sussman 在 _Structure and Interpretation of Computer Programs_（MIT Press，1996）的序言中所写，

> 程序必须为人们阅读而编写，只是顺带供机器执行。

强制类型转换若使用得当，是实现可读代码的一种有价值手段，而这样的代码可以作为与领域专家交流的基础。
然而，严重依赖强制类型转换的 API 有若干重要限制。
在你自己的库中使用强制类型转换之前，请仔细考虑这些限制。

首先，强制类型转换只会在有足够类型信息可供 Lean 知道所涉及的全部类型的上下文中被应用，因为强制类型转换的类型类中没有输出参数。这意味着，函数上的返回类型标注可能决定结果是类型错误还是成功应用强制类型转换。
例如，从非空列表到列表的强制类型转换使以下程序能够工作：

```anchor lastSpiderA
def lastSpider : Option String :=
  List.getLast? idahoSpiders
```
另一方面，如果省略类型标注，那么结果类型就是未知的，因此 Lean 无法找到该强制类型转换：
```anchor lastSpiderB
def lastSpider :=
  List.getLast? idahoSpiders
```
```anchorError lastSpiderB
Application type mismatch: The argument
  idahoSpiders
has type
  NonEmptyList String
but is expected to have type
  List ?m.3
in the application
  List.getLast? idahoSpiders
```
更一般地，当某个强制类型转换因某种原因未被应用时，用户会收到原始类型错误，这可能使强制类型转换链难以调试。

最后，在字段访问器记法的上下文中不会应用强制类型转换。
这意味着，需要被强制转换的表达式与不需要强制转换的表达式之间仍然存在重要差异，并且这一差异对于你的 API 用户是可见的。
