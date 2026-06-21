import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true


#doc (Manual) "额外的便利语法" =>
%%%
tag := "type-class-conveniences"
file := "Additional-Conveniences"
%%%

# 实例的构造子语法
%%%
tag := "instance-constructor-syntax"
file := "Constructor-Syntax-for-Instances"
%%%

在幕后，类型类是结构类型，而实例是这些类型的值。
二者唯一的区别是，Lean 会存储关于类型类的额外信息，例如哪些参数是输出参数，并且实例会被注册以供搜索。
虽然具有结构类型的值通常使用 {lit}`⟨...⟩` 语法，或使用花括号和字段来定义，而实例通常使用 {kw}`where` 来定义，但这两种语法都适用于这两类定义。

:::paragraph
例如，一个林业应用程序可以如下表示树木：

```anchor trees
structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]
```
这三种语法都是等价的。
:::

:::paragraph
类似地，类型类实例可以用全部三种语法来定义：

```anchor Display
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName
```

{kw}`where` 语法通常用于实例，而结构则使用花括号语法或 {kw}`where` 语法。
当需要强调某个结构类型非常类似于一个元组，只是其字段恰好带有名称、而这些名称在当前并不重要时，{lit}`⟨...⟩` 语法会很有用。
然而，在某些情况下，使用其他替代方式也是合理的。
特别地，库可能会提供一个构造实例值的函数。
在实例声明中的 {lit}`:=` 之后放置对该函数的调用，是使用这种函数的最简单方式。
:::

# 示例
%%%
tag := "example-command"
file := "Examples"
%%%

在试验 Lean 代码时，定义可能比 {kw}`#eval` 或 {kw}`#check` 命令更便于使用。
首先，定义不会产生任何输出，这有助于使读者的注意力集中在最有意思的输出上。
其次，编写大多数 Lean 程序时，最容易的做法是从类型签名开始，让 Lean 在编写程序本身时提供更多帮助和更好的错误消息。
另一方面，{kw}`#eval` 和 {kw}`#check` 在 Lean 能够根据所给表达式确定类型的上下文中最容易使用。
第三，{kw}`#eval` 不能用于其类型没有 {moduleName}`ToString` 或 {moduleName}`Repr` 实例的表达式，例如函数。
最后，多步骤的 {kw}`do` 块、{kw}`let` 表达式以及其他占多行的语法形式，若要在 {kw}`#eval` 或 {kw}`#check` 中带类型标注来书写，会尤其困难，原因只是所需的括号化可能难以预料。

:::paragraph
为绕过这些问题，Lean 支持在源文件中显式给出示例。
示例类似于没有名称的定义。
例如，一个由哥本哈根绿地中常见鸟类组成的非空列表可以写作：

```anchor birdExample
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }
```
:::

:::paragraph
示例可以通过接受实参来定义函数：

```anchor commAdd
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
```
虽然这会在幕后创建一个函数，但这个函数没有名称，也不能被调用。
尽管如此，这对于展示一个库如何与某个给定类型的任意值或未知值一起使用是有用的。
在源文件中，{kw}`example` 声明最好与注释配合使用，这些注释说明该示例如何阐明库中的概念。
:::
