import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true


#doc (Manual) "其他便利功能" =>
%%%
tag := "type-class-conveniences"
%%%

# 实例的构造函数语法
%%%
tag := "instance-constructor-syntax"
%%%

在幕后，类型类都是一些结构体类型，实例都是那些类型的值。唯一的区别是 Lean 存储关于类型类的额外信息，例如哪些参数是输出参数，和记录要被搜索的实例。
虽然具有结构类型的值通常使用 {lit}`⟨...⟩` 语法或大括号和字段来定义，而实例通常使用 {kw}`where` 来定义，但这两种语法都适用于这两种定义。

:::paragraph
例如，一个林业应用程序可能会这样表示树木：

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
所有三种语法都是等效的。
:::

:::paragraph
同样，类型类实例可以使用所有三种语法来定义：

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

{kw}`where` 语法通常用于实例，而结构使用大括号语法或 {kw}`where` 语法。
当强调结构类型非常像一个元组，其中字段恰好被命名，但名称目前不重要时，{lit}`⟨...⟩` 语法可能很有用。
然而，有些情况用其他方式可能才是合理的。具体而言，一个库可能提供一个构建实例值的函数。
在实例声明中将对此函数的调用放在 {lit}`:=` 之后是使用此类函数的最简单方法。
:::

# {kw}`example`
%%%
tag := "example-command"
%%%

当用 Lean 代码做实验时，定义可能比 {kw}`#eval` 或 {kw}`#check` 命令更方便使用。
首先，定义不会产生任何输出，这可以让读者的注意力集中在最有趣的输出上。第二，从一个类型签名开始一个 Lean 程序是最简单的方式，这也会使 Lean 能够提供更多的协助和更好的错误信息。
另一方面，{kw}`#eval` 和 {kw}`#check` 在 Lean 能够从提供的表达式中确定类型的上下文中最好用。
第三，{kw}`#eval` 不能用于其类型没有 {moduleName}`ToString` 或 {moduleName}`Repr` 实例的表达式，例如函数。
最后，多步 {kw}`do` 块、{kw}`let`-表达式以及其他占用多行的语法形式在 {kw}`#eval` 或 {kw}`#check` 中有时候是一个需要多层括号区分优先级的长表达式，在这里面插入类型标注会很难读。

:::paragraph
为了绕开这些问题，Lean 支持源码中例子的显式类型推断。一个例子就是一个无名的定义。
例如，可以这样写一个在哥本本哈根绿地中常见的鸟类的非空列表：

```anchor birdExample
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }
```
:::

:::paragraph
示例可以通过接受参数来定义函数：

```anchor commAdd
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
```
这会在幕后创建一个函数，这个函数没有名字，也不能被调用。此外，这可以用来检查某库中的函数是否可以在任意的或一些类型的未知值上正常工作。
在源码中，{kw}`example` 声明很适合与解释概念的注释搭配使用。
:::
