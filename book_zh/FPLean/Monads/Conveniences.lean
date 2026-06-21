import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Conveniences"

#doc (Manual) "额外便利" =>
%%%
tag := "monads-conveniences"
file := "Additional-Conveniences"
%%%

# 共享的参数类型
%%%
tag := "shared-argument-types"
file := "Shared-Argument-Types"
%%%

在定义一个接受多个相同类型参数的函数时，可以把这些参数都写在同一个冒号之前。
例如，

```anchor equalHuhOld
def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
可以写作

```anchor equalHuhNew
def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
当类型签名很大时，这尤其有用。

# 前导点记法
%%%
tag := "leading-dot-notation"
file := "Leading-Dot-Notation"
%%%

归纳类型的构造子位于命名空间中。
这允许多个相关的归纳类型使用相同的构造子名称，但也可能导致程序变得冗长。
在已知所讨论的归纳类型的上下文中，可以通过在构造子名称前加一个点来省略命名空间，Lean 会使用期望类型来解析构造子名称。
例如，镜像一棵二叉树的函数可以写作：

```anchor mirrorOld
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
```
省略命名空间会使它显著缩短，但代价是在不包含 Lean 编译器的上下文（例如代码审查工具）中，程序会更难阅读：

```anchor mirrorNew
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```

使用表达式的期望类型来消解命名空间歧义，也适用于构造子以外的名称。
如果 {anchorName BinTreeEmpty}`BinTree.empty` 被定义为创建 {anchorName BinTreeEmpty}`BinTree` 的另一种方式，那么它也可以与点记法一起使用：

```anchor BinTreeEmpty
def BinTree.empty : BinTree α := .leaf
```
```anchor emptyDot
#check (.empty : BinTree Nat)
```
```anchorInfo emptyDot
BinTree.empty : BinTree Nat
```

# 或模式
%%%
tag := "or-patterns"
file := "Or-Patterns"
%%%

在允许多个模式的上下文中，例如 {kw}`match` 表达式，多个模式可以共享其结果表达式。
表示星期几的数据类型 {anchorName Weekday}`Weekday`：

```anchor Weekday
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
```

可以使用模式匹配来检查某一天是否是周末：

```anchor isWeekendA
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false
```
这已经可以通过使用构造子的点记法来简化：

```anchor isWeekendB
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
```
由于两个周末模式具有相同的结果表达式（{anchorName isWeekendC}`true`），它们可以合并为一个：

```anchor isWeekendC
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
```
这还可以进一步简化为一个不命名参数的版本：

```anchor isWeekendD
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

在幕后，结果表达式只是被复制到每个模式中。
这意味着模式可以绑定变量，如下面这个例子所示：它从一个和类型中移除 {anchorName SumNames}`inl` 和 {anchorName SumNames}`inr` 构造子，而这两个构造子都包含同一类型的值：

```anchor condense
def condense : α ⊕ α → α
  | .inl x | .inr x => x
```
由于结果表达式会被复制，由模式绑定的变量不必具有相同的类型。
可以使用适用于多种类型的重载函数，来编写一个单一的结果表达式，使其适用于绑定不同类型变量的模式：

```anchor stringy
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"
```
在实践中，只有所有模式共享的变量才能在结果表达式中被引用，因为结果必须对每个模式都有意义。
在 {anchorName getTheNat}`getTheNat` 中，只有 {anchorName getTheNat}`n` 可以被访问；尝试使用 {anchorName getTheNat}`x` 或 {anchorName getTheNat}`y` 都会导致错误。

```anchor getTheNat
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n
```
试图在类似定义中访问 {anchorName getTheAlpha}`x` 会导致错误，因为第二个模式中没有可用的 {anchorName getTheAlpha}`x`：
```anchor getTheAlpha
def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, y) => x
```
```anchorError getTheAlpha
Unknown identifier `x`
```

结果表达式本质上被复制粘贴到模式匹配的每个分支这一事实，可能导致一些令人意外的行为。
例如，以下定义是可接受的，因为结果表达式的 {anchorName SumNames}`inr` 版本引用的是 {anchorName getTheString}`str` 的全局定义：

```anchor getTheString
def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str
```
在两个构造子上调用此函数会揭示这种令人困惑的行为。
在第一种情况下，需要一个类型标注来告诉 Lean {anchorName getTheString}`β` 应当是什么类型：
```anchor getOne
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
```
```anchorInfo getOne
"twenty"
```
在第二种情况下，使用全局定义：
```anchor getTwo
#eval getTheString (.inr (20, "twenty"))
```
```anchorInfo getTwo
"Some string"
```

使用或模式可以极大地简化某些定义并提高其清晰度，如 {anchorName isWeekendD}`Weekday.isWeekend` 所示。
由于存在产生混淆行为的可能性，使用它们时应当谨慎，尤其是在涉及多种类型的变量或互不相交的变量集合时。
