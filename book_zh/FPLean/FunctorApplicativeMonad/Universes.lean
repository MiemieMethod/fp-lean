import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Universes"

#doc (Manual) "宇宙" =>
%%%
tag := "universe-levels"
%%%

为了简化，本书到目前为止略去了 Lean 的一个重要特性：_宇宙 (Universes)_。
宇宙是一种对其他类型进行分类的类型。
其中两个是我们熟悉的：{anchorTerm TypeType}`Type` 和 {anchorTerm PropType}`Prop`。
{anchorTerm SomeTypes}`Type` 分类了普通类型，例如 {anchorName SomeTypes}`Nat`、{anchorTerm SomeTypes}`String`、{anchorTerm SomeTypes}`Int → String × Char` 和 {anchorTerm SomeTypes}`IO Unit`。
{anchorTerm PropType}`Prop` 分类了可能为真或假的命题，例如 {anchorTerm SomeTypes}`"nisse" = "elf"` 或 {anchorTerm SomeTypes}`3 > 2`。
{anchorTerm PropType}`Prop` 的类型是 {anchorTerm SomeTypes}`Type`：
```anchor PropType
#check Prop
```
```anchorInfo PropType
Prop : Type
```

出于技术原因，我们需要比这两个更多的宇宙。
具体而言，{anchorTerm SomeTypes}`Type` 本身不能是一个 {anchorTerm SomeTypes}`Type`。
这会导致逻辑悖论的产生，并削弱 Lean 作为定理证明器的实用性。

对此的正式论证被称为 _吉拉德悖论 (Girard's Paradox)_。
它与一个更著名的悖论有关，称为 _罗素悖论 (Russell's Paradox)_，该悖论用于展示早期版本的集合论是不一致的。
在这些集合论中，一个集合可以通过一个属性来定义。
例如，所有红色事物的集合，所有水果的集合，所有自然数的集合，甚至所有集合的集合。
给定一个集合，可以询问一个给定的元素是否被包含在其中。
例如，一只蓝色的鸟不会被包含在所有红色事物的集合中，但所有红色事物的集合被包含在所有集合的集合中。
实际上，所有集合的集合甚至包含其自身。

那么，所有不包含自身的集合的集合呢？
它包含所有红色事物的集合，因为所有红色事物的集合本身并不是红色的。
它不包含所有集合的集合，因为所有集合的集合包含自身。
但它是否包含自身呢？
如果它包含自身，那么它就不能包含自身。
但如果它不包含自身，那么它就必须包含自身。

这是一个矛盾，表明了初始的假设存在问题。
具体而言，允许通过提供任意属性来构造集合的做法过于强大。
集合论的后续版本限制了集合的构造以消除这种悖论。

在那些可以将类型 {anchorTerm SomeTypes}`Type` 分配给 {anchorTerm SomeTypes}`Type` 的依赖类型理论的版本中，可以构建一个相关的悖论。
为了确保 Lean 具有自洽的逻辑基础并且能够被用作数学工具，{anchorTerm SomeTypes}`Type` 需要有其他类型。
这个类型称为 {anchorTerm SomeTypes}`Type 1`：
```anchor TypeType
#check Type
```
```anchorInfo TypeType
Type : Type 1
```
类似地，{anchorTerm Type1Type}`Type 1` 是一个 {anchorTerm Type1Type}`Type 2`，
{anchorTerm Type2Type}`Type 2` 是一个 {anchorTerm Type2Type}`Type 3`，
{anchorTerm Type3Type}`Type 3` 是一个 {anchorTerm Type3Type}`Type 4`，等等。

函数类型占据了可以同时包含参数类型和返回类型的最小宇宙。
这意味着 {anchorTerm NatNatType}`Nat → Nat` 是一个 {anchorTerm NatNatType}`Type`，{anchorTerm Fun00Type}`Type → Type` 是一个 {anchorTerm Fun00Type}`Type 1`，而 {anchorTerm Fun12Type}`Type 3` 是一个 {anchorTerm Fun12Type}`Type 1 → Type 2`。

这个规则有一个例外。
如果一个函数的返回类型是 {anchorTerm PropType}`Prop`，那么即使参数在更大的宇宙中，例如 {anchorTerm SomeTypes}`Type` 或甚至 {anchorTerm SomeTypes}`Type 1`，整个函数类型也在 {anchorTerm PropType}`Prop` 中。
具体而言，这意味着具有普通类型的值的谓词在 {anchorTerm PropType}`Prop` 中。
例如，类型 {anchorTerm FunPropType}`(n : Nat) → n = n + 0` 表示了从一个 {anchorTerm SomeTypes}`Nat` 到它等于自身加零的证据的函数。
尽管 {anchorTerm SomeTypes}`Nat` 在 {anchorTerm SomeTypes}`Type` 中，根据这个规则，这个函数类型在 {anchorTerm FunPropType}`Prop` 中。
同样，尽管 {anchorTerm SomeTypes}`Type` 在 {anchorTerm SomeTypes}`Type 1` 中，函数类型 {anchorTerm FunTypePropType}`Type → 2 + 2 = 4` 仍在 {anchorTerm FunTypePropType}`Prop` 中。

# 用户定义类型
%%%
tag := "inductive-type-universes"
%%%

结构体和归纳数据类型可以声明为存在于特定的宇宙中。
Lean 随后会检查每个数据类型是否通过位于足够大的宇宙中来避免悖论，从而防止它包含其自身的类型。
例如，在以下声明中，{anchorName MyList1}`MyList` 被声明为驻留在 {anchorTerm SomeTypes}`Type` 中，而它的类型参数 {anchorName MyList1}`α` 也是如此：

```anchor MyList1
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
{anchorTerm MyList1Type}`MyList` 本身是一个 {anchorTerm MyList1Type}`Type → Type`。
这意味着它不能用于包含实际类型，因为那样的话它的参数将会是 {anchorTerm SomeTypes}`Type`，也就是一个 {anchorTerm SomeTypes}`Type 1`：
```anchor myListNat1Err
def myListOfNat : MyList Type :=
  .cons Nat .nil
```
```anchorError myListNat1Err
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  MyList Type
```

更新 {anchorName MyList2}`MyList` 使其参数为一个 {anchorTerm MyList2}`Type 1`，这会导致该定义被 Lean 拒绝：
```anchor MyList2
inductive MyList (α : Type 1) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
```anchorError MyList2
Invalid universe level in constructor `MyList.cons`: Parameter has type
  α
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```
发生此错误的原因是，类型为 {anchorName MyList2}`α` 的 {anchorTerm MyList2}`cons` 的参数来自一个比 {anchorName MyList2}`MyList` 更大的宇宙。
将 {anchorName MyList2}`MyList` 本身置于 {anchorTerm SomeTypes}`Type 1` 中可以解决这个问题，但代价是 {anchorName MyList2}`MyList` 本身在需要 {anchorTerm SomeTypes}`Type` 的内容中变得不便使用。

决定某种数据类型是否被允许的具体规则有些复杂。
通常来说，最简单的方法是，从其最大的参数所属的宇宙与自身所属的宇宙相同的数据类型开始。
然后，如果 Lean 拒绝了该定义，那就将其层级增加一级，这通常会奏效。

# 宇宙多态
%%%
tag := "universe-polymorphism"
%%%

在特定的宇宙中定义一个数据类型可能会导致代码重复。
将 {anchorName MyList1}`MyList` 置于 {anchorTerm MyList1Type}`Type → Type` 中意味着它不能被用于实际的类型列表。
将它放在 {anchorTerm MyList15Type}`Type 1 → Type 1` 内意味着它不能用于类型列表的列表。
与其复制粘贴数据类型以在 {anchorTerm SomeTypes}`Type`、{anchorTerm SomeTypes}`Type 1`、{anchorTerm Type2Type}`Type 2` 等中创建不同版本，不如使用一种称为 _宇宙多态_ 的特性来编写单个可以在任意这些宇宙中实例化的定义。

普通的多态类型在定义中使用变量来表示类型。
这使得 Lean 可以以不同的方式填充这些变量，从而使这些定义可以与各种类型一起使用。
同样，宇宙多态性允许变量在定义中表示宇宙，使得 Lean 可以以不同的方式去填充它们，以便可以用于各种宇宙。
正如类型参数通常用希腊字母命名一样，宇宙参数通常命名为 {lit}`u`、{lit}`v` 和 {lit}`w`。

{anchorName MyList3}`MyList` 的这个定义没有指定特定的宇宙层级，而是使用变量 {anchorTerm MyList3}`u` 来表示任意层级。
如果最终的数据类型与 {anchorTerm SomeTypes}`Type` 一起使用，那么 {anchorTerm MyList3}`u` 是 {lit}`0`；如果与 {anchorTerm Fun12Type}`Type 3` 一起使用，那么 {anchorTerm MyList3}`u` 是 {lit}`3`：

```anchor MyList3
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

通过这个定义，{anchorName MyList3}`MyList` 的相同定义可以用于包含实际的自然数以及自然数类型本身：

```anchor myListOfNat3
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
```
它甚至可以包含其自身：

```anchor myListOfList3
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
```

这似乎使得写出一个逻辑悖论成为可能。
毕竟，宇宙系统的全部意义在于排除自指类型。
然而，在幕后，每次出现 {anchorName MyList3}`MyList` 时都会提供一个宇宙层级的参数。
本质上，{anchorName MyList3}`MyList` 的宇宙多态定义在每个层级创建了数据类型的一个 _副本_，层级参数选择要使用哪个副本。
这些层级参数使用一个点和大括号书写，例如 {anchorTerm MyListDotZero}`MyList.{0} : Type → Type`，{anchorTerm MyListDotOne}`MyList.{1} : Type 1 → Type 1`，和 {anchorTerm MyListDotTwo}`MyList.{2} : Type 2 → Type 2`。

明确地写出所有层次，之前的例子变成了：

```anchor myListOfList3Expl
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
```

当一个宇宙多态定义接受了多个类型作为参数时，最好给每个参数赋予其自己的层级变量，以实现最大的灵活性。
例如，一个带有单个层级参数的 {anchorName SumNoMax}`Sum` 版本可以写成如下形式：

```anchor SumNoMax
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
这个定义可以在多个层级上使用：

```anchor SumPoly
def stringOrNat : Sum String Nat := .inl "hello"

def typeOrType : Sum Type Type := .inr Nat
```
但是，它要求两个参数位于同一个宇宙内：
```anchor stringOrTypeLevels
def stringOrType : Sum String Type := .inr Nat
```
```anchorError stringOrTypeLevels
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Sum String Type
```

通过为两个类型参数的宇宙层级使用不同的变量，并声明生成的数据类型是两者中最大的层级，这可以使该数据类型更加灵活：

```anchor SumMax
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
这使得 {anchorName SumMax}`Sum` 可以与来自不同宇宙的参数一起使用：

```anchor stringOrTypeSum
def stringOrType : Sum String Type := .inr Nat
```

在 Lean 需要宇宙层级的位置，以下任意一种都是被允许的：
 * 具体的层级，如 {lit}`0` 或 {lit}`1`
 * 代表层级的变量，如 {anchorTerm SumMax}`u` 或 {anchorTerm SumMax}`v`
 * 两个层级的最大值，写作 {anchorTerm SumMax}`max` 应用于这些层级
 * 层级增加，写作 {anchorTerm someTrueProps}`+ 1`

## 编写宇宙多态定义
%%%
tag := none
%%%

到目前为止，本书中定义的每种数据类型都在 {anchorTerm SomeTypes}`Type` 中，即最小的数据宇宙。
在展示 Lean 标准库中的多态数据类型时，例如 {anchorName SomeTypes}`List` 和 {anchorName SumMax}`Sum`，本书创建了它们的非宇宙多态的版本。
实际的版本使用了宇宙多态性来实现类型层级和非类型层级程序之间的代码复用。

在编写宇宙多态类型时，有一些通用的指导准则需要遵守。
首先，独立的类型参数应具有不同的宇宙变量，这使得多态定义能够与更多种类的参数一起使用，从而增加代码复用的可能性。
其次，整个类型本身通常要么位于所有宇宙变量的最大值，要么位于比这个最大值大一的层级。
先尝试使用两者中较小的那个。
最后，最好将新类型放在一个尽可能小的宇宙中，这使得它在其他内容中可以更灵活地使用。
非多态类型，如 {anchorTerm SomeTypes}`Nat` 和 {anchorName SomeTypes}`String`，可以直接放在 {anchorTerm Type0Type}`Type 0` 中。

## {anchorTerm PropType}`Prop` 和多态
%%%
tag := none
%%%


就像 {anchorTerm SomeTypes}`Type`、{anchorTerm SomeTypes}`Type 1` 等描述了对程序和数据进行分类的类型一样，{anchorTerm PropType}`Prop` 则用于对逻辑命题进行分类。
{anchorTerm PropType}`Prop` 中的类型描述了什么可以作为令人信服的证据以证明一个陈述的真。
命题在许多方面与普通类型相似：它们可以被归纳地声明，它们可以有构造子，并且函数也可以将命题作为参数。
然而，与数据类型不同的是，通常来说，为证明陈述的真实性所提供的 _那个_ 证据的具体内容并不重要，重要的是提供了 _那个_ 证据。
另一方面，程序不仅要返回一个 {anchorTerm SomeTypes}`Nat`，而且要返回 _正确的_ {anchorTerm SomeTypes}`Nat`，这一点非常重要。

{anchorTerm PropType}`Prop` 位于宇宙层级体系的底部，且 {anchorTerm PropType}`Prop` 的类型是 {anchorTerm SomeTypes}`Type`。
这意味着 {anchorTerm PropType}`Prop` 适合作为 {anchorName SomeTypes}`List` 的一个参数，原因和 {anchorTerm SomeTypes}`Nat` 一样。
命题列表的类型是 {anchorTerm SomeTypes}`List Prop`：

```anchor someTrueProps
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```
显式地填写宇宙参数表明了 {anchorTerm PropType}`Prop` 是一个 {anchorTerm SomeTypes}`Type`：

```anchor someTruePropsExp
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```

在幕后，{anchorTerm PropType}`Prop` 和 {anchorTerm SomeTypes}`Type` 被统一到一个称为 {anchorTerm SomeTypes}`Sort` 的层级体系中。
{anchorTerm PropType}`Prop` 与 {anchorTerm sorts}`Sort 0` 相同，{anchorTerm Type0Type}`Type 0` 是 {anchorTerm sorts}`Sort 1`，{anchorTerm SomeTypes}`Type 1` 是 {anchorTerm sorts}`Sort 2`，依此类推。
实际上，{anchorTerm sorts}`Type u` 就是 {anchorTerm sorts}`Sort (u+1)`。
在使用 Lean 编写程序时，这通常并不相关，但它可能有时会出现在错误消息中，并解释 {anchorName sorts}`CoeSort` 类的名称。
此外，将 {anchorTerm PropType}`Prop` 作为 {anchorTerm sorts}`Sort 0` 可以使得一个额外的宇宙运算符变得有用。
宇宙级别 {lit}`imax u v` 在 {anchorTerm sorts}`v` 为 {lit}`0` 时为 {lit}`0`，否则为 {anchorTerm sorts}`u` 或 {anchorTerm sorts}`v` 中较大的那个。
结合 {anchorTerm sorts}`Sort`，这使得在编写代码时可以使用一个特殊规则，该规则允许返回 {anchorTerm PropType}`Prop` 的函数在 {anchorTerm PropType}`Prop` 和 {anchorTerm SomeTypes}`Type` 宇宙之间尽可能地具有可移植性。

# 多态的实际应用
%%%
tag := none
%%%

在本书的其余部分，多态数据类型、结构体和类的定义将使用宇宙多态性，以便与 Lean 的标准库保持一致。
这将使 {moduleName}`Functor`、{anchorName next}`Applicative` 和 {anchorName next}`Monad` 类的完整展示与它们的实际定义完全一致。
