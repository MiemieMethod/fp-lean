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
file := "Universes"
%%%

为简明起见，本书到目前为止略过了 Lean 的一个重要特性：_宇宙_。
宇宙是一种对其他类型进行分类的类型。
其中两个是大家熟悉的：{anchorTerm TypeType}`Type` 和 {anchorTerm PropType}`Prop`。
{anchorTerm SomeTypes}`Type` 对普通类型进行分类，例如 {anchorName SomeTypes}`Nat`、{anchorTerm SomeTypes}`String`、{anchorTerm SomeTypes}`Int → String × Char` 和 {anchorTerm SomeTypes}`IO Unit`。
{anchorTerm PropType}`Prop` 对可能为真或为假的命题进行分类，例如 {anchorTerm SomeTypes}`"nisse" = "elf"` 或 {anchorTerm SomeTypes}`3 > 2`。
{anchorTerm PropType}`Prop` 的类型是 {anchorTerm SomeTypes}`Type`：
```anchor PropType
#check Prop
```
```anchorInfo PropType
Prop : Type
```

出于技术原因，需要比这两个更多的宇宙。
特别地，{anchorTerm SomeTypes}`Type` 本身不能是一个 {anchorTerm SomeTypes}`Type`。
否则将允许构造出逻辑悖论，并削弱 Lean 作为定理证明器的有用性。

对此的形式化论证称为 _Girard's Paradox_。
它与一个更广为人知、称为 _Russell's Paradox_ 的悖论相关；后者曾被用来说明早期版本的集合论是不一致的。
在这些集合论中，可以用一个性质来定义集合。
例如，可以有所有红色事物的集合、所有水果的集合、所有自然数的集合，甚至所有集合的集合。
给定一个集合，可以询问某个给定元素是否包含在其中。
例如，一只蓝知更鸟不包含在所有红色事物的集合中，但所有红色事物的集合包含在所有集合的集合中。
事实上，所有集合的集合甚至包含它自身。

那么，不包含自身的所有集合所组成的集合又如何呢？
它包含所有红色事物所组成的集合，因为所有红色事物所组成的集合本身并不是红色的。
它不包含所有集合所组成的集合，因为所有集合所组成的集合包含自身。
但是它包含自身吗？
如果它包含自身，那么它就不能包含自身。
但如果它不包含自身，那么它就必须包含自身。

这是一个矛盾，表明初始假设中有某些内容是错误的。
特别地，允许通过给出任意性质来构造集合过于强大。
后来的集合论版本限制了集合的形成方式，以排除该悖论。

在某些将类型 {anchorTerm SomeTypes}`Type` 赋给 {anchorTerm SomeTypes}`Type` 的依值类型论版本中，可以构造出一个相关的悖论。
为了确保 Lean 具有一致的逻辑基础，并能够作为数学工具使用，{anchorTerm SomeTypes}`Type` 需要具有某个其他类型。
这个类型称为 {anchorTerm SomeTypes}`Type 1`：
```anchor TypeType
#check Type
```
```anchorInfo TypeType
Type : Type 1
```
类似地，{anchorTerm Type1Type}`Type 1` 是一个 {anchorTerm Type1Type}`Type 2`，
{anchorTerm Type2Type}`Type 2` 是一个 {anchorTerm Type2Type}`Type 3`，
{anchorTerm Type3Type}`Type 3` 是一个 {anchorTerm Type3Type}`Type 4`，依此类推。

函数类型位于能够同时容纳参数类型和返回类型的最小宇宙中。
这意味着 {anchorTerm NatNatType}`Nat → Nat` 是一个 {anchorTerm NatNatType}`Type`，{anchorTerm Fun00Type}`Type → Type` 是一个 {anchorTerm Fun00Type}`Type 1`，而 {anchorTerm Fun12Type}`Type 3` 是一个 {anchorTerm Fun12Type}`Type 1 → Type 2`。

这条规则有一个例外。
如果一个函数的返回类型是 {anchorTerm PropType}`Prop`，那么整个函数类型位于 {anchorTerm PropType}`Prop` 中，即使其参数位于诸如 {anchorTerm SomeTypes}`Type` 甚至 {anchorTerm SomeTypes}`Type 1` 这样更大的宇宙中。
特别地，这意味着关于具有普通类型的值的谓词位于 {anchorTerm PropType}`Prop` 中。
例如，类型 {anchorTerm FunPropType}`(n : Nat) → n = n + 0` 表示一个从 {anchorTerm SomeTypes}`Nat` 到“它等于它自身加零”的证据的函数。
尽管 {anchorTerm SomeTypes}`Nat` 位于 {anchorTerm SomeTypes}`Type` 中，由于这条规则，该函数类型位于 {anchorTerm FunPropType}`Prop` 中。
类似地，尽管 {anchorTerm SomeTypes}`Type` 位于 {anchorTerm SomeTypes}`Type 1` 中，函数类型 {anchorTerm FunTypePropType}`Type → 2 + 2 = 4` 仍然位于 {anchorTerm FunTypePropType}`Prop` 中。

# 用户定义的类型
%%%
tag := "inductive-type-universes"
file := "User-Defined-Types"
%%%

结构和归纳数据类型可以被声明为居于特定宇宙中。
随后 Lean 会检查每个数据类型是否处在足够大的宇宙中，以防止它包含自己的类型，从而避免悖论。
例如，在下面的声明中，{anchorName MyList1}`MyList` 被声明为位于 {anchorTerm SomeTypes}`Type` 中，其类型参数 {anchorName MyList1}`α` 也是如此：

```anchor MyList1
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
{anchorTerm MyList1Type}`MyList` 本身是一个 {anchorTerm MyList1Type}`Type → Type`。
这意味着它不能用于包含实际类型，因为那样它的实参就会是 {anchorTerm SomeTypes}`Type`，而 {anchorTerm SomeTypes}`Type` 是一个 {anchorTerm SomeTypes}`Type 1`：
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

将 {anchorName MyList2}`MyList` 更新为使其参数为一个 {anchorTerm MyList2}`Type 1`，会得到一个被 Lean 拒绝的定义：
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
出现这个错误，是因为传给 {anchorTerm MyList2}`cons` 的、类型为 {anchorName MyList2}`α` 的参数来自比 {anchorName MyList2}`MyList` 更大的宇宙。
将 {anchorName MyList2}`MyList` 本身放入 {anchorTerm SomeTypes}`Type 1` 可以解决这个问题，但代价是 {anchorName MyList2}`MyList` 现在自身在期望 {anchorTerm SomeTypes}`Type` 的上下文中使用起来并不方便。

支配某个数据类型是否被允许的具体规则有些复杂。
一般而言，最容易的做法是先让该数据类型与其各参数中最大的宇宙处于同一宇宙。
然后，如果 Lean 拒绝该定义，就将其层级增加一，这通常会通过。

# 宇宙多态
%%%
tag := "universe-polymorphism"
file := "Universe-Polymorphism"
%%%

在某个特定宇宙中定义数据类型可能导致代码重复。
将 {anchorName MyList1}`MyList` 放在 {anchorTerm MyList1Type}`Type → Type` 中意味着它不能用于真正的类型列表。
将它放在 {anchorTerm MyList15Type}`Type 1 → Type 1` 中意味着它不能用于类型列表的列表。
与其通过复制粘贴该数据类型来创建 {anchorTerm SomeTypes}`Type`、{anchorTerm SomeTypes}`Type 1`、{anchorTerm Type2Type}`Type 2` 等版本，不如使用称为_宇宙多态_的特性来编写一个单一定义，使其可以在这些宇宙中的任意一个中实例化。

普通多态类型在定义中使用变量来代表类型。
这允许 Lean 以不同方式填充这些变量，从而使这些定义能够用于多种类型。
类似地，宇宙多态允许变量在定义中代表宇宙，使 Lean 能够以不同方式填充它们，从而使它们能够用于多种宇宙。
正如类型实参按惯例用希腊字母命名一样，宇宙实参按惯例命名为 {lit}`u`、{lit}`v` 和 {lit}`w`。

这个 {anchorName MyList3}`MyList` 定义并不指定某个特定的宇宙层级，而是使用变量 {anchorTerm MyList3}`u` 来代表任意层级。
如果所得的数据类型与 {anchorTerm SomeTypes}`Type` 一起使用，那么 {anchorTerm MyList3}`u` 就是 {lit}`0`；如果它与 {anchorTerm Fun12Type}`Type 3` 一起使用，那么 {anchorTerm MyList3}`u` 就是 {lit}`3`：

```anchor MyList3
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

有了这个定义，同一个 {anchorName MyList3}`MyList` 定义既可以用于包含实际的自然数，也可以用于包含自然数类型本身：

```anchor myListOfNat3
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
```
它甚至可以包含自身：

```anchor myListOfList3
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
```

看起来，这似乎会使写出逻辑悖论成为可能。
毕竟，宇宙系统的全部目的正是排除自引用类型。
然而，在幕后，{anchorName MyList3}`MyList` 的每一次出现都会被提供一个宇宙层级参数。
本质上，{anchorName MyList3}`MyList` 的宇宙多态定义在每个层级上都创建了该数据类型的一个_副本_，而层级参数会选择要使用哪一个副本。
这些层级参数用点和花括号写出，因此有 {anchorTerm MyListDotZero}`MyList.{0} : Type → Type`、{anchorTerm MyListDotOne}`MyList.{1} : Type 1 → Type 1` 和 {anchorTerm MyListDotTwo}`MyList.{2} : Type 2 → Type 2`。

显式写出层级后，前面的例子变为：

```anchor myListOfList3Expl
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
```

当一个宇宙多态定义以多个类型作为实参时，最好为每个实参赋予其自身的层级变量，以获得最大的灵活性。
例如，可以如下编写一个带有单一层级实参的 {anchorName SumNoMax}`Sum` 版本：

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
然而，它要求两个参数都位于同一个宇宙中：
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

通过为两个类型参数的宇宙层级使用不同的变量，然后声明所得数据类型位于二者中的较大者，可以使此数据类型更加灵活：

```anchor SumMax
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
这使得 {anchorName SumMax}`Sum` 可以用于来自不同宇宙的参数：

```anchor stringOrTypeSum
def stringOrType : Sum String Type := .inr Nat
```

在 Lean 期望宇宙层级的位置，允许使用以下任意一种：
 * 一个具体层级，如 {lit}`0` 或 {lit}`1`
 * 代表某个层级的变量，例如 {anchorTerm SumMax}`u` 或 {anchorTerm SumMax}`v`
 * 两个层级的最大值，写作将 {anchorTerm SumMax}`max` 应用于这些层级
 * 层级提升，记作 {anchorTerm someTrueProps}`+ 1`

## 编写宇宙多态定义
%%%
tag := none
file := "Writing-Universe-Polymorphic-Definitions"
%%%

到目前为止，本书中定义的每个数据类型都位于 {anchorTerm SomeTypes}`Type`，即最小的数据宇宙中。
在介绍 Lean 标准库中的多态数据类型（例如 {anchorName SomeTypes}`List` 和 {anchorName SumMax}`Sum`）时，本书创建了它们的非宇宙多态版本。
真正的版本使用宇宙多态，以便在类型层级程序和非类型层级程序之间复用代码。

在编写宇宙多态类型时，有一些通用准则可遵循。
首先，相互独立的类型参数应具有不同的宇宙变量，这使得该多态定义能够用于更广泛的实参，从而增加代码复用的可能性。
其次，整个类型本身通常位于所有宇宙变量的最大值所在的宇宙中，或位于比该最大值高一层的宇宙中。
先尝试这两者中较小的那个。
最后，最好将新类型放在尽可能小的宇宙中，这使它能在其他上下文中更灵活地使用。
非多态类型，例如 {anchorTerm SomeTypes}`Nat` 和 {anchorName SomeTypes}`String`，可以直接放置在 {anchorTerm Type0Type}`Type 0` 中。

## {anchorTerm PropType}`Prop` 与多态性
%%%
tag := none
file := "Prop-and-Polymorphism"
%%%


正如 {anchorTerm SomeTypes}`Type`、{anchorTerm SomeTypes}`Type 1` 等描述对程序和数据进行分类的类型一样，{anchorTerm PropType}`Prop` 对逻辑命题进行分类。
{anchorTerm PropType}`Prop` 中的类型描述什么可算作一个陈述为真的有说服力的证据。
命题在许多方面类似于普通类型：它们可以归纳地声明，可以有构造子，函数也可以将命题作为参数。
然而，与数据类型不同的是，通常并不重要的是为一个陈述的真提供了_哪一个_证据，而只是提供了证据_这一事实_。
另一方面，一个程序不仅返回一个 {anchorTerm SomeTypes}`Nat`，而且返回的是_正确的_ {anchorTerm SomeTypes}`Nat`，这一点非常重要。

{anchorTerm PropType}`Prop` 位于宇宙层级结构的底部，而 {anchorTerm PropType}`Prop` 的类型是 {anchorTerm SomeTypes}`Type`。
这意味着 {anchorTerm PropType}`Prop` 适合作为提供给 {anchorName SomeTypes}`List` 的参数，其理由与 {anchorTerm SomeTypes}`Nat` 相同。
命题的列表具有类型 {anchorTerm SomeTypes}`List Prop`：

```anchor someTrueProps
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```
显式填入宇宙参数表明 {anchorTerm PropType}`Prop` 是一个 {anchorTerm SomeTypes}`Type`：

```anchor someTruePropsExp
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```

在幕后，{anchorTerm PropType}`Prop` 和 {anchorTerm SomeTypes}`Type` 被统一到一个称为 {anchorTerm SomeTypes}`Sort` 的单一层级结构中。
{anchorTerm PropType}`Prop` 与 {anchorTerm sorts}`Sort 0` 相同，{anchorTerm Type0Type}`Type 0` 是 {anchorTerm sorts}`Sort 1`，{anchorTerm SomeTypes}`Type 1` 是 {anchorTerm sorts}`Sort 2`，依此类推。
事实上，{anchorTerm sorts}`Type u` 与 {anchorTerm sorts}`Sort (u+1)` 相同。
在用 Lean 编写程序时，这通常并不相关，但它可能不时出现在错误消息中，并且解释了 {anchorName sorts}`CoeSort` 类的名称。
此外，将 {anchorTerm PropType}`Prop` 作为 {anchorTerm sorts}`Sort 0` 使得又一个宇宙运算符变得有用。
当 {anchorTerm sorts}`v` 为 {lit}`0` 时，宇宙层级 {lit}`imax u v` 是 {lit}`0`；否则，它是 {anchorTerm sorts}`u` 或 {anchorTerm sorts}`v` 中较大的那个。
与 {anchorTerm sorts}`Sort` 一起，这使得在编写应当尽可能可移植于 {anchorTerm PropType}`Prop` 和 {anchorTerm SomeTypes}`Type` 宇宙之间的代码时，可以使用针对返回 {anchorTerm PropType}`Prop` 的函数的特殊规则。

# 实践中的多态性
%%%
tag := none
file := "Polymorphism-in-Practice"
%%%

在本书余下部分中，多态数据类型、结构和类的定义将使用宇宙多态性，以便与 Lean 标准库保持一致。
这将使 {moduleName}`Functor`、{anchorName next}`Applicative` 和 {anchorName next}`Monad` 类的完整呈现能够与它们的实际定义完全一致。
