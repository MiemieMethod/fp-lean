import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "结构与继承" =>
%%%
tag := "structure-inheritance"
file := "Structures-and-Inheritance"
%%%

为了理解 {anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Applicative` 和 {anchorName ApplicativeLaws}`Monad` 的完整定义，还需要另一个 Lean 特性：结构继承。
结构继承允许一种结构类型提供另一种结构的接口，并附带额外字段。
当对具有清晰分类关系的概念建模时，这可能很有用。
例如，考虑一个神话生物模型。
其中有些体型大，有些体型小：

```anchor MythicalCreature
structure MythicalCreature where
  large : Bool
deriving Repr
```
在幕后，定义 {anchorName MythicalCreature}`MythicalCreature` 结构会创建一个归纳类型，它带有一个名为 {anchorName MythicalCreatureMore}`mk` 的单一构造子：
```anchor MythicalCreatureMk
#check MythicalCreature.mk
```
```anchorInfo MythicalCreatureMk
MythicalCreature.mk (large : Bool) : MythicalCreature
```
类似地，会创建一个函数 {anchorName MythicalCreatureLarge}`MythicalCreature.large`，它实际从构造子中提取该字段：
```anchor MythicalCreatureLarge
#check MythicalCreature.large
```
```anchorInfo MythicalCreatureLarge
MythicalCreature.large (self : MythicalCreature) : Bool
```

在大多数古老故事中，每个怪物都能以某种方式被击败。
对一个怪物的描述应当包括这一信息，以及它是否巨大：

```anchor Monster
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
```
标题中的 {anchorTerm Monster}`extends MythicalCreature` 表明每个怪物也是神话中的存在。
要定义一个 {anchorName Monster}`Monster`，应同时提供来自 {anchorName Monster}`MythicalCreature` 的字段和来自 {anchorName Monster}`Monster` 的字段。
巨魔是一种大型怪物，且易受阳光伤害：

```anchor troll
def troll : Monster where
  large := true
  vulnerability := "sunlight"
```

在幕后，继承是用组合实现的。
构造子 {anchorName MonsterMk}`Monster.mk` 接受一个 {anchorName Monster}`MythicalCreature` 作为其参数：
```anchor MonsterMk
#check Monster.mk
```
```anchorInfo MonsterMk
Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster
```
除了定义用于提取每个新字段的值的函数之外，还定义了一个类型为 {anchorTerm MonsterToCreature}`Monster → MythicalCreature` 的函数 {anchorTerm MonsterToCreature}`Monster.toMythicalCreature`。
这可用于提取底层的生物。

在 Lean 中沿继承层级向上移动，并不等同于面向对象语言中的向上转型。
向上转型运算符会使来自派生类的值被当作父类的一个实例来处理，但该值保留其身份和结构。
然而，在 Lean 中，沿继承层级向上移动实际上会擦除底层信息。
要观察这一点的实际效果，请考虑对 {anchorTerm evalTrollCast}`troll.toMythicalCreature` 求值的结果：
```anchor evalTrollCast
#eval troll.toMythicalCreature
```
```anchorInfo evalTrollCast
{ large := true }
```
只保留 {anchorName MythicalCreature}`MythicalCreature` 的字段。


正如 {kw}`where` 语法一样，带有字段名的花括号记法也适用于结构继承：

```anchor troll2
def troll : Monster := {large := true, vulnerability := "sunlight"}
```
然而，委托给底层构造子的匿名尖括号记法会暴露内部细节：
```anchor wrongTroll1
def troll : Monster := ⟨true, "sunlight"⟩
```
```anchorError wrongTroll1
Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  MythicalCreature
in the application
  Monster.mk true
```
需要额外的一组尖括号，这会在 {anchorName troll3}`true` 上调用 {anchorName MythicalCreatureMk}`MythicalCreature.mk`：

```anchor troll3
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
```


Lean 的点记法能够将继承纳入考虑。
换言之，已有的 {anchorName trollLargeNoDot}`MythicalCreature.large` 可以与 {anchorName Monster}`Monster` 一起使用，并且 Lean 会在调用 {anchorName trollLargeNoDot}`MythicalCreature.large` 之前自动插入对 {anchorTerm MonsterToCreature}`Monster.toMythicalCreature` 的调用。
然而，这只在使用点记法时发生；若使用普通函数调用语法来应用字段查找函数，则会导致类型错误：
```anchor trollLargeNoDot
#eval MythicalCreature.large troll
```
```anchorError trollLargeNoDot
Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.large troll
```
点记法也可以在用户定义函数中考虑继承。
小型生物就是非大型的生物：

```anchor small
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
```
对 {anchorTerm smallTroll}`troll.small` 求值会得到 {anchorTerm smallTroll}`false`，而尝试对 {anchorTerm smallTrollWrong}`MythicalCreature.small troll` 求值会产生：
```anchorError smallTrollWrong
Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.small troll
```

# 多重继承
%%%
tag := "multiple-structure-inheritance"
file := "Multiple-Inheritance"
%%%

助手是一种神话生物，在得到正确报酬时可以提供帮助：

```anchor Helper
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
```
例如，_nisse_ 是一种小精灵，据说在得到美味的粥时会帮忙料理家务：

```anchor elf
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
```

如果被驯化，巨魔会成为出色的帮手。
它们足够强壮，能够在一夜之间犁完整片田地，不过它们需要模型山羊来使其安于自己的生活境遇。
怪物助手是同时也是帮手的怪物：

```anchor MonstrousAssistant
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
```
此结构类型的一个值必须填充两个父结构中的所有字段：

```anchor domesticatedTroll
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
```

这两个父结构类型都扩展了 {anchorName MythicalCreature}`MythicalCreature`。
如果以朴素的方式实现多重继承，那么这可能导致“菱形问题”：对于给定的 {anchorName MonstrousAssistant}`MonstrousAssistant`，应当通过哪条路径到达 {anchorName MythicalCreature}`large` 将不明确。
它应当从所包含的 {anchorName Monster}`Monster` 中取得 {lit}`large`，还是从所包含的 {anchorName Helper}`Helper` 中取得？
在 Lean 中，答案是采用第一个指定的到祖父结构的路径，而额外父结构的字段会被复制，并不是让新结构直接同时包含两个父结构。

这一点可以通过考察 {anchorName MonstrousAssistant}`MonstrousAssistant` 的构造子的签名看出：
```anchor checkMonstrousAssistantMk
#check MonstrousAssistant.mk
```
```anchorInfo checkMonstrousAssistantMk
MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant
```
它以一个 {anchorName Monster}`Monster` 作为参数，并同时接收 {anchorName Helper}`Helper` 在 {anchorName MythicalCreature}`MythicalCreature` 之上引入的两个字段。
类似地，虽然 {anchorName MonstrousAssistantMore}`MonstrousAssistant.toMonster` 只是从构造子中提取 {anchorName Monster}`Monster`，但 {anchorName printMonstrousAssistantToHelper}`MonstrousAssistant.toHelper` 没有可供提取的 {anchorName Helper}`Helper`。
{kw}`#print` 命令会揭示它的实现：
```anchor printMonstrousAssistantToHelper
#print MonstrousAssistant.toHelper
```
```anchorInfo printMonstrousAssistantToHelper
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
```
此函数从 {anchorName MonstrousAssistant}`MonstrousAssistant` 的字段构造一个 {anchorName Helper}`Helper`。
{lit}`@[reducible]` 属性与写作 {kw}`abbrev` 具有相同效果。

## 默认声明
%%%
tag := "inheritance-defaults"
file := "Default-Declarations"
%%%

当一个结构继承自另一个结构时，可以使用默认字段定义，基于子结构的字段来实例化父结构的字段。
如果需要比判断某个生物是否大型更精细的大小特异性，则可以将一个专门描述大小的数据类型与继承结合使用，从而得到一个结构，其中 {anchorName MythicalCreature}`large` 字段由 {anchorName SizedCreature}`size` 字段的内容计算而来：

```anchor SizedCreature
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large
```
然而，这个默认定义只是一个默认定义。
不同于 C# 或 Scala 等语言中的属性继承，子结构中的定义只会在没有为 {anchorName MythicalCreature}`large` 提供具体值时使用，并且可能出现不合情理的结果：

```anchor nonsenseCreature
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
```
如果子结构不应偏离父结构，则有几种选择：

 1. 记录这种关系，就像对 {anchorName SizedCreature}`BEq` 和 {anchorName MonstrousAssistantMore}`Hashable` 所做的那样
 2. 定义一个命题，说明这些字段以适当方式相关；并设计 API，使其在关键处要求该命题为真的证据
 3. 完全不使用继承

第二种选择可以如下所示：

```anchor sizesMatch
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
```
注意，单个等号用于表示相等性_命题_，而双等号用于表示一个检查相等性并返回 {anchorName MythicalCreature}`Bool` 的函数。
{anchorName sizesMatch}`SizesMatch` 被定义为 {kw}`abbrev`，因为它应当在证明中自动展开，使得 {tactic}`decide` 能够看到应当证明的等式。

_huldre_ 是一种中等大小的神话生物——事实上，它们与人类一样高大。
{anchorName huldresize}`huldre` 上的两个大小字段彼此一致：

```anchor huldresize
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide
```


## 类型类继承
%%%
tag := "type-class-inheritance"
file := "Type-Class-Inheritance"
%%%

在幕后，类型类就是结构。
定义一个新的类型类会定义一个新的结构，而定义一个实例会创建该结构类型的一个值。
随后它们会被加入 Lean 的内部表中，使 Lean 能够在需要时找到这些实例。
由此可知，类型类可以从其他类型类继承。

由于类型类继承使用的正是相同的语言特性，它支持结构继承的所有特性，包括多重继承、父类型方法的默认实现，以及菱形结构的自动折叠。
这在许多与 Java、C# 和 Kotlin 等语言中的多接口继承有用的相同场景中也很有用。
通过仔细设计类型类继承层次，程序员可以同时获得两方面的优点：一组细粒度、可独立实现的抽象，以及从更大、更一般的抽象自动构造这些特定抽象的能力。
