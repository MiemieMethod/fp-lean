import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "结构体和继承" =>
%%%
tag := "structure-inheritance"
%%%

为了理解 {anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Applicative` 和 {anchorName ApplicativeLaws}`Monad` 的完整定义，另一个 Lean 的特性必不可少：结构体继承 (Structure Inheritance)。
结构体继承允许一种结构体类型提供另一种结构体类型的接口，并添加额外的属性。
这在对具有明确分类关系的概念进行建模时非常有用。
例如，以神话生物 (Mythical Creature) 的模型为例。
其中有些很大型，有些很小型：

```anchor MythicalCreature
structure MythicalCreature where
  large : Bool
deriving Repr
```
在幕后，定义 {anchorName MythicalCreature}`MythicalCreature` 结构体会创建一个具有名为 {anchorName MythicalCreatureMore}`mk` 的单一构造子的归纳类型：
```anchor MythicalCreatureMk
#check MythicalCreature.mk
```
```anchorInfo MythicalCreatureMk
MythicalCreature.mk (large : Bool) : MythicalCreature
```
类似地，当一个函数 {anchorName MythicalCreatureLarge}`MythicalCreature.large` 被创建，它实际上从构造子中提取了属性：
```anchor MythicalCreatureLarge
#check MythicalCreature.large
```
```anchorInfo MythicalCreatureLarge
MythicalCreature.large (self : MythicalCreature) : Bool
```

在大多数古老的故事中，每个怪物都可以用某种方式被击败。
一只怪物 (Monster) 的描述应该包括以下信息，以及它是否庞大：

```anchor Monster
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
```
标题中的 {anchorTerm Monster}`extends MythicalCreature` 表明每个怪物也都是神话生物。
要定义一个 {anchorName Monster}`Monster`，其 {anchorName Monster}`MythicalCreature` 的属性和 {anchorName Monster}`Monster` 的属性应被同时提供。
巨魔 (Troll) 是一种对阳光敏感的大型怪物：

```anchor troll
def troll : Monster where
  large := true
  vulnerability := "sunlight"
```

在幕后，继承是通过组合来实现的。
构造子 {anchorName MonsterMk}`Monster.mk` 将 {anchorName Monster}`MythicalCreature` 作为其参数：
```anchor MonsterMk
#check Monster.mk
```
```anchorInfo MonsterMk
Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster
```
除了定义函数来提取每个新属性的值之外，一个类型为 {anchorTerm MonsterToCreature}`Monster → MythicalCreature` 的函数 {anchorTerm MonsterToCreature}`Monster.toMythicalCreature` 也被定义了。
其可以被用于提取底层的生物。

在 Lean 的继承层级体系中逐级上升与面向对象语言中的向上转型（Upcasting）并不相同。
向上转型运算符会使派生类的值被视为父类的实例，但该值会保留其原有的特性和结构体。
然而，在 Lean 中，在继承层级体系内逐级上升实际上会擦除原有的底层信息。
要查看此操作，请看 {anchorTerm evalTrollCast}`troll.toMythicalCreature` 的求值结果：
```anchor evalTrollCast
#eval troll.toMythicalCreature
```
```anchorInfo evalTrollCast
{ large := true }
```
只有 {anchorName MythicalCreature}`MythicalCreature` 的属性被保留了。


如同 {kw}`where` 语法一样，使用属性名称的花括号表示法也适用于结构体继承：

```anchor troll2
def troll : Monster := {large := true, vulnerability := "sunlight"}
```
不过，委托给底层构造子的匿名尖括号表示法揭示了内部的细节：
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
需要额外的一对尖括号，这将对 {anchorName troll3}`true` 调用 {anchorName MythicalCreatureMk}`MythicalCreature.mk`：

```anchor troll3
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
```


Lean 的点表示法能够考虑继承。
换句话说，现有的 {anchorName trollLargeNoDot}`MythicalCreature.large` 可以和 {anchorName Monster}`Monster` 一起使用，并且 Lean 会在调用 {anchorName trollLargeNoDot}`MythicalCreature.large` 之前自动插入对 {anchorTerm MonsterToCreature}`Monster.toMythicalCreature` 的调用。
不过，这仅在使用点表示法时发生，并且使用正常的函数调用语法来应用属性查找函数会致使一个类型错误的发生：
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
对于用户定义函数 (User-Defined Function)，点表示法还可以考虑其继承关系。
小型生物是指那些不大的生物：

```anchor small
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
```
对于 {anchorTerm smallTroll}`troll.small` 的求值结果是 {anchorTerm smallTroll}`false`，而尝试对 {anchorTerm smallTrollWrong}`MythicalCreature.small troll` 求值则会产生以下结果：
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
%%%

助手是一种神话生物，当给予适当的报酬时，它就可以提供帮助：

```anchor Helper
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
```
例如，_nisse_ 是一种小精灵，众所周知，当给他提供美味的粥时，它就会帮忙打理家务：

```anchor elf
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
```

如果巨魔被驯化，它们便会成为出色的助手。
它们强壮到可以在一个晚上耕完整片田地，尽管它们需要模型山羊来让它们对自己的生活感到满意。
怪物助手是既是怪物又是助手：

```anchor MonstrousAssistant
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
```
这种结构体类型的值必须由两个父结构体的所有属性进行填充：

```anchor domesticatedTroll
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
```

这两种父结构体类型都扩展自 {anchorName MythicalCreature}`MythicalCreature`。
如果多重继承被简单地实现，那么这可能会导致“菱形问题”，即在一个给定的 {anchorName MonstrousAssistant}`MonstrousAssistant` 中，不清楚应该采用哪条路径来获取 {anchorName MythicalCreature}`large`。
它应该从所包含的 {anchorName Monster}`Monster` 还是 {anchorName Helper}`Helper` 中去获取 {lit}`large` 呢？
在 Lean 中，答案是采用第一条指定到祖先结构体的路径，并且其他父结构体的属性会被复制，而不是让新的结构体直接包含两个父结构体。

通过检验 {anchorName MonstrousAssistant}`MonstrousAssistant` 的构造子的签名可以看到这一点：
```anchor checkMonstrousAssistantMk
#check MonstrousAssistant.mk
```
```anchorInfo checkMonstrousAssistantMk
MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant
```
它接受一个 {anchorName Monster}`Monster` 作为参数，以及 {anchorName Helper}`Helper` 在 {anchorName MythicalCreature}`MythicalCreature` 之上引入的两个属性。
类似地，虽然 {anchorName MonstrousAssistantMore}`MonstrousAssistant.toMonster` 仅仅是从构造子中提取出 {anchorName Monster}`Monster`，但 {anchorName printMonstrousAssistantToHelper}`MonstrousAssistant.toHelper` 并没有 {anchorName Helper}`Helper` 可以提取。
{kw}`#print` 命令展现了其实现方式：
```anchor printMonstrousAssistantToHelper
#print MonstrousAssistant.toHelper
```
```anchorInfo printMonstrousAssistantToHelper
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
```
此函数从 {anchorName MonstrousAssistant}`MonstrousAssistant` 的属性中构造了一个 {anchorName Helper}`Helper`。
{lit}`@[reducible]` 属性的作用与编写 {kw}`abbrev` 相同。

## 默认声明
%%%
tag := "inheritance-defaults"
%%%

当一个结构体继承自另一个结构体时，可以使用默认属性定义，即基于子结构体的属性去实例化父结构体的属性。
如果需要比生物是否庞大更具体的尺寸特征，则可以结合使用描述尺寸的专用数据类型和继承机制，以此产生一个结构体，其中 {anchorName MythicalCreature}`large` 属性是根据 {anchorName SizedCreature}`size` 属性的内容计算得出的：

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
但是，这个默认定义只是一个默认定义。
与 C# 或 Scala 等语言中的属性继承不同，子结构体中的定义仅在没有提供 {anchorName MythicalCreature}`large` 的具体值时才会使用，并且可能会出现无意义的结果：

```anchor nonsenseCreature
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
```
如果子结构体不应偏离父结构体，可以采用几种做法：

 1. 记录这种关系，就像对 {anchorName SizedCreature}`BEq` 和 {anchorName MonstrousAssistantMore}`Hashable` 所做的那样。
 2. 定义一个命题，说明这些字段具有适当的关系，并设计 API，使其在关键位置要求提供该命题为真的证据。
 3. 完全不使用继承。

第二种做法可以写成如下形式：

```anchor sizesMatch
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
```
请注意，单个等号用于表示等式 _命题_ ，而双等号用于表示一个检查相等性并返回 {anchorName MythicalCreature}`Bool` 的函数。
{anchorName sizesMatch}`SizesMatch` 被定义为 {kw}`abbrev`，因为它应该在证明中自动展开，以使得 {tactic}`decide` 能看到需要被证明的等式。

_huldre_ 是一种中等体型的神话生物——实际上，它们与人类的体型相同。
{anchorName huldresize}`huldre` 上的两个大小属性是相互匹配的：

```anchor huldresize
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide
```


## 类型类继承
%%%
tag := "type-class-inheritance"
%%%

在幕后，类型类是结构体。
定义一个新的类型类会定义一个新的结构体，而定义一个实例会创建该结构体类型的一个值。
然后，它们被添加到 Lean 的内部表中，以便 Lean 可以根据请求找到实例。
这样做的结果是类型类能够继承其他类型类。

由于使用了完全相同的语言特性，类型类继承支持结构体继承的所有特性，包括多重继承、父类型方法的默认实现以及自动解决菱形继承问题。
这在许多情况下都很有用，就像 Java、C# 和 Kotlin 等语言中的多重接口继承。
通过精心设计类型类的继承层级体系，程序员可以兼得两方面的优势：一方面是得到一个可独立实现的抽象的精细集合，另一方面是从更大、更通用的抽象中自动构造出这些特定的抽象。
