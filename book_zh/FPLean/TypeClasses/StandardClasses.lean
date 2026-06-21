import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "标准类" =>
%%%
tag := "standard-classes"
file := "Standard-Classes"
%%%


本节介绍 Lean 中可以使用类型类进行重载的多种运算符和函数。
每个运算符或函数都对应于某个类型类的一个方法。
不同于 C++，Lean 中的中缀运算符被定义为具名函数的缩写；这意味着为新类型重载它们并不是通过运算符本身完成的，而是通过其底层名称（例如 {moduleName}`HAdd.hAdd`）完成的。

# 算术
%%%
tag := "arithmetic-classes"
file := "Arithmetic"
%%%

多数算术运算符都有异质形式，其中参数可以具有不同的类型，并且由一个输出参数决定所得表达式的类型。
对于每个异质运算符，都有一个对应的同质版本；去掉字母 {lit}`h` 即可得到它，因此 {moduleName}`HAdd.hAdd` 变为 {moduleName}`Add.add`。
以下算术运算符是重载的：

:::table +header

*
 -  表达式
 -  脱糖
 -  类名
*
 -  {anchorTerm plusDesugar}`x + y`
 -  {anchorTerm plusDesugar}`HAdd.hAdd x y`
 -  {moduleName}`HAdd`
*
 -  {anchorTerm minusDesugar}`x - y`
 -  {anchorTerm minusDesugar}`HSub.hSub x y`
 -  {moduleName}`HSub`
*
 -  {anchorTerm timesDesugar}`x * y`
 -  {anchorTerm timesDesugar}`HMul.hMul x y`
 -  {moduleName}`HMul`
*
 -  {anchorTerm divDesugar}`x / y`
 -  {anchorTerm divDesugar}`HDiv.hDiv x y`
 -  {moduleName}`HDiv`
*
 -  {anchorTerm modDesugar}`x % y`
 -  {anchorTerm modDesugar}`HMod.hMod x y`
 -  {moduleName}`HMod`
*
 -  {anchorTerm powDesugar}`x ^ y`
 -  {anchorTerm powDesugar}`HPow.hPow x y`
 -  {moduleName}`HPow`
*
 -  {anchorTerm negDesugar}`- x`
 -  {anchorTerm negDesugar}`Neg.neg x`
 -  {moduleName}`Neg`


:::

# 按位运算符
%%%
tag := "bitwise-classes"
file := "Bitwise-Operators"
%%%

Lean 包含若干标准按位运算符，它们使用类型类进行重载。
对于固定宽度类型，例如 {anchorTerm UInt8}`UInt8`、{anchorTerm UInt16}`UInt16`、{anchorTerm UInt32}`UInt32`、{anchorTerm UInt64}`UInt64` 和 {anchorTerm USize}`USize`，都有相应实例。
后者是当前平台上的机器字大小，通常为 32 位或 64 位。
以下按位运算符是重载的：

:::table +header
*
 -  表达式
 -  脱糖
 -  类名

*
 -  {anchorTerm bAndDesugar}`x &&& y`
 -  {anchorTerm bAndDesugar}`HAnd.hAnd x y`
 -  {moduleName}`HAnd`
*
 -  {anchorTerm bOrDesugar}`x ||| y`
 -  {anchorTerm bOrDesugar}`HOr.hOr x y`
 -  {moduleName}`HOr`
*
 -  {anchorTerm bXorDesugar}`x ^^^ y`
 -  {anchorTerm bXorDesugar}`HXor.hXor x y`
 -  {moduleName}`HXor`
*
 -  {anchorTerm complementDesugar}`~~~x`
 -  {anchorTerm complementDesugar}`Complement.complement x`
 -  {moduleName}`Complement`
*
 -  {anchorTerm shrDesugar}`x >>> y`
 -  {anchorTerm shrDesugar}`HShiftRight.hShiftRight x y`
 -  {moduleName}`HShiftRight`
*
 -  {anchorTerm shlDesugar}`x <<< y`
 -  {anchorTerm shlDesugar}`HShiftLeft.hShiftLeft x y`
 -  {moduleName}`HShiftLeft`

:::

由于名称 {anchorName chapterIntro}`And` 和 {anchorName chapterIntro}`Or` 已经被用作逻辑联结词的名称，{anchorName chapterIntro}`HAnd` 和 {anchorName chapterIntro}`HOr` 的同质版本称为 {anchorName moreOps}`AndOp` 和 {anchorName moreOps}`OrOp`，而不是 {anchorName chapterIntro}`And` 和 {anchorName chapterIntro}`Or`。

# 相等性与排序
%%%
tag := "equality-and-ordering"
file := "Equality-and-Ordering"
%%%

测试两个值是否相等通常使用 {moduleName}`BEq` 类，它是“布尔相等”的缩写。
由于 Lean 被用作定理证明器，在 Lean 中实际上有两类相等运算符：
 * {deftech}_布尔相等_与其他编程语言中的相等属于同一种相等。它是一个接受两个值并返回一个 {anchorName CoeBoolProp}`Bool` 的函数。布尔相等用两个等号书写，正如在 Python 和 C# 中一样。由于 Lean 是一门纯函数式语言，因此不存在引用相等与值相等的分别概念——指针不能被直接观察。
 * {deftech}_命题相等_ 是两个事物相等这一数学陈述。命题相等不是函数；相反，它是一个允许证明的数学陈述。它用单个等号书写。一个命题相等的陈述就像一种类型，用来分类该相等性的证据。

这两种相等概念都很重要，并且用于不同的目的。
布尔相等在程序中很有用，尤其是在需要判定两个值是否相等时。
例如，{anchorTerm boolEqTrue}`"Octopus" ==  "Cuttlefish"` 求值为 {anchorTerm boolEqTrue}`false`，而 {anchorTerm boolEqFalse}`"Octopodes" ==  "Octo".append "podes"` 求值为 {anchorTerm boolEqFalse}`true`。
有些值，例如函数，无法检查其相等性。
例如，{anchorTerm functionEq}`(fun (x : Nat) => 1 + x) == (Nat.succ ·)` 会产生错误：
```anchorError functionEq
failed to synthesize
  BEq (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
如这条消息所示，{lit}`==` 是通过类型类重载的。
表达式 {anchorTerm beqDesugar}`x == y` 实际上是 {anchorTerm beqDesugar}`BEq.beq x y` 的简写。

命题相等性是一个数学陈述，而不是一次程序调用。
由于命题类似于描述某个陈述之证据的类型，命题相等性与 {anchorName readFile}`String` 和 {anchorTerm moreOps}`Nat → List Int` 这样的类型更为相近，而不是与布尔相等性相近。
这意味着它不能被自动检查。
不过，只要两个表达式具有相同的类型，它们的相等性就可以在 Lean 中陈述。
陈述 {anchorTerm functionEqProp}`(fun (x : Nat) => 1 + x) = (Nat.succ ·)` 是一个完全合理的陈述。
从数学的角度看，如果两个函数将相等的输入映射到相等的输出，那么这两个函数就是相等的；因此这个陈述甚至是真的，尽管它需要一个一行证明来说服 Lean 确认这一事实。

一般而言，当把 Lean 用作编程语言时，坚持使用布尔函数而非命题最为容易。
然而，正如 {moduleName}`Bool` 的构造子名称 {moduleName}`true` 和 {moduleName}`false` 所暗示的，这一区别有时会变得模糊。
有些命题是_可判定的_，这意味着它们可以像布尔函数一样被检查。
检查命题为真还是为假的函数称为_判定过程_，它返回该命题为真或为假的_证据_。
可判定命题的一些例子包括自然数的相等与不等、字符串的相等，以及由本身可判定的命题构成的“与”和“或”。

:::paragraph
在 Lean 中，{kw}`if` 作用于可判定命题。
例如，{anchorTerm twoLessFour}`2 < 4` 是一个命题：
```anchor twoLessFour
#check 2 < 4
```
```anchorInfo twoLessFour
2 < 4 : Prop
```
尽管如此，把它写作 {kw}`if` 中的条件是完全可接受的。
例如，{anchorTerm ifProp}`if 2 < 4 then 1 else 2` 的类型是 {moduleName}`Nat`，并求值为 {anchorTerm ifProp}`1`。
:::

并非所有命题都是可判定的。
如果它们都是可判定的，那么计算机只需运行判定过程就能够证明任何真命题，数学家也就会失业。
更具体地说，可判定命题具有 {anchorName DecLTLEPos}`Decidable` 类型类的实例，该实例包含判定过程。
试图像使用 {anchorName CoeBoolProp}`Bool` 一样使用一个不可判定的命题，会导致无法找到 {anchorName DecLTLEPos}`Decidable` 实例。
例如，{anchorTerm funEqDec}`if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"` 会得到：
```anchorError funEqDec
failed to synthesize
  Decidable ((fun x => 1 + x) = fun x => x.succ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

以下通常是可判定的命题通过类型类进行重载：

:::table +header
*
 -  表达式
 -  脱糖
 -  类名
*
 -  {anchorTerm ltDesugar}`x < y`
 -  {anchorTerm ltDesugar}`LT.lt x y`
 -  {moduleName}`LT`
*
 -  {anchorTerm leDesugar}`x ≤ y`
 -  {anchorTerm leDesugar}`LE.le x y`
 -  {moduleName}`LE`
*
 -  {anchorTerm gtDesugar}`x > y`
 -  {anchorTerm gtDesugar}`LT.lt y x`
 -  {moduleName}`LT`
*
 -  {anchorTerm geDesugar}`x ≥ y`
 -  {anchorTerm geDesugar}`LE.le y x`
 -  {moduleName}`LE`
:::

由于尚未演示如何定义新的命题，因此可能难以定义 {moduleName}`LT` 和 {moduleName}`LE` 的全新实例。
然而，它们可以根据已有实例来定义。
{anchorName LTPos}`Pos` 的 {moduleName}`LT` 和 {moduleName}`LE` 实例可以使用 {moduleName}`Nat` 的已有实例：

```anchor LTPos
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
```

```anchor LEPos
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
```
这些命题默认情况下不可判定，因为 Lean 在合成实例时不会展开命题的定义。
可以使用 {anchorName DecLTLEPos}`inferInstanceAs` 运算符弥合这一点；如果给定类的实例存在，它会找到该实例：

```anchor DecLTLEPos
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))
```
类型检查器确认这些命题的定义相互匹配。
将它们混淆会导致错误：
```anchor LTLEMismatch
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))
```
```anchorError LTLEMismatch
Type mismatch
  inferInstanceAs (Decidable (x.toNat < y.toNat))
has type
  Decidable (x.toNat < y.toNat)
but is expected to have type
  Decidable (x ≤ y)
```

:::paragraph
使用 {lit}`<`、{lit}`==` 和 {lit}`>` 比较值可能效率低下。
先检查一个值是否小于另一个值，然后再检查它们是否相等，可能需要对大型数据结构进行两次遍历。
为了解决这个问题，Java 和 C# 分别有标准的 {java}`compareTo` 和 {CSharp}`CompareTo` 方法，类可以重写这些方法以同时实现这三种操作。
如果接收者小于参数，这些方法返回负整数；如果二者相等，则返回零；如果接收者大于参数，则返回正整数。
Lean 并不重载整数的含义，而是有一个内建归纳类型来描述这三种可能性：
```anchor Ordering
inductive Ordering where
  | lt
  | eq
  | gt
```
{anchorName OrdPos}`Ord` 类型类可以被重载以产生这些比较。
对于 {anchorName OrdPos}`Pos`，一种实现可以是：
```anchor OrdPos
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp
```
在 Java 中适合使用 {java}`compareTo` 的情形，在 Lean 中应使用 {moduleName}`Ord.compare`。
:::

# 散列
%%%
tag := "hashing"
file := "Hashing"
%%%

Java 和 C# 分别有 {java}`hashCode` 和 {CSharp}`GetHashCode` 方法，用于计算一个值的哈希，以便在哈希表等数据结构中使用。
Lean 中的对应物是一个称为 {anchorName Hashable}`Hashable` 的类型类：

```anchor Hashable
class Hashable (α : Type) where
  hash : α → UInt64
```
如果两个值根据其类型的某个 {moduleName}`BEq` 实例被认为相等，那么它们应当具有相同的哈希值。
换言之，如果 {anchorTerm HashableSpec}`x == y`，那么 {anchorTerm HashableSpec}`hash x == hash y`。
如果 {anchorTerm HashableSpec}`x ≠ y`，那么 {anchorTerm HashableSpec}`hash x` 不一定会不同于 {anchorTerm HashableSpec}`hash y`（毕竟，{moduleName}`Nat` 值的数量无限多于 {moduleName}`UInt64` 值的数量），但如果不相等的值很可能具有不相等的哈希值，则基于哈希的数据结构会有更好的性能。
这与 Java 和 C# 中的期望相同。

标准库包含一个函数 {anchorTerm mixHash}`mixHash`，其类型为 {anchorTerm mixHash}`UInt64 → UInt64 → UInt64`，可用于为一个构造子的不同字段组合哈希值。
对于归纳数据类型，可以通过为每个构造子分配一个唯一编号，然后将该编号与每个字段的哈希值混合，来编写一个合理的哈希函数。
例如，可以为 {anchorName HashablePos}`Pos` 编写一个 {anchorName HashablePos}`Hashable` 实例：

```anchor HashablePos
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos
```

:::paragraph
多态类型的 {anchorTerm HashableNonEmptyList}`Hashable` 实例可以使用递归实例搜索。
只有当 {anchorName HashableNonEmptyList}`α` 可以被哈希时，才能对 {anchorTerm HashableNonEmptyList}`NonEmptyList α` 进行哈希：
```anchor HashableNonEmptyList
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
```
:::
:::paragraph
二叉树在 {anchorName TreeHash}`BEq` 和 {anchorName TreeHash}`Hashable` 的实现中同时使用递归和递归实例搜索：

```anchor TreeHash
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree
```
:::

# 派生标准类
%%%
tag := "deriving-standard-classes"
file := "Deriving-Standard-Classes"
%%%

像 {moduleName}`BEq` 和 {moduleName}`Hashable` 这样的类的实例，手工实现起来往往相当繁琐。
Lean 包含一项称为_实例派生_的功能，允许编译器自动构造许多类型类的行为良好的实例。
事实上，在 {ref "polymorphism"}[关于多态的第一节]中 {anchorName Firewood (module:=Examples.Intro)}`Firewood` 的定义里的 {anchorTerm Firewood (module := Examples.Intro)}`deriving Repr` 短语，就是实例派生的一个例子。

实例可以通过两种方式派生。
第一种方式可在定义结构或归纳类型时使用。
在这种情况下，在类型声明的末尾添加 {kw}`deriving`，随后写出应为其派生实例的类名。
对于已经定义好的类型，可以使用独立的 {kw}`deriving` 命令。
写作 {kw}`deriving instance`{lit}` C1, C2, ... `{kw}`for`{lit}` T`，即可事后为类型 {lit}`T` 派生 {lit}`C1, C2, ...` 的实例。

只需极少量代码，就可以为 {anchorName BEqHashableDerive}`Pos` 和 {anchorName BEqHashableDerive}`NonEmptyList` 派生 {moduleName}`BEq` 与 {moduleName}`Hashable` 实例：

```anchor BEqHashableDerive
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList
```

至少可以为以下类派生实例：

 * {moduleName}`Inhabited`
 * {moduleName}`BEq`
 * {moduleName}`Repr`
 * {moduleName}`Hashable`
 * {moduleName}`Ord`

然而，在某些情况下，派生出的 {moduleName}`Ord` 实例可能无法精确地产生应用中所需的顺序。
在这种情况下，手写一个 {moduleName}`Ord` 实例也是可以的。
高级 Lean 用户可以扩展可派生其实例的类的集合。

除了在程序员生产率和代码可读性方面具有明显优势之外，派生实例还使代码更易维护，因为随着类型定义的演化，实例也会被更新。
在审查代码变更时，涉及数据类型更新的修改，如果没有一行接一行的样板式相等性测试和散列计算修改，会容易阅读得多。

# 追加
%%%
tag := "append-class"
file := "Appending"
%%%

许多数据类型都有某种追加运算符。
在 Lean 中，追加两个值通过类型类 {anchorName HAppend}`HAppend` 进行重载；它是一种异质操作，类似于算术运算中使用的操作：

```anchor HAppend
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
```
语法 {anchorTerm desugarHAppend}`xs ++ ys` 会脱糖为 {anchorTerm desugarHAppend}`HAppend.hAppend xs ys`。
对于同质情形，实现 {moduleName}`Append` 的一个实例就足够了，它遵循通常的模式：

```anchor AppendNEList
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
```

在定义上述实例之后，
```anchor appendSpiders
#eval idahoSpiders ++ idahoSpiders
```
具有如下输出：
```anchorInfo appendSpiders
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider",
           "Banded Garden Spider",
           "Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider"] }
```

类似地，{moduleName}`HAppend` 的定义允许将非空列表追加到普通列表：

```anchor AppendNEListList
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }
```
有了这个实例，
```anchor appendSpidersList
#eval idahoSpiders ++ ["Trapdoor Spider"]
```
得到
```anchorInfo appendSpidersList
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider", "Trapdoor Spider"] }
```

# 函子
%%%
tag := "Functor"
file := "Functors"
%%%

如果一个多态类型拥有名为 {anchorName FunctorDef}`map` 的函数的重载，并且该函数通过一个函数变换其中包含的每个元素，则该多态类型就是一个 {deftech}_functor_。
虽然大多数语言使用这一术语，但 C# 中对应于 {anchorName FunctorDef}`map` 的概念称为 {CSharp}`System.Linq.Enumerable.Select`。
例如，将一个函数映射到列表上，会构造一个新列表，其中起始列表中的每一项都被该函数作用于该项所得的结果替换。
将一个函数 {anchorName optionFMeta}`f` 映射到一个 {anchorName optionFMeta}`Option` 上，会使 {anchorName optionFMeta}`none` 保持不变，并将 {anchorTerm optionFMeta}`some x` 替换为 {anchorTerm optionFMeta}`some (f x)`。

下面是一些函子的例子，以及它们的 {anchorName FunctorDef}`Functor` 实例如何重载 {anchorName FunctorDef}`map`：
 * {anchorTerm mapList}`Functor.map (· + 5) [1, 2, 3]` 求值为 {anchorTerm mapList}`[6, 7, 8]`
 * {anchorTerm mapOption}`Functor.map toString (some (List.cons 5 List.nil))` 求值为 {anchorTerm mapOption}`some "[5]"`
 * {anchorTerm mapListList}`Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]` 求值为 {anchorTerm mapListList}`[[3, 2, 1], [6, 5, 4]]`

由于 {anchorName mapList}`Functor.map` 作为这个常见操作的名称略长，Lean 还为映射函数提供了一个中缀运算符，即 {lit}`<$>`。
前面的例子可以改写如下：
 * {anchorTerm mapInfixList}`(· + 5) <$> [1, 2, 3]` 求值为 {anchorTerm mapInfixList}`[6, 7, 8]`
 * {anchorTerm mapInfixOption}`toString <$> (some (List.cons 5 List.nil))` 求值为 {anchorTerm mapInfixOption}`some "[5]"`
 * {anchorTerm mapInfixListList}`List.reverse <$> [[1, 2, 3], [4, 5, 6]]` 求值为 {anchorTerm mapInfixListList}`[[3, 2, 1], [6, 5, 4]]`

{anchorTerm FunctorNonEmptyList}`NonEmptyList` 的一个 {anchorTerm FunctorNonEmptyList}`Functor` 实例要求指定 {anchorName FunctorNonEmptyList}`map` 函数。

```anchor FunctorNonEmptyList
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
```
这里，{anchorTerm FunctorNonEmptyList}`map` 使用 {moduleName}`List` 的 {anchorTerm FunctorNonEmptyList}`Functor` 实例，将函数映射到尾部。
这个实例是为 {anchorTerm FunctorNonEmptyList}`NonEmptyList` 而不是为 {anchorTerm FunctorNonEmptyListA}`NonEmptyList α` 定义的，因为参数类型 {anchorTerm FunctorNonEmptyListA}`α` 在解析类型类时不起作用。
一个 {anchorTerm FunctorNonEmptyList}`NonEmptyList` _无论条目的类型是什么_，都可以将函数映射到其上。
如果 {anchorTerm FunctorNonEmptyListA}`α` 是该类的一个参数，那么就可能构造出只适用于 {anchorTerm FunctorNonEmptyListA}`NonEmptyList Nat` 的 {anchorTerm FunctorNonEmptyList}`Functor` 版本；但是，作为函子的一部分含义就是 {anchorName FunctorNonEmptyList}`map` 适用于任意条目类型。

:::paragraph
下面是 {anchorTerm FunctorPPoint}`PPoint` 的一个 {anchorTerm FunctorPPoint}`Functor` 实例：

```anchor FunctorPPoint
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }
```
在此情形中，{anchorName FunctorPPoint}`f` 已经被同时应用于 {anchorName FunctorPPoint}`x` 和 {anchorName FunctorPPoint}`y`。
:::

即使函子中包含的类型本身也是函子，映射函数也只会深入一层。
也就是说，当在 {anchorTerm NEPP}`NonEmptyList (PPoint Nat)` 上使用  {anchorName FunctorPPoint}`map` 时，被映射的函数应当以 {anchorTerm NEPP}`PPoint Nat` 作为其参数，而不是 {moduleName}`Nat`。

{anchorName FunctorLaws}`Functor` 类的定义使用了一个尚未讨论的语言特性：默认方法定义。
通常，一个类会指定某个有意义地组合在一起的、最小的可重载操作集合，然后使用带有实例隐式参数的多态函数，在这些重载操作的基础上提供一个更大的功能库。
例如，函数 {anchorName concat}`concat` 可以连接任意非空列表，只要其中的元素是可追加的：

```anchor concat
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
```
然而，对于某些类，如果了解某个数据类型的内部结构，就可以更高效地实现一些操作。

在这些情况下，可以提供默认方法定义。
默认方法定义根据其他方法给出某个方法的默认实现。
不过，实例实现者可以选择用更高效的实现覆盖这个默认定义。
默认方法定义在 {kw}`class` 定义中包含 {lit}`:=`。

在 {anchorName FunctorDef}`Functor` 的情形中，当被映射的函数忽略其参数时，某些类型有一种更高效的方式来实现 {anchorName FunctorDef}`map`。
忽略其参数的函数称为_常量函数_，因为它们总是返回同一个值。
下面是 {anchorName FunctorDef}`Functor` 的定义，其中 {anchorName FunctorDef}`mapConst` 有一个默认实现：

```anchor FunctorDef
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
```

正如不遵守 {moduleName}`BEq` 的 {anchorName HashableSpec}`Hashable` 实例是有缺陷的一样，在映射函数时移动数据的 {moduleName}`Functor` 实例也是有缺陷的。
例如，{moduleName}`List` 的一个有缺陷的 {moduleName}`Functor` 实例可能会丢弃其参数并总是返回空列表，或者可能会反转列表。
{moduleName}`PPoint` 的一个不良 {moduleName}`Functor` 实例可能会把 {anchorTerm FunctorPPointBad}`f x` 同时放入 {anchorName FunctorPPointBad}`x` 和 {anchorName FunctorPPointBad}`y` 字段，或者交换它们。
具体而言，{anchorName FunctorDef}`Functor` 实例应当遵循两条规则：
 1. 映射恒等函数应当得到原始参数。
 2. 映射两个复合起来的函数，应当与将它们的映射复合起来具有相同的效果。

更形式地说，第一条规则表示 {anchorTerm FunctorLaws}`id <$> x` 等于 {anchorTerm FunctorLaws}`x`。
第二条规则表示 {anchorTerm FunctorLaws}`map (fun y => f (g y)) x` 等于 {anchorTerm FunctorLaws}`map f (map g x)`。
复合 {anchorTerm compDef}`f ∘ g` 也可以写作 {anchorTerm compDef}`fun y => f (g y)`。
这些规则防止 {anchorName FunctorDef}`map` 的实现移动数据或删除其中一部分。

# 你可能遇到的消息
%%%
tag := "standard-classes-messages"
file := "Messages-You-May-Meet"
%%%

Lean 不能为所有类派生实例。
例如，代码
```anchor derivingNotFound
deriving instance ToString for NonEmptyList
```
会产生如下错误：
```anchorError derivingNotFound
No deriving handlers have been implemented for class `ToString`
```
调用 {anchorTerm derivingNotFound}`deriving instance` 会使 Lean 查阅一个内部的类型类实例代码生成器表。
如果找到了该代码生成器，那么它会在所提供的类型上被调用，以创建该实例。
然而，这条消息意味着没有找到用于 {anchorName derivingNotFound}`ToString` 的代码生成器。

# 练习
%%%
tag := "standard-classes-exercises"
file := "Exercises"
%%%

 * 编写一个 {anchorTerm moreOps}`HAppend (List α) (NonEmptyList α) (NonEmptyList α)` 的实例并测试它。
 * 为二叉树数据类型实现一个 {anchorTerm FunctorLaws}`Functor` 实例。
