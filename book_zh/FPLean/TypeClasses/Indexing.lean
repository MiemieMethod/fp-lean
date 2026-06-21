import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "数组与索引" =>
%%%
file := "Arrays-and-Indexing"
%%%


{ref "props-proofs-indexing"}[插曲]描述了如何使用索引记法，以便按位置在列表中查找条目。
此语法也由一个类型类支配，并且可用于多种不同的类型。

# 数组
%%%
tag := "array-indexing"
file := "Arrays"
%%%

例如，对于大多数用途，Lean 数组比链表高效得多。
在 Lean 中，类型 {anchorTerm arrVsList}`Array α` 是一个动态大小的数组，保存类型为 {anchorName arrVsList}`α` 的值，很像 Java 的 {java}`ArrayList`、C++ 的 {cpp}`std::vector` 或 Rust 的 {rust}`Vec`。
不同于 {anchorTerm arrVsList}`List`，后者在每次使用 {anchorName arrVsList}`cons` 构造子时都有一次指针间接访问；数组占据一段连续的内存区域，这对处理器缓存要好得多。
此外，在数组中查找一个值需要常数时间，而在链表中查找所需时间与被访问的索引成正比。

在像 Lean 这样的纯函数式语言中，不可能改变数据结构中的某个给定位置。
取而代之的是，构造一个包含所需修改的副本。
然而，复制并不总是必要的：Lean 编译器和运行时包含一种优化，当数组只有一个唯一引用时，它可以允许在幕后将修改实现为变更。

数组的写法类似于列表，但前面带有 {lit}`#`：

```anchor northernTrees
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
```
数组中的值的数量可以使用 {anchorName arrVsList}`Array.size` 得到。
例如，{anchorTerm northernTreesSize}`northernTrees.size` 求值为 {anchorTerm northernTreesSize}`4`。
对于小于数组大小的索引，可以像对列表一样使用索引记法来取得相应的值。
也就是说，{anchorTerm northernTreesTwo}`northernTrees[2]` 求值为 {anchorTerm northernTreesTwo}`"elm"`。
类似地，编译器要求提供索引在界内的证明；并且与列表一样，试图查找数组边界之外的值会导致编译期错误。
例如，{anchorTerm northernTreesEight}`northernTrees[8]` 会产生：
```anchorError northernTreesEight
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 8 < northernTrees.size
```

# 非空列表
%%%
tag := "non-empty-list-indexing"
file := "Non-Empty-Lists"
%%%

表示非空列表的数据类型可以定义为一个结构，其中一个字段表示列表的头部，另一个字段表示尾部；尾部是一个普通的、可能为空的列表：

```anchor NonEmptyList
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
```
例如，非空列表 {moduleName}`idahoSpiders`（其中包含一些原产于美国爱达荷州的蜘蛛物种）由 {anchorTerm firstSpider}`"Banded Garden Spider"` 后接另外四种蜘蛛组成，总计五种蜘蛛：

```anchor idahoSpiders
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
```

用递归函数在此列表中查找特定索引处的值时，应考虑三种可能性：
 1. 索引为 {anchorTerm NEListGetHuh}`0`，此时应返回列表的头部。
 2. 索引为 {anchorTerm NEListGetHuh}`n + 1` 且尾部为空，在这种情况下该索引越界。
 3. 索引为 {anchorTerm NEListGetHuh}`n + 1` 且尾部非空；在这种情况下，该函数可以在尾部和 {anchorTerm NEListGetHuh}`n` 上递归调用。

例如，一个返回 {moduleName}`Option` 的查找函数可以写成如下形式：

```anchor NEListGetHuh
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
```
模式匹配中的每一种情况都对应于上述可能性之一。
对 {anchorName NEListGetHuh}`get?` 的递归调用不需要 {moduleName}`NonEmptyList` 命名空间限定符，因为定义体隐式地位于该定义的命名空间中。
编写此函数的另一种方式是在索引大于零时使用列表查找 {anchorTerm NEListGetHuhList}`xs.tail[n]?`：

```anchor NEListGetHuhList
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
```

如果列表包含一个条目，那么只有 {anchorTerm nats}`0` 是有效索引。
如果它包含两个条目，那么 {anchorTerm nats}`0` 和 {anchorTerm nats}`1` 都是有效索引。
如果它包含三个条目，那么 {anchorTerm nats}`0`、{anchorTerm nats}`1` 和 {anchorTerm nats}`2` 是有效索引。
换言之，非空列表中的有效索引是严格小于列表长度的自然数，也就是小于或等于尾部长度的自然数。

关于索引在界内意味着什么，其定义应写成一个 {kw}`abbrev`，因为用于寻找索引可接受这一证据的策略能够求解数的不等式，但它们并不了解名称 {moduleName}`NonEmptyList.inBounds`：

```anchor inBoundsNEList
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
```
此函数返回一个可能为真也可能为假的命题。
例如，{anchorTerm spiderBoundsChecks}`2` 对于 {moduleName}`idahoSpiders` 是在界内的，而 {anchorTerm spiderBoundsChecks}`5` 则不是：

```anchor spiderBoundsChecks
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide
```
逻辑否定运算符的优先级很低，这意味着 {anchorTerm spiderBoundsChecks}`¬idahoSpiders.inBounds 5` 等价于 {anchorTerm spiderBoundsChecks'}`¬(idahoSpiders.inBounds 5)`。


这一事实可用于编写一个需要索引有效性证据、因而不必返回 {moduleName}`Option` 的查找函数；做法是委托给列表版本，该版本在编译时检查证据：

```anchor NEListGet
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
```
当然，也可以将此函数写成直接使用该证据，而不是委托给一个恰好能够使用同一证据的标准库函数。
这需要使用本书后文将描述的处理证明与命题的技术。


# 重载索引
%%%
tag := "overloading-indexing"
file := "Overloading-Indexing"
%%%

集合类型的索引记法可以通过定义 {anchorName GetElem}`GetElem` 类型类的实例来重载。
为保持灵活性，{anchorName GetElem}`GetElem` 有四个参数：
 * 集合的类型
 * 索引的类型
 * 从集合中提取出的元素的类型
 * 一个函数，用于确定什么可算作索引在界内的证据

元素类型和证据函数都是输出参数。
{anchorName GetElem}`GetElem` 只有一个方法 {anchorName GetElem}`getElem`，它以一个集合值、一个索引值以及索引在界内的证据作为实参，并返回一个元素：

```anchor GetElem
class GetElem
    (coll : Type)
    (idx : Type)
    (item : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
```

在 {anchorTerm GetElemNEList}`NonEmptyList α` 的情形中，这些参数是：
 * 集合是 {anchorTerm GetElemNEList}`NonEmptyList α`
 * 索引的类型为 {anchorName GetElemNEList}`Nat`
 * 元素的类型是 {anchorName GetElemNEList}`α`
 * 若一个索引小于或等于尾部的长度，则该索引在界内

事实上，{anchorTerm GetElemNEList}`GetElem` 实例可以直接委托给 {anchorTerm GetElemNEList}`NonEmptyList.get`：

```anchor GetElemNEList
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
```
有了这个实例，{anchorTerm GetElemNEList}`NonEmptyList` 就变得与 {moduleName}`List` 一样便于使用。
求值 {anchorTerm firstSpider}`idahoSpiders.head` 得到 {anchorTerm firstSpider}`"Banded Garden Spider"`，而 {anchorTerm tenthSpider}`idahoSpiders[9]` 会导致如下编译时错误：
```anchorError tenthSpider
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ idahoSpiders.inBounds 9
```

由于集合类型和索引类型都是 {anchorTerm ListPosElem}`GetElem` 类型类的输入参数，因此可以使用新的类型来索引既有集合。
正数类型 {anchorTerm ListPosElem}`Pos` 是 {anchorTerm ListPosElem}`List` 的完全合理的索引，只是需要注意它不能指向第一个条目。
下面的 {anchorTerm ListPosElem}`GetElem` 实例允许像使用 {moduleName}`Nat` 一样方便地使用 {anchorTerm ListPosElem}`Pos` 来查找列表条目：

```anchor ListPosElem
instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
```

索引对于非数值索引也可以是有意义的。
例如，{moduleName}`Bool` 可用于在一个点的各字段之间进行选择，其中 {moduleName}`false` 对应于 {anchorTerm PPointBoolGetElem}`x`，而 {moduleName}`true` 对应于 {anchorTerm PPointBoolGetElem}`y`：

```anchor PPointBoolGetElem
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y
```
在这种情况下，两个布尔值都是有效索引。
因为每个可能的 {moduleName}`Bool` 都在界内，所以证据只是为真的命题 {moduleName}`True`。
