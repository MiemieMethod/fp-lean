import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.DB"

#doc (Manual) "实例详解：带类型的查询" =>
%%%
tag := "typed-queries"
file := "Worked-Example___-Typed-Queries"
%%%

当构建一个旨在类似某种其他语言的 API 时，带索引的族非常有用。
它们可用于编写 HTML 构造子库，使其不允许生成无效 HTML；也可用于编码某种配置文件格式的特定规则；还可用于建模复杂的业务约束。
本节描述如何使用带索引的族在 Lean 中编码关系代数的一个子集，作为较简单的技术示范；这些技术可用于构建更强大的数据库查询语言。

该子集使用类型系统来强制字段名互不相交等要求，并使用类型层面的计算将模式反映到查询返回值的类型中。
不过，它并不是一个现实的系统——数据库被表示为链表的链表，类型系统远比 SQL 的类型系统简单，并且关系代数的算子与 SQL 的算子并不真正匹配。
然而，它已经足够大，能够展示有用的原则和技术。

# 数据的一个宇宙
%%%
tag := "typed-query-data-universe"
file := "A-Universe-of-Data"
%%%

在此关系代数中，列中可保存的基础数据可以具有类型 {anchorName DBType}`Int`、{anchorName DBType}`String` 和 {anchorName DBType}`Bool`，并由宇宙 {anchorName DBType}`DBType` 描述：

```anchor DBType
inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
```

使用 {anchorName DBType}`DBType.asType` 可使这些码被用作类型。
例如：
```anchor mountHoodEval
#eval ("Mount Hood" : DBType.string.asType)
```
```anchorInfo mountHoodEval
"Mount Hood"
```

可以比较由这三种数据库类型中的任意一种所描述的值是否相等。
然而，要向 Lean 说明这一点需要一些工作。
直接使用 {anchorName BEqDBType}`BEq` 会失败：
```anchor dbEqNoSplit
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  x == y
```
```anchorError dbEqNoSplit
failed to synthesize
  BEq t.asType

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
正如在嵌套有序对宇宙中一样，类型类搜索不会自动检查 {anchorName dbEqNoSplit}`t` 的值的每一种可能性。
解决方案是使用模式匹配来细化 {anchorTerm dbEq}`x` 和 {anchorName dbEq}`y` 的类型：

```anchor dbEq
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
```
在此函数版本中，{anchorName dbEq}`x` 和 {anchorName dbEq}`y` 在三个相应情形中具有类型 {anchorName DBType}`Int`、{anchorName DBType}`String` 和 {anchorName DBType}`Bool`，而这些类型全都有 {anchorName BEqDBType}`BEq` 实例。
可以使用 {anchorName dbEq}`DBType.beq` 的定义，为由 {anchorName DBType}`DBType` 编码的类型定义一个 {anchorName BEqDBType}`BEq` 实例：

```anchor BEqDBType
instance {t : DBType} : BEq t.asType where
  beq := t.beq
```
这不同于码的实例：

```anchor BEqDBTypeCodes
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
```
前一个实例允许比较取自这些码所描述类型的值，而后一个实例允许比较这些码本身。

可以使用相同技术编写一个 {anchorName ReprAsType}`Repr` 实例。
{anchorName ReprAsType}`Repr` 类的方法称为 {anchorName ReprAsType}`reprPrec`，因为它被设计为在显示值时考虑诸如运算符优先级之类的因素。
通过依值模式匹配细化类型，可以使用 {anchorName DBType}`Int`、{anchorName DBType}`String` 和 {anchorName DBType}`Bool` 的 {anchorName ReprAsType}`Repr` 实例中的 {anchorName ReprAsType}`reprPrec` 方法：

```anchor ReprAsType
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
```

# 模式与表
%%%
tag := "schemas"
file := "Schemas-and-Tables"
%%%

模式描述数据库中每一列的名称和类型：

```anchor Schema
structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column
```
事实上，模式可以被看作描述表中行的一个宇宙。
空模式描述单元类型；只有一列的模式单独描述该值；而至少有两列的模式则由一个元组表示：

```anchor Row
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
```

如 {ref "prod"}[关于乘积类型的开头一节] 中所述，Lean 的乘积类型和元组是右结合的。
这意味着嵌套有序对等价于普通的扁平元组。

表是共享同一模式的行的列表：

```anchor Table
abbrev Table (s : Schema) := List (Row s)
```
例如，登临山峰的日记可以用模式 {anchorName peak}`peak` 表示：

```anchor peak
abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]
```
本书作者曾登临的一组选定山峰表现为一个普通的元组列表：

```anchor mountainDiary
def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]
```
另一个例子由瀑布以及到访它们的日记构成：

```anchor waterfall
abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]
```

```anchor waterfallDiary
def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]
```

## 递归与宇宙再探
%%%
tag := "recursion-universes-revisited"
file := "Recursion-and-Universes___-Revisited"
%%%

将行方便地组织为元组是有代价的：{anchorName Row}`Row` 分别处理其两个基本情形这一事实意味着，在类型中使用 {anchorName Row}`Row` 且通过对码（也就是模式）递归来定义的函数，也需要作出相同区分。
一个会受此影响的例子是相等性检查，它通过对模式递归来定义一个检查行是否相等的函数。
此例不能通过 Lean 的类型检查器：
```anchor RowBEqRecursion
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | col::cols =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
```
```anchorError RowBEqRecursion
Type mismatch
  (v1, r1')
has type
  ?m.10 × ?m.11
but is expected to have type
  Row (col :: cols)
```
问题在于模式 {anchorTerm RowBEqRecursion}`col :: cols` 没有充分细化这些行的类型。
这是因为 Lean 此时尚无法判断匹配到的是 {anchorName Row}`Row` 定义中的单元素模式 {anchorTerm Row}`[col]`，还是 {anchorTerm Row}`col1 :: col2 :: cols` 模式，因此对 {anchorName Row}`Row` 的调用不会计算归约到有序对类型。
解决方案是在 {anchorName RowBEq}`Row.bEq` 的定义中镜像 {anchorName Row}`Row` 的结构：

```anchor RowBEq
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq
```

不同于其他语境，出现在类型中的函数不能仅按其输入/输出行为来理解。
使用这些类型的程序会发现自己被迫镜像类型层面函数所使用的算法，使其结构与该类型的模式匹配和递归行为相一致。
使用依值类型编程的一项重要技能，就是选择具有恰当计算行为的适当类型层面函数。

## 列指针
%%%
tag := "column-pointers"
file := "Column-Pointers"
%%%

有些查询只有在某个模式包含特定列时才有意义。
例如，返回海拔高于 1000 米的山峰的查询，只有在具有一个包含整数的 {anchorTerm peak}`"elevation"` 列的模式语境中才有意义。
表明某列包含在某个模式中的一种方式，是直接提供指向它的指针；而将该指针定义为带索引的族，则可以排除无效指针。

一列可以通过两种方式出现在模式中：要么它位于模式的开头，要么它位于模式中较后的某处。
最终，如果一列位于某个模式中较后的地方，那么它将成为该模式某个尾部的开头。

带索引的族 {anchorName HasCol}`HasCol` 是将该规约翻译为 Lean 代码的结果：

```anchor HasCol
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
```
该族的三个参数分别是模式、列名以及列的类型。
这三者都是指标，但若将参数重新排序，把模式放在列名和类型之后，就可以使名称和类型成为参数。
当模式以列 {anchorTerm HasCol}`⟨name, t⟩` 开头时，可以使用构造子 {anchorName HasCol}`here`；因此，它是指向模式中第一列的指针，并且只能在第一列具有所需名称和类型时使用。
构造子 {anchorName HasCol}`there` 将指向较小模式的指针转换为指向在其上多了一列的模式的指针。

因为 {anchorTerm peak}`"elevation"` 是 {anchorName peak}`peak` 中的第三列，所以可以用 {anchorName HasCol}`there` 跳过前两列来找到它，此后它就是第一列。
换言之，要满足类型 {anchorTerm peakElevationInt}`HasCol peak "elevation" .int`，可使用表达式 {anchorTerm peakElevationInt}`.there (.there .here)`。
理解 {anchorName HasCol}`HasCol` 的一种方式是将其看作某种带有装饰的 {anchorName Naturals}`Nat`：{anchorName Naturals}`zero` 对应于 {anchorName HasCol}`here`，而 {anchorName Naturals}`succ` 对应于 {anchorName HasCol}`there`。
额外的类型信息使得出现差一错误成为不可能。

指向模式中特定列的指针可用于从行中提取该列的值：

```anchor Rowget
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
```
第一步是对模式进行模式匹配，因为这决定了行是元组还是单个值。
不需要为空模式提供情形，因为有一个 {anchorName HasCol}`HasCol` 可用，并且 {anchorName HasCol}`HasCol` 的两个构造子都指定了非空模式。
如果模式只有一列，那么指针必须指向它，因此只需匹配 {anchorName HasCol}`HasCol` 的 {anchorName HasCol}`here` 构造子。
如果模式有两列或更多列，那么必须有一个对应 {anchorName HasCol}`here` 的情形，此时值就是行中的第一个值；还要有一个对应 {anchorName HasCol}`there` 的情形，此时使用递归调用。
因为 {anchorName HasCol}`HasCol` 类型保证该列存在于行中，所以 {anchorName Rowget}`Row.get` 不需要返回 {anchorName nullable}`Option`。

{anchorName HasCol}`HasCol` 扮演两个角色：
 1. 它充当某个具有特定名称和类型的列存在于模式中的_证据_。

 2. 它充当可用于在行中找到与该列关联的值的_数据_。

第一个角色，即证据的角色，类似于命题的使用方式。
指标族 {anchorName HasCol}`HasCol` 的定义可以被解读为：什么算作给定列存在的证据这一规范。
然而，与命题不同，使用了 {anchorName HasCol}`HasCol` 的哪一个构造子是重要的。
在第二个角色中，构造子像 {anchorName Naturals}`Nat` 一样用于在集合中查找数据。
使用指标族编程通常要求能够熟练地在这两种视角之间切换。

## 子模式
%%%
tag := "subschemas"
file := "Subschemas"
%%%

关系代数中的一个重要操作是将表或行_投影_到一个较小的模式。
所有不存在于较小模式中的列都会被遗忘。
为了使投影有意义，较小的模式必须是较大模式的子模式，这意味着较小模式中的每一列都必须存在于较大模式中。
正如 {anchorName HasCol}`HasCol` 使得可以在行中编写不会失败的单列查找一样，将子模式关系表示为指标族，也使得可以编写不会失败的投影函数。

一个模式作为另一个模式的子模式的各种方式，可以定义为一个指标族。
基本思想是：若较小模式中的每一列都出现在较大模式中，则较小模式就是较大模式的子模式。
如果较小模式为空，那么它当然是较大模式的子模式，这由构造子 {anchorName Subschema}`nil` 表示。
如果较小模式有一列，那么该列必须在较大模式中，并且该子模式中的所有其余列也必须构成较大模式的子模式。
这由构造子 {anchorName Subschema}`cons` 表示。

```anchor Subschema
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
```
换言之，{anchorName Subschema}`Subschema` 为较小模式的每一列分配一个 {anchorName HasCol}`HasCol`，该 {anchorName HasCol}`HasCol` 指向它在较大模式中的位置。

模式 {anchorName travelDiary}`travelDiary` 表示 {anchorName peak}`peak` 和 {anchorName waterfall}`waterfall` 共有的字段：

```anchor travelDiary
abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
```
它当然是 {anchorName peak}`peak` 的子模式，如下例所示：

```anchor peakDiarySub
example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))
```
然而，像这样的代码难以阅读，也难以维护。
一种改进方式是指示 Lean 自动写出 {anchorName Subschema}`Subschema` 和 {anchorName HasCol}`HasCol` 构造子。
这可以使用在 {ref "props-proofs-indexing"}[关于命题与证明的插曲]中介绍的策略功能来完成。
该插曲使用 {kw}`by decide` 和 {kw}`by simp` 为各种命题提供证据。

在此语境中，有两个策略是有用的：
 * {kw}`constructor` 策略指示 Lean 使用某个数据类型的构造子来解决问题。
 * {kw}`repeat` 策略指示 Lean 反复重复某个策略，直到该策略失败或证明完成为止。

在下一个例子中，{kw}`by constructor` 的效果与直接写 {anchorName peakDiarySub}`.nil` 相同：

```anchor emptySub
example : Subschema [] peak := by constructor
```
然而，对一个稍微复杂一些的类型尝试同样的策略会失败：
```anchor notDone
example : Subschema [⟨"location", .string⟩] peak := by constructor
```
```anchorError notDone
unsolved goals
case a
⊢ HasCol peak "location" DBType.string

case a
⊢ Subschema [] peak
```
以 {lit}`unsolved goals` 开头的错误描述的是未能完全构造出其本应构造的表达式的策略。
在 Lean 的策略语言中，_目标_是一个类型，策略要在幕后构造适当的表达式来满足它。
在此情形中，{kw}`constructor` 导致 {anchorName SubschemaNames}`Subschema.cons` 被应用，而这两个目标表示 {anchorName Subschema}`cons` 所期望的两个参数。
再添加一个 {kw}`constructor` 实例会使第一个目标（{anchorTerm SubschemaNames}`HasCol peak "location" DBType.string`）由 {anchorName SubschemaNames}`HasCol.there` 来处理，因为 {anchorName peak}`peak` 的第一列不是 {anchorTerm SubschemaNames}`"location"`：
```anchor notDone2
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
```
```anchorError notDone2
unsolved goals
case a.a
⊢ HasCol
  [{ name := "location", contains := DBType.string }, { name := "elevation", contains := DBType.int },
    { name := "lastVisited", contains := DBType.int }]
  "location" DBType.string

case a
⊢ Subschema [] peak
```
然而，添加第三个 {kw}`constructor` 会使第一个目标得到解决，因为 {anchorName SubschemaNames}`HasCol.here` 是适用的：
```anchor notDone3
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
```
```anchorError notDone3
unsolved goals
case a
⊢ Subschema [] peak
```
第四个 {kw}`constructor` 实例解决了 {anchorTerm SubschemaNames}`Subschema peak []` 目标：

```anchor notDone4
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor
```
事实上，不使用策略写出的版本有四个构造子：

```anchor notDone5
example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil
```

与其通过试验来找出应该写多少次 {kw}`constructor`，不如使用 {kw}`repeat` 策略来要求 Lean 只要 {kw}`constructor` 持续取得进展就不断尝试它：

```anchor notDone6
example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
```
这个更灵活的版本也适用于更有意思的 {anchorName Subschema}`Subschema` 问题：

```anchor subschemata
example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor
```

盲目尝试构造子直到某个构造子奏效的方法，对于 {anchorName Naturals}`Nat` 或 {anchorTerm misc}`List Bool` 这样的类型并不十分有用。
毕竟，一个表达式具有类型 {anchorName Naturals}`Nat` 并不意味着它就是_正确的_ {anchorName Naturals}`Nat`。
但是像 {anchorName HasCol}`HasCol` 和 {anchorName Subschema}`Subschema` 这样的类型受到其指标的充分约束，以至于永远只有一个构造子适用；这意味着程序本身的内容不那么有意思，而计算机可以选出正确的那个。

如果一个模式是另一个模式的子模式，那么它也是在该较大模式上扩展一个额外列之后所得模式的子模式。
这一事实可以用函数定义来刻画。
{anchorName SubschemaAdd}`Subschema.addColumn` 接受 {anchorName SubschemaAdd}`smaller` 是 {anchorName SubschemaAdd}`bigger` 的子模式这一证据，然后返回 {anchorName SubschemaAdd}`smaller` 是 {anchorTerm SubschemaAdd}`c :: bigger` 的子模式这一证据，也就是说，返回 {anchorName SubschemaAdd}`bigger` 加上一个额外列后的证据：

```anchor SubschemaAdd
def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn
```
子模式描述了在较大模式中何处找到较小模式中的每一列。
{anchorName SubschemaAdd}`Subschema.addColumn` 必须将这些描述从原来的较大模式转换到扩展后的较大模式。
在 {anchorName Subschema}`nil` 情形中，较小模式是 {lit}`[]`，而 {anchorName Subschema}`nil` 也是 {lit}`[]` 是 {anchorTerm SubschemaAdd}`c :: bigger` 的子模式的证据。
在 {anchorName Subschema}`cons` 情形中，它描述了如何把 {anchorName SubschemaAdd}`smaller` 中的一列放入 {anchorName SubschemaAdd}`bigger`；该列的位置需要用 {anchorName HasCol}`there` 调整，以考虑新增列 {anchorName SubschemaAdd}`c`，并且递归调用会调整其余列。

理解 {anchorName Subschema}`Subschema` 的另一种方式是：它定义了两个模式之间的一个_关系_——存在类型为 {anchorTerm misc}`Subschema smaller bigger` 的表达式，意味着 {anchorTerm misc}`(smaller, bigger)` 处于该关系中。
该关系是自反的，意思是每个模式都是其自身的子模式：

```anchor SubschemaSame
def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn
```


## 投影行
%%%
tag := "projecting-rows"
file := "Projecting-Rows"
%%%

给定 {anchorName RowProj}`s'` 是 {anchorName RowProj}`s` 的子模式这一证据，{anchorName RowProj}`s` 中的一行可以被投影为 {anchorName RowProj}`s'` 中的一行。
这是通过使用 {anchorName RowProj}`s'` 是 {anchorName RowProj}`s` 的子模式这一证据完成的，该证据说明了 {anchorName RowProj}`s'` 的每一列在 {anchorName RowProj}`s` 中何处找到。
{anchorName RowProj}`s'` 中的新行通过从旧行中的适当位置取回值，逐列构造出来。

执行此投影的函数 {anchorName RowProj}`Row.project` 有三个情形，对应于 {anchorName RowProj}`Row` 本身的每个情形。
它将 {anchorName Rowget}`Row.get` 与 {anchorName RowProj}`Subschema` 参数中的每个 {anchorName HasCol}`HasCol` 一起使用，以构造投影后的行：

```anchor RowProj
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
```


# 条件与选择
%%%
tag := "conditions-and-selection"
file := "Conditions-and-Selection"
%%%

投影会从表中移除不需要的列，但查询还必须能够移除不需要的行。
这一操作称为_选择_。
选择依赖于具备某种表达哪些行是所需行的手段。

示例查询语言包含表达式，它们类似于 SQL 的 {lit}`WHERE` 子句中可以写出的内容。
表达式由指标族 {anchorName DBExpr}`DBExpr` 表示。
因为表达式可以引用数据库中的列，但不同的子表达式全都具有相同的模式，所以 {anchorName DBExpr}`DBExpr` 将数据库模式作为参数。
此外，每个表达式都有一个类型，而这些类型会变化，因此它是一个指标：

```anchor DBExpr
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t
```
{anchorName DBExpr}`col` 构造子表示对数据库中某列的引用。
{anchorName DBExpr}`eq` 构造子比较两个表达式是否相等，{anchorName DBExpr}`lt` 检查一个表达式是否小于另一个表达式，{anchorName DBExpr}`and` 是布尔合取，而 {anchorName DBExpr}`const` 是某个类型的常量值。

例如，{anchorName peak}`peak` 中的一个表达式若要检查 {lit}`elevation` 列是否大于 1000 且位置是否为 {anchorTerm mountainDiary}`"Denmark"`，可以写作：

```anchor tallDk
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
```
这有些冗长。
特别是，对列的引用包含对 {anchorTerm tallDk}`by repeat constructor` 的样板调用。
Lean 中一种称为_宏_的功能可以通过消除这些样板代码来帮助提高表达式的可读性：

```anchor cBang
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
```
此声明向 Lean 添加了 {kw}`c!` 关键字，并指示 Lean 将任何后接表达式的 {kw}`c!` 实例替换为相应的 {anchorTerm cBang}`DBExpr.col` 构造。
这里，{anchorName cBang}`term` 表示 Lean 表达式，而不是命令、策略或语言的其他部分。
Lean 宏有点类似于 C 预处理器宏，但它们更好地集成到语言中，并且会自动避免 CPP 的一些陷阱。
事实上，它们与 Scheme 和 Racket 中的宏关系非常密切。

借助此宏，该表达式可以易读得多：

```anchor tallDkBetter
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))
```

在给定行的上下文中求表达式的值时，使用 {anchorName Rowget}`Row.get` 提取列引用，并将所有其他表达式委托给 Lean 对值的操作来处理：

```anchor DBExprEval
def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
```

对哥本哈根地区最高的山丘 Valby Bakke 求该表达式的值，得到 {anchorName misc}`false`，因为 Valby Bakke 的海拔远低于 1 千米：
```anchor valbybakke
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
```
```anchorInfo valbybakke
false
```
对一座虚构的海拔为 1230m 的山求该表达式的值，得到 {anchorName misc}`true`：
```anchor fakeDkBjerg
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
```
```anchorInfo fakeDkBjerg
true
```
对美国爱达荷州最高峰求该表达式的值，得到 {anchorName misc}`false`，因为爱达荷州不属于丹麦：
```anchor borah
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)
```
```anchorInfo borah
false
```

# 查询
%%%
tag := "typed-query-language"
file := "Queries"
%%%

该查询语言基于关系代数。
除表之外，它还包含以下运算符：
 1. 两个具有相同模式的表达式的并集，将两个查询所得的行合并起来
 2. 两个具有相同模式的表达式的差集，从第一个结果中的行移除第二个结果中出现的行
 3. 按某个准则进行选择，即根据一个表达式过滤查询结果
 4. 投影到一个子模式，从查询结果中移除若干列
 5. 笛卡儿积，将一个查询中的每一行与另一个查询中的每一行组合起来
 6. 重命名查询结果中的一列，这会修改其模式
 7. 给查询中的所有列名加上一个前缀

最后一个运算符并非严格必要，但它使该语言使用起来更加方便。

同样，查询由一个索引族表示：

```anchor Query
inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
  | project :
    Query s → (s' : Schema) →
    Subschema s' s →
    Query s'
  | product :
    Query s1 → Query s2 →
    disjoint (s1.map Column.name) (s2.map Column.name) →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) →
    !((s.map Column.name).contains n') →
    Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map fun c => {c with name := n ++ "." ++ c.name})
```
{anchorName Query}`select` 构造子要求用于选择的表达式返回一个布尔值。
{anchorName Query}`product` 构造子的类型包含一次对 {anchorName Query}`disjoint` 的调用，这确保两个模式不共享任何名称：

```anchor disjoint
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)
```
在期望类型的位置使用类型为 {anchorName misc}`Bool` 的表达式，会触发从 {anchorName misc}`Bool` 到 {anchorTerm misc}`Prop` 的强制类型转换。
正如可判定命题可以被视为布尔值，其中该命题的证据被强制转换为 {anchorName misc}`true`，而该命题的反驳被强制转换为 {anchorName misc}`false`，布尔值也会被强制转换为一个命题，该命题陈述此表达式等于 {anchorName misc}`true`。
由于该库的所有使用都预期发生在模式已预先给定的上下文中，此命题可以用 {kw}`by simp` 证明。
类似地，{anchorName renameColumn}`renameColumn` 构造子会检查新名称在模式中尚不存在。
它使用辅助函数 {anchorName renameColumn}`Schema.renameColumn` 来改变 {anchorName HasCol}`HasCol` 所指向的列的名称：

```anchor renameColumn
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
```

# 执行查询
%%%
tag := "executing-queries"
file := "Executing-Queries"
%%%

执行查询需要若干辅助函数。
查询的结果是一张表；这意味着查询语言中的每个操作都需要一个作用于表的相应实现。

## 笛卡儿积
%%%
tag := "executing-cartesian-product"
file := "Cartesian-Product"
%%%

取两张表的笛卡儿积，是通过将第一张表中的每一行追加到第二张表中的每一行来完成的。
首先，由于 {anchorName Row}`Row` 的结构，向一行添加单列需要对其模式进行模式匹配，以确定结果将是一个裸值还是一个元组。
因为这是常见操作，将该模式匹配分解到一个辅助函数中会很方便：

```anchor addVal
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
```
追加两行同时按第一个模式和第一行的结构递归，因为行的结构与模式的结构同步推进。
当第一行为空时，追加返回第二行。
当第一行是单元素行时，将该值添加到第二行。
当第一行包含多列时，将第一列的值添加到对该行其余部分递归所得的结果中。

```anchor RowAppend
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
```

标准库中的 {anchorName ListFlatMap}`List.flatMap` 会把一个自身返回列表的函数应用于输入列表中的每个条目，并返回按顺序追加所得列表后的结果：

```anchor ListFlatMap
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
```
其类型签名表明 {anchorName ListFlatMap}`List.flatMap` 可用于实现一个 {anchorTerm ListMonad}`Monad List` 实例。
事实上，{anchorName ListFlatMap}`List.flatMap` 与 {anchorTerm ListMonad}`pure x := [x]` 一起确实实现了一个单子。
然而，它并不是一个很有用的 {anchorName ListMonad}`Monad` 实例。
{anchorName ListMonad}`List` 单子基本上是 {anchorName Many (module:=Examples.Monads.Many)}`Many` 的一个版本，它会在用户有机会请求某个数量的值之前，预先探索搜索空间中的_每一条_可能路径。
由于这个性能陷阱，通常不宜为 {anchorName ListMonad}`List` 定义 {anchorName ListMonad}`Monad` 实例。
然而在这里，查询语言没有用于限制返回结果数量的运算符，因此组合所有可能性正是所期望的行为：

```anchor TableCartProd
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
```

正如 {anchorName ListProduct (module:=Examples.DependentTypes.Finite)}`List.product` 一样，身份单子中带有可变状态的循环也可用作另一种实现技术：

```anchor TableCartProdOther
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse
```


## 差集
%%%
tag := "executing-difference"
file := "Difference"
%%%

从表中移除不需要的行可以使用 {anchorName misc}`List.filter` 完成，它接受一个列表和一个返回 {anchorName misc}`Bool` 的函数。
返回的新列表只包含使该函数返回 {anchorName misc}`true` 的条目。
例如，
```anchorTerm filterA
["Willamette", "Columbia", "Sandy", "Deschutes"].filter (·.length > 8)
```
求值得到
```anchorTerm filterA
["Willamette", "Deschutes"]
```
因为 {anchorTerm filterA}`"Columbia"` 和 {anchorTerm filterA}`"Sandy"` 的长度小于或等于 {anchorTerm filterA}`8`。
可以使用辅助函数 {anchorName ListWithout}`List.without` 来移除表中的条目：

```anchor ListWithout
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)
```
在解释查询时，这将与 {anchorName Row}`Row` 的 {anchorName BEqDBType}`BEq` 实例一起使用。

## 重命名列
%%%
tag := "executing-renaming-columns"
file := "Renaming-Columns"
%%%
重命名一行中的列，是用一个递归函数遍历该行，直到找到所讨论的列；此时，具有新名称的列获得与具有旧名称的列相同的值：

```anchor renameRow
def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)
```
虽然此函数改变了其参数的_类型_，但实际返回值所包含的数据与原参数完全相同。
从运行时角度看，{anchorName renameRow}`Row.rename` 不过是一个缓慢的恒等函数。
使用索引族编程的一个困难在于，当性能很重要时，这类操作可能会造成妨碍。
要消除这些“重新索引”函数，需要非常谨慎且常常较为脆弱的设计。

## 给列名加前缀
%%%
tag := "executing-prefixing-column-names"
file := "Prefixing-Column-Names"
%%%

给列名添加前缀与重命名列非常相似。
不同的是，{anchorName prefixRow}`prefixRow` 不能前进到某个目标列后就返回，而必须处理所有列：

```anchor prefixRow
def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)
```
这可以与 {anchorName misc}`List.map` 一起使用，以便给表中的所有行添加前缀。
同样，此函数的存在只是为了改变一个值的类型。

## 组合各个部分
%%%
tag := "query-exec-runner"
file := "Putting-the-Pieces-Together"
%%%

定义完所有这些辅助函数后，执行查询只需要一个简短的递归函数：

```anchor QueryExec
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q e => exec q |>.filter e.evaluate
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow
```
构造子的某些参数在执行期间不会使用。
特别是，构造子 {anchorName Query}`project` 和函数 {anchorName RowProj}`Row.project` 都将较小的模式作为显式参数，但该模式是较大模式的子模式这一_证据_的类型包含了足够信息，使 Lean 能够自动填充该参数。
类似地，{anchorName Query}`product` 构造子所要求的两张表具有互不相交的列名这一事实，对于 {anchorName TableCartProd}`Table.cartesianProduct` 并不需要。
一般而言，依值类型提供了许多机会，使 Lean 能够代表程序员填充参数。

对查询结果使用点记法，可以调用在 {lit}`Table` 和 {lit}`List` 命名空间中定义的函数，例如 {anchorName misc}`List.map`、{anchorName misc}`List.filter` 和 {anchorName TableCartProd}`Table.cartesianProduct`。
这之所以可行，是因为 {anchorName Table}`Table` 是使用 {kw}`abbrev` 定义的。
就像类型类搜索一样，点记法可以穿透由 {kw}`abbrev` 创建的定义。

{anchorName Query}`select` 的实现也相当简洁。
执行查询 {anchorName selectCase}`q` 后，使用 {anchorName misc}`List.filter` 移除不满足该表达式的行。
{anchorName misc}`List.filter` 期望一个从 {anchorTerm Table}`Row s` 到 {anchorName misc}`Bool` 的函数，但 {anchorName DBExprEval}`DBExpr.evaluate` 的类型是 {anchorTerm DBExprEvalType}`Row s → DBExpr s t → t.asType`。
由于 {anchorName Query}`select` 构造子的类型要求该表达式具有类型 {anchorTerm Query}`DBExpr s .bool`，在此上下文中 {anchorTerm DBExprEvalType}`t.asType` 实际上就是 {anchorName misc}`Bool`。

一个查找所有海拔超过 500 米的山峰高度的查询可以写为：

```anchor Query1
open Query in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (c! "elevation")) |>.project
  [⟨"elevation", .int⟩] (by repeat constructor)
```

执行它会返回预期的整数列表：
```anchor Query1Exec
#eval example1.exec
```
```anchorInfo Query1Exec
[3637, 1519, 2549]
```

为了规划观光游览，将同一地点的所有山峰和瀑布配对可能是有意义的。
这可以通过取两张表的笛卡儿积、只选择其中位置相等的行，然后投影出名称来完成：

```anchor Query2
open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
由于示例数据只包含美国的瀑布，执行该查询会返回美国境内的山峰和瀑布配对：
```anchor Query2Exec
#eval example2.exec
```
```anchorInfo Query2Exec
[("Mount Nebo", "Multnomah Falls"), ("Mount Nebo", "Shoshone Falls"), ("Moscow Mountain", "Multnomah Falls"),
  ("Moscow Mountain", "Shoshone Falls"), ("Mount St. Helens", "Multnomah Falls"),
  ("Mount St. Helens", "Shoshone Falls")]
```

## 你可能遇到的错误
%%%
tag := "typed-queries-error-messages"
file := "Errors-You-May-Meet"
%%%


许多潜在错误都被 {anchorName Query}`Query` 的定义排除了。
例如，若忘记 {anchorTerm Query2}`"mountain.location"` 中添加的限定符，会产生一个编译时错误，并高亮显示列引用 {anchorTerm QueryOops1}`c! "location"`：
```anchor QueryOops1
open Query in
def example2 :=
  let mountains := table mountainDiary |>.prefixWith "mountain"
  let waterfalls := table waterfallDiary |>.prefixWith "waterfall"
  mountains.product waterfalls (by simp)
    |>.select (.eq (c! "location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
这是极好的反馈！
另一方面，错误消息的文本却很难据此采取行动：
```anchorError QueryOops1
unsolved goals
case a.a.a.a.a.a.a
mountains : Query (List.map (fun c => { name := "mountain" ++ "." ++ c.name, contains := c.contains }) peak) := ⋯
waterfalls : Query (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) waterfall) := ⋯
⊢ HasCol (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) []) "location" ?m.62066
```

类似地，若忘记给两张表的名称添加前缀，会在 {kw}`by decide` 处产生错误；这里本应提供证据，表明这些模式事实上互不相交：
```anchor QueryOops2
open Query in
def example2 :=
  let mountains := table mountainDiary
  let waterfalls := table waterfallDiary
  mountains.product waterfalls (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
这条错误消息更有帮助：
```anchorError QueryOops2
Tactic `decide` proved that the proposition
  disjoint (List.map Column.name peak) (List.map Column.name waterfall) = true
is false
```

Lean 的宏系统包含了所需的一切，不仅能为查询提供方便的语法，还能安排生成有帮助的错误消息。
遗憾的是，描述如何用 Lean 宏实现语言超出了本书范围。
像 {anchorName Query}`Query` 这样的索引族，作为有类型数据库交互库的核心或许最合适，而不是作为其用户界面。

# 练习
%%%
tag := "typed-query-exercises"
file := "Exercises"
%%%

## 日期
%%%
tag := none
file := "Dates"
%%%

定义一个表示日期的结构。将其加入 {anchorName DBExpr}`DBType` 宇宙，并相应地更新其余代码。提供看起来必要的额外 {anchorName DBExpr}`DBExpr` 构造子。

## 可空类型
%%%
tag := none
file := "Nullable-Types"
%%%

通过用以下结构表示数据库类型，为查询语言添加对可空列的支持：
```anchor nullable
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
```

在 {anchorName Schema}`Column` 和 {anchorName DBExpr}`DBExpr` 中用此类型替代 {anchorName DBExpr}`DBType`，并查阅 SQL 关于 {lit}`NULL` 和比较运算符的规则，以确定 {anchorName DBExpr}`DBExpr` 的构造子的类型。

## 试验策略
%%%
tag := none
file := "Experimenting-with-Tactics"
%%%


要求 Lean 使用 {kw}`by repeat constructor` 查找以下类型的值，其结果是什么？解释为什么每个都会得到相应的结果。
 * {anchorName Naturals}`Nat`
 * {anchorTerm misc}`List Nat`
 * {anchorTerm misc}`Vect Nat 4`

 * {anchorTerm misc}`Row []`
 * {anchorTerm misc}`Row [⟨"price", .int⟩]`
 * {anchorTerm misc}`Row peak`
 * {anchorTerm misc}`HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int`
