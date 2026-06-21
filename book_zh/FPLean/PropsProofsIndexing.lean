import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Props"

set_option pp.rawOnError true

#doc (Manual) "插曲：命题、证明与索引" =>
%%%
tag := "props-proofs-indexing"
number := false
htmlSplit := .never
file := "Interlude___-Propositions___-Proofs___-and-Indexing"
%%%

与许多语言一样，Lean 使用方括号对数组和列表进行索引。
例如，如果 {moduleTerm}`woodlandCritters` 定义如下：

```anchor woodlandCritters
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
```

于是可以提取各个组成部分：

```anchor animals
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
```

然而，尝试提取第四个元素会导致编译期错误，而不是运行时错误：

```anchor outOfBounds
def oops := woodlandCritters[3]
```

```anchorError outOfBounds
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < woodlandCritters.length
```

这个错误消息表示，Lean 曾尝试自动地从数学上证明 {moduleTerm}`3 < woodlandCritters.length`（即 {moduleTerm}`3 < List.length woodlandCritters`），这将意味着该查找是安全的，但它未能做到。
越界错误是一类常见的缺陷，而 Lean 利用其作为编程语言和定理证明器的双重性质，尽可能多地排除这类错误。

理解其工作方式需要理解三个关键概念：命题、证明和策略。

# 命题与证明
%%%
tag := "propositions-and-proofs"
file := "Propositions-and-Proofs"
%%%

_命题_ 是可以为真或为假的陈述。
以下所有英文句子都是命题：

 * $`1 + 1 = 2`
 * 加法满足交换律。
 * 存在无限多个素数。
 * $`1 + 1 = 15`
 * 巴黎是法国的首都。
 * 布宜诺斯艾利斯是韩国的首都。
 * 所有鸟都会飞。

另一方面，无意义的陈述不是命题。
尽管在语法上成立，以下这些都不是命题：

 * 1 + green = ice cream
 * 所有首都都是素数。
 * 至少有一个 gorg 是 fleep。

命题有两类：一类是纯数学的，只依赖于我们对概念的定义；另一类是关于现实世界的事实。
像 Lean 这样的定理证明器关注前一类，而对于企鹅的飞行能力或城市的法律地位则无话可说。

_证明_是说明一个命题为真的有说服力的论证。
对于数学命题，这些论证会使用所涉及概念的定义以及逻辑论证的规则。
大多数证明是写给人理解的，并省略了许多繁琐细节。
像 Lean 这样的计算机辅助定理证明器被设计为允许数学家在省略许多细节的同时书写证明，而由软件负责补全缺失的显式步骤。
这些步骤可以被机械地检查。
这降低了疏漏或错误发生的可能性。

在 Lean 中，程序的类型描述了可以与该程序交互的方式。
例如，类型为 {moduleTerm}`Nat → List String` 的程序是一个函数，它接受一个 {moduleTerm}`Nat` 参数并产生一个字符串列表。
换言之，每个类型都规定了什么样的程序算作具有该类型的程序。

在 Lean 中，命题事实上是类型。
它们规定了什么可算作该陈述为真的证据。
通过提供这种证据来证明命题，而该证据由 Lean 检查。
另一方面，如果命题为假，则构造这种证据将是不可能的。

例如，命题 $`1 + 1 = 2` 可以直接在 Lean 中写出。
该命题的证据是构造子 {moduleTerm}`rfl`，它是 _reflexivity_ 的缩写。
在数学中，如果一个关系使每个元素都与其自身相关，则称该关系是_自反的_；这是为了拥有合理的相等概念所需的基本条件。
因为 {moduleTerm}`1 + 1` 计算为 {moduleTerm}`2`，所以它们实际上是同一个东西：

```anchor onePlusOneIsTwo
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
```

另一方面，{moduleTerm}`rfl` 并不能证明假命题 $`1 + 1 = 15`：

```anchor onePlusOneIsFifteen
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
```

```anchorError onePlusOneIsFifteen
Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  1 + 1 = 15
```

这个错误消息表明，当等式陈述的两边已经是同一个数时，{moduleTerm}`rfl` 可以证明这两个表达式相等。
因为 {moduleTerm}`1 + 1` 会直接求值为 {moduleTerm}`2`，它们被认为是相同的，这使得 {moduleTerm}`onePlusOneIsTwo` 能够被接受。
正如 {moduleTerm}`Type` 描述表示数据结构和函数的类型，例如 {moduleTerm}`Nat`、{moduleTerm}`String` 和 {moduleTerm}`List (Nat × String × (Int → Float))`，{moduleTerm}`Prop` 描述命题。

当一个命题已被证明时，它称为一个_定理_。
在 Lean 中，按照惯例会使用 {kw}`theorem` 关键字而不是 {kw}`def` 来声明定理。
这有助于读者看出哪些声明意在被解读为数学证明，哪些是定义。
一般而言，对于证明，重要的是存在某个命题为真的证据，而具体提供的是_哪一个_证据并不特别重要。
另一方面，对于定义，所选择的具体值则非常重要——毕竟，一个总是返回 {anchorTerm SomeNats}`0` 的加法定义显然是错误的。
由于证明的细节对于后续证明并不重要，使用 {kw}`theorem` 关键字使 Lean 编译器能够获得更大的并行性。

前面的例子可以改写如下：

```anchor onePlusOneIsTwoProp
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
```


# 策略
%%%
tag := "tactics"
file := "Tactics"
%%%

证明通常使用_策略_来书写，而不是直接提供证据。
策略是构造某个命题的证据的小程序。
这些程序在一个_证明状态_中运行，该状态跟踪待证明的陈述（称为_目标_）以及可用于证明它的假设。
在一个目标上运行策略会产生一个包含新目标的新证明状态。
当所有目标都已被证明时，证明就完成了。

要用策略写证明，请以 {kw}`by` 开始定义。
写下 {kw}`by` 会使 Lean 进入策略模式，直到下一个缩进代码块结束。
在策略模式中，Lean 会持续提供关于当前证明状态的反馈。
用策略写出时，{anchorTerm onePlusOneIsTwoTactics}`onePlusOneIsTwo` 仍然相当简短：

```anchor onePlusOneIsTwoTactics
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide
```

{tactic}`decide` 策略会调用一个_判定过程_，即一个能够检查某个陈述是真还是假的程序，并在任一情况下返回合适的证明。
它主要用于处理像 {anchorTerm SomeNats}`1` 和 {anchorTerm SomeNats}`2` 这样的具体值。
本书中其他重要的策略是 {tactic}`simp`，它是“simplify”的缩写，以及 {tactic}`grind`，后者能够自动证明许多定理。

策略之所以有用，有若干原因：
 1. 许多证明若写到最细微的细节，会既复杂又繁琐，而策略可以自动化这些无趣的部分。
 2. 用策略写出的证明随着时间推移更易于维护，因为灵活的自动化可以掩盖定义中的小改动。
 3. 由于单个策略可以证明许多不同的定理，Lean 可以在幕后使用策略，使用户不必手工书写证明。例如，数组查找需要一个关于索引在界内的证明，而策略通常可以构造该证明，用户无需为此操心。

在幕后，索引记法使用一个策略来证明用户的查找操作是安全的。
该策略会考虑许多关于算术的事实，并将它们与任何局部已知的事实结合起来，尝试证明索引在边界内。

{tactic}`simp` 策略是 Lean 证明中的主力工具。
它将目标改写为尽可能简单的形式。
在许多情况下，这种改写会把陈述简化到足以自动证明的程度。
在幕后会构造一个详细的形式化证明，但使用 {tactic}`simp` 会隐藏这种复杂性。

与 {tactic}`decide` 类似，{tactic}`grind` 策略用于完成证明。
它使用来自 SMT 求解器的一组技术，能够证明种类广泛的定理。
与 {tactic}`simp` 不同，{tactic}`grind` 若不能完整完成证明，就绝不会朝证明取得部分进展；它要么完全成功，要么失败。
{tactic}`grind` 策略非常强大、可定制且可扩展；由于这种能力和灵活性，当它无法证明一个定理时，其输出包含大量信息，可以帮助受过训练的 Lean 用户诊断失败原因。
这在入门时可能令人难以承受，因此本章只使用 {tactic}`decide` 和 {tactic}`simp`。

# 联结词
%%%
tag := "connectives"
file := "Connectives"
%%%

逻辑的基本构件，例如“与”、“或”、“真”、“假”和“非”，称为{deftech}_逻辑联结词_。
每个联结词都定义了什么算作其为真的证据。
例如，要证明命题“_A_ 且 _B_”，就必须同时证明 _A_ 和 _B_。
这意味着“_A_ 且 _B_”的证据是一个序对，其中同时包含 _A_ 的证据和 _B_ 的证据。
类似地，“_A_ 或 _B_”的证据由 _A_ 的证据或 _B_ 的证据之一构成。

特别地，这些连接词大多像数据类型一样定义，并且它们具有构造子。
如果 {anchorTerm AndProp}`A` 和 {anchorTerm AndProp}`B` 是命题，那么“{anchorTerm AndProp}`A` 且 {anchorTerm AndProp}`B`”（写作 {anchorTerm AndProp}`A ∧ B`）也是一个命题。
{anchorTerm AndProp}`A ∧ B` 的证据由构造子 {anchorTerm AndIntro}`And.intro` 构成，该构造子的类型为 {anchorTerm AndIntro}`A → B → A ∧ B`。
将 {anchorTerm AndIntro}`A` 和 {anchorTerm AndIntro}`B` 替换为具体命题后，可以用 {anchorTerm AndIntroEx}`And.intro rfl rfl` 证明 {anchorTerm AndIntroEx}`1 + 1 = 2 ∧ "Str".append "ing" = "String"`。
当然，{tactic}`decide` 也足够强大，能够找到这个证明：

```anchor AndIntroExTac
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide
```


类似地，“{anchorTerm OrProp}`A` 或 {anchorTerm OrProp}`B`”（写作 {anchorTerm OrProp}`A ∨ B`）有两个构造子，因为“{anchorTerm OrProp}`A` 或 {anchorTerm OrProp}`B`”的一个证明只要求两个底层命题中有一个为真。
有两个构造子：{anchorTerm OrIntro1}`Or.inl`，其类型为 {anchorTerm OrIntro1}`A → A ∨ B`；以及 {anchorTerm OrIntro2}`Or.inr`，其类型为 {anchorTerm OrIntro2}`B → A ∨ B`。

蕴含（若 {anchorTerm impliesDef}`A` 则 {anchorTerm impliesDef}`B`）用函数表示。
特别地，一个将 {anchorTerm impliesDef}`A` 的证据转换为 {anchorTerm impliesDef}`B` 的证据的函数，本身就是 {anchorTerm impliesDef}`A` 蕴含 {anchorTerm impliesDef}`B` 的证据。
这不同于通常对蕴含的描述，在通常描述中 {anchorTerm impliesDef}`A → B` 是 {anchorTerm impliesDef}`¬A ∨ B` 的简写，但这两种表述是等价的。

由于“且”的证据是一个构造子，因此它可以与模式匹配一起使用。
例如，一个证明 {anchorTerm andImpliesOr}`A` 且 {anchorTerm andImpliesOr}`B` 蕴含 {anchorTerm andImpliesOr}`A` 或 {anchorTerm andImpliesOr}`B` 的证明，是这样一个函数：它从 {anchorTerm andImpliesOr}`A` 和 {anchorTerm andImpliesOr}`B` 的证据中取出 {anchorTerm andImpliesOr}`A` 的证据（或 {anchorTerm andImpliesOr}`B` 的证据），然后使用此证据产生 {anchorTerm andImpliesOr}`A` 或 {anchorTerm andImpliesOr}`B` 的证据：

```anchor andImpliesOr
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a
```


:::table +header
*
  - 联结词
  - Lean 语法
  - 证据
*
 -  真
 -  {anchorName connectiveTable}`True`
 -  {anchorTerm connectiveTable}`True.intro : True`

*
 -  假
 -  {anchorName connectiveTable}`False`
 -  无证据

*
 -  {anchorName connectiveTable}`A` 且 {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∧ B`
 -  {anchorTerm connectiveTable}`And.intro : A → B → A ∧ B`

*
 -  {anchorName connectiveTable}`A` 或 {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∨ B`
 -  或者 {anchorTerm connectiveTable}`Or.inl : A → A ∨ B`，或者 {anchorTerm connectiveTable}`Or.inr : B → A ∨ B`

*
 -  {anchorName connectiveTable}`A` 蕴含 {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A → B`
 -  一个将 {anchorName connectiveTable}`A` 的证据转换为 {anchorName connectiveTable}`B` 的证据的函数

*
 -  非 {anchorName connectiveTable}`A`
 -  {anchorTerm connectiveTable}`¬A`
 -  一个会将 {anchorName connectiveTable}`A` 的证据转换为 {anchorName connectiveTable}`False` 的证据的函数


:::

{tactic}`decide` 策略可以证明使用这些联结词的定理。
例如：

```anchor connectivesD
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide
```


# 作为参数的证据
%%%
tag := "evidence-passing"
file := "Evidence-as-Arguments"
%%%

在某些情况下，安全地索引列表要求该列表具有某个最小长度，但列表本身是一个变量而不是具体值。
为了使这一查找安全，必须有某种证据表明该列表足够长。
使索引安全的最简单方法之一，是让执行数据结构查找的函数把所需的安全性证据作为参数。
例如，返回列表中第三个条目的函数通常并不安全，因为列表可能包含零个、一个或两个条目：

```anchor thirdErr
def third (xs : List α) : α := xs[2]
```

```anchorError thirdErr
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.5379
xs : List α
⊢ 2 < xs.length
```

然而，可以通过添加一个由索引操作安全性的证据构成的参数，把证明该列表至少有三个条目的义务强加给调用者：

```anchor third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
```

在此例中，{anchorTerm third}`xs.length > 2` 不是一个检查 {anchorTerm third}`xs` _是否_有多于 2 个条目的程序。
它是一个可能为真也可能为假的命题，而参数 {anchorTerm third}`ok` 必须是它为真的证据。

当函数在一个具体列表上被调用时，其长度是已知的。
在这些情况下，{anchorTerm thirdCritters}`by decide` 可以自动构造证据：

```anchor thirdCritters
#eval third woodlandCritters (by decide)
```

```anchorInfo thirdCritters
"snail"
```


# 无证据索引
%%%
tag := "indexing-without-evidence"
file := "Indexing-Without-Evidence"
%%%

在不便证明索引操作位于边界内的情况下，还有其他替代方案。
添加一个问号会得到一个 {anchorName thirdOption}`Option`，其中如果索引在边界内，结果就是 {anchorName OptionNames}`some`，否则就是 {anchorName OptionNames}`none`。
例如：


```anchor thirdOption
def thirdOption (xs : List α) : Option α := xs[2]?
```

```anchor thirdOptionCritters
#eval thirdOption woodlandCritters
```

```anchorInfo thirdOptionCritters
some "snail"
```

```anchor thirdOptionTwo
#eval thirdOption ["only", "two"]
```

```anchorInfo thirdOptionTwo
none
```

:::paragraph
还有一个版本会在索引越界时使程序崩溃，而不是返回一个 {moduleTerm}`Option`：

```anchor crittersBang
#eval woodlandCritters[1]!
```

```anchorInfo crittersBang
"deer"
```
:::


# 你可能遇到的消息
%%%
tag := "props-proofs-indexing-messages"
file := "Messages-You-May-Meet"
%%%
除了证明某个陈述为真之外，{anchorTerm thirdRabbitErr}`decide` 策略还可以证明它为假。
当要求证明一个单元素列表具有多于两个元素时，它会返回一个错误，表明该陈述确实为假：

```anchor thirdRabbitErr
#eval third ["rabbit"] (by decide)
```


```anchorError thirdRabbitErr
Tactic `decide` proved that the proposition
  ["rabbit"].length > 2
is false
```


{tactic}`simp` 和 {tactic}`decide` 策略不会自动展开带有 {kw}`def` 的定义。
尝试使用 {anchorTerm onePlusOneIsStillTwo}`simp` 证明 {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo` 会失败：

```anchor onePlusOneIsStillTwo
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
```

错误消息只是说明它无能为力，因为若不展开 {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo`，就无法取得任何进展：

```anchorError onePlusOneIsStillTwo
`simp` made no progress
```

使用 {anchorTerm onePlusOneIsStillTwo2}`decide` 也会失败：

```anchor onePlusOneIsStillTwo2
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
```

这也是因为它没有展开 {anchorName onePlusOneIsStillTwo2}`OnePlusOneIsTwo`：

```anchorError onePlusOneIsStillTwo2
failed to synthesize
  Decidable OnePlusOneIsTwo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

用 {ref "abbrev-vs-def"}[{kw}`abbrev` 可解决此问题] 定义 {anchorName onePlusOneIsStillTwo}`OnePlusOneIsTwo`，可以通过将该定义标记为可展开来解决这个问题。

除了当 Lean 无法找到索引操作安全的编译期证据时发生的错误之外，使用不安全索引的多态函数还可能产生以下消息：

```anchor unsafeThird
def unsafeThird (xs : List α) : α := xs[2]!
```


```anchorError unsafeThird
failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

这是由于一项技术性限制；该限制是为了使 Lean 既可用作证明定理的逻辑，又可用作编程语言。
特别地，只有其类型至少包含一个值的程序才允许崩溃。
这是因为 Lean 中的命题是一种类型，用于分类其为真的证据。
假命题没有这样的证据。
如果一个具有空类型的程序可以崩溃，那么这个崩溃的程序就可以被用作假命题的一种伪造证据。

在内部，Lean 包含一张类型表，其中列出了已知至少有一个值的类型。
这个错误表示，某个任意类型 {anchorTerm unsafeThird}`α` 不一定在该表中。
下一章将说明如何向这张表添加内容，以及如何成功编写像 {anchorTerm unsafeThird}`unsafeThird` 这样的函数。

在列表和用于查找的方括号之间添加空白，会导致另一条消息：

```anchor extraSpace
#eval woodlandCritters [1]
```


```anchorError extraSpace
Function expected at
  woodlandCritters
but this term has type
  List String

Note: Expected a function because this term is being applied to the argument
  [1]
```

添加一个空格会使 Lean 将该表达式视为函数应用，并将索引视为一个只包含单个数字的列表。
这条错误消息源于让 Lean 尝试把 {anchorTerm woodlandCritters}`woodlandCritters` 当作函数来处理。

## 练习
%%%
tag := "props-proofs-indexing-exercises"
file := "Exercises"
%%%

* 使用 {anchorTerm exercises}`rfl` 证明以下定理：{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`。如果用 {anchorTerm exercises}`rfl` 来证明 {anchorTerm exercises}`5 < 18`，会发生什么？为什么？
* 使用 {anchorTerm exercises}`by decide` 证明以下定理：{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`、{anchorTerm exercises}`5 < 18`。
* 编写一个函数，用于查找列表中的第五个条目。将此次查找是安全的这一证据作为参数传给该函数。
