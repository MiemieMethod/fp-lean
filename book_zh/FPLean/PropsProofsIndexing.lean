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
%%%

和许多语言一样，Lean 使用方括号对数组和列表进行索引。
例如，如果 {moduleTerm}`woodlandCritters` 定义如下：

```anchor woodlandCritters
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
```

那么可以提取各个组成部分：

```anchor animals
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
```

然而，试图提取第四个元素会导致编译时错误，而不是运行时错误：

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

这条错误消息表明，Lean 试图自动从数学上证明 {moduleTerm}`3 < woodlandCritters.length`（即 {moduleTerm}`3 < List.length woodlandCritters`）；若能证明这一点，就意味着这次查找是安全的，但 Lean 没能完成这个证明。
越界错误是一类常见缺陷，而 Lean 利用自己既是程序设计语言又是定理证明器的双重性质，尽可能排除这类错误。

要理解这是如何工作的，需要理解三个关键概念：命题、证明和策略。

# 命题与证明
%%%
tag := "propositions-and-proofs"
%%%

_命题_是一个可以为真或为假的陈述。
以下自然语言句子都是命题：

 * $`1 + 1 = 2`
 * 加法满足交换律。
 * 素数有无穷多个。
 * $`1 + 1 = 15`
 * 巴黎是法国的首都。
 * 布宜诺斯艾利斯是韩国的首都。
 * 所有鸟都会飞。

另一方面，无意义的陈述不是命题。
下面这些句子虽然语法上可以成立，但都不是命题：

 * 1 + 绿色 = 冰淇淋
 * 所有首都都是素数。
 * 至少有一个 gorg 是 fleep。

命题分为两类：一类是纯数学命题，它们只依赖于我们对概念的定义；另一类是关于世界事实的命题。
像 Lean 这样的定理证明器关心的是前一类命题，而不会讨论企鹅的飞行能力或城市的法律地位。

_证明_是说明某个命题为真的有说服力的论证。
对于数学命题，这些论证会使用相关概念的定义以及逻辑推理规则。
大多数证明是写给人看的，因此会省略许多繁琐细节。
像 Lean 这样的计算机辅助定理证明器，其设计目标是允许数学家在省略许多细节的情况下编写证明；补全缺失的显式步骤则是软件的职责。
这些步骤可以被机械地检查。
这降低了疏漏或错误出现的可能性。

在 Lean 中，程序的类型描述了可以如何与该程序交互。
例如，类型为 {moduleTerm}`Nat → List String` 的程序是一个函数，它接受一个 {moduleTerm}`Nat` 参数并产生一个字符串列表。
换言之，每个类型都规定了什么样的程序才算具有该类型。

在 Lean 中，命题实际上就是类型。
它们规定了什么样的对象可作为该陈述为真的证据。
通过提供这种证据，并由 Lean 检查它，就能证明相应命题。
另一方面，如果命题为假，就不可能构造出这种证据。

例如，命题 $`1 + 1 = 2` 可以直接用 Lean 写出。
这个命题的证据是构造子 {moduleTerm}`rfl`，它是_自反性_（reflexivity）的缩写。
在数学中，如果关系中的每个元素都与自身相关，那么该关系就是_自反的_；这是得到合理等号概念的基本要求。
由于 {moduleTerm}`1 + 1` 会计算为 {moduleTerm}`2`，二者实际上是同一对象：

```anchor onePlusOneIsTwo
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
```

另一方面，{moduleTerm}`rfl` 不能证明假命题 $`1 + 1 = 15`：

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

这条错误消息表明，当等式两边已经是同一个数时，{moduleTerm}`rfl` 可以证明两个表达式相等。
由于 {moduleTerm}`1 + 1` 会直接求值为 {moduleTerm}`2`，它们被视为相同对象，因此 {moduleTerm}`onePlusOneIsTwo` 能够被接受。
正如 {moduleTerm}`Type` 描述表示数据结构和函数的类型，例如 {moduleTerm}`Nat`、{moduleTerm}`String` 和 {moduleTerm}`List (Nat × String × (Int → Float))`，{moduleTerm}`Prop` 描述命题。

当一个命题已经被证明时，它称为一个_定理_。
在 Lean 中，按照惯例应使用 {kw}`theorem` 关键字而不是 {kw}`def` 来声明定理。
这有助于读者看出哪些声明应被理解为数学证明，哪些声明是定义。
一般来说，对于证明，重要的是存在一个命题为真的证据，而提供的_具体_证据并不特别重要。
另一方面，对于定义，选择的具体值则非常重要；毕竟，一个总是返回 {anchorTerm SomeNats}`0` 的加法定义显然是错误的。
由于证明的细节对后续证明并不重要，使用 {kw}`theorem` 关键字能让 Lean 编译器获得更高的并行性。

前面的例子可以改写如下：

```anchor onePlusOneIsTwoProp
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
```


# 策略
%%%
tag := "tactics"
%%%

证明通常使用_策略_编写，而不是直接提供证据。
策略是构造某个命题证据的小程序。
这些程序在_证明状态_中运行；证明状态会追踪待证明的陈述（称为_目标_），以及可用于证明它的假设。
在一个目标上运行策略会产生一个新的证明状态，其中可能包含新的目标。
当所有目标都被证明时，证明就完成了。

要用策略编写证明，需要以 {kw}`by` 开始定义。
写下 {kw}`by` 会让 Lean 进入策略模式，直到下一个缩进块结束。
在策略模式中，Lean 会持续提供关于当前证明状态的反馈。
用策略写出时，{anchorTerm onePlusOneIsTwoTactics}`onePlusOneIsTwo` 仍然相当简短：

```anchor onePlusOneIsTwoTactics
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide
```

{tactic}`decide` 策略会调用一个_判定过程_，即一个能够检查某个陈述是真还是假的程序，并在任一情形下返回合适的证明。
它主要用于处理 {anchorTerm SomeNats}`1` 和 {anchorTerm SomeNats}`2` 这样的具体值。
本书中其他重要策略包括 {tactic}`simp`，它是 “simplify” 的缩写；以及 {tactic}`grind`，它能自动证明许多定理。

策略之所以有用，有若干原因：
 1. 许多证明如果写到最细节处会很复杂且繁琐，而策略可以自动完成这些无趣的部分。
 2. 用策略写成的证明随着时间推移更容易维护，因为灵活的自动化可以掩盖定义中的小变化。
 3. 由于单个策略可以证明许多不同定理，Lean 可以在幕后使用策略，让用户不必手写证明。例如，数组查找需要一个索引在界内的证明，而策略通常可以构造出该证明，不需要用户操心。

在幕后，索引记法使用一个策略来证明用户的查找操作是安全的。
该策略会考虑许多关于算术的事实，并把它们与所有局部已知事实结合起来，尝试证明索引在界内。

{tactic}`simp` 策略是 Lean 证明中的主力工具。
它会把目标改写成尽可能简单的形式。
在许多情况下，这种改写会把陈述简化到可以自动证明的程度。
在幕后，Lean 会构造详细的形式化证明；但使用 {tactic}`simp` 会隐藏这种复杂性。

与 {tactic}`decide` 类似，{tactic}`grind` 策略用于完成证明。
它使用来自 SMT 求解器的一系列技术，能够证明种类很广的定理。
与 {tactic}`simp` 不同，{tactic}`grind` 如果不能完全完成证明，就不会产生中间进展；它要么完全成功，要么失败。
{tactic}`grind` 非常强大、可定制且可扩展；由于这种能力和灵活性，当它未能证明某个定理时，其输出会包含大量信息，可以帮助有经验的 Lean 用户诊断失败原因。
这在初学阶段可能显得过于繁杂，因此本章只使用 {tactic}`decide` 和 {tactic}`simp`。

# 连词
%%%
tag := "connectives"
%%%

逻辑的基本构件，例如“且”“或”“真”“假”和“非”，称为{deftech}_逻辑连词_。
每个连词都规定了什么对象可算作其为真的证据。
例如，要证明陈述“_A_ 且 _B_”，就必须同时证明 _A_ 和 _B_。
这意味着“_A_ 且 _B_”的证据是一个有序对，其中同时包含 _A_ 的证据和 _B_ 的证据。
类似地，“_A_ 或 _B_”的证据要么由 _A_ 的证据组成，要么由 _B_ 的证据组成。

特别地，这些连词中的大多数都像数据类型一样定义，并且具有构造子。
如果 {anchorTerm AndProp}`A` 和 {anchorTerm AndProp}`B` 是命题，那么“{anchorTerm AndProp}`A` 且 {anchorTerm AndProp}`B`”（写作 {anchorTerm AndProp}`A ∧ B`）也是一个命题。
{anchorTerm AndProp}`A ∧ B` 的证据由构造子 {anchorTerm AndIntro}`And.intro` 给出，其类型为 {anchorTerm AndIntro}`A → B → A ∧ B`。
将 {anchorTerm AndIntro}`A` 和 {anchorTerm AndIntro}`B` 替换为具体命题后，可以用 {anchorTerm AndIntroEx}`And.intro rfl rfl` 证明 {anchorTerm AndIntroEx}`1 + 1 = 2 ∧ "Str".append "ing" = "String"`。
当然，{tactic}`decide` 也足够强大，能够找到这个证明：

```anchor AndIntroExTac
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide
```


类似地，“{anchorTerm OrProp}`A` 或 {anchorTerm OrProp}`B`”（写作 {anchorTerm OrProp}`A ∨ B`）有两个构造子，因为要证明“{anchorTerm OrProp}`A` 或 {anchorTerm OrProp}`B`”，只需要两个底层命题之一为真。
这两个构造子分别是 {anchorTerm OrIntro1}`Or.inl` 和 {anchorTerm OrIntro2}`Or.inr`；前者类型为 {anchorTerm OrIntro1}`A → A ∨ B`，后者类型为 {anchorTerm OrIntro2}`B → A ∨ B`。

蕴涵（若 {anchorTerm impliesDef}`A` 则 {anchorTerm impliesDef}`B`）用函数表示。
特别地，一个把 {anchorTerm impliesDef}`A` 的证据转换为 {anchorTerm impliesDef}`B` 的证据的函数，本身就是 {anchorTerm impliesDef}`A` 蕴涵 {anchorTerm impliesDef}`B` 的证据。
这不同于对蕴涵的通常描述；在通常描述中，{anchorTerm impliesDef}`A → B` 是 {anchorTerm impliesDef}`¬A ∨ B` 的缩写，但这两种表述是等价的。

由于“且”的证据是构造子，因此可以对其进行模式匹配。
例如，要证明 {anchorTerm andImpliesOr}`A` 且 {anchorTerm andImpliesOr}`B` 蕴涵 {anchorTerm andImpliesOr}`A` 或 {anchorTerm andImpliesOr}`B`，可以给出一个函数：它从 {anchorTerm andImpliesOr}`A` 与 {anchorTerm andImpliesOr}`B` 的合取证据中取出 {anchorTerm andImpliesOr}`A` 的证据（或 {anchorTerm andImpliesOr}`B` 的证据），再用这个证据产生 {anchorTerm andImpliesOr}`A` 或 {anchorTerm andImpliesOr}`B` 的证据：

```anchor andImpliesOr
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a
```


:::table +header
*
  - 连词
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
 -  {anchorTerm connectiveTable}`Or.inl : A → A ∨ B` 或 {anchorTerm connectiveTable}`Or.inr : B → A ∨ B` 之一

*
 -  {anchorName connectiveTable}`A` 蕴涵 {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A → B`
 -  将 {anchorName connectiveTable}`A` 的证据转换为 {anchorName connectiveTable}`B` 的证据的函数

*
 -  非 {anchorName connectiveTable}`A`
 -  {anchorTerm connectiveTable}`¬A`
 -  会将 {anchorName connectiveTable}`A` 的证据转换为 {anchorName connectiveTable}`False` 的证据的函数


:::

{tactic}`decide` 策略可以证明使用这些连词的定理。
例如：

```anchor connectivesD
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide
```


# 证据作为参数
%%%
tag := "evidence-passing"
%%%

在某些情况下，要安全地索引列表，就要求该列表至少具有某个最小长度；但列表本身可能是变量，而不是具体值。
要使这种查找安全，就必须有某种证据说明列表足够长。
使索引安全的最简单方法之一，是让执行数据结构查找的函数把所需的安全性证据作为参数。
例如，返回列表第三个条目的函数一般并不安全，因为列表可能包含零个、一个或两个条目：

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

然而，可以通过增加一个参数，把证明列表至少有三个条目的义务交给调用者；该参数由索引操作安全这一事实的证据组成：

```anchor third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
```

在这个例子中，{anchorTerm third}`xs.length > 2` 不是一个检查 {anchorTerm third}`xs` _是否_有超过两个条目的程序。
它是一个可能为真也可能为假的命题，而参数 {anchorTerm third}`ok` 必须是它为真的证据。

当函数应用于具体列表时，其长度是已知的。
在这些情况下，{anchorTerm thirdCritters}`by decide` 可以自动构造证据：

```anchor thirdCritters
#eval third woodlandCritters (by decide)
```

```anchorInfo thirdCritters
"snail"
```


# 无证据的索引
%%%
tag := "indexing-without-evidence"
%%%

在不便证明索引操作位于界内的情况下，还有其他替代方案。
加上问号会得到一个 {anchorName thirdOption}`Option`；如果索引在界内，结果就是 {anchorName OptionNames}`some`，否则就是 {anchorName OptionNames}`none`。
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
还有一个版本会在索引越界时使程序崩溃，而不是返回 {moduleTerm}`Option`：

```anchor crittersBang
#eval woodlandCritters[1]!
```

```anchorInfo crittersBang
"deer"
```
:::


# 可能遇到的消息
%%%
tag := "props-proofs-indexing-messages"
%%%
除了证明某个陈述为真以外，{anchorTerm thirdRabbitErr}`decide` 策略也可以证明某个陈述为假。
当要求它证明一个单元素列表有超过两个元素时，它会返回一条错误，指出该陈述确实为假：

```anchor thirdRabbitErr
#eval third ["rabbit"] (by decide)
```


```anchorError thirdRabbitErr
Tactic `decide` proved that the proposition
  ["rabbit"].length > 2
is false
```


{tactic}`simp` 和 {tactic}`decide` 策略不会自动展开用 {kw}`def` 给出的定义。
试图使用 {anchorTerm onePlusOneIsStillTwo}`simp` 证明 {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo` 会失败：

```anchor onePlusOneIsStillTwo
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
```

这条错误消息只是说明它无法做任何事情，因为如果不展开 {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo`，就无法取得进展：

```anchorError onePlusOneIsStillTwo
`simp` made no progress
```

使用 {anchorTerm onePlusOneIsStillTwo2}`decide` 也会失败：

```anchor onePlusOneIsStillTwo2
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
```

这同样是因为它没有展开 {anchorName onePlusOneIsStillTwo2}`OnePlusOneIsTwo`：

```anchorError onePlusOneIsStillTwo2
failed to synthesize
  Decidable OnePlusOneIsTwo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

使用 {ref "abbrev-vs-def"}[{kw}`abbrev`] 定义 {anchorName onePlusOneIsStillTwo}`OnePlusOneIsTwo` 会把该定义标记为可展开，从而修复这个问题。

除了 Lean 无法找到索引操作安全的编译时证据时产生的错误之外，使用不安全索引的多态函数还可能产生如下消息：

```anchor unsafeThird
def unsafeThird (xs : List α) : α := xs[2]!
```


```anchorError unsafeThird
failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

这是由一个技术性限制导致的；该限制是让 Lean 同时能够作为证明定理的逻辑和程序设计语言使用的一部分。
特别地，只有类型至少包含一个值的程序才允许崩溃。
这是因为 Lean 中的命题是一种类型，用来分类其为真的证据。
假命题没有这样的证据。
如果一个空类型的程序能够崩溃，那么这个会崩溃的程序就可以被用作假命题的一种伪造证据。

在内部，Lean 包含一张表，记录已知至少有一个值的类型。
这条错误的意思是，任意类型 {anchorTerm unsafeThird}`α` 不一定在这张表中。
下一章会说明如何向这张表添加内容，以及如何成功编写类似 {anchorTerm unsafeThird}`unsafeThird` 的函数。

在列表和用于查找的方括号之间添加空格，可能导致另一条消息：

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

添加空格会使 Lean 把该表达式视为函数应用，并把索引视为一个只含一个数字的列表。
这条错误消息来自 Lean 试图把 {anchorTerm woodlandCritters}`woodlandCritters` 当作函数处理。

## 练习
%%%
tag := "props-proofs-indexing-exercises"
%%%

* 使用 {anchorTerm exercises}`rfl` 证明以下定理：{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`。如果使用 {anchorTerm exercises}`rfl` 证明 {anchorTerm exercises}`5 < 18`，会发生什么？为什么？
* 使用 {anchorTerm exercises}`by decide` 证明以下定理：{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`、{anchorTerm exercises}`5 < 18`。
* 编写一个函数，用于查找列表中的第五个条目。把该查找安全这一事实的证据作为参数传给这个函数。
