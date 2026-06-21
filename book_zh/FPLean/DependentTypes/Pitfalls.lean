import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.Pitfalls"

#doc (Manual) "使用依值类型编程的陷阱" =>
%%%
tag := "dependent-type-pitfalls"
file := "Pitfalls-of-Programming-with-Dependent-Types"
%%%

依值类型的灵活性使类型检查器能够接受更多有用的程序，因为类型语言具有足够的表达力，能够描述表达力较弱的类型系统无法描述的变化。
同时，依值类型表达非常细粒度规格的能力，使类型检查器能够拒绝更多有缺陷的程序。
这种能力是有代价的。

诸如 {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` 这类返回类型的函数，其内部实现与它们所产生的类型之间的紧密耦合，是一个更大困难的实例：当函数被用于类型中时，函数的接口与实现之间的区别开始瓦解。
通常，只要不改变函数的类型签名或输入输出行为，所有重构都是有效的。
函数可以被改写为使用更高效的算法和数据结构，可以修复缺陷，也可以改进代码清晰度，而不会破坏客户端代码。
然而，当函数被用于类型中时，函数实现的内部细节会成为类型的一部分，因而也成为另一个程序的_接口_的一部分。

例如，考察以下两个在 {anchorName plusL}`Nat` 上实现加法的方式。
{anchorName plusL}`Nat.plusL` 对其第一个参数递归：

```anchor plusL
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
```
另一方面，{anchorName plusR}`Nat.plusR` 对其第二个参数递归：

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
这两个加法实现都忠实于其底层的数学概念，因此当给定相同参数时，它们返回相同的结果。

然而，当这两个实现被用于类型中时，它们呈现出相当不同的接口。
例如，考察一个拼接两个 {anchorName appendL}`Vect` 的函数。
这个函数应当返回一个 {anchorName appendL}`Vect`，其长度为各参数长度之和。
因为 {anchorName appendL}`Vect` 本质上是带有更丰富类型信息的 {anchorName moreNames}`List`，所以像为 {anchorName moreNames}`List.append` 编写函数那样来编写它是合理的，即对第一个参数进行模式匹配和递归。
从一个类型签名以及指向占位符的初始模式匹配开始，会得到两条消息：
```anchor appendL1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
```
第一条消息在 {anchorName moreNames}`nil` 情形中说明，占位符应被替换为一个长度为 {lit}`plusL 0 k` 的 {anchorName appendL}`Vect`：
```anchorError appendL1
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
第二条消息在 {anchorName moreNames}`cons` 情形中说明，占位符应被替换为一个长度为 {lit}`plusL (n✝ + 1) k` 的 {anchorName appendL}`Vect`：
```anchorError appendL2
don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α ((n✝ + 1).plusL k)
```
{lit}`n` 后面的符号称为_匕首号_，用于表示 Lean 在内部发明的名称。
在幕后，对第一个 {anchorName appendL1}`Vect` 进行模式匹配也隐式地导致第一个 {anchorName plusL}`Nat` 的值被细化，因为构造子 {anchorName moreNames}`cons` 上的索引是 {anchorTerm Vect (module:=Examples.DependentTypes)}`n + 1`，其中 {anchorName appendL}`Vect` 的尾部长度为 {anchorTerm Vect (module:=Examples.DependentTypes)}`n`。
这里，{lit}`n✝` 表示比参数 {anchorName appendL1}`n` 小一的 {anchorName moreNames}`Nat`。

# 定义相等性
%%%
tag := "definitional-equality"
file := "Definitional-Equality"
%%%

在 {anchorName appendL3}`plusL` 的定义中，有一个模式情形 {anchorTerm plusL}`0, k => k`。
这适用于第一个占位符中使用的长度，因此另一种写出下划线类型 {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)` 的方式是 {anchorTerm moreNames}`Vect α k`。
类似地，{anchorName plusL}`plusL` 包含一个模式情形 {anchorTerm plusL}`n + 1, k => plusL n k + 1`。
这意味着第二个下划线的类型可以等价地写作 {lit}`Vect α (plusL n✝ k + 1)`。

为了揭示幕后发生的事情，第一步是显式写出 {anchorName plusL}`Nat` 参数；这也会产生不带匕首号的错误消息，因为这些名称现在已经在程序中显式写出：
```anchor appendL3
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendL3
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
```anchorError appendL4
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusL k)
```
用这些类型的简化版本标注下划线并不会引入类型错误，这意味着程序中写出的类型与 Lean 自行找到的类型是等价的：
```anchor appendL5
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL5
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
```anchorError appendL6
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

第一种情形要求一个 {anchorTerm appendL5}`Vect α k`，而 {anchorName appendL5}`ys` 具有该类型。
这与把空列表追加到任意其他列表会返回那个其他列表的方式是平行的。
用 {anchorName appendL7}`ys` 取代第一个下划线来细化该定义，会得到一个只剩下一个下划线有待填补的程序：
```anchor appendL7
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL7
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

这里发生了一件非常重要的事情。
在 Lean 期望一个 {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)` 的上下文中，它收到了一个 {anchorTerm moreNames}`Vect α k`。
然而，{anchorName plusL}`Nat.plusL` 不是一个 {kw}`abbrev`，因此它似乎不应当在类型检查期间运行。
实际发生的是别的事情。

理解正在发生什么的关键在于，Lean 在类型检查时并不只是展开 {kw}`abbrev`。
它还可以在检查两个类型是否彼此等价时执行计算，使得一个类型的任意表达式都可以用于期望另一个类型的上下文中。
这个性质称为_定义性相等_，它是微妙的。

当然，书写完全相同的两个类型会被认为是定义性相等的——{anchorName moreNames}`Nat` 与 {anchorName moreNames}`Nat`，或者 {anchorTerm moreNames}`List String` 与 {anchorTerm moreNames}`List String`，都应当被认为相等。
由不同数据类型构成的任意两个具体类型都不相等，因此 {anchorTerm moreNames}`List Nat` 不等于 {anchorName moreNames}`Int`。
此外，仅在内部名称重命名上不同的类型是相等的，因此 {anchorTerm moreNames}`(n : Nat) → Vect String n` 与 {anchorTerm moreNames}`(k : Nat) → Vect String k` 相同。
由于类型可以包含普通数据，定义性相等还必须描述数据何时相等。
相同构造子的使用是相等的，因此 {anchorTerm moreNames}`0` 等于 {anchorTerm moreNames}`0`，并且 {anchorTerm moreNames}`[5, 3, 1]` 等于 {anchorTerm moreNames}`[5, 3, 1]`。

然而，类型所包含的不仅仅是函数箭头、数据类型和构造子。
它们还包含_变量_和_函数_。
变量的定义性相等相对简单：每个变量只等于它自身，因此 {anchorTerm moreNames}`(n k : Nat) → Vect Int n` 与 {anchorTerm moreNames}`(n k : Nat) → Vect Int k` 并非定义性相等。
另一方面，函数则更为复杂。
虽然数学上认为，如果两个函数具有相同的输入—输出行为，那么它们就是相等的，但并不存在高效算法来检查这一点，而定义性相等的全部要旨正是让 Lean 检查两个类型是否可以互换。
相反，Lean 认为函数只有在它们都是 {kw}`fun` 表达式且其函数体定义性相等时，才是定义性相等的。
换言之，两个函数必须使用_同一个算法_，并调用_同一些辅助定义_，才会被认为是定义性相等的。
这通常并没有太大帮助，因此函数的定义性相等主要用于完全相同的已定义函数出现在两个类型中的情形。

当函数在类型中被_调用_时，检查定义性相等可能涉及对函数调用进行规约。
类型 {anchorTerm moreNames}`Vect String (1 + 4)` 与类型 {anchorTerm moreNames}`Vect String (3 + 2)` 是定义性相等的，因为 {anchorTerm moreNames}`1 + 4` 与 {anchorTerm moreNames}`3 + 2` 定义性相等。
为了检查它们的相等性，二者都会被规约为 {anchorTerm moreNames}`5`，随后可以五次使用构造子规则。
对于应用于数据的函数，其定义性相等可以先通过查看它们是否已经相同来检查——毕竟，无需将 {anchorTerm moreNames}`["a", "b"] ++ ["c"]` 规约后再检查它是否等于 {anchorTerm moreNames}`["a", "b"] ++ ["c"]`。
如果并非如此，就调用该函数并将其替换为它的值，然后再检查该值。

并非所有函数参数都是具体数据。
例如，类型可能包含并非由 {anchorName moreNames}`zero` 和 {anchorName moreNames}`succ` 构造子构造出的 {anchorName moreNames}`Nat`。
在类型 {anchorTerm moreFun}`(n : Nat) → Vect String n` 中，变量 {anchorName moreFun}`n` 是一个 {anchorName moreFun}`Nat`，但在函数被调用之前，不可能知道它究竟是_哪一个_ {anchorName moreFun}`Nat`。
事实上，该函数可能先以 {anchorTerm moreNames}`0` 调用，随后又以 {anchorTerm moreNames}`17` 调用，之后再以 {anchorTerm moreNames}`33` 调用。
如 {anchorName appendL}`appendL` 的定义所示，类型为 {anchorName moreFun}`Nat` 的变量也可以传递给诸如 {anchorName appendL}`plusL` 这样的函数。
事实上，类型 {anchorTerm moreFun}`(n : Nat) → Vect String n` 与类型 {anchorTerm moreNames}`(n : Nat) → Vect String (Nat.plusL 0 n)` 定义相等。

{anchorName againFun}`n` 与 {anchorTerm againFun}`Nat.plusL 0 n` 定义相等的原因在于，{anchorName plusL}`plusL` 的模式匹配检查它的_第一个_参数。
这会造成问题：{anchorTerm moreFun}`(n : Nat) → Vect String n` 与 {anchorTerm stuckFun}`(n : Nat) → Vect String (Nat.plusL n 0)` _并不_定义相等，尽管零应当既是加法的左单位元，也是右单位元。
这是因为模式匹配在遇到变量时会停滞。
在 {anchorName stuckFun}`n` 的实际值变得已知之前，无法知道应当选择 {anchorTerm stuckFun}`Nat.plusL n 0` 的哪一个分支。

同样的问题也出现在查询示例中的 {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` 函数上。
类型 {anchorTerm RowStuck (module:=Examples.DependentTypes.DB)}`Row (c :: cs)` 不会规约为任何数据类型，因为 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 的定义分别处理单元素列表和至少含有两个条目的列表。
换言之，当它试图将变量 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`cs` 与具体的 {anchorName moreNames}`List` 构造子匹配时会停滞。
这就是为什么几乎每个拆解或构造 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 的函数都需要匹配与 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 本身相同的三个分支：使其不再停滞会显露出可用于模式匹配或构造子的具体类型。

{anchorName appendL8}`appendL` 中缺失的分支需要一个 {lit}`Vect α (Nat.plusL n k + 1)`。
索引中的 {lit}`+ 1` 表明下一步应当使用 {anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons`：
```anchor appendL8
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
```
```anchorError appendL8
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k)
```
对 {anchorName appendL9}`appendL` 的递归调用可以构造出具有所需长度的 {anchorName appendL9}`Vect`：

```anchor appendL9
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
```
既然程序已经完成，去掉对 {anchorName appendL9}`n` 和 {anchorName appendL9}`k` 的显式匹配会使它更易阅读，也更易调用该函数：

```anchor appendL
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
```

使用定义相等来比较类型意味着，定义相等所涉及的一切，包括函数定义的内部细节，都会成为使用依值类型和索引族的程序的_接口_的一部分。
在类型中暴露函数的内部细节意味着，对被暴露程序进行重构可能导致使用它的程序不再通过类型检查。
特别地，{anchorName appendL}`plusL` 被用于 {anchorName appendL}`appendL` 的类型这一事实意味着，{anchorName appendL}`plusL` 的定义不能被本来等价的 {anchorName plusR}`plusR` 替换。

# 在加法上停滞
%%%
tag := "stuck-addition"
file := "Getting-Stuck-on-Addition"
%%%

如果改用 {anchorName appendR}`plusR` 来定义 append，会发生什么？
以同样的方式开始，即在每个分支中写出显式长度和占位下划线，会显示如下有用的错误消息：
```anchor appendR1
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR1
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)
```
```anchorError appendR2
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
然而，尝试在第一个占位符周围放置一个 {anchorTerm appendR3}`Vect α k` 类型标注，会产生类型不匹配错误：
```anchor appendR3
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR3
Type mismatch
  ?m.11
has type
  Vect α k
but is expected to have type
  Vect α (Nat.plusR 0 k)
```
这个错误指出 {anchorTerm plusRinfo}`Nat.plusR 0 k` 与 {anchorName plusRinfo}`k` _并不_定义相等。

:::paragraph
这是因为 {anchorName plusR}`plusR` 具有如下定义：

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
其模式匹配发生在_第二个_参数上，而不是第一个参数上，这意味着变量 {anchorName plusRinfo}`k` 出现在该位置会阻止它归约。
Lean 标准库中的 {anchorName plusRinfo}`Nat.add` 等价于 {anchorName plusRinfo}`plusR`，而不是 {anchorName plusRinfo}`plusL`，因此试图在这个定义中使用它会导致完全相同的困难：
```anchor appendR4
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR4
Type mismatch
  ?m.15
has type
  Vect α k
but is expected to have type
  Vect α (0 + k)
```

加法在变量处变得_停滞_。
要使其摆脱停滞，需要 {ref "equality-and-ordering"}[命题相等]。
:::

# 命题相等
%%%
tag := "propositional-equality"
file := "Propositional-Equality"
%%%

命题相等是断言两个表达式相等的数学陈述。
定义相等是一种环境性的事实，Lean 会在需要时自动检查；而命题相等的陈述则需要显式证明。
一旦某个相等命题得到证明，它就可以在程序中用于修改一个类型，将相等式的一边替换为另一边，从而可能使类型检查器摆脱停滞。

定义相等之所以如此受限，是为了使其能够由算法检查。
命题相等要丰富得多，但计算机一般不能检查两个表达式是否在命题意义下相等，尽管它可以验证一个声称的证明事实上确为证明。
定义相等与命题相等之间的划分体现了人与机器之间的分工：最枯燥的相等作为定义相等的一部分被自动检查，从而使人类心智得以处理命题相等中那些有趣的问题。
类似地，定义相等由类型检查器自动调用，而命题相等则必须被专门援引。


在 {ref "props-proofs-indexing"}[命题、证明与索引] 中，一些相等陈述使用 {tactic}`decide` 得到证明。
所有这些相等陈述中，命题相等事实上已经是定义相等。
通常，命题相等的陈述首先通过变形化为定义相等，或化为与已有已证相等足够接近的形式，然后使用诸如 {tactic}`decide` 或 {tactic}`simp` 之类的工具来处理简化后的情形。
{tactic}`simp` 策略相当强大：在幕后，它使用若干快速的自动化工具来构造证明。
一个称为 {kw}`rfl` 的更简单策略专门使用定义相等来证明命题相等。
名称 {kw}`rfl` 是 _reflexivity_（自反性）的缩写；自反性是相等的性质，断言任何事物都等于其自身。

要使 {anchorName appendR}`appendR` 摆脱停滞，需要证明 {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k`，而这不是定义相等，因为 {anchorName plusR}`plusR` 在其第二个参数中的变量处停滞。
要使它进行计算，{anchorName plusR_zero_left1}`k` 必须变成一个具体的构造子。
这是模式匹配的工作。

:::paragraph
具体而言，由于 {anchorName plusR_zero_left1}`k` 可以是_任意_ {anchorName plusR_zero_left1}`Nat`，此任务需要一个函数，它能够为无论什么样的_任意_ {anchorName plusR_zero_left1}`k` 返回 {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k` 的证据。
这应当是一个返回相等证明的函数，其类型为 {anchorTerm plusR_zero_left1}`(k : Nat) → k = Nat.plusR 0 k`。
用初始模式和占位符开始编写，会得到如下消息：
```anchor plusR_zero_left1
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
```
```anchorError plusR_zero_left1
don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0
```
```anchorError plusR_zero_left2
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
```
通过模式匹配将 {anchorName plusR_zero_left1}`k` 细化为 {anchorTerm plusR_zero_left1}`0` 之后，第一个占位符表示某个按定义成立的陈述的证据。
{kw}`rfl` 策略会处理它，只留下第二个占位符：
```anchor plusR_zero_left3
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => _
```
:::

第二个占位符稍微棘手一些。
表达式 {anchorTerm plusRStep}`Nat.plusR 0 k + 1` 与 {anchorTerm plusRStep}`Nat.plusR 0 (k + 1)` 定义相等。
这意味着目标也可以写作 {anchorTerm plusR_zero_left4}`k + 1 = Nat.plusR 0 k + 1`：
```anchor plusR_zero_left4
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
```
```anchorError plusR_zero_left4
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 k + 1
```

:::paragraph
在相等陈述两边的 {anchorTerm plusR_zero_left4}`+ 1` 之下，是该函数自身返回内容的另一个实例。
换言之，对 {anchorName plusR_zero_left4}`k` 的递归调用会返回 {anchorTerm plusR_zero_left4}`k = Nat.plusR 0 k` 的证据。
如果相等不能应用于函数参数，那就不能称为相等。
换言之，若 {anchorTerm congr}`x = y`，则 {anchorTerm congr}`f x = f y`。
标准库包含一个函数 {anchorName congr}`congrArg`，它接受一个函数和一个相等证明，并返回一个新的证明，其中该函数已被应用于相等两边。
在此情形中，该函数是 {anchorTerm plusR_zero_left_done}`(· + 1)`：

```anchor plusR_zero_left_done
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

:::paragraph
由于这实际上是一个命题的证明，它应当声明为 {kw}`theorem`：

```anchor plusR_zero_left_thm
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

命题相等可以使用向右三角算子 {anchorTerm appendRsubst}`▸` 部署到程序中。
给定一个相等证明作为其第一个参数，并给定某个其他表达式作为其第二个参数，该算子会在第二个参数的类型中，将相等式一边的实例替换为相等式另一边的实例。
换言之，下面的定义不含类型错误：
```anchor appendRsubst
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
第一个占位符具有期望的类型：
```anchorError appendRsubst
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
现在可以用 {anchorName appendR5}`ys` 填入它：
```anchor appendR5
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
```

填入剩余的占位符需要使另一个加法实例摆脱停滞：
```anchorError appendR5
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
这里，要证明的陈述是 {anchorTerm plusR_succ_left}`Nat.plusR (n + 1) k = Nat.plusR n k + 1`，它可以与 {anchorTerm appendRsubst}`▸` 一起使用，将 {anchorTerm appendRsubst}`+ 1` 拉到表达式的最外层，使其与 {anchorName Vect}`cons` 的索引匹配。

该证明是一个递归函数，它对 {anchorName appendR}`plusR` 的第二个参数，即 {anchorName appendR5}`k`，进行模式匹配。
这是因为 {anchorName appendR5}`plusR` 本身也对其第二个参数进行模式匹配，所以该证明可以通过模式匹配使其“摆脱停滞”，暴露其计算行为。
该证明的骨架与 {anchorName appendR}`plusR_zero_left` 的骨架非常相似：
```anchor plusR_succ_left_0
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
```

剩余情形的类型与 {anchorTerm congr}`Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1` 定义相等，因此可以像在 {anchorName plusR_zero_left_thm}`plusR_zero_left` 中一样，用 {anchorName congr}`congrArg` 解决：
```anchorError plusR_succ_left_2
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
```
这得到一个完成的证明：

```anchor plusR_succ_left
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
```

完成的证明可用于使 {anchorName appendR}`appendR` 中的第二个情形摆脱停滞：

```anchor appendR
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
```
当再次将 {anchorName appendR}`appendR` 的长度参数设为隐式时，它们不再被显式命名，因而不能在证明中按名称援引。
然而，Lean 的类型检查器在幕后有足够的信息自动填入它们，因为没有其他值能使这些类型匹配：

```anchor appendRImpl
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
```

# 优点与缺点
%%%
tag := "dependent-types-pros-and-cons"
file := "Pros-and-Cons"
%%%

索引族具有一个重要性质：对它们进行模式匹配会影响定义相等。
例如，在针对 {anchorTerm Vect}`Vect` 的 {kw}`match` 表达式中的 {anchorName Vect}`nil` 情形里，长度直接_变成_ {anchorTerm moreNames}`0`。
定义相等可能非常方便，因为它始终处于活动状态，且不需要显式调用。

然而，在依值类型和模式匹配中使用定义相等有严重的软件工程缺点。
首先，函数必须专门为了在类型中使用而编写，而便于在类型中使用的函数可能并未采用最高效的算法。
一旦某个函数通过在类型中使用而被暴露，其实现就成为接口的一部分，从而给未来的重构带来困难。
其次，定义相等可能很慢。
当被要求检查两个表达式是否定义相等时，如果相关函数很复杂并且有许多抽象层，Lean 可能需要运行大量代码。
第三，由定义相等失败产生的错误消息并不总是容易理解，因为它们可能以函数内部实现的术语来表述。
错误消息中各表达式的来源并不总是容易理解。
最后，在一组索引族和依值类型函数中编码非平凡不变量往往可能很脆弱。
当函数暴露出来的归约行为被证明不能提供方便的定义相等时，常常需要修改系统中的早期定义。
另一种选择是在程序中到处援引相等证明，但这些证明可能变得相当笨重。

在惯用的 Lean 代码中，索引数据类型并不经常使用。
相反，通常使用子类型和显式命题来强制保证重要不变量。
这种方法涉及许多显式证明，而很少援引定义相等。
作为一个交互式定理证明器，Lean 的设计使显式证明变得方便。
一般而言，在大多数情况下应当优先采用这种方法。

然而，理解数据类型的索引族很重要。
诸如 {anchorName plusR_zero_left_thm}`plusR_zero_left` 和 {anchorName plusR_succ_left}`plusR_succ_left` 这样的递归函数事实上是_数学归纳法证明_。
递归的基本情形对应于归纳中的基本情形，而递归调用表示对归纳假设的援引。
更一般地，Lean 中的新命题常常被定义为证据的归纳类型，而这些归纳类型通常带有索引。
证明定理的过程事实上就是在幕后构造具有这些类型的表达式，这一过程与本节中的证明并非完全不同。
此外，索引数据类型有时正是完成任务的恰当工具。
熟练使用它们，是理解何时使用它们的重要组成部分。



# 练习
%%%
tag := "dependent-type-pitfalls-exercises"
file := "Exercises"
%%%

 * 使用 {anchorName plusR_succ_left}`plusR_succ_left` 风格的递归函数，证明对于所有 {anchorName moreNames}`Nat` {anchorName exercises}`n` 和 {anchorName exercises}`k`，都有 {anchorTerm exercises}`n.plusR k = n + k`。
 * 在 {anchorName moreNames}`Vect` 上编写一个函数，使得 {anchorName plusR}`plusR` 比 {anchorName plusL}`plusL` 更自然，而 {anchorName plusL}`plusL` 会要求在定义中使用证明。
