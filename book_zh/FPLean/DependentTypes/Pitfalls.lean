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
%%%

依值类型的灵活性允许类型检查器接受更多有用的程序，因为类型的语言足够表达那些一般类型系统不够表达的变化。
同时，依值类型表达非常精细的规范的能力允许类型检查器拒绝更多有错误的程序。
这种能力是有代价的。

返回类型的函数（如 {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` ）的实现与它的类型之间的紧密耦合是下列问题的一个具体案例：
当类型中包含函数时，接口和实现之间的区别开始瓦解。
通常，只要重构不改变函数的类型签名或输入输出行为，它就不会导致问题。
所以一个函数可以方便地进行下列重构而不会破坏客户端代码：使用更高效的算法和数据结构重写，修复错误，提高代码的清晰度。
然而，当函数出现在类型中时，函数的内部实现成为类型的一部分，因此成为另一个程序的_接口_的一部分。

以 {anchorName plusL}`Nat` 上的加法的两个实现为例。
{anchorName plusL}`Nat.plusL` 对第一个参数进行递归：

```anchor plusL
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
```
{anchorName plusR}`Nat.plusR` 则对第二个参数进行递归：

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
两种加法的实现都与数学概念一致，因此在给定相同参数时返回相同的结果。

然而，当这两种实现用于类型时，它们呈现出非常不同的接口。
以一个将两个 {anchorName appendL}`Vect` 连接起来的函数为例。
这个函数应该返回一个长度为两个参数的长度之和的 {anchorName appendL}`Vect`。
因为 {anchorName appendL}`Vect` 本质上是一个带有更多信息的 {anchorName moreNames}`List`，所以写这个函数类似 {anchorName moreNames}`List.append`，对第一个参数进行模式匹配和递归。
让我们给定一个初始的类型签名然后进行模式匹配。占位符给出两条信息：
```anchor appendL1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
```
第一个信息：在 {anchorName moreNames}`nil` 的情形下，占位符应该被替换为一个长度为 {lit}`plusL 0 k` 的 {anchorName appendL}`Vect`：
```anchorError appendL1
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
第二个信息：在 {anchorName moreNames}`cons` 的情形下，占位符应该被替换为一个长度为 {lit}`plusL (n✝ + 1) k` 的 {anchorName appendL}`Vect`：
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
{lit}`n` 后面的符号，称为_剑标（dagger）_，用于表示 Lean 内部生成的名称。
对第一个 {anchorName appendL1}`Vect` 的模式匹配隐式导致第一个 {anchorName plusL}`Nat` 的值也被细化，因为构造子 {anchorName moreNames}`cons` 的索引是 {anchorTerm Vect (module:=Examples.DependentTypes)}`n + 1`，{anchorName appendL}`Vect` 的尾部长度为 {anchorTerm Vect (module:=Examples.DependentTypes)}`n`。
在这里，{lit}`n✝` 表示比参数 {anchorName appendL1}`n` 小1的 {anchorName moreNames}`Nat`。

# 定义相等性
%%%
tag := "definitional-equality"
%%%

在 {anchorName appendL3}`plusL` 的定义中，有一个模式 {anchorTerm plusL}`0, k => k`。
因此第一个下划线的类型 {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)` 的另一个写法是 {anchorTerm moreNames}`Vect α k`。
类似地，{anchorName plusL}`plusL` 包含另一个模式 {anchorTerm plusL}`n + 1, k => plusL n k + 1`。
因此第二个下划线的类型可以等价地写为 {lit}`Vect α (plusL n✝ k + 1)`。

为了清楚到底发生了什么，第一步是显式地写出 {anchorName plusL}`Nat` 参数。这一变化同时导致错误信息中的剑标消失了，因为此时程序已经显式给出了这个参数的名字：
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
用简化版本的类型注释下划线不会导致类型错误，这意味着程序中写的类型与 Lean 自己找到的类型是等价的：
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

第一个情形要求一个 {anchorTerm appendL5}`Vect α k`，而 {anchorName appendL5}`ys` 有这种类型。
这跟将一个列表附加到一个空列表时直接返回这个列表的情况相似。
用 {anchorName appendL7}`ys` 替代第一个下划线后，只剩下一个下划线需要填充：
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

这里发生了非常重要的事情。
在 Lean 期望一个 {anchorTerm moreNames}`Vect α (Nat.plusL 0 k)` 的上下文中，它接受了一个 {anchorTerm moreNames}`Vect α k` 。
然而，{anchorName plusL}`Nat.plusL` 不是一个 {kw}`abbrev`，所以似乎它不应该在类型检查期间运行。
还有其他事情发生了。

理解发生了什么的关键在于 Lean 在类型检查期间不止展开所有 {kw}`abbrev` 的定义。
它还可以在检查两个类型是否等价时执行计算，从而允许一个具有类型A的表达式可以在一个期待类型B的上下文中被使用。
这种属性称为_定义相等性（definitional equality）_。这种相等性很微妙。

当然，完全相同的两个类型被认为是定义相等的，例如 {anchorName moreNames}`Nat` 和 {anchorName moreNames}`Nat` 或 {anchorTerm moreNames}`List String` 和 {anchorTerm moreNames}`List String`。
任何两个由不同数据类型构造的具体类型都不相等，因此 {anchorTerm moreNames}`List Nat` 不等于 {anchorName moreNames}`Int`。
此外，两个只在内部名称上存在不同的类型（译者注：即α-等价）是相等的，例如 {anchorTerm moreNames}`(n : Nat) → Vect String n` 与 {anchorTerm moreNames}`(k : Nat) → Vect String k`。
因为类型可以包含普通数据，定义相等还必须描述何时数据是相等的。
使用相同构造子的数据是相等的，因此 {anchorTerm moreNames}`0` 等于 {anchorTerm moreNames}`0`，{anchorTerm moreNames}`[5, 3, 1]` 等于 {anchorTerm moreNames}`[5, 3, 1]`。

然而，类型不仅包含函数类型、数据类型和构造子。
它们还包含_变量_和_函数_。
变量的定义相等性相对简单：每个变量只等于自己，因此 {anchorTerm moreNames}`(n k : Nat) → Vect Int n` 不等于 {anchorTerm moreNames}`(n k : Nat) → Vect Int k`。
函数则复杂得多。数学上对函数相等的定义为两个函数具有相同的输入输出行为。但这种相等性无法被算法检查。
这违背了而定义相等性的目的：通过算法自动检查两个类型是否相等。
因此，Lean 认为函数只有在它们的函数体定义相等时才是定义相等的。
换句话说，两个函数必须使用_相同的算法_，调用_相同的辅助函数_，才能被认为是定义相等的。
这通常不是很有用，因此函数的定义相等一般只用于当两个类型中出现完全相同的函数时。

当函数在类型中被_调用_时，检查定义相等可能涉及规约这些调用。
类型 {anchorTerm moreNames}`Vect String (1 + 4)` 与类型 {anchorTerm moreNames}`Vect String (3 + 2)` 是定义相等的，因为 {anchorTerm moreNames}`1 + 4` 与 {anchorTerm moreNames}`3 + 2` 是定义相等的。
为了检查它们的相等性，两者都被规约为 {anchorTerm moreNames}`5`，然后使用五次“构造子”规则。
检查函数应用于数据的定义相等性可以首先检查它们是否已经相同——例如，检查 {anchorTerm moreNames}`["a", "b"] ++ ["c"]` 是否等于 {anchorTerm moreNames}`["a", "b"] ++ ["c"]` 时没有必要进行规约。
如果不同，调用函数并继续检查结果的定义相等性。

并非所有函数参数都是具体数据。
例如，类型可能包含不是由 {anchorName moreNames}`zero` 和 {anchorName moreNames}`succ` 构造子构建的 {anchorName moreNames}`Nat`。
在类型 {anchorTerm moreFun}`(n : Nat) → Vect String n` 中，变量 {anchorName moreFun}`n` 是一个 {anchorName moreFun}`Nat`，但在调用函数之前不可能知道它_哪个_ {anchorName moreFun}`Nat`。
实际上，函数可能首先用 {anchorTerm moreNames}`0` 调用，然后用 {anchorTerm moreNames}`17` 调用，然后再用 {anchorTerm moreNames}`33` 调用。
如 {anchorName appendL}`appendL` 的定义中所见，类型为 {anchorName moreFun}`Nat` 的变量也可以传递给 {anchorName appendL}`plusL` 等函数。
实际上，类型 {anchorTerm moreFun}`(n : Nat) → Vect String n` 和 {anchorTerm moreNames}`(n : Nat) → Vect String (Nat.plusL 0 n)` 定义相等。

{anchorName againFun}`n` 和 {anchorTerm againFun}`Nat.plusL 0 n` 是定义相等的原因是 {anchorName plusL}`plusL` 对的_第一个_参数进行模式匹配。
这在别的情况下会导致问题：{anchorTerm moreFun}`(n : Nat) → Vect String n` 与 {anchorTerm stuckFun}`(n : Nat) → Vect String (Nat.plusL n 0)` 并_不_定义相等，尽管0应该同时是加法的左和右单位元。
这是因为模式匹配在遇到变量时会卡住。
在 {anchorName stuckFun}`n` 的实际值变得已知之前，没有办法知道应该选择 {anchorTerm stuckFun}`Nat.plusL n 0` 的哪种情形。

同样的问题出现在查询示例中的 {anchorName Row (module:=Examples.DependentTypes.DB)}`Row` 函数中。
类型 {anchorTerm RowStuck (module:=Examples.DependentTypes.DB)}`Row (c :: cs)` 不会规约到任何数据类型，因为 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 的定义对单例列表和至少有两个条目的列表的处理方式不同。
换句话说，当尝试将变量 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`cs` 与具体的 {anchorName moreNames}`List` 构造子匹配时会卡住。
这就是为什么几乎每个拆分或构造 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 的函数都需要与 {anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row` 本身对应的三种情形：为了获得模式匹配或构造子可以使用的具体类型。

{anchorName appendL8}`appendL` 中缺失的情形需要一个 {lit}`Vect α (Nat.plusL n k + 1)`。
索引中的 {lit}`+ 1` 表明下一步是使用 {anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons`：
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
一个对 {anchorName appendL9}`appendL` 的递归调用可以构造一个具有所需长度的 {anchorName appendL9}`Vect` ：

```anchor appendL9
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
```
既然程序完成了，删除对 {anchorName appendL9}`n` 和 {anchorName appendL9}`k` 的显式匹配使得这个函数更容易阅读和调用：

```anchor appendL
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
```

比较类型使用定义相等意味着定义相等中涉及的所有内容，包括函数的内部定义，都成为使用依值类型和索引族的程序的_接口_的一部分。
在类型中暴露函数的内部实现意味着重构暴露的函数可能导致使用它的程序无法通过类型检查。
特别是，{anchorName appendL}`plusL` 在 {anchorName appendL}`appendL` 的类型中使用的事实意味着 {anchorName appendL}`plusL` 的使用不能被等价的 {anchorName plusR}`plusR` 替换。

# 在加法上卡住
%%%
tag := "stuck-addition"
%%%

如果使用 {anchorName appendR}`plusR` 定义 append 会发生什么？
让我们从头来过。使用显式长度并用占位符填充每种情形，会显示以下有用的错误消息：
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
然而，尝试在第一个占位符上添加一个 {anchorTerm appendR3}`Vect α k` 类型注释会导致类型不匹配错误：
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
这个错误指出 {anchorTerm plusRinfo}`Nat.plusR 0 k` 和 {anchorName plusRinfo}`k` _不_定义相等。

:::paragraph
这是因为 {anchorName plusR}`plusR` 有以下定义：

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
它的模式匹配发生在_第二_个参数上，而非第一个，这意味着该位置上的变量 {anchorName plusRinfo}`k` 阻止了它的规约。
Lean 标准库中的 {anchorName plusRinfo}`Nat.add` 等价于 {anchorName plusRinfo}`plusR` ，而不是 {anchorName plusRinfo}`plusL` ，因此尝试在这个定义中使用它会导致完全相同的问题：
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

加法在变量上_卡住_。
解决它需要 {ref "equality-and-ordering"}[命题相等]。
:::

# 命题相等性
%%%
tag := "propositional-equality"
%%%

命题相等性是两个表达式相等的数学陈述。
Lean 在需要时会自动检查定义相等性，但命题相等性需要显式证明。
一旦一个相等命题被证明，它就可以在程序中被使用，从而将一个类型替换为等式另一侧的类型，从而解套卡住的类型检查器。

定义相等性只规定了很有限的相等性，所以它可以被算法自动地检查。
命题相等性要丰富得多，但计算机通常无法检查两个表达式是否命题相等，尽管它可以验证所谓的证明是否实际上是一个证明。
定义相等和命题相等之间的分裂代表了人类和机器之间的分工：最无聊的相等性作为定义相等的一部分被自动检查，从而使人类思维可以处理命题相等中可用的有趣问题。
同样，定义相等性由类型检查器自动调用，而命题相等必须明确地被调用。


在 {ref "props-proofs-indexing"}[命题、证明和索引] 中，一些相等性命题使用 {tactic}`decide` 证明。
那里面的相等性命题实际上已经定义相等。
通常，命题相等性的证明是通过首先将它们变成定义相等或接近现有证明的相等性的形式，然后使用像 {tactic}`decide` 或 {tactic}`simp` 这样的策术来处理简化后的情形。
{tactic}`simp` 策术非常强大：它使用许多快速的自动化工具来构造证明。
一个更简单的策术叫做 {kw}`rfl` ，它专门使用定义相等来证明命题相等。
{kw}`rfl` 的名称来自_反射性（reflexivity）_的缩写，它是相等性的一个属性：一切都等于自己。

解决 {anchorName appendR}`appendR` 需要一个证明，即 {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k`。它们并不定义相等，因为 {anchorName plusR}`plusR` 在第二个参数的变量上卡住了。
为了让它计算，{anchorName plusR_zero_left1}`k` 必须是一个具体的构造子。
这时，我们可以使用模式匹配。

:::paragraph
因为 {anchorName plusR_zero_left1}`k` 可以是_任何_ {anchorName plusR_zero_left1}`Nat` ，所以我们需要一个对任何 {anchorName plusR_zero_left1}`k` 都能返回 {anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k` 的证据的函数。
它的类型应该为 {anchorTerm plusR_zero_left1}`(k : Nat) → k = Nat.plusR 0 k`。
进行模式匹配并输入占位符后得到以下信息：
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
将 {anchorName plusR_zero_left1}`k` 通过模式匹配细化为 {anchorTerm plusR_zero_left1}`0` 后，第一个占位符需要一个定义相等的命题的证据。
使用 {kw}`rfl` 策术完成它，只留下第二个占位符：
```anchor plusR_zero_left3
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => _
```
:::

第二个占位符有点棘手。
表达式 {anchorTerm plusRStep}`Nat.plusR 0 k + 1` 定义相等于 {anchorTerm plusRStep}`Nat.plusR 0 (k + 1)`。
这意味着目标也可以写成 {anchorTerm plusR_zero_left4}`k + 1 = Nat.plusR 0 k + 1`：
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
在等式命题两侧的 {anchorTerm plusR_zero_left4}`+ 1` 下面是函数本身返回的另一个实例。
换句话说，对 {anchorName plusR_zero_left4}`k` 的递归调用将返回 {anchorTerm plusR_zero_left4}`k = Nat.plusR 0 k` 的证据。
如果相等性不适用于函数参数，那么它就不是相等性。
换句话说，如果 {anchorTerm congr}`x = y` ，那么 {anchorTerm congr}`f x = f y` 。
标准库包含一个函数 {anchorName congr}`congrArg`，它接受一个函数和一个相等性证明，并返回一个新的证明，其中函数已经应用于等式的两侧。
在这种情形下，函数是 {anchorTerm plusR_zero_left_done}`(· + 1)`：

```anchor plusR_zero_left_done
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

:::paragraph
因为这实际上是一个命题的证明，所以应该声明为 {kw}`theorem`：

```anchor plusR_zero_left_thm
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

命题相等性可以使用右三角运算符 {anchorTerm appendRsubst}`▸` 在程序中使用。
给定一个相等性证明作为第一个参数，另一个表达式作为第二个参数，这个运算符将第二个参数类型中等式左侧的实例替换为等式的右侧的实例。
换句话说，以下定义不会导致类型错误：
```anchor appendRsubst
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
第一个占位符有预期的类型：
```anchorError appendRsubst
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
现在可以用 {anchorName appendR5}`ys` 填充它：
```anchor appendR5
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
```

填充剩下的占位符需要解套另一个卡住的加法：
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
这里，要证明的命题是 {anchorTerm plusR_succ_left}`Nat.plusR (n + 1) k = Nat.plusR n k + 1`，可以使用 {anchorTerm appendRsubst}`▸` 将 {anchorTerm appendRsubst}`+ 1` 拉到表达式的顶部，使其与 {anchorName Vect}`cons` 的索引匹配。

证明是一个递归函数，它对 {anchorName appendR}`plusR` 的第二个参数 {anchorName appendR5}`k` 进行模式匹配。
这是因为 {anchorName appendR5}`plusR` 自身也是对第二个参数进行模式匹配，所以证明可以相同的模式匹配解套它，将计算行为暴露出来。
证明的框架与 {anchorName appendR}`plusR_zero_left` 非常相似：
```anchor plusR_succ_left_0
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
```

剩下的情形的类型在定义上等于 {anchorTerm congr}`Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1`，因此可以像 {anchorName plusR_zero_left_thm}`plusR_zero_left` 一样用 {anchorName congr}`congrArg` 解决：
```anchorError plusR_succ_left_2
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
```
证明就此完成：

```anchor plusR_succ_left
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
```

完成的证明可以用来解套 {anchorName appendR}`appendR` 中的第二个情形：

```anchor appendR
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
```
如果再次将 {anchorName appendR}`appendR` 的长度参数改成隐式参数，它们在证明中也将不具有显示的名字。
然而，Lean 的类型检查器有足够的信息自动填充它们，只有唯一的值可以使类型匹配：

```anchor appendRImpl
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
```

# 优势和劣势
%%%
tag := "dependent-types-pros-and-cons"
%%%

索引族有一个重要的特性：对它们进行模式匹配会影响定义相等性。
例如，在 {anchorTerm Vect}`Vect` 上的 {kw}`match` 表达式中的 {anchorName Vect}`nil` 情形中，长度会直接_变成_ {anchorTerm moreNames}`0`。
定义相等非常好用，因为它从不需要显式调用。

然而，使用依赖类型和模式匹配的定义相等在软件工程上有严重的缺点。
首先，在类型中使用的函数需要额外编写，同时在类型中方便使用的实现并不一定是一个高效的实现。
一旦一个函数在类型中被使用，它的实现就成为接口的一部分，导致未来重构困难。
其次，检查定义相等性可能会很慢。
当检查两个表达式是否定义相等时，如果相关的函数复杂并且有许多抽象层，Lean 可能需要运行大量代码。
第三，定义相等检查失败而报告的错误信息可能很难理解，因为它们通常包含了函数内部实现相关的信息。
并不总是容易理解错误消息中表达式的来源。
最后，在一组索引族和依赖类型函数中编码非平凡的不变性通常是脆弱的。
当函数的规约行为不能方便地提供需要的定义相等性时，通常需要更改系统中的早期定义。
另一种方法是在程序中的很多地方手动引入相等性的证明，但这样会变得非常麻烦。

在惯用的 Lean 代码中，带有索引的数据类型并不经常使用。
相反，子类型和显式命题通常用于保证重要的不变性。
这种方法涉及许多显式证明，而很少直接使用定义相等。
为了可以被用作一个交互式定理证明器，Lean 的很多设计是为了使显式证明方便。
一般来说，在大多数情况下，应该优先考虑这种方法。

然而，理解索引族是重要的。
诸如 {anchorName plusR_zero_left_thm}`plusR_zero_left` 和 {anchorName plusR_succ_left}`plusR_succ_left` 之类的递归函数实际上是_使用了数学归纳法的证明_。
递归的基情形对应于归纳的基情形，递归调用则表示对归纳假设的使用。
更一般地说，Lean 中的新命题通常被定义为证据的归纳类型，这些归纳类型通常具有索引。
证明定理的过程实际上是在构造具有这些类型的表达式，这个过程与本节中的证明非常相似。
此外，索引数据类型有时确实是最佳选择。熟练掌握它们的使用是知道何时使用它们的一个重要部分。



# 练习
%%%
tag := "dependent-type-pitfalls-exercises"
%%%

 * 使用类似于 {anchorName plusR_succ_left}`plusR_succ_left` 的递归函数，证明对于所有的 {anchorName moreNames}`Nat` {anchorName exercises}`n` 和 {anchorName exercises}`k`，{anchorTerm exercises}`n.plusR k = n + k`。
 * 写一个在 {anchorName moreNames}`Vect` 上的函数，其中 {anchorName plusR}`plusR` 比 {anchorName plusL}`plusL` 更自然：{anchorName plusL}`plusL` 需要在定义中显示使用（命题相等性的）证明。
