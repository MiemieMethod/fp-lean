import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "小结" =>
%%%
tag := "getting-to-know-summary"
file := "Summary"
%%%

# 求值表达式
%%%
tag := none
file := "Evaluating-Expressions"
%%%

在 Lean 中，计算发生在表达式被求值时。
这遵循数学表达式的通常规则：按照通常的运算顺序，子表达式被其值替换，直到整个表达式成为一个值。
在对 {kw}`if` 或 {kw}`match` 求值时，分支中的表达式不会被求值，直到条件的值或匹配对象的值已经确定。

变量一旦被赋予一个值，就永远不会改变。
与数学类似但不同于大多数编程语言，Lean 中的变量只是值的占位符，而不是可以写入新值的地址。
变量的值可以来自使用 {kw}`def` 的全局定义、使用 {kw}`let` 的局部定义、作为函数的具名参数，或来自模式匹配。

# 函数
%%%
tag := none
file := "Functions"
%%%

Lean 中的函数是一等值，这意味着它们可以作为参数传递给其他函数，可以保存在变量中，并且可以像任何其他值一样使用。
每个 Lean 函数都恰好接受一个参数。
为了编码接受多个参数的函数，Lean 使用一种称为柯里化的技术：提供第一个参数后会返回一个期待其余参数的函数。
为了编码不接受参数的函数，Lean 使用 {moduleName}`Unit` 类型，这是可能提供信息最少的参数。

创建函数主要有三种方式：
1. 匿名函数使用 {kw}`fun` 编写。
例如，一个交换 {anchorName fragments}`Point` 字段的函数可以写作 {anchorTerm swapLambda}`fun (point : Point) => { x := point.y, y := point.x : Point }`
2. 非常简单的匿名函数可以通过在括号内放置一个或多个居中的点 {anchorTerm subOneDots}`·` 来书写。
每个居中的点都会成为函数的一个参数，而圆括号界定其函数体。
   例如，一个从其参数中减去一的函数可以写作 {anchorTerm subOneDots}`(· - 1)`，而不是写作 {anchorTerm subOneDots}`fun x => x - 1`。
3. 函数可以通过 {kw}`def` 或 {kw}`let` 来定义，方式是添加参数列表或使用模式匹配记法。

# 类型
%%%
tag := none
file := "Types"
%%%

Lean 会检查每个表达式都有一个类型。
诸如 {anchorName fragments}`Int`、{anchorName fragments}`Point`、{anchorTerm fragments}`{α : Type} → Nat → α → List α` 和 {anchorTerm fragments}`Option (String ⊕ (Nat × String))` 这样的类型描述了最终可能为某个表达式得到的值。
与其他语言一样，Lean 中的类型可以为程序表达轻量级规约，并由 Lean 编译器检查，从而免去某些类别的单元测试。
与大多数语言不同，Lean 的类型还可以表达任意数学内容，将编程与定理证明这两个世界统一起来。
虽然使用 Lean 证明定理大体上超出了本书范围，_[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)_ 包含了关于这一主题的更多信息。

某些表达式可以被赋予多个类型。
例如，{lit}`3` 可以是 {anchorName fragments}`Int`，也可以是 {anchorName fragments}`Nat`。
在 Lean 中，应将其理解为两个不同的表达式：一个具有类型 {anchorName fragments}`Nat`，另一个具有类型 {anchorName fragments}`Int`，它们只是碰巧以相同的方式书写；而不是将其理解为同一个事物具有两个不同的类型。

Lean 有时能够自动确定类型，但类型往往必须由用户提供。
这是因为 Lean 的类型系统具有如此强的表达能力。
即使 Lean 能找到一个类型，它也未必能找到所期望的类型——{lit}`3` 可能本意是作为 {anchorName fragments}`Int` 使用，但如果没有进一步的约束，Lean 会赋予它类型 {anchorName fragments}`Nat`。
一般而言，显式写出大多数类型是一个好习惯，只让 Lean 填充那些非常显然的类型。
这会改善 Lean 的错误消息，并有助于使程序员的意图更加清晰。

某些函数或数据类型以类型作为参数。
它们称为_多态的_。
多态性允许编写诸如计算列表长度的程序，而无需关心列表中条目的类型。
由于类型在 Lean 中是一等的，多态性不需要任何特殊语法，因此类型会像其他参数一样被传递。
在函数类型中为参数命名，允许后续类型提及该名称；当函数被应用于某个参数时，所得项的类型通过将参数名称替换为实际应用到它的值而得到。

# 结构与归纳类型
%%%
tag := none
file := "Structures-and-Inductive-Types"
%%%

可以使用 {kw}`structure` 或 {kw}`inductive` 特性向 Lean 引入全新的数据类型。
这些新类型不被认为等价于任何其他类型，即使它们的定义在其他方面完全相同。
数据类型具有_构造子_，用于说明其值可以如何被构造，并且每个构造子接受若干个参数。
Lean 中的构造子不同于面向对象语言中的构造器：Lean 的构造子是惰性的、用于保存数据的容器，而不是初始化已分配对象的主动代码。

通常，{kw}`structure` 用于引入积类型（即只有一个构造子且该构造子接受任意数量参数的类型），而 {kw}`inductive` 用于引入和类型（即具有许多不同构造子的类型）。
用 {kw}`structure` 定义的数据类型会为每个字段提供一个访问器函数。
结构体和归纳数据类型都可以通过模式匹配来使用；模式匹配使用调用相应构造子的语法的一个子集，暴露存储在构造子内部的值。
模式匹配意味着，知道如何创建一个值，也就意味着知道如何使用它。

# 递归
%%%
tag := none
file := "Recursion"
%%%

当正在定义的名称在定义本身中被使用时，该定义就是递归的。
因为 Lean 除了是一门编程语言之外还是一个交互式定理证明器，所以递归定义受到某些限制。
在 Lean 的逻辑侧，循环定义可能导致逻辑不一致。

为了确保递归定义不会破坏 Lean 的逻辑侧面，Lean 必须能够证明所有递归函数都会终止，无论它们以什么参数被调用。
在实践中，这意味着：要么所有递归调用都在输入的结构上更小的部分上执行，从而确保总是朝着基本情形取得进展；要么用户必须提供某种其他证据，证明该函数总会终止。
类似地，递归归纳类型不允许具有一个接受从该类型_出发_的函数作为参数的构造子，因为这会使编码非终止函数成为可能。
