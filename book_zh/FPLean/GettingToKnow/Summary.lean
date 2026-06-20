import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "总结" =>
%%%
tag := "getting-to-know-summary"
%%%

# 表达式求值
%%%
tag := none
%%%

在 Lean 中，计算在表达式被求值时发生。
这遵循数学表达式的通常规则：子表达式按照通常的运算顺序被它们的值替换，直到整个表达式变成一个值。
在求值 {kw}`if` 或 {kw}`match` 时，分支中的表达式直到条件或匹配主体的值被找到后才被求值。

一旦被赋值，变量就永远不会改变。
与数学类似，但与大多数编程语言不同，Lean 变量只是值的占位符，而不是可以写入新值的地址。
变量的值可以来自使用 {kw}`def` 的全局定义、使用 {kw}`let` 的局部定义、作为函数的命名参数，或来自模式匹配。

# 函数
%%%
tag := none
%%%

在 Lean 中，函数是一等公民，这意味着它们可以作为参数传递给其他函数，保存在变量中，并像任何其他值一样使用。
每个 Lean 函数只接受一个参数。
为了编码一个接受多个参数的函数，Lean 使用一种称为柯里化的技术，即提供第一个参数会返回一个期望剩余参数的函数。
为了编码一个不接受任何参数的函数，Lean 使用 {moduleName}`Unit` 类型，这是信息量最少的参数。

创建函数主要有三种方法：
1. 匿名函数使用 {kw}`fun` 编写。
   例如，一个交换 {anchorName fragments}`Point` 字段的函数可以写成 {anchorTerm swapLambda}`fun (point : Point) => { x := point.y, y := point.x : Point }`
2. 非常简单的匿名函数可以通过在括号内放置一个或多个居中点 {anchorTerm subOneDots}`·` 来编写。
   每个居中点都成为函数的一个参数，括号界定其主体。
   例如，一个从其参数中减去一的函数可以写成 {anchorTerm subOneDots}`(· - 1)` 而不是 {anchorTerm subOneDots}`fun x => x - 1`。
3. 函数可以使用 {kw}`def` 或 {kw}`let` 通过添加参数列表或使用模式匹配表示法来定义。

# 类型
%%%
tag := none
%%%

Lean 检查每个表达式都有一个类型。
类型，例如 {anchorName fragments}`Int`、{anchorName fragments}`Point`、{anchorTerm fragments}`{α : Type} → Nat → α → List α` 和 {anchorTerm fragments}`Option (String ⊕ (Nat × String))`，描述了最终可能为表达式找到的值。
与其他语言一样，Lean 中的类型可以表达由 Lean 编译器检查的程序的轻量级规范，从而无需某些类别的单元测试。
与大多数语言不同，Lean 的类型还可以表达任意数学，从而统一了编程和定理证明的世界。
虽然使用 Lean 证明定理超出了本书的范围，但 *[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)* 包含有关此主题的更多信息。

有些表达式可以被赋予多种类型。
例如，{lit}`3` 可以是 {anchorName fragments}`Int` 或 {anchorName fragments}`Nat`。
在 Lean 中，这应该被理解为两个独立的表达式，一个类型为 {anchorName fragments}`Nat`，另一个类型为 {anchorName fragments}`Int`，它们恰好以相同的方式编写，而不是同一事物的两种不同类型。

Lean 有时能够自动确定类型，但通常需要用户提供类型。
这是因为 Lean 的类型系统非常富有表现力。
即使 Lean 可以找到一个类型，它也可能找不到所需的类型——{lit}`3` 可能旨在用作 {anchorName fragments}`Int`，但如果没有进一步的约束，Lean 会给它 {anchorName fragments}`Nat` 类型。
总的来说，明确编写大多数类型是一个好主意，只让 Lean 填充非常明显的类型。
这可以改善 Lean 的错误消息，并有助于使程序员的意图更清晰。

一些函数或数据类型将类型作为参数。
它们被称为*多态*。
多态性允许程序计算列表的长度，而无需关心列表中条目的类型。
因为类型在 Lean 中是一等公民，所以多态性不需要任何特殊的语法，因此类型的传递方式与其他参数一样。
在函数类型中命名参数允许后续类型引用该名称，当函数应用于参数时，通过将参数的名称替换为应用它的实际值来找到结果项的类型。

# 结构和归纳类型
%%%
tag := none
%%%

可以使用 {kw}`structure` 或 {kw}`inductive` 功能将全新的数据类型引入 Lean。
这些新类型不被认为等同于任何其他类型，即使它们的定义在其他方面是相同的。
数据类型具有*构造函数*，用于解释其值的构造方式，每个构造函数都接受一定数量的参数。
Lean 中的构造函数与面向对象语言中的构造函数不同：Lean 的构造函数是数据的惰性持有者，而不是初始化已分配对象的活动代码。

通常，{kw}`structure` 用于引入乘积类型（即，只有一个构造函数并接受任意数量参数的类型），而 {kw}`inductive` 用于引入和类型（即，具有许多不同构造函数的类型）。
使用 {kw}`structure` 定义的数据类型为每个字段提供一个访问器函数。
结构和归纳数据类型都可以通过模式匹配来使用，它使用用于调用所述构造函数的语法的子集来公开存储在构造函数内部的值。
模式匹配意味着知道如何创建值就意味着知道如何使用它。

# 递归
%%%
tag := none
%%%

当被定义的名称在定义本身中使用时，定义是递归的。
因为 Lean 除了是一种编程语言之外，还是一个交互式定理证明器，所以对递归定义有一定的限制。
在 Lean 的逻辑方面，循环定义可能导致逻辑不一致。

为了确保递归定义不会破坏 Lean 的逻辑方面，Lean 必须能够证明所有递归函数都会终止，无论它们使用什么参数调用。
在实践中，这意味着要么递归调用都在输入的结构上更小的部分上执行，这确保了总是朝着基本情况取得进展，要么用户必须提供其他一些证据来证明函数总是终止。
同样，递归归纳类型不允许具有将*来自*该类型的函数作为参数的构造函数，因为这会使编码非终止函数成为可能。
