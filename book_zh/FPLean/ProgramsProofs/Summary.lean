import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "总结" =>
%%%
tag := "programs-proofs-summary"
%%%

# 尾递归
%%%
tag := none
%%%

尾递归是一种递归，其中递归调用的结果会立即返回，而非以其他方式使用。
这些递归调用称为「尾调用」。尾调用很有趣，因为它们可以编译成跳转指令而非调用指令，
并且可以重新使用当前栈帧，而非压入新的一帧。换句话说，尾递归函数实际上就是循环。

使递归函数更快的常用方法是使用累加器传递风格对其进行重写。
它不使用调用栈来记住如何处理递归调用的结果，而是使用一个名为「累加器」的附加参数来收集此信息。
例如，用于反转列表的尾递归函数的累加器按相反顺序包含已经处理过的列表项。

在 Lean 中，只有自尾调用（self-tail-call）会被优化为循环。
换句话说，两个以互相尾调用结束的函数不会被优化。

# 引用计数与原地更新
%%%
tag := none
%%%

与 Java、C# 和大多数 JavaScript 实现中那样使用跟踪垃圾收集器不同，
Lean 使用引用计数进行内存管理。这意味着内存中的每个值都包含一个字段，
该字段跟踪引用它的其他值的数量，并且运行时系统在引用出现或消失时维护这些计数。
引用计数也用在了 Python、PHP 和 Swift 中。

当要求分配一个新对象时，Lean 的运行时系统能够回收引用计数降为零的现有对象。
此外，如果数组的引用计数为一，则数组操作（如 {anchorName names}`Array.set` 和 {anchorName names}`Array.swap`）将修改原数组，
而非分配一个修改后的副本。如果 {anchorName names}`Array.swap` 持有对数组的唯一引用，
那么程序的其他部分就无法分辨它是被改变了还是被复制了。

在 Lean 中编写高效的代码需要使用尾递归，并小心确保大数组被唯一使用。
虽然可以通过检查函数的定义来识别尾调用，但了解一个值是否被唯一引用可能需要阅读整个程序。
调试辅助函数 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 可以用在程序的关键位置来检查一个值是否被共享。

# 证明程序的正确性
%%%
tag := none
%%%

以累加器传递样式重写程序，或进行其他使程序运行更快的转换，也可能会让程序更难理解。
保留程序的原始版本（正确性更加明显）是有用的，然后将其用作优化版本的可执行规范。
虽然单元测试等技术在 Lean 中与在任何其他语言中一样有效，
但 Lean 还允许使用数学证明来完全确保函数的两个版本对 *所有* 可能的输入返回相同的结果。

通常，证明两个函数相等是使用函数外延性（{kw}`funext` 策略）完成的，
该原则指出如果两个函数对每个输入都返回相同的值，则它们相等。
如果函数是递归的，那么归纳法通常是证明它们输出相同的好方法。
通常，函数的递归定义会对某个特定参数进行递归调用；这个参数是归纳的好选择。
在某些情况下，归纳假设不够强。
解决这个问题通常需要思考如何构建定理陈述的更通用版本，以提供足够强的归纳假设。
特别是，为了证明一个函数等价于一个累加器传递版本，
需要一个将任意初始累加器值与原始函数的最终结果联系起来的定理陈述。

# 安全的数组索引
%%%
tag := none
%%%

类型 {anchorTerm names}`Fin n` 表示严格小于 {anchorName names}`n` 的自然数。
{anchorName names}`Fin` 是“finite”（有限）的缩写。
与子类型一样，{anchorTerm names}`Fin n` 是一个包含 {anchorName names}`Nat` 和证明该 {anchorName names}`Nat` 小于 {anchorName names}`n` 的结构。
不存在类型为 {anchorTerm names}`Fin 0` 的值。

如果 {anchorName names}`arr` 是一个 {anchorTerm names}`Array α`，那么 {anchorTerm names}`Fin arr.size` 总是包含一个适合作为 {anchorName names}`arr` 索引的数字。

Lean 为 {anchorName names}`Fin` 提供了大多数有用的数字类型类的实例。
{anchorName names}`Fin` 的 {anchorName names}`OfNat` 实例执行模运算，而不是在提供的数字大于 {anchorName names}`Fin` 可以接受的范围时在编译时失败。

# 临时证明
%%%
tag := none
%%%

有时，假装一个陈述已被证明而实际上没有做证明工作是有用的。
当确保一个陈述的证明适用于某些任务时，这很有用，例如在另一个证明中进行重写，
确定数组访问是安全的，或者表明递归调用是在比原始参数更小的值上进行的。
花时间证明某件事，结果却发现其他证明会更有用，这是非常令人沮丧的。

{anchorTerm names}`sorry` 策略使 Lean 临时接受一个陈述，就好像它是一个真正的证明一样。
它可以被看作类似于 C# 中抛出 {CSharp}`NotImplementedException` 的存根方法。
任何依赖于 {anchorTerm names}`sorry` 的证明在 Lean 中都会包含一个警告。

小心！
{anchorTerm names}`sorry` 策略可以证明_任何_陈述，甚至是错误的陈述。
证明 {anchorTerm names}`3 < 2` 可能会导致越界数组访问持续到运行时，从而意外地使程序崩溃。
在开发过程中使用 {anchorTerm names}`sorry` 很方便，但将其保留在代码中是危险的。

# 证明终止性
%%%
tag := none
%%%

当一个递归函数不使用结构体递归时，Lean 无法自动确定它是否停机。
在这些情况下，该函数可以用 {kw}`partial` 标记为偏函数。但是，也可以提供证明函数停机的证明。

偏函数有一个关键的缺点：它们不能在类型检查或证明中展开。
这意味着 Lean 作为交互式定理证明器的价值不能应用于它们。
此外，证明一个预期停机的函数实际上总是停机，可以消除更多潜在的 bug 来源。

递归函数末尾允许的 {kw}`termination_by` 子句可用于指定递归函数停机的原因。
该子句将函数的参数映射到一个表达式，该表达式预期在每次递归调用时都会变小。
可能减小的表达式的示例包括不断增长的数组索引与数组大小之间的差、
每次递归调用时减半的列表长度，或一对列表，其中恰好一个在每次递归调用时都会缩小。

Lean 包含的证明自动化可以自动确定某些表达式在每次调用时都会缩小，但许多有趣的程序需要手动证明。
这些证明可以使用 {kw}`have` 提供，{kw}`have` 是 {kw}`let` 的一个版本，旨在局部提供证明而非值。

编写递归函数的一个好方法是从声明它们为 {kw}`partial` 开始，并通过测试调试它们，
直到它们返回正确的答案。然后，可以删除 {kw}`partial` 并用 {kw}`termination_by` 子句替换它。
Lean 会在需要证明的每个递归调用上放置错误高亮，其中包含需要证明的语句。
每个这样的语句都可以放在 {kw}`have` 中，证明为 {anchorTerm names}`sorry`。
如果 Lean 接受该程序并且它仍然通过测试，最后一步就是实际证明使 Lean 接受它的定理。
这种方法可以防止浪费时间来证明一个有缺陷的程序的停机性。
