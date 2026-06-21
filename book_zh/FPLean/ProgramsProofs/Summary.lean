import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "小结" =>
%%%
tag := "programs-proofs-summary"
file := "Summary"
%%%

# 尾递归
%%%
tag := none
file := "Tail-Recursion"
%%%

尾递归是一种递归，其中递归调用的结果会被立即返回，而不是以其他方式使用。
这些递归调用称为 _尾调用_。
尾调用之所以值得关注，是因为它们可以被编译为跳转指令而非调用指令，并且可以重用当前栈帧，而不是压入新的栈帧。
换言之，尾递归函数实际上就是循环。

使递归函数更快的一种常见方法是将其改写为累加器传递风格。
这种方法不使用调用栈来记住应当如何处理递归调用的结果，而是使用一个称为_累加器_的额外参数来收集这些信息。
例如，一个反转列表的尾递归函数的累加器包含已经见过的列表项，且顺序相反。

在 Lean 中，只有自尾调用会被优化为循环。
换言之，如果两个函数都以对另一个函数的尾调用结束，它们不会被优化。

# 引用计数与原地更新
%%%
tag := none
file := "Reference-Counting-and-In-Place-Updates"
%%%

Lean 并不使用 Java、C# 以及大多数 JavaScript 实现中所采用的跟踪式垃圾收集器，而是使用引用计数进行内存管理。
这意味着内存中的每个值都包含一个字段，用来记录有多少其他值引用它，并且运行时系统会在引用出现或消失时维护这些计数。
引用计数也用于 Python、PHP 和 Swift。

当被要求分配一个新对象时，Lean 的运行时系统能够回收引用计数正在降为零的现有对象。
此外，诸如 {anchorName names}`Array.set` 和 {anchorName names}`Array.swap` 这样的数组操作，如果数组的引用计数为一，则会变更该数组，而不是分配一个修改后的副本。
如果 {anchorName names}`Array.swap` 持有对某个数组的唯一引用，那么程序的其他任何部分都无法分辨它是被变更了而不是被复制了。

在 Lean 中编写高效代码需要使用尾递归，并且需要谨慎确保大型数组被唯一地使用。
虽然可以通过检查函数定义来识别尾调用，但要理解某个值是否被唯一引用，可能需要阅读整个程序。
调试辅助工具 {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` 可以在程序中的关键位置使用，以检查某个值未被共享。

# 证明程序正确
%%%
tag := none
file := "Proving-Programs-Correct"
%%%

将程序改写为累加器传递风格，或者进行其他使其运行更快的变换，也可能使程序更难理解。
保留更明显正确的程序原始版本，并将其用作优化版本的可执行规范，可能很有用。
虽然单元测试等技术在 Lean 中和在任何其他语言中一样有效，但 Lean 还允许使用数学证明来完全确保这两个函数版本对_所有可能的_输入都返回相同的结果。

通常，证明两个函数相等是通过函数外延性（{kw}`funext` 策略）完成的；函数外延性这一原则表明，如果两个函数对每个输入都返回相同的值，那么它们相等。
如果这些函数是递归的，那么归纳通常是证明其输出相同的好方法。
通常，函数的递归定义会在某个特定参数上进行递归调用；这个参数是进行归纳的良好选择。
在某些情况下，归纳假设不够强。
修正这一问题通常需要思考如何构造定理陈述的更一般版本，以提供足够强的归纳假设。
特别地，为了证明一个函数等价于其传递累加器的版本，需要一个将任意初始累加器值与原函数最终结果关联起来的定理陈述。

# 安全的数组索引
%%%
tag := none
file := "Safe-Array-Indices"
%%%

类型 {anchorTerm names}`Fin n` 表示严格小于 {anchorName names}`n` 的自然数。
{anchorName names}`Fin` 是“finite”的缩写。
与子类型一样，一个 {anchorTerm names}`Fin n` 是一个结构，其中包含一个 {anchorName names}`Nat`，以及这个 {anchorName names}`Nat` 小于 {anchorName names}`n` 的证明。
不存在类型 {anchorTerm names}`Fin 0` 的值。

如果 {anchorName names}`arr` 是一个 {anchorTerm names}`Array α`，则 {anchorTerm names}`Fin arr.size` 始终包含一个适合作为 {anchorName names}`arr` 索引的数。

Lean 为 {anchorName names}`Fin` 提供了大多数有用数值类型类的实例。
{anchorName names}`Fin` 的 {anchorName names}`OfNat` 实例执行模算术；如果所给数字大于 {anchorName names}`Fin` 能接受的范围，它们不会在编译时失败。

# 临时证明
%%%
tag := none
file := "Provisional-Proofs"
%%%

有时，假装某个陈述已经被证明而实际上不去完成其证明，可能是有用的。
这在确认某个陈述的证明是否适合某项任务时很有用，例如在另一个证明中进行重写、判定数组访问是安全的，或说明某个递归调用是在比原始参数更小的值上进行的。
花时间证明某个东西之后，才发现另一个证明本会更加有用，这是非常令人沮丧的。

{anchorTerm names}`sorry` 策略会使 Lean 暂时接受一个陈述，仿佛它是一个真正的证明。
它可以被看作类似于 C# 中抛出 {CSharp}`NotImplementedException` 的存根方法。
任何依赖 {anchorTerm names}`sorry` 的证明都会在 Lean 中包含一条警告。

小心！
{anchorTerm names}`sorry` 策略可以证明_任何_陈述，甚至包括假陈述。
证明 {anchorTerm names}`3 < 2` 可能导致越界数组访问持续到运行时，从而使程序意外崩溃。
在开发期间使用 {anchorTerm names}`sorry` 很方便，但将它保留在代码中是危险的。

# 证明终止性
%%%
tag := none
file := "Proving-Termination"
%%%

当递归函数不使用结构递归时，Lean 无法自动判定它会终止。
在这些情况下，可以直接将该函数标记为 {kw}`partial`。
然而，也可以提供该函数会终止的证明。

部分函数有一个关键缺点：它们不能在类型检查期间或证明中被展开。
这意味着 Lean 作为交互式定理证明器的价值无法应用于它们。
此外，证明一个预期会终止的函数实际上总是会终止，还能消除一个潜在的错误来源。

函数末尾允许出现的 {kw}`termination_by` 子句可用于指定递归函数终止的原因。
该子句将函数的参数映射到一个表达式，并期望该表达式在每次递归调用时都变得更小。
可能递减的表达式示例包括：数组中一个增长的索引与数组大小之间的差、每次递归调用都被切成两半的列表的长度，或一对列表，其中恰有一个在每次递归调用时缩短。

Lean 包含证明自动化功能，能够自动判定某些表达式在每次调用时都会缩小，但许多有趣的程序仍需要手工证明。
这些证明可以用 {kw}`have` 提供；{kw}`have` 是 {kw}`let` 的一个版本，旨在局部提供证明而非值。

编写递归函数的一种好方法，是先将它们声明为 {kw}`partial`，并通过测试进行调试，直到它们返回正确答案。
然后，可以移除 {kw}`partial`，并用一个 {kw}`termination_by` 子句替换它。
Lean 会在每个需要证明的递归调用处放置错误高亮，其中包含需要证明的陈述。
这些陈述中的每一个都可以放入一个 {kw}`have` 中，并将证明写作 {anchorTerm names}`sorry`。
如果 Lean 接受该程序，并且它仍然通过测试，那么最后一步就是实际证明那些使 Lean 能接受它的定理。
这种方法可以避免把时间浪费在证明一个有缺陷的程序会终止上。
