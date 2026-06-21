import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.SpecialTypes"

#doc (Manual) "特殊类型" =>
%%%
tag := "runtime-special-types"
file := "Special-Types"
%%%

理解数据在内存中的表示非常重要。
通常，可以从数据类型的定义理解其表示。
每个构造子都对应于内存中的一个对象，该对象有一个头部，其中包含一个标签和一个引用计数。
构造子的每个参数都表示为指向某个其他对象的指针。
换言之，{anchorName all}`List` 确实是一个链表，而从 {kw}`structure` 中取出一个字段确实只是沿着指针追踪。

然而，这条规则有一些重要例外。
编译器会特殊处理若干类型。
例如，类型 {anchorName all}`UInt32` 被定义为 {anchorTerm all}`Fin (2 ^ 32)`，但在运行时它会被替换为一个基于机器字的真正原生实现。
类似地，尽管 {anchorName all}`Nat` 的定义暗示了一个类似于 {anchorTerm all}`List Unit` 的实现，实际的运行时表示却会对足够小的数使用立即机器字，并对较大的数使用高效的任意精度算术库。
Lean 编译器会把使用模式匹配的定义翻译为适用于这种表示的相应操作，并把诸如加法和减法等操作调用映射到底层算术库中的快速操作。
毕竟，加法所需的时间不应与加数的大小成线性关系。

某些类型具有特殊表示这一事实也意味着，在使用它们时需要格外谨慎。
这些类型中的大多数由一个 {kw}`structure` 构成，而编译器会对它进行特殊处理。
对于这些结构，直接使用构造子或字段访问器可能会触发一次代价高昂的转换：从高效表示转换为便于证明但速度较慢的表示。
例如，{anchorName all}`String` 被定义为一个包含字符列表的结构，但字符串的运行时表示使用 UTF-8，而不是指向字符的指针所构成的链表。
将构造子应用于字符列表会创建一个按 UTF-8 编码这些字符的字节数组，而访问该结构的字段则需要花费与字符串长度成线性的时间来解码 UTF-8 表示并分配一个链表。
数组也以类似方式表示。
从逻辑角度看，数组是包含数组元素列表的结构，但运行时表示是动态大小的数组。
在运行时，构造子会把列表转换为数组，而字段访问器会根据数组分配一个链表。
各种数组操作会由编译器替换为高效版本；这些版本在可能时会改变数组，而不是分配新数组。

类型本身以及命题的证明都会从编译后的代码中完全擦除。
换言之，它们不占用任何空间，并且任何可能作为证明的一部分而执行的计算也同样会被擦除。
这意味着，证明可以利用将字符串和数组作为归纳定义列表时所具有的便利接口，包括使用归纳法证明关于它们的性质，而不会在程序运行时强加缓慢的转换步骤。
对于这些内置类型，数据具有便利的逻辑表示，并不意味着程序一定很慢。

如果一个结构类型只有一个非类型、非证明字段，那么构造子本身在运行时会消失，并被它的唯一参数替代。
换言之，子类型的表示与其底层类型完全相同，而不是多一层间接访问。
类似地，{anchorName all}`Fin` 在内存中只是 {anchorName all}`Nat`，并且可以创建单字段结构来跟踪 {anchorName all}`Nat` 或 {anchorName all}`String` 的不同用途，而无需付出性能代价。
如果一个构造子没有非类型、非证明参数，那么该构造子也会消失，并在本来要使用指针的位置被一个常量值替代。
这意味着 {anchorName all}`true`、{anchorName all}`false` 和 {anchorName all}`none` 是常量值，而不是指向堆分配对象的指针。


下列类型具有特殊表示：

:::table +header
*
  * 类型
  * 逻辑表示
  * 运行时表示

*
  * {anchorName all}`Nat`
  * 一元表示，每个 {anchorTerm all}`Nat.succ` 有一个指针
  * 高效的任意精度整数

*
  * {anchorName all}`Int`
  * 一个和类型，带有表示正值或负值的构造子，每个构造子都包含一个 {anchorName all}`Nat`
  * 高效的任意精度整数

*
  * {anchorTerm all}`BitVec w`
  * 带有适当界限 $`2^w` 的 {anchorName all}`Fin`
  * 高效的任意精度整数

*
  * {anchorName all}`UInt8`, {anchorName all}`UInt16`, {anchorName all}`UInt32`, {anchorName all}`UInt64`, {anchorName all}`USize`
  * 宽度正确的位向量
  * 固定精度的机器整数

*
  * {anchorName all}`Int8`, {anchorName all}`Int16`, {anchorName all}`Int32`, {anchorName all}`Int64`, {anchorName all}`ISize`
  * 一个相同宽度的包装后的无符号整数
  * 定精度机器整数

*
  * {anchorName all}`Char`
  * 一个 {anchorName all}`UInt32`，并配有证明它是有效码点的证明
  * 普通字符

*
  * {anchorName all}`String`
  * 一个结构，其中在名为 {anchorTerm StringDetail}`data` 的字段中包含一个 {anchorTerm all}`List Char`
  * UTF-8 编码的字符串

*
  * {anchorTerm sequences}`Array α`
  * 一个结构，其中在名为 {anchorName sequences}`toList` 的字段中包含一个 {anchorTerm sequences}`List α`
  * 由指向 {anchorName sequences}`α` 值的指针组成的紧凑数组

*
  * {anchorTerm all}`Sort u`
  * 一个类型
  * 完全擦除

*
  * 命题的证明
  * 当该命题被视为一种证据类型时，由该命题所指示的任何数据
  * 完全擦除
:::


# 练习
%%%
tag := "runtime-special-types-exercise"
file := "Exercise"
%%%

{ref "positive-numbers"}[{anchorName Pos (module := Examples.Classes)}`Pos` 的定义]没有利用 Lean 将 {anchorName all}`Nat` 编译为高效类型这一点。
在运行时，它本质上是一个链表。
另一种做法是，如{ref "subtypes"}[关于子类型的开头小节]所述，可以定义一个子类型，使得 Lean 的快速 {anchorName all}`Nat` 类型能够在内部使用。
在运行时，证明将被擦除。
由于所得结构只有一个数据字段，它就表示为该字段，这意味着 {anchorName Pos (module := Examples.Classes)}`Pos` 的这种新表示与 {anchorName all}`Nat` 的表示相同。

在证明定理 {anchorTerm all}`∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0` 之后，为 {anchorName Pos (module := Examples.Classes)}`Pos` 的这个新表示定义 {anchorName all}`ToString` 和 {anchorName all}`Add` 的实例。然后，定义一个 {anchorName all}`Mul` 的实例，并在过程中证明任何必要的定理。
