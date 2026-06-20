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
%%%

理解数据在内存中的表示非常重要。通常，可以从数据类型的定义中理解它的表示。
每个构造子对应于内存中的一个对象，该对象有一个包含标记和引用计数的头。
构造子的参数分别由指向其他对象的指针表示。换句话说，{anchorName all}`List` 实际上是一个链表，
从 {kw}`structure` 中提取一个字段实际上只是跟随一个指针。

然而，这个规则有一些重要的例外。编译器对许多类型进行了特殊处理。
例如，类型 {anchorName all}`UInt32` 被定义为 {anchorTerm all}`Fin (2 ^ 32)`，但在运行时它会被替换为基于机器字的实际原生实现。
类似地，尽管 {anchorName all}`Nat` 的定义暗示了一个类似于 {anchorTerm all}`List Unit` 的实现，
但实际的运行时表示会对足够小的数字使用立即（immediate）机器字，
对较大的数字则使用高效的任意精度算术库。Lean 编译器会将使用模式匹配的定义转换为与其表示对应的适当操作，
并且对加法和减法等操作的调用会被映射到底层算术库中的快速操作。
毕竟，加法不应该花费与加数大小成线性的时间。

由于某些类型具有特殊表示，因此在使用它们时需要小心。
这些类型中的大多数由编译器特殊处理的 {kw}`structure` 组成。对于这些结构体，
直接使用构造子或字段访问器可能会触发从高效表示到方便证明的低效表示的昂贵转换。
例如，{anchorName all}`String` 被定义为包含字符列表的结构体，但字符串的运行时表示使用了 UTF-8，
而非指向字符的指针链表。将构造子应用于字符列表会创建一个以 UTF-8 编码它们的字节数组，
而访问结构体的字段需要线性时间来解码 UTF-8 的表示并分配一个链表。数组的表示方式类似。
从逻辑角度来看，数组是包含数组元素列表的结构体，但运行时表示则是一个动态大小的数组。
在运行时，构造子会将列表转换为数组，而字段访问器则会在数组中分配一个链表。
编译器用高效的版本替换了各种数组操作，这些版本在可能的情况下会改变数组，而非分配一个新的数组。

类型本身和命题的证明都会从编译后的代码中完全擦除。换句话说，它们不会占用任何空间，
证明过程中可能执行的任何计算也同样会被擦除，
这意味着证明可以利用字符串和数组作为归纳定义列表的简便接口，包括使用归纳法来证明它们，
而不会在程序运行时施加缓慢的转换步骤。对于这些内置类型，数据的简便逻辑表示并不意味着程序一定会很慢。

如果一个结构体类型只有一个非类型，非证明的字段，那么构造子自身会在运行时消失，
并被替换为其单个参数。换句话说，其子类型与其底层类型完全相同，不会带有额外的间接层。
同样，{anchorName all}`Fin` 在内存中只是 {anchorName all}`Nat`，并且可以创建单字段结构体来跟踪 {anchorName all}`Nat` 或 {anchorName all}`String` 的不同用法，
而无需支付性能损失。如果一个构造子没有非类型，非证明的参数，那么该构造子也会消失，
并被一个常量值替换，否则指针将用于该常量值。这意味着 {anchorName all}`true`、{anchorName all}`false` 和 {anchorName all}`none` 是常量值，
而非指向堆分配对象的指针。


以下类型拥有特殊的表示：

:::table +header
*
  * 类型
  * 逻辑表示
  * 运行时表示

*
  * {anchorName all}`Nat`
  * 一元表示，每个 {anchorTerm all}`Nat.succ` 包含一个指针
  * 高效的任意精度整数

*
  * {anchorName all}`Int`
  * 一个和类型，具有表示正值和负值的构造子，每个构造子都包含一个 {anchorName all}`Nat`
  * 高效的任意精度整数

*
  * {anchorTerm all}`BitVec w`
  * 一个具有适当界 $`2^w` 的 {anchorName all}`Fin`
  * 高效的任意精度整数

*
  * {anchorName all}`UInt8`, {anchorName all}`UInt16`, {anchorName all}`UInt32`, {anchorName all}`UInt64`, {anchorName all}`USize`
  * 正确宽度的位向量
  * 固定精度机器整数

*
  * {anchorName all}`Int8`, {anchorName all}`Int16`, {anchorName all}`Int32`, {anchorName all}`Int64`, {anchorName all}`ISize`
  * 同宽度无符号整数的包装
  * 固定精度机器整数

*
  * {anchorName all}`Char`
  * 一个 {anchorName all}`UInt32`，并配以它是有效码点的证明
  * 普通字符

*
  * {anchorName all}`String`
  * 一个结构体，在名为 {anchorTerm StringDetail}`data` 的字段中包含 {anchorTerm all}`List Char`
  * UTF-8 编码字符串

*
  * {anchorTerm sequences}`Array α`
  * 一个结构体，在名为 {anchorName sequences}`toList` 的字段中包含 {anchorTerm sequences}`List α`
  * 指向 {anchorName sequences}`α` 值的指针的紧凑数组

*
  * {anchorTerm all}`Sort u`
  * 一个类型
  * 完全擦除

*
  * 命题的证明
  * 将命题视为证据类型时，该命题所暗示的任意数据
  * 完全擦除
:::


# 练习
%%%
tag := "runtime-special-types-exercise"
%%%

{ref "positive-numbers"}[{anchorName Pos (module := Examples.Classes)}`Pos` 的定义] 并没有利用 Lean 会把 {anchorName all}`Nat` 编译成高效类型这一事实。
在运行时，它本质上仍然是一个链表。
另一种做法是像 {ref "subtypes"}[最开始介绍子类型的那一节] 那样定义一个子类型，从而在内部使用 Lean 高效的 {anchorName all}`Nat` 类型。
在运行时，证明会被擦除。
由于所得结构只有一个数据字段，它在运行时就直接表示为该字段本身，这意味着这种新的 {anchorName Pos (module := Examples.Classes)}`Pos` 表示与 {anchorName all}`Nat` 的表示完全相同。

在证明定理 {anchorTerm all}`∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0` 之后，请为这种新的 {anchorName Pos (module := Examples.Classes)}`Pos` 表示定义 {anchorName all}`ToString` 和 {anchorName all}`Add` 的实例。然后再定义一个 {anchorName all}`Mul` 实例，并在过程中证明任何必要的定理。
