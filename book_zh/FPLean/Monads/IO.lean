import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.IO"

#doc (Manual) "IO 单子" =>
%%%
tag := "io-monad"
%%%

{anchorName names}`IO` 作为单子可以从两个角度理解，这在 {ref "running-a-program"}[运行程序] 一节中进行了描述。
每个角度都可以帮助理解 {anchorName names}`IO` 的 {anchorName names}`pure` 和 {anchorName names}`bind` 的含义。

从第一个视角看，{anchorName names}`IO` 活动是 Lean 运行时系统的指令。
例如，指令可能是 “从该文件描述符读取字符串，然后使用该字符串重新调用纯 Lean 代码”。
这是一种 *外部* 的视角，即从操作系统的视角看待程序。
在这种情况下，{anchorName names}`pure` 是一个不请求 RTS 产生任何作用的 {anchorName names}`IO` 活动，
而 {anchorName names}`bind` 指示 RTS 首先执行一个产生潜在作用的操作，然后使用结果值调用程序的其余部分。

从第二个视角看，{anchorName names}`IO` 活动会变换整个世界。{anchorName names}`IO` 活动实际上是纯（Pure）的，
因为它接受一个唯一的世界作为参数，然后返回改变后的世界。
这是一种 *内部* 的视角，它对应了 {anchorName names}`IO` 在 Lean 中的表示方式。
世界在 Lean 中表示为一个标记，而 {anchorName names}`IO` 单子的结构化可以确保标记刚好使用一次。

为了了解其工作原理，逐层解析它的定义会很有帮助。
{kw}`#print` 命令揭示了 Lean 数据类型和定义的内部结构。例如：
```anchor printNat
#print Nat
```
的结果为
```anchorInfo printNat
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
```
而
```anchor printCharIsAlpha
#print Char.isAlpha
```
的结果为
```anchorInfo printCharIsAlpha
def Char.isAlpha : Char → Bool :=
fun c => c.isUpper || c.isLower
```

有时，{kw}`#print` 的输出包含了本书中尚未展示的 Lean 特性。例如：
```anchor printListIsEmpty
#print List.isEmpty
```
会产生
```anchorInfo printListIsEmpty
def List.isEmpty.{u} : {α : Type u} → List α → Bool :=
fun {α} x =>
  match x with
  | [] => true
  | head :: tail => false
```
它在定义名的后面包含了一个 {lit}`.{u}`，并将类型标注为 {anchorTerm names}`Type u` 而非只是 {anchorTerm names}`Type`。
目前可以安全地忽略它。

打印 {anchorName names}`IO` 的定义表明它是根据更简单的结构定义的：
```anchor printIO
#print IO
```
```anchorInfo printIO
@[reducible] def IO : Type → Type :=
EIO IO.Error
```
{anchorName printIOError}`IO.Error` 表示 {anchorName names}`IO` 活动可能抛出的所有错误：
```anchor printIOError
#print IO.Error
```
```anchorInfo printIOError
inductive IO.Error : Type
number of parameters: 0
constructors:
IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
IO.Error.otherError : UInt32 → String → IO.Error
IO.Error.resourceBusy : UInt32 → String → IO.Error
IO.Error.resourceVanished : UInt32 → String → IO.Error
IO.Error.unsupportedOperation : UInt32 → String → IO.Error
IO.Error.hardwareFault : UInt32 → String → IO.Error
IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
IO.Error.illegalOperation : UInt32 → String → IO.Error
IO.Error.protocolError : UInt32 → String → IO.Error
IO.Error.timeExpired : UInt32 → String → IO.Error
IO.Error.interrupted : String → UInt32 → String → IO.Error
IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
IO.Error.unexpectedEof : IO.Error
IO.Error.userError : String → IO.Error
```
{anchorTerm names}`EIO ε α` 表示一个 {anchorName names}`IO` 活动，它将以类型为 {anchorTerm names}`ε` 的错误表示终止，或者以类型为 {anchorTerm names}`α` 的值表示成功。
这意味着，与 {anchorTerm names}`Except ε` 单子一样，{anchorName names}`IO` 单子也包括定义错误处理和异常的能力。

剥离另一层，{anchorName names}`EIO` 本身又是根据更简单的结构定义的：
```anchor printEIO
#print EIO
```
```anchorInfo printEIO
def EIO : Type → Type → Type :=
fun ε α => EST ε IO.RealWorld α
```
{anchorName printEStateM}`EST` 单子同时包含错误和状态，它类似于 {anchorName names}`Except` 与 {anchorName State (module := Examples.Monads)}`State` 的组合。
它使用另一个类型 {anchorName printEStateMResult}`EST.Out` 定义：
```anchor printEStateM
#print EST
```
```anchorInfo printEStateM
def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α
```
换言之，类型为 {anchorTerm EStateMNames}`EST ε σ α` 的程序是一个函数，它接受类型为 {anchorName EStateMNames}`σ` 的初始状态，并返回一个 {anchorTerm EStateMNames}`EST.Out ε σ α`。
状态被包装在类型 {anchorName VoidSigma}`Void` 中；这是一个内部原语，会使值从编译后的代码中擦除。{anchorTerm VoidSigma}`Void σ` 与 {anchorName save (module:=Examples.Monads)}`Unit` 具有相同表示。

{anchorName EStateMNames}`EST.Out` 与 {anchorName names}`Except` 的定义非常相似，其中一个构造子表示成功终止，另一个构造子表示错误：
```anchor printEStateMResult
#print EST.Out
```
```anchorInfo printEStateMResult
inductive EST.Out : Type → Type → Type → Type
number of parameters: 3
constructors:
EST.Out.ok : {ε σ α : Type} → α → Void σ → EST.Out ε σ α
EST.Out.error : {ε σ α : Type} → ε → Void σ → EST.Out ε σ α
```
正如 {anchorTerm Except (module:=Examples.Monads)}`Except ε α` 一样，{anchorName names (show := ok)}`EST.Out.ok` 构造子包含一个类型为 {anchorName Except (module:=Examples.Monads)}`α` 的结果，而 {anchorName names (show := error)}`EST.Out.error` 构造子包含一个类型为 {anchorName Except (module:=Examples.Monads)}`ε` 的异常。
与 {anchorName names}`Except` 不同，这两个构造子都有一个额外的状态字段，其中包含计算的最终状态。

{anchorTerm names}`EST ε σ` 的 {anchorName names}`Monad` 实例需要 {anchorName names}`pure` 和 {anchorName names}`bind`。
与 {anchorName State (module:=Examples.Monads)}`State` 一样，{anchorName names}`EST` 的 {anchorName names}`pure` 实现接受一个初始状态并原样返回它；与 {anchorName names}`Except` 一样，它把自己的参数放在 {anchorName names (show := ok)}`EST.Out.ok` 构造子中返回：
```anchor printEStateMpure
#print EST.pure
```
```anchorInfo printEStateMpure
protected def EST.pure : {α ε σ : Type} → α → EST ε σ α :=
fun {α ε σ} a s => EST.Out.ok a s
```
{kw}`protected` 的意思是，即使已经打开 {anchorName names}`EST` 命名空间，也仍然需要使用完整名称 {anchorName printEStateMpure}`EST.pure`。

类似地，{anchorName names}`EST` 的 {anchorName names}`bind` 也以初始状态作为参数。
它把这个初始状态传给第一个动作。
然后，它像 {anchorName names}`Except` 的 {anchorName names}`bind` 一样，检查结果是否为错误。
如果是错误，则原样返回该错误，且 {anchorName names}`bind` 的第二个参数不会被使用。
如果结果成功，那么第二个参数会同时应用于返回值和所得状态。
```anchor printEStateMbind
#print EST.bind
```
```anchorInfo printEStateMbind
protected def EST.bind : {ε σ α β : Type} → EST ε σ α → (α → EST ε σ β) → EST ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EST.Out.ok a s => f a s
  | EST.Out.error e s => EST.Out.error e s
```

把这些放在一起看，{anchorName names}`IO` 是一个同时跟踪状态和错误的单子。
可用错误的集合由数据类型 {anchorName printIOError}`IO.Error` 给出，它具有许多构造子，用来描述程序中可能出错的多种情况。
状态是一个表示真实世界的类型，称为 {anchorTerm RealWorld}`IO.RealWorld`。
每个基本 {anchorName names}`IO` 动作都接收这个真实世界，并返回另一个真实世界，同时配以错误或结果。
在 {anchorName names}`IO` 中，{anchorName names}`pure` 原样返回世界，而 {anchorName names}`bind` 把一个动作修改后的世界传给下一个动作。

由于整个宇宙无法放进计算机内存，被传递的世界只是一个表示。
只要世界令牌不被重复使用，这种表示就是安全的。
类型 {anchorTerm RealWorld}`IO.RealWorld` 是一个平凡的原始类型，完全不需要任何表示，因为它只在 {anchorName VoidSigma}`Void` 内部使用。
