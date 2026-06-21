import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Defs"

#doc (Manual) "单子构造工具包" =>
%%%
file := "A-Monad-Construction-Kit"
%%%

{anchorName m}`ReaderT` 远非唯一有用的单子转换器。
本节描述若干其他转换器。
每个单子转换器都由以下部分组成：
 1. 一个以单子作为参数的定义或数据类型 {anchorName general}`T`。
它应当具有类似 {anchorTerm general}`(Type u → Type v) → Type u → Type v` 的类型，不过它可以在单子之前接受额外的参数。
 2. 一个用于 {anchorTerm general}`T m` 的 {anchorName general}`Monad` 实例，它依赖于 {anchorTerm general}`Monad m` 的实例。这使得转换后的单子能够作为单子使用。
 3. 一个 {anchorName general}`MonadLift` 实例，它将类型为 {anchorTerm general}`m α` 的动作转换为类型为 {anchorTerm general}`T m α` 的动作，其中 {anchorName general}`m` 是任意单子。这使得来自底层单子的动作可以在经过转换的单子中使用。

此外，转换器的 {anchorName general}`Monad` 实例应当遵守 {anchorName general}`Monad` 的约定，至少在底层 {anchorName general}`Monad` 实例遵守该约定时如此。
另外，在变换后的单子中，{anchorTerm general}`monadLift (pure x : m α)` 应当等价于 {anchorTerm general}`pure x`，并且 {anchorName general}`monadLift` 应当在 {anchorName MonadStateT}`bind` 上分配，使得 {anchorTerm general}`monadLift (x >>= f : m α)` 与 {anchorTerm general}`(monadLift x : m α) >>= fun y => monadLift (f y)` 相同。

许多单子转换器还会以 {anchorName m}`MonadReader` 的风格定义类型类，用来描述单子中实际可用的效果。
这可以提供更大的灵活性：它允许编写仅依赖于某个接口的程序，而不把底层单子约束为必须由某个给定的转换器实现。
类型类是程序表达其需求的一种方式，而单子转换器则是满足这些需求的一种便利方式。


# 使用 {lit}`OptionT` 表示失败
%%%
tag := "OptionT"
file := "Failure-with-OptionT"
%%%

由 {anchorName OptionExcept}`Option` 单子表示的失败，以及由 {anchorName M1eval}`Except` 单子表示的异常，都有相应的转换器。
在 {anchorName OptionTdef}`Option` 的情形中，可以通过让一个单子在原本包含 {anchorName OptionTdef}`α` 类型的值之处包含 {anchorTerm OptionTdef}`Option α` 类型的值，来向该单子添加失败。
例如，{anchorTerm m}`IO (Option α)` 表示并不总是返回 {anchorName m}`α` 类型值的 {anchorName m}`IO` 动作。
这提示了单子转换器 {anchorName OptionTdef}`OptionT` 的定义：

```anchor OptionTdef
def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)
```

作为 {anchorName OptionTdef}`OptionT` 实际使用的一个例子，考虑一个向用户提问的程序。
函数 {anchorName getSomeInput}`getSomeInput` 请求一行输入，并移除其两端的空白字符。
如果所得的修剪后输入非空，则返回它；但如果不存在非空白字符，则该函数失败：

```anchor getSomeInput
def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed
```
这个特定应用程序用用户的姓名和他们最喜欢的甲虫种类来跟踪用户：

```anchor UserInfo
structure UserInfo where
  name : String
  favoriteBeetle : String
```
向用户请求输入并不比只使用 {anchorName m}`IO` 的函数更加冗长：

```anchor getUserInfo
def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩
```
然而，由于该函数运行在 {anchorTerm getSomeInput}`OptionT IO` 上下文中，而不只是运行在 {anchorName m}`IO` 中，因此第一次调用 {anchorName getSomeInput}`getSomeInput` 时的失败会导致整个 {anchorName getUserInfo}`getUserInfo` 失败，控制流永远不会到达关于甲虫的问题。
主函数 {anchorName interact}`interact` 在纯 {anchorName m}`IO` 上下文中调用 {anchorName interact}`getUserInfo`，这使它能够通过对内部的 {anchorName m}`Option` 进行匹配来检查该调用是成功还是失败：

```anchor interact
def interact : IO Unit := do
  match ← getUserInfo with
  | none =>
    IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {beetle}."
```

## 单子实例
%%%
tag := "OptionT-monad-instance"
file := "The-Monad-Instance"
%%%

编写单子实例会揭示一个困难。
根据类型，{anchorName MonadExceptT}`pure` 应当使用来自底层单子 {anchorName firstMonadOptionT}`m` 的 {anchorName MonadMissingUni}`pure`，并结合 {anchorName firstMonadOptionT}`some`。
正如 {anchorName m}`Option` 的 {anchorName firstMonadOptionT}`bind` 会对第一个参数进行分支，并传播 {anchorName firstMonadOptionT}`none` 一样，{anchorName firstMonadOptionT}`OptionT` 的 {anchorName firstMonadOptionT}`bind` 应当运行构成第一个参数的单子式动作，对结果进行分支，然后传播 {anchorName firstMonadOptionT}`none`。
按照这一草图会得到以下定义，但 Lean 不接受它：
```anchor firstMonadOptionT
instance [Monad m] : Monad (OptionT m) where
  pure x := pure (some x)
  bind action next := do
    match (← action) with
    | none => pure none
    | some v => next v
```
错误消息显示了一个晦涩的类型不匹配：
```anchorError firstMonadOptionT
Application type mismatch: The argument
  some x
has type
  Option α✝
but is expected to have type
  α✝
in the application
  pure (some x)
```
这里的问题在于，Lean 为周围对 {anchorName firstMonadOptionT}`pure` 的使用选择了错误的 {anchorName firstMonadOptionT}`Monad` 实例。
在 {anchorName firstMonadOptionT}`bind` 的定义中也会出现类似错误。
一种解决方法是使用类型标注来引导 Lean 选择正确的 {anchorName MonadOptionTAnnots}`Monad` 实例：

```anchor MonadOptionTAnnots
instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none
    | some v => next v : m (Option _))
```
虽然这个解决方案可行，但它并不优雅，而且代码会变得有些嘈杂。

另一种解决方案是定义一些函数，使其类型签名引导 Lean 找到正确的实例。
事实上，{anchorName OptionTStructure}`OptionT` 本可以被定义为一个结构：

```anchor OptionTStructure
structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)
```
这将解决该问题，因为构造子 {anchorName OptionTStructuredefs}`OptionT.mk` 和字段访问器 {anchorName OptionTStructuredefs}`OptionT.run` 会引导类型类推断找到正确的实例。
这样做的缺点是，所得代码更复杂，并且这些结构可能使证明更难阅读。
可以通过定义一些函数来兼得二者之长：这些函数扮演与构造子 {anchorName OptionTStructuredefs}`OptionT.mk` 和字段 {anchorName OptionTStructuredefs}`OptionT.run` 相同的角色，但适用于直接定义：

```anchor FakeStructOptionT
def OptionT.mk (x : m (Option α)) : OptionT m α := x

def OptionT.run (x : OptionT m α) : m (Option α) := x
```
这两个函数都原封不动地返回其输入，但它们标示了意在呈现 {anchorName FakeStructOptionT}`OptionT` 接口的代码与意在呈现底层单子 {anchorName FakeStructOptionT}`m` 接口的代码之间的边界。
使用这些辅助函数，{anchorName MonadOptionTFakeStruct}`Monad` 实例变得更易读：

```anchor MonadOptionTFakeStruct
instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do
    match ← action with
    | none => pure none
    | some v => next v
```
这里，使用 {anchorName FakeStructOptionT}`OptionT.mk` 表明其参数应被视为使用 {anchorName MonadOptionTFakeStruct}`m` 接口的代码，这使 Lean 能够选择正确的 {anchorName MonadOptionTFakeStruct}`Monad` 实例。

定义单子实例之后，最好检查单子契约是否得到满足。
第一步是表明 {anchorTerm OptionTFirstLaw}`bind (pure v) f` 与 {anchorTerm OptionTFirstLaw}`f v` 相同。
步骤如下：

```anchorEqSteps OptionTFirstLaw
bind (pure v) f
={ /-- Unfolding the definitions of `bind` and `pure` -/
   by simp [bind, pure, OptionT.mk]
}=
OptionT.mk do
  match ← pure (some v) with
  | none => pure none
  | some x => f x
={
/-- Desugaring nested action syntax -/
}=
OptionT.mk do
  let y ← pure (some v)
  match y with
  | none => pure none
  | some x => f x
={
/-- Desugaring `do`-notation -/
}=
OptionT.mk
  (pure (some v) >>= fun y =>
    match y with
    | none => pure none
    | some x => f x)
={
  /-- Using the first monad rule for `m` -/
  by simp [LawfulMonad.pure_bind (m := m)]
}=
OptionT.mk
  (match some v with
   | none => pure none
   | some x => f x)
={
/-- Reduce `match` -/
}=
OptionT.mk (f v)
={
/-- Definition of `OptionT.mk` -/
}=
f v
```

第二条规则说明 {anchorTerm OptionTSecondLaw}`bind w pure` 与 {anchorName OptionTSecondLaw}`w` 相同。
为了展示这一点，展开 {anchorName OptionTSecondLaw}`bind` 和 {anchorName OptionTSecondLaw}`pure` 的定义，得到：
```anchorTerm OptionTSecondLaw
OptionT.mk do
    match ← w with
    | none => pure none
    | some v => pure (some v)
```
在这个模式匹配中，两个分支的结果都与被匹配的模式相同，只是在其外面包了一层 {anchorName OptionTSecondLaw}`pure`。
换言之，它等价于 {anchorTerm OptionTSecondLaw}`w >>= fun y => pure y`，而这是 {anchorName OptionTFirstLaw}`m` 的第二条单子规则的一个实例。

最后一条规则说明 {anchorTerm OptionTThirdLaw}`bind (bind v f) g` 与 {anchorTerm OptionTThirdLaw}`bind v (fun x => bind (f x) g)` 相同。
可以用同样的方式检查这一点：展开 {anchorName OptionTThirdLaw}`bind` 和 {anchorName OptionTSecondLaw}`pure` 的定义，然后委托给底层单子 {anchorName OptionTFirstLaw}`m`。

## 一个 {lit}`Alternative` 实例
%%%
tag := "OptionT-Alternative-instance"
file := "An-Alternative-Instance"
%%%

使用 {anchorName OptionTdef}`OptionT` 的一种便捷方式是通过 {anchorName AlternativeOptionT}`Alternative` 类型类。
成功返回已经由 {anchorName AlternativeOptionT}`pure` 表示，而 {anchorName AlternativeOptionT}`Alternative` 的 {anchorName AlternativeOptionT}`failure` 和 {anchorName AlternativeOptionT}`orElse` 方法提供了一种方式，用于编写从若干子程序中返回第一个成功结果的程序：

```anchor AlternativeOptionT
instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x y := OptionT.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()
```


## 提升
%%%
tag := "OptionT-lifting"
file := "Lifting"
%%%

将一个动作从 {anchorName LiftOptionT}`m` 提升到 {anchorTerm LiftOptionT}`OptionT m`，只需要把 {anchorName LiftOptionT}`some` 包裹在该计算的结果外面：

```anchor LiftOptionT
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))
```


# 异常
%%%
tag := "exceptions"
file := "Exceptions"
%%%

{anchorName ExceptT}`Except` 的单子转换器版本与 {anchorName m}`Option` 的单子转换器版本非常相似。
向某个类型为 {anchorTerm ExceptT}`m`{lit}` `{anchorTerm ExceptT}`α` 的单子动作添加类型为 {anchorName ExceptT}`ε` 的异常，可以通过向 {anchorName MonadExcept}`α` 添加异常来完成，从而得到类型 {anchorTerm ExceptT}`m (Except ε α)`：

```anchor ExceptT
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)
```
{anchorName OptionTdef}`OptionT` 提供 {anchorName FakeStructOptionT}`OptionT.mk` 和 {anchorName FakeStructOptionT}`OptionT.run` 函数，用以引导类型检查器找到正确的 {anchorName MonadOptionTFakeStruct}`Monad` 实例。
这个技巧对 {anchorName ExceptTFakeStruct}`ExceptT` 也很有用：

```anchor ExceptTFakeStruct
  def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

  def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x
```
{anchorName MonadExceptT}`ExceptT` 的 {anchorName MonadExceptT}`Monad` 实例也与 {anchorName MonadOptionTFakeStruct}`OptionT` 的实例非常相似。
唯一的区别在于，它传播一个特定的错误值，而不是 {anchorName MonadOptionTFakeStruct}`none`：

```anchor MonadExceptT
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x
```

{anchorName ExceptTFakeStruct}`ExceptT.mk` 和 {anchorName ExceptTFakeStruct}`ExceptT.run` 的类型签名包含一个细微之处：它们显式标注了 {anchorName ExceptTFakeStruct}`α` 和 {anchorName ExceptTFakeStruct}`ε` 的宇宙层级。
如果不显式标注它们，那么 Lean 会生成一个更一般的类型签名，其中它们具有不同的多态宇宙变量。
然而，{anchorName ExceptTFakeStruct}`ExceptT` 的定义期望它们位于同一宇宙中，因为它们二者都可以作为参数提供给 {anchorName ExceptTFakeStruct}`m`。
这可能会在 {anchorName MonadStateT}`Monad` 实例中导致一个问题：宇宙层级求解器无法找到可行的解：

```anchor ExceptTNoUnis
def ExceptT.mk (x : m (Except ε α)) : ExceptT ε m α := x
```
```anchor MonadMissingUni
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match (← result) with
    | .error e => pure (.error e)
    | .ok x => next x
```
```anchorError MonadMissingUni
stuck at solving universe constraint
  max ?u.10439 ?u.10440 =?= u
while trying to unify
  ExceptT ε m β✝ : Type v
with
  ExceptT.{max ?u.10440 ?u.10439, v} ε m β✝ : Type v
```
这类错误消息通常是由约束不足的宇宙变量引起的。
诊断它可能比较棘手，但一个好的第一步是查找某些定义中被复用、而在另一些定义中未被复用的宇宙变量。

不同于 {anchorName m}`Option`，{anchorName m}`Except` 数据类型通常不被用作数据结构。
它总是与其 {anchorName MonadExceptT}`Monad` 实例一起用作控制结构。
这意味着，将 {anchorTerm ExceptTLiftExcept}`Except ε` 动作以及来自底层单子 {anchorName ExceptTLiftExcept}`m` 的动作提升到 {anchorTerm ExceptTLiftExcept}`ExceptT ε m` 中是合理的。
将 {anchorName ExceptTLiftExcept}`Except` 动作提升为 {anchorName ExceptTLiftExcept}`ExceptT` 动作，是通过用 {anchorName ExceptTLiftExcept}`m` 的 {anchorName ExceptTLiftExcept}`pure` 将它们包装起来完成的，因为一个仅具有异常效果的动作不可能具有来自单子 {anchorName ExceptTLiftExcept}`m` 的任何效果：

```anchor ExceptTLiftExcept
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)
```
因为来自 {anchorName ExceptTLiftExcept}`m` 的动作本身不含任何异常，所以它们的值应当包装在 {anchorName MonadExceptT}`Except.ok` 中。
这可以利用 {anchorName various}`Functor` 是 {anchorName various}`Monad` 的超类这一事实来完成，因此可以使用 {anchorName various}`Functor.map` 将函数应用于任意单子计算的结果：

```anchor ExceptTLiftM
instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)
```

## 用于异常的类型类
%%%
tag := "exceptions-type-classes"
file := "Type-Classes-for-Exceptions"
%%%

异常处理从根本上由两种操作组成：抛出异常的能力，以及从异常中恢复的能力。
到目前为止，这分别是通过 {anchorName m}`Except` 的构造子和模式匹配来实现的。
然而，这会将使用异常的程序绑定到异常处理效应的一种特定编码。
使用类型类来刻画这些操作，使得使用异常的程序能够用于_任何_支持抛出和捕获的单子。

抛出异常应当以一个异常作为参数，并且在任何需要单子动作的上下文中都应当允许这样做。
规范中“任何上下文”的部分可以通过写作 {anchorTerm MonadExcept}`m α` 表示为一个类型——因为无法产生任意类型的值，所以 {anchorName MonadExcept}`throw` 操作必定在做某种使控制流离开程序该部分的事情。
捕获异常应当接受任意单子动作以及一个处理器，而该处理器应当说明如何从一个异常回到该动作的类型：

```anchor MonadExcept
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α
```

{anchorName MonadExcept}`MonadExcept` 上的宇宙层级不同于 {anchorName ExceptT}`ExceptT` 的宇宙层级。
在 {anchorName ExceptT}`ExceptT` 中，{anchorName ExceptT}`ε` 和 {anchorName ExceptT}`α` 具有相同的层级，而 {anchorName MonadExcept}`MonadExcept` 不施加这样的限制。
这是因为 {anchorName MonadExcept}`MonadExcept` 从不把异常值放入 {anchorName MonadExcept}`m` 中。
最一般的宇宙签名承认这样一个事实：在这个定义中，{anchorName MonadExcept}`ε` 和 {anchorName MonadExcept}`α` 是完全独立的。
更加一般意味着该类型类可以为更广泛的类型实例化。

使用 {anchorName MonadExcept}`MonadExcept` 的一个示例程序是一个简单的除法服务。
该程序分为两部分：一个前端，提供基于字符串的用户界面并处理错误；以及一个后端，实际执行除法。
前端和后端都可以抛出异常，前者用于处理格式不正确的输入，后者用于处理除以零的错误。
这些异常是一个归纳类型：

```anchor ErrEx
inductive Err where
  | divByZero
  | notANumber : String → Err
```
后端检查是否为零，并在可以时执行除法：

```anchor divBackend
def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)
```
前端的辅助函数 {anchorName asNumber}`asNumber` 在传入的字符串不是数字时抛出异常。
整个前端将其输入转换为 {anchorName asNumber}`Int`，并调用后端；它通过返回一个友好的字符串错误来处理异常：

```anchor asNumber
def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i
```

```anchor divFrontend
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""
```
抛出和捕获异常十分常见，因此 Lean 为使用 {anchorName divFrontendSugary}`MonadExcept` 提供了一种特殊语法。
正如 {lit}`+` 是 {anchorName various}`HAdd.hAdd` 的简写一样，{kw}`try` 和 {kw}`catch` 可以用作 {anchorName MonadExcept}`tryCatch` 方法的简写：

```anchor divFrontendSugary
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""
```

除了 {anchorName m}`Except` 和 {anchorName ExceptT}`ExceptT` 之外，对于其他乍看之下可能不像异常的类型，也存在有用的 {anchorName MonadExcept}`MonadExcept` 实例。
例如，由 {anchorName m}`Option` 导致的失败可以看作抛出一个完全不含任何数据的异常，因此存在一个 {anchorTerm OptionExcept}`MonadExcept Unit Option` 实例，允许将 {kw}`try`{lit}` ...`{kw}`catch`{lit}` ...` 语法与 {anchorName m}`Option` 一起使用。

# 状态
%%%
tag := "state-monad"
file := "State"
%%%

通过使单子动作接受一个初始状态作为参数，并将最终状态与其结果一同返回，可以向单子添加对可变状态的模拟。
状态单子的 bind 运算符将一个动作的最终状态作为参数提供给下一个动作，从而使状态贯穿整个程序。
这一模式也可以表示为单子转换器：

```anchor DefStateT
def StateT (σ : Type u)
    (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
```


同样，单子实例与 {anchorName State (module := Examples.Monads)}`State` 的单子实例非常相似。
唯一的区别在于，输入状态和输出状态是在底层单子中传递并返回的，而不是通过纯代码来处理：

```anchor MonadStateT
instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'
```

相应的类型类具有 {anchorName MonadState}`get` 和 {anchorName MonadState}`set` 方法。
{anchorName MonadState}`get` 和 {anchorName MonadState}`set` 的一个缺点是，在更新状态时很容易 {anchorName MonadState}`set` 错误的状态。
这是因为，获取状态、更新状态、再保存更新后的状态，是编写某些程序的一种自然方式。
例如，以下程序统计一个字母字符串中不带变音符号的英语元音和辅音的数量：

```anchor countLetters
structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList
```
很容易把 {anchorTerm countLetters}`set st'` 写成 {lit}`set st`。
在大型程序中，这类错误可能导致难以诊断的 bug。

虽然在调用 {anchorName countLetters}`get` 时使用嵌套动作可以解决这个问题，但它不能解决所有这类问题。
例如，一个函数可能会基于某个结构中另外两个字段的值来更新其中一个字段。
这将需要对 {anchorName countLetters}`get` 进行两次独立的嵌套动作调用。
由于 Lean 编译器包含一些只有在某个值仅有一个引用时才有效的优化，复制对状态的引用可能会导致代码显著变慢。
通过使用 {anchorName countLettersModify}`modify` 可以同时规避潜在的性能问题和潜在的错误；{anchorName countLettersModify}`modify` 使用一个函数来转换状态：

```anchor countLettersModify
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
该类型类包含一个名为 {anchorName modify}`modifyGet`、类似于 {anchorName modify}`modify` 的函数，它允许函数在单一步骤中同时计算返回值并变换旧状态。
该函数返回一个对，其中第一个元素是返回值，第二个元素是新状态；{anchorName modify}`modify` 只是把 {anchorName modify}`Unit` 的构造子添加到 {anchorName modify}`modifyGet` 中所用的对上：

```anchor modify
def modify [MonadState σ m] (f : σ → σ) : m Unit :=
  modifyGet fun s => ((), f s)
```

{anchorName MonadState}`MonadState` 的定义如下：

```anchor MonadState
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u+1) v) where
  get : m σ
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α
```
{anchorName MonadState}`PUnit` 是 {anchorName modify}`Unit` 类型的一个版本，它具有宇宙多态性，从而允许它位于 {anchorTerm MonadState}`Type u` 中而不是 {anchorTerm MonadState}`Type` 中。
虽然可以依据 {anchorName MonadState}`get` 和 {anchorName MonadState}`set` 为 {anchorName MonadState}`modifyGet` 提供默认实现，但这样不会容许那些使 {anchorName MonadState}`modifyGet` 一开始就有用的优化，从而会使该方法失去作用。

# {lit}`Of` 类与 {lit}`The` 函数
%%%
tag := "of-and-the"
file := "Of-Classes-and-The-Functions"
%%%

到目前为止，每个接受额外信息的单子类型类，例如 {anchorName MonadExcept}`MonadExcept` 的异常类型或 {anchorName MonadState}`MonadState` 的状态类型，都将这类额外信息作为输出参数。
对于简单程序，这通常很方便，因为一个分别结合一次 {anchorName MonadStateT}`StateT`、{anchorName m}`ReaderT` 和 {anchorName ExceptT}`ExceptT` 用法的单子，只有一个状态类型、环境类型和异常类型。
然而，随着单子的复杂性增长，它们可能涉及多个状态类型或错误类型。
在这种情况下，使用输出参数会使得在同一个 {kw}`do` 块中同时以两个状态为目标成为不可能。

对于这些情形，存在一些附加的类型类，其中额外信息不是输出参数。
这些类型类的版本在名称中使用词 {lit}`Of`。
例如，{anchorName getTheType}`MonadStateOf` 类似于 {anchorName MonadState}`MonadState`，但没有 {anchorName MonadState}`outParam` 修饰符。

这些类并不使用 {anchorName MonadState}`outParam`，而是为各自的状态、环境或异常类型使用 {anchorName various}`semiOutParam`。
类似于 {anchorName MonadState}`outParam`，在 Lean 开始搜索实例之前，并不要求 {anchorName various}`semiOutParam` 已知。
然而，有一个重要区别：在搜索实例时会忽略 {anchorName MonadState}`outParam`，因此它们是真正的输出。
如果在搜索之前已知某个 {anchorName MonadState}`outParam`，那么 Lean 只会检查搜索结果是否与已知内容相同。
另一方面，在搜索开始之前已知的 {anchorName various}`semiOutParam` 可以用于缩小候选范围，就像输入参数一样。

当状态单子的状态类型是一个 {anchorName MonadState}`outParam` 时，每个单子至多只能有一种状态类型。
这是方便的，因为它改善了类型推断：状态类型可以在更多情形下被推断出来。
这也是不方便的，因为由多次使用 {anchorName countLetters}`StateT` 构造出的单子无法提供有用的 {anchorName modify}`MonadState` 实例。
然而，使用 {anchorName modifyTheType}`MonadStateOf` 会使 Lean 在可用时将状态类型纳入考虑，以选择要使用的实例，因此一个单子可以提供多种状态类型。
其缺点是，当状态类型没有被足够明确地指定时，所得实例可能不是原本期望的那个，这可能导致令人困惑的错误消息。

类似地，也存在一些类型类方法的版本，它们将附加信息的类型作为_显式_参数而不是隐式参数来接受。
对于 {anchorName modifyTheType}`MonadStateOf`，有类型为如下形式的 {anchorTerm getTheType}`getThe`
```anchorTerm getTheType
(σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ
```
以及类型为如下形式的 {anchorTerm modifyTheType}`modifyThe`
```anchorTerm modifyTheType
(σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → (σ → σ) → m PUnit
```
这里没有 {lit}`setThe`，因为新状态的类型足以决定使用哪个外围状态单子转换器。

在 Lean 标准库中，存在这些类的非 {lit}`Of` 版本的实例，它们是根据带有 {lit}`Of` 的版本的实例定义的。
换言之，实现 {lit}`Of` 版本会同时得到二者的实现。
通常较好的做法是实现 {lit}`Of` 版本，然后开始使用该类的非 {lit}`Of` 版本来编写程序；如果输出参数变得不便，再过渡到 {lit}`Of` 版本。

# 转换器与 {lit}`Id`
%%%
tag := "transformers-and-Id"
file := "Transformers-and-Id"
%%%

恒等单子 {anchorName various}`Id` 是一个完全没有任何效果的单子，用于那些由于某种原因期望一个单子、但实际上并不需要任何效果的语境中。
{anchorName various}`Id` 的另一种用途是作为单子转换器栈的底部。
例如，{anchorTerm StateTDoubleB}`StateT σ Id` 的工作方式就和 {anchorTerm set (module:=Examples.Monads)}`State σ` 一样。


# 练习
%%%
tag := "monad-transformer-exercises"
file := "Exercises"
%%%

## 单子契约
%%%
tag := none
file := "Monad-Contract"
%%%

用纸笔检查本节中每个单子转换器都满足单子转换器约定的规则。

## 日志记录转换器
%%%
tag := none
file := "Logging-Transformer"
%%%

定义 {anchorName WithLog (module:=Examples.Monads)}`WithLog` 的单子转换器版本。
同时定义相应的类型类 {lit}`MonadWithLog`，并编写一个结合日志记录和异常的程序。

## 文件计数
%%%
tag := none
file := "Counting-Files"
%%%

用 {anchorName MonadStateT}`StateT` 修改 {lit}`doug` 的单子，使其统计所见目录和文件的数量。
执行结束时，它应显示类似如下的报告：
```
  Viewed 38 files in 5 directories.
```
