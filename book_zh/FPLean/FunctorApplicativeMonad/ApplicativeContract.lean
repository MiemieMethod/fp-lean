import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "应用函子约定" =>
%%%
tag := "applicative-laws"
file := "The-Applicative-Contract"
%%%

就像 {anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Monad`，以及实现 {anchorName SizedCreature}`BEq` 和 {anchorName MonstrousAssistantMore}`Hashable` 的类型一样，{anchorName ApplicativeLaws}`Applicative` 也有一组所有实例都应遵守的规则。

应用函子应当遵循四条规则：
1. 它应当遵守恒等律，即 {anchorTerm ApplicativeLaws}`pure id <*> v = v`
2. 它应当遵守函数复合，因此 {anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
3. 对纯操作进行定序应当是无操作，因此 {anchorTerm ApplicativeLaws}`pure f <*> pure x`{lit}` = `{anchorTerm ApplicativeLaws}`pure (f x)`
4. 纯操作的顺序无关紧要，因此 {anchorTerm ApplicativeLaws}`u <*> pure x = pure (fun f => f x) <*> u`

要检查 {anchorTerm ApplicativeOption}`Applicative Option` 实例的这些规则，首先将 {anchorName ApplicativeLaws}`pure` 展开为 {anchorName ApplicativeOption}`some`。

第一条规则说明 {anchorTerm ApplicativeOptionLaws1}`some id <*> v = v`。
{anchorName ApplicativeOption}`Option` 的 {anchorName fakeSeq}`seq` 定义说明这等同于 {anchorTerm ApplicativeOptionLaws1}`id <$> v = v`，而这是已经检查过的 {anchorName ApplicativeLaws}`Functor` 规则之一。

第二条规则表明 {anchorTerm ApplicativeOptionLaws2}`some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`。
如果 {anchorName ApplicativeOptionLaws2}`u`、{anchorName ApplicativeOptionLaws2}`v` 或 {anchorName ApplicativeOptionLaws2}`w` 中的任意一个是 {anchorName ApplicativeOption}`none`，那么等式两边都是 {anchorName ApplicativeOption}`none`，因此该性质成立。
假设 {anchorName ApplicativeOptionLaws2}`u` 是 {anchorTerm OptionHomomorphism1}`some f`，{anchorName ApplicativeOptionLaws2}`v` 是 {anchorTerm OptionHomomorphism1}`some g`，并且 {anchorName ApplicativeOptionLaws2}`w` 是 {anchorTerm OptionHomomorphism1}`some x`，那么这等价于说 {anchorTerm OptionHomomorphism}`some (· ∘ ·) <*> some f <*> some g <*> some x = some f <*> (some g <*> some x)`。
对两边求值会得到相同的结果：
```anchorEvalSteps OptionHomomorphism1
some (· ∘ ·) <*> some f <*> some g <*> some x
===>
some (f ∘ ·) <*> some g <*> some x
===>
some (f ∘ g) <*> some x
===>
some ((f ∘ g) x)
===>
some (f (g x))
```
```anchorEvalSteps OptionHomomorphism2
some f <*> (some g <*> some x)
===>
some f <*> (some (g x))
===>
some (f (g x))
```

第三条规则直接由 {anchorName fakeSeq}`seq` 的定义推出：
```anchorEvalSteps OptionPureSeq
some f <*> some x
===>
f <$> some x
===>
some (f x)
```

在第四种情形中，假设 {anchorName ApplicativeLaws}`u` 是 {anchorTerm OptionPureSeq}`some f`，因为如果它是 {anchorName AlternativeOption}`none`，则等式两边都是 {anchorName AlternativeOption}`none`。
{anchorTerm OptionPureSeq}`some f <*> some x` 直接求值为 {anchorTerm OptionPureSeq}`some (f x)`，{anchorTerm OptionPureSeq2}`some (fun g => g x) <*> some f` 亦然。


# 所有应用函子都是函子
%%%
tag := "applicatives-are-functors"
file := "All-Applicatives-are-Functors"
%%%

{anchorName ApplicativeMap}`Applicative` 的两个运算符足以定义 {anchorName ApplicativeMap}`map`：

```anchor ApplicativeMap
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
```

然而，只有在 {anchorName ApplicativeLaws}`Applicative` 的契约保证 {anchorName ApplicativeLaws}`Functor` 的契约时，才能用它来实现 {anchorName ApplicativeLaws}`Functor`。
{anchorName ApplicativeLaws}`Functor` 的第一条规则是 {anchorTerm AppToFunTerms}`id <$> x = x`，这直接由 {anchorName ApplicativeLaws}`Applicative` 的第一条规则推出。
{anchorName ApplicativeLaws}`Functor` 的第二条规则是 {anchorTerm AppToFunTerms}`map (f ∘ g) x = map f (map g x)`。
在这里展开 {anchorName AppToFunTerms}`map` 的定义会得到 {anchorTerm AppToFunTerms}`pure (f ∘ g) <*> x = pure f <*> (pure g <*> x)`。
使用纯操作的顺序执行是无操作这一规则，左侧可以改写为 {anchorTerm AppToFunTerms}`pure (· ∘ ·) <*> pure f <*> pure g <*> x`。
这是应用函子尊重函数复合这一规则的一个实例。

这证明了如下 {anchorName ApplicativeMap}`Applicative` 定义的合理性：它扩展 {anchorName ApplicativeLaws}`Functor`，并给出用 {anchorName ApplicativeExtendsFunctorOne}`pure` 和 {anchorName ApplicativeExtendsFunctorOne}`seq` 表示的 {anchorTerm ApplicativeExtendsFunctorOne}`map` 的默认定义：

```anchor ApplicativeExtendsFunctorOne
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)
```

# 所有单子都是应用函子
%%%
tag :="monads-are-applicative"
file := "All-Monads-are-Applicative-Functors"
%%%

{anchorName MonadExtends}`Monad` 的一个实例已经要求实现 {anchorName MonadSeq}`pure`。
这与 {anchorName MonadExtends}`bind` 合在一起，足以定义 {anchorName MonadSeq}`seq`：

```anchor MonadSeq
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
```
再次，检查 {anchorName MonadSeq}`Monad` 约定蕴含 {anchorName MonadExtends}`Applicative` 约定，将允许在 {anchorName MonadSeq}`Monad` 扩展 {anchorName MonadExtends}`Applicative` 时，将此作为 {anchorTerm MonadExtends}`seq` 的默认定义。

本节余下部分给出一个论证，说明这个基于 {anchorName MonadExtends}`bind` 的 {anchorTerm MonadExtends}`seq` 实现事实上满足 {anchorName MonadExtends}`Applicative` 契约。
函数式编程的美妙之处之一在于，这类论证可以用铅笔在纸上完成，只需使用 {ref "evaluating"}[关于表达式求值的起始小节]中的那类求值规则。
在阅读这些论证时思考这些运算的含义，有时有助于理解。

将 {kw}`do` 记法替换为对 {lit}`>>=` 的显式使用，会使应用 {anchorName MonadSeqDesugar}`Monad` 规则更容易：

```anchor MonadSeqDesugar
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
```


要检查此定义是否遵守恒等律，需要检查 {anchorTerm mSeqRespIdInit}`seq (pure id) (fun () => v) = v`。
左边等价于 {anchorTerm mSeqRespIdInit}`pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y)`。
中间的单位函数可以立即消去，得到 {anchorTerm mSeqRespIdInit}`pure id >>= fun g => v >>= fun y => pure (g y)`。
利用 {anchorName mSeqRespIdInit}`pure` 是 {anchorTerm mSeqRespIdInit}`>>=` 的左单位元这一事实，这与 {anchorTerm mSeqRespIdInit}`v >>= fun y => pure (id y)` 相同，而 {anchorTerm mSeqRespIdInit}`v >>= fun y => pure (id y)` 就是 {anchorTerm mSeqRespIdInit}`v >>= fun y => pure y`。
因为 {anchorTerm mSeqRespIdInit}`fun x => f x` 与 {anchorName mSeqRespIdInit}`f` 相同，所以这与 {anchorTerm mSeqRespIdInit}`v >>= pure` 相同；再利用 {anchorName mSeqRespIdInit}`pure` 是 {anchorTerm mSeqRespIdInit}`>>=` 的右单位元这一事实，可以得到 {anchorName mSeqRespIdInit}`v`。

这种非形式化推理可以通过稍作重新排版而变得更易读。
在下表中，将“{lit}`EXPR1 ={ REASON }= EXPR2`”读作“{lit}`EXPR1` 与 {lit}`EXPR2` 相同，因为 {lit}`REASON`”：

```anchorEqSteps mSeqRespId
pure id >>= fun g => v >>= fun y => pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
v >>= fun y => pure (id y)
={
/-- Reduce the call to `id` -/
}=
v >>= fun y => pure y
={
/-- `fun x => f x` is the same as `f` -/
by
  have {α β } {f : α → β} : (fun x => f x) = (f) := rfl
  rfl
}=
v >>= pure
={
/-- `pure` is a right identity of `>>=` -/
by simp
}=
v
```



要检查它是否尊重函数复合，需检查 {anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`。
第一步是用 {anchorName MonadSeqDesugar}`seq` 的这个定义替换 {lit}`<*>`。
此后，使用 {anchorName ApplicativeLaws}`Monad` 约定中的恒等律和结合律的一系列（稍长的）步骤，足以从一边得到另一边：
```anchorEqSteps mSeqRespComp
seq (seq (seq (pure (· ∘ ·)) (fun _ => u))
      (fun _ => v))
  (fun _ => w)
={
/-- Definition of `seq` -/
}=
((pure (· ∘ ·) >>= fun f =>
   u >>= fun x =>
   pure (f x)) >>= fun g =>
  v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Insertion of parentheses for clarity -/
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= (fun g =>
   v >>= fun y =>
  pure (g y))) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
(u >>= fun x =>
  pure (x ∘ ·) >>= fun g =>
 v  >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp only [LawfulMonad.pure_bind]
}=
(u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- Associativity of `>>=` -/
by simp only [LawfulMonad.bind_assoc]
}=
u >>= fun x =>
v >>= fun y =>
pure (x ∘ y) >>= fun h =>
w >>= fun z =>
pure (h z)
={
/-- `pure` is a left identity of `>>=` -/
by simp [bind_pure_comp]; rfl
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure ((x ∘ y) z)
={
/-- Definition of function composition -/
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (x (y z))
={
/--
Time to start moving backwards!
`pure` is a left identity of `>>=`
-/
by simp
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (y z) >>= fun q =>
pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
v >>= fun y =>
 (w >>= fun p =>
  pure (y p)) >>= fun q =>
 pure (x q)
={
/-- Associativity of `>>=` -/
by simp
}=
u >>= fun x =>
 (v >>= fun y =>
  w >>= fun q =>
  pure (y q)) >>= fun z =>
 pure (x z)
={
/-- This includes the definition of `seq` -/
}=
u >>= fun x =>
seq v (fun () => w) >>= fun q =>
pure (x q)
={
/-- This also includes the definition of `seq` -/
}=
seq u (fun () => seq v (fun () => w))
```


为了检查对纯操作进行顺序执行是一个无操作：
```anchorEqSteps mSeqPureNoOp
seq (pure f) (fun () => pure x)
={
/-- Replacing `seq` with its definition -/
}=
pure f >>= fun g =>
pure x >>= fun y =>
pure (g y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure f >>= fun g =>
pure (g x)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
pure (f x)
```


最后，检查纯操作的顺序无关紧要：
```anchorEqSteps mSeqPureNoOrder
seq u (fun () => pure x)
={
/-- Definition of `seq` -/
}=
u >>= fun f =>
pure x >>= fun y =>
pure (f y)
={
/-- `pure` is a left identity of `>>=` -/
by simp
}=
u >>= fun f =>
pure (f x)
={
/-- Clever replacement of one expression by an equivalent one that makes the rule match -/
}=
u >>= fun f =>
pure ((fun g => g x) f)
={
/-- `pure` is a left identity of `>>=` -/
by simp [LawfulMonad.pure_bind]
}=
pure (fun g => g x) >>= fun h =>
u >>= fun f =>
pure (h f)
={
/-- Definition of `seq` -/
}=
seq (pure (fun f => f x)) (fun () => u)
```


这说明可以合理地定义一个扩展 {anchorName ApplicativeLaws}`Applicative` 的 {anchorName ApplicativeLaws}`Monad`，并为 {anchorTerm MonadExtends}`seq` 给出默认定义：

```anchor MonadExtends
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)
```
{anchorName MonadExtends}`Applicative` 自身对 {anchorTerm ApplicativeExtendsFunctorOne}`map` 的默认定义意味着，每个 {anchorName MonadExtends}`Monad` 实例也会自动生成 {anchorName MonadExtends}`Applicative` 和 {anchorName ApplicativeExtendsFunctorOne}`Functor` 实例。

# 附加约定
%%%
tag := "additional-stipulations"
file := "Additional-Stipulations"
%%%

除了遵守与每个类型类相关联的各自约定之外，组合实现 {anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Applicative` 和 {anchorName ApplicativeLaws}`Monad` 应当与这些默认实现等价地工作。
换言之，一个同时提供 {anchorName ApplicativeLaws}`Applicative` 和 {anchorName ApplicativeLaws}`Monad` 实例的类型，不应有一个 {anchorTerm MonadExtends}`seq` 的实现，其行为不同于 {anchorName MonadSeq}`Monad` 实例作为默认实现所生成的版本。
这一点很重要，因为多态函数可能会被重构，将 {lit}`>>=` 的使用替换为 {lit}`<*>` 的等价使用，或者将 {lit}`<*>` 的使用替换为 {lit}`>>=` 的等价使用。
这种重构不应改变使用此代码的程序的含义。

这条规则解释了为什么不应在 {anchorName ApplicativeLaws}`Monad` 实例中使用 {anchorName ValidateAndThen}`Validate.andThen` 来实现 {anchorName MonadExtends}`bind`。
就其自身而言，它遵守单子约定。
然而，当它被用来实现 {anchorTerm MonadExtends}`seq` 时，其行为并不等价于 {anchorTerm MonadExtends}`seq` 本身。
为了看出它们的差异，考虑两个计算的例子，这两个计算都会返回错误。
先从一个应当返回两个错误的情形开始：一个错误来自验证函数（它同样也可能来自该函数的先前参数），另一个错误来自验证实参：

```anchor counterexample
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
```

将它们与 {anchorName Validate}`Validate` 的 {anchorName ApplicativeValidate}`Applicative` 实例中的 {lit}`<*>` 版本组合，会导致两个错误都报告给用户：
```anchorEvalSteps realSeq
notFun <*> notArg
===>
match notFun with
| .ok g => g <$> notArg
| .errors errs =>
  match notArg with
  | .ok _ => .errors errs
  | .errors errs' => .errors (errs ++ errs')
===>
match notArg with
| .ok _ =>
  .errors { head := "First error", tail := [] }
| .errors errs' =>
  .errors ({ head := "First error", tail := [] } ++ errs')
===>
.errors
  ({ head := "First error", tail := [] } ++
   { head := "Second error", tail := []})
===>
.errors {
  head := "First error",
  tail := ["Second error"]
}
```

使用以 {lit}`>>=` 实现的 {anchorName MonadSeqDesugar}`seq` 版本（这里改写为 {anchorName fakeSeq}`andThen`）时，结果是只能得到第一个错误：
```anchorEvalSteps fakeSeq
seq notFun (fun () => notArg)
===>
notFun.andThen fun g =>
notArg.andThen fun y =>
pure (g y)
===>
match notFun with
| .errors errs => .errors errs
| .ok val =>
  (fun g =>
    notArg.andThen fun y =>
    pure (g y)) val
===>
.errors { head := "First error", tail := [] }
```
