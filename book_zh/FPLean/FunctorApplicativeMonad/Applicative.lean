import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "应用函子" =>
%%%
tag := "applicative"
file := "Applicative-Functors"
%%%

_应用函子_是具有两个额外可用操作的函子：{anchorName ApplicativeOption}`pure` 和 {anchorName ApplicativeOption}`seq`。
{anchorName ApplicativeOption}`pure` 与 {anchorName ApplicativeLaws}`Monad` 中使用的是同一个运算符，因为 {anchorName ApplicativeLaws}`Monad` 实际上继承自 {anchorName ApplicativeOption}`Applicative`。
{anchorName ApplicativeOption}`seq` 很像 {anchorName FunctorNames}`map`：它允许使用一个函数来变换某个数据类型中的内容。
然而，对于 {anchorName ApplicativeOption}`seq`，函数本身也包含在该数据类型中：{anchorTerm seqType}`f (α → β) → (Unit → f α) → f β`。
将函数置于类型 {anchorName seqType}`f` 之下，使得 {anchorName ApplicativeOption}`Applicative` 实例能够控制该函数如何被应用，而 {anchorName FunctorNames}`Functor.map` 则无条件地应用一个函数。
第二个参数的类型以 {anchorTerm seqType}`Unit →` 开头，以便在函数永远不会被应用的情况下，允许 {anchorName ApplicativeOption}`seq` 的定义短路。

这种短路行为的价值可以在 {anchorTerm ApplicativeOption}`Applicative Option` 的实例中看到：

```anchor ApplicativeOption
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
```
在这种情况下，如果没有可供 {anchorName ApplicativeOption}`seq` 应用的函数，那么就无需计算其参数，因此 {anchorName ApplicativeOption}`x` 永远不会被调用。
同样的考虑也影响了 {anchorName ApplicativeExcept}`Except` 的 {anchorName ApplicativeExcept}`Applicative` 实例：

```anchor ApplicativeExcept
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
```
这种短路行为仅依赖于_包围_该函数的 {anchorName AlternativeOption}`Option` 或 {anchorName ApplicativeExcept}`Except` 结构，而不依赖于函数本身。

单子可以看作是在纯函数式语言中捕获顺序执行语句这一概念的一种方式。
一个语句的结果可以影响接下来运行哪些语句。
这可以从 {anchorName bindType}`bind` 的类型中看出：{anchorTerm bindType}`m α → (α → m β) → m β`。
第一个语句产生的值会作为输入传给一个函数，该函数计算下一个要执行的语句。
连续使用 {anchorName bindType}`bind` 就像命令式编程语言中的语句序列，而 {anchorName bindType}`bind` 足够强大，可以实现条件和循环等控制结构。

按照这个类比，{anchorName ApplicativeId}`Applicative` 捕获的是带有副作用的语言中的函数应用。
在 Kotlin 或 C# 这样的语言中，函数的参数从左到右求值。
较早参数执行的副作用发生在较晚参数执行的副作用之前。
然而，函数本身并不足以实现依赖于某个参数具体_值_的自定义短路运算符。

通常不会直接调用 {anchorName ApplicativeExtendsFunctorOne}`seq`。
相反，会使用运算符 {lit}`<*>`。
该运算符把它的第二个参数包装在 {lit}`fun () => ...` 中，从而简化调用位置。
换言之，{anchorTerm seqSugar}`E1 <*> E2` 是 {anchorTerm seqSugar}`Seq.seq E1 (fun () => E2)` 的语法糖。


使 {anchorName ApplicativeExtendsFunctorOne}`seq` 能够与多个参数一起使用的关键特性在于，Lean 中的多参数函数实际上是一个单参数函数，它返回另一个正在等待其余参数的函数。
换言之，如果 {anchorName ApplicativeExtendsFunctorOne}`seq` 的第一个参数正在等待多个参数，那么 {anchorName ApplicativeExtendsFunctorOne}`seq` 的结果将会等待其余参数。
例如，{anchorTerm somePlus}`some Plus.plus` 可以具有类型 {anchorTerm somePlus}`Option (Nat → Nat → Nat)`。
提供一个参数 {anchorTerm somePlusFour}`some Plus.plus <*> some 4` 后，得到类型 {anchorTerm somePlusFour}`Option (Nat → Nat)`。
这本身又可以与 {anchorName ApplicativeExtendsFunctorOne}`seq` 一起使用，因此 {anchorTerm somePlusFourSeven}`some Plus.plus <*> some 4 <*> some 7` 具有类型 {anchorTerm somePlusFourSeven}`Option Nat`。

并非每个函子都是应用函子。
{anchorName Pair}`Pair` 类似于内建的积类型 {anchorName names}`Prod`：

```anchor Pair
structure Pair (α β : Type) : Type where
  first : α
  second : β
```
与 {anchorName ApplicativeExcept}`Except` 一样，{anchorTerm PairType}`Pair` 的类型是 {anchorTerm PairType}`Type → Type → Type`。
这意味着 {anchorTerm FunctorPair}`Pair α` 的类型是 {anchorTerm PairType}`Type → Type`，并且可以给出一个 {anchorName FunctorPair}`Functor` 实例：

```anchor FunctorPair
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
```
此实例遵守 {anchorName FunctorPair}`Functor` 契约。

需要检查的两个性质是 {anchorEvalStep checkPairMapId 0}`id <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapId 2}`Pair.mk x y` 以及 {anchorEvalStep checkPairMapComp1 0}`f <$> g <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapComp2 0}`(f ∘ g) <$> Pair.mk x y`。
第一个性质可以只通过逐步求值左侧来检查，并注意到它求值为右侧：
```anchorEvalSteps checkPairMapId
id <$> Pair.mk x y
===>
Pair.mk x (id y)
===>
Pair.mk x y
```
第二个可以通过逐步执行两边并注意到它们产生相同结果来检查：
```anchorEvalSteps checkPairMapComp1
f <$> g <$> Pair.mk x y
===>
f <$> Pair.mk x (g y)
===>
Pair.mk x (f (g y))
```
```anchorEvalSteps checkPairMapComp2
(f ∘ g) <$> Pair.mk x y
===>
Pair.mk x ((f ∘ g) y)
===>
Pair.mk x (f (g y))
```

然而，尝试定义一个 {anchorName ApplicativeExcept}`Applicative` 实例并不顺利。
它将需要一个 {anchorName Pairpure (show := pure)}`Pair.pure` 的定义：
```anchor Pairpure
def Pair.pure (x : β) : Pair α β := _
```
```anchorError Pairpure
don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β
```
作用域中有一个类型为 {anchorName Pairpure2}`β` 的值（即 {anchorName Pairpure2}`x`），而下划线给出的错误消息提示下一步是使用构造子 {anchorName Pairpure2}`Pair.mk`：
```anchor Pairpure2
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
```
```anchorError Pairpure2
don't know how to synthesize placeholder for argument `first`
context:
β α : Type
x : β
⊢ α
```
遗憾的是，并不存在可用的 {anchorName Pairpure2}`α`。
因为为了定义 {anchorTerm ApplicativePair}`Applicative (Pair α)` 的实例，{anchorName Pairpure2 (show := pure)}`Pair.pure` 必须对_所有可能的类型_ {anchorName Pairpure2}`α` 都起作用，所以这是不可能的。
毕竟，调用者可以选择令 {anchorName Pairpure2}`α` 为 {anchorName ApplicativePair}`Empty`，而它根本没有任何值。

# 一个非单子的应用函子
%%%
tag := "validate"
file := "A-Non-Monadic-Applicative"
%%%

在验证表单中的用户输入时，通常认为最好一次性提供多个错误，而不是一次只提供一个错误。
这使用户能够总体了解需要做什么才能让计算机满意，而不是在逐个字段纠正错误时感到不断被催促。

理想情况下，验证用户输入这一事实应当在执行验证的函数类型中可见。
它应当返回一个具体的数据类型——例如，检查一个文本框是否包含数字时，应当返回真正的数值类型。
验证例程可以在输入未通过验证时抛出异常。
然而，异常有一个主要缺点：它们会在第一个错误处终止程序，从而使得累积错误列表成为不可能。

另一方面，累积错误列表并在其非空时失败这一常见设计模式也有问题。
一长串嵌套的 {kw}`if` 语句若逐一验证输入数据的各个小节，会很难维护，并且很容易漏掉一两条错误消息。
理想情况下，验证应当能够通过一个 API 执行；该 API 既允许返回一个新值，又能自动跟踪并累积错误消息。

一个名为 {anchorName Validate}`Validate` 的应用函子提供了一种实现这种 API 风格的方法。
类似于 {anchorName ApplicativeExcept}`Except` 单子，{anchorName Validate}`Validate` 允许构造一个新值，以准确刻画经过验证的数据。
不同于 {anchorName ApplicativeExcept}`Except`，它允许累积多个错误，而没有忘记检查列表是否为空的风险。

## 用户输入
%%%
tag := "user-input"
file := "User-Input"
%%%
作为用户输入的一个例子，考虑如下结构：

```anchor RawInput
structure RawInput where
  name : String
  birthYear : String
```
要实现的业务逻辑如下：
 1. 名称不得为空
 2. 出生年份必须是数字且非负
 3. 出生年份必须大于 1900，并且小于或等于该表单被验证时所在的年份

将这些表示为一个数据类型将需要一种称为_子类型_的新特性。
有了这个工具，就可以编写一个使用应用函子来跟踪错误的验证框架，并在该框架中实现这些规则。

## 子类型
%%%
tag := "subtypes"
file := "Subtypes"
%%%

表示这些条件最容易的方式是使用一个额外的 Lean 类型，称为 {anchorName Subtype}`Subtype`：

```anchor Subtype
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
```
这个结构有两个类型参数：一个隐式参数，即数据 {anchorName Subtype}`α` 的类型；以及一个显式参数 {anchorName Subtype}`p`，它是关于 {anchorName Subtype}`α` 的谓词。
_谓词_是一个含有变量的逻辑陈述；用一个值替换该变量即可得到实际陈述，例如{ref "overloading-indexing"}[{moduleName}`GetElem` 的参数]，它描述索引对于一次查找而言处于界内意味着什么。
在 {anchorName Subtype}`Subtype` 的情形中，该谓词从 {anchorName Subtype}`α` 的值中切分出使谓词成立的某个子集。
该结构的两个字段分别是来自 {anchorName Subtype}`α` 的一个值，以及该值满足谓词 {anchorName Subtype}`p` 的证据。
Lean 对 {anchorName Subtype}`Subtype` 有特殊语法。
如果 {anchorName Subtype}`p` 的类型是 {anchorTerm Subtype}`α → Prop`，那么类型 {anchorTerm subtypeSugarIn}`Subtype p` 也可以写作 {anchorTerm subtypeSugar}`{x : α // p x}`，甚至在类型 {anchorName Subtype}`α` 能被自动推断时写作 {anchorTerm subtypeSugar2}`{x // p x}`。

{ref "positive-numbers"}[将正数表示为归纳类型]清晰明了，并且易于编程使用。
然而，它有一个关键缺点。
虽然从 Lean 程序的角度看，{anchorName names}`Nat` 和 {anchorName names}`Int` 具有普通归纳类型的结构，但编译器会对它们作特殊处理，并使用快速的任意精度数值库来实现它们。
对于额外的用户定义类型，情况并非如此。
不过，{anchorName names}`Nat` 的一个将其限制为非零数的子类型，使得新类型既能使用高效表示，又仍能在编译时排除零：

```anchor FastPos
def FastPos : Type := {x : Nat // x > 0}
```

最小的快速正数仍然是一。
现在，它不再是归纳类型的构造子，而是一个用尖括号构造的结构实例。
第一个参数是底层的 {anchorName FastPos}`Nat`，第二个参数是说明该 {anchorName FastPos}`Nat` 大于零的证据：

```anchor one
def one : FastPos := ⟨1, by decide⟩
```
命题 {anchorTerm onep}`1 > 0` 是可判定的，因此 {tactic}`decide` 策略会产生必要的证据。
{anchorName OfNatFastPos}`OfNat` 实例非常类似于 {anchorName Pos (module:=Examples.Classes)}`Pos` 的实例，只是它使用一个简短的策略证明来提供 {lit}`n + 1 > 0` 的证据：

```anchor OfNatFastPos
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩
```
这里需要 {tactic}`simp`，因为 {tactic}`decide` 需要具体的值，但所讨论的命题是 {anchorTerm OfNatFastPosp}`n + 1 > 0`。

子类型是一把双刃剑。
它们允许高效地表示验证规则，但也把维护这些规则的负担转移给库的用户，用户必须_证明_自己没有违反重要的不变量。
一般而言，将它们用于库的内部是个好主意，同时向用户提供一个能自动确保所有不变量都得到满足的 API，并将任何必要证明都保留在库的内部。

检查类型为 {anchorName NatFastPosRemarks}`α` 的值是否属于子类型 {anchorTerm NatFastPosRemarks}`{x : α // p x}`，通常要求命题 {anchorTerm NatFastPosRemarks}`p x` 是可判定的。
{ref "equality-and-ordering"}[关于相等性和序关系类的一节]描述了可判定命题如何与 {kw}`if` 一起使用。
当 {kw}`if` 与一个可判定命题一起使用时，可以提供一个名称。
在 {kw}`then` 分支中，该名称绑定到该命题为真的证据；在 {kw}`else` 分支中，它绑定到该命题为假的证据。
这在检查给定的 {anchorName NatFastPos}`Nat` 是否为正时很有用：

```anchor NatFastPos
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none
```
在 {kw}`then` 分支中，{anchorName NatFastPos}`h` 被绑定为表明 {anchorTerm NatFastPos}`n > 0` 的证据，而此证据可用作 {anchorName Subtype}`Subtype` 的构造子的第二个实参。


## 已验证的输入
%%%
tag := "validated-input"
file := "Validated-Input"
%%%

经过验证的用户输入是一个结构，它使用多种技术表达业务逻辑：
 * 该结构类型本身编码了它被检查为有效时的年份，因此 {anchorTerm CheckedInputEx}`CheckedInput 2019` 与 {anchorTerm CheckedInputEx}`CheckedInput 2020` 不是同一个类型
 * 出生年份表示为 {anchorName CheckedInput}`Nat`，而不是 {anchorName CheckedInput}`String`
 * 子类型用于约束名称字段和诞生年份字段中的允许值

```anchor CheckedInput
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
```

:::paragraph
输入验证器应当以当前年份和一个 {anchorName RawInput}`RawInput` 作为实参，并返回一个已检查的输入，或者至少一个验证失败。
这由 {anchorName Validate}`Validate` 类型表示：
```anchor Validate
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
```
它看起来非常像 {anchorName ApplicativeExcept}`Except`。
唯一的区别是，{anchorName Validate}`errors` 构造子可以包含不止一个失败。
:::

{anchorName Validate}`Validate` 是一个函子。
在其上映射一个函数，会变换其中可能存在的任何成功值，就如同 {anchorName ApplicativeExcept}`Except` 的 {anchorName FunctorValidate}`Functor` 实例中那样：

```anchor FunctorValidate
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
```

{anchorName ApplicativeValidate}`Validate` 的 {anchorName ApplicativeValidate}`Applicative` 实例与 {anchorName ApplicativeExcept}`Except` 的实例有一个重要区别：{anchorName ApplicativeExcept}`Except` 的实例会在遇到第一个错误时终止，而 {anchorName ApplicativeValidate}`Validate` 的实例会谨慎地累积来自函数分支和参数分支_两者_的所有错误：

```anchor ApplicativeValidate
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')
```

:::paragraph
将 {anchorName ApplicativeValidate}`.errors` 与 {anchorName Validate}`NonEmptyList` 的构造子一起使用有些冗长。
像 {anchorName reportError}`reportError` 这样的辅助函数能使代码更可读。
在此应用中，错误报告将由字段名与消息配对组成：

```anchor Field
def Field := String
```

```anchor reportError
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
```
:::

{anchorName ApplicativeValidate}`Validate` 的 {anchorName ApplicativeValidate}`Applicative` 实例允许分别编写每个字段的检查过程，然后将它们组合起来。
检查名称包括确保字符串非空，然后以 {anchorName Subtype}`Subtype` 的形式返回这一事实的证据。
这使用了 {kw}`if` 的证据绑定版本：

```anchor checkName
def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
```
在 {kw}`then` 分支中，{anchorName checkName}`h` 被绑定为表明 {anchorTerm checkName}`name = ""` 的证据；而在 {kw}`else` 分支中，它被绑定为表明 {lit}`¬name = ""` 的证据。

确实有些验证错误会使其他检查无法进行。
例如，如果一个困惑的用户写下单词 {anchorTerm checkDavidSyzygy}`"syzygy"` 而不是一个数字，那么检查出生年份字段是否大于 1900 就毫无意义。
只有在确保该字段事实上包含一个数字之后，检查该数字的允许范围才有意义。
这可以用函数 {anchorName ValidateAndThen (show := andThen)}`Validate.andThen` 表达：

```anchor ValidateAndThen
def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
```
虽然此函数的类型签名使其适合在 {anchorTerm bindType}`Monad` 实例中用作 {anchorName bindType}`bind`，但有充分理由不这样做。
这些理由在{ref "additional-stipulations"}[描述 {anchorName ApplicativeExcept}`Applicative` 约定的那一节]中说明。

为了检查出生年份是否为数字，一个名为 {anchorTerm CheckedInputEx}`String.toNat? : String → Option Nat` 的内置函数很有用。
最为用户友好的做法是先使用 {anchorName CheckedInputEx}`String.trim` 去除首尾空白：

```anchor checkYearIsNat
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n
```

:::paragraph
为了检查所提供的年份是否处于预期范围内，应当嵌套使用 {kw}`if` 的提供证据形式：

```anchor checkBirthYear
def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"
```
:::

:::paragraph
最后，可以使用 {anchorTerm checkInput}`<*>` 将这三个组成部分组合起来：

```anchor checkInput
def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat
```
:::

:::paragraph
测试 {anchorName checkDavid1984}`checkInput` 表明，它确实可以返回多条反馈：
```anchor checkDavid1984
#eval checkInput 2023 {name := "David", birthYear := "1984"}
```
```anchorInfo checkDavid1984
Validate.ok { name := "David", birthYear := 1984 }
```
```anchor checkBlank2045
#eval checkInput 2023 {name := "", birthYear := "2045"}
```
```anchorInfo checkBlank2045
Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }
```
```anchor checkDavidSyzygy
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
```
```anchorInfo checkDavidSyzygy
Validate.errors { head := ("birth year", "Must be digits"), tail := [] }
```
:::

使用 {anchorName checkInput}`checkInput` 进行表单验证，展示了 {anchorName ApplicativeNames}`Applicative` 相对于 {anchorName MonadExtends}`Monad` 的一个关键优势。
由于 {lit}`>>=` 提供了足够的能力，可以根据第一步得到的值来修改程序其余部分的执行，它就_必须_从第一步接收一个值以便继续传递。
如果没有接收到值（例如因为发生了错误），那么 {lit}`>>=` 就无法执行程序的其余部分。
{anchorName Validate}`Validate` 展示了为什么无论如何运行程序的其余部分可能是有用的：在不需要先前数据的情况下，运行程序的其余部分可以产生有用信息（在此情形中，是更多验证错误）。
{anchorName ApplicativeNames}`Applicative` 的 {lit}`<*>` 可以在重新组合结果之前运行其两个参数。
类似地，{lit}`>>=` 强制顺序执行。
每一步都必须完成后，下一步才可以运行。
这通常是有用的，但它使得不同线程无法并行执行，而这种并行本可从程序的实际数据依赖关系中自然产生。
像 {anchorName MonadExtends}`Monad` 这样更强大的抽象增加了 API 使用者可获得的灵活性，但降低了 API 实现者可获得的灵活性。
