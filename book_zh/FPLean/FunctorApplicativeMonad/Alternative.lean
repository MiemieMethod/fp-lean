import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "选择" =>
%%%
tag := "alternative"
file := "Alternatives"
%%%


# 从失败中恢复
%%%
tag := "alternative-recovery"
file := "Recovery-from-Failure"
%%%

{anchorName Validate}`Validate` 也可用于输入有多种可接受方式的情形。
对于输入表单 {anchorName RawInput}`RawInput`，一组实现旧系统约定的替代业务规则可以如下：

 1. 所有人类用户都必须提供四位数字的出生年份。
 2. 由于较早记录不完整，1970 年以前出生的用户不需要提供姓名。
 3. 1970 年以后出生的用户必须提供姓名。
 4. 公司应当将 {anchorTerm checkCompany}`"FIRM"` 输入为其诞生年份，并提供公司名称。

对于 1970 年出生的用户，并未作出任何特别安排。
预期他们要么放弃，要么谎报自己的出生年份，要么打电话联系。
公司认为这是开展业务可以接受的成本。

下面的归纳类型刻画了可由这些给定规则产生的值：

```anchor LegacyCheckedInput
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr
```

然而，这些规则的验证器更为复杂，因为它必须处理全部三种情况。
虽然它可以写成一系列嵌套的 {kw}`if` 表达式，但更容易的做法是分别设计这三种情况，然后将它们组合起来。
这需要一种在保留错误消息的同时从失败中恢复的机制：

```anchor ValidateorElse
def Validate.orElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
```

这种从失败中恢复的模式非常常见，因此 Lean 为它提供了内置语法，并将其附属于名为 {anchorName OrElse}`OrElse` 的类型类：

```anchor OrElse
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
```
表达式 {anchorTerm OrElseSugar}`E1 <|> E2` 是 {anchorTerm OrElseSugar}`OrElse.orElse E1 (fun () => E2)` 的简写。
{anchorName Validate}`Validate` 的 {anchorName OrElse}`OrElse` 实例允许将此语法用于错误恢复：

```anchor OrElseValidate
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
```

{anchorName LegacyCheckedInput}`LegacyCheckedInput` 的验证器可以由每个构造子的验证器构造出来。
公司的规则规定，诞生年份应当是字符串 {anchorTerm checkCompany}`"FIRM"`，并且名称应当非空。
然而，构造子 {anchorName names1}`LegacyCheckedInput.company` 完全没有诞生年份的表示，因此没有简单的方法用 {anchorTerm checkCompanyProv}`<*>` 来完成这一点。
关键是使用一个带有 {anchorTerm checkCompanyProv}`<*>` 的函数，并让它忽略自己的参数。

检查一个布尔条件成立、但不在类型中记录关于这一事实的任何证据，可以用 {anchorName checkThat}`checkThat` 完成：

```anchor checkThat
def checkThat (condition : Bool)
    (field : Field) (msg : String) :
    Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
```
{anchorName checkCompanyProv}`checkCompany` 的这个定义使用 {anchorName checkCompanyProv}`checkThat`，然后丢弃所得的 {anchorName checkThat}`Unit` 值：

```anchor checkCompanyProv
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" <*>
    checkName input.name
```

然而，这一定义相当冗长。
它可以通过两种方式简化。
第一种是将第一次使用的 {anchorTerm checkCompanyProv}`<*>` 替换为一个专门版本，该版本会自动忽略第一个参数返回的值，称为 {anchorTerm checkCompany}`*>`。
这个运算符同样由一个类型类控制，该类型类称为 {anchorName ClassSeqRight}`SeqRight`，并且 {anchorTerm seqRightSugar}`E1 *> E2` 是 {anchorTerm seqRightSugar}`SeqRight.seqRight E1 (fun () => E2)` 的语法糖：

```anchor ClassSeqRight
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
```
存在一个用 {anchorName fakeSeq}`seq` 定义 {anchorName ClassSeqRight}`seqRight` 的默认实现：{lit}`seqRight (a : f α) (b : Unit → f β) : f β := pure (fun _ x => x) <*> a <*> b ()`。

使用 {anchorName ClassSeqRight}`seqRight` 后，{anchorName checkCompanyProv2}`checkCompany` 变得更简单：

```anchor checkCompanyProv2
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name
```
还可以再做一次简化。
对于每个 {anchorName ApplicativeExcept}`Applicative`，{anchorTerm ApplicativeLaws}`pure f <*> E` 等价于 {anchorTerm ApplicativeLaws}`f <$> E`。
换言之，使用 {anchorName fakeSeq}`seq` 来应用一个通过 {anchorName ApplicativeExtendsFunctorOne}`pure` 放入 {anchorName ApplicativeExtendsFunctorOne}`Applicative` 类型中的函数，是过度的；该函数本可以直接使用 {anchorName ApplicativeLaws}`Functor.map` 来应用。
这种简化得到：

```anchor checkCompany
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  .company <$> checkName input.name
```

{anchorName LegacyCheckedInput}`LegacyCheckedInput` 剩余的两个构造子在其字段中使用子类型。
一个用于检查子类型的通用工具会使这些定义更易读：

```anchor checkSubtype
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
```
在该函数的参数列表中，类型类 {anchorTerm checkSubtype}`[Decidable (p v)]` 出现在参数 {anchorName checkSubtype}`v` 和 {anchorName checkSubtype}`p` 的指定之后，这一点很重要。
否则，它将指向一组额外的自动隐式参数，而不是指向手动提供的值。
正是 {anchorName checkSubtype}`Decidable` 实例使得命题 {anchorTerm checkSubtype}`p v` 可以用 {kw}`if` 检查。

这两种人类情形不需要任何额外工具：

```anchor checkHumanBefore1970
def checkHumanBefore1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970)
        ("birth year", "less than 1970") <*>
      pure input.name
```

```anchor checkHumanAfter1970
def checkHumanAfter1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970)
        ("birth year", "greater than 1970") <*>
      checkName input.name
```

这三种情形的验证器可以使用 {anchorTerm OrElseSugar}`<|>` 组合起来：

```anchor checkLegacyInput
def checkLegacyInput (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input
```

成功的情形如预期那样返回 {anchorName LegacyCheckedInput}`LegacyCheckedInput` 的构造子：
```anchor trollGroomers
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
```
```anchorInfo trollGroomers
Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")
```
```anchor johnny
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
```
```anchorInfo johnny
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")
```
```anchor johnnyAnon
#eval checkLegacyInput ⟨"", "1963"⟩
```
```anchorInfo johnnyAnon
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")
```

最坏的可能输入会返回所有可能的失败：
```anchor allFailures
#eval checkLegacyInput ⟨"", "1970"⟩
```
```anchorInfo allFailures
Validate.errors
  { head := ("birth year", "FIRM if a company"),
    tail := [("name", "Required"),
             ("birth year", "less than 1970"),
             ("birth year", "greater than 1970"),
             ("name", "Required")] }
```


# {lit}`Alternative` 类
%%%
tag := "Alternative"
file := "The-Alternative-Class"
%%%

许多类型都支持某种失败与恢复的概念。
关于{ref "nondeterministic-search"}[在多种单子中求值算术表达式]一节中的 {anchorName AlternativeMany}`Many` 单子就是这样一种类型，{anchorName AlternativeOption}`Option` 也是如此。
二者都支持不提供原因的失败（这不同于例如 {anchorName ApplicativeExcept}`Except` 和 {anchorName Validate}`Validate`，它们要求给出某种关于出错原因的指示）。

{anchorName FakeAlternative}`Alternative` 类描述了具有额外的失败与恢复运算符的应用函子：

```anchor FakeAlternative
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α
```
正如 {anchorTerm misc}`Add α` 的实现者可以免费获得 {anchorTerm misc}`HAdd α α α` 实例一样，{anchorName FakeAlternative}`Alternative` 的实现者也可以免费获得 {anchorName OrElse}`OrElse` 实例：

```anchor AltOrElse
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
```

{anchorName ApplicativeOption}`Option` 的 {anchorName FakeAlternative}`Alternative` 实现会保留第一个非 {anchorName ApplicativeOption}`none` 参数：

```anchor AlternativeOption
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()
```
类似地，{anchorName AlternativeMany}`Many` 的实现遵循 {moduleName (module := Examples.Monads.Many)}`Many.union` 的一般结构，只是由于诱导惰性的 {anchorName guard}`Unit` 参数放置位置不同而有一些细微差异：

```anchor AlternativeMany
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse
```

与其他类型类一样，{anchorName FakeAlternative}`Alternative` 使得可以定义多种操作，它们适用于实现了 {anchorName FakeAlternative}`Alternative` 的_任意_应用函子。
其中最重要的一个是 {anchorName guard}`guard`；当一个可判定命题为假时，它会导致 {anchorName guard}`failure`：

```anchor guard
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure
```
在单子程序中提前终止执行非常有用。
在 {anchorName evenDivisors}`Many` 中，它可用于过滤掉搜索的一整个分支，如下面这个计算某个自然数的所有偶因子的程序所示：

```anchor evenDivisors
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
```
在 {anchorTerm evenDivisors20}`20` 上运行它会得到预期结果：
```anchor evenDivisors20
#eval (evenDivisors 20).takeAll
```
```anchorInfo evenDivisors20
[20, 10, 4, 2]
```


# 练习
%%%
tag := "Alternative-exercises"
file := "Exercises"
%%%

## 改进验证的友好性
%%%
tag := none
file := "Improve-Validation-Friendliness"
%%%

使用 {anchorTerm OrElseSugar}`<|>` 的 {anchorName Validate}`Validate` 程序所返回的错误可能难以阅读，因为被包含在错误列表中仅仅意味着该错误可以通过_某条_代码路径到达。
可以使用一种结构更强的错误报告，更准确地引导用户完成该过程：

 * 将 {anchorName misc}`Validate.errors` 中的 {anchorName Validate}`NonEmptyList` 替换为一个裸类型变量，然后更新 {anchorTerm ApplicativeValidate}`Applicative (Validate ε)` 和 {anchorTerm OrElseValidate}`OrElse (Validate ε α)` 实例的定义，使其只要求存在可用的 {anchorTerm misc}`Append ε` 实例。
 * 定义一个函数 {anchorTerm misc}`Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α`，它转换一次验证运行中的所有错误。
 * 使用数据类型 {anchorName TreeError}`TreeError` 表示错误，重写旧版验证系统，使其跟踪自己穿过这三个备选分支的路径。
 * 编写一个函数 {anchorTerm misc}`report : TreeError → String`，输出 {anchorName TreeError}`TreeError` 所累积的警告和错误的用户友好视图。

```anchor TreeError
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
```
