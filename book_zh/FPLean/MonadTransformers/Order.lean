import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Defs"

#doc (Manual) "单子转换器的排序" =>
%%%
tag := "monad-transformer-order"
file := "Ordering-Monad-Transformers"
%%%

当由一叠单子转换器组合出一个单子时，必须注意单子转换器分层的顺序是有意义的。
同一组转换器的不同排序会产生不同的单子。

这个版本的 {anchorName countLettersClassy}`countLetters` 与先前版本相同，只是它使用类型类来描述可用效应的集合，而不是提供一个具体的单子：

```anchor countLettersClassy
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
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
状态单子转换器和异常单子转换器可以按两种不同的顺序组合，每种顺序都会得到一个具有这两个类型类实例的单子：

```anchor SomeMonads
abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)
```

当在不会使程序抛出异常的输入上运行时，这两个单子会产生相似的结果：
```anchor countLettersM1Ok
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countLettersM2Ok
#eval countLetters (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
然而，这些返回值之间存在一个细微差别。
在 {anchorName M1eval}`M1` 的情形中，最外层的构造子是 {anchorName MonadExceptT}`Except.ok`，其中包含一个由 unit 构造子与最终状态组成的对。
在 {anchorName M2eval}`M2` 的情形中，最外层的构造子是这个对，其中包含只应用于 unit 构造子的 {anchorName MonadExceptT}`Except.ok`。
最终状态位于 {anchorName MonadExceptT}`Except.ok` 之外。
在两种情形中，程序都返回元音和辅音的计数。

另一方面，当字符串导致抛出异常时，只有一个单子会给出元音和辅音的计数。
使用 {anchorName M1eval}`M1` 时，只返回一个异常值：
```anchor countLettersM1Error
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM1Error
Except.error (StEx.Err.notALetter '!')
```
使用 {anchorName SomeMonads}`M2` 时，异常值会与抛出异常时的状态配对：
```anchor countLettersM2Error
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM2Error
(Except.error (StEx.Err.notALetter '!'), { vowels := 2, consonants := 3 })
```

可能会很容易认为 {anchorName SomeMonads}`M2` 优于 {anchorName SomeMonads}`M1`，因为它提供了更多在调试时可能有用的信息。
同一个程序在 {anchorName SomeMonads}`M1` 中计算出的答案可能与在 {anchorName SomeMonads}`M2` 中计算出的答案_不同_，而且没有原则性的理由说其中一个答案必然比另一个更好。
这可以通过给程序添加一个处理异常的步骤来看出：

```anchor countWithFallback
def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"
```
这个程序总是成功，但它可能以不同的结果成功。
如果没有抛出异常，那么结果与 {anchorName countWithFallback}`countLetters` 相同：
```anchor countWithFallbackM1Ok
#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countWithFallbackM2Ok
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
然而，如果异常被抛出并被捕获，那么最终状态就会非常不同。
对于 {anchorName countWithFallbackM1Error}`M1`，最终状态只包含来自 {anchorTerm countWithFallback}`"Fallback"` 的字母计数：
```anchor countWithFallbackM1Error
#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Error
Except.ok ((), { vowels := 2, consonants := 6 })
```
使用 {anchorName countWithFallbackM2Error}`M2` 时，最终状态包含来自 {anchorTerm countWithFallbackM2Error}`"hello!"` 和 {anchorTerm countWithFallback}`"Fallback"` 的字母计数，正如在命令式语言中所预期的那样：
```anchor countWithFallbackM2Error
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Error
(Except.ok (), { vowels := 4, consonants := 9 })
```

在 {anchorName countWithFallbackM1Error}`M1` 中，抛出异常会将状态“回滚”到捕获该异常的位置。
在 {anchorName countLettersM2Error}`M2` 中，对状态的修改会在异常的抛出与捕获之间保持下来。
通过展开 {anchorName SomeMonads}`M1` 和 {anchorName SomeMonads}`M2` 的定义，可以看到这一差异。
{anchorTerm M1eval}`M1 α` 展开为 {anchorTerm M1eval}`LetterCounts → Except Err (α × LetterCounts)`，而 {anchorTerm M2eval}`M2 α` 展开为 {anchorTerm M2eval}`LetterCounts → Except Err α × LetterCounts`。
也就是说，{anchorTerm M1eval}`M1 α` 描述的是这样的函数：它们接受一个初始字母计数，并返回一个错误，或者返回一个与更新后的计数配对的 {anchorName M1eval}`α`。
当在 {anchorName M1eval}`M1` 中抛出异常时，不存在最终状态。
{anchorTerm M2eval}`M2 α` 描述的是这样的函数：它们接受一个初始字母计数，并返回一个新的字母计数，该计数与一个错误或一个 {anchorName M2eval}`α` 配对。
当在 {anchorName M2eval}`M2` 中抛出异常时，它会伴随一个状态。

# 可交换的单子
%%%
tag := "commuting-monads"
file := "Commuting-Monads"
%%%

在函数式编程的术语中，如果两个单子转换器可以重新排序而不改变程序的含义，则称它们_可交换_。
当 {anchorName SomeMonads}`StateT` 和 {anchorName SomeMonads}`ExceptT` 重新排序时，程序结果可能不同这一事实意味着，状态与异常并不可交换。
一般而言，不应期望单子转换器可交换。

尽管并非所有单子转换器都可交换，但有些可以。
例如，{anchorName SomeMonads}`StateT` 的两次使用可以重新排序。
展开 {anchorTerm StateTDoubleA}`StateT σ (StateT σ' Id) α` 中的定义会得到类型 {anchorTerm StateTDoubleA}`σ → σ' → ((α × σ) × σ')`，而 {anchorTerm StateTDoubleB}`StateT σ' (StateT σ Id) α` 会得到 {anchorTerm StateTDoubleB}`σ' → σ → ((α × σ') × σ)`。
换言之，它们之间的差异在于：它们在返回类型的不同位置嵌套 {anchorName StateTDoubleA}`σ` 和 {anchorName StateTDoubleA}`σ'` 类型，并且以不同的顺序接受其参数。
任何客户端代码仍然需要提供相同的输入，并且仍然会接收相同的输出。

大多数同时具有可变状态和异常的编程语言都像 {anchorName SomeMonads}`M2` 那样工作。
在这些语言中，当异常被抛出时_应当_回滚的状态很难表达，并且通常需要以一种非常类似于在 {anchorName SomeMonads}`M1` 中传递显式状态值的方式来模拟。
单子转换器赋予了选择效应顺序解释的自由，使其适合手头的问题，而且两种选择在编程时同样容易。
然而，它们也要求在选择转换器的顺序时格外谨慎。
强大的表达能力伴随着检查所表达内容是否符合意图的责任，而 {anchorName countWithFallback}`countWithFallback` 的类型签名可能比它应有的更加多态。


# 练习
%%%
tag := "monad-transformer-order-exercises"
file := "Exercises"
%%%

 * 通过展开 {anchorName m}`ReaderT` 和 {anchorName SomeMonads}`StateT` 的定义，并对所得类型进行推理，检查它们是否可交换。
 * {anchorName m}`ReaderT` 和 {anchorName SomeMonads}`ExceptT` 可交换吗？通过展开它们的定义并对所得类型进行推理来检查你的答案。
 * 基于 {anchorName Many (module:=Examples.Monads.Many)}`Many` 的定义构造一个单子转换器 {lit}`ManyT`，并给出合适的 {anchorName AlternativeOptionT}`Alternative` 实例。检查它满足 {anchorName AlternativeOptionT}`Monad` 约定。
 * {lit}`ManyT` 与 {anchorName SomeMonads}`StateT` 可交换吗？如果可以，请通过展开定义并推理所得类型来检验你的答案。如果不可以，请分别编写一个 {lit}`ManyT (StateT σ Id)` 中的程序和一个 {lit}`StateT σ (ManyT Id)` 中的程序。每个程序都应当是对于给定的单子转换器排序更为合理的程序。
