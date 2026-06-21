import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes"

#doc (Manual) "索引族" =>
%%%
tag := "indexed-families"
file := "Indexed-Families"
%%%

多态归纳类型接受类型实参。
例如，{moduleName}`List` 接受一个实参，用来决定列表中元素的类型；{moduleName}`Except` 接受若干实参，用来决定异常或值的类型。
这些类型实参在该数据类型的每个构造子中都相同，称为_参数_。

然而，归纳类型的实参并不一定要在每个构造子中都相同。
若某个归纳类型的类型实参会随所选构造子而变化，则称这样的归纳类型为_索引族_；其中会变化的实参称为_索引_。
索引族的“hello world”示例是一种列表类型：除元素类型之外，它的类型还包含列表长度；按惯例，这类列表称为“向量”：

```anchor Vect
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
```

由三个 {anchorName vect3}`String` 组成的向量的类型包含这样一个事实：它含有三个 {anchorName vect3}`String`：

```anchor vect3
example : Vect String 3 :=
  .cons "one" (.cons "two" (.cons "three" .nil))
```


函数声明可以在冒号之前接受一些参数，表示它们在整个定义中可用；也可以在冒号之后接受一些参数，表示希望对它们进行模式匹配，并逐情况定义函数。
归纳数据类型有类似的原则：实参 {anchorName Vect}`α` 在数据类型声明的顶部、冒号之前命名，这表示它是一个参数，在定义中所有出现 {anchorName Vect}`Vect` 的地方都必须作为第一个实参提供；而 {anchorName Vect}`Nat` 实参出现在冒号之后，表示它是一个可以变化的索引。
事实上，在 {anchorName Vect}`nil` 和 {anchorName Vect}`cons` 构造子声明中，{anchorName Vect}`Vect` 的三次出现都一致地将 {anchorName Vect}`α` 作为第一个实参，而第二个实参在每种情况下都不同。



{anchorName Vect}`nil` 的声明说明它是类型 {anchorTerm Vect}`Vect α 0` 的构造子。
这意味着，在期望 {anchorTerm nilNotLengthThree}`Vect String 3` 的语境中使用 {anchorName nilNotLengthThree}`Vect.nil` 是类型错误，正如在期望 {anchorTerm otherEx}`List String` 的语境中 {anchorTerm otherEx}`[1, 2, 3]` 是类型错误一样：
```anchor nilNotLengthThree
example : Vect String 3 := Vect.nil
```
```anchorError nilNotLengthThree
Type mismatch
  Vect.nil
has type
  Vect ?m.3 0
but is expected to have type
  Vect String 3
```
在此例中，{anchorTerm Vect}`0` 与 {anchorTerm nilNotLengthThree}`3` 之间的不匹配所起的作用，与任何其他类型不匹配完全相同，尽管 {anchorTerm Vect}`0` 和 {anchorTerm nilNotLengthThree}`3` 本身并不是类型。
消息中的元变量可以忽略，因为它的存在表明 {anchorName otherEx}`Vect.nil` 可以具有任意元素类型。

索引族称为类型的_族_，是因为不同的索引值会使不同的构造子可供使用。
在某种意义上，索引族并不是一个类型；更确切地说，它是一组相关类型，而索引值的选择同时也从这组类型中选择了一个类型。
为 {anchorName Vect}`Vect` 选择索引 {anchorTerm otherEx}`5` 意味着只有构造子 {anchorName Vect}`cons` 可用，而选择索引 {anchorTerm Vect}`0` 意味着只有 {anchorName Vect}`nil` 可用。

如果索引尚未知晓（例如因为它是一个变量），那么在索引变得已知之前，不能使用任何构造子。
将 {anchorName nilNotLengthN}`n` 用作长度时，{anchorName otherEx}`Vect.nil` 和 {anchorName consNotLengthN}`Vect.cons` 都不能使用，因为无法知道变量 {anchorName nilNotLengthN}`n` 应当表示与 {anchorTerm Vect}`0` 匹配的 {anchorName Vect}`Nat`，还是表示 {anchorTerm Vect}`n + 1`：
```anchor nilNotLengthN
example : Vect String n := Vect.nil
```
```anchorError nilNotLengthN
Type mismatch
  Vect.nil
has type
  Vect ?m.2 0
but is expected to have type
  Vect String n
```
```anchor consNotLengthN
example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
```
```anchorError consNotLengthN
Type mismatch
  Vect.cons "Hello" (Vect.cons "world" Vect.nil)
has type
  Vect String (0 + 1 + 1)
but is expected to have type
  Vect String n
```

将列表长度作为其类型的一部分，意味着该类型会包含更多信息。
例如，{anchorName replicateStart}`Vect.replicate` 是一个函数，它用某个给定值的若干个副本创建一个 {anchorName replicateStart}`Vect`。
精确表达这一点的类型是：
```anchor replicateStart
def Vect.replicate (n : Nat) (x : α) : Vect α n := _
```
实参 {anchorName replicateStart}`n` 作为结果的长度出现。
与下划线占位符相关联的消息描述了当前任务：
```anchorError replicateStart
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α n
```

使用索引族时，只有当 Lean 能看出构造子的索引与期望类型中的索引相匹配时，才能应用构造子。
然而，没有任何一个构造子的索引与 {anchorName replicateStart}`n` 匹配——{anchorName Vect}`nil` 与 {anchorName otherEx}`Nat.zero` 匹配，{anchorName Vect}`cons` 与 {anchorName otherEx}`Nat.succ` 匹配。
正如前面的类型错误示例一样，变量 {anchorName Vect}`n` 可以表示二者中的任意一个，这取决于把哪个 {anchorName Vect}`Nat` 作为实参提供给函数。
解决方法是使用模式匹配来分别考虑这两种可能情况：
```anchor replicateMatchOne
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => _
  | k + 1 => _
```
因为 {anchorName replicateStart}`n` 出现在期望类型中，对 {anchorName replicateStart}`n` 进行模式匹配会在 match 的两个分支中_细化_期望类型。
在第一个下划线处，期望类型已经变为 {lit}`Vect α 0`：
```anchorError replicateMatchOne
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α 0
```
在第二个下划线处，它已经变为 {lit}`Vect α (k + 1)`：
```anchorError replicateMatchTwo
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)
```
当模式匹配除了发现某个值的结构之外，还会细化程序的类型时，它称为_依值模式匹配_。

经过细化的类型使得应用构造子成为可能。
第一个下划线匹配 {anchorName otherEx}`Vect.nil`，第二个下划线匹配 {anchorName consNotLengthN}`Vect.cons`：
```anchor replicateMatchFour
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons _ _
```
{anchorName replicateMatchFour}`.cons` 下方的第一个下划线应当具有类型 {anchorName replicateMatchFour}`α`。
有一个 {anchorName replicateMatchFour}`α` 可用，即 {anchorName replicateMatchFour}`x`：
```anchorError replicateMatchFour
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ α
```
第二个下划线应当是一个 {lit}`Vect α k`，它可以通过对 {anchorName replicate}`replicate` 的递归调用产生：
```anchorError replicateMatchFive
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α k
```
下面是 {anchorName replicate}`replicate` 的最终定义：

```anchor replicate
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
```

除了在编写函数时提供帮助之外，{anchorName replicate}`Vect.replicate` 这种信息量更大的类型还允许客户端代码在不阅读源代码的情况下排除许多意外函数。
列表版本的 {anchorName listReplicate}`replicate` 可能产生长度错误的列表：

```anchor listReplicate
def List.replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: x :: replicate k x
```
然而，在 {anchorName replicateOops}`Vect.replicate` 中犯这个错误会导致类型错误：
```anchor replicateOops
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (.cons x (replicate k x))
```
```anchorError replicateOops
Application type mismatch: The argument
  cons x (replicate k x)
has type
  Vect α (k + 1)
but is expected to have type
  Vect α k
in the application
  cons x (cons x (replicate k x))
```


函数 {anchorName otherEx}`List.zip` 将两个列表组合起来：把第一个列表中的第一个元素与第二个列表中的第一个元素配对，把第一个列表中的第二个元素与第二个列表中的第二个元素配对，依此类推。
{anchorName otherEx}`List.zip` 可用于把美国俄勒冈州最高的三座山峰与丹麦最高的三座山峰配对：
```anchorTerm zip1
["Mount Hood",
 "Mount Jefferson",
 "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
```
结果是一个由三个序对组成的列表：
```anchorTerm zip1
[("Mount Hood", "Møllehøj"),
 ("Mount Jefferson", "Yding Skovhøj"),
 ("South Sister", "Ejer Bavnehøj")]
```
当两个列表长度不同时，应当发生什么并不十分明确。
与许多语言一样，Lean 选择忽略其中一个列表中多出的元素。
例如，将俄勒冈州最高的五座山峰的高度与丹麦最高的三座山峰的高度组合，会得到三个序对。
特别地，
```anchorTerm zip2
[3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]
```
求值为
```anchorTerm zip2
[(3428.8, 170.86), (3201, 170.77), (3158.5, 170.35)]
```

这种做法很方便，因为它总能返回一个答案；但当列表并非有意地具有不同长度时，它有丢弃数据的风险。
F# 采用另一种做法：它的 {fsharp}`List.zip` 版本会在长度不匹配时抛出异常，如下面这个 {lit}`fsi` 会话所示：
```fsharp
> List.zip [3428.8; 3201.0; 3158.5; 3075.0; 3064.0] [170.86; 170.77; 170.35];;
```
```fsharpError
System.ArgumentException: The lists had different lengths.
list2 is 2 elements shorter than list1 (Parameter 'list2')
   at Microsoft.FSharp.Core.DetailedExceptions.invalidArgDifferentListLength[?](String arg1, String arg2, Int32 diff) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 24
   at Microsoft.FSharp.Primitives.Basics.List.zipToFreshConsTail[a,b](FSharpList`1 cons, FSharpList`1 xs1, FSharpList`1 xs2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 918
   at Microsoft.FSharp.Primitives.Basics.List.zip[T1,T2](FSharpList`1 xs1, FSharpList`1 xs2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 929
   at Microsoft.FSharp.Collections.ListModule.Zip[T1,T2](FSharpList`1 list1, FSharpList`1 list2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/list.fs:line 466
   at <StartupCode$FSI_0006>.$FSI_0006.main@()
Stopped due to error
```
这避免了意外丢弃信息，但程序崩溃也有其自身的困难。
Lean 中的等价做法会使用 {anchorName otherEx}`Option` 或 {anchorName otherEx}`Except` 单子，但这会引入一种负担，而这种安全性未必值得付出该代价。

:::paragraph
然而，使用 {anchorName Vect}`Vect` 可以写出一个 {anchorName VectZip}`zip` 版本，其类型要求两个实参具有相同长度：

```anchor VectZip
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
```

这个定义只为两种情况提供了模式：两个实参同为 {anchorName otherEx}`Vect.nil`，或两个实参同为 {anchorName consNotLengthN}`Vect.cons`；Lean 接受了该定义，而没有给出像 {anchorName otherEx}`List` 的类似定义会产生的“缺少情况”错误：
```anchor zipMissing
def List.zip : List α → List β → List (α × β)
  | [], [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
```
```anchorError zipMissing
Missing cases:
(List.cons _ _), []
[], (List.cons _ _)
```
:::

这是因为第一个模式中使用的构造子 {anchorName Vect}`nil` 或 {anchorName Vect}`cons` 会_细化_类型检查器关于长度 {anchorName VectZip}`n` 的知识。
当第一个模式是 {anchorName Vect}`nil` 时，类型检查器还可以判定长度是 {anchorTerm VectZipLen}`0`，因此第二个模式唯一可能的选择是 {anchorName Vect}`nil`。
类似地，当第一个模式是 {anchorName Vect}`cons` 时，类型检查器可以判定长度是某个 {anchorName VectZipLen}`Nat` {anchorName VectZipLen}`k` 的 {anchorTerm VectZipLen}`k+1`，因此第二个模式唯一可能的选择是 {anchorName Vect}`cons`。
事实上，添加一个同时使用 {anchorName Vect}`nil` 和 {anchorName Vect}`cons` 的分支会导致类型错误，因为长度不匹配：
```anchor zipExtraCons
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .nil, .cons y ys => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
```
```anchorError zipExtraCons
Type mismatch
  Vect.cons y ys
has type
  Vect ?m.10 (?m.16 + 1)
but is expected to have type
  Vect β 0
```
通过将 {anchorName VectZipLen}`n` 变成显式实参，可以观察到对长度的细化：

```anchor VectZipLen
def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)
```

# 练习
%%%
tag := "indexed-families-exercises"
file := "Exercises"
%%%


形成使用依值类型编程的直觉需要经验，本节练习非常重要。
对每个练习，都应在编写代码的过程中通过实验观察类型检查器能够捕获哪些错误，以及不能捕获哪些错误。
这也是培养理解错误消息直觉的好方法。

 * 复核 {anchorName VectZip}`Vect.zip` 在组合俄勒冈州最高的三座山峰与丹麦最高的三座山峰时是否给出了正确答案。
由于 {anchorName Vect}`Vect` 没有 {anchorName otherEx}`List` 所具有的语法糖，先定义 {anchorTerm exerciseDefs}`oregonianPeaks : Vect String 3` 和 {anchorTerm exerciseDefs}`danishPeaks : Vect String 3` 可能会有帮助。

 * 定义一个具有类型 {anchorTerm exerciseDefs}`(α → β) → Vect α n → Vect β n` 的函数 {anchorName exerciseDefs}`Vect.map`。

 * 定义一个函数 {anchorName exerciseDefs}`Vect.zipWith`，它用一个函数逐个组合 {anchorName Vect}`Vect` 中的元素。
它应当具有类型 {anchorTerm exerciseDefs}`(α → β → γ) → Vect α n → Vect β n → Vect γ n`。

 * 定义一个函数 {anchorName exerciseDefs}`Vect.unzip`，它将由序对构成的 {anchorName Vect}`Vect` 拆分为一对 {anchorName Vect}`Vect`。它应当具有类型 {anchorTerm exerciseDefs}`Vect (α × β) n → Vect α n × Vect β n`。

 * 定义一个函数 {anchorName exerciseDefs}`Vect.push`，它向 {anchorName Vect}`Vect` 的_末尾_添加一个元素。其类型应当是 {anchorTerm exerciseDefs}`Vect α n → α → Vect α (n + 1)`，并且 {anchorTerm snocSnowy}`#eval Vect.push (.cons "snowy" .nil) "peaks"` 应当产生 {anchorInfo snocSnowy}`Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))`。

 * 定义一个函数 {anchorName exerciseDefs}`Vect.reverse`，它反转 {anchorName Vect}`Vect` 的顺序。

 * 定义一个具有如下类型的函数 {anchorName exerciseDefs}`Vect.drop`：{anchorTerm exerciseDefs}`(n : Nat) → Vect α (k + n) → Vect α k`。
通过检查 {anchorTerm ejerBavnehoej}`#eval danishPeaks.drop 2` 是否产生 {anchorInfo ejerBavnehoej}`Vect.cons "Ejer Bavnehøj" (Vect.nil)` 来验证它能正常工作。

 * 定义一个具有类型 {anchorTerm take}`(n : Nat) → Vect α (k + n) → Vect α n` 的函数 {anchorName take}`Vect.take`，它返回 {anchorName Vect}`Vect` 中前 {anchorName take}`n` 个元素。用一个示例检查它能正常工作。
