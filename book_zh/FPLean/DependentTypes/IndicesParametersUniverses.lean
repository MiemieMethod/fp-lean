import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.IndicesParameters"

#doc (Manual) "索引、参数与宇宙层级" =>
%%%
tag := "indices-parameters-universe-levels"
file := "Indices___-Parameters___-and-Universe-Levels"
%%%

归纳类型的索引与参数之间的区别，并不只是描述该类型的实参在不同构造子之间是否变化的一种方式。
在确定它们的宇宙层级之间的关系时，归纳类型的某个实参是参数还是索引同样很重要。
特别地，归纳类型可以与某个参数处于同一宇宙层级，但它必须位于比其索引更大的宇宙中。
这一限制是必要的，以确保 Lean 既能用作定理证明器，也能用作编程语言——没有这一限制，Lean 的逻辑将是不一致的。
通过实验观察错误消息，是说明这些规则以及精确决定类型实参何时是参数或索引的规则的一种好方法。

一般而言，归纳类型的定义在冒号之前接受其参数，在冒号之后接受其索引。
参数像函数实参一样被赋予名称，而索引只描述其类型。
这一点可以在 {anchorName Vect (module := Examples.DependentTypes)}`Vect` 的定义中看到：

```anchor Vect (module := Examples.DependentTypes)
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
```
在这个定义中，{anchorName Vect (module:=Examples.DependentTypes)}`α` 是一个参数，而 {anchorName Vect (module:=Examples.DependentTypes)}`Nat` 是一个索引。
参数可以在整个定义中被引用（例如，{anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons` 使用 {anchorName Vect (module:=Examples.DependentTypes)}`α` 作为其第一个实参的类型），但它们必须始终一致地使用。
由于索引预期会变化，因此它们在每个构造子处分别被赋予具体值，而不是在数据类型定义的顶部作为实参提供。


一个带参数的非常简单的数据类型是 {anchorName WithParameter}`WithParameter`：

```anchor WithParameter
inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α
```
宇宙层级 {anchorTerm WithParameter}`u` 既可用于参数，也可用于该归纳类型本身；这说明参数不会提高数据类型的宇宙层级。
类似地，当存在多个参数时，归纳类型取得其中较大的宇宙层级：

```anchor WithTwoParameters
inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β
```
由于参数不会提高数据类型的宇宙层级，使用参数可能更方便。
Lean 会尝试识别那些写法上像索引（位于冒号之后）、但用法上像参数的实参，并将它们转为参数：
下面两个归纳数据类型都把其参数写在冒号之后：

```anchor WithParameterAfterColon
inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α
```

```anchor WithParameterAfterColon2
inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α
```

当参数未在最初的数据类型声明中命名时，只要在每个构造子中一致地使用，就可以为它使用不同的名称。
下面的声明会被接受：

```anchor WithParameterAfterColonDifferentNames
inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β
```
然而，这种灵活性并不适用于显式声明其参数名称的数据类型：
```anchor WithParameterBeforeColonDifferentNames
inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
  | test1 : α → WithParameterBeforeColonDifferentNames α
  | test2 : β → WithParameterBeforeColonDifferentNames β
```
```anchorError WithParameterBeforeColonDifferentNames
Mismatched inductive type parameter in
  WithParameterBeforeColonDifferentNames β
The provided argument
  β
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
类似地，试图为索引命名会导致错误：
```anchor WithNamedIndex
inductive WithNamedIndex (α : Type u) : Type (u + 1) where
  | test1 : WithNamedIndex α
  | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
```
```anchorError WithNamedIndex
Mismatched inductive type parameter in
  WithNamedIndex (α × α)
The provided argument
  α × α
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

使用适当的宇宙层级，并将索引放在冒号之后，会得到一个可被接受的声明：

```anchor WithIndex
inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)
```


即使 Lean 有时能够根据归纳类型声明中冒号之后的某个实参在所有构造子中的一致使用，判定它是参数，所有参数仍然必须出现在所有索引之前。
试图将参数放在索引之后，会导致该实参本身被视为索引，而这将要求提高该数据类型的宇宙层级：
```anchor ParamAfterIndex
inductive ParamAfterIndex : Nat → Type u → Type u where
  | test1 : ParamAfterIndex 0 γ
  | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ
```
```anchorError ParamAfterIndex
Invalid universe level in constructor `ParamAfterIndex.test1`: Parameter `γ` has type
  Type u
at universe level
  u+2
which is not less than or equal to the inductive type's resulting universe level
  u+1
```

参数不一定是类型。
这个例子表明，像 {anchorName NatParamFour}`Nat` 这样的普通数据类型也可以用作参数：
```anchor NatParamFour
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam 4 5
```
```anchorError NatParamFour
Mismatched inductive type parameter in
  NatParam 4 5
The provided argument
  4
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
按建议使用 {anchorName NatParam}`n` 会使该声明被接受：

```anchor NatParam
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5
```




可以从这些实验中得出什么结论？
参数与索引的规则如下：
 1. 参数必须在每个构造子的类型中以完全相同的方式使用。
 2. 所有参数都必须出现在所有索引之前。
 3. 正在定义的数据类型的宇宙层级必须至少与最大的参数一样大，并且严格大于最大的索引。
 4. 写在冒号之前的具名实参始终是参数，而冒号之后的实参通常是索引。若冒号之后的实参在所有构造子中都被一致地使用，并且没有出现在任何索引之后，Lean 可能会判定这种用法使它们成为参数。

拿不准时，可以使用 Lean 命令 {kw}`#print` 来检查某个数据类型有多少个实参是参数。
例如，对于 {anchorTerm printVect}`Vect`，它指出参数数量为 1：
```anchor printVect
#print Vect
```
```anchorInfo printVect
inductive Vect.{u} : Type u → Nat → Type u
number of parameters: 1
constructors:
Vect.nil : {α : Type u} → Vect α 0
Vect.cons : {α : Type u} → {n : Nat} → α → Vect α n → Vect α (n + 1)
```

在选择数据类型实参的顺序时，值得思考哪些实参应为参数，哪些应为索引。
使尽可能多的实参成为参数有助于控制宇宙层级，这可以使复杂程序更容易通过类型检查。
使之成为可能的一种方法是确保实参列表中所有参数都出现在所有索引之前。

此外，尽管 Lean 能够根据用法判定冒号之后的实参实际上是参数，最好仍然为参数写出显式名称。
这会向读者清楚表明意图，并且当该实参在各构造子之间被误用为不一致时，会使 Lean 报告错误。
