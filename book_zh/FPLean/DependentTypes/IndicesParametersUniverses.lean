import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.IndicesParameters"

#doc (Manual) "索引、参量和宇宙层级" =>
%%%
tag := "indices-parameters-universe-levels"
%%%

归纳类型的参量和索引的区别不仅仅是这些参数在构造子之间相同还是不同。
当确定宇宙层级之间的关系时，归纳类型参数是参量还是索引也很重要：
归纳类型的宇宙层级可以与参量相同，但必须比其索引更大。
这种限制是为了确保 Lean 除了作为编程语言还可以作为定理证明器——否则，Lean 的逻辑将是不一致的。
我们将通过展示不同例子输出的错误信息来阐释决定以下两者的具体规则：宇宙层级和某个参数应该被视为参量还是索引。

通常来说，在归纳类型定义中出现在冒号之前的被当作参量，出现在冒号之后的被当作索引。
参量像函数参数可以给出类型和名字，而索引只能给出类型。
如 {anchorName Vect (module := Examples.DependentTypes)}`Vect` 的定义所示：

```anchor Vect (module := Examples.DependentTypes)
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
```
在这个定义中，{anchorName Vect (module:=Examples.DependentTypes)}`α` 是一个参量，{anchorName Vect (module:=Examples.DependentTypes)}`Nat` 是一个索引。
参量可以在整个定义中被使用（例如，{anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons` 使用 {anchorName Vect (module:=Examples.DependentTypes)}`α` 作为其第一个参数的类型），但它们必须始终一致。
因为索引可能会不同，所以它们在每个构造子中被分配单独的值，而不是作为参数出现在数据类型的顶部的定义中。


一个非常简单的带有参量的数据类型是 {anchorName WithParameter}`WithParameter`：

```anchor WithParameter
inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α
```
宇宙层级 {anchorTerm WithParameter}`u` 可以用于参量和归纳类型本身，说明参量不会增加数据类型的宇宙层级。
同样，当有多个参量时，归纳类型的宇宙层级取决于这些参量的宇宙层级中最大的那个：

```anchor WithTwoParameters
inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β
```
由于参量不会增加数据类型的宇宙层级，使用它们很方便。
Lean 会尝试识别像索引一样出现在冒号之后，但像参量一样使用的参数，并将它们转换为参量：
以下两个归纳数据类型的参量都出现在冒号之后：

```anchor WithParameterAfterColon
inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α
```

```anchor WithParameterAfterColon2
inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α
```

当一个参量在数据类型的声明中没有命名时，可以在每个构造子中使用不同的名称，只要它们的使用是一致的。
以下声明被接受：

```anchor WithParameterAfterColonDifferentNames
inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β
```
然而，当参量的命名被指定时，这种灵活性就不被允许了：
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
类似的，尝试命名一个索引会导致错误：
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

使用适当的宇宙层级并将索引放在冒号之后会导致一个可接受的声明：

```anchor WithIndex
inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)
```


虽然 Lean 有时（即，在确定一个参数在所有构造子中的使用一致时）可以确定冒号后的参数是一个参量，但所有参量仍然需要出现在所有索引之前。
试图在索引之后放置一个参量会导致该参量被视为一个索引，进而导致数据类型的宇宙层级必须增加：
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

参量不必是类型。这个例子显示了普通数据类型，如 {anchorName NatParamFour}`Nat` 也可以被用作参量：
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
按照错误信息的提示改成 {anchorName NatParam}`n` 会导致声明被接受：

```anchor NatParam
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5
```




从以上结果中可以总结出什么？
参量和索引的规则如下：
 1. 参量在每个构造子的类型中的使用方式必须相同。
 2. 所有参量必须在所有索引之前。
 3. 正在定义的数据类型的宇宙层级必须至少与最大的参量宇宙层级一样大，并严格大于最大的索引宇宙层级。
 4. 冒号前写的命名参数始终是参量，而冒号后的参数通常是索引。如果 Lean 发现冒号后的参数在所有构造子中使用一致且不在任何索引之后，则可能能够将这个参数视为参量。

当不确定时，可以使用 Lean 命令 {kw}`#print` 来检查数据类型参数中的多少是参量。
例如，对于 {anchorTerm printVect}`Vect`，它指出参量的数量是 1：
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

在选择数据类型的参数顺序时，应当考虑哪些参数应该是参量，哪些应该是索引。
尽可能多地将参数作为参量有助于保持一个可控的宇宙层级，从而使复杂的程序的类型检查更容易进行。
一种可能方法是确保参数列表中所有参量出现在所有索引之前。

同时，尽管 Lean 有时可以确定冒号后的参数仍然是参量，但最好使用显式命名编写参量。
这使读者清晰的明白意图，并且 Lean 在这个参量在构造子之间有不一致的使用时会报告错误。
