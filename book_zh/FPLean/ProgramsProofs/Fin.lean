import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Fin"

#doc (Manual) "安全数组索引" =>
%%%
tag := "Fin"
%%%

{anchorName sundries}`Array` 和 {anchorName sundries}`Nat` 的 {anchorTerm sundries}`GetElem` 实例需要证明提供的 {anchorName sundries}`Nat` 小于数组。
在实践中，这些证明通常最终会连同索引一起传递给函数。
与其分别传递索引和证明，可以使用名为 {anchorName Fin}`Fin` 的类型将索引和证明捆绑到单个值中。
这可以使代码更易阅。

类型 {anchorTerm sundries}`Fin n` 表示严格小于 {anchorName sundries}`n` 的数字。
换句话说，{anchorTerm sundries}`Fin 3` 描述 {anchorTerm sundries}`0`、{anchorTerm sundries}`1` 和 {anchorTerm sundries}`2`，而 {anchorTerm sundries}`Fin 0` 没有任何值。
{anchorName Fin}`Fin` 的定义类似于 {anchorName sundries}`Subtype`，因为 {anchorTerm sundries}`Fin n` 是一个包含 {anchorName Fin}`Nat` 和小于 {anchorName sundries}`n` 的证明的结构体：

```anchor Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
```

Lean 包含 {anchorName sundries}`ToString` 和 {anchorName sundries}`OfNat` 的实例，允许将 {anchorName Fin}`Fin` 值方便地用作数字。
换句话说，{anchorTerm fiveFinEight}`#eval (5 : Fin 8)` 的输出为 {anchorInfo fiveFinEight}`5`，而非类似 {lit}`{val := 5, isLt := _}` 的值。

当提供的数字大于边界时，{anchorName Fin}`Fin` 的 {anchorName sundries}`OfNat` 实例不会失败，而是返回一个对边界取模的值。
这意味着 {anchorTerm finOverflow}`#eval (45 : Fin 10)` 的结果是 {anchorInfo finOverflow}`5`，而非编译时错误。

在返回类型中，将 {anchorName Fin}`Fin` 作为找到的索引返回，能够让它与其所在的数据结构的连接更加清晰。
{ref "proving-termination"}[上一节]中的 {anchorName ArrayFind}`Array.find` 返回一个索引，调用者不能立即使用它来执行数组查找，因为有关其有效性的信息已丢失。
更具体类型的值可以直接使用，而不会使程序变得复杂得多：

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
```

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0
```

# 练习
%%%
tag := "Fin-exercises"
%%%

编写一个函数 {anchorTerm exercise}`Fin.next? : Fin n → Option (Fin n)` 当 {anchorName nextThreeFin}`Fin` 在边界内时返回下一个最大的 {anchorName nextThreeFin}`Fin`，否则返回 {anchorName ArrayFindHelper}`none`。
检查
```anchor nextThreeFin
#eval (3 : Fin 8).next?
```
输出
```anchorInfo nextThreeFin
some 4
```
并且
```anchor nextSevenFin
#eval (7 : Fin 8).next?
```
输出
```anchorInfo nextSevenFin
none
```
