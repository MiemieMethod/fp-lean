import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Fin"

#doc (Manual) "有界数" =>
%%%
tag := "Fin"
file := "Bounded-Numbers"
%%%

{anchorName sundries}`Array` 和 {anchorName sundries}`Nat` 的 {anchorTerm sundries}`GetElem` 实例要求有一个证明，证明所提供的 {anchorName sundries}`Nat` 小于数组的长度。
在实践中，这些证明常常会与索引一起传递给函数。
与其分别传递一个索引和一个证明，不如使用名为 {anchorName Fin}`Fin` 的类型，将索引和证明捆绑成一个单一的值。
这可以使代码更易读。

类型 {anchorTerm sundries}`Fin n` 表示严格小于 {anchorName sundries}`n` 的数。
换言之，{anchorTerm sundries}`Fin 3` 描述 {anchorTerm sundries}`0`、{anchorTerm sundries}`1` 和 {anchorTerm sundries}`2`，而 {anchorTerm sundries}`Fin 0` 根本没有值。
{anchorName Fin}`Fin` 的定义类似于 {anchorName sundries}`Subtype`，因为 {anchorTerm sundries}`Fin n` 是一个包含 {anchorName Fin}`Nat` 以及它小于 {anchorName sundries}`n` 的证明的结构：

```anchor Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
```

Lean 包含 {anchorName sundries}`ToString` 和 {anchorName sundries}`OfNat` 的实例，使得 {anchorName Fin}`Fin` 值可以方便地作为数来使用。
换言之，{anchorTerm fiveFinEight}`#eval (5 : Fin 8)` 的输出是 {anchorInfo fiveFinEight}`5`，而不是类似 {lit}`{val := 5, isLt := _}` 的东西。

当给定的数大于界限时，{anchorName Fin}`Fin` 的 {anchorName sundries}`OfNat` 实例并不失败，而是返回该数对界限取模后的值。
这意味着 {anchorTerm finOverflow}`#eval (45 : Fin 10)` 的结果是 {anchorInfo finOverflow}`5`，而不是编译时错误。

在返回类型中，将一个 {anchorName Fin}`Fin` 作为找到的索引返回，会使它与其所在数据结构之间的联系更加清楚。
{ref "proving-termination"}[上一节]中的 {anchorName ArrayFind}`Array.find` 返回的索引，调用者不能立即用来在数组中执行查找，因为关于其有效性的信息已经丢失。
更具体的类型会产生一个可以使用的值，而不会使程序显著复杂化：

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
file := "Exercise"
%%%

编写一个函数 {anchorTerm exercise}`Fin.next? : Fin n → Option (Fin n)`：当下一个更大的 {anchorName nextThreeFin}`Fin` 仍在界内时返回它，否则返回 {anchorName ArrayFindHelper}`none`。
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
