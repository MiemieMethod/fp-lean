import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Do"

#doc (Manual) "单子的 {kw}`do`-记法" =>
%%%
tag := "monad-do-notation"
file := "do-Notation-for-Monads"
%%%

尽管基于单子的 API 非常强大，但显式地将 {lit}`>>=` 与匿名函数一起使用仍然有些繁琐。
正如使用中缀运算符来代替对 {anchorName names}`HAdd.hAdd` 的显式调用一样，Lean 为单子提供了一种称为 _{kw}`do`-记法_ 的语法，可以使使用单子的程序更易读写。
这正是在 {anchorName names}`IO` 中编写程序所用的同一种 {kw}`do`-记法，而 {anchorName names}`IO` 也是一个单子。

在 {ref "hello-world"}[Hello, World!] 中，{kw}`do` 语法用于组合 {anchorName names}`IO` 动作，但这些程序的含义是直接解释的。
理解如何用单子进行编程，意味着现在可以根据 {kw}`do` 如何翻译为对底层单子运算符的使用来解释它。

当 {kw}`do` 中唯一的语句是单个表达式 {anchorName doSugar1a}`E` 时，会使用 {kw}`do` 的第一种翻译。
在这种情况下，{kw}`do` 会被移除，因此
```anchor doSugar1a
do E
```
翻译为
```anchor doSugar1b
E
```

当 {kw}`do` 的第一条语句是带箭头并绑定局部变量的 {kw}`let` 时，使用第二种翻译。
这会被翻译为对 {lit}`>>=` 的使用，并配以一个绑定同一变量的函数，因此
```anchor doSugar2a
 do let x ← E₁
    Stmt
    …
    Eₙ
```
翻译为
```anchor doSugar2b
E₁ >>= fun x =>
  do Stmt
     …
     Eₙ
```

当 {kw}`do` 块的第一条语句是一个表达式时，它被认为是一个返回 {anchorName names}`Unit` 的单子动作，因此该函数匹配 {anchorName names}`Unit` 构造子并且
```anchor doSugar3a
  do E₁
     Stmt
     …
     Eₙ
```
翻译为
```anchor doSugar3b
E₁ >>= fun () =>
  do Stmt
     …
     Eₙ
```

最后，当 {kw}`do` 块中的第一条语句是一个使用 {lit}`:=` 的 {kw}`let` 时，翻译后的形式是普通的 let 表达式，因此
```anchor doSugar4a
do let x := E₁
   Stmt
   …
   Eₙ
```
翻译为
```anchor doSugar4b
let x := E₁
do Stmt
   …
   Eₙ
```

:::paragraph
使用 {anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`Monad` 类的 {anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`firstThirdFifthSeventh` 定义如下：

```anchor firstThirdFifthSeventhMonad (module := Examples.Monads.Class)
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
使用 {kw}`do`-记法后，它会显著更易读：
```anchor firstThirdFifthSeventhDo
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)
```
:::

:::paragraph
在没有 {anchorName mapM}`Monad` 类型类时，为树的节点编号的函数 {anchorName numberMonadicish (module := Examples.Monads)}`number` 写作：

```anchor numberMonadicish (module := Examples.Monads)
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
有了 {anchorName mapM}`Monad` 和 {kw}`do`，它的定义就简洁得多：

```anchor numberDo
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← get
      set (n + 1)
      let numberedRight ← helper right
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
:::

将 {kw}`do` 与 {anchorName names}`IO` 一起使用时的所有便利，也都可在将它用于其他单子时获得。
例如，嵌套动作也适用于任意单子。
{anchorName mapM (module:=Examples.Monads.Class)}`mapM` 的原始定义是：

```anchor mapM (module := Examples.Monads.Class)
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
使用 {kw}`do` 记法，它可以写作：

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)
```
使用嵌套动作使它几乎与原来的非单子式 {anchorName names}`map` 一样简短：

```anchor mapMNested
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))
```
使用嵌套动作，{anchorName numberDoShort}`number` 可以写得简洁得多：

```anchor numberDoShort
def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure
        (BinTree.branch
          (← helper left)
          ((← increment), x)
          (← helper right))
  (helper t 0).snd
```



# 练习
%%%
tag := "monad-do-notation-exercises"
file := "Exercises"
%%%

 * 使用 {kw}`do` 记法重写 {anchorName evaluateM (module:=Examples.Monads.Class)}`evaluateM`、它的辅助函数以及各种具体用例，而不是显式调用 {lit}`>>=`。
 * 使用嵌套动作重写 {anchorName firstThirdFifthSeventhDo}`firstThirdFifthSeventh`。
