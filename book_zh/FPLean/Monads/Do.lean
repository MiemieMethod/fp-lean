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
%%%

基于单子的 API 非常强大，但显式使用 {lit}`>>=` 和匿名函数仍然有些繁琐。
正如使用中缀运算符代替显式调用 {anchorName names}`HAdd.hAdd` 一样，Lean 提供了一种称为 *{kw}`do`-记法* 的单子语法，它可以使使用单子的程序更易于阅读和编写。
这与用于编写 {anchorName names}`IO` 程序的 {kw}`do`-记法完全相同，而 {anchorName names}`IO` 也是一个单子。

在 {ref "hello-world"}[Hello, World!] 中，{kw}`do` 语法用于组合 {anchorName names}`IO` 活动，但这些程序的含义是直接解释的。理解如何运用单子进行编程意味着现在可以用 {kw}`do` 来解释它如何转换为对底层单子运算符的使用。

当 {kw}`do` 中的唯一语句是单个表达式 {anchorName doSugar1a}`E` 时，会使用 {kw}`do` 的第一种翻译。
在这种情况下，{kw}`do` 被删除，因此
```anchor doSugar1a
do E
```
会被翻译为
```anchor doSugar1b
E
```

当 {kw}`do` 的第一个语句是带有箭头的 {kw}`let` 绑定一个局部变量时，则使用第二种翻译。
它会翻译为使用 {lit}`>>=` 以及绑定同一变量的函数，因此
```anchor doSugar2a
 do let x ← E₁
    Stmt
    …
    Eₙ
```
会被翻译为
```anchor doSugar2b
E₁ >>= fun x =>
  do Stmt
     …
     Eₙ
```

当 {kw}`do` 块的第一个语句是一个表达式时，它会被认为是一个返回 {anchorName names}`Unit` 的单子操作，因此该函数匹配 {anchorName names}`Unit` 构造子，而
```anchor doSugar3a
  do E₁
     Stmt
     …
     Eₙ
```
会被翻译为
```anchor doSugar3b
E₁ >>= fun () =>
  do Stmt
     …
     Eₙ
```

最后，当 {kw}`do` 块的第一个语句是使用 {lit}`:=` 的 {kw}`let` 时，翻译后的形式是一个普通的 let 表达式，因此
```anchor doSugar4a
do let x := E₁
   Stmt
   …
   Eₙ
```
会被翻译为
```anchor doSugar4b
let x := E₁
do Stmt
   …
   Eₙ
```

:::paragraph
使用 {anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`Monad` 类的 {anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`firstThirdFifthSeventh` 的定义如下：

```anchor firstThirdFifthSeventhMonad (module := Examples.Monads.Class)
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
使用 {kw}`do`-记法，它会变得更加易读：
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
若没有 {anchorName mapM}`Monad` 类型类，则对树的节点进行编号的函数 {anchorName numberMonadicish (module := Examples.Monads)}`number` 写作如下形式：

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
有了 {anchorName mapM}`Monad` 和 {kw}`do`，其定义就简洁多了：

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

使用 {kw}`do` 与 {anchorName names}`IO` 的所有便利性在使用其他单子时也可用。
例如，嵌套操作也适用于任何单子。{anchorName mapM (module:=Examples.Monads.Class)}`mapM` 的原始定义为：

```anchor mapM (module := Examples.Monads.Class)
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
使用 {kw}`do`-记法，可以写成：

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)
```
使用嵌套操作会让它与原始非单子 {anchorName names}`map` 一样简洁：

```anchor mapMNested
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))
```
使用嵌套操作，{anchorName numberDoShort}`number` 可以变得更加简洁：

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
%%%

 * 使用 {kw}`do`-记法而非显式调用 {lit}`>>=` 重写 {anchorName evaluateM (module:=Examples.Monads.Class)}`evaluateM`、辅助函数以及不同的特定用例。
 * 使用嵌套操作重写 {anchorName firstThirdFifthSeventhDo}`firstThirdFifthSeventh`。
