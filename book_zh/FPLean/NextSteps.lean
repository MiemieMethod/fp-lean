import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

#doc (Manual) "继续学习" =>
%%%
tag := "next-steps"
htmlSplit := .never
%%%

本书介绍了 Lean 中函数式编程的基本知识，包括一些互动定理证明的内容。使用依值类型的函数式语言（如 Lean）是一个深奥的主题，内容丰富。根据您的兴趣，以下资源可能对学习 Lean 4 有用。

# "学习 Lean"
%%%
tag := "learning-lean"
%%%

Lean 4 本身在以下资源中有详细描述：

继续学习 Lean 的最佳方式是开始阅读和编写代码，在遇到困难时查阅文档。此外， [Lean Zulip](https://leanprover.zulipchat.com/) 是结识其他 Lean 用户、寻求帮助和帮助他人的好地方。

# Lean 形式化数学
%%%
tag := none
%%%

数学学习资源广泛分布在 [社区网站](https://leanprover-community.github.io/learn.html) 上。

# 在计算机科学中使用依值类型
%%%
tag := none
%%%

Rocq 是一种与 Lean 有许多共同点的语言。对于计算机科学家来说，
《[软件基础](https://coq-zh.github.io/SF-zh/)》系列教材提供了一个很好的介绍，
介绍了 Rocq 在计算机科学中的应用。Lean 和 Rocq 的基本思想非常相似，
编程技巧在两个语言之间是可以相互转换的。

# 使用依值类型编程
%%%
tag := none
%%%

对有兴趣学习使用索引族和依值类型来结构化程序的程序员来说，Edwin Brady 的 [_Type Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris) 提供了一个很好的介绍。像 Rocq 一样，Idris 是 Lean 的近亲，尽管它缺乏策略。

# 理解依值类型
%%%
tag := none
%%%

[_The Little Typer_](https://thelittletyper.com/) 是一本为没有正式学习过逻辑或编程语言理论，但希望理解依值类型论核心思想的程序员准备的书。虽然上述所有资源都旨在实现尽可能的实用，但这本书通过从头开始构建基础，使用仅来自编程的概念来呈现依值类型理论的方法。
