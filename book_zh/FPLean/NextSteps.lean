import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

#doc (Manual) "后续学习" =>
%%%
tag := "next-steps"
htmlSplit := .never
file := "Next-Steps"
%%%

本书介绍了 Lean 中函数式编程的最基础内容，其中包括少量交互式定理证明。
使用像 Lean 这样的依值类型函数式语言是一个深刻的主题，可谈之处甚多。
根据你的兴趣，以下资源可能有助于学习 Lean 4。

# 学习 Lean
%%%
tag := "learning-lean"
file := "Learning-Lean"
%%%

Lean 4 本身在以下资源中有所介绍：

 * [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) 是一篇关于使用 Lean 编写证明的教程。
 * [The Lean 4 Manual](https://lean-lang.org/doc/reference/latest/) 对该语言及其特性作了详细说明。
 * [How To Prove It With Lean](https://djvelleman.github.io/HTPIwL/) 是备受推崇的教材 [_How To Prove It_](https://www.cambridge.org/highereducation/books/how-to-prove-it/6D2965D625C6836CD4A785A2C843B3DA) 的基于 Lean 的配套读物，后者介绍如何书写纸笔数学证明。
 * [Metaprogramming in Lean 4](https://github.com/arthurpaulino/lean4-metaprogramming-book) 概述了 Lean 的扩展机制，范围从中缀运算符和记号，到宏、自定义策略，以及完整的自定义嵌入式语言。
 * [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) 对喜欢递归笑话的读者来说可能会很有趣。

然而，继续学习 Lean 的最佳方式是开始阅读和编写代码，并在遇到困难时查阅文档。
此外，[Lean Zulip](https://leanprover.zulipchat.com/) 是结识其他 Lean 用户、寻求帮助以及帮助他人的绝佳场所。

# Lean 中的数学
%%%
tag := none
file := "Mathematics-in-Lean"
%%%

[社区网站](https://leanprover-community.github.io/learn.html) 上提供了大量面向数学家的学习资源。

# 在计算机科学中使用依值类型
%%%
tag := none
file := "Using-Dependent-Types-in-Computer-Science"
%%%

Rocq 是一种与 Lean 有许多共同之处的语言。
对于计算机科学家而言，[Software Foundations](https://softwarefoundations.cis.upenn.edu/) 这一交互式教材系列为 Rocq 在计算机科学中的应用提供了极好的入门介绍。
Lean 和 Rocq 的基本思想非常相似，并且技能可以很容易地在这两个系统之间迁移。

# 依值类型编程
%%%
tag := none
file := "Programming-with-Dependent-Types"
%%%

对于有兴趣学习使用索引族和依值类型来组织程序的程序员，Edwin Brady 的 [_Type Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris) 提供了极好的入门介绍。
与 Rocq 一样，Idris 是 Lean 的近亲，尽管它缺少策略。

# 理解依值类型
%%%
tag := none
file := "Understanding-Dependent-Types"
%%%

[_The Little Typer_](https://thelittletyper.com/) 是一本面向程序员的书：这些程序员尚未正式学习过逻辑或程序设计语言理论，但希望理解依值类型论的核心思想。
尽管上述所有资源都力求尽可能实用，_The Little Typer_ 则呈现了一种依值类型论的入门路径：只使用来自编程的概念，从零开始构建最基础的内容。
声明：_Functional Programming in Lean_ 的作者也是 _The Little Typer_ 的作者之一。
