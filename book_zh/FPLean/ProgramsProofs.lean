import VersoManual
import FPLean.Examples

import FPLean.ProgramsProofs.TailRecursion
import FPLean.ProgramsProofs.TailRecursionProofs
import FPLean.ProgramsProofs.ArraysTermination
import FPLean.ProgramsProofs.Inequalities
import FPLean.ProgramsProofs.Fin
import FPLean.ProgramsProofs.InsertionSort
import FPLean.ProgramsProofs.SpecialTypes
import FPLean.ProgramsProofs.Summary


open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.TODO"

#doc (Manual) "编程、证明与性能" =>
%%%
file := "Programming___-Proving___-and-Performance"
%%%

本章讨论编程。
程序需要计算出正确的结果，但也需要高效地做到这一点。
为了编写高效的函数式程序，重要的是既要知道如何恰当地使用数据结构，也要知道如何思考运行程序所需的时间和空间。

本章也讨论证明。
在 Lean 中进行高效编程时，数组是最重要的数据结构之一，但安全地使用数组需要证明数组索引在界内。
此外，大多数有意义的数组算法并不遵循结构递归的模式；相反，它们会在数组上迭代。
尽管这些算法会终止，Lean 未必能够自动检查这一点。
证明可用于说明程序为何会终止。

为了使程序更快而改写程序，通常会得到更难理解的代码。
证明还可以表明，即使两个程序使用不同的算法或实现技术，它们也总是计算出相同的答案。
以这种方式，缓慢而直接的程序可以作为快速而复杂版本的规约。

将证明与编程相结合，可以使程序既安全又高效。
证明允许省略运行时边界检查，使许多测试变得不必要，并且在不引入任何运行时性能开销的情况下，为程序提供极高程度的可信度。
然而，证明关于程序的定理可能耗时且代价高昂，因此其他工具往往更经济。

交互式定理证明是一个深奥的主题。
本章只提供一个初步体验，侧重于在 Lean 中编程实践时会出现的证明。
大多数有趣的定理与编程并不密切相关。
如需进一步学习的资源列表，请参阅 {ref "next-steps"}[后续步骤]。
然而，正如学习编程时一样，学习写证明也没有什么能够替代亲手实践——现在该开始了！

{include 1 FPLean.ProgramsProofs.TailRecursion}

{include 1 FPLean.ProgramsProofs.TailRecursionProofs}

{include 1 FPLean.ProgramsProofs.ArraysTermination}

{include 1 FPLean.ProgramsProofs.Inequalities}

{include 1 FPLean.ProgramsProofs.Fin}

{include 1 FPLean.ProgramsProofs.InsertionSort}

{include 1 FPLean.ProgramsProofs.SpecialTypes}

{include 1 FPLean.ProgramsProofs.Summary}
