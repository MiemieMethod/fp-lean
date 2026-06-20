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

本章是关于编程的。程序不仅需要计算出正确的结果，还需要高效地执行。为了编写高效的功能程序，了解如何适当地使用数据结构，以及如何考虑运行程序所需的时间和空间非常重要。

本章也是关于证明的。在 Lean 中进行高效编程最重要的数据结构体之一是数组，但安全使用数组需要证明数组索引在边界内。此外，大多数有趣的数组算法并不遵循结构化递归模式。相反，它们会遍历数组。虽然这些算法会停机，但 Lean 不一定能够自动检查这一点。证明可以用来展示程序为什么会停机。

重写程序使其运行得更快通常会导致代码更难理解。证明还可以表明两个程序始终会计算出相同的答案，即使它们使用不同的算法或实现技术。通过这种方式，缓慢、直白的程序可以作为快速、复杂版本的规范。

将证明和编程相结合，可以使程序既安全又高效。证明允许省略运行时边界检查，它们使许多测试变得不必要，并且它们在不引入任何运行时性能开销的情况下为程序提供了极高的置信度。然而，证明程序的定理可能是耗时且昂贵的，因此其他工具通常更经济。

交互式定理证明是一个深刻的话题。本章仅提供一个示例，面向在 Lean 中编程时出现的证明。大多数有趣的定理与编程没有密切关系。请参阅 {ref "next-steps"}[继续学习] 以获取更多学习资源的列表。然而，就像学习编程一样，在学习编写证明时，没有什么是可以替代实践经验的——是时候开始了！

{include 1 FPLean.ProgramsProofs.TailRecursion}

{include 1 FPLean.ProgramsProofs.TailRecursionProofs}

{include 1 FPLean.ProgramsProofs.ArraysTermination}

{include 1 FPLean.ProgramsProofs.Inequalities}

{include 1 FPLean.ProgramsProofs.Fin}

{include 1 FPLean.ProgramsProofs.InsertionSort}

{include 1 FPLean.ProgramsProofs.SpecialTypes}

{include 1 FPLean.ProgramsProofs.Summary}
