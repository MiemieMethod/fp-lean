import VersoManual
import FPLean.Examples

import FPLean.HelloWorld.RunningAProgram
import FPLean.HelloWorld.StepByStep
import FPLean.HelloWorld.StartingAProject
import FPLean.HelloWorld.Cat
import FPLean.HelloWorld.Conveniences
import FPLean.HelloWorld.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean


#doc (Manual) "Hello, World!" =>
%%%
tag := "hello-world"
file := "Hello___-World___"
%%%

虽然 Lean 被设计为具有丰富的交互式环境，使程序员能够在不离开自己喜爱的文本编辑器范围的情况下，从语言获得大量反馈，但它也是一种可以编写真实程序的语言。
这意味着它也具有批处理模式编译器、构建系统、包管理器，以及编写程序所必需的所有其他工具。

虽然{ref "getting-to-know"}[上一章]介绍了 Lean 中函数式编程的基础，本章则说明如何启动一个编程项目、编译它，并运行其结果。
运行并与其环境交互的程序（例如，通过从标准输入读取输入或创建文件）难以同将计算理解为数学表达式求值的观点相协调。
除了对 Lean 构建工具的描述之外，本章还提供了一种思考与外部世界交互的函数式程序的方式。

{include 1 FPLean.HelloWorld.RunningAProgram}

{include 1 FPLean.HelloWorld.StepByStep}

{include 1 FPLean.HelloWorld.StartingAProject}

{include 1 FPLean.HelloWorld.Cat}

{include 1 FPLean.HelloWorld.Conveniences}

{include 1 FPLean.HelloWorld.Summary}
