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
%%%

虽然 Lean 被设计为一个丰富的交互式环境，程序员无需离开他们最喜欢的文本编辑器，
就能从语言中获得相当多的反馈，但它同时也是一门可以编写现实程序的语言。
这意味着它还具有批量编译器、构建系统、包管理器以及编写程序所需的一切工具。

{ref "getting-to-know"}[上一章]介绍了 Lean 函数式编程的基础知识，本章将解释如何开始一个编程项目、编译它并运行出结果。运行并与环境交互的程序（例如通过读取标准输入或创建文件）很难和将计算理解为数学表达式的求值相协调。除了介绍 Lean 构建工具之外，本章还提供了一种思考函数式程序与世界如何交互的方法。

{include 1 FPLean.HelloWorld.RunningAProgram}

{include 1 FPLean.HelloWorld.StepByStep}

{include 1 FPLean.HelloWorld.StartingAProject}

{include 1 FPLean.HelloWorld.Cat}

{include 1 FPLean.HelloWorld.Conveniences}

{include 1 FPLean.HelloWorld.Summary}
