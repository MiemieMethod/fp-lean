import VersoManual
import FPLean.Examples
import FPLean.GettingToKnow.Evaluating
import FPLean.GettingToKnow.Types
import FPLean.GettingToKnow.FunctionsDefinitions
import FPLean.GettingToKnow.Structures
import FPLean.GettingToKnow.DatatypesPatterns
import FPLean.GettingToKnow.Polymorphism
import FPLean.GettingToKnow.Conveniences
import FPLean.GettingToKnow.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Hello"


#doc (Manual) "了解 Lean" =>
%%%
tag := "getting-to-know"
%%%

按照惯例，介绍一门编程语言通常会编译并运行一个在控制台上显示「Hello, world!」的程序。这个简单的程序能确保语言工具安装正确，且程序员能够运行已编译的代码。

然而，自 20 世纪 70 年代以来，编程发生了许多变化。如今，编译器通常集成到了文本编辑器中，编程环境会在编写程序时提供反馈。
Lean 也是如此：它实现了语言服务器协议（Language Server Protocol，LSP）的扩展版本，允许它与文本编辑器通信并在用户键入时提供反馈。

Python、Haskell 和 JavaScript 等许多不同语言都提供读入-求值-打印循环（read-eval-print-loop，REPL），也称为交互式顶层或浏览器控制台；用户可以在其中输入表达式或语句。
随后，语言会计算并显示用户输入的结果。
与之不同，Lean 把这些功能整合进与编辑器的交互中，提供一些命令，使文本编辑器能够把反馈直接显示在程序文本之中。
本章简要介绍如何在编辑器中与 Lean 交互，而 {ref "hello-world"}[Hello, World!] 则说明如何以传统方式从命令行批处理模式使用 Lean。

阅读本书时，最好在编辑器中打开 Lean，一边阅读一边输入每个示例。
请尝试修改这些示例，看看会发生什么！

{include 1 FPLean.GettingToKnow.Evaluating}

{include 1 FPLean.GettingToKnow.Types}

{include 1 FPLean.GettingToKnow.FunctionsDefinitions}

{include 1 FPLean.GettingToKnow.Structures}

{include 1 FPLean.GettingToKnow.DatatypesPatterns}

{include 1 FPLean.GettingToKnow.Polymorphism}

{include 1 FPLean.GettingToKnow.Conveniences}

{include 1 FPLean.GettingToKnow.Summary}
