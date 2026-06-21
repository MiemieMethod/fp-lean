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


#doc (Manual) "初识 Lean" =>
%%%
tag := "getting-to-know"
file := "Getting-to-Know-Lean"
%%%

按照传统，介绍一种编程语言时，应当编译并运行一个在控制台上显示 {moduleTerm}`"Hello, world!"` 的程序。
这个简单程序确保该语言的工具链已正确安装，并且程序员能够运行编译后的代码。

然而，自 20 世纪 70 年代以来，编程已经发生了变化。
如今，编译器通常集成到文本编辑器中，编程环境会在程序编写过程中提供反馈。
Lean 也不例外：它实现了 Language Server Protocol 的扩展版本，使其能够与文本编辑器通信，并在用户输入时提供反馈。

像 Python、Haskell 和 JavaScript 这样各不相同的语言都提供读取-求值-打印循环（REPL），也称为交互式顶层或浏览器控制台，用户可以在其中输入表达式或语句。
随后，语言会计算并显示用户输入的结果。
另一方面，Lean 将这些功能集成到与编辑器的交互中，提供一些命令，使文本编辑器能够显示直接集成在程序文本自身中的反馈。
本章简要介绍如何在编辑器中与 Lean 交互，而 {ref "hello-world"}[Hello, World!] 则描述如何以批处理模式从命令行按传统方式使用 Lean。

阅读本书时，最好在编辑器中打开 Lean，跟随内容并输入每一个示例。请尝试改动这些
示例，看看会发生什么！

{include 1 FPLean.GettingToKnow.Evaluating}

{include 1 FPLean.GettingToKnow.Types}

{include 1 FPLean.GettingToKnow.FunctionsDefinitions}

{include 1 FPLean.GettingToKnow.Structures}

{include 1 FPLean.GettingToKnow.DatatypesPatterns}

{include 1 FPLean.GettingToKnow.Polymorphism}

{include 1 FPLean.GettingToKnow.Conveniences}

{include 1 FPLean.GettingToKnow.Summary}
