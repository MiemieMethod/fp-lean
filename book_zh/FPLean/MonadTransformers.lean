import VersoManual

import FPLean.Examples

import FPLean.MonadTransformers.ReaderIO
import FPLean.MonadTransformers.Transformers
import FPLean.MonadTransformers.Order
import FPLean.MonadTransformers.Do
import FPLean.MonadTransformers.Conveniences
import FPLean.MonadTransformers.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "单子转换器" =>

单子是在纯语言中编码某一类副作用的方式。
不同的单子提供不同的作用，例如状态和错误处理。
许多单子甚至提供了大多数语言中没有的有用作用，例如非确定性搜索、读取器，甚至延续。

典型的应用程序通常包含一组易于测试、且不使用单子的核心函数，并在外层配以一个包装层；该包装层使用单子来编码必要的应用逻辑。
这些单子由一些众所周知的组件构造而成。
例如：
 * 可变状态通过一个函数参数以及一个同类型返回值来编码
 * 错误处理通过类似 {moduleName}`Except` 的返回类型来编码，其中包含表示成功和失败的构造子
 * 日志记录通过把返回值与日志配对来编码

然而，手动编写每个单子是繁琐的，需要定义各种类型类的样板代码。每个组件也都可以提取到一个定义中，该定义修改某个其他单子以添加额外的作用。这种定义称为*单子转换器*（Monad Transformer）。一个具体的单子可以从一组单子转换器构建，从而实现更多代码的重用。

{include 1 FPLean.MonadTransformers.ReaderIO}

{include 1 FPLean.MonadTransformers.Transformers}

{include 1 FPLean.MonadTransformers.Order}

{include 1 FPLean.MonadTransformers.Do}

{include 1 FPLean.MonadTransformers.Conveniences}

{include 1 FPLean.MonadTransformers.Summary}
