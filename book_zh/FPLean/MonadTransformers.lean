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
%%%
file := "Monad-Transformers"
%%%

单子是在纯语言中编码某些副作用集合的一种方式。
不同的单子提供不同的效果，例如状态和错误处理。
许多单子甚至提供大多数语言中没有的有用效果，例如非确定性搜索、读取器，甚至续延。

典型应用程序具有一组核心函数，这些函数不使用单子编写，因而易于测试；同时还配有一个外层包装器，该包装器使用单子来编码必要的应用程序逻辑。
这些单子由众所周知的组件构造而成。
例如：
 * 可变状态用一个函数参数和一个返回值来编码，二者具有相同的类型
 * 错误处理通过使用类似于 {moduleName}`Except` 的返回类型来编码，其中包含表示成功和失败的构造子
 * 日志记录通过将返回值与日志配对来编码

然而，手工编写每个单子十分繁琐，其中涉及各种类型类的样板式定义。
这些组成部分中的每一个也都可以抽取为一个定义，用来修改某个其他单子以添加额外的效应。
这样的定义称为_单子转换器_。
一个具体的单子可以由一组单子转换器构建而成，这使得代码复用大为增加。

{include 1 FPLean.MonadTransformers.ReaderIO}

{include 1 FPLean.MonadTransformers.Transformers}

{include 1 FPLean.MonadTransformers.Order}

{include 1 FPLean.MonadTransformers.Do}

{include 1 FPLean.MonadTransformers.Conveniences}

{include 1 FPLean.MonadTransformers.Summary}
