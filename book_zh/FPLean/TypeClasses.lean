import VersoManual
import FPLean.Examples

import FPLean.TypeClasses.Pos
import FPLean.TypeClasses.Polymorphism
import FPLean.TypeClasses.OutParams
import FPLean.TypeClasses.Indexing
import FPLean.TypeClasses.Coercions
import FPLean.TypeClasses.Conveniences
import FPLean.TypeClasses.StandardClasses
import FPLean.TypeClasses.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "重载与类型类" =>
%%%
tag := "type-classes"
file := "Overloading-and-Type-Classes"
%%%

在许多语言中，内建数据类型会得到特殊处理。
例如，在 C 和 Java 中，{lit}`+` 可用于相加 {c}`float` 和 {c}`int`，但不能用于相加来自第三方库的任意精度数。
类似地，数值字面量可以直接用于内建类型，但不能用于用户定义的数值类型。
其他语言为运算符提供一种 {deftech}_重载_ 机制，其中同一个运算符可以被赋予针对新类型的含义。
在这些语言中，例如 C++ 和 C#，种类繁多的内建运算符都可以被重载，而编译器使用类型检查器来选择某个特定实现。

除了数值字面量和运算符之外，许多语言还允许函数或方法的重载。
在 C++、Java、C# 和 Kotlin 中，允许一个方法有多个实现，它们具有不同数量和类型的参数。
编译器使用参数的数量及其类型来确定所意图的是哪一个重载。

函数和运算符重载有一个关键限制：多态函数不能将其类型参数限制为那些存在给定重载的类型。
例如，某个重载方法可能为字符串、字节数组和文件指针定义，但却无法编写一个适用于其中任意一种类型的第二个方法。
因此，这第二个方法本身必须针对原方法具有重载的每一种类型分别重载，从而产生许多样板定义，而不是一个单一的多态定义。
这一限制的另一个后果是，某些运算符（例如 Java 中的相等性）最终会为_每一种_参数组合定义，即使这样做未必合理。
如果程序员不非常谨慎，这可能导致程序在运行时崩溃，或悄无声息地计算出错误结果。

Lean 使用一种称为{deftech}_类型类_的机制来实现重载；该机制由 Haskell 开创，允许以一种能与多态良好配合的方式对运算符、函数和字面量进行重载。
类型类描述了一组可重载的操作。
要为一个新类型重载这些操作，需要创建一个_实例_，其中包含针对该新类型的每个操作的实现。
例如，一个名为 {anchorName chapterIntro}`Add` 的类型类描述了允许加法的类型，而 {anchorTerm chapterIntro}`Add` 针对 {anchorTerm chapterIntro}`Nat` 的一个实例则提供了针对 {anchorTerm chapterIntro}`Nat` 的加法实现。

术语 _class_ 和 _instance_ 对于习惯面向对象语言的人来说可能令人困惑，因为它们与面向对象语言中的类和实例并没有密切关系。
不过，它们确实有共同的根源：在日常语言中，“class”一词指共享某些共同属性的群体。
虽然面向对象编程中的类当然描述了具有共同属性的对象群体，但该术语还额外指一种编程语言中用于描述此类群体的特定机制。
类型类也是一种描述共享共同属性的类型的手段（也就是某些操作的实现），但除此之外，它们实际上与面向对象编程中的类没有什么共同之处。

Lean 的类型类更类似于 Java 或 C# 的 _interface_。
类型类和接口都描述一组概念上相关的操作，这些操作为某个类型或一组类型而实现。
类似地，类型类的一个实例类似于 Java 或 C# 类中由其所实现接口规定的代码，而不是 Java 或 C# 类的一个对象实例。
不同于 Java 或 C# 的接口，即使类型作者无法访问某个类型类，也可以为该类型赋予该类型类的实例。
在这一点上，它们与 Rust trait 非常相似。

{include 1 FPLean.TypeClasses.Pos}

{include 1 FPLean.TypeClasses.Polymorphism}

{include 1 FPLean.TypeClasses.OutParams}

{include 1 FPLean.TypeClasses.Indexing}

{include 1 FPLean.TypeClasses.StandardClasses}

{include 1 FPLean.TypeClasses.Coercions}

{include 1 FPLean.TypeClasses.Conveniences}

{include 1 FPLean.TypeClasses.Summary}
