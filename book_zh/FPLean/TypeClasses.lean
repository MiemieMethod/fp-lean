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
%%%

在许多语言中，内置数据类型有特殊的优待。例如，在 C 和 Java 中，{lit}`+` 可以被用于 {c}`float` 和 {c}`int`，但不能用于其他第三方库的数字。类似地，数字字面量可以被直接用于内置类型，但是不能用于用户定义的数字类型。其他语言为运算符提供 {deftech}*重载（overloading）* 机制，使得同一个运算符可以在新的类型有意义。在这些语言中，比如 C++ 和 C#，多种内置运算符都可以被重载，编译器使用类型检查来选择一个特定的实现。

除了数字字面量和运算符，许多语言还可以重载函数或方法。
在 C++，Java，C# 和 Kotlin 中，对于不同的数字和类型参数，一个方法可以有多种实现。
编译器使用参数的数字和它们的类型来决定使用哪个重载。

函数和运算符的重载有一个关键的受限之处：多态函数无法限定它们的类型参数为重载存在的那些类型。
例如，一个重载方法可能在字符串，字节数组和文件指针上有定义，但是没有任何方法能写第二个方法能在任意这些类型上适用。
如果想这样做的话，这第二个方法必须本身也为每一个类型都有一个原始方法的重载，最终产生许多繁琐的定义而不是一个简单的多态定义。
这种限制的另一个后果是一些运算符（例如 Java 中的等号）对 *每一个* 参数组合都要有定义，即使这样做是完全没必要的。
如果程序员没有很谨慎的话，这可能会导致程序在运行时崩溃，或者静静地计算出错误的结果。

Lean 用 {deftech}*类型类（type classes）* 机制（源于 Haskell）来实现重载。
这使得运算符，函数和字面量重载与多态有一个很好的配合。
一个类型类描述了一族可重载的运算符。
要将这些运算符重载到新的类型上，你需要创建一个包含对新类型的每一个运算的实现方式的 *实例（instance）* 。
例如，类型类 {anchorName chapterIntro}`Add` 描述了可加的类型，一个对 {anchorTerm chapterIntro}`Nat` 类型的 {anchorTerm chapterIntro}`Add` 实例提供了 {anchorTerm chapterIntro}`Nat` 上加法的实现。

*类* 和 *实例* 这两个词可能会使面向对象程序员感到混淆，因为 Lean 中的它们与面向对象语言中的类和实例关系不大。
然而，它们有相同的基本性质：在日常语言中，“类”这个词指的是具有某些共同属性的组。
虽然面向对象编程中的类确实描述了具有共同属性的对象组，但该术语还指代描述此类对象组的特定编程语言机制。
类型类也是描述共享共同属性的类型（即某些操作的实现）的一种方式，但它们与面向对象编程中的类并没有其他共同点。

Lean 的类型类更像是 Java 或 C# 中的 *接口（interface）*。
类型类和接口都描述了在概念上有联系的运算的集合，这些运算为一个类型或一个类型集合实现。
类似地，类型类的实例也很像 Java 或 C# 中描述实现了的接口的类，而不是 Java 或 C# 中类的实例。
不像 Java 或 C# 的接口，对于一个类型，该类型的作者并不能访问的类型类也可以给这个类型实例。
从这种意义上讲，这和 Rust 的 traits 很像。

{include 1 FPLean.TypeClasses.Pos}

{include 1 FPLean.TypeClasses.Polymorphism}

{include 1 FPLean.TypeClasses.OutParams}

{include 1 FPLean.TypeClasses.Indexing}

{include 1 FPLean.TypeClasses.StandardClasses}

{include 1 FPLean.TypeClasses.Coercions}

{include 1 FPLean.TypeClasses.Conveniences}

{include 1 FPLean.TypeClasses.Summary}
