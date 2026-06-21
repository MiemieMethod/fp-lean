import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"


set_option pp.rawOnError true

#doc (Manual) "小结" =>
%%%
tag :="type-classes-summary"
file := "Summary"
%%%

# 类型类与重载
%%%
tag := none
file := "Type-Classes-and-Overloading"
%%%

类型类是 Lean 用于重载函数和运算符的机制。
多态函数可以用于多个类型，但无论用于哪种类型，它的行为方式都相同。
例如，一个将两个列表追加起来的多态函数可以使用，而不论列表中元素的类型是什么；但它不能根据所遇到的具体类型而表现出不同的行为。
另一方面，使用类型类重载的操作也可以用于多个类型。
然而，每个类型都需要其自身对该重载操作的实现。
这意味着行为可以根据所提供的类型而变化。

一个_类型类_具有名称、参数，以及由若干带类型的名称组成的主体。
名称用于指称这些重载操作，参数决定定义中的哪些方面可以被重载，而主体则提供可重载操作的名称和类型签名。
每个可重载操作称为该类型类的一个 {deftech}_方法_。
类型类可以用其他方法来提供某些方法的默认实现，从而在不需要时免除实现者手工定义每个重载的负担。

类型类的一个 {deftech}_实例_ 为给定参数提供各方法的实现。
实例可以是多态的，在这种情况下它们可以适用于多种参数；并且在某个特定类型存在更高效版本的情况下，它们还可以选择性地为默认方法提供更具体的实现。

类型类参数要么是 {deftech}_输入参数_（默认情况），要么是 {deftech}_输出参数_（由 {moduleName}`outParam` 修饰符指示）。
在所有输入参数都不再是元变量之前，Lean 不会开始搜索实例；而输出参数可以在搜索实例的过程中被求解。
类型类的参数不必是类型——它们也可以是普通值。
用于重载自然数字面量的 {moduleName}`OfNat` 类型类，将被重载的 {moduleName}`Nat` 本身作为一个参数，这使得实例能够限制允许的数字。

实例可以标记为 {anchorTerm defaultAdd}`@[default_instance]` 属性。
当一个实例是默认实例时，如果 Lean 由于类型中存在元变量而本来无法找到实例，那么它将作为后备选择被选中。

# 用于常见语法的类型类
%%%
tag := none
file := "Type-Classes-for-Common-Syntax"
%%%

Lean 中的大多数中缀运算符都是用类型类来重写的。
例如，加法运算符对应于一个名为 {moduleName}`Add` 的类型类。
这些运算符中的大多数都有相应的异质版本，其中两个参数不必具有相同的类型。
这些异质运算符使用该类的一个版本来重载，其名称以 {lit}`H` 开头，例如 {moduleName}`HAdd`。

索引语法通过一个名为 {moduleName}`GetElem` 的类型类来重载，该类型类涉及证明。
{moduleName}`GetElem` 有两个输出参数，分别是要从集合中提取的元素的类型，以及一个可用于判定什么算作索引值在集合边界内的证据的函数。
这种证据由一个命题描述，并且在使用数组索引时，Lean 会尝试证明这个命题。
当 Lean 无法在编译时检查列表或数组访问操作是否在边界内时，可以通过在索引语法后追加一个 {lit}`?`，将该检查推迟到运行时。

# 函子
%%%
tag := none
file := "Functors"
%%%


函子是一种支持映射操作的多态类型。
这种映射操作“就地”变换所有元素，而不改变任何其他结构。
例如，列表是函子，并且映射操作既不能丢弃、复制，也不能打乱列表中的条目。

虽然函子是通过具有 {anchorName FunctorDef}`map` 来定义的，但 Lean 中的 {anchorName FunctorDef}`Functor` 类型类包含一个额外的默认方法，该方法负责将常量函数映射到一个值上，用同一个新值替换所有其类型由多态类型变量给出的值。
对于某些函子，这可以比遍历整个结构更高效地完成。

# 派生实例
%%%
tag := none
file := "Deriving-Instances"
%%%


许多类型类都有非常标准的实现。
例如，布尔相等类 {moduleName}`BEq` 通常通过先检查两个参数是否由同一个构造子构造，再检查它们的所有参数是否相等来实现。
这些类的实例可以被_自动_创建。

在定义归纳类型或结构时，声明末尾的 {kw}`deriving` 子句会使实例被自动创建。
此外，可以在数据类型的定义之外使用 {kw}`deriving instance`﻿{lit}` ... `﻿{kw}`for`﻿{lit}` ...` 命令，以使实例被生成。
由于每一个可派生其实例的类都需要特殊处理，并非所有类都是可派生的。

# 强制类型转换
%%%
tag := none
file := "Coercions"
%%%


强制类型转换允许 Lean 通过插入一次函数调用，从通常会成为编译期错误的情况中恢复；该函数调用把数据从一种类型变换为另一种类型。
例如，从任意类型 {anchorName CoeOption}`α` 到类型 {anchorTerm CoeOption}`Option α` 的强制类型转换允许直接书写值，而不必使用 {anchorName CoeOption}`some` 构造子，从而使 {anchorName CoeOption}`Option` 的工作方式更像面向对象语言中的可空类型。

强制类型转换有多种。
它们可以从不同种类的错误中恢复，并且由各自的类型类表示。
{anchorName CoeOption}`Coe` 类用于从类型错误中恢复。
当 Lean 在需要类型为 {anchorName Coe}`β` 的某个对象的上下文中得到一个类型为 {anchorName Coe}`α` 的表达式时，Lean 首先尝试串联起一条强制类型转换链，将 {anchorName Coe}`α` 转换为 {anchorName Coe}`β`，只有在无法做到这一点时才显示错误。
{moduleName}`CoeDep` 类将正在被强制转换的具体值作为额外参数，从而允许对该值进行进一步的类型类搜索，或者允许在实例中使用构造子来限制转换的作用范围。
{moduleName}`CoeFun` 类会拦截在编译函数应用时本来会出现的“不是函数”错误，并且在可能时允许将函数位置上的值转换为真正的函数。
