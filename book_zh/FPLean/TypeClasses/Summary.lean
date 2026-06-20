import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"


set_option pp.rawOnError true

#doc (Manual) "总结" =>
%%%
tag :="type-classes-summary"
%%%

# 类型类和重载
%%%
tag := none
%%%

类型类是 Lean 重载函数和运算符的机制。一个多态函数可以用于多种类型，但是不管是什么类型，它的行为都是一致的。例如，一个连接两个列表的多态函数在使用时不关心列表中元素的类型，但它也不可能根据具体的元素类型有不一样的行为。另一方面，一个用类型类重载的运算符，也可以用在多种类型上。然而，每个类型都需要自己的重载运算实现。这意味着可以根据不同的类型有不同的行为。

一个 *类型类* 有名称，参数，和一个包含了名称和类型的类体。名字是一种代指重载运算符的方式，参数决定了哪些方面的定义可以被重载，类体提供了可重载运算的名称和类型签名。每一个可重载运算都被称为类型类的一个 {deftech}*方法*。类型类可能会提供一些方法的默认实现，使得程序员从手动实现每个重载（只要实现可以被自动完成）中解放出来。

一个类型类的 {deftech}*实例*为给定参数提供方法的实现。实例可能是多态的，这种情况下它能接受多种参数，同时也可能在对于一些类型存在更高效的实现时提供更具体实现。

类型类参数要么是一个{deftech}*输入参数*（input parameters）（默认情况下），或者是一个 {deftech}*输出参数*（通过 {moduleName}`outParam` 修饰）。在所有输出参数变为已知前，Lean 不会开始实例搜索。输出参数会在实例搜索过程中给出。类型类的参数不一定要是一个类型，它也可以是一个常规值。{moduleName}`OfNat` 类型类被用于重载自然数字面量，接受要被重载的 {moduleName}`Nat` 本身作为参数，这可以使实例限制允许的数字。

实例可能会被标注为 {anchorTerm defaultAdd}`@[default_instance]` 属性。当一个实例是默认实例时，那么就会作为 Lean 因存在元变量而无法找到实例的回退。

# 常用语法的类型类
%%%
tag := none
%%%

Lean 中多数中缀运算符都是用类型类来重载的。例如，加法对应于 {moduleName}`Add` 类型类。多数运算符都有与之对应的异质运算，该运算的两个参数不需要是同一种类型。这些异质运算符使用前面加个 {lit}`H` 的类型类来重载，比如 {moduleName}`HAdd`。

索引语法使用 {moduleName}`GetElem` 类型类来重载，该类型类包含证明。{moduleName}`GetElem` 有两个输出参数，一个是要被从中提取出的元素的类型，另一个是用来证明索引值未越界的函数。这个证明是用命题来描述的，Lean 会在索引时尝试证明这个命题。当 Lean 在编译时不能检查列表或元组索引是否越界时，可以通过为索引操作添加 {lit}`?` 来让检查发生在运行时。

# 函子
%%%
tag := none
%%%


一个函子是一个支持映射运算的泛型。这个映射运算“在原地”映射所有的元素，不会改变其他结构。例如，列表是函子，所以列表上的映射不会删除，复制或混合列表中的元素。

如果定义了 {anchorName FunctorDef}`map`，那么这个类型就是一个函子。Lean 中的 {anchorName FunctorDef}`Functor` 类型类还包含了额外的默认方法，这些方法可以将映射常数函数到值，替换所有类型是由多态变量给出的值为一个相同的新值。对于一些函子，这比转换整个结构更高效。

# 派生实例
%%%
tag := none
%%%


许多类型类都有非常标准的实现。例如，布尔等价类型类 {moduleName}`BEq` 经常被实现为先检查参数是否有一样的构造器，然后检查他们的值是否相等。这些类型类的实例可以 *自动* 创建。

在定义归纳类型或结构时，声明末尾的 {kw}`deriving` 子句将导致自动创建实例。
此外，可以在数据类型定义之外使用 {kw}`deriving instance`﻿{lit}` ... `﻿{kw}`for`﻿{lit}` ...` 命令来生成实例。
因为可以为其派生实例的每个类都需要特殊处理，所以并非所有类都是可派生的。

# 强制类型转换
%%%
tag := none
%%%


强制转换允许 Lean 向一个正常来说应该出现编译错误的地方插入一个函数调用，该调用将转换数据的类型，从而从错误中恢复。例如，一个从任意类型 {anchorName CoeOption}`α` 到类型 {anchorTerm CoeOption}`Option α` 的强制转换使得值可以直接写出，而不是被包裹在 {anchorName CoeOption}`some` 构造子中。这样 {anchorName CoeOption}`Option` 就像是有空值类型的语言中的空值那样。

有许多不同的强制转换。他们可以从不同的错误类型中恢复，他们都是用自己的类型类来描述的。{anchorName CoeOption}`Coe` 类型类用于从类型错误中恢复。当 Lean 有一个 {anchorName Coe}`α` 类型的表达式，但却希望这里是一个 {anchorName Coe}`β` 类型时，Lean 会首先尝试串起一个能将 {anchorName Coe}`α` 强制转换为 {anchorName Coe}`β` 的链，仅当它无法这么做的时候才会报错。{moduleName}`CoeDep` 类将被强制转换的具体值作为额外参数，这样可以对该值进行进一步的类型类搜索，或者在实例中使用构造函数来限制转换的范围。{moduleName}`CoeFun` 类在编译函数应用时会拦截“不是函数”的错误，并允许将函数位置的值转换为实际函数（如果可能的话）。
