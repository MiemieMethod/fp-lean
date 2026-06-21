import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "结构" =>
%%%
tag := "structures"
file := "Structures"
%%%

编写程序的第一步通常是识别问题领域中的概念，然后在代码中为它们找到合适的表示。
有时，一个领域概念是其他更简单概念的集合。
在这种情况下，将这些较简单的组成部分组合到一个单一的“包”中，并为其赋予一个有意义的名称，会很方便。
在 Lean 中，这是通过_结构_完成的；它们类似于 C 或 Rust 中的 {c}`struct`，以及 C# 中的 {CSharp}`record`。

定义一个结构会向 Lean 引入一个全新的类型，该类型不能被化简为任何其他类型。
这很有用，因为多个结构可能表示不同的概念，尽管它们包含相同的数据。
例如，一个点可以用笛卡尔坐标或极坐标表示，二者各自都是一对浮点数。
定义不同的结构可以防止 API 客户端将二者混淆。

Lean 的浮点数类型称为 {anchorName zeroFloat}`Float`，浮点数按通常记法书写。

```anchorTerm onePointTwo
#check 1.2
```


```anchorInfo onePointTwo
1.2 : Float
```


```anchorTerm negativeLots
#check -454.2123215
```


```anchorInfo negativeLots
-454.2123215 : Float
```


```anchorTerm zeroPointZero
#check 0.0
```


```anchorInfo zeroPointZero
0.0 : Float
```

当浮点数以带小数点的形式书写时，Lean 会推断其类型为 {anchorName zeroFloat}`Float`。如果书写时不带小数点，则可能需要类型标注。

```anchorTerm zeroNat
#check 0
```


```anchorInfo zeroNat
0 : Nat
```



```anchorTerm zeroFloat
#check (0 : Float)
```


```anchorInfo zeroFloat
0 : Float
```



笛卡尔点是一个具有两个 {anchorName zeroFloat}`Float` 字段的结构，字段名为 {anchorName Point}`x` 和 {anchorName Point}`y`。
这是使用 {kw}`structure` 关键字声明的。


```anchor Point
structure Point where
  x : Float
  y : Float
```

在此声明之后，{anchorName Point}`Point` 是一个新的结构类型。
创建结构类型的值的典型方式是在花括号内为其所有字段提供值。
笛卡尔平面的原点是 {anchorName Point}`x` 和 {anchorName Point}`y` 都为零的位置：

```anchor origin
def origin : Point := { x := 0.0, y := 0.0 }
```

{anchorTerm originEval}`#eval origin` 的结果看起来非常像 {anchorName origin}`origin` 的定义。

```anchorInfo originEval
{ x := 0.000000, y := 0.000000 }
```


由于结构的作用是将一组数据“捆绑”起来，为其命名并将其作为一个单元来处理，因此能够提取结构的各个字段同样重要。
这可以使用点记法完成，如同在 C、Python、Rust 或 JavaScript 中那样。

```anchorTerm originx
#eval origin.x
```

```anchorInfo originx
0.000000
```


```anchorTerm originy
#eval origin.y
```

```anchorInfo originy
0.000000
```

:::paragraph
这可用于定义以结构作为参数的函数。
例如，点的加法通过将其底层坐标值相加来执行。
应当有

```anchorTerm addPointsEx
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
```

得到

```anchorInfo addPointsEx
{ x := -6.500000, y := 32.200000 }
```
:::

该函数本身接受两个 {anchorName Point}`Point` 作为实参，名为 {anchorName addPoints}`p1` 和 {anchorName addPoints}`p2`。
所得的点基于 {anchorName addPoints}`p1` 和 {anchorName addPoints}`p2` 二者的 {anchorName addPoints}`x` 与 {anchorName addPoints}`y` 字段：

```anchor addPoints
def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
```


类似地，两点之间的距离，即它们的 {anchorName Point}`x` 和 {anchorName Point}`y` 分量之差的平方和的平方根，可以写作：

```anchor distance
def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
```

例如，$`(1, 2)` 与 $`(5, -1)` 之间的距离是 $`5`：

```anchorTerm evalDistance
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
```

```anchorInfo evalDistance
5.000000
```



多个结构可以具有同名字段。
三维点数据类型可以共享字段 {anchorName Point3D}`x` 和 {anchorName Point3D}`y`，并用相同的字段名进行实例化：

```anchor Point3D
structure Point3D where
  x : Float
  y : Float
  z : Float
```

```anchor origin3D
def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
```

这意味着，为了使用花括号语法，必须知道该结构的预期类型。
如果类型未知，Lean 将无法实例化该结构。
例如，

```anchorTerm originNoType
#check { x := 0.0, y := 0.0 }
```

导致错误

```anchorError originNoType
invalid {...} notation, expected type is not known
```


照常，可以通过提供类型标注来补救这种情况。

```anchorTerm originWithAnnot
#check ({ x := 0.0, y := 0.0 } : Point)
```


```anchorInfo originWithAnnot
{ x := 0.0, y := 0.0 } : Point
```


为了使程序更简洁，Lean 还允许在花括号内部写出结构类型标注。

```anchorTerm originWithAnnot2
#check { x := 0.0, y := 0.0 : Point}
```


```anchorInfo originWithAnnot2
{ x := 0.0, y := 0.0 } : Point
```


# 更新结构
%%%
tag := "updating-structures"
file := "Updating-Structures"
%%%

设想一个函数 {anchorName zeroXBad}`zeroX`，它将某个 {anchorName zeroXBad}`Point` 的 {anchorName zeroXBad}`x` 字段替换为 {anchorTerm zeroX}`0`。
在大多数编程语言共同体中，这句话会表示：由 {anchorName Point}`x` 指向的内存位置将被一个新值覆盖。
然而，Lean 是一种函数式编程语言。
在函数式编程共同体中，这类说法几乎总是指：分配一个新的 {anchorName Point}`Point`，其 {anchorName Point}`x` 字段指向新值，而所有其他字段都指向来自输入的原始值。
编写 {anchorName zeroXBad}`zeroX` 的一种方式是逐字遵循这一描述：为 {anchorName Point}`x` 填入新值，并手动转移 {anchorName Point}`y`：

```anchor zeroXBad
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }
```

然而，这种编程风格有一些缺点。
首先，如果向结构添加新字段，那么每一个更新任何字段的位置都必须随之更新，从而造成维护困难。
其次，如果结构包含多个类型相同的字段，那么复制粘贴式编码确实有风险导致字段内容被重复或互换。
最后，程序会变得冗长而繁琐。

Lean 提供了一种方便的语法，用于替换结构中的某些字段，同时保持其他字段不变。
这是通过在结构初始化中使用 {kw}`with` 关键字来完成的。
未改变字段的来源出现在 {kw}`with` 之前，新字段出现在其后。
例如，{anchorName zeroX}`zeroX` 可以只写出新的 {anchorName Point}`x` 值：

```anchor zeroX
def zeroX (p : Point) : Point :=
  { p with x := 0 }
```

请记住，这种结构更新语法并不会修改已有值——它会创建与旧值共享某些字段的新值。
给定点 {anchorName fourAndThree}`fourAndThree`：

```anchor fourAndThree
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
```

对其求值，然后使用 {anchorName zeroX}`zeroX` 对其更新并求值，再次对其求值会得到原始值：

```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


```anchorTerm zeroXFourAndThreeEval
#eval zeroX fourAndThree
```


```anchorInfo zeroXFourAndThreeEval
{ x := 0.000000, y := 3.400000 }
```


```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


结构更新不会修改原有结构，这一事实的一个结果是：当新值由旧值计算得到时，对这种情形进行推理会变得更容易。
所有对旧结构的引用，在所提供的所有新值中，仍然指向相同的字段值。




# 幕后机制
%%%
tag := "behind-the-scenes"
file := "Behind-the-Scenes"
%%%

每个结构都有一个_构造子_。
在这里，“构造子”一词可能会造成混淆。
不同于 Java 或 Python 等语言中的构造器，Lean 中的构造子不是在初始化数据类型时运行的任意代码。
相反，构造子只是收集要存储在新分配的数据结构中的数据。
不能提供自定义构造子来预处理数据或拒绝无效参数。
这实际上是“构造子”一词在两个语境中具有不同但相关含义的情形。


默认情况下，名为 {lit}`S` 的结构的构造子名为 {lit}`S.mk`。
这里，{lit}`S` 是命名空间限定符，{lit}`mk` 是构造子本身的名称。
除了使用花括号初始化语法外，也可以直接应用该构造子。

```anchorTerm checkPointMk
#check Point.mk 1.5 2.8
```

然而，这通常不被认为是良好的 Lean 风格，而且 Lean 甚至会使用标准的结构初始化器语法返回其反馈。

```anchorInfo checkPointMk
{ x := 1.5, y := 2.8 } : Point
```


构造子具有函数类型，这意味着凡是期望函数的地方都可以使用它们。
例如，{anchorName Pointmk}`Point.mk` 是一个函数，它接受两个 {anchorName Point}`Float`（分别为 {anchorName Point}`x` 和 {anchorName Point}`y`），并返回一个新的 {anchorName Point}`Point`。

```anchorTerm Pointmk
#check (Point.mk)
```

```anchorInfo Pointmk
Point.mk : Float → Float → Point
```

若要覆盖结构的构造子名称，请在开头写两个冒号。
例如，若要使用 {anchorName PointCtorNameName}`Point.point` 而不是 {anchorName Pointmk}`Point.mk`，请写作：

```anchor PointCtorName
structure Point where
  point ::
  x : Float
  y : Float
```

除了构造子之外，还会为结构的每个字段定义一个访问器函数。
这些访问器与字段同名，并位于该结构的命名空间中。
对于 {anchorName Point}`Point`，会生成访问器函数 {anchorName Pointx}`Point.x` 和 {anchorName Pointy}`Point.y`。

```anchorTerm Pointx
#check (Point.x)
```

```anchorInfo Pointx
Point.x : Point → Float
```

```anchorTerm Pointy
#check (Point.y)
```

```anchorInfo Pointy
Point.y : Point → Float
```


事实上，正如花括号结构构造语法会在幕后转换为对结构构造子的调用一样，先前 {anchorName addPoints}`addPoints` 定义中的语法 {anchorName addPoints}`x` 会转换为对 {anchorName addPoints}`x` 访问器的调用。
也就是说，{anchorTerm originx}`#eval origin.x` 和 {anchorTerm originx1}`#eval Point.x origin` 都产生

```anchorInfo originx1
0.000000
```


访问器点记法不仅可用于结构体字段。
它还可用于接受任意数量参数的函数。
更一般地，访问器记法的形式为 {lit}`TARGET.f ARG1 ARG2 ...`。
如果 {lit}`TARGET` 的类型为 {lit}`T`，则会调用名为 {lit}`T.f` 的函数。
{lit}`TARGET` 成为其类型为 {lit}`T` 的最左侧参数；这通常是第一个参数，但并非总是如此，而 {lit}`ARG1 ARG2 ...` 则按顺序作为其余参数提供。
例如，{anchorName stringAppend}`String.append` 可以从字符串用访问器记法调用，尽管 {anchorName Inline}`String` 并不是带有 {anchorName stringAppendDot}`append` 字段的结构体。

```anchorTerm stringAppendDot
#eval "one string".append " and another"
```

```anchorInfo stringAppendDot
"one string and another"
```

在该示例中，{lit}`TARGET` 表示 {anchorTerm stringAppendDot}`"one string"`，而 {lit}`ARG1` 表示 {anchorTerm stringAppendDot}`" and another"`。

函数 {anchorName modifyBoth}`Point.modifyBoth`（即在 {lit}`Point` 命名空间中定义的 {anchorName modifyBothTest}`modifyBoth`）将一个函数应用于 {anchorName Point}`Point` 中的两个字段：

```anchor modifyBoth
def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
```

即使 {anchorName Point}`Point` 参数位于函数参数之后，也同样可以将它与点记法一起使用：

```anchorTerm modifyBothTest
#eval fourAndThree.modifyBoth Float.floor
```

```anchorInfo modifyBothTest
{ x := 4.000000, y := 3.000000 }
```

在这种情况下，{lit}`TARGET` 表示 {anchorName fourAndThree}`fourAndThree`，而 {lit}`ARG1` 是 {anchorName modifyBothTest}`Float.floor`。
这是因为访问器记法的目标会被用作类型能够匹配的第一个参数，而不一定是第一个参数。

# 练习
%%%
tag := "structure-exercises"
file := "Exercises"
%%%

 * 定义一个名为 {anchorName RectangularPrism}`RectangularPrism` 的结构体，其中包含一个长方体的高、宽和深，三者均为 {anchorName RectangularPrism}`Float`。
 * 定义一个名为 {anchorTerm RectangularPrism}`volume : RectangularPrism → Float` 的函数，用于计算长方体的体积。
 * 定义一个名为 {anchorName RectangularPrism}`Segment` 的结构，用其端点表示一条线段，并定义一个函数 {lit}`length : Segment → Float` 来计算线段的长度。{anchorName RectangularPrism}`Segment` 至多应有两个字段。
 * 声明 {anchorName RectangularPrism}`RectangularPrism` 会引入哪些名称？
 * 以下 {anchorName Hamster}`Hamster` 和 {anchorName Book}`Book` 的声明会引入哪些名称？它们的类型是什么？

    ```anchor Hamster
    structure Hamster where
      name : String
      fluffy : Bool
    ```

    ```anchor Book
    structure Book where
      makeBook ::
      title : String
      author : String
      price : Float
    ```
