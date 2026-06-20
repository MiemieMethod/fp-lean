import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.TODO"

#doc (Manual) "致谢" =>
%%%
number := false
%%%


这本免费的在线书籍得以完成，离不开 Microsoft Research 的慷慨支持；他们资助了本书的写作，并使其能够免费发布。
在写作过程中，他们也让我能够借助 Lean 开发团队的专业知识：团队既回答了我的问题，也让 Lean 变得更易使用。
特别地，Leonardo de Moura 发起了这个项目并帮助我起步；Chris Lovett 搭建了 CI 与部署自动化，并作为试读者给出了很好的反馈；Gabriel Ebner 提供了技术审阅；Sarah Smith 让行政事务保持顺畅；Vanessa Rodriguez 帮助我诊断源代码高亮库与 iOS 上某些 Safari 版本之间一个棘手的交互问题。

写作本书占用了许多正常工作时间以外的时间。
我的妻子 Ellie Thrane Christiansen 承担了比平常更多的家庭事务；如果没有她这样做，本书不可能存在。
每周额外投入一天工作对我的家庭并不容易；感谢你们在我写作期间的耐心与支持。

围绕 Lean 的在线社区为这个项目提供了热情的支持，既有技术上的，也有情感上的。
特别地，当我学习 Lean 的元编程系统、以便编写支持代码来让错误消息文本既能在 CI 中检查又能方便地纳入本书时，Sebastian Ullrich 提供了关键帮助。
每当发布新的修订版本后，热心读者往往会在数小时内发现错误、提出建议，并给予我许多善意。
特别感谢 Arien Malec、Asta Halkjær From、Bulhwi Cha、Craig Stuntz、Daniel Fabian、Evgenia Karunus、eyelash、Floris van Doorn、František Silváši、Henrik Böving、Ian Young、Jeremy Salwen、Jireh Loreaux、Kevin Buzzard、Lars Ericson、Liu Yuxi、Mac Malone、Malcolm Langfield、Mario Carneiro、Newell Jensen、Patrick Massot、Paul Chisholm、Pietro Monticone、Tomas Puverle、Yaël Dillies、Zhiyuan Bao 和 Zyad Hassan 提出的许多风格与技术方面的建议。
