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
file := "Acknowledgments"
%%%


这本免费在线书籍得以问世，离不开 Microsoft Research 的慷慨支持；他们资助了本书的撰写，并将其免费提供。
在写作过程中，他们使我能够借助 Lean 开发团队的专业知识，既回答我的问题，也让 Lean 更易于使用。
特别是，Leonardo de Moura 发起了该项目并帮助我起步，Chris Lovett 建立了 CI 和部署自动化，并作为试读者提供了出色的反馈，Gabriel Ebner 提供了技术审阅，Sarah Smith 使行政方面保持良好运转，Vanessa Rodriguez 帮助我诊断了源代码高亮库与 iOS 上某些版本的 Safari 之间一种棘手的交互。

撰写本书占用了正常工作时间之外的许多时间。
我的妻子 Ellie Thrane Christiansen 承担了比平常更多的家庭事务；如果没有她这样做，本书便不可能存在。
每周额外工作一天对我的家人并不容易——感谢你们在我写作期间的耐心与支持。

围绕 Lean 的在线社区为本项目提供了热情的支持，既有技术上的，也有情感上的。
特别是，在我学习 Lean 的元编程系统、以便编写支持代码时，Sebastian Ullrich 提供了关键帮助；这些代码使错误消息文本既能在 CI 中得到检查，又能方便地包含在本书自身之中。
每次发布新修订后数小时内，热心读者就会找出错误、提出建议，并给予我许多善意。
特别地，我要感谢 Arien Malec、Asta Halkjær From、Bulhwi Cha、Craig Stuntz、Daniel Fabian、Evgenia Karunus、eyelash、Floris van Doorn、František Silváši、Henrik Böving、Ian Young、Jeremy Salwen、Jireh Loreaux、Kevin Buzzard、Lars Ericson、Liu Yuxi、Mac Malone、Malcolm Langfield、Mario Carneiro、Newell Jensen、Patrick Massot、Paul Chisholm、Pietro Monticone、Tomas Puverle、Yaël Dillies、Zhiyuan Bao 和 Zyad Hassan，感谢他们在文体和技术方面提出的许多建议。
