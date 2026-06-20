import VersoManual

import FPLean.Intro
import FPLean.Acks
import FPLean.GettingToKnow
import FPLean.HelloWorld
import FPLean.PropsProofsIndexing
import FPLean.TypeClasses
import FPLean.Monads
import FPLean.FunctorApplicativeMonad
import FPLean.MonadTransformers
import FPLean.DependentTypes
import FPLean.TacticsInductionProofs
import FPLean.ProgramsProofs
import FPLean.NextSteps

open Verso.Genre Manual
open Verso Code External

open Verso Doc Elab in
open Lean (quote) in
@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do
    let version ← IO.FS.readFile "../examples/lean-toolchain"
    let version := version.stripPrefix "leanprover/lean4:" |>.trim
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Lean 函数式编程" =>

%%%
authors := ["David Thrane Christiansen"]
%%%


_版权所有 Microsoft Corporation 2023 和 Lean FRO, LLC 2023–2025_



这是一本关于将 Lean 作为编程语言使用的免费书籍。所有代码示例都使用 Lean 版本 {versionString}[] 进行测试。

{include 1 FPLean.Intro}

{include 1 FPLean.Acks}

{include 1 FPLean.GettingToKnow}

{include 1 FPLean.HelloWorld}

{include 1 FPLean.PropsProofsIndexing}

{include 1 FPLean.TypeClasses}

{include 1 FPLean.Monads}

{include 1 FPLean.FunctorApplicativeMonad}

{include 1 FPLean.MonadTransformers}

{include 1 FPLean.DependentTypes}

{include 1 FPLean.TacticsInductionProofs}

{include 1 FPLean.ProgramsProofs}

{include 1 FPLean.NextSteps}
