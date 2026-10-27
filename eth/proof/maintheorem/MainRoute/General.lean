/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainRoute.GeneralDefs
import TwoMachines.Main
import Wrap.Main
import ToTuring.Closure.Basic
import GeneralPieces.ThmRunningTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The chain for every solver, from the statements of its steps

`routeOn_of` proves `RouteOnEverySolver`. It takes the statements of the steps as hypotheses, each
under the name it has where it is proved: Theorem D (a) for every machine that computes the function
of Steps 1 to 5 (proof/variables/RecursionToBound); `EveryChoiceMeetsThmVariablesB`,
`EveryExhaustiveMachineTriesAll`, the front end and the test, the exhaustive machine
(proof/variables/PairsToBound); `EveryAlternationMeetsMinBound`, for counting and for deciding, the
renaming front end, `MinBoundIsTheMainTheorem` (proof/maintheorem/MinOfBounds). The two tools are in
proof/machines/TwoMachines. No arithmetic is done: each field is an application of the statement of
its step to the objects of the steps before. The solver, its levels and the function for
the bound in m are arbitrary. -/

public section

namespace MainRoute

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

/-- The chain for every solver, from the statements of the steps. -/
theorem routeOn_of (hVariablesAEvery : RecursionToBound.ThmVariablesAForEveryMachine) (hChoice : EveryChoiceMeetsThmVariablesB) (hTries : EveryExhaustiveMachineTriesAll) (hFront : FrontEndAndTestExist)
    (hExh : ExhaustiveMachineExists) (hAlt : EveryAlternationMeetsMinBound) (hDec : EveryAlternationDecidesWithinMinBound) (hRen : RenamingFrontEndExists) (hMain : MinBoundIsTheMainTheorem) : RouteOnEverySolver := by
  intro Idx _ S e C₀ Q hPoly num hnum
  obtain ⟨n₀, hn₀⟩ := hVariablesAEvery Idx S e C₀ Q hPoly num hnum
  refine ⟨n₀, fun a ha fm em hMex hM n₁ hn₁ => ?_⟩
  obtain ⟨hVariablesAEx, hVariablesA⟩ := hn₀ n₁ hn₁
  -- Theorem D (b) for every chosen machine, from the body of Theorem D (a)
  have hVariablesB : ∀ (Ma : TM2ComputableAux Bool Bool) (Ca : ℕ), ThmVariablesAFor S Q Ma Ca → ∀ (Mb : TM2ComputableAux Bool Bool) (cb : ℕ), TriesAllWithin Mb cb →
      ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
        ∀ (M₂ : TM2ComputableAux Bool Bool) (q₂ : ℕ), Chooses Ma Mb test pre id id id M₂ q₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂ := hChoice Idx S e C₀ Q a ha
  -- the same, for the machines built on the named function
  have hVariablesB' : ∀ M₂ : TM2ComputableAux Bool Bool, ChosenAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (S.K (Q.idx 0)) M₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂ := by
    rintro M₂ ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩
    obtain ⟨Ca, hCa⟩ := hVariablesA Ma qa hMa
    obtain ⟨cb, hcb⟩ := hTries Mb qb hMb
    exact hVariablesB Ma Ca hCa Mb cb hcb pre test hpre htest M₂ q₂ hch
  -- existence
  have hex : ∀ post : List Bool → List Bool, PolyT post → ∃ N : TM2ComputableAux Bool Bool,
      BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) post N := fun post hpost => by
    obtain ⟨Ma, qa, hfa, hMa⟩ := hVariablesAEx
    obtain ⟨Mb, -, qb, hfb, -, hMb⟩ := hExh
    obtain ⟨⟨pre, hpreP, hpre⟩, hT⟩ := hFront
    obtain ⟨test, htestP, htest⟩ := hT (S.K (Q.idx 0))
    obtain ⟨Ka, Kb, M₂, q₂', q₂, hf₂, hh₂, hch⟩ := everyTwoMachinesCanBeChosenBetween Ma Mb hfa hfb test pre id id id htestP hpreP PolyT.id' PolyT.id' PolyT.id'
    obtain ⟨M₁, q₁, hf₁, hM₁⟩ := hMex
    obtain ⟨ren, hrenP, hren⟩ := hRen
    obtain ⟨K₁, K₂, N, q', q, hfN, hhN, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ ren ren post post hrenP hrenP hpost hpost
    exact ⟨N, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, q, q', pre, ren, test, Ka, Kb, K₁, K₂, hfa, hfb, hf₂, hf₁, hfN, hpreP, htestP, hrenP, hMa, hMb, hpre, htest, hh₂, hch, hM₁, hren, hhN, halt⟩
  exact
    { da := hVariablesA
      variablesBFromTheBody := hVariablesB
      tries := hTries
      db := hVariablesB'
      cor := hAlt
      main := by
        rintro N ⟨M₁, M₂, q₁, q, ren, hch, hM₁, hren, halt⟩
        obtain ⟨C₂, hC₂⟩ := hVariablesB' M₂ hch
        obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
        obtain ⟨C, hC⟩ := hAlt ren hren M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
        exact ⟨C, hC, (hMain N C).1 hC⟩
      decides := by
        rintro N ⟨M₁, M₂, q₁, q, ren, hch, hM₁, hren, halt⟩
        obtain ⟨C₂, hC₂⟩ := hVariablesB' M₂ hch
        obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
        exact hDec ren hren M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
      exist := ⟨hex id PolyT.id', hex someBit lastStepsArePolynomialTime.2⟩ }

end MainRoute
