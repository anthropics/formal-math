/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NamesInOrder.Defs
import MainRoute.GeneralMain
import MainRoute.General
import MainRoute.EveryMachine
import TwoMachines.Main
import MinOfBounds.Main
import MinOfBounds.Rename
import MinOfBounds.Arith
import PairsToBound.Main
import Wrap.Main
import Wrap.Sim
import ToTuring.Closure.Basic
import VariableBound.Paper.Arith
import VariableBound.Paper.Forms
import GeneralPieces.Main
import GeneralPieces.ThmRunningTime
import GeneralPieces.Tied.Bound

/-! # Alternating two machines on the same input, and the chain of steps from a solver for cliques to the Main Theorem

The theorems `everyDirectAlternation_of`, `onEverySolver_of` and `forAllPieces_of` take the steps
that they need as hypotheses, named by the statements that they use; NamesInOrder/Main.lean supplies
them.
* `everyDirectAlternation_of`: both machines are started on the same word `SatM.enc k φ` and put out
  the same word, so a machine that runs them in alternation puts it out within q·(min(t₁, t₂) + L + 1)^q
  steps; `AlternationCostGoesIntoC` does the rest, and `VariableBound.Paper.corMinIsMainTheorem`
  passes from the bound of the Main Theorem to that of Corollary 11.
* `onEverySolver_of`: from `MainRoute.BothBoundsOnEverySolver`: its first clause gives the bound in
  m with a polynomial, its field `db` the bound of Theorem D (b) for every machine made as Step 6
  says, its field `exist` the machines.
* `forAllPieces_of`: the recursion of Appendix A on the pieces of Appendix B is an instance. -/

public section

namespace NamesInOrder

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)

/-- Corollary 11 from the first sentence of Theorem A (c) and Theorem D (b), for every machine. -/
theorem everyDirectAlternation_of (hCost : AlternationCostGoesIntoC) : EveryDirectAlternationMeetsTheBound := by
  intro M₁ C₁ h₁ M₂ C₂ h₂ N q hN
  obtain ⟨C, hC⟩ := hCost C₁ C₂ q
  have h : MainTheoremFor N C := fun k n φ hk hφ hm hn hocc =>
    Outputs.mono (hN (SatM.enc k φ) _ _ _ _ (h₁ k n φ hk hφ hm hocc) (h₂ k n φ hk hn hφ) rfl) (hC k n φ hk hφ hm hn hocc)
  exact ⟨C, (VariableBound.Paper.corMinIsMainTheorem N C).2 h, h⟩

/-- A machine that is built directly is assembled directly and has finite alphabets. -/
theorem builtIsAssembledDirectly : BuiltIsAssembledDirectly := by
  rintro fa ea fm em K₀ N ⟨Ma, Mb, M₂, M₁, qa, qb, q₂, -, q₁, q, -, pre, test, -, -, -, -, -, -, -, -, hfN, -, -, hMa, hMb, hpre, htest, -, hch, hM₁, -, halt⟩
  exact ⟨⟨M₁, M₂, q₁, q, ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩, hM₁, halt⟩, hfN⟩

/-- The chain for every solver. -/
theorem onEverySolver_of (hBoth : BothBoundsOnEverySolver) (hAlone : BoundInMWithoutThePolynomial) (hAlt : EveryDirectAlternationMeetsTheBound) : OnEverySolver := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := hBoth Idx S e C₀ Q hS num hnum
  refine ⟨n₀, fun a ha n₁ hn₁ => ?_⟩
  obtain ⟨hM, hR⟩ := hn₀ a ha
  have R := hR n₁ hn₁
  have hM' : ∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (AM S Q.pick) (eM S Q.pick) q₁ → ∃ C₁ : ℕ, MeetsBoundInMAlone M₁ C₁ := fun M₁ q₁ h => by
    obtain ⟨C, hC⟩ := hM M₁ q₁ h
    exact hAlone M₁ C hC
  refine ⟨hM', ?_, ?_⟩
  · rintro N ⟨M₁, M₂, q₁, q, hch, hM₁, halt⟩
    obtain ⟨C₂, hC₂⟩ := R.db M₂ hch
    obtain ⟨C₁, hC₁⟩ := hM' M₁ q₁ hM₁
    exact hAlt M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
  · obtain ⟨-, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, -, -, pre, -, test, Ka, Kb, -, -, hfa, hfb, hf₂, hf₁, -, hpreP, htestP, -, hMa, hMb, hpre, htest, hh₂, hch, hM₁, -⟩ := R.exist.1
    obtain ⟨K₁, K₂, N, q', q, hfN, hhN, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ id id id id PolyT.id' PolyT.id' PolyT.id' PolyT.id'
    exact ⟨N, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, q, q', pre, test, Ka, Kb, K₁, K₂, hfa, hfb, hf₂, hf₁, hfN, hpreP, htestP, hMa, hMb, hpre, htest, hh₂, hch, hM₁, hhN, halt⟩

/-- The chain for all pieces of Appendix B: an instance of the chain for every solver. -/
theorem forAllPieces_of (hOn : OnEverySolver) (hPairs : ThePairsSatisfyTheHypothesis) (hTheta : ThetaOfThePairs) : ForAllPieces := by
  intro c P₀ A val h
  obtain ⟨C₀, Cp, H⟩ := hPairs c
  obtain ⟨Q, hPoly, hK, hpick, hnum, -⟩ := H P₀ A val h.1
  obtain ⟨n₀, hn₀⟩ := hOn _ _ _ C₀ Q hPoly fractionHalf hnum
  refine ⟨n₀, fun n₁ hn₁ => ?_⟩
  have hθ : ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) l ≤ ((3 * GeneralPieces.x₀Of c + 6 : ℕ) : ℝ) / Real.sqrt (lg ((RecursionWithPieces.solverAB P₀ val c).K (Q.idx l))) := fun l => by
    rw [hK l]
    obtain ⟨-, -, -, -, -, t6⟩ := hTheta (GeneralPieces.x₀Of c) l (GeneralPieces.x₀Of_ge c)
    refine t6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hx : (0 : ℝ) ≤ (GeneralPieces.x₀Of c : ℝ) := Nat.cast_nonneg _
    have hs : Real.sqrt (3 * (GeneralPieces.x₀Of c : ℝ) + 6) ≤ 3 * (GeneralPieces.x₀Of c : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hs0 := Real.sqrt_nonneg (3 * (GeneralPieces.x₀Of c : ℝ) + 6)
    push_cast
    linarith
  obtain ⟨r1, r2, r3⟩ := hn₀ (3 * GeneralPieces.x₀Of c + 6) hθ n₁ hn₁
  rw [hpick] at r1 r2 r3
  rw [hK 0] at r2 r3
  exact ⟨r1, r2, r3⟩

/-- The Main Theorem and Corollary 11, read off the chain with Theorem B. -/
theorem closed_of (hAll : ForAllPieces) : MainTheoremAllOccur ∧ CorMinAllOccur := by
  obtain ⟨c, P₀, A', val, h⟩ := GeneralPieces.thmHalfPieces_iff.1 AppRunningTime.thmHalfPieces
  obtain ⟨n₀, hn₀⟩ := hAll c P₀ A' val h
  obtain ⟨-, hN, N, hB⟩ := hn₀ n₀ le_rfl
  obtain ⟨hA, hf⟩ := builtIsAssembledDirectly _ _ _ _ _ _ hB
  obtain ⟨C, hC12, hC1⟩ := hN N hA
  exact ⟨⟨N, C, hf, hC1⟩, ⟨N, C, hf, hC12⟩⟩

/-- The first sentence of Theorem A (c), at α′ = 1/2, as a closed statement. -/
theorem boundInMHolds_of (hAll : ForAllPieces) : BoundInMHolds := by
  obtain ⟨c, P₀, A', val, h⟩ := GeneralPieces.thmHalfPieces_iff.1 AppRunningTime.thmHalfPieces
  obtain ⟨n₀, hn₀⟩ := hAll c P₀ A' val h
  obtain ⟨hM, -, -⟩ := hn₀ n₀ le_rfl
  obtain ⟨M, q, hf, hc⟩ := (boundInMForEveryMachine c P₀ A' val h.1).1
  obtain ⟨C, hC⟩ := hM M q hc
  exact ⟨M, C, hf, hC⟩

end NamesInOrder
