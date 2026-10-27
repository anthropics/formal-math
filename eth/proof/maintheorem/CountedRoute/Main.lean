/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRoute.Defs
import ThmVariables.PartA
import NamesInOrder.Main
import MainRoute.GeneralMain
import CountedToPadded.Main
import CountedToPadded.Need
import CountedInstance.Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The chain from counted operations: the proofs

* `onEveryMachineWithQueryAccessFrom`: the step from counted operations to the padding string
  (`QueryMachines.Bridge.SolverOfMachineLevels`) gives, for a machine E with the printed hypothesis,
  a polynomial-time solver with a sequence of levels for the numbers e′_ℓ in [e_ℓ, 2e_ℓ];
  `ThmVariables.numberBetween_cut` gives the clause that a number in [e′_ℓ, 2e′_ℓ] can be computed;
  e′_ℓ ≤ 2e_ℓ ≤ 2a/√(log K_ℓ) (`QueryMachines.Bridge.CutNumberFacts`). The chain for
  every solver (`NamesInOrder.OnEverySolver`; for Step 6 `MainRoute.BothBoundsOnEverySolver`) is
  applied to this solver, and the names are rewritten.
* `onTheCountedRecursionFrom`: the machine of Theorem A (b) on the pieces of Appendix B meets the
  hypothesis (`CountedInstance.TheRecursionMeetsTheHypothesis`).
* `closedStatementsFrom`: the closed statements are read off. -/

public section

namespace CountedRoute

open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)

/-- The chain from counted operations, from the step to the padding string and the chains for every
solver. -/
theorem onEveryMachineWithQueryAccessFrom : OnEveryMachineWithQueryAccessFrom := by
  intro hB hCut hBoth hOn K e C₀ kf num E _ hyp
  obtain ⟨hP, Q, -, hK, hpick⟩ := hB E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  have hnb := ThmVariables.numberBetween_cut Q hyp.number.1 hK
  obtain ⟨n₀, hn₀⟩ := hOn _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) hnb
  obtain ⟨n₀', hn₀'⟩ := hBoth _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) hnb
  refine ⟨max n₀ n₀', fun a ha n₁ hn₁ => ?_⟩
  have ha' : ∀ l : ℕ, cutNumber K num l ≤ ((2 * a : ℕ) : ℝ) / Real.sqrt (lg ((solverOfMachine E num C₀).K (Q.idx l))) := fun l => by
    rw [hK l]
    have h1 := ((hCut K e C₀ num hyp.levels hyp.number).2 l).2.2.1
    have h2 := ha l
    have h3 : ((2 * a : ℕ) : ℝ) / Real.sqrt (lg (K l)) = 2 * ((a : ℝ) / Real.sqrt (lg (K l))) := by
      push_cast
      ring
    rw [h3]
    linarith
  obtain ⟨r1, r2, r3⟩ := hn₀ (2 * a) ha' n₁ (le_trans (le_max_left _ _) hn₁)
  have r0 := ((hn₀' (2 * a) ha').2 n₁ (le_trans (le_max_right _ _) hn₁)).db
  rw [hpick] at r0 r1 r2 r3
  rw [hK 0] at r0 r2 r3
  exact ⟨r0, r1, r2, r3⟩

/-- The chain on the machine of Theorem A (b). -/
theorem onTheCountedRecursionFrom : OnTheCountedRecursionFrom := by
  rintro ⟨c, x₀, C₀, D, Alg, hPieces, hShort, hAppHalfPieces, hx, hc, hsteps, hsolves, hlev, hcomp, hnum, hrate⟩ hOn
  have hyp : ThmVariables.Hypothesis (_root_.Levels.Gen.K x₀) (_root_.Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ (levelsUnder x₀) fractionHalf (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) :=
    ⟨hlev, hcomp, hnum, hsteps, hsolves⟩
  refine ⟨c, x₀, C₀, D, Alg, hPieces, hShort, hAppHalfPieces, hx, hc, hrate, hyp, ?_⟩
  intro inst
  obtain ⟨n₀, hn₀⟩ := hOn _ _ C₀ _ _ (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) hyp
  exact ⟨n₀, fun n₁ h => hn₀ (3 * x₀ + 6) hrate n₁ h⟩

/-- The closed statements, read off the chain on the machine of Theorem A (b). -/
theorem closedStatementsFrom : ClosedStatementsFrom := by
  rintro ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, -, hyp, h⟩
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨n₀, hn₀⟩ := h
  obtain ⟨hVariablesB, hM, hN, N, hB⟩ := hn₀ n₀ le_rfl
  obtain ⟨hA, hf⟩ := builtIsAssembledDirectly _ _ _ _ _ _ hB
  obtain ⟨C, h12, h1⟩ := hN N hA
  obtain ⟨Ma, Mb, M₂, M₁, qa, qb, q₂, -, q₁, -, -, pre, test, -, -, -, -, -, -, hf₂, hf₁, -, -, -, hMa, hMb, hpre, htest, -, hch, hM₁, -⟩ := hB
  obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
  obtain ⟨C₂, hC₂⟩ := hVariablesB M₂ ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩
  exact ⟨⟨N, C, hf, h1⟩, ⟨N, C, hf, h12⟩, ⟨M₂, C₂, hf₂, hC₂⟩, ⟨M₁, C₁, hf₁, hC₁⟩⟩

/-- **The chain from counted operations.** -/
theorem onEveryMachineWithQueryAccess : OnEveryMachineWithQueryAccess := onEveryMachineWithQueryAccessFrom solverOfMachineLevels cutNumberFacts bothBoundsOnEverySolver onEverySolver

/-- **The chain on the machine of Theorem A (b).** -/
theorem onTheCountedRecursion : OnTheCountedRecursion := onTheCountedRecursionFrom CountedInstance.theRecursionMeetsTheHypothesis onEveryMachineWithQueryAccess

/-- **The Main Theorem** of the paper, on Theorem A (b) in counted operations. -/
theorem mainTheoremHolds : MainTheoremHolds := (closedStatementsFrom onTheCountedRecursion).1

/-- **Corollary 11**, on Theorem A (b) in counted operations. -/
theorem corMinHolds : CorMinHolds := (closedStatementsFrom onTheCountedRecursion).2.1

/-- **The conclusion of Theorem D (b)**, on Theorem A (b) in counted operations. -/
theorem thmVariablesBHolds : ThmVariablesBHolds := (closedStatementsFrom onTheCountedRecursion).2.2.1

/-- **The first sentence of Theorem A (c)**, at α′ = 1/2, on Theorem A (b) in counted operations. -/
theorem boundInMHolds : BoundInMHolds := (closedStatementsFrom onTheCountedRecursion).2.2.2

end CountedRoute
