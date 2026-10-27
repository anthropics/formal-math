/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmVariables.Defs
import ThmVariables.Bound
import ToTuring.Closure.Basic
import ToTuring.Lib.Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Theorem D (a) with the printed hypothesis, from the form with the padding string

Let K, e, C₀, `kf`, `num`, E be as in the printed hypothesis. The step from counted operations to
the padding string (`SolverFromMachine`, a hypothesis here) gives a polynomial-time solver S with a
sequence Q of levels for the same K_ℓ and for e′_ℓ = `CliqueLevels.cutNumber K num ℓ`, the number in
[e_ℓ, 2e_ℓ] cut at 1.
* The clause of the hypothesis that a number in [e′_ℓ, 2e′_ℓ] can be computed holds for the sequence
  e′, because e′_ℓ itself is computed: it is the fraction min(a, b)/b for the fraction a/b that
  `num` returns (`QueryMachines.Bridge.cutFraction`; `cut_eq`, `numberBetween_cut`).
* Theorem D (a) with the padding string (`RecursionToBound.ThmVariablesAWithNumberBetween`, a
  hypothesis here) gives a machine M with the bound at e′_ℓ.
* The levels of n are the same, because K at the ℓ-th index is K_ℓ.
* e_ℓ ≤ e′_ℓ ≤ 2e_ℓ and e′_ℓ ≤ 1, so the bound at e′_ℓ is the bound at e_ℓ with twice the constant
  (`boundAtANumberBetween`). The last two points are `conclusion_of_cut`. -/

public section

namespace ThmVariables

open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)

/-- min(a, b)/b = min(a/b, 1), for all natural numbers a and b (both sides are 0 if b = 0). -/
theorem cut_eq (a b : ℕ) : ((min a b : ℕ) : ℝ) / (b : ℝ) = min ((a : ℝ) / b) 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [Nat.cast_min, ← min_div_div_right hb'.le, div_self hb'.ne']

/-- e′_ℓ = `cutNumber K num ℓ` is not negative, for all K, `num` and ℓ. -/
theorem cutNumber_nonneg (K : ℕ → ℕ) (num : List Unit × List Unit → ℕ × ℕ) (l : ℕ) : 0 ≤ cutNumber K num l := le_min (by positivity) zero_le_one

/-- A number in [e′_ℓ, 2e′_ℓ] can be computed from ℓ in time polynomial in K_ℓ, for e′_ℓ the number
that `num` returns, cut at 1: it is e′_ℓ itself. Hypotheses: Q is a sequence of levels of a solver S
for the numbers e′_ℓ, `num` is polynomial-time, and S has K_ℓ at the ℓ-th index of Q. -/
theorem numberBetween_cut {Idx : Type} [Enc Idx] {S : Solver Idx} {K : ℕ → ℕ} {num : List Unit × List Unit → ℕ × ℕ} {C₀ : ℕ} (Q : S.Seq (cutNumber K num) C₀)
    (hnum : PolyT num) (hK : ∀ l : ℕ, S.K (Q.idx l) = K l) : PairsToBound.NumberBetween S Q (cutFraction num) := by
  refine ⟨by unfold cutFraction; fun_prop, fun l => ?_⟩
  have e1 : (((cutFraction num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).1 : ℕ) : ℝ) / (((cutFraction num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).2 : ℕ) : ℝ) = cutNumber K num l := by
    rw [hK]
    exact cut_eq _ _
  rw [e1]
  have := cutNumber_nonneg K num l
  exact ⟨le_rfl, by linarith⟩

/-- A machine with the bound of Theorem D (a) for a solver whose levels are K_ℓ and e′_ℓ, the number
in [e_ℓ, 2e_ℓ] cut at 1, has the bound for K_ℓ and e_ℓ with twice the constant. Hypotheses: K, e, C₀
satisfy the printed inequalities (`CliqueLevels.Levels`), `num` returns a number in [e_ℓ, 2e_ℓ]
(`CliqueLevels.NumberBetween`), Q is a sequence of levels of the solver S for the numbers e′_ℓ, and
S has K_ℓ at the ℓ-th index of Q. -/
theorem conclusion_of_cut {Idx : Type} [Enc Idx] {S : Solver Idx} {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ C₀' : ℕ} {num : List Unit × List Unit → ℕ × ℕ} (Q : S.Seq (cutNumber K num) C₀')
    (hL : Levels K e C₀) (hnum : CliqueLevels.NumberBetween K e num) (hK : ∀ l : ℕ, S.K (Q.idx l) = K l) {M : TM2ComputableAux Bool Bool} {C' : ℕ} (hM : ThmVariablesAFor S Q M C') :
    Conclusion K e M (2 * C') := by
  intro k n l φ hl hk hk4 hφ
  have hl' : MainTheoremForms.IsLevel S Q n l := by
    unfold MainTheoremForms.IsLevel
    rw [hK, hK]
    exact hl
  obtain ⟨ev⟩ := hM k n l φ hl' hk hk4 hφ
  obtain ⟨h1, h2⟩ := hnum.2 l
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (boundAtANumberBetween C' k n (e l) (cutNumber K num l) (by omega) (e_pos hL l)
    (le_min h1 (hL.e_le l)) ((min_le_left _ _).trans h2) (min_le_right _ _))⟩⟩

/-- Theorem D (a) with the printed hypothesis follows from Theorem D (a) with the padding string and
the step from a machine to a solver. -/
theorem partAFromThePaddingString : PartAFromThePaddingString := by
  intro hSolver hVariablesA K e C₀ kf num E hyp
  obtain ⟨Idx, inst, S, C₀', Q, hS, hK⟩ := hSolver K e C₀ kf num E hyp
  obtain ⟨M, C', hf, hM⟩ := hVariablesA Idx S (cutNumber K num) C₀' Q hS (cutFraction num) (numberBetween_cut Q hyp.number.1 hK)
  exact ⟨M, 2 * C', hf, conclusion_of_cut Q hyp.levels hyp.number hK hM⟩

end ThmVariables
