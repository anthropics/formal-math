/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import SparsificationLemma.StepSparsify
import SparsificationLemma.Side
import SparsificationLemma.One
import SparsificationLemma.Cal.Facts
import StepSparsify.CalLeaves
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Main
import ClauseBound.Alg.Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Theorem D (a) along the printed Step 5: the tree, its outputs, and the input

Four statements of proof/variables/RecursionToBound/Defs.lean are proved here.
* `walkTreeIsSparsify`. The tree that `countAll` walks starts with the n clauses xᵢ ∨ ¬xᵢ on the
  side list; the outputs do not change if it starts with the empty side list
  (`SparsificationLemma.stOutputsSame`). By `SparsificationLemma.Cal.factI` the procedure has
  stopped on every path after `Cal.depthC` steps, a bound computed from Calabro's thresholds, so
  cutting the paths later gives the
  same leaves (`StepSparsify.leaves_eq_of_le`).
* `outputsAreFew`. ε = min(r, 1) lies in [e, 2e] and is at most 1, because e ≤ r ≤ 2e and e ≤ 1; the
  bound 2^(εn) on the number of outputs is `SparsificationLemma.StepSparsify.outputs_le`.
* `ownDeltaIsBounded`. The general theorem on the sparsification at Calabro's thresholds
  (`SparsificationLemma.Cal.gen`) says that a variable occurs in at most 2·(θ₀ + … + θ_(k−1)) + 2
  clauses of an output; Δ is the larger of 2 and the largest of these numbers.
* `widthOnTheCode`. The reader gives n and the clauses back (`ClauseBound.Alg.Decode.stDecM`);
  clauses keep their lengths; and `Q.pick` at ⌊n^(1/17)⌋ gives the level of n
  (`VariableBound.VariablesA.pick_eq`, `VariableBound.VariablesA.level_eq_pick`).
Correct.lean uses the lemmas on ε in the namespace `RecursionToBound.Eps`. Numbers.lean has lemmas
of the same kind under other names (`epsOf_pos`, `epsOf_le_one`, `epsOf_cast`), which Exponent.lean
uses. -/

public section

namespace RecursionToBound

open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)

/-! ### The number ε -/

namespace Eps

/-- ε is positive if numerator and denominator of r are. -/
theorem pos {r : ℕ × ℕ} (h1 : 0 < r.1) (h2 : 0 < r.2) : 0 < epsOf r :=
  lt_min (div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)) one_pos

/-- ε ≤ 1. -/
theorem le_one (r : ℕ × ℕ) : epsOf r ≤ 1 := min_le_right _ _

/-- ε as a real number: min(r, 1). -/
theorem cast (r : ℕ × ℕ) : ((epsOf r : ℚ) : ℝ) = min ((r.1 : ℝ) / (r.2 : ℝ)) 1 := by
  rw [epsOf, Rat.cast_min, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, Rat.cast_one]

/-- If 0 < e ≤ r, then numerator and denominator of r are positive. -/
theorem pos_of_le {r : ℕ × ℕ} {e : ℝ} (he : 0 < e) (h : e ≤ (r.1 : ℝ) / (r.2 : ℝ)) : 0 < r.1 ∧ 0 < r.2 := by
  have hp : 0 < (r.1 : ℝ) / (r.2 : ℝ) := lt_of_lt_of_le he h
  constructor
  · rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · rw [h0, Nat.cast_zero, zero_div] at hp
      exact absurd hp (lt_irrefl _)
    · exact h0
  · rcases Nat.eq_zero_or_pos r.2 with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero] at hp
      exact absurd hp (lt_irrefl _)
    · exact h0

/-- α ≥ 1 for k ≥ 3 and 0 < r. -/
theorem one_le_alpha {k : ℕ} {r : ℕ × ℕ} (hk : 3 ≤ k) (h1 : 0 < r.1) (h2 : 0 < r.2) : 1 ≤ Cal.alphaC k (epsOf r) :=
  SparsificationLemma.StepSparsify.one_le_alpha hk (pos h1 h2) (le_one r)

end Eps

/-! ### The tree and its outputs -/

/-- The outputs at the leaves of the tree that `countAll` walks are the outputs of
`SparsificationLemma.Cal.sparsify`. -/
theorem walkTreeIsSparsify : WalkTreeIsSparsify := by
  intro k n D r ψ hk h1 h2 hψ hD
  have hα := Eps.one_le_alpha hk h1 h2
  have hψ' : IsKCNF k n (noTaut ψ) := (stNoTaut ψ).2.1 k n hψ
  have e : tree (Cal.thetaC (Cal.alphaC k (epsOf r))) k D (noTaut ψ) = tree (Cal.thetaC (Cal.alphaC k (epsOf r))) k (Cal.depthC (Cal.alphaC k (epsOf r)) k n) (noTaut ψ) :=
    _root_.StepSparsify.leaves_eq_of_le _ _ D _ hD (Cal.factI (Cal.alphaC k (epsOf r)) k n (noTaut ψ) hα (by omega) hψ')
  unfold thresholds
  rw [stOutputsSame, outputs, e]
  rfl

/-- «… each of the at most 2^(2en) outputs», and e ≤ ε ≤ 2e, ε ≤ 1. -/
theorem outputsAreFew : OutputsAreFew := by
  intro k n r e ψ hk he0 he1 hlo hhi hψ
  obtain ⟨h1, h2⟩ := Eps.pos_of_le he0 hlo
  have hc := Eps.cast r
  have a1 : e ≤ ((epsOf r : ℚ) : ℝ) := by
    rw [hc]
    exact le_min hlo he1
  have a2 : ((epsOf r : ℚ) : ℝ) ≤ 2 * e := by
    rw [hc]
    exact (min_le_left _ _).trans hhi
  have a3 : ((epsOf r : ℚ) : ℝ) ≤ 1 := by
    rw [hc]
    exact min_le_right _ _
  exact ⟨a1, a2, a3, SparsificationLemma.StepSparsify.outputs_le hk (Eps.pos h1 h2) (Eps.le_one r) hψ,
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right a2 (Nat.cast_nonneg n))⟩

/-- In every output a variable occurs in at most `occBound k r` clauses, so the Δ of the output is
at most this number. -/
theorem ownDeltaIsBounded : OwnDeltaIsBounded := by
  intro k n r ψ hk h1 h2 hψ Φ hΦ
  have hα := Eps.one_le_alpha hk h1 h2
  have hψ' : IsKCNF k n (noTaut ψ) := (stNoTaut ψ).2.1 k n hψ
  have h : ∀ v, occN Φ v ≤ occBound k r := ((Cal.gen hα (by omega) hψ').2.2.1 Φ hΦ).2
  have h2 : 2 ≤ occBound k r := by
    unfold occBound
    omega
  exact max_le h2 (Finset.sup_le fun v _ => h v)

/-! ### What the function reads from the code of (k, φ) -/

/-- «the largest number of literals in a clause, or 3» can be read from the formula with natural
numbers as variables. -/
theorem widthOr3F_toN {n : ℕ} (φ : CNF n) : widthOr3F (Decode.toN φ) = widthOr3 φ := by
  unfold widthOr3F widthOr3
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    have e1 : SparsificationLemma.StepSparsify.widthOf (Decode.toN (C :: φ)) = max C.length (SparsificationLemma.StepSparsify.widthOf (Decode.toN φ)) := by
      simp [SparsificationLemma.StepSparsify.widthOf, Decode.toN]
    rw [e1, List.map_cons, List.foldr_cons, ← ih]
    omega

/-- On the code of (k, φ) the function reads this k, the number for the level of n, and the index of
that level. -/
theorem widthOnTheCode : WidthOnTheCode := by
  refine ⟨fun k n φ hk hφ => ?_, fun Idx _ S e C₀ Q num k n l φ hk hφ hl => ?_⟩
  · obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
    rw [widthU, hdec]
    exact widthOr3F_toN φ
  · obtain ⟨-, hdec⟩ := Decode.stDecM k n φ hk hφ.1
    have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
    have hi : idxU Q.pick (SatM.enc k φ) = Q.idx l := by rw [idxU, hn, Q.pick_idx, VariableBound.VariablesA.level_eq_pick Q hl]
    exact ⟨by rw [numU, hi, hn, VariableBound.VariablesA.pick_eq Q hl], hi⟩

end RecursionToBound
