/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Exact

/-!
# Bounds that follow from one contributing choice

The numbers of units that a party holds at the beginning, and the outcomes of the moves.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

theorem sum_div_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℕ) : ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Nat.add_le_add_left ih _).trans Nat.div_add_div_le_add_div

theorem sum_length_cat {A : ℕ} (X : Fin A → List Γ) : ∑ b, (X b).length = (cat X).length := by
  rw [cat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The number of units of the strings to (or from) all parties. -/
theorem sum_ucount_le {A : ℕ} {X : Option S → Fin A → List Γ} (h : ∑ s, (cat (X s)).length ≤ T) :
    ∑ b, ucount ub (strOf cb fun s => X s b) ≤ (T + A * (Fintype.card S + 1)) * c / ub + A := by
  have e1 : ∀ b, ucount ub (strOf cb fun s => X s b) =
      (∑ s, (X s b).length + (Fintype.card S + 1)) * c / ub + 1 := by
    intro b
    rw [ucount, length_strOf]
  simp only [e1]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine Nat.add_le_add_right ((sum_div_le _ _ _).trans (Nat.div_le_div_right ?_)) _
  rw [← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [sum_length_cat, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_le_add_right h _

end Nc.Cut
