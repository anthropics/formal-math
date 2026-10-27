/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import Mathlib.Data.Nat.Choose.Sum

/-! # The sums that are cut off, and their product over good layers

An assignment σ violates v clauses of a layer. The inclusion-exclusion sum Σ_j (−1)^j·C(v, j) is 1
if v = 0 and 0 otherwise; cut off at j ≤ w it is still that
as long as v ≤ w (`Tsg_of_le`). Likewise Σ_{j ≤ w} C(v, j) = 2^v as long as v ≤ w (`Tpl_of_le`). The
layers are good (`Good`) if every assignment that satisfies all
later layers violates at most w clauses of a layer. Then, for EVERY assignment, the product of the
signed sums over the layers is 1 if the assignment satisfies all
layers and 0 otherwise (`prod_Tsg`): at the last layer with a violated clause the sum is exact and
is 0, whatever the earlier factors are. So one evaluation
`trunc n w (Λ :: rest)` is the sum of 2^(number of violated clauses of Λ) over the assignments that
satisfy rest (`trunc_of_good`), and with an empty first layer it
is the number of assignments that satisfy all layers (`trunc_nil_cons`). -/

public section

namespace PaddedDescent.F.Mark

open Finset Groundwork.Prog

/-- The signed sum cut off at w is exact for v ≤ w: it is 1 if v = 0 and 0 otherwise. -/
theorem Tsg_of_le {w v : ℕ} (h : v ≤ w) : Tsg w v = if v = 0 then 1 else 0 := by
  unfold Tsg
  rw [← Int.alternating_sum_range_choose]
  symm
  apply sum_subset (by intro x hx; simp only [mem_range] at *; omega)
  intro x _ hx
  simp only [mem_range, not_lt] at hx
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The unsigned sum cut off at w is exact for v ≤ w: it is 2^v. -/
theorem Tpl_of_le {w v : ℕ} (h : v ≤ w) : Tpl w v = 2 ^ v := by
  unfold Tpl
  have := Nat.sum_range_choose v
  rw [← Nat.cast_sum]
  have h2 : ∑ j ∈ range (w + 1), v.choose j = ∑ j ∈ range (v + 1), v.choose j := by
    symm
    apply sum_subset (by intro x hx; simp only [mem_range] at *; omega)
    intro x _ hx
    simp only [mem_range, not_lt] at hx
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [h2, this]; norm_cast

/-- σ violates no clause of L exactly if every clause of L has a true literal. -/
theorem nvio_eq_zero {σ : ℕ → Bool} {L : Fml} : nvio σ L = 0 ↔ ∀ C ∈ L, ∃ l ∈ C, σ l.1 = l.2 := by
  simp only [nvio, List.countP_eq_zero, vio, List.all_eq_true, not_forall, bne_iff_ne, ne_eq, not_not, exists_prop]

/-- For good layers and every assignment, the product of the signed sums is 1 if the assignment
satisfies all layers and 0 otherwise. -/
theorem prod_Tsg {n w : ℕ} (σ : Fin n → Bool) : ∀ {Ls : List Fml}, Good n w Ls →
    (Ls.map fun L => Tsg w (nvio (ext σ) L)).prod = if ∀ L ∈ Ls, nvio (ext σ) L = 0 then 1 else 0
  | [], _ => by simp
  | Λ :: rest, h => by
    rw [List.map_cons, List.prod_cons, prod_Tsg σ h.2]
    by_cases hr : ∀ L ∈ rest, nvio (ext σ) L = 0
    · rw [if_pos hr, mul_one, Tsg_of_le (h.1 σ hr)]
      by_cases h0 : nvio (ext σ) Λ = 0
      · rw [if_pos h0, if_pos]
        intro L hL
        rcases List.mem_cons.1 hL with rfl | hL
        · exact h0
        · exact hr L hL
      · rw [if_neg h0, if_neg]
        exact fun hall => h0 (hall Λ List.mem_cons_self)
    · rw [if_neg hr, mul_zero, if_neg]
      exact fun hall => hr fun L hL => hall L (List.mem_cons_of_mem _ hL)

/-- One evaluation on good layers: the sum of 2^(number of violated clauses of the first layer) over
the assignments that satisfy the other layers. -/
theorem trunc_of_good {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : Good n w (Λ :: rest)) :
    trunc n w (Λ :: rest) = ∑ σ : Fin n → Bool, if ∀ L ∈ rest, nvio (ext σ) L = 0 then (2 : ℤ) ^ nvio (ext σ) Λ else 0 := by
  unfold trunc
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [List.headD_cons, List.tail_cons]
  rw [prod_Tsg σ h.2]
  by_cases hr : ∀ L ∈ rest, nvio (ext σ) L = 0
  · rw [if_pos hr, if_pos hr, mul_one, Tpl_of_le (h.1 σ hr)]
  · rw [if_neg hr, if_neg hr, mul_zero]

/-- With an empty first layer, one evaluation on good layers is the number of assignments that
satisfy all layers. -/
theorem trunc_nil_cons {n w : ℕ} {Ls : List Fml} (h : Good n w Ls) :
    trunc n w ([] :: Ls) = ((univ.filter fun σ : Fin n → Bool => ∀ L ∈ Ls, nvio (ext σ) L = 0).card : ℤ) := by
  rw [trunc_of_good (Λ := []) ⟨fun σ _ => by simp [nvio], h⟩]
  simp [nvio]

end PaddedDescent.F.Mark

namespace PaddedDescent.F

end PaddedDescent.F
