/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.PDeriv
public import Mathlib.Data.Finsupp.Multiset

/-! # Multi-index factorials and the linear form Σ_v x_v·c_v

Tools for "Expanding the exponentials" (Appendix B, the paragraph on generating functions): α! = ∏_v
α_v! (`fac`), its value at 0 and its change when one variable is added (`fac_zero`,
`fac_add_single`); induction on a multi-index, one variable at a time (`induction_single`);
the identity a·(n + 1) = (n + 1)•a in a ℚ-algebra (`mul_natCast_succ`); and ∂/∂x_i Σ_v x_v·c_v = c_i
(`pderiv_lin`). -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset MvPowerSeries

variable {X A : Type} [CommRing A] [Algebra ℚ A]

/-! ### Multi-indices -/

/-- α! = ∏_v α_v!. -/
noncomputable def fac (α : X →₀ ℕ) : ℚ := α.prod fun _ m => (m.factorial : ℚ)

theorem fac_zero : fac (0 : X →₀ ℕ) = 1 := Finsupp.prod_zero_index

theorem fac_add_single (α : X →₀ ℕ) (i : X) : fac (α + Finsupp.single i 1) = ((α i : ℚ) + 1) * fac α := by
  classical
  have hs1 : (α + Finsupp.single i 1).support ⊆ insert i α.support := by
    refine Finsupp.support_add.trans (union_subset (subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans (singleton_subset_iff.2 (mem_insert_self _ _))
  have key : ∀ β : X →₀ ℕ, β.support ⊆ insert i α.support → fac β = ∏ v ∈ insert i α.support, ((β v).factorial : ℚ) :=
    fun β h => Finsupp.prod_of_support_subset β h _ fun _ _ => by simp
  have h2 : ∏ v ∈ (insert i α.support).erase i, ((((α + Finsupp.single i 1 : X →₀ ℕ)) v).factorial : ℚ) = ∏ v ∈ (insert i α.support).erase i, ((α v).factorial : ℚ) :=
    prod_congr rfl fun v hv => by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (ne_of_mem_erase hv), add_zero]
  rw [key _ hs1, key α (subset_insert _ _), ← mul_prod_erase _ _ (mem_insert_self i _), ← mul_prod_erase _ (fun v => ((α v).factorial : ℚ)) (mem_insert_self i _), h2,
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/-- Induction on a multi-index: one more variable at a time. -/
theorem induction_single {p : (X →₀ ℕ) → Prop} (h0 : p 0) (hs : ∀ α i, p α → p (α + Finsupp.single i 1)) (α : X →₀ ℕ) : p α := by
  induction h : α.degree generalizing α with
  | zero => rw [(Finsupp.degree_eq_zero_iff α).1 h]; exact h0
  | succ n ih =>
    have hne : α.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      rintro rfl
      simp at h
    obtain ⟨i, hi⟩ := hne
    rw [← sub_single_add hi]
    exact hs _ i (ih _ (by have := degree_sub_single hi; omega))

theorem mul_natCast_succ (a : A) (n : ℕ) : a * ((n : A) + 1) = ((n : ℚ) + 1) • a := by
  rw [Algebra.smul_def, map_add, map_natCast, map_one, mul_comm]

/-! ### The linear form Σ_v x_v·c_v -/

omit [Algebra ℚ A] in
/-- ∂/∂x_i Σ_v x_v·c_v = c_i. -/
theorem pderiv_lin (c : X → A) (i : X) : pderiv A i (lin c) = C (c i) := by
  classical
  ext α
  rw [coeff_pderiv, coeff_lin, degree_add_single, coeff_C]
  by_cases h : α = 0
  · subst h
    rw [map_zero, zero_add, if_pos rfl, zero_add, Finsupp.support_single i one_ne_zero, sum_singleton, if_pos rfl]
    simp
  · have h' : α.degree ≠ 0 := fun h0 => h ((Finsupp.degree_eq_zero_iff α).1 h0)
    rw [if_neg (by omega), if_neg h, zero_mul]

end GeneralPieces.GenF
