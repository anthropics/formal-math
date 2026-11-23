/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The permanent under renaming and padding
-/

namespace Nc

open Finset

variable {R : Type*} [CommSemiring R]
variable {C D E : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem permanent_submatrix_equiv (e : D ≃ C) (M : Matrix C C R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv e.permCongr _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Matrix.submatrix_apply, Equiv.permCongr_apply]

/-- A diagonal of ones does not change the permanent. -/
theorem permanent_pad (M : Matrix C C R) :
    (Matrix.fromBlocks M 0 0 (1 : Matrix E E R)).permanent = M.permanent := by
  unfold Matrix.permanent
  symm
  refine Finset.sum_of_injOn (fun τ => Equiv.Perm.sumCongr τ 1) ?_ ?_ ?_ ?_
  · intro τ _ τ' _ e
    have := Equiv.Perm.sumCongrHom_injective (α := C) (β := E) (a₁ := (τ, 1)) (a₂ := (τ', 1)) e
    exact (Prod.mk.inj this).1
  · intro τ _
    simp
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hfix : ∀ k : E, σ (Sum.inr k) = Sum.inr k := by
      intro k
      by_contra hk
      apply hne
      refine Finset.prod_eq_zero (mem_univ (Sum.inr k)) ?_
      rcases hs : σ (Sum.inr k) with c | e
      · rw [Matrix.fromBlocks_apply₁₂]
        rfl
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_ne]
        rintro rfl
        exact hk hs
    have hmaps : Set.MapsTo σ (Set.range (Sum.inl : C → C ⊕ E)) (Set.range Sum.inl) := by
      rintro _ ⟨c, rfl⟩
      rcases hs : σ (Sum.inl c) with c' | e
      · exact ⟨c', rfl⟩
      · have := σ.injective (hs.trans (hfix e).symm)
        cases this
    obtain ⟨⟨τ, κ⟩, rfl⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    have : κ = 1 := by
      ext k
      have := hfix k
      simpa using this
    subst this
    exact ⟨τ, by simp, rfl⟩
  · intro τ _
    rw [Fintype.prod_sum_type]
    simp

/-- A square matrix sits in every larger one with the same permanent. -/
theorem exists_permanent_fin (M : Matrix C C R) {S : ℕ} (hS : Fintype.card C ≤ S) :
    ∃ M' : Matrix (Fin S) (Fin S) R, M'.permanent = M.permanent ∧
      ∀ i j, (M' i j = 0 ∨ M' i j = 1) ∨ ∃ c d, M' i j = M c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hS
  let e : Fin (Fintype.card C + k) ≃ C ⊕ Fin k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _))
  refine ⟨(Matrix.fromBlocks M 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e, ?_, fun i j => ?_⟩
  · rw [permanent_submatrix_equiv, permanent_pad]
  · rw [Matrix.submatrix_apply]
    rcases e i with c | a <;> rcases e j with d | b
    · exact Or.inr ⟨c, d, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

end Nc
