/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Determinants that factor, and the expansion of `det [[X, AΛB],[B'ΛA', Y]]`

Rows and columns fall into two groups. For every set `T` of inner indices the expansion has a term
`∏_T λ · α_T · β_T`, where `α_T` depends on `X, A, A'` and `β_T` on `Y, B, B'` only; it vanishes unless
`T` has as many elements on the left as on the right.
-/

namespace Nc.Cross

open Matrix Finset

section split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The matrix with the entries of `N₁` in the rows and columns of the first group, those of `N₂` in the rows
and columns of the second, and zeros elsewhere. -/
def glueMat (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] (N₁ N₂ : Matrix ι ι R) :
    Matrix ι ι R :=
  of fun i j => if rg i then (if cg j then N₁ i j else 0) else (if cg j then 0 else N₂ i j)

theorem det_glue_zero_of_lt (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter cg).card < (univ.filter rg).card) :
    (glueMat rg cg N₁ N₂).det = 0 := by
  rw [det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hj⟩ : ∃ j, rg (σ j) ∧ ¬ cg j := by
    by_contra hcon
    push Not at hcon
    refine absurd h (not_lt.2 ?_)
    refine Finset.card_le_card_of_injOn (fun i => σ.symm i) ?_ (fun i _ j _ hij => σ.symm.injective hij)
    intro i hi
    have hi' : rg i := (Finset.mem_filter.1 hi).2
    have := hcon (σ.symm i) (by simpa using hi')
    simpa using this
  have : ∏ i, glueMat rg cg N₁ N₂ (σ i) i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [glueMat, hj.1, hj.2])
  rw [this, smul_zero]

theorem det_glue_zero (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter rg).card ≠ (univ.filter cg).card) :
    (glueMat rg cg N₁ N₂).det = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [← det_transpose]
    have : (glueMat rg cg N₁ N₂)ᵀ = glueMat cg rg N₁ᵀ N₂ᵀ := by
      ext i j
      by_cases h1 : cg i <;> by_cases h2 : rg j <;> simp [glueMat, h1, h2]
    rw [this]
    exact det_glue_zero_of_lt cg rg _ _ h
  · exact det_glue_zero_of_lt rg cg _ _ h

/-- A glued determinant is a product. -/
theorem det_glue (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] :
    ∃ (α β : Matrix ι ι R → R), ∀ N₁ N₂, (glueMat rg cg N₁ N₂).det = α N₁ * β N₂ := by
  by_cases h : (univ.filter rg).card = (univ.filter cg).card
  swap
  · exact ⟨fun _ => 0, fun _ => 0, fun N₁ N₂ => by rw [det_glue_zero _ _ _ _ h, zero_mul]⟩
  have hc : Fintype.card {i // cg i} = Fintype.card {i // rg i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, h]
  let e : {i // cg i} ≃ {i // rg i} := Fintype.equivOfCardEq hc
  let τ : Equiv.Perm ι := Equiv.extendSubtype e
  have h1 : ∀ i, cg i → rg (τ i) := fun i hi => Equiv.extendSubtype_mem e i hi
  have h2 : ∀ i, ¬ cg i → ¬ rg (τ i) := fun i hi => Equiv.extendSubtype_not_mem e i hi
  refine ⟨fun N₁ => ((Equiv.Perm.sign τ : ℤ) : R) * (toSquareBlockProp (N₁.submatrix τ id) cg).det,
    fun N₂ => (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det, fun N₁ N₂ => ?_⟩
  have hp := det_permute τ (glueMat rg cg N₁ N₂)
  have hs : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have hb : ((glueMat rg cg N₁ N₂).submatrix τ id).det =
      (toSquareBlockProp (N₁.submatrix τ id) cg).det *
        (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det := by
    rw [twoBlockTriangular_det _ cg]
    · congr 1
      · congr 1
        ext i j
        simp [toSquareBlockProp, glueMat, h1 i i.2, j.2]
      · congr 1
        ext i j
        simp [toSquareBlockProp, glueMat, h2 i i.2, j.2]
    · intro i hi j hj
      simp [glueMat, h2 i hi, hj]
  rw [hb] at hp
  linear_combination (-(glueMat rg cg N₁ N₂).det) * hs - ((Equiv.Perm.sign τ : ℤ) : R) * hp

end split

section expand

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]

/-- Expansion of a determinant in the rows `λ_r v_r + e_r`. -/
theorem det_expand (P : n → (n ⊕ m) → R) (l : m → R) (v e : m → (n ⊕ m) → R) :
    (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det =
      ∑ T : Finset m, (∏ r ∈ T, l r) *
        (of (Sum.elim P (T.piecewise v e)) : Matrix (n ⊕ m) (n ⊕ m) R).det := by
  let g : MultilinearMap R (fun _ : m => (n ⊕ m) → R) R :=
    (MultilinearMap.currySum (detRowAlternating (n := n ⊕ m) (R := R)).toMultilinearMap) P
  have hg : ∀ w : m → (n ⊕ m) → R, g w = (of (Sum.elim P w) : Matrix (n ⊕ m) (n ⊕ m) R).det := by
    intro w
    rfl
  have h1 := g.map_add_univ (fun r => l r • v r) e
  have h2 : ∀ T : Finset m, g (T.piecewise (fun r => l r • v r) e) =
      (∏ r ∈ T, l r) * g (T.piecewise v e) := by
    intro T
    have := g.map_piecewise_smul l (T.piecewise v e) T
    rw [smul_eq_mul] at this
    rw [← this]
    congr 1
    ext r : 1
    by_cases hr : r ∈ T <;> simp [hr]
  calc (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det
      = g ((fun r => l r • v r) + e) := rfl
    _ = ∑ T : Finset m, g (T.piecewise (fun r => l r • v r) e) := h1
    _ = _ := Finset.sum_congr rfl fun T _ => by rw [h2, hg]

end expand

end Nc.Cross
