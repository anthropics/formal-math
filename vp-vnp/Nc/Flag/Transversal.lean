/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Para

/-!
# Section "Flat or contracting": transversal matrices

"We call W₁, W₂, … transversal if both their column spaces and their row spaces are independent." The theorem
`transversal_iff` says that this holds if and only if, for some invertible p and q, W_k = p·dg(S_k)·q with disjoint sets S_k.
-/

open Finset Matrix Submodule

namespace Nc.Flag

variable {m : ℕ}

/-- The column space of a matrix. -/
def colSpace (W : Mt m) : Submodule F2 (Fin m → F2) := span F2 (Set.range W.col)

/-- The row space of a matrix. -/
def rowSpace (W : Mt m) : Submodule F2 (Fin m → F2) := span F2 (Set.range W.row)

/-- "We call W₁, W₂, … transversal if both their column spaces and their row spaces are independent." -/
def Transversal {ι : Type} (W : ι → Mt m) : Prop :=
  iSupIndep (fun k => colSpace (W k)) ∧ iSupIndep fun k => rowSpace (W k)

theorem rowSpace_eq (W : Mt m) : rowSpace W = colSpace Wᵀ := by
  rw [rowSpace, colSpace, Matrix.col_transpose]

/-- The transpose of an invertible matrix. -/
def trU (p : GLM (Fin m)) : GLM (Fin m) where
  val := (p : Mt m)ᵀ
  inv := ((p⁻¹ : GLM (Fin m)) : Mt m)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem X_transpose (p q : GLM (Fin m)) (S : Finset (Fin m)) : (X p q S)ᵀ = X (trU q) (trU p) S := by
  rw [X, X, Matrix.transpose_mul, Matrix.transpose_mul, dg, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rfl

theorem X_apply (p q : GLM (Fin m)) (S : Finset (Fin m)) (a b : Fin m) :
    X p q S a b = ∑ i ∈ S, (p : Mt m) a i * (q : Mt m) i b := by
  rw [X, Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ S), Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.sum_eq_zero (s := univ.filter fun i => i ∉ S), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [dg, Matrix.mul_diagonal, if_pos hi, mul_one]
  · intro i hi
    rw [dg, Matrix.mul_diagonal, if_neg (Finset.mem_filter.1 hi).2, mul_zero, zero_mul]

theorem linearIndependent_col (p : GLM (Fin m)) : LinearIndependent F2 (p : Mt m).col :=
  Matrix.linearIndependent_cols_iff_isUnit.2 p.isUnit

/-- The column space of p·dg(S)·q is spanned by the columns of p in S. -/
theorem colSpace_X (p q : GLM (Fin m)) (S : Finset (Fin m)) :
    colSpace (X p q S) = span F2 ((p : Mt m).col '' S) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨b, rfl⟩
    have h : (X p q S).col b = ∑ i ∈ S, (q : Mt m) i b • (p : Mt m).col i := by
      ext a
      simp [Matrix.col, X_apply, mul_comm]
    rw [h]
    exact sum_mem fun i hi => smul_mem _ _ (subset_span (Set.mem_image_of_mem _ hi))
  · rintro _ ⟨i, hi, rfl⟩
    have h : (p : Mt m).col i = ∑ b, ((q⁻¹ : GLM (Fin m)) : Mt m) b i • (X p q S).col b := by
      ext a
      have h1 : (X p q S * ((q⁻¹ : GLM (Fin m)) : Mt m)) a i = (p : Mt m) a i := by
        rw [X, Units.mul_inv_cancel_right, dg, Matrix.mul_diagonal, if_pos (Finset.mem_coe.1 hi), mul_one]
      rw [Matrix.mul_apply] at h1
      simp only [Matrix.col, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← h1]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [SetLike.mem_coe, h]
    exact sum_mem fun b _ => smul_mem _ _ (subset_span (Set.mem_range_self b))

theorem iSupIndep_colSpace {ι : Type} (p q : GLM (Fin m)) (S : ι → Finset (Fin m))
    (hd : ∀ k l, k ≠ l → Disjoint (S k) (S l)) : iSupIndep fun k => colSpace (X p q (S k)) := by
  intro k
  simp only [colSpace_X]
  have h1 : ⨆ (j) (_ : j ≠ k), span F2 ((p : Mt m).col '' (S j : Set (Fin m))) ≤
      span F2 ((p : Mt m).col '' ⋃ (j) (_ : j ≠ k), (S j : Set (Fin m))) :=
    iSup₂_le fun j hj => span_mono (Set.image_mono (Set.subset_iUnion₂ (s := fun j (_ : j ≠ k) => (S j : Set (Fin m))) j hj))
  refine Disjoint.mono_right h1 ((linearIndependent_col p).disjoint_span_image ?_)
  rw [Set.disjoint_iUnion₂_right]
  exact fun j hj => Finset.disjoint_coe.2 (hd k j hj.symm)

theorem exists_perm_comp {α : Type} (f g : α → Fin m) (hf : f.Injective) (hg : g.Injective) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, σ (f k) = g k := by
  classical
  let e : {x // x ∈ Set.range f} ≃ {x // x ∈ Set.range g} :=
    (Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)
  refine ⟨e.extendSubtype, fun k => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f k) (Set.mem_range_self k)]
  have : (Equiv.ofInjective f hf).symm ⟨f k, Set.mem_range_self k⟩ = k :=
    Equiv.ofInjective_symm_apply hf k
  simp [e, this]

/-- Linearly independent vectors are columns, at given places, of an invertible matrix. -/
theorem exists_glm_col {α : Type} (v : α → Fin m → F2) (hv : LinearIndependent F2 v) (ε : α → Fin m)
    (hε : ε.Injective) : ∃ P : GLM (Fin m), ∀ k, (P : Mt m).col (ε k) = v k := by
  classical
  have hs := hv.linearIndepOn_id
  let b := Module.Basis.extend hs
  have : Fintype (hs.extend (Set.subset_univ _)) := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let e₀ : hs.extend (Set.subset_univ _) ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let u : α → hs.extend (Set.subset_univ _) := fun k => ⟨v k, hs.subset_extend _ (Set.mem_range_self k)⟩
  have hu : (fun k => e₀ (u k)).Injective := fun k l h =>
    hv.injective (congrArg Subtype.val (e₀.injective h))
  obtain ⟨σ, hσ⟩ := exists_perm_comp (fun k => e₀ (u k)) ε hu hε
  let c : Module.Basis (Fin m) F2 (Fin m → F2) := b.reindex (e₀.trans σ)
  have hc : ∀ k, c (ε k) = v k := by
    intro k
    have h1 : (e₀.trans σ).symm (ε k) = u k := by
      rw [Equiv.symm_apply_eq]
      exact (hσ k).symm
    rw [Module.Basis.reindex_apply, h1]
    exact Module.Basis.extend_apply_self hs _
  have hA : IsUnit (Matrix.of fun i j => c j i : Mt m) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 c.linearIndependent
  exact ⟨hA.unit, fun k => hc k⟩

/-- Linearly independent vectors are rows, at given places, of an invertible matrix. -/
theorem exists_glm_row {α : Type} (v : α → Fin m → F2) (hv : LinearIndependent F2 v) (ε : α → Fin m)
    (hε : ε.Injective) : ∃ Q : GLM (Fin m), ∀ k, (Q : Mt m).row (ε k) = v k := by
  obtain ⟨P, hP⟩ := exists_glm_col v hv ε hε
  exact ⟨trU P, hP⟩

theorem linearIndependent_sigma {ι : Type} {W : ι → Mt m} (h : iSupIndep fun k => colSpace (W k))
    (p q : ι → GLM (Fin m)) (S : ι → Finset (Fin m)) (hW : ∀ k, W k = X (p k) (q k) (S k)) :
    LinearIndependent F2 fun x : Σ k, S k => (p x.1 : Mt m).col x.2 := by
  have hle : ∀ k, span F2 (Set.range fun i : S k => (p k : Mt m).col i) ≤ colSpace (W k) := by
    intro k
    rw [hW k, colSpace_X]
    refine span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Set.mem_image_of_mem _ i.2
  refine linearIndependent_iUnion_finite (f := fun k (i : S k) => (p k : Mt m).col i)
    (fun k => (linearIndependent_col (p k)).comp _ Subtype.val_injective) fun k t _ hk => ?_
  refine (h k).mono (hle k) (iSup₂_le fun j hj => ?_)
  exact le_iSup₂_of_le (f := fun j (_ : j ≠ k) => colSpace (W j)) j (fun e => hk (e ▸ hj)) (hle j)

/-- Matrices are transversal if and only if in some frame (p, q) they are diagonal, with entries 0 and 1 and with
disjoint supports. -/
theorem transversal_iff {ι : Type} [Fintype ι] (W : ι → Mt m) :
    Transversal W ↔ ∃ (p q : GLM (Fin m)) (S : ι → Finset (Fin m)),
      (∀ k l, k ≠ l → Disjoint (S k) (S l)) ∧ ∀ k, W k = X p q (S k) := by
  classical
  constructor
  · rintro ⟨hc, hr⟩
    choose p q S hW using fun k => exists_X (W k)
    have hv := linearIndependent_sigma hc p q S hW
    have hv' : LinearIndependent F2 fun x : Σ k, S k => (q x.1 : Mt m).row x.2 := by
      simp only [rowSpace_eq] at hr
      exact linearIndependent_sigma hr (fun k => trU (q k)) (fun k => trU (p k)) S
        fun k => by rw [hW k, X_transpose]
    have hcard : Fintype.card (Σ k, S k) ≤ Fintype.card (Fin m) := by
      have := hv.fintype_card_le_finrank
      rw [Module.finrank_fin_fun] at this
      exact this.trans (Fintype.card_fin m).ge
    obtain ⟨ε⟩ := Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨P, hP⟩ := exists_glm_col _ hv ε ε.injective
    obtain ⟨Q, hQ⟩ := exists_glm_row _ hv' ε ε.injective
    refine ⟨P, Q, fun k => univ.image fun i : S k => ε ⟨k, i⟩, fun k l hkl => ?_, fun k => ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx'
      exact hkl (congrArg Sigma.fst (ε.injective hj)).symm
    · ext a b
      rw [hW k, X_apply, X_apply, Finset.sum_image fun i _ j _ h => by
        simpa using ε.injective h, ← Finset.sum_coe_sort (S k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := congrFun (hP ⟨k, i⟩) a
      have h2 := congrFun (hQ ⟨k, i⟩) b
      simp only [Matrix.col, Matrix.row, Matrix.transpose_apply] at h1 h2
      rw [h1, h2]
  · rintro ⟨p, q, S, hd, hW⟩
    have e : W = fun k => X p q (S k) := funext hW
    subst e
    refine ⟨iSupIndep_colSpace p q S hd, ?_⟩
    simp only [rowSpace_eq, X_transpose]
    exact iSupIndep_colSpace _ _ S hd

end Nc.Flag
