/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Transversal

/-!
# Section "Flat or contracting", step "Rank one": vectors and matrices of rank one

Linear algebra over F₂ for the proof of Theorem thm:alt (Paper/Alternative.lean). The matrix u xᵀ is `vecMulVec u x`. For
nonzero u₁x₁ᵀ and u₂x₂ᵀ, the matrices W, u₁x₁ᵀ, u₂x₂ᵀ are transversal if and only if u₁, u₂ are independent modulo the column space of W, and x₁, x₂ modulo
its row space (`transversal_vec_iff`). The lemma `connect` joins any two vectors outside a subspace of codimension at least 2 by
steps x ↦ x + y with x, y independent modulo the subspace.
-/

open Finset Matrix Submodule

namespace Nc.Flag

variable {m : ℕ} {A : Submodule F2 (Fin m → F2)}

theorem vadd_self (u : Fin m → F2) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

theorem vadd_cancel_left (u v : Fin m → F2) : u + (u + v) = v := by
  rw [← add_assoc, vadd_self, zero_add]

theorem mem_span_singleton_F2 {u v : Fin m → F2} : v ∈ span F2 {u} ↔ v = 0 ∨ v = u := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have h : a = 0 ∨ a = 1 := by
      revert a
      decide
    rcases h with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem mem_sup_span_F2 {u v : Fin m → F2} : v ∈ A ⊔ span F2 {u} ↔ v ∈ A ∨ v + u ∈ A := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases mem_span_singleton_F2.1 hz with rfl | rfl
    · exact Or.inl (by rwa [add_zero])
    · exact Or.inr (by rwa [add_assoc, vadd_self, add_zero])
  · rintro (h | h)
    · exact ⟨v, h, 0, zero_mem _, add_zero _⟩
    · exact ⟨v + u, h, u, mem_span_singleton_self u, by rw [add_assoc, vadd_self, add_zero]⟩

/-- The vectors u₁, u₂ are independent modulo the subspace A: none of u₁, u₂, u₁ + u₂ lies in A. In other words, u₁ is
outside A, and u₂ is outside the span of u₁ with A. -/
def Indep2 (A : Submodule F2 (Fin m → F2)) (u₁ u₂ : Fin m → F2) : Prop := u₁ ∉ A ∧ u₂ ∉ A ∧ u₁ + u₂ ∉ A

theorem indep2_iff {u₁ u₂ : Fin m → F2} : Indep2 A u₁ u₂ ↔ u₁ ∉ A ∧ u₂ ∉ A ⊔ span F2 {u₁} := by
  rw [mem_sup_span_F2, not_or, add_comm u₂ u₁]
  rfl

theorem Indep2.symm {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A u₂ u₁ :=
  ⟨h.2.1, h.1, by rw [add_comm]; exact h.2.2⟩

theorem Indep2.add_right {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A u₁ (u₁ + u₂) :=
  ⟨h.1, h.2.2, by rw [vadd_cancel_left]; exact h.2.1⟩

theorem Indep2.add_left {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A (u₁ + u₂) u₂ :=
  ⟨h.2.2, h.2.1, by rw [add_assoc, vadd_self, add_zero]; exact h.1⟩

theorem exists_notMem (hA : Module.finrank F2 A < m) : ∃ u, u ∉ A := by
  by_contra h
  push Not at h
  have : A = ⊤ := eq_top_iff.2 fun u _ => h u
  rw [this, finrank_top, Module.finrank_fin_fun] at hA
  exact lt_irrefl _ hA

/-- Outside a subspace of codimension at least 2, every vector has a second one that is independent of it. -/
theorem exists_indep2 (hA : Module.finrank F2 A + 2 ≤ m) {u : Fin m → F2} (hu : u ∉ A) : ∃ v, Indep2 A u v := by
  have h1 : Module.finrank F2 (A ⊔ span F2 {u} : Submodule F2 (Fin m → F2)) < m := by
    have h2 := Submodule.finrank_add_le_finrank_add_finrank A (span F2 {u})
    have h3 : Module.finrank F2 (span F2 {u}) ≤ 1 := by
      have := finrank_span_le_card (R := F2) ({u} : Set (Fin m → F2))
      simpa using this
    omega
  obtain ⟨v, hv⟩ := exists_notMem h1
  exact ⟨v, indep2_iff.2 ⟨hu, hv⟩⟩

/-- "Such moves connect all vectors outside" a subspace R of codimension at least 2: a function that does not change when x
becomes x + y, for x, y independent modulo R, has one value outside R. -/
theorem connect {R : Submodule F2 (Fin m → F2)} (hR : Module.finrank F2 R + 2 ≤ m) {g : (Fin m → F2) → ℝ}
    (hg : ∀ x y, Indep2 R x y → g (x + y) = g x) {x x' : Fin m → F2} (hx : x ∉ R) (hx' : x' ∉ R) : g x = g x' := by
  by_cases h : x + x' ∈ R
  · obtain ⟨z, hz⟩ := exists_indep2 hR hx
    have h1 : z + (x + x') ∉ R := fun h2 => hz.2.1 (by simpa using R.sub_mem h2 h)
    have e : x + z + (z + (x + x')) = x' := by
      rw [add_assoc, vadd_cancel_left, vadd_cancel_left]
    have h2 := hg (x + z) (z + (x + x')) ⟨hz.2.2, h1, by rwa [e]⟩
    rw [e] at h2
    rw [h2, hg x z hz]
  · have h2 := hg x (x + x') ⟨hx, h, by rwa [vadd_cancel_left]⟩
    rw [vadd_cancel_left] at h2
    exact h2.symm

/-! ### Matrices u xᵀ -/

theorem vec_ne_zero {u x : Fin m → F2} : vecMulVec u x ≠ 0 ↔ u ≠ 0 ∧ x ≠ 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp at h
  · rintro ⟨hu, hx⟩ h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    have := congrFun (congrFun h i) j
    rw [vecMulVec_apply] at this
    exact (mul_ne_zero hi hj) this

theorem colSpace_vec (u : Fin m → F2) {x : Fin m → F2} (hx : x ≠ 0) : colSpace (vecMulVec u x) = span F2 {u} := by
  have hc : ∀ j, (vecMulVec u x).col j = x j • u := fun j => by
    funext i
    simp [Matrix.col, vecMulVec_apply, mul_comm]
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    rw [hc]
    exact smul_mem _ _ (mem_span_singleton_self u)
  · rintro _ rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    have h1 : x j = 1 := by
      have : ∀ a : F2, a ≠ 0 → a = 1 := by decide
      exact this _ hj
    refine subset_span ⟨j, ?_⟩
    rw [hc, h1, one_smul]

theorem rowSpace_vec {u : Fin m → F2} (hu : u ≠ 0) (x : Fin m → F2) : rowSpace (vecMulVec u x) = span F2 {x} := by
  rw [rowSpace_eq, transpose_vecMulVec, colSpace_vec x hu]

theorem colSpace_zero : colSpace (0 : Mt m) = ⊥ := by
  refine (span_eq_bot).2 ?_
  rintro _ ⟨j, rfl⟩
  rfl

theorem rowSpace_zero : rowSpace (0 : Mt m) = ⊥ := by
  rw [rowSpace_eq, transpose_zero, colSpace_zero]

theorem finrank_colSpace (W : Mt m) : Module.finrank F2 (colSpace W) = W.rank :=
  (Matrix.rank_eq_finrank_span_cols W).symm

theorem finrank_rowSpace (W : Mt m) : Module.finrank F2 (rowSpace W) = W.rank :=
  (Matrix.rank_eq_finrank_span_row W).symm

theorem rank_vec {u x : Fin m → F2} (hu : u ≠ 0) (hx : x ≠ 0) : (vecMulVec u x).rank = 1 := by
  rw [← finrank_colSpace, colSpace_vec u hx, finrank_span_singleton hu]

/-! ### Independent subspaces -/

theorem iSupIndep_two {B C : Submodule F2 (Fin m → F2)} : iSupIndep ![B, C] ↔ Disjoint B C :=
  iSupIndep_pair (i := 0) (j := 1) (by decide) (by decide)

theorem iSupIndep_three {B C D : Submodule F2 (Fin m → F2)} :
    iSupIndep ![B, C, D] ↔ Disjoint B (C ⊔ D) ∧ Disjoint C (B ⊔ D) ∧ Disjoint D (B ⊔ C) := by
  have e0 : (⨆ (j : Fin 3) (_ : j ≠ 0), ![B, C, D] j) = C ⊔ D := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 1 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
    fin_cases j
    · exact absurd rfl hj
    · exact le_sup_left
    · exact le_sup_right
  have e1 : (⨆ (j : Fin 3) (_ : j ≠ 1), ![B, C, D] j) = B ⊔ D := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
    fin_cases j
    · exact le_sup_left
    · exact absurd rfl hj
    · exact le_sup_right
  have e2 : (⨆ (j : Fin 3) (_ : j ≠ 2), ![B, C, D] j) = B ⊔ C := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 1 (by decide) le_rfl))
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
    · exact absurd rfl hj
  rw [iSupIndep_def, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, h1, h2, -⟩
    exact ⟨e0 ▸ h0, e1 ▸ h1, e2 ▸ h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨e0.symm ▸ h0, e1.symm ▸ h1, e2.symm ▸ h2, fun i => i.elim0⟩

theorem disjoint_span_F2 {u : Fin m → F2} (hu : u ≠ 0) : Disjoint A (span F2 {u}) ↔ u ∉ A := by
  rw [disjoint_def]
  constructor
  · intro h hA
    exact hu (h u hA (mem_span_singleton_self u))
  · intro h v hv hv'
    rcases mem_span_singleton_F2.1 hv' with rfl | rfl
    · rfl
    · exact absurd hv h

theorem iSupIndep_of_indep2 {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) :
    iSupIndep ![A, span F2 {u₁}, span F2 {u₂}] := by
  rw [iSupIndep_three]
  refine ⟨disjoint_def.2 fun v hv hv' => ?_, disjoint_def.2 fun v hv hv' => ?_, disjoint_def.2 fun v hv hv' => ?_⟩
  · rcases mem_sup_span_F2.1 hv' with h1 | h1 <;> rcases mem_span_singleton_F2.1 h1 with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hv) h.1
    · have : v = u₂ := by rw [← vadd_cancel_left u₂ v, add_comm u₂ v, h2, add_zero]
      exact absurd (this ▸ hv) h.2.1
    · have : v = u₁ + u₂ := by rw [← h2, add_assoc, vadd_self, add_zero]
      exact absurd (this ▸ hv) h.2.2
  · rcases mem_span_singleton_F2.1 hv with rfl | rfl
    · rfl
    · rcases mem_sup_span_F2.1 hv' with h1 | h1
      · exact absurd h1 h.1
      · exact absurd h1 h.2.2
  · rcases mem_span_singleton_F2.1 hv with rfl | rfl
    · rfl
    · rcases mem_sup_span_F2.1 hv' with h1 | h1
      · exact absurd h1 h.2.1
      · exact absurd (by rwa [add_comm] at h1) h.2.2

theorem indep2_of_iSupIndep {u₁ u₂ : Fin m → F2} (h1 : u₁ ≠ 0) (h2 : u₂ ≠ 0)
    (h : iSupIndep ![A, span F2 {u₁}, span F2 {u₂}]) : Indep2 A u₁ u₂ := by
  obtain ⟨d0, d1, -⟩ := iSupIndep_three.1 h
  rw [disjoint_def] at d0 d1
  have m1 : u₁ ∈ span F2 {u₁} := mem_span_singleton_self u₁
  have m2 : u₂ ∈ span F2 {u₂} := mem_span_singleton_self u₂
  refine ⟨fun hA => h1 (d0 _ hA (mem_sup_left m1)), fun hA => h2 (d0 _ hA (mem_sup_right m2)), fun hA => ?_⟩
  have e := d0 _ hA (add_mem (mem_sup_left m1) (mem_sup_right m2))
  have e' : u₁ = u₂ := by rw [← vadd_cancel_left u₁ u₂, e, add_zero]
  exact h1 (d1 _ m1 (mem_sup_right (e' ▸ m2)))

/-! ### Transversal matrices of rank one -/

theorem transversal_two {W V : Mt m} :
    Transversal ![W, V] ↔ Disjoint (colSpace W) (colSpace V) ∧ Disjoint (rowSpace W) (rowSpace V) := by
  have e1 : (fun k => colSpace (![W, V] k)) = ![colSpace W, colSpace V] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun k => rowSpace (![W, V] k)) = ![rowSpace W, rowSpace V] := by
    funext k
    fin_cases k <;> rfl
  rw [Transversal, e1, e2, iSupIndep_two, iSupIndep_two]

theorem transversal_three {W V V' : Mt m} : Transversal ![W, V, V'] ↔
    iSupIndep ![colSpace W, colSpace V, colSpace V'] ∧ iSupIndep ![rowSpace W, rowSpace V, rowSpace V'] := by
  have e1 : (fun k => colSpace (![W, V, V'] k)) = ![colSpace W, colSpace V, colSpace V'] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun k => rowSpace (![W, V, V'] k)) = ![rowSpace W, rowSpace V, rowSpace V'] := by
    funext k
    fin_cases k <;> rfl
  rw [Transversal, e1, e2]

/-- W and u xᵀ ≠ 0 are transversal if and only if u is outside the column space and x outside the row space of W. -/
theorem transversal_vec {W : Mt m} {u x : Fin m → F2} (hu : u ≠ 0) (hx : x ≠ 0) :
    Transversal ![W, vecMulVec u x] ↔ u ∉ colSpace W ∧ x ∉ rowSpace W := by
  rw [transversal_two, colSpace_vec u hx, rowSpace_vec hu x, disjoint_span_F2 hu, disjoint_span_F2 hx]

/-- W, u₁x₁ᵀ ≠ 0 and u₂x₂ᵀ ≠ 0 are transversal if and only if u₁, u₂ are independent modulo the column space of W and x₁, x₂
modulo its row space. -/
theorem transversal_vec_iff {W : Mt m} {u₁ u₂ x₁ x₂ : Fin m → F2} (h1 : vecMulVec u₁ x₁ ≠ 0)
    (h2 : vecMulVec u₂ x₂ ≠ 0) : Transversal ![W, vecMulVec u₁ x₁, vecMulVec u₂ x₂] ↔
      Indep2 (colSpace W) u₁ u₂ ∧ Indep2 (rowSpace W) x₁ x₂ := by
  obtain ⟨hu₁, hx₁⟩ := vec_ne_zero.1 h1
  obtain ⟨hu₂, hx₂⟩ := vec_ne_zero.1 h2
  rw [transversal_three, colSpace_vec u₁ hx₁, colSpace_vec u₂ hx₂, rowSpace_vec hu₁ x₁, rowSpace_vec hu₂ x₂]
  exact ⟨fun h => ⟨indep2_of_iSupIndep hu₁ hu₂ h.1, indep2_of_iSupIndep hx₁ hx₂ h.2⟩,
    fun h => ⟨iSupIndep_of_indep2 h.1, iSupIndep_of_indep2 h.2⟩⟩

theorem Indep2.ne_zero {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : u₁ ≠ 0 ∧ u₂ ≠ 0 :=
  ⟨fun e => h.1 (e ▸ A.zero_mem), fun e => h.2.1 (e ▸ A.zero_mem)⟩

theorem transversal_of_indep2 {W : Mt m} {u₁ u₂ x₁ x₂ : Fin m → F2} (hu : Indep2 (colSpace W) u₁ u₂)
    (hx : Indep2 (rowSpace W) x₁ x₂) : Transversal ![W, vecMulVec u₁ x₁, vecMulVec u₂ x₂] :=
  (transversal_vec_iff (vec_ne_zero.2 ⟨hu.ne_zero.1, hx.ne_zero.1⟩) (vec_ne_zero.2 ⟨hu.ne_zero.2, hx.ne_zero.2⟩)).2
    ⟨hu, hx⟩

/-- The zero matrix is transversal to every matrix. -/
theorem transversal_zero (V : Mt m) : Transversal ![0, V] := by
  rw [transversal_two, colSpace_zero, rowSpace_zero]
  exact ⟨disjoint_bot_left, disjoint_bot_left⟩

/-- The last two of three transversal matrices are transversal. -/
theorem Transversal.tail {W V V' : Mt m} (h : Transversal ![W, V, V']) : Transversal ![V, V'] := by
  obtain ⟨h1, h2⟩ := transversal_three.1 h
  rw [iSupIndep_three] at h1 h2
  exact transversal_two.2 ⟨h1.2.1.mono_right le_sup_right, h2.2.1.mono_right le_sup_right⟩

/-- The matrix p·dg{i}·q is u xᵀ for the column u of p and the row x of q with the index i. -/
theorem X_singleton (p q : GLM (Fin m)) (i : Fin m) : X p q {i} = vecMulVec ((p : Mt m).col i) ((q : Mt m).row i) := by
  ext a b
  rw [X_apply, sum_singleton, vecMulVec_apply]
  rfl

theorem col_ne_zero (p : GLM (Fin m)) (i : Fin m) : (p : Mt m).col i ≠ 0 := (linearIndependent_col p).ne_zero i

theorem row_ne_zero (q : GLM (Fin m)) (i : Fin m) : (q : Mt m).row i ≠ 0 :=
  (Matrix.linearIndependent_rows_iff_isUnit.2 q.isUnit).ne_zero i

end Nc.Flag
