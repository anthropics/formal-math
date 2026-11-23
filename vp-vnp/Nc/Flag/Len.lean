/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Length functions on a group, matrices over F₂ and averages over pairs of invertible matrices
-/

open Finset Matrix

namespace Nc.Flag

/-- A length function: `dist z (g • z)` for an isometric action. -/
structure Len (G : Type*) [Group G] where
  /-- the value -/
  val : G → ℝ
  one' : val 1 = 0
  inv' : ∀ g, val g⁻¹ = val g
  mul' : ∀ g h, val (g * h) ≤ val g + val h

namespace Len
variable {G : Type*} [Group G] (l : Len G)

theorem nonneg (g : G) : 0 ≤ l.val g := by
  have h := l.mul' g g⁻¹
  rw [mul_inv_cancel, l.one', l.inv'] at h
  linarith

theorem conj (g h : G) : l.val (g * h * g⁻¹) ≤ 2 * l.val g + l.val h := by
  have h1 := l.mul' (g * h) g⁻¹
  have h2 := l.mul' g h
  rw [l.inv'] at h1
  linarith

end Len

/-- Minkowski for square sums. -/
theorem sqrt_sum_le {α : Type*} (s : Finset α) (a b c : α → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (h : ∀ i, c i ≤ a i + b i) :
    √(∑ i ∈ s, c i ^ 2) ≤ √(∑ i ∈ s, a i ^ 2) + √(∑ i ∈ s, b i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, b i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hcs : ∑ i ∈ s, a i * b i ≤ √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, b i ^ 2) := by
    rw [← Real.sqrt_mul hA]
    apply Real.le_sqrt_of_sq_le
    exact sum_mul_sq_le_sq_mul_sq s a b
  calc ∑ i ∈ s, c i ^ 2 ≤ ∑ i ∈ s, (a i + b i) ^ 2 :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (hc i) (h i) 2
    _ = ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
        rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
        linarith

/-- The field with two elements. -/
abbrev F2 := ZMod 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invertible matrices. -/
abbrev GLM (ι : Type*) [Fintype ι] [DecidableEq ι] := (Matrix ι ι F2)ˣ

noncomputable instance : Fintype (GLM ι) := Fintype.ofFinite _

/-- The sum of `f(PMQ)²` over invertible `P`, `Q`. -/
noncomputable def DM (f : Matrix ι ι F2 → ℝ) (M : Matrix ι ι F2) : ℝ :=
  ∑ p : GLM ι, ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2

theorem DM_mul (f : Matrix ι ι F2 → ℝ) (a b : GLM ι) (M : Matrix ι ι F2) :
    DM f ((a : Matrix ι ι F2) * M * (b : Matrix ι ι F2)) = DM f M := by
  unfold DM
  rw [← Equiv.sum_comp (Equiv.mulRight a)
    (fun p : GLM ι => ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun p _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft b)
    (fun q : GLM ι => f (((Equiv.mulRight a p : GLM ι) : Matrix ι ι F2) * M *
      (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.coe_mulLeft, Units.val_mul, Matrix.mul_assoc]

/-- The diagonal idempotent of a set of indices. -/
def dg (S : Finset ι) : Matrix ι ι F2 := Matrix.diagonal fun i => if i ∈ S then 1 else 0

theorem dg_empty : dg (∅ : Finset ι) = 0 := by
  simp [dg]

theorem dg_union {S T : Finset ι} (h : Disjoint S T) : dg (S ∪ T) = dg S + dg T := by
  unfold dg
  rw [Matrix.diagonal_add]
  congr 1
  funext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.1 h hS
    simp [hS, hT]
  · simp [hS]

/-- The unit of a permutation. -/
def permU (σ : Equiv.Perm ι) : GLM ι where
  val := (1 : Matrix ι ι F2).submatrix σ id
  inv := (1 : Matrix ι ι F2).submatrix id σ
  val_inv := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]
  inv_val := by
    rw [Matrix.submatrix_mul_equiv (1 : Matrix ι ι F2) (1 : Matrix ι ι F2) id σ id]
    simp

theorem permU_conj (σ : Equiv.Perm ι) (M : Matrix ι ι F2) :
    (permU σ : Matrix ι ι F2) * M * ((permU σ)⁻¹ : GLM ι) = M.submatrix σ σ := by
  ext i j
  simp [permU, Matrix.mul_apply, Matrix.one_apply]

theorem DM_dg_congr (f : Matrix ι ι F2 → ℝ) {S T : Finset ι} (h : S.card = T.card) :
    DM f (dg S) = DM f (dg T) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, ∀ i, σ i ∈ S ↔ i ∈ T := by
    have e : {i // i ∈ T} ≃ {i // i ∈ S} := Fintype.equivOfCardEq (by simp [h])
    refine ⟨e.extendSubtype, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · by_contra hT
      exact e.extendSubtype_not_mem i hT hi
    · exact e.extendSubtype_mem i hi
  rw [← DM_mul f (permU σ) ((permU σ)⁻¹) (dg S), permU_conj]
  congr 1
  ext i j
  simp only [dg, Matrix.submatrix_apply, Matrix.diagonal_apply, σ.injective.eq_iff, hσ]

theorem DM_dg_le (f : Matrix ι ι F2 → ℝ) (hf : ∀ M, 0 ≤ f M)
    (hadd : ∀ M N, f (M + N) ≤ f M + f N) {S T : Finset ι} (h : Disjoint S T) :
    √(DM f (dg (S ∪ T))) ≤ √(DM f (dg S)) + √(DM f (dg T)) := by
  unfold DM
  simp only [← Fintype.sum_prod_type']
  refine sqrt_sum_le univ _ _ _ (fun _ => hf _) (fun _ => hf _) (fun _ => hf _) fun x => ?_
  rw [dg_union h, Matrix.mul_add, Matrix.add_mul]
  exact hadd _ _

end Nc.Flag
