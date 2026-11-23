/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Rank
import Nc.Tower.UT

/-!
# The unitriangular group: windows, blocks, reflections
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

/-- The matrix of an element. -/
abbrev mat {h : ℕ} (A : U h) : Matrix (Fin h) (Fin h) F2 := A.1.1

theorem mat_inj {h : ℕ} {A B : U h} (hAB : mat A = mat B) : A = B := Subtype.ext (Subtype.ext hAB)

theorem mat_mul {h : ℕ} (A B : U h) : mat (A * B) = mat A * mat B := rfl

theorem mat_one {h : ℕ} : mat (1 : U h) = 1 := rfl

theorem mat_x {h : ℕ} (j : Fin (h - 1)) : mat (x h j) = 1 + Matrix.single (lo j) (hi j) 1 := rfl

theorem mat_lt {h : ℕ} (A : U h) {i j : Fin h} (hij : j < i) : mat A i j = 0 := (A.2 i j).1 hij

theorem mat_diag {h : ℕ} (A : U h) (i : Fin h) : mat A i i = 1 := (A.2 i i).2

/-- An element from its matrix. -/
def mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : U h :=
  ⟨⟨M, by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro i j hij
      exact h0 i j hij⟩, fun i j => ⟨h0 i j, h1 i⟩⟩

theorem mat_mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : mat (mk M h0 h1) = M := rfl

section Win
variable {p n h : ℕ} (hp : p + n ≤ h)

/-- The place of an index of a window. -/
def we (i : Fin n) : Fin h := ⟨p + i.1, by omega⟩

theorem we_inj {i j : Fin n} : we hp i = we hp j ↔ i = j := by
  simp only [we, Fin.ext_iff]
  omega

theorem we_lt {i j : Fin n} : we hp i < we hp j ↔ i < j := by
  simp only [we, Fin.lt_def]
  omega

/-- The inclusion matrix of a window. -/
def wi : Matrix (Fin h) (Fin n) F2 := Matrix.of fun i a => if i = we hp a then 1 else 0

theorem wi_t_mul : (wi hp)ᵀ * wi hp = 1 := by
  ext a b
  simp [Matrix.mul_apply, wi, Matrix.one_apply, we_inj, eq_comm]

theorem wi_mul_apply (A : Matrix (Fin n) (Fin n) F2) (i j : Fin h) :
    (wi hp * A * (wi hp)ᵀ) i j =
      ∑ b, ∑ a, if i = we hp a ∧ j = we hp b then A a b else 0 := by
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, sum_mul]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  by_cases h1 : i = we hp a <;> by_cases h2 : j = we hp b <;> simp [h1, h2]

theorem wi_mul_we (A : Matrix (Fin n) (Fin n) F2) (a b : Fin n) :
    (wi hp * A * (wi hp)ᵀ) (we hp a) (we hp b) = A a b := by
  rw [wi_mul_apply, sum_eq_single b, sum_eq_single a]
  · simp
  · intro c _ hc
    simp [we_inj, hc.symm]
  · simp
  · intro c _ hc
    simp [we_inj, hc.symm]
  · simp

theorem wi_mul_not (A : Matrix (Fin n) (Fin n) F2) {i : Fin h} (hi : ∀ a, i ≠ we hp a)
    (j : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  rw [wi_mul_apply]
  simp [hi]

theorem wi_mul_not' (A : Matrix (Fin n) (Fin n) F2) {j : Fin h} (hj : ∀ a, j ≠ we hp a)
    (i : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  rw [wi_mul_apply]
  simp [hj]

/-- The matrix of a window element. -/
def wm (A : Matrix (Fin n) (Fin n) F2) : Matrix (Fin h) (Fin h) F2 :=
  wi hp * A * (wi hp)ᵀ + (1 - wi hp * (1 : Matrix (Fin n) (Fin n) F2) * (wi hp)ᵀ)

theorem wm_one : wm hp 1 = 1 := by
  simp [wm]

theorem wm_mul (A B : Matrix (Fin n) (Fin n) F2) : wm hp (A * B) = wm hp A * wm hp B := by
  have hmul : ∀ C D : Matrix (Fin n) (Fin n) F2,
      (wi hp * C * (wi hp)ᵀ) * (wi hp * D * (wi hp)ᵀ) = wi hp * (C * D) * (wi hp)ᵀ := by
    intro C D
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp)ᵀ) (wi hp), wi_t_mul, Matrix.one_mul]
  unfold wm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, hmul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The embedding of the unitriangular group of a window. -/
def win : U n →* U h where
  toFun A := mk (wm hp (mat A))
    (by
      intro i j hij
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hij.ne']
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        by_cases h2 : ∃ b, j = we hp b
        · obtain ⟨b, rfl⟩ := h2
          have hba : b < a := (we_lt hp).1 hij
          rw [wi_mul_we, wi_mul_we, mat_lt A hba, Matrix.one_apply_ne hba.ne']
          simp
        · push_neg at h2
          rw [wi_mul_not' hp _ h2, wi_mul_not' hp _ h2]
          simp
      · push_neg at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
    (by
      intro i
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq]
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        rw [wi_mul_we, wi_mul_we, mat_diag, Matrix.one_apply_eq]
        simp
      · push_neg at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
  map_one' := mat_inj (by rw [mat_mk, mat_one, wm_one, mat_one])
  map_mul' A B := mat_inj (by rw [mat_mk, mat_mul, wm_mul]; rfl)

theorem mat_win (A : U n) : mat (win hp A) = wm hp (mat A) := rfl

/-- The place of a type of a window. -/
def wt (j : Fin (n - 1)) : Fin (h - 1) := ⟨p + j.1, by omega⟩

theorem win_x (j : Fin (n - 1)) : win hp (x n j) = x h (wt hp j) := by
  apply mat_inj
  rw [mat_win, mat_x, mat_x, wm, Matrix.mul_add, Matrix.add_mul]
  have : wi hp * Matrix.single (lo j) (hi j) (1 : F2) * (wi hp)ᵀ =
      Matrix.single (lo (wt hp j)) (hi (wt hp j)) (1 : F2) := by
    ext a b
    rw [wi_mul_apply, Matrix.single_apply, sum_eq_single (hi j), sum_eq_single (lo j)]
    · have h1 : we hp (lo j) = lo (wt hp j) := rfl
      have h2 : we hp (hi j) = hi (wt hp j) := rfl
      rw [h1, h2, Matrix.single_apply_same]
      simp only [eq_comm]
    · intro c _ hc
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.1.symm
    · simp
    · intro c _ hc
      refine sum_eq_zero fun d _ => ?_
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.2.symm
    · simp
  rw [this]
  abel

end Win

section Blocks
variable {a b : ℕ}

theorem hl : 0 + a ≤ a + b := by omega
theorem hr : a + b ≤ a + b := le_rfl

theorem wi_lr : (wi (hl (a := a) (b := b)))ᵀ * wi (hr (a := a) (b := b)) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, Matrix.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  by_cases h1 : k = we (hl (a := a) (b := b)) i
  · have h2 : k ≠ we (hr (a := a) (b := b)) j := by
      rw [h1]
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp [h2]
  · simp [h1]

theorem wi_rl : (wi (hr (a := a) (b := b)))ᵀ * wi (hl (a := a) (b := b)) = 0 := by
  rw [← Matrix.transpose_transpose (wi (hl (a := a) (b := b))), ← Matrix.transpose_mul, wi_lr,
    Matrix.transpose_zero]

theorem wi_add : wi (hl (a := a) (b := b)) * (wi (hl (a := a) (b := b)))ᵀ +
    wi (hr (a := a) (b := b)) * (wi (hr (a := a) (b := b)))ᵀ = 1 := by
  ext i j
  have h1 := wi_mul_apply (hl (a := a) (b := b)) 1 i j
  have h2 := wi_mul_apply (hr (a := a) (b := b)) 1 i j
  rw [Matrix.mul_one] at h1 h2
  rw [Matrix.add_apply, h1, h2]
  clear h1 h2
  by_cases hi : i.1 < a
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hl (a := a) (b := b)) k := ⟨⟨i.1, hi⟩, by simp [we]⟩
    have h3 : ∀ c, we (hl (a := a) (b := b)) k ≠ we (hr (a := a) (b := b)) c := by
      intro c
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp only [h3, false_and, if_false, sum_const_zero, add_zero, we_inj, Matrix.one_apply]
    rw [sum_congr rfl fun b _ => sum_eq_single k (by
      intro c _ hc
      simp [hc.symm]) (by simp)]
    simp only [true_and]
    by_cases hj : ∃ l, j = we (hl (a := a) (b := b)) l
    · obtain ⟨l, rfl⟩ := hj
      rw [sum_eq_single l]
      · simp [we_inj]
      · intro c _ hc
        simp [we_inj, hc.symm]
      · simp
    · push_neg at hj
      simp [hj, (hj k).symm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hr (a := a) (b := b)) k :=
      ⟨⟨i.1 - a, by omega⟩, by simp only [we, Fin.ext_iff]; omega⟩
    have h3 : ∀ c, we (hr (a := a) (b := b)) k ≠ we (hl (a := a) (b := b)) c := by
      intro c
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp only [h3, false_and, if_false, sum_const_zero, zero_add, we_inj, Matrix.one_apply]
    rw [sum_congr rfl fun b _ => sum_eq_single k (by
      intro c _ hc
      simp [hc.symm]) (by simp)]
    simp only [true_and]
    by_cases hj : ∃ l, j = we (hr (a := a) (b := b)) l
    · obtain ⟨l, rfl⟩ := hj
      rw [sum_eq_single l]
      · simp [we_inj]
      · intro c _ hc
        simp [we_inj, hc.symm]
      · simp
    · push_neg at hj
      simp [hj, (hj k).symm]

end Blocks

end Nc.Flag
