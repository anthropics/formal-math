/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Len

/-!
# Blow-ups `N ↦ N ⊗ 1` of matrices over F₂
-/

open Finset Matrix

namespace Nc.Flag

variable {μ κ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- The inclusion matrix of an embedding. -/
def inc (e : μ × κ ↪ ι) : Matrix ι (μ × κ) F2 := fun i x => if i = e x then 1 else 0

theorem inc_t_mul (e : μ × κ ↪ ι) : (inc e)ᵀ * inc e = 1 := by
  ext x y
  simp [Matrix.mul_apply, inc, Matrix.one_apply, eq_comm]

theorem inc_mul_diag (e : μ × κ ↪ ι) (T : Finset (μ × κ)) :
    inc e * dg T * (inc e)ᵀ = dg (T.map e) := by
  ext i j
  simp only [Matrix.mul_apply, inc, dg, Matrix.transpose_apply, Matrix.diagonal_apply,
    Finset.mem_map]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : ∃ x, e x = i
  · obtain ⟨x, rfl⟩ := hi
    by_cases hj : ∃ y, e y = j
    · obtain ⟨y, rfl⟩ := hj
      by_cases hxy : x = y
      · subst hxy
        simp [e.injective.eq_iff]
      · simp [e.injective.eq_iff, hxy]
    · have : ∀ y, j ≠ e y := fun y h => hj ⟨y, h.symm⟩
      have h2 : e x ≠ j := fun h => hj ⟨x, h⟩
      simp [this, h2]
  · have h1 : ∀ y, i ≠ e y := fun y h => hi ⟨y, h.symm⟩
    have h2 : ∀ y, e y ≠ i := fun y h => hi ⟨y, h⟩
    simp only [h1, if_false, sum_const_zero, ite_self]
    split_ifs with h3 h4
    · obtain ⟨a, -, ha⟩ := h4
      exact absurd ha (h2 a)
    · rfl
    · rfl

/-- The blow-up of a matrix along an embedding. -/
def blow (e : μ × κ ↪ ι) (N : Matrix μ μ F2) : Matrix ι ι F2 :=
  inc e * (Matrix.kroneckerMap (· * ·) N (1 : Matrix κ κ F2)) * (inc e)ᵀ

theorem blow_add (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M + N) = blow e M + blow e N := by
  unfold blow
  rw [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

theorem blow_mul (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M * N) = blow e M * blow e N := by
  unfold blow
  have h : Matrix.kroneckerMap (· * ·) (M * N) (1 : Matrix κ κ F2) =
      Matrix.kroneckerMap (· * ·) M (1 : Matrix κ κ F2) *
        Matrix.kroneckerMap (· * ·) N (1 : Matrix κ κ F2) := by
    have := Matrix.mul_kronecker_mul M N (1 : Matrix κ κ F2) (1 : Matrix κ κ F2)
    rw [Matrix.mul_one] at this
    exact this
  rw [h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((inc e)ᵀ) (inc e), inc_t_mul, Matrix.one_mul]

theorem blow_dg (e : μ × κ ↪ ι) (T : Finset μ) :
    blow e (dg T) = dg ((T ×ˢ (univ : Finset κ)).map e) := by
  unfold blow
  rw [← inc_mul_diag]
  congr 2
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.kroneckerMap_apply, dg, Matrix.diagonal_apply, Matrix.one_apply,
    Finset.mem_product, Finset.mem_univ, and_true, Prod.mk.injEq]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- The complement of the blow-up of one. -/
def blowC (e : μ × κ ↪ ι) : Matrix ι ι F2 := 1 - blow e 1

theorem blow_mul_blowC (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blow e M * blowC e = 0 := by
  rw [blowC, Matrix.mul_sub, ← blow_mul, Matrix.mul_one, Matrix.mul_one, sub_self]

theorem blowC_mul_blow (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blowC e * blow e M = 0 := by
  rw [blowC, Matrix.sub_mul, ← blow_mul, Matrix.one_mul, Matrix.one_mul, sub_self]

theorem blowC_sq (e : μ × κ ↪ ι) : blowC e * blowC e = blowC e := by
  conv_lhs => rw [blowC, Matrix.sub_mul, ← blowC, blow_mul_blowC, Matrix.one_mul, sub_zero]

theorem blow_unit_aux (e : μ × κ ↪ ι) {M N : Matrix μ μ F2} (h : M * N = 1) :
    (blow e M + blowC e) * (blow e N + blowC e) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ← blow_mul, h, blow_mul_blowC,
    blowC_mul_blow, blowC_sq, add_zero, zero_add, blowC]
  abel

/-- Blow-ups of invertible matrices, extended by the identity. -/
def blowU (e : μ × κ ↪ ι) (p : GLM μ) : GLM ι where
  val := blow e p + blowC e
  inv := blow e (p⁻¹ : GLM μ) + blowC e
  val_inv := blow_unit_aux e (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  inv_val := blow_unit_aux e (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

theorem blowU_mul (e : μ × κ ↪ ι) (p q : GLM μ) (M : Matrix μ μ F2) :
    (blowU e p : Matrix ι ι F2) * blow e M * (blowU e q : Matrix ι ι F2) =
      blow e ((p : Matrix μ μ F2) * M * (q : Matrix μ μ F2)) := by
  show (blow e p + blowC e) * blow e M * (blow e q + blowC e) = _
  rw [Matrix.add_mul, blowC_mul_blow, add_zero, Matrix.mul_add, ← blow_mul, blow_mul_blowC,
    add_zero, ← blow_mul]

/-- The contraction hypothesis of the contracting case for a function on a group: along every additive map
from μ×μ matrices, full rank is only `s²` times as far as rank one. -/
def Contr {G : Type*} [Group G] (l : Len G) (μ : ℕ) (s : ℝ) : Prop :=
  ∀ τ : Matrix (Fin μ) (Fin μ) F2 → G, (∀ M N, τ (M + N) = τ M * τ N) →
    ∀ i, DM (fun M => l.val (τ M)) (dg univ) ≤ s ^ 2 * DM (fun M => l.val (τ M)) (dg {i})

theorem DM_blow (e : μ × κ ↪ ι) (f : Matrix ι ι F2 → ℝ) (M : Matrix μ μ F2) :
    ∑ p : GLM ι, ∑ q : GLM ι,
      DM (fun N => f ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2))) M =
      (Fintype.card (GLM μ) : ℝ) ^ 2 * DM f (blow e M) := by
  have h : ∀ a b : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 = DM f (blow e M) := by
    intro a b
    rw [← blowU_mul, ← DM_mul f (blowU e a) (blowU e b) (blow e M)]
    rfl
  simp only [DM] at h ⊢
  calc _ = ∑ p : GLM ι, ∑ a : GLM μ, ∑ q : GLM ι, ∑ b : GLM μ,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_congr rfl fun p _ => sum_comm
    _ = ∑ a : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι, ∑ b : GLM μ,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_comm
    _ = ∑ a : GLM μ, ∑ p : GLM ι, ∑ b : GLM μ, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 :=
        sum_congr rfl fun a _ => sum_congr rfl fun p _ => sum_comm
    _ = ∑ a : GLM μ, ∑ b : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_congr rfl fun a _ => sum_comm
    _ = _ := by
      rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => h a b]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      ring

variable {G : Type*} [Group G]

theorem DM_digit (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) (e : Fin m × κ ↪ ι) (i : Fin m) :
    DM (fun M => l.val (τ M)) (dg ((univ : Finset (Fin m × κ)).map e)) ≤
      s ^ 2 * DM (fun M => l.val (τ M)) (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e)) := by
  have h0 : (0 : ℝ) < (Fintype.card (GLM (Fin m)) : ℝ) ^ 2 := by
    have : 0 < Fintype.card (GLM (Fin m)) := Fintype.card_pos
    positivity
  refine le_of_mul_le_mul_left ?_ h0
  rw [mul_left_comm, ← univ_product_univ, ← blow_dg, ← blow_dg, ← DM_blow, ← DM_blow, mul_sum]
  refine sum_le_sum fun p _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun q _ => ?_
  exact hC (fun N => τ ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2)))
    (fun M N => by rw [blow_add, Matrix.mul_add, Matrix.add_mul, hτ]) i

end Nc.Flag
