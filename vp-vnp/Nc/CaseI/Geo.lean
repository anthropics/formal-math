/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The points of the lower bound for the complete network

In ℝ^k the ends (a, b), a ≠ b, stand at p a b = (e_a − e_b)/(2√2), so that p a b and p b a have distance one.
For a balanced set A ⊂ [k] there is a point x with ‖x‖ = 1/(6√k) such that the distances from p a b to x (a ∈ A)
and to −x (a ∉ A) add up to at most k(k−1)/2 − k/12.
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- e_a − e_b, divided by √2. -/
noncomputable def uvec (a b : Fin k) : EuclideanSpace ℝ (Fin k) :=
  (√2)⁻¹ • (EuclideanSpace.single a 1 - EuclideanSpace.single b 1)

/-- The place of the end (a, b). -/
noncomputable def pvec (a b : Fin k) : EuclideanSpace ℝ (Fin k) := (1 / 2 : ℝ) • uvec a b

theorem uvec_swap (a b : Fin k) : uvec b a = -uvec a b := by
  rw [uvec, uvec, ← smul_neg, neg_sub]

theorem norm_uvec {a b : Fin k} (h : a ≠ b) : ‖uvec a b‖ = 1 := by
  have h1 : ‖(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, PiLp.norm_single, PiLp.norm_single, EuclideanSpace.inner_single_left]
    simp [h]
    norm_num
  have h2 : ‖(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ (Fin k))‖ = √2 := by
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  rw [uvec, norm_smul, h2, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (by positivity)

theorem dist_pvec {a b : Fin k} (h : a ≠ b) : dist (pvec a b) (pvec b a) = 1 := by
  rw [pvec, pvec, uvec_swap a b, dist_eq_norm, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num
  exact norm_uvec h

/-- The distance from half a unit vector. -/
theorem dist_half_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}
    (hu : ‖u‖ = 1) (x : V) : dist ((1 / 2 : ℝ) • u) x ≤ 1 / 2 - inner ℝ u x + ‖x‖ ^ 2 := by
  rw [dist_eq_norm]
  have h1 : ‖(1 / 2 : ℝ) • u - x‖ ^ 2 = 1 / 4 - inner ℝ u x + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hu, real_inner_smul_left, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    ring
  have h2 : 0 ≤ ‖(1 / 2 : ℝ) • u - x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(1 / 2 : ℝ) • u - x‖ - 1 / 2)]

/-- The direction for the set A. -/
noncomputable def vvec (A : Finset (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun a => if a ∈ A then (k : ℝ) - A.card else -(A.card : ℝ)

theorem vvec_apply (A : Finset (Fin k)) (a : Fin k) :
    vvec A a = if a ∈ A then (k : ℝ) - A.card else -(A.card : ℝ) := rfl

/-- |A|·(k − |A|)·k. -/
noncomputable def qnum (A : Finset (Fin k)) : ℝ := A.card * ((k : ℝ) - A.card) * k

theorem sum_ite_card (A : Finset (Fin k)) (y z : ℝ) :
    ∑ a : Fin k, (if a ∈ A then y else z) = A.card * y + ((k : ℝ) - A.card) * z := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (fun a => a ∈ A)
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
  have : ((univ.filter fun a => a ∉ A).card : ℝ) = k - A.card := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast h
  exact this

theorem norm_vvec (A : Finset (Fin k)) : ‖vvec A‖ ^ 2 = qnum A := by
  rw [EuclideanSpace.norm_sq_eq]
  have h1 : ∀ a, ‖vvec A a‖ ^ 2 = if a ∈ A then ((k : ℝ) - A.card) ^ 2 else (A.card : ℝ) ^ 2 := by
    intro a
    rw [Real.norm_eq_abs, sq_abs, vvec_apply]
    split_ifs <;> ring
  simp only [h1]
  rw [sum_ite_card, qnum]
  ring

theorem sum_vvec (A : Finset (Fin k)) : ∑ a, vvec A a = 0 := by
  simp only [vvec_apply]
  rw [sum_ite_card]
  ring

theorem inner_uvec (a b : Fin k) (v : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (uvec a b) v = (√2)⁻¹ * (v a - v b) := by
  rw [uvec, real_inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp

/-- The sign of a. -/
noncomputable def sg (A : Finset (Fin k)) (a : Fin k) : ℝ := if a ∈ A then 1 else -1

theorem sum_sg (A : Finset (Fin k)) : ∑ a, ∑ b, sg A a * (vvec A a - vvec A b) = 2 * qnum A := by
  have h1 : ∀ a, ∑ b, sg A a * (vvec A a - vvec A b) = k * (sg A a * vvec A a) := by
    intro a
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_vvec, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h1]
  rw [← Finset.mul_sum]
  have h2 : ∀ a, sg A a * vvec A a = if a ∈ A then (k : ℝ) - A.card else (A.card : ℝ) := by
    intro a
    rw [sg, vvec_apply]
    split_ifs <;> ring
  simp only [h2]
  rw [sum_ite_card, qnum]
  ring


end Nc.CaseI
