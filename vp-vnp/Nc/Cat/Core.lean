/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Complete CAT(0) spaces: definitions

`Cat.CN X`: `X` is complete and any two points have a midpoint with the CN inequality.
What follows from the defining inequalities of barycentres (`IsBary`) and of points at
fraction `t` (`IsPt`) in any metric space. The facts on CAT(0) spaces are Lemma lem:toolkit, in Paper/Toolkit.lean.
-/

open Filter Topology

namespace Cat

/-- Complete CAT(0) spaces: complete, and every two points have a midpoint with the
inequality of Bruhat and Tits. -/
class CN (X : Type*) [MetricSpace X] : Prop extends CompleteSpace X where
  exists_mid : ∀ x v : X, ∃ m : X, ∀ z : X,
    dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4

variable {X : Type*} [MetricSpace X]

section min
variable [CN X]

/-- The midpoint. -/
noncomputable def mid (x v : X) : X := Classical.choose (CN.exists_mid x v)

theorem cn (x v z : X) :
    dist z (mid x v) ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 :=
  Classical.choose_spec (CN.exists_mid x v) z

theorem dist_mid_left (x v : X) : dist x (mid x v) = dist x v / 2 := by
  have h1 := cn x v x
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_self] at h1 h2
  rw [dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3
  have ha : dist x (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

theorem dist_mid_right (x v : X) : dist (mid x v) v = dist x v / 2 := by
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_mid_left] at h3
  rw [dist_self, dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3 ⊢
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

end min

/-! ### Barycentres -/

section bary
variable {ι : Type*} [Fintype ι]

/-- `b` is the barycentre of the points `x i` with weights `w i` (of any total weight):
the inequality of variances. -/
def IsBary (w : ι → ℝ) (x : ι → X) (b : X) : Prop :=
  ∀ y, ∑ i, w i * dist b (x i) ^ 2 + (∑ i, w i) * dist y b ^ 2 ≤ ∑ i, w i * dist y (x i) ^ 2

theorem IsBary.unique {w : ι → ℝ} {x : ι → X} {b b' : X} (hw : 0 < ∑ i, w i)
    (h : IsBary w x b) (h' : IsBary w x b') : b = b' := by
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm] at h1
  have h3 : (∑ i, w i) * dist b b' ^ 2 ≤ 0 := by linarith
  have h4 : dist b b' ^ 2 ≤ 0 := by
    by_contra h5
    push Not at h5
    exact absurd h3 (not_le.2 (mul_pos hw h5))
  have h5 : dist b b' = 0 := by
    have := sq_nonneg (dist b b')
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 this)
  exact dist_eq_zero.1 h5

/-- A barycentre is mapped to a barycentre by a surjective isometry. -/
theorem IsBary.map {Y : Type*} [MetricSpace Y] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) {f : X → Y} (hf : Isometry f) (hs : Function.Surjective f) :
    IsBary w (fun i => f (x i)) (f b) := by
  intro y
  obtain ⟨y, rfl⟩ := hs y
  simpa only [hf.dist_eq] using h y

/-- Barycentres don't depend on the names of the points. -/
theorem IsBary.comp_equiv {κ : Type*} [Fintype κ] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) (e : κ ≃ ι) : IsBary (w ∘ e) (x ∘ e) b := by
  intro y
  have h1 := h y
  rw [← e.sum_comp fun i => w i * dist b (x i) ^ 2, ← e.sum_comp w,
    ← e.sum_comp fun i => w i * dist y (x i) ^ 2] at h1
  exact h1

end bary

/-! ### Points at fraction `t` -/

/-- `b` is the point at fraction `t` between `x` and `v`. -/
def IsPt (x v : X) (t : ℝ) (b : X) : Prop :=
  ∀ z, dist z b ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2

theorem IsPt.dist_left {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist x b = t * dist x v := by
  have h2 := h x
  have h3 := h v
  have h4 := dist_triangle x b v
  rw [dist_self] at h2 h3
  rw [dist_comm v x] at h3
  rw [dist_comm b v] at h4
  have ha : dist x b ≤ t * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg h0 dist_nonneg) |>.2
    nlinarith
  have hb : dist v b ≤ (1 - t) * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg (by linarith) dist_nonneg) |>.2
    nlinarith
  linarith

theorem IsPt.symm {x v b : X} {t : ℝ} (h : IsPt x v t b) : IsPt v x (1 - t) b := by
  intro z
  have := h z
  rw [dist_comm v x]
  linarith

theorem IsPt.dist_right {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist b v = (1 - t) * dist x v := by
  have := h.symm.dist_left (by linarith) (by linarith)
  rw [dist_comm b v, this, dist_comm v x]

/-- A point with the distances of the point at fraction `t` is the point at fraction `t`. -/
theorem IsPt.eq_of_dist {x v b b' : X} {t : ℝ} (h : IsPt x v t b)
    (h2 : dist x b' = t * dist x v) (h3 : dist b' v = (1 - t) * dist x v) : b' = b := by
  have h4 := h b'
  rw [dist_comm b' x, h2, h3] at h4
  have h5 : dist b' b ^ 2 ≤ 0 := by nlinarith
  exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h5 (sq_nonneg _)))

theorem le_two_mul_of_forall {S a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ τ : ℝ, 0 < τ → S ≤ τ * b ^ 2 + a ^ 2 / τ) : S ≤ 2 * a * b := by
  rcases ha.eq_or_lt with rfl | ha
  · by_contra hS
    push Not at hS
    simp only [mul_zero, zero_mul] at hS
    have h1 := h (S / (2 * (b ^ 2 + 1))) (by positivity)
    have h2 : S / (2 * (b ^ 2 + 1)) * b ^ 2 ≤ S / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    simp at h1
    linarith
  rcases hb.eq_or_lt with rfl | hb
  · by_contra hS
    push Not at hS
    rw [mul_zero] at hS
    have h1 := h (2 * (a ^ 2 + 1) / S) (by positivity)
    have h2 : a ^ 2 / (2 * (a ^ 2 + 1) / S) ≤ S / 2 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : 2 * (a ^ 2 + 1) / S * (0 : ℝ) ^ 2 = 0 := by ring
    linarith
  · have h1 := h (a / b) (by positivity)
    have h2 : a / b * b ^ 2 + a ^ 2 / (a / b) = 2 * a * b := by
      field_simp
      ring
    linarith

end Cat
