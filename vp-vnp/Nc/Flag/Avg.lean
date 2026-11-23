/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Window

/-!
# One step of the averaging of projections: the arithmetic
-/

open Finset

namespace Nc.Flag

open Cat
open Nc.Tower (U SL2 lo hi x)

/-- One step of the averaging. -/
theorem step_num {X Y d L δ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hL : 1 ≤ L) (hδ : 0 < δ)
    (h1 : Y ^ 2 ≤ (1 - δ / L) * X ^ 2) (h2 : L * d ^ 2 ≤ X ^ 2 - Y ^ 2) :
    d ≤ 2 / √δ * (X - Y) := by
  have hL0 : 0 < L := by linarith
  have h3 : δ * X ^ 2 ≤ L * (X ^ 2 - Y ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h1 hL0.le
    have h5 : L * ((1 - δ / L) * X ^ 2) = L * X ^ 2 - δ * X ^ 2 := by field_simp
    rw [h5] at h4
    linarith
  have hYX : Y ≤ X := by
    refine (abs_le_of_sq_le_sq' (show Y ^ 2 ≤ X ^ 2 from ?_) hX).2
    have : 0 ≤ δ * X ^ 2 := by positivity
    have h6 : 0 ≤ X ^ 2 - Y ^ 2 := by
      by_contra h7
      push Not at h7
      have := mul_neg_of_pos_of_neg hL0 h7
      linarith
    linarith
  have hs : 0 < √δ := Real.sqrt_pos.2 hδ
  rcases hX.eq_or_lt with rfl | hX0
  · have hY0 : Y = 0 := le_antisymm hYX hY
    subst hY0
    have : d ^ 2 ≤ 0 := by
      by_contra h6
      push Not at h6
      have := mul_pos hL0 h6
      linarith
    have : d = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
    rw [this]
    simp
  · have h4 : δ * X ^ 2 * (L * d ^ 2) ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) := by
      have e1 : 0 ≤ X ^ 2 - Y ^ 2 := by nlinarith
      calc δ * X ^ 2 * (L * d ^ 2) ≤ (L * (X ^ 2 - Y ^ 2)) * (X ^ 2 - Y ^ 2) :=
            mul_le_mul h3 h2 (by positivity) (by positivity)
        _ = L * ((X + Y) ^ 2 * (X - Y) ^ 2) := by ring
        _ ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hL0.le
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith
    have h5 : δ * d ^ 2 ≤ 4 * (X - Y) ^ 2 := by
      have h6 : (L * X ^ 2) * (δ * d ^ 2) ≤ (L * X ^ 2) * (4 * (X - Y) ^ 2) := by linarith
      exact le_of_mul_le_mul_left h6 (by positivity)
    have h6 : (√δ * d) ^ 2 ≤ (2 * (X - Y)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hδ.le]
      linarith
    have h7 := (abs_le_of_sq_le_sq' h6 (by linarith)).2
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith

end Nc.Flag
