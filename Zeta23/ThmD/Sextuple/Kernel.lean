/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace Zeta23.ThmD.Sextuple

/-- The normalized Montgomery--Taylor translate kernel.  The `Real.sinc`
form includes the removable values at `x = ±√2` by definition. -/
def mtKernel (x : ℝ) : ℝ :=
  (Real.sinc ((x - Real.sqrt 2) / 2) +
    Real.sinc ((x + Real.sqrt 2) / 2)) /
      (2 * Real.sinc (Real.sqrt 2 / 2))

@[simp] theorem mtKernel_zero : mtKernel 0 = 1 := by
  have hs : Real.sinc (Real.sqrt 2 / 2) ≠ 0 := by
    have hθpos : 0 < Real.sqrt 2 / 2 := by positivity
    have hθlt : Real.sqrt 2 / 2 < Real.pi := by
      have hsqrt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      nlinarith [Real.pi_gt_three]
    rw [Real.sinc_of_ne_zero (ne_of_gt hθpos)]
    exact div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne' (ne_of_gt hθpos)
  simp only [mtKernel, zero_sub, zero_add]
  rw [show -Real.sqrt 2 / 2 = -(Real.sqrt 2 / 2) by ring, Real.sinc_neg]
  field_simp
  norm_num

@[simp] theorem mtKernel_neg (x : ℝ) : mtKernel (-x) = mtKernel x := by
  rw [mtKernel, mtKernel]
  have h₁ : (-x - Real.sqrt 2) / 2 = -((x + Real.sqrt 2) / 2) := by ring
  have h₂ : (-x + Real.sqrt 2) / 2 = -((x - Real.sqrt 2) / 2) := by ring
  rw [h₁, h₂, Real.sinc_neg, Real.sinc_neg]
  ring

/-- A denominator-only closed form of `mtKernel`, used by the rational
interval checker away from the two removable points. -/
def mtKernelClosed (x : ℝ) : ℝ :=
  (Real.sqrt 2 * x * Real.cos (Real.sqrt 2 / 2) * Real.sin (x / 2) -
      2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (x / 2)) /
    ((x ^ 2 - 2) * Real.sin (Real.sqrt 2 / 2))

/-- The sinc definition agrees with the closed form off `x² = 2`. -/
theorem mtKernel_eq_closed {x : ℝ} (hx : x ^ 2 ≠ 2) :
    mtKernel x = mtKernelClosed x := by
  have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : Real.sqrt 2 ≠ 0 := by positivity
  have hm : x - Real.sqrt 2 ≠ 0 := by
    intro h
    have : x = Real.sqrt 2 := sub_eq_zero.mp h
    apply hx
    rw [this, ha2]
  have hp : x + Real.sqrt 2 ≠ 0 := by
    intro h
    have : x = -Real.sqrt 2 := eq_neg_of_add_eq_zero_left h
    apply hx
    rw [this, neg_sq, ha2]
  have hθ : Real.sqrt 2 / 2 ≠ 0 := div_ne_zero ha (by norm_num)
  have hs : Real.sin (Real.sqrt 2 / 2) ≠ 0 := by
    have hpos : 0 < Real.sqrt 2 / 2 := by positivity
    have hlt : Real.sqrt 2 / 2 < Real.pi := by
      have hsqrt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      nlinarith [Real.pi_gt_three]
    exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne'
  rw [mtKernel, mtKernelClosed,
    Real.sinc_of_ne_zero (div_ne_zero hm (by norm_num)),
    Real.sinc_of_ne_zero (div_ne_zero hp (by norm_num)),
    Real.sinc_of_ne_zero hθ]
  rw [show (x - Real.sqrt 2) / 2 = x / 2 - Real.sqrt 2 / 2 by ring,
    show (x + Real.sqrt 2) / 2 = x / 2 + Real.sqrt 2 / 2 by ring,
    Real.sin_sub, Real.sin_add]
  field_simp [hm, hp, hθ, hs]
  ring_nf
  have ha3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, ha2]
  rw [ha2, ha3]
  ring

/-- A coarse exact lower bound for sinc on the only small-argument range
needed to start the interval certificate. -/
lemma sinc_ge_47_96 {z : ℝ} (hz : |z| ≤ 7/4) : (47/96 : ℝ) ≤ Real.sinc z := by
  wlog hz0 : 0 ≤ z generalizing z
  · have hneg : 0 ≤ -z := neg_nonneg.mpr (le_of_not_ge hz0)
    have habs : |-z| ≤ 7/4 := by simpa using hz
    simpa [Real.sinc_neg] using this (z := -z) habs hneg
  rcases hz0.eq_or_lt with rfl | hzpos
  · norm_num [Real.sinc_zero]
  · rw [Real.sinc_of_ne_zero hzpos.ne']
    apply (le_div_iff₀ hzpos).2
    have hzsq : z^2 ≤ (7/4 : ℝ)^2 := (sq_le_sq₀ hz0 (by norm_num)).2 (by
      simpa [abs_of_nonneg hz0] using hz)
    have hsin := Real.sin_ge_sub_cube hzpos.le
    nlinarith [mul_nonneg hzpos.le (sub_nonneg.mpr hzsq)]

/-- On `[0,2]` the kernel is far from its first zero.  This elementary
bound closes the low-distance cells without evaluating the removable form. -/
theorem mtKernel_low_sq {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (1/4 : ℝ) ≤ 2 * mtKernel x ^ 2 := by
  have ha0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have ha2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hale : Real.sqrt 2 ≤ 3/2 := by
    apply (sq_le_sq₀ ha0 (by norm_num)).mp
    rw [ha2]
    norm_num
  have hm : |(x - Real.sqrt 2)/2| ≤ 7/4 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hp : |(x + Real.sqrt 2)/2| ≤ 7/4 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have ht : |Real.sqrt 2/2| ≤ 7/4 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hkm := sinc_ge_47_96 hm
  have hkp := sinc_ge_47_96 hp
  have hkt := sinc_ge_47_96 ht
  have hkt1 := Real.sinc_le_one (Real.sqrt 2/2)
  have hden : 0 < 2 * Real.sinc (Real.sqrt 2/2) := by linarith
  have hk : (47/96 : ℝ) ≤ mtKernel x := by
    rw [mtKernel, le_div_iff₀ hden]
    nlinarith
  nlinarith [sq_nonneg (mtKernel x - 47/96)]

end Zeta23.ThmD.Sextuple
