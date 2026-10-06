/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ThmD/UnionDecimal.lean — certified numerical enclosure for the
simple-or-on-critical-line endpoint.
-/
import Zeta23.ThmD.Union

noncomputable section


open Finset

namespace Complex

private theorem cos_bound_14 {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)‖ ≤
      ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  calc
    ‖cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)‖ =
        ‖(exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ ≤ ‖exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤ ‖-x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (n := 14) (by simpa) (by norm_num),
        Complex.exp_bound (n := 14) (by simpa) (by norm_num)]
    _ = ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by norm_num

private theorem sin_bound_14 {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)‖ ≤
      ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  calc
    ‖sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)‖ =
        ‖(exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial) * I / 2 -
         (exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial) * I / 2‖ := by
      simp [sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ ≤ ‖exp (-x * I) - ∑ m ∈ range 14, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m ∈ range 14, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ ≤ ‖-x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * I‖ ^ 14 * ((Nat.succ 14 : ℝ) *
          (Nat.factorial 14 * (14 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (n := 14) (by simpa) (by norm_num),
        Complex.exp_bound (n := 14) (by simpa) (by norm_num)]
    _ = ‖x‖ ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by norm_num

end Complex

namespace Real

private theorem cos_bound_14 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
      - x ^ 10 / 3628800 + x ^ 12 / 479001600)| ≤
      |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  simpa [← Complex.ofReal_cos, ← norm_eq_abs, ← Complex.norm_real] using
    Complex.cos_bound_14 (x := (x : ℂ)) (by simpa)

private theorem sin_bound_14 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
      - x ^ 11 / 39916800 + x ^ 13 / 6227020800)| ≤
      |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) := by
  simpa [← Complex.ofReal_sin, ← norm_eq_abs, ← Complex.norm_real] using
    Complex.sin_bound_14 (x := (x : ℂ)) (by simpa)

end Real


namespace Zeta23.ThmD

private theorem sin_cos_numeric :
    |Real.cos (Real.sqrt 2)⁻¹ - (3329448031 / 4379443200 : ℝ)| ≤
        (1 / 10414899855360 : ℝ) ∧
    |Real.sin (Real.sqrt 2)⁻¹ -
        (Real.sqrt 2)⁻¹ * (366139007209 / 398529331200 : ℝ)| ≤
        (1 / 10414899855360 : ℝ) := by
  let x : ℝ := (Real.sqrt 2)⁻¹
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    exact Zeta23.ThmD.sqrt_two_inv_lt_one
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_pos hxpos]
    exact hxlt.le
  have hx2 : x ^ 2 = (1 / 2 : ℝ) := by
    dsimp [x]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have heven (n : ℕ) : x ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
    rw [pow_mul, hx2]
  have hodd (n : ℕ) : x ^ (2 * n + 1) = x * (1 / 2 : ℝ) ^ n := by
    rw [pow_add, heven]
    ring
  have hpoly_cos :
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
        - x ^ 10 / 3628800 + x ^ 12 / 479001600 =
      (3329448031 / 4379443200 : ℝ) := by
    rw [show x ^ 2 = (1 / 2 : ℝ) ^ 1 by simpa using heven 1,
      show x ^ 4 = (1 / 2 : ℝ) ^ 2 by simpa using heven 2,
      show x ^ 6 = (1 / 2 : ℝ) ^ 3 by simpa using heven 3,
      show x ^ 8 = (1 / 2 : ℝ) ^ 4 by simpa using heven 4,
      show x ^ 10 = (1 / 2 : ℝ) ^ 5 by simpa using heven 5,
      show x ^ 12 = (1 / 2 : ℝ) ^ 6 by simpa using heven 6]
    norm_num
  have hpoly_sin :
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
        - x ^ 11 / 39916800 + x ^ 13 / 6227020800 =
      x * (366139007209 / 398529331200 : ℝ) := by
    rw [show x ^ 3 = x * (1 / 2 : ℝ) ^ 1 by simpa [mul_comm] using hodd 1,
      show x ^ 5 = x * (1 / 2 : ℝ) ^ 2 by simpa [mul_comm] using hodd 2,
      show x ^ 7 = x * (1 / 2 : ℝ) ^ 3 by simpa [mul_comm] using hodd 3,
      show x ^ 9 = x * (1 / 2 : ℝ) ^ 4 by simpa [mul_comm] using hodd 4,
      show x ^ 11 = x * (1 / 2 : ℝ) ^ 5 by simpa [mul_comm] using hodd 5,
      show x ^ 13 = x * (1 / 2 : ℝ) ^ 6 by simpa [mul_comm] using hodd 6]
    ring
  have herr :
      |x| ^ 14 * ((15 : ℝ) / (Nat.factorial 14 * 14)) =
        (1 / 10414899855360 : ℝ) := by
    rw [abs_of_pos hxpos,
      show x ^ 14 = (1 / 2 : ℝ) ^ 7 by simpa using heven 7]
    norm_num [Nat.factorial]
  have hc := Real.cos_bound_14 (x := x) hxabs
  have hs := Real.sin_bound_14 (x := x) hxabs
  rw [hpoly_cos, herr] at hc
  rw [hpoly_sin, herr] at hs
  simpa [x] using And.intro hc hs

end Zeta23.ThmD

namespace Zeta23.ThmD

/-- A fully kernel-checked decimal enclosure of the endpoint union constant. -/
theorem unionProp_cStar_one_decimal :
    (887620008173 / 1000000000000 : ℝ) <
        unionProp (cStar 1) ∧
      unionProp (cStar 1) <
        (887620008174 / 1000000000000 : ℝ) := by
  let r : ℝ := Real.sqrt 2
  let x : ℝ := r⁻¹
  let rlo : ℝ := 1414213562373095 / 1000000000000000
  let rhi : ℝ := 1414213562373096 / 1000000000000000
  let xlo : ℝ := 707106781186547 / 1000000000000000
  let xhi : ℝ := 707106781186548 / 1000000000000000
  let slo : ℝ := 6496369390799 / 10000000000000
  let shi : ℝ := 6496369390802 / 10000000000000
  let clo : ℝ := 7602445970756 / 10000000000000
  let chi : ℝ := 7602445970759 / 10000000000000
  let L : ℝ := 887620008173 / 1000000000000
  let U : ℝ := 887620008174 / 1000000000000
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg 2
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hr2 : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num)
  have hrlo_pos : 0 < rlo := by norm_num [rlo]
  have hrhi_pos : 0 < rhi := by norm_num [rhi]
  have hrlo_sq : rlo ^ 2 < 2 := by norm_num [rlo]
  have hrhi_sq : 2 < rhi ^ 2 := by norm_num [rhi]
  have hrlo_lt : rlo < r := by
    apply (sq_lt_sq₀ hrlo_pos.le hr0).mp
    rw [hr2]
    exact hrlo_sq
  have hr_lt_rhi : r < rhi := by
    apply (sq_lt_sq₀ hr0 hrhi_pos.le).mp
    rw [hr2]
    exact hrhi_sq
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hx2 : x ^ 2 = (1 / 2 : ℝ) := by
    dsimp [x]
    rw [inv_pow, hr2]
    norm_num
  have hxlo_pos : 0 < xlo := by norm_num [xlo]
  have hxhi_pos : 0 < xhi := by norm_num [xhi]
  have hxlo_sq : xlo ^ 2 < (1 / 2 : ℝ) := by norm_num [xlo]
  have hxhi_sq : (1 / 2 : ℝ) < xhi ^ 2 := by norm_num [xhi]
  have hxlo_lt : xlo < x := by
    apply (sq_lt_sq₀ hxlo_pos.le hxpos.le).mp
    rw [hx2]
    exact hxlo_sq
  have hx_lt_xhi : x < xhi := by
    apply (sq_lt_sq₀ hxpos.le hxhi_pos.le).mp
    rw [hx2]
    exact hxhi_sq
  have htrig := sin_cos_numeric
  change |Real.cos x - (3329448031 / 4379443200 : ℝ)| ≤
      (1 / 10414899855360 : ℝ) ∧
    |Real.sin x - x * (366139007209 / 398529331200 : ℝ)| ≤
      (1 / 10414899855360 : ℝ) at htrig
  rcases htrig with ⟨hcos_abs, hsin_abs⟩
  have hcos_interval := abs_le.mp hcos_abs
  have hsin_interval := abs_le.mp hsin_abs
  have hcos_lower :
      (3329448031 / 4379443200 : ℝ) - 1 / 10414899855360 ≤
        Real.cos x := by
    linarith only [hcos_interval.1]
  have hcos_upper :
      Real.cos x ≤ (3329448031 / 4379443200 : ℝ) +
        1 / 10414899855360 := by
    linarith only [hcos_interval.2]
  have hclo : clo < Real.cos x := by
    have hconst : clo < (3329448031 / 4379443200 : ℝ) -
        1 / 10414899855360 := by norm_num [clo]
    exact hconst.trans_le hcos_lower
  have hcos_chi : Real.cos x < chi := by
    have hconst : (3329448031 / 4379443200 : ℝ) +
        1 / 10414899855360 < chi := by norm_num [chi]
    exact hcos_upper.trans_lt hconst
  have hsin_lower :
      x * (366139007209 / 398529331200 : ℝ) -
          1 / 10414899855360 ≤ Real.sin x := by
    linarith only [hsin_interval.1]
  have hsin_upper :
      Real.sin x ≤ x * (366139007209 / 398529331200 : ℝ) +
          1 / 10414899855360 := by
    linarith only [hsin_interval.2]
  have hslo : slo < Real.sin x := by
    have hA : 0 < (366139007209 / 398529331200 : ℝ) := by norm_num
    have hconst : slo < xlo * (366139007209 / 398529331200 : ℝ) -
        1 / 10414899855360 := by norm_num [slo, xlo]
    have hxA : xlo * (366139007209 / 398529331200 : ℝ) <
        x * (366139007209 / 398529331200 : ℝ) :=
      mul_lt_mul_of_pos_right hxlo_lt hA
    exact hconst.trans ((sub_lt_sub_right hxA _).trans_le hsin_lower)
  have hsin_shi : Real.sin x < shi := by
    have hA : 0 < (366139007209 / 398529331200 : ℝ) := by norm_num
    have hconst : xhi * (366139007209 / 398529331200 : ℝ) +
        1 / 10414899855360 < shi := by norm_num [shi, xhi]
    have hxA : x * (366139007209 / 398529331200 : ℝ) <
        xhi * (366139007209 / 398529331200 : ℝ) :=
      mul_lt_mul_of_pos_right hx_lt_xhi hA
    have hxAE : x * (366139007209 / 398529331200 : ℝ) +
        1 / 10414899855360 <
        xhi * (366139007209 / 398529331200 : ℝ) +
          1 / 10414899855360 := by
      simpa [add_comm] using
        add_lt_add_right hxA (1 / 10414899855360 : ℝ)
    exact hsin_upper.trans_lt (hxAE.trans hconst)
  have hslo_pos : 0 < slo := by norm_num [slo]
  have hclo_pos : 0 < clo := by norm_num [clo]
  have hsin_pos : 0 < Real.sin x := hslo_pos.trans hslo
  have hcos_pos : 0 < Real.cos x := hclo_pos.trans hclo
  have hqpos : 0 < 3 / 2 + r := by positivity
  have hL_lt_one : L < 1 := by norm_num [L]
  have hU_lt_one : U < 1 := by norm_num [U]
  have hBLower_pos :
      0 < 1 / 2 + (1 - L) * (3 / 2 + rlo) := by
    positivity
  have hBUpper_pos :
      0 < 1 / 2 + (1 - U) * (3 / 2 + rhi) := by
    positivity
  have hcert_lower :
      xhi * chi <
        (1 / 2 + (1 - L) * (3 / 2 + rlo)) * slo := by
    norm_num [xhi, chi, L, rlo, slo]
  have hcert_upper :
      (1 / 2 + (1 - U) * (3 / 2 + rhi)) * shi <
        xlo * clo := by
    norm_num [U, rhi, shi, xlo, clo]
  have hxcos_upper : x * Real.cos x < xhi * chi := by
    exact mul_lt_mul hx_lt_xhi hcos_chi.le hcos_pos hxhi_pos.le
  have hBLower_lt :
      1 / 2 + (1 - L) * (3 / 2 + rlo) <
        1 / 2 + (1 - L) * (3 / 2 + r) := by
    nlinarith
  have hBsin_lower :
      (1 / 2 + (1 - L) * (3 / 2 + rlo)) * slo <
        (1 / 2 + (1 - L) * (3 / 2 + r)) * Real.sin x := by
    exact mul_lt_mul hBLower_lt hslo.le hslo_pos (hBLower_pos.trans hBLower_lt).le
  have hratio_upper :
      x * (Real.cos x / Real.sin x) <
        1 / 2 + (1 - L) * (3 / 2 + r) := by
    rw [← mul_div_assoc, div_lt_iff₀ hsin_pos]
    exact hxcos_upper.trans (hcert_lower.trans hBsin_lower)
  have hxcos_lower : xlo * clo < x * Real.cos x := by
    exact mul_lt_mul hxlo_lt hclo.le hclo_pos hxpos.le
  have hB_lt_upper :
      1 / 2 + (1 - U) * (3 / 2 + r) <
        1 / 2 + (1 - U) * (3 / 2 + rhi) := by
    nlinarith
  have hBsin_upper :
      (1 / 2 + (1 - U) * (3 / 2 + r)) * Real.sin x <
        (1 / 2 + (1 - U) * (3 / 2 + rhi)) * shi := by
    exact mul_lt_mul hB_lt_upper hsin_shi.le hsin_pos hBUpper_pos.le
  have hratio_lower :
      1 / 2 + (1 - U) * (3 / 2 + r) <
        x * (Real.cos x / Real.sin x) := by
    rw [← mul_div_assoc, lt_div_iff₀ hsin_pos]
    exact hBsin_upper.trans (hcert_upper.trans hxcos_lower)
  have hunion :
      unionProp (cStar 1) =
        1 + (1 / 2 - x * (Real.cos x / Real.sin x)) / (3 / 2 + r) := by
    rw [unionProp_cStar_eq, HD_one]
    unfold Zeta23.ZeroSide.unionQ
    change 1 + (3 / 2 - x * (Real.cos x / Real.sin x) - 1) /
      (3 / 2 + r) = _
    ring
  rw [hunion]
  change L < 1 + (1 / 2 - x * (Real.cos x / Real.sin x)) / (3 / 2 + r) ∧
    1 + (1 / 2 - x * (Real.cos x / Real.sin x)) / (3 / 2 + r) < U
  constructor
  · have hinner :
        (L - 1) * (3 / 2 + r) <
          1 / 2 - x * (Real.cos x / Real.sin x) := by
      nlinarith only [hratio_upper]
    have hfrac :
        L - 1 <
          (1 / 2 - x * (Real.cos x / Real.sin x)) / (3 / 2 + r) :=
      (lt_div_iff₀ hqpos).2 hinner
    linarith only [hfrac]
  · have hinner :
        1 / 2 - x * (Real.cos x / Real.sin x) <
          (U - 1) * (3 / 2 + r) := by
      nlinarith only [hratio_lower]
    have hfrac :
        (1 / 2 - x * (Real.cos x / Real.sin x)) / (3 / 2 + r) < U - 1 :=
      (div_lt_iff₀ hqpos).2 hinner
    linarith only [hfrac]

/-- The requested seven-decimal lower bound follows from the tight enclosure. -/
theorem unionProp_cStar_one_gt_8876200 :
    (8876200 / 10 ^ 7 : ℝ) < unionProp (cStar 1) := by
  exact (by norm_num : (8876200 / 10 ^ 7 : ℝ) <
      887620008173 / 1000000000000).trans unionProp_cStar_one_decimal.1


/-- A kernel-checked decimal enclosure of the coefficient obtained from the
Montgomery--Taylor ordinary-ordinate collision target. -/
theorem collisionEndpoint_decimal :
    (890833567893 / 10 ^ 12 : ℝ) <
        1 - ((cStar 1)⁻¹ - 1) / 3 ∧
      1 - ((cStar 1)⁻¹ - 1) / 3 <
        (8908335678932 / 10 ^ 13 : ℝ) := by
  let x : ℝ := (Real.sqrt 2)⁻¹
  let xlo : ℝ := 707106781186547 / 10 ^ 15
  let xhi : ℝ := 707106781186548 / 10 ^ 15
  let slo : ℝ := 64963693907997 / 10 ^ 14
  let shi : ℝ := 64963693908017 / 10 ^ 14
  let clo : ℝ := 76024459707562 / 10 ^ 14
  let chi : ℝ := 76024459707582 / 10 ^ 14
  let L : ℝ := 890833567893 / 10 ^ 12
  let U : ℝ := 8908335678932 / 10 ^ 13
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hx2 : x ^ 2 = (1 / 2 : ℝ) := by
    dsimp [x]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hxlo_pos : 0 < xlo := by norm_num [xlo]
  have hxhi_pos : 0 < xhi := by norm_num [xhi]
  have hxlo_sq : xlo ^ 2 < (1 / 2 : ℝ) := by norm_num [xlo]
  have hxhi_sq : (1 / 2 : ℝ) < xhi ^ 2 := by norm_num [xhi]
  have hxlo_lt : xlo < x := by
    apply (sq_lt_sq₀ hxlo_pos.le hxpos.le).mp
    rw [hx2]
    exact hxlo_sq
  have hx_lt_xhi : x < xhi := by
    apply (sq_lt_sq₀ hxpos.le hxhi_pos.le).mp
    rw [hx2]
    exact hxhi_sq
  have htrig := sin_cos_numeric
  change |Real.cos x - (3329448031 / 4379443200 : ℝ)| ≤
      (1 / 10414899855360 : ℝ) ∧
    |Real.sin x - x * (366139007209 / 398529331200 : ℝ)| ≤
      (1 / 10414899855360 : ℝ) at htrig
  rcases htrig with ⟨hcos_abs, hsin_abs⟩
  have hcos_interval := abs_le.mp hcos_abs
  have hsin_interval := abs_le.mp hsin_abs
  have hcos_lower :
      (3329448031 / 4379443200 : ℝ) - 1 / 10414899855360 ≤
        Real.cos x := by
    linarith only [hcos_interval.1]
  have hcos_upper :
      Real.cos x ≤ (3329448031 / 4379443200 : ℝ) +
        1 / 10414899855360 := by
    linarith only [hcos_interval.2]
  have hclo : clo < Real.cos x := by
    have hconst : clo < (3329448031 / 4379443200 : ℝ) -
        1 / 10414899855360 := by norm_num [clo]
    exact hconst.trans_le hcos_lower
  have hcos_chi : Real.cos x < chi := by
    have hconst : (3329448031 / 4379443200 : ℝ) +
        1 / 10414899855360 < chi := by norm_num [chi]
    exact hcos_upper.trans_lt hconst
  have hsin_lower :
      x * (366139007209 / 398529331200 : ℝ) -
          1 / 10414899855360 ≤ Real.sin x := by
    linarith only [hsin_interval.1]
  have hsin_upper :
      Real.sin x ≤ x * (366139007209 / 398529331200 : ℝ) +
          1 / 10414899855360 := by
    linarith only [hsin_interval.2]
  have hslo : slo < Real.sin x := by
    have hA : 0 < (366139007209 / 398529331200 : ℝ) := by norm_num
    have hconst : slo < xlo * (366139007209 / 398529331200 : ℝ) -
        1 / 10414899855360 := by norm_num [slo, xlo]
    have hxA : xlo * (366139007209 / 398529331200 : ℝ) <
        x * (366139007209 / 398529331200 : ℝ) :=
      mul_lt_mul_of_pos_right hxlo_lt hA
    exact hconst.trans ((sub_lt_sub_right hxA _).trans_le hsin_lower)
  have hsin_shi : Real.sin x < shi := by
    have hA : 0 < (366139007209 / 398529331200 : ℝ) := by norm_num
    have hconst : xhi * (366139007209 / 398529331200 : ℝ) +
        1 / 10414899855360 < shi := by norm_num [shi, xhi]
    have hxA : x * (366139007209 / 398529331200 : ℝ) <
        xhi * (366139007209 / 398529331200 : ℝ) :=
      mul_lt_mul_of_pos_right hx_lt_xhi hA
    have hxAE : x * (366139007209 / 398529331200 : ℝ) +
        1 / 10414899855360 <
        xhi * (366139007209 / 398529331200 : ℝ) +
          1 / 10414899855360 := by
      simpa [add_comm] using
        add_lt_add_right hxA (1 / 10414899855360 : ℝ)
    exact hsin_upper.trans_lt (hxAE.trans hconst)
  have hslo_pos : 0 < slo := by norm_num [slo]
  have hclo_pos : 0 < clo := by norm_num [clo]
  have hsin_pos : 0 < Real.sin x := hslo_pos.trans hslo
  have hcos_pos : 0 < Real.cos x := hclo_pos.trans hclo
  have hBLpos : 0 < 7 / 2 - 3 * L := by norm_num [L]
  have hBUpos : 0 < 7 / 2 - 3 * U := by norm_num [U]
  have hcert_lower :
      xhi * chi < (7 / 2 - 3 * L) * slo := by
    norm_num [xhi, chi, L, slo]
  have hcert_upper :
      (7 / 2 - 3 * U) * shi < xlo * clo := by
    norm_num [U, shi, xlo, clo]
  have hxcos_upper : x * Real.cos x < xhi * chi :=
    mul_lt_mul hx_lt_xhi hcos_chi.le hcos_pos hxhi_pos.le
  have hratio_upper :
      x * (Real.cos x / Real.sin x) < 7 / 2 - 3 * L := by
    rw [← mul_div_assoc, div_lt_iff₀ hsin_pos]
    exact hxcos_upper.trans
      (hcert_lower.trans (mul_lt_mul_of_pos_left hslo hBLpos))
  have hxcos_lower : xlo * clo < x * Real.cos x :=
    mul_lt_mul hxlo_lt hclo.le hclo_pos hxpos.le
  have hratio_lower :
      7 / 2 - 3 * U < x * (Real.cos x / Real.sin x) := by
    rw [show x * (Real.cos x / Real.sin x) =
      (x * Real.cos x) / Real.sin x by rw [mul_div_assoc],
      lt_div_iff₀ hsin_pos]
    exact (mul_lt_mul_of_pos_left hsin_shi hBUpos).trans
      (hcert_upper.trans hxcos_lower)
  have hinv : (cStar 1)⁻¹ = 1 / 2 + x *
      (Real.cos x / Real.sin x) := by
    simpa only [x] using cStar_one_inv_eq_montgomeryTaylor
  have hform :
      1 - ((cStar 1)⁻¹ - 1) / 3 =
        7 / 6 - x * (Real.cos x / Real.sin x) / 3 := by
    rw [hinv]
    ring
  rw [hform]
  change L < 7 / 6 - x * (Real.cos x / Real.sin x) / 3 ∧
    7 / 6 - x * (Real.cos x / Real.sin x) / 3 < U
  constructor <;> linarith

/-- The certified lower decimal endpoint, in the repository's canonical epsilon form. -/
theorem thmD₀_union_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  intro ε hε
  have hη : 0 < unionProp (cStar 1) - (887620008173 / 10 ^ 12 : ℝ) + ε := by
    linarith [unionProp_cStar_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀_union
    (unionProp (cStar 1) - (887620008173 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- The certified lower decimal endpoint in cumulative windows `0 < Im ρ ≤ T`. -/
theorem thmD₀_union_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  intro ε hε
  have hη : 0 < unionProp (cStar 1) - (887620008173 / 10 ^ 12 : ℝ) + ε := by
    linarith [unionProp_cStar_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀_union_cumulative
    (unionProp (cStar 1) - (887620008173 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

end Zeta23.ThmD
