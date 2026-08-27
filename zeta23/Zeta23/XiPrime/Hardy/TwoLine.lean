/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/TwoLine.lean — estimates for W on the line Re s = 2 and in the strip 1/8 ≤ Re ≤ 4, |Im| ≥ 2
(zero side; [XF′ (Z5), (Z6)(i), (Z7) local inputs]).  These are exactly the hypotheses
(hfa, hgrow, hlow') of Zeta23/XiPrime/ZeroCount/Generic.lean, for f := hardyW:
  * hardyW_analyticOnNhd_disc : W analytic on closedBall (2+it) (91/50) for |t| ≥ 2 (the disc misses ℝ);
  * re_L2_two_ge : Re L₂(2+it) ≥ ½log(|t|/2) − 3  (digamma Stirling at 1+it/2 and, via the shift Γℝ′/Γℝ(u) =
    Γℝ′/Γℝ(u+2) − 1/u twice, at (3−it)/2);
  * hardyW_two_line_lower : ∃ t₁ ≥ 2, ∀ |t| ≥ t₁, 1 ≤ ‖W(2+it)‖  (= ‖ζ(2+it)‖·‖L₂ + ζ′/ζ‖ ≥ (1/3)·3);
  * hardyW_growth : ‖W(s)‖ ≤ C·|Im s|² on 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2.
-/
import Zeta23.XiPrime.Hardy.Basic
import Zeta23.XiPrime.ZeroCount.Y

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

/-! ### the shift Γℝ′/Γℝ(u) = Γℝ′/Γℝ(u+2) − 1/u off the real axis -/

theorem logDeriv_Gammaℝ_shift {u : ℂ} (hu : u.im ≠ 0) :
    logDeriv Gammaℝ u = logDeriv Gammaℝ (u + 2) - 1 / u := by
  have hu0 := ne_zero_of_im_ne_zero hu
  have hu2 : (u + 2).im ≠ 0 := by simpa using hu
  -- Γℝ(z+2) = Γℝ(z)·z/(2π) near u
  have hev : (fun z => Gammaℝ (z + 2)) =ᶠ[𝓝 u] fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ)) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hu] with z hz
    rw [Gammaℝ_add_two (ne_zero_of_im_ne_zero hz)]; ring
  have hd2 : DifferentiableAt ℂ Gammaℝ (u + 2) := differentiableAt_Gammaℝ_of_im_ne_zero hu2
  have hdu : DifferentiableAt ℂ Gammaℝ u := differentiableAt_Gammaℝ_of_im_ne_zero hu
  -- logDeriv of the left side
  have hL : logDeriv (fun z => Gammaℝ (z + 2)) u = logDeriv Gammaℝ (u + 2) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]
  -- logDeriv of the right side
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z / 2 / (Real.pi : ℂ)) u := by fun_prop
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hR : logDeriv (fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ))) u = logDeriv Gammaℝ u + 1 / u := by
    rw [logDeriv_mul u (Gammaℝ_ne_zero_of_im_ne_zero hu) (by simp [hu0, hπ]) hdu hlin]
    congr 1
    rw [logDeriv_apply]
    have : deriv (fun z : ℂ => z / 2 / (Real.pi : ℂ)) u = 1 / 2 / (Real.pi : ℂ) := by
      rw [deriv_div_const, deriv_div_const, deriv_id'']
    rw [this]; field_simp
  -- the two functions agree near u, so their logDerivs at u agree
  have heq : logDeriv (fun z => Gammaℝ (z + 2)) u = logDeriv (fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ))) u := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [← hL, heq, hR]; ring

/-! ### Re L₂ on the line Re s = 2 -/

/-- Re Γℝ′/Γℝ(s) ≥ −1 + ½(log(|Im s|/2) − 4) for Re s > 0, |Im s| ≥ 2. -/
lemma re_logDeriv_Gammaℝ_ge {s : ℂ} (hs : 0 < s.re) (him : 2 ≤ |s.im|) :
    -1 + (1 / 2) * (Real.log (|s.im| / 2) - 4) ≤ (logDeriv Gammaℝ s).re := by
  rw [Zeta23.RvM.logDeriv_Gammaℝ hs]
  have hw : 0 < (s / 2).re := by simp; linarith
  have hwim : (s / 2).im = s.im / 2 := by simp
  have hw' : 1 ≤ |(s / 2).im| := by rw [hwim, abs_div, abs_two]; linarith
  have hψ := Zeta23.XiPrime.ZeroCount.re_digamma_ge hw hw'
  rw [hwim, abs_div, abs_two] at hψ
  have hlogpi : Real.log Real.pi ≤ 2 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hre_const : (-(Real.log Real.pi : ℂ) / 2).re = -(Real.log Real.pi) / 2 := by
    simp [Complex.neg_re, Complex.div_ofNat_re]
  have hre_half : ((1 / 2 : ℂ) * Complex.digamma (s / 2)).re = (1 / 2) * (Complex.digamma (s / 2)).re := by
    rw [Complex.mul_re]; simp
  simp only [Complex.add_re]
  rw [hre_const, hre_half]
  linarith

/-- **Re L₂(2+it) ≥ ½log(|t|/2) − 3** for |t| ≥ 2. -/
theorem re_L2_two_ge {t : ℝ} (ht : 2 ≤ |t|) :
    (1 / 2) * Real.log (|t| / 2) - 3 ≤ (L2 (2 + t * I)).re := by
  have him : ((2 : ℂ) + t * I).im ≠ 0 := by
    simp; intro h; rw [h] at ht; norm_num at ht
  rw [L2_eq him]
  -- the (1−s)-term: 1 − s = −1 − it; shift twice to 3 − it
  have e1 : (1 : ℂ) - (2 + t * I) = -1 - t * I := by ring
  have hu1 : ((-1 : ℂ) - t * I).im ≠ 0 := by simpa using him
  have hu2 : ((-1 : ℂ) - t * I + 2).im ≠ 0 := by simpa using him
  have hshift : logDeriv Gammaℝ (-1 - t * I)
      = logDeriv Gammaℝ (3 - t * I) - 1 / (1 - t * I) - 1 / (-1 - t * I) := by
    rw [logDeriv_Gammaℝ_shift hu1, logDeriv_Gammaℝ_shift hu2]
    have e2 : (-1 : ℂ) - t * I + 2 = 1 - t * I := by ring
    have e3 : (1 : ℂ) - t * I + 2 = 3 - t * I := by ring
    rw [e2, e3]
  rw [e1, hshift]
  have hA := re_logDeriv_Gammaℝ_ge (s := 2 + t * I) (by simp) (by simpa using ht)
  have hB := re_logDeriv_Gammaℝ_ge (s := 3 - t * I) (by simp) (by simpa using ht)
  have himA : |((2 : ℂ) + t * I).im| = |t| := by simp
  have himB : |((3 : ℂ) - t * I).im| = |t| := by simp [abs_neg]
  rw [himA] at hA; rw [himB] at hB
  -- the two rational terms have opposite real parts
  have hr : ((1 : ℂ) / (1 - t * I)).re = ((1 : ℂ) / (-1 - t * I)).re * (-1) := by
    rw [one_div, one_div, Complex.inv_re, Complex.inv_re]
    simp [Complex.normSq_apply]; ring
  have hsum_re : (logDeriv Gammaℝ (2 + t * I)
        + (logDeriv Gammaℝ (3 - t * I) - 1 / (1 - t * I) - 1 / (-1 - t * I))).re
      = (logDeriv Gammaℝ (2 + t * I)).re + (logDeriv Gammaℝ (3 - t * I)).re := by
    simp only [Complex.add_re, Complex.sub_re]
    rw [hr]; ring
  rw [Complex.div_re]
  simp only [Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_div, add_zero]
  rw [hsum_re]
  nlinarith

/-! ### analyticity on the Landau discs -/

lemma im_ne_zero_of_mem_closedBall {t r : ℝ} (hr : r < 2) (ht : 2 ≤ |t|) {z : ℂ}
    (hz : z ∈ closedBall ((2 : ℂ) + t * I) r) : z.im ≠ 0 := by
  intro h0
  rw [mem_closedBall, dist_eq_norm] at hz
  have him := Complex.abs_im_le_norm (z - (2 + t * I))
  simp [h0] at him
  linarith [hz]

theorem hardyW_analyticOnNhd_disc (t : ℝ) (ht : 2 ≤ |t|) :
    AnalyticOnNhd ℂ hardyW (closedBall ((2 : ℂ) + t * I) (91 / 50)) := fun _ hz =>
  hardyW_analyticAt (im_ne_zero_of_mem_closedBall (by norm_num) ht hz)

/-! ### the lower bound on Re s = 2 -/

lemma two_line_im_ne_zero {t : ℝ} (ht : 2 ≤ |t|) : ((2 : ℂ) + t * I).im ≠ 0 := by
  simp; intro h; rw [h] at ht; norm_num at ht

/-- W = ζ·(ζ′/ζ + L₂) where ζ ≠ 0. -/
lemma hardyW_eq_zeta_mul {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    hardyW s = riemannZeta s * (logDeriv riemannZeta s + L2 s) := by
  rw [hardyW, logDeriv_apply]; field_simp

/-- **‖W(2+it)‖ ≥ 1 for |t| ≥ t₁**, and Re(ζ′/ζ + L₂)(2+it) ≥ 3 there  [XF′ (Z6)(i)]. -/
theorem hardyW_two_line_lower : ∃ t₁ : ℝ, 2 ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ |t| →
    3 ≤ (logDeriv riemannZeta (2 + t * I) + L2 (2 + t * I)).re ∧ 1 ≤ ‖hardyW (2 + t * I)‖ := by
  set K : ℝ := ‖deriv riemannZeta 2 / riemannZeta 2‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨2 * Real.exp (12 + 2 * K), ?_, fun t ht => ?_⟩
  · have : 1 ≤ Real.exp (12 + 2 * K) := Real.one_le_exp (by positivity)
    linarith
  have hexp1 : 1 ≤ Real.exp (12 + 2 * K) := Real.one_le_exp (by positivity)
  have ht2 : 2 ≤ |t| := by linarith
  have hlog : 12 + 2 * K ≤ Real.log (|t| / 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith
  have hL := re_L2_two_ge ht2
  have hζζ : -K ≤ (logDeriv riemannZeta (2 + t * I)).re := by
    have h1 := Complex.abs_re_le_norm (logDeriv riemannZeta (2 + t * I))
    rw [abs_le] at h1
    linarith [h1.1, Zeta23.XiPrime.ZeroCount.norm_logDeriv_zeta_two_le t]
  have hG : 3 ≤ (logDeriv riemannZeta (2 + t * I) + L2 (2 + t * I)).re := by
    rw [Complex.add_re]; linarith
  refine ⟨hG, ?_⟩
  rw [hardyW_eq_zeta_mul (Zeta23.XiPrime.ZeroCount.zeta_two_line_ne_zero t), norm_mul]
  have hz : (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := Zeta23.RvM.zeta_lower_bound_two t
  have hGn : 3 ≤ ‖logDeriv riemannZeta (2 + t * I) + L2 (2 + t * I)‖ := le_trans hG (Complex.re_le_norm _)
  calc (1 : ℝ) = (1 / 3) * 3 := by norm_num
    _ ≤ ‖riemannZeta (2 + t * I)‖ * ‖logDeriv riemannZeta (2 + t * I) + L2 (2 + t * I)‖ := by gcongr

/-- W is not identically zero on either half-plane: W(2 ± it₁) ≠ 0. -/
theorem exists_hardyW_ne_zero_upper : ∃ z : ℂ, 0 < z.im ∧ hardyW z ≠ 0 := by
  obtain ⟨t₁, ht₁, h⟩ := hardyW_two_line_lower
  refine ⟨2 + t₁ * I, by simp; linarith, fun h0 => ?_⟩
  have := (h t₁ (by rw [abs_of_pos (by linarith)])).2
  rw [h0, norm_zero] at this; linarith

theorem exists_hardyW_ne_zero_lower : ∃ z : ℂ, z.im < 0 ∧ hardyW z ≠ 0 := by
  obtain ⟨t₁, ht₁, h⟩ := hardyW_two_line_lower
  refine ⟨2 + ((-t₁ : ℝ) : ℂ) * I, by simp; linarith, fun h0 => ?_⟩
  have := (h (-t₁) (by rw [abs_neg, abs_of_pos (by linarith)])).2
  rw [h0, norm_zero] at this; linarith

/-! ### polynomial growth of W in the strip -/

/-- ‖Γℝ′/Γℝ(s)‖ ≤ ‖s‖/4 + 5 for Re s > 0, |Im s| ≥ 2 (crude, from ‖ψ(w)‖ ≤ ‖w‖ + 8). -/
lemma norm_logDeriv_Gammaℝ_le_lin {s : ℂ} (hs : 0 < s.re) (him : 2 ≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤ ‖s‖ / 4 + 5 := by
  rw [Zeta23.RvM.logDeriv_Gammaℝ hs]
  have hw : 0 < (s / 2).re := by simp; linarith
  have hw' : 1 ≤ |(s / 2).im| := by
    have : (s / 2).im = s.im / 2 := by simp
    rw [this, abs_div, abs_two]; linarith
  have hψ := Zeta23.XiPrime.ZeroCount.norm_digamma_le hw hw'
  have hns : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; norm_num
  rw [hns] at hψ
  have hlogpi : Real.log Real.pi ≤ 2 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have h1 : ‖-(Real.log Real.pi : ℂ) / 2‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    norm_num; linarith
  have h2 : ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖ ≤ (1 / 2) * (‖s‖ / 2 + 8) := by
    rw [norm_mul]; norm_num; linarith
  calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖ := norm_add_le _ _
    _ ≤ 1 + (1 / 2) * (‖s‖ / 2 + 8) := add_le_add h1 h2
    _ = ‖s‖ / 4 + 5 := by ring

/-- ‖L₂(s)‖ ≤ 2|Im s| + 12 for 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2. -/
lemma norm_L2_le {s : ℂ} (hre : 1 / 8 ≤ s.re) (hre' : s.re ≤ 4) (him : 2 ≤ |s.im|) :
    ‖L2 s‖ ≤ 2 * |s.im| + 12 := by
  have hs : s.im ≠ 0 := by intro h; rw [h] at him; norm_num at him
  have hpos : 0 < s.re := by linarith
  rw [L2_eq hs]
  -- shift the (1−s)-term twice: 1 − s ↦ 5 − s, Re ≥ 1
  have hu1 : (1 - s).im ≠ 0 := im_one_sub_ne_zero hs
  have hu2 : (1 - s + 2).im ≠ 0 := by simpa using hs
  have hshift : logDeriv Gammaℝ (1 - s) = logDeriv Gammaℝ (5 - s) - 1 / (3 - s) - 1 / (1 - s) := by
    rw [logDeriv_Gammaℝ_shift hu1, logDeriv_Gammaℝ_shift hu2]
    have e2 : (1 : ℂ) - s + 2 = 3 - s := by ring
    have e3 : (3 : ℂ) - s + 2 = 5 - s := by ring
    rw [e2, e3]
  rw [hshift]
  have hns : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have hsre : |s.re| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hA := norm_logDeriv_Gammaℝ_le_lin hpos him
  have h5 : (5 - s).im = -s.im := by simp
  have hB := norm_logDeriv_Gammaℝ_le_lin (s := 5 - s) (by simp; linarith) (by rw [h5, abs_neg]; exact him)
  have hn5 : ‖(5 : ℂ) - s‖ ≤ 5 + ‖s‖ := by
    calc ‖(5 : ℂ) - s‖ ≤ ‖(5:ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ = 5 + ‖s‖ := by norm_num
  -- the two rational terms are ≤ 1/2 each
  have hinv : ∀ a : ℝ, ‖(1 : ℂ) / ((a : ℂ) - s)‖ ≤ 1 / 2 := by
    intro a
    rw [norm_div, norm_one]
    have : |s.im| ≤ ‖(a : ℂ) - s‖ := by
      have h := Complex.abs_im_le_norm ((a : ℂ) - s)
      simpa [abs_neg] using h
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h3 := hinv 3; have h1' := hinv 1
  push_cast at h3 h1'
  calc ‖(logDeriv Gammaℝ s + (logDeriv Gammaℝ (5 - s) - 1 / (3 - s) - 1 / (1 - s))) / 2‖
      = ‖logDeriv Gammaℝ s + (logDeriv Gammaℝ (5 - s) - 1 / (3 - s) - 1 / (1 - s))‖ / 2 := by
        rw [norm_div]; norm_num
    _ ≤ (‖logDeriv Gammaℝ s‖ + (‖logDeriv Gammaℝ (5 - s)‖ + ‖(1:ℂ) / (3 - s)‖ + ‖(1:ℂ) / (1 - s)‖)) / 2 := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((‖s‖ / 4 + 5) + ((5 + ‖s‖) / 4 + 5 + 1 / 2 + 1 / 2)) / 2 := by
        gcongr
        · exact hB.trans (by linarith)
    _ ≤ 2 * |s.im| + 12 := by nlinarith [norm_nonneg s]

/-- **growth of W**: ‖W(s)‖ ≤ C·|Im s|² on 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2. -/
theorem hardyW_growth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| →
    ‖hardyW s‖ ≤ C * |s.im| ^ 2 := by
  obtain ⟨Cζ, hCζ, hζb⟩ := Zeta23.RvM.zeta_growth (δ := 1 / 16) (by norm_num)
  refine ⟨40 * Cζ, by positivity, fun s hre hre' him => ?_⟩
  set t : ℝ := |s.im| with ht
  have ht2 : 2 ≤ t := him
  have hζ : ‖riemannZeta s‖ ≤ Cζ * t := hζb s (by linarith) (by linarith)
  have hζ' : ‖deriv riemannZeta s‖ ≤ 24 * Cζ * t :=
    Zeta23.XiPrime.ZeroCount.norm_deriv_zeta_le hCζ hζb hre him
  have hL : ‖L2 s‖ ≤ 2 * t + 12 := norm_L2_le hre hre' him
  calc ‖hardyW s‖ = ‖deriv riemannZeta s + L2 s * riemannZeta s‖ := rfl
    _ ≤ ‖deriv riemannZeta s‖ + ‖L2 s‖ * ‖riemannZeta s‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 24 * Cζ * t + (2 * t + 12) * (Cζ * t) := by gcongr
    _ ≤ 40 * Cζ * t ^ 2 := by
        have hCt : 0 ≤ Cζ * t := by positivity
        have h12 : 12 ≤ 6 * t := by linarith
        nlinarith [hCt, h12]

end Hardy
end XiPrime
end Zeta23

end
