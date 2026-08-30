/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/Y.lean — analytic estimates for Y := ξ′/Γℝ.

Y (Zeta23.XiPrime.Yfn, Seam.lean §3) is analytic on Re s > 0 with the zeros/multiplicities of ξ′.  Here:
  * Yfn_growth      : ‖Y(s)‖ ≤ C·|Im s|⁴ on 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2  (closed form + ζ linear growth
                      Zeta23.RvM.zeta_growth + Cauchy estimate for ζ′ + vertical Stirling for ψ);
  * two_line_lower  : for |t| ≥ t₁:  3 ≤ Re (L + ζ′/ζ)(2+it)  and  1 ≤ ‖Y(2+it)‖
                      (Re ψ(1+it/2) ≥ log(|t|/2) − 4 from Zeta23.StirlingVert.digamma_stirling, against the
                      t-uniform bound ‖ζ′/ζ(2+it)‖ ≤ ‖ζ′(2)/ζ(2)‖, and ‖ζ(2+it)‖ ≥ 1/3).
These are exactly the two inputs (growth on a disc inside Re s > 0, lower bound at its centre 2+it) that
Jensen/Landau need; cf. Zeta23/RvM/LocalCount.lean and Zeta23/WeilEF/Landau.lean for ζ.
-/
import Zeta23.XiPrime.Seam
import Zeta23.RvM.ZetaGrowth
import Zeta23.GammaFacts.StirlingVert
import Zeta23.FromPNTPlus.ZetaBounds
import Mathlib.Analysis.Complex.Liouville

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-! ### crude digamma bounds from vertical Stirling -/

/-- ‖ψ(w)‖ ≤ ‖w‖ + 8 for Re w > 0, |Im w| ≥ 1. -/
lemma norm_digamma_le {w : ℂ} (hw : 0 < w.re) (hw' : 1 ≤ |w.im|) :
    ‖Complex.digamma w‖ ≤ ‖w‖ + 8 := by
  have h := Zeta23.StirlingVert.digamma_stirling hw (by linarith)
  have him2 : 1 ≤ w.im ^ 2 := by
    have := sq_abs w.im
    nlinarith [abs_nonneg w.im]
  have h3 : 3 / w.im ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hw1 : 1 ≤ ‖w‖ := le_trans hw' (Complex.abs_im_le_norm w)
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw
  have hlog : ‖Complex.log w‖ ≤ ‖w‖ + Real.pi := by
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ ‖w‖ + Real.pi := by
          apply add_le_add _ (Complex.abs_arg_le_pi w)
          rw [abs_of_nonneg (Real.log_nonneg hw1)]
          linarith [Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < ‖w‖)]
  have hinv : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / 2 := by
    rw [norm_div]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, div_le_iff₀ (by linarith)]
    nlinarith
  calc ‖Complex.digamma w‖
      = ‖(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) + Complex.log w - (1 / 2 : ℂ) / w‖ := by
        ring_nf
    _ ≤ ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ + ‖Complex.log w‖ + ‖(1 / 2 : ℂ) / w‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 3 + (‖w‖ + Real.pi) + 1 / 2 := by linarith
    _ ≤ ‖w‖ + 8 := by linarith [Real.pi_lt_four]

/-- Re ψ(w) ≥ log |Im w| − 4 for Re w > 0, |Im w| ≥ 1. -/
lemma re_digamma_ge {w : ℂ} (hw : 0 < w.re) (hw' : 1 ≤ |w.im|) :
    Real.log |w.im| - 4 ≤ (Complex.digamma w).re := by
  have h := Zeta23.StirlingVert.digamma_stirling hw (by linarith)
  have him2 : 1 ≤ w.im ^ 2 := by
    have := sq_abs w.im
    nlinarith [abs_nonneg w.im]
  have h3 : 3 / w.im ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hw1 : 1 ≤ ‖w‖ := le_trans hw' (Complex.abs_im_le_norm w)
  have hre := Complex.abs_re_le_norm (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
  rw [abs_le] at hre
  have hre1 := hre.1
  simp only [Complex.sub_re, Complex.add_re] at hre1
  have hlogre : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  have hlogmono : Real.log |w.im| ≤ Real.log ‖w‖ :=
    Real.log_le_log (by linarith) (Complex.abs_im_le_norm w)
  have hinv : ((1 / 2 : ℂ) / w).re ≤ 1 / 2 := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_div]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ### growth of Y -/

/-- Cauchy estimate for ζ′ from the linear growth of ζ:  ‖ζ′(s)‖ ≤ 24·C_ζ·|Im s| for Re s ≥ 1/8, |Im s| ≥ 2. -/
lemma norm_deriv_zeta_le {C : ℝ} (hC : 0 < C)
    (hζ : ∀ s : ℂ, (1 / 16 : ℝ) ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im|)
    {s : ℂ} (hre : 1 / 8 ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖deriv riemannZeta s‖ ≤ 24 * C * |s.im| := by
  have hR : (0 : ℝ) < 1 / 16 := by norm_num
  -- on the circle: Re ≥ 1/16, 1 ≤ |Im| ≤ |Im s| + 1/16
  have hsph : ∀ z ∈ sphere s (1 / 16), ‖riemannZeta z‖ ≤ C * (|s.im| + 1) := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hre' : |(z - s).re| ≤ 1 / 16 := by rw [← hz]; exact Complex.abs_re_le_norm _
    have him' : |(z - s).im| ≤ 1 / 16 := by rw [← hz]; exact Complex.abs_im_le_norm _
    simp only [Complex.sub_re, Complex.sub_im] at hre' him'
    rw [abs_le] at hre' him'
    have h1 : (1 / 16 : ℝ) ≤ z.re := by linarith [hre'.1]
    have h2 : 1 ≤ |z.im| := by
      rcases le_abs'.mp him with h | h
      · rw [abs_of_neg (by linarith [him'.2])]; linarith [him'.2]
      · rw [abs_of_pos (by linarith [him'.1])]; linarith [him'.1]
    have h3 : |z.im| ≤ |s.im| + 1 := by
      have h5 : |z.im - s.im| ≤ 1 / 16 := abs_le.mpr ⟨him'.1, him'.2⟩
      have h6 := abs_sub_abs_le_abs_sub z.im s.im
      linarith
    calc ‖riemannZeta z‖ ≤ C * |z.im| := hζ z h1 h2
      _ ≤ C * (|s.im| + 1) := by gcongr
  have hdiff : DiffContOnCl ℂ riemannZeta (ball s (1 / 16)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (by norm_num)]
    intro z hz
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro hz1
    rw [mem_closedBall, Complex.dist_eq, hz1] at hz
    have : |((1 : ℂ) - s).im| ≤ 1 / 16 := le_trans (Complex.abs_im_le_norm _) hz
    simp at this
    rw [abs_le] at this
    have : |s.im| ≤ 1 / 16 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff hsph
  calc ‖deriv riemannZeta s‖ ≤ C * (|s.im| + 1) / (1 / 16) := key
    _ = 16 * C * (|s.im| + 1) := by ring
    _ ≤ 24 * C * |s.im| := by nlinarith

/-- ‖Γℝ′/Γℝ(s)‖ ≤ 4|Im s| for 0 < Re s ≤ 4, |Im s| ≥ 2 (crude). -/
lemma norm_logDeriv_Gammaℝ_le {s : ℂ} (hre : 0 < s.re) (hre' : s.re ≤ 4) (him : 2 ≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤ 4 * |s.im| := by
  rw [Zeta23.RvM.logDeriv_Gammaℝ hre]
  have hw : 0 < (s / 2).re := by simp; linarith
  have hw' : 1 ≤ |(s / 2).im| := by
    simp only [Complex.div_ofNat_im]
    rw [abs_div, abs_two]
    linarith
  have hψ := norm_digamma_le hw hw'
  have hs : ‖s‖ ≤ 4 + |s.im| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im s) ?_
    rw [abs_of_pos hre]
    linarith
  have hs2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; norm_num
  have hlogpi : ‖-(Real.log Real.pi : ℂ) / 2‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have : Real.log Real.pi ≤ 2 := by
      have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
      have h4' : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith [Real.log_two_lt_d9]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2)‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖ := norm_add_le _ _
    _ ≤ 1 + 1 / 2 * (‖s‖ / 2 + 8) := by
        gcongr
        rw [norm_mul, ← hs2]
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]
        gcongr
    _ ≤ 4 * |s.im| := by linarith

/-- **Polynomial growth of Y**: ‖Y(s)‖ ≤ C·|Im s|⁴ for 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2. -/
theorem Yfn_growth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| →
    ‖Yfn s‖ ≤ C * |s.im| ^ 4 := by
  obtain ⟨Cζ, hCζ, hζb⟩ := Zeta23.RvM.zeta_growth (δ := 1 / 16) (by norm_num)
  refine ⟨100 * Cζ, by positivity, fun s hre hre' him => ?_⟩
  have hpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at him; norm_num at him
  set t : ℝ := |s.im| with ht
  have ht2 : 2 ≤ t := him
  have hns : ‖s‖ ≤ 3 * t := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im s) ?_
    rw [abs_of_pos hpos]; linarith
  have hns1 : ‖s - 1‖ ≤ 4 * t := by
    refine le_trans (norm_sub_le _ _) ?_
    simp; linarith
  have hns12 : ‖s - 1 / 2‖ ≤ 4 * t := by
    refine le_trans (norm_sub_le _ _) ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]; linarith
  have hpoly : ‖s * (s - 1) / 2‖ ≤ 6 * t ^ 2 := by
    rw [norm_div, norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [this, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have := mul_le_mul hns hns1 (norm_nonneg _) (by positivity)
    nlinarith
  have hζ : ‖riemannZeta s‖ ≤ Cζ * t := hζb s (by linarith) (by linarith)
  have hζ' : ‖deriv riemannZeta s‖ ≤ 24 * Cζ * t := norm_deriv_zeta_le hCζ hζb hre him
  have hL : ‖logDeriv Gammaℝ s‖ ≤ 4 * t := norm_logDeriv_Gammaℝ_le hpos hre' him
  rw [Yfn_eq hpos hs1]
  have hA : ‖(s - 1 / 2) * riemannZeta s‖ ≤ 4 * Cζ * t ^ 2 := by
    rw [norm_mul]
    have := mul_le_mul hns12 hζ (norm_nonneg _) (by positivity)
    nlinarith
  have hB : ‖logDeriv Gammaℝ s * riemannZeta s + deriv riemannZeta s‖ ≤ 4 * Cζ * t ^ 2 + 24 * Cζ * t := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    have := mul_le_mul hL hζ (norm_nonneg _) (by positivity)
    nlinarith
  have hC : ‖s * (s - 1) / 2 * (logDeriv Gammaℝ s * riemannZeta s + deriv riemannZeta s)‖
      ≤ 6 * t ^ 2 * (4 * Cζ * t ^ 2 + 24 * Cζ * t) := by
    rw [norm_mul]
    exact mul_le_mul hpoly hB (norm_nonneg _) (by positivity)
  have h4 : 4 ≤ t ^ 2 := by nlinarith
  have ht4 : t ^ 2 ≤ t ^ 4 / 4 := by
    have : t ^ 2 * 4 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have ht3 : t ^ 3 ≤ t ^ 4 / 2 := by
    have : t ^ 3 * 2 ≤ t ^ 3 * t := mul_le_mul_of_nonneg_left ht2 (by positivity)
    nlinarith
  have e1 : 4 * Cζ * t ^ 2 ≤ Cζ * t ^ 4 := by
    have := mul_le_mul_of_nonneg_left ht4 hCζ.le; nlinarith
  have e2 : 144 * Cζ * t ^ 3 ≤ 72 * Cζ * t ^ 4 := by
    have := mul_le_mul_of_nonneg_left ht3 hCζ.le; nlinarith
  calc ‖(s - 1 / 2) * riemannZeta s
        + s * (s - 1) / 2 * (logDeriv Gammaℝ s * riemannZeta s + deriv riemannZeta s)‖
      ≤ 4 * Cζ * t ^ 2 + 6 * t ^ 2 * (4 * Cζ * t ^ 2 + 24 * Cζ * t) :=
        le_trans (norm_add_le _ _) (add_le_add hA hC)
    _ = 4 * Cζ * t ^ 2 + 24 * Cζ * t ^ 4 + 144 * Cζ * t ^ 3 := by ring
    _ ≤ Cζ * t ^ 4 + 24 * Cζ * t ^ 4 + 72 * Cζ * t ^ 4 := by linarith
    _ ≤ 100 * Cζ * t ^ 4 := by nlinarith [pow_nonneg (abs_nonneg s.im) 4]

/-- analyticity of Y on a closed disc of radius r < 2 about 2 + it. -/
theorem Yfn_analyticOnNhd_disc (t : ℝ) {r : ℝ} (hr : r < 2) :
    AnalyticOnNhd ℂ Yfn (closedBall (2 + t * I) r) := by
  apply Yfn_analyticOnNhd
  intro s hs
  rw [mem_closedBall, Complex.dist_eq] at hs
  have := Complex.abs_re_le_norm (s - (2 + t * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at this
  rw [abs_le] at this
  show 0 < s.re
  linarith [this.1]

/-! ### the line Re s = 2 -/

lemma two_line_re (t : ℝ) : ((2 : ℂ) + t * I).re = 2 := by simp
lemma two_line_im (t : ℝ) : ((2 : ℂ) + t * I).im = t := by simp
lemma two_line_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := fun h => by
  have := congrArg Complex.re h; simp at this
lemma two_line_ne_zero (t : ℝ) : (2 : ℂ) + t * I ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this
lemma zeta_two_line_ne_zero (t : ℝ) : riemannZeta (2 + t * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp)

/-- t-uniform bound for ζ′/ζ on Re s = 2: ‖ζ′/ζ(2+it)‖ ≤ ‖ζ′(2)/ζ(2)‖. -/
lemma norm_logDeriv_zeta_two_le (t : ℝ) :
    ‖logDeriv riemannZeta (2 + t * I)‖ ≤ ‖deriv riemannZeta 2 / riemannZeta 2‖ := by
  have h := dlog_riemannZeta_bdd_on_vertical_lines_generalized 2 2 t (by norm_num) le_rfl
  rw [neg_div, norm_neg] at h
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [e2] at h
  rw [logDeriv_apply]
  exact h

/-- Re L(2+it) ≥ ½ log(|t|/2) − 3 for |t| ≥ 2. -/
lemma re_Lfn_two_ge {t : ℝ} (ht : 2 ≤ |t|) :
    (1 / 2) * Real.log (|t| / 2) - 3 ≤ (Lfn (2 + t * I)).re := by
  rw [Lfn_eq_digamma (by simp : (0:ℝ) < ((2 : ℂ) + t * I).re)]
  have hw : 0 < (((2 : ℂ) + t * I) / 2).re := by simp
  have hwim : (((2 : ℂ) + t * I) / 2).im = t / 2 := by simp
  have hw' : 1 ≤ |(((2 : ℂ) + t * I) / 2).im| := by
    rw [hwim, abs_div, abs_two]; linarith
  have hψ := re_digamma_ge hw hw'
  rw [hwim, abs_div, abs_two] at hψ
  have h1 : 0 ≤ (1 / ((2 : ℂ) + t * I)).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (by simp) (Complex.normSq_nonneg _)
  have h2 : 0 ≤ (1 / ((2 : ℂ) + t * I - 1)).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hlogpi : Real.log Real.pi ≤ 2 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hre_const : (-(Real.log Real.pi : ℂ) / 2).re = -(Real.log Real.pi) / 2 := by
    simp [Complex.neg_re, Complex.div_ofNat_re]
  have hre_half : ((1 / 2 : ℂ) * Complex.digamma (((2 : ℂ) + t * I) / 2)).re
      = (1 / 2) * (Complex.digamma (((2 : ℂ) + t * I) / 2)).re := by
    rw [Complex.mul_re]; simp
  simp only [Complex.add_re]
  rw [hre_const, hre_half]
  linarith

/-- **Lower bounds on the line Re s = 2, far up**: there is t₁ ≥ 2 such that for |t| ≥ t₁,
  3 ≤ Re (L + ζ′/ζ)(2+it)   and   1 ≤ ‖Y(2+it)‖. -/
theorem two_line_lower : ∃ t₁ : ℝ, 2 ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ |t| →
    3 ≤ (Lfn (2 + t * I) + logDeriv riemannZeta (2 + t * I)).re ∧ 1 ≤ ‖Yfn (2 + t * I)‖ := by
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
  have hL := re_Lfn_two_ge ht2
  have hζζ : -K ≤ (logDeriv riemannZeta (2 + t * I)).re := by
    have h1 := Complex.abs_re_le_norm (logDeriv riemannZeta (2 + t * I))
    rw [abs_le] at h1
    linarith [h1.1, norm_logDeriv_zeta_two_le t]
  have hG : 3 ≤ (Lfn (2 + t * I) + logDeriv riemannZeta (2 + t * I)).re := by
    rw [Complex.add_re]; linarith
  refine ⟨hG, ?_⟩
  -- ‖Y‖ = ‖s(s−1)/2‖ ‖ζ‖ ‖G‖ ≥ 1 · (1/3) · 3
  have hs : (0:ℝ) < ((2 : ℂ) + t * I).re := by simp
  rw [Yfn_eq_factor hs (two_line_ne_one t) (zeta_two_line_ne_zero t), norm_mul, norm_mul]
  have hp : 1 ≤ ‖((2 : ℂ) + t * I) * ((2 : ℂ) + t * I - 1) / 2‖ := by
    rw [norm_div, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have ha : 2 ≤ ‖(2 : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((2 : ℂ) + t * I)
      simpa using this
    have hb : 1 ≤ ‖(2 : ℂ) + t * I - 1‖ := by
      have := Complex.abs_re_le_norm ((2 : ℂ) + t * I - 1)
      simp at this
      norm_num at this
      exact this
    nlinarith [norm_nonneg ((2 : ℂ) + t * I - 1)]
  have hz : (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := Zeta23.RvM.zeta_lower_bound_two t
  have hGn : 3 ≤ ‖Lfn (2 + t * I) + logDeriv riemannZeta (2 + t * I)‖ :=
    le_trans hG (Complex.re_le_norm _)
  calc (1 : ℝ) = 1 * (1 / 3) * 3 := by norm_num
    _ ≤ ‖((2 : ℂ) + t * I) * ((2 : ℂ) + t * I - 1) / 2‖ * ‖riemannZeta (2 + t * I)‖
          * ‖Lfn (2 + t * I) + logDeriv riemannZeta (2 + t * I)‖ := by
        gcongr

/-! ### ‖Γℝ′/Γℝ‖ ≪ log (second-order Stirling) -/

/-- ‖Γℝ′/Γℝ(s)‖ ≤ log(|Im s|+3) + 5 for 0 < Re s ≤ 4, |Im s| ≥ 2. -/
lemma norm_logDeriv_Gammaℝ_le_log {s : ℂ} (hre : 0 < s.re) (hre' : s.re ≤ 4) (him : 2 ≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤ Real.log (|s.im| + 3) + 5 := by
  rw [Zeta23.RvM.logDeriv_Gammaℝ hre]
  set w : ℂ := s / 2 with hw
  have hwre : 0 < w.re := by simp [hw]; linarith
  have hwim : w.im = s.im / 2 := by simp [hw]
  have hw' : 1 ≤ |w.im| := by rw [hwim, abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.digamma_stirling hwre (by linarith)
  have him2 : 1 ≤ w.im ^ 2 := by have := sq_abs w.im; nlinarith [abs_nonneg w.im]
  have h3 : 3 / w.im ^ 2 ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hw1 : 1 ≤ ‖w‖ := le_trans hw' (Complex.abs_im_le_norm w)
  have hwle : ‖w‖ ≤ |s.im| + 3 := by
    have : ‖w‖ = ‖s‖ / 2 := by rw [hw, norm_div]; norm_num
    rw [this]
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hre] at this
    linarith
  have hlog : ‖Complex.log w‖ ≤ Real.log (|s.im| + 3) + Real.pi := by
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ Real.log (|s.im| + 3) + Real.pi := by
          apply add_le_add _ (Complex.abs_arg_le_pi w)
          rw [abs_of_nonneg (Real.log_nonneg hw1)]
          exact Real.log_le_log (by linarith) hwle
  have hinv : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / 2 := by
    rw [norm_div]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, div_le_iff₀ (by linarith)]
    nlinarith
  have hψ : ‖Complex.digamma w‖ ≤ Real.log (|s.im| + 3) + Real.pi + 7 / 2 := by
    calc ‖Complex.digamma w‖
        = ‖(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) + Complex.log w - (1 / 2 : ℂ) / w‖ := by
          ring_nf
      _ ≤ ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ + ‖Complex.log w‖ + ‖(1 / 2 : ℂ) / w‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 3 + (Real.log (|s.im| + 3) + Real.pi) + 1 / 2 := by linarith
      _ = Real.log (|s.im| + 3) + Real.pi + 7 / 2 := by ring
  have hlogpi : ‖-(Real.log Real.pi : ℂ) / 2‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have : Real.log Real.pi ≤ 2 := by
      have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
      have h4' : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith [Real.log_two_lt_d9]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]; linarith
  calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma w‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma w‖ := norm_add_le _ _
    _ ≤ 1 + 1 / 2 * (Real.log (|s.im| + 3) + Real.pi + 7 / 2) := by
        gcongr
        rw [norm_mul]
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]
        gcongr
    _ ≤ Real.log (|s.im| + 3) + 5 := by
        have := Real.log_nonneg (by linarith [abs_nonneg s.im] : (1:ℝ) ≤ |s.im| + 3)
        nlinarith [Real.pi_lt_four]

end ZeroCount
end XiPrime
end Zeta23
