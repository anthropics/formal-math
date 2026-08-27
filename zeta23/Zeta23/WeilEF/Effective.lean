/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Effective.lean — effective-EF extractions: explicit numeric constants for the
three remaining existential links in the EF pipeline.

E1. zeta_growth_quarter_explicit : ∀ s, 1/4 ≤ re ≤ 2 → 1 ≤ |im| → ‖ζ s‖ ≤ C₁ * |im| ^ 1
    with a named rational C₁ (the Euler–Maclaurin riemannZeta0
    pieces are all explicitly bounded inside).
E2. zeta_local_zero_count_explicit : N(t,t+1] ≤ A₀ * log(|t|+3) with named A₀
    (ZerosBound at radii (0.84, 0.95)-ish × the B from E1).
E3. mu_increment_explicit : |μ(t+r) − μ(t)| ≤ K(|r| + r²)/t with named K (from
    digamma_stirling's ≤ 3/im² remainder + the explicit main-term derivative).
-/
import Zeta23.RvM.ZetaGrowth
import Zeta23.RvM.LocalCount
import Zeta23.RvM.CountByIntegral
import Zeta23.GammaFacts.StirlingVert
import Zeta23.WeilEF.Landau
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Zeta23.ThmE.GammaFactsChiProof

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set

namespace Zeta23
namespace WeilEF

/-! ## E1: explicit growth constant on the quarter-strip -/

/-- **E1**: ‖ζ(s)‖ ≤ (13/2)·|Im s| on 1/4 ≤ Re s (≤ 2), |Im s| ≥ 1 — the explicit form of
zeta_growth_quarter's ∃-pair: (A, C) = (1, 13/2). -/
theorem zeta_growth_quarter_explicit {s : ℂ} (h₁ : (1/4 : ℝ) ≤ s.re) (h₃ : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (13/2) * |s.im| := by
  have h := Zeta23.RvM.riemannZeta_linear_growth (δ := 1/4) (by norm_num) h₁ h₃
  have : (5/2 + ((1:ℝ)/4)⁻¹) = (13/2 : ℝ) := by norm_num
  rwa [this] at h

/-! ## E1b: the partial fraction with fully numeric constant
`zeta_logDeriv_partial_fraction_explicit` is the forall-form of
Zeta23.WeilEF.zeta_logDeriv_partial_fraction (Landau.lean) with constant 135000000: the same
proof body with the growth input specialized to A := 1, C0 := 13/2 (from
zeta_growth_quarter_explicit, `simpa [Real.rpow_one]`), so A' = max 1 0 = 1, C0 + 2 = 17/2,
and the final numeric fold
  (44795000*50/91)*(log 3 + log (17/2) + 1 + 1) <= 135000000
via log 3 <= 9/8 (3 <= e^(9/8): e*e^(1/8) >= 2.7182818*(1+1/8) = 3.058, add_one_le_exp),
log (17/2) <= log 9 = 2*log 3 <= 9/4; sum <= 43/8; 24612638*43/8 <= 132293000.
-/

set_option maxHeartbeats 1600000 in
theorem zeta_logDeriv_partial_fraction_explicit : ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 135000000 * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ 135000000 * Real.log (|t| + 3) := by
  intro t ht
  set A : ℝ := 1 with hAdef
  set C₀ : ℝ := 13/2 with hC₀def
  have hC₀ : (0:ℝ) < C₀ := by rw [hC₀def]; norm_num
  have hgrow : ∀ s : ℂ, (1/4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C₀ * |s.im| ^ A := by
    intro s h₁ h₂ h₃
    rw [hC₀def, hAdef, Real.rpow_one]
    exact zeta_growth_quarter_explicit h₁ h₃
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hζs₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)
  have hlow : (1/3 : ℝ) ≤ ‖riemannZeta s₀‖ := Zeta23.RvM.zeta_lower_bound_two t
  -- analyticity on the closed ball of radius 91/50
  have hone : (1 : ℂ) ∉ Metric.closedBall s₀ (91/50) := by
    intro h
    rw [Metric.mem_closedBall, Complex.dist_eq] at h
    have him : ((1 : ℂ) - s₀).im = -t := by simp [hs₀]
    have : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
      calc |t| = |((1:ℂ) - s₀).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - s₀‖ := Complex.abs_im_le_norm _
    linarith
  have hfa : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    Zeta23.RvM.analyticOnNhd_riemannZeta hone
  -- the B-bound on the (24/25)·(91/50)-ball
  set B : ℝ := 3 * (C₀ * (|t| + 2) ^ A' + 2) with hB
  have ht2 : (1:ℝ) ≤ |t| + 2 := by linarith
  have hpow1 : (1:ℝ) ≤ (|t| + 2) ^ A' := Real.one_le_rpow ht2 hA'0
  have hB2 : 2 ≤ B := by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)), ‖riemannZeta w‖ ≤ B * ‖riemannZeta s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : |w.re - 2| ≤ 24/25 * (91/50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this
      linarith
    have hwim : |w.im - t| ≤ 24/25 * (91/50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this
      linarith
    have hwim1 : 1 ≤ |w.im| := by
      have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith [hwim]
    have hwimt : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h2 : |w.im| - |t| ≤ |w.im - t| := this
      linarith [hwim]
    have hbound : ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
      rcases le_or_gt w.re 2 with hre2 | hre2
      · have h14 : (1/4 : ℝ) ≤ w.re := by
          rw [abs_le] at hwre
          linarith
        have := hgrow w h14 hre2 hwim1
        calc ‖riemannZeta w‖ ≤ C₀ * |w.im| ^ A := this
          _ ≤ C₀ * (|t| + 2) ^ A' := by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^ A ≤ |w.im| ^ A' :=
                    Real.rpow_le_rpow_of_exponent_le hwim1 (le_max_left _ _)
                _ ≤ (|t| + 2) ^ A' := Real.rpow_le_rpow (by linarith) hwimt hA'0
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by linarith
      · have := Zeta23.RvM.norm_riemannZeta_le_of_two_le_re (s := w) (by linarith)
        have hπ : (Real.pi : ℝ) ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤ Real.pi ^ 2 / 6 := this
          _ ≤ 2 := hπ
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
    calc ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := hbound
      _ = (B * (1/3)) := by rw [hB]; ring
      _ ≤ B * ‖riemannZeta s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := logDeriv_partial_fraction_disk (f := riemannZeta)
    (by norm_num : (0:ℝ) < 91/50) hfa hζs₀ hB2 hfB
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [hZset]
  · refine hZcount.trans ?_
    have hT3 : (2:ℝ) ≤ Real.log (|t| + 3) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have h1 := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
        _ ≤ 9 := by norm_num
        _ ≤ |t| + 3 := by linarith
    have hlogB : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
      have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
        rw [hB]
        nlinarith [hpow1, hC₀]
      have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
        Real.log_le_log (by rw [hB]; positivity) h1
      rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
        Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
        Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
        Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
      have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
      have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
        rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
      rw [hBeq]
      nlinarith [mul_nonneg hA'0 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
        mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
        mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), hT3]
    have hratio : ((24/25 : ℝ))/(22/25) = 12/11 := by norm_num
    have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlogpos : (0:ℝ) < Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]
          linarith
      _ ≤ 12 * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 135000000 * Real.log (|t| + 3) := by
          have hA'1 : A' = 1 := by rw [hA', hAdef]; norm_num
          have hlog3 : Real.log 3 ≤ 9/8 := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have he := Real.exp_one_gt_d9
            have h18 : Real.exp (1/8 : ℝ) ≥ 1 + 1/8 := by
              have := Real.add_one_le_exp (1/8 : ℝ)
              linarith
            calc (3:ℝ) ≤ 2.718281828 * (1 + 1/8) := by norm_num
              _ ≤ Real.exp 1 * Real.exp (1/8) := by
                  have h0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
                  have h1 : (2.718281828:ℝ) ≤ Real.exp 1 := by linarith
                  nlinarith [Real.exp_pos (1/8 : ℝ)]
              _ = Real.exp (9/8 : ℝ) := by rw [← Real.exp_add]; norm_num
          have hlog17 : Real.log (C₀ + 2) ≤ 9/4 := by
            rw [hC₀def]
            have h9 : (13/2 : ℝ) + 2 ≤ 9 := by norm_num
            calc Real.log ((13:ℝ)/2 + 2) ≤ Real.log 9 := Real.log_le_log (by norm_num) h9
              _ = Real.log (3 ^ 2) := by norm_num
              _ = 2 * Real.log 3 := by rw [Real.log_pow]; push_cast; ring
              _ ≤ 9/4 := by linarith
          have hsum : Real.log 3 + Real.log (C₀ + 2) + A' ≤ 35/8 := by
            rw [hA'1]
            linarith
          have hc0 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          have hc1 : (0:ℝ) ≤ Real.log (C₀ + 2) := by
            rw [hC₀def]
            exact Real.log_nonneg (by norm_num)
          have hfold : (12:ℝ) * (Real.log 3 + Real.log (C₀ + 2) + A') ≤ 135000000 :=
            le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 12)) (by norm_num)
          calc (12:ℝ) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3))
              = (12 * (Real.log 3 + Real.log (C₀ + 2) + A')) * Real.log (|t| + 3) := by ring
            _ ≤ 135000000 * Real.log (|t| + 3) :=
              mul_le_mul_of_nonneg_right hfold (by linarith)
  · intro s hs hζs
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hζs).trans ?_
    have hT3 : (2:ℝ) ≤ Real.log (|t| + 3) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have h1 := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
        _ ≤ 9 := by norm_num
        _ ≤ |t| + 3 := by linarith
    have hlogB : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
      have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
        rw [hB]
        nlinarith [hpow1, hC₀]
      have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
        Real.log_le_log (by rw [hB]; positivity) h1
      rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
        Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
        Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
        Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
      have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
      have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
        rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
      rw [hBeq]
      nlinarith [mul_nonneg hA'0 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
        mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
        mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), hT3]
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 135000000 * Real.log (|t| + 3) := by
          have hA'1 : A' = 1 := by rw [hA', hAdef]; norm_num
          have hlog3 : Real.log 3 ≤ 9/8 := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have he := Real.exp_one_gt_d9
            have h18 : Real.exp (1/8 : ℝ) ≥ 1 + 1/8 := by
              have := Real.add_one_le_exp (1/8 : ℝ)
              linarith
            calc (3:ℝ) ≤ 2.718281828 * (1 + 1/8) := by norm_num
              _ ≤ Real.exp 1 * Real.exp (1/8) := by
                  have h0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
                  have h1 : (2.718281828:ℝ) ≤ Real.exp 1 := by linarith
                  nlinarith [Real.exp_pos (1/8 : ℝ)]
              _ = Real.exp (9/8 : ℝ) := by rw [← Real.exp_add]; norm_num
          have hlog17 : Real.log (C₀ + 2) ≤ 9/4 := by
            rw [hC₀def]
            have h9 : (13/2 : ℝ) + 2 ≤ 9 := by norm_num
            calc Real.log ((13:ℝ)/2 + 2) ≤ Real.log 9 := Real.log_le_log (by norm_num) h9
              _ = Real.log (3 ^ 2) := by norm_num
              _ = 2 * Real.log 3 := by rw [Real.log_pow]; push_cast; ring
              _ ≤ 9/4 := by linarith
          have hsum : Real.log 3 + Real.log (C₀ + 2) + A' ≤ 35/8 := by
            rw [hA'1]
            linarith
          have hlogT3nn : (0:ℝ) ≤ Real.log (|t| + 3) := by linarith
          have hc0 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          have hc1 : (0:ℝ) ≤ Real.log (C₀ + 2) := by
            rw [hC₀def]
            exact Real.log_nonneg (by norm_num)
          have hfold : (44795000 / (91/50) : ℝ) * (Real.log 3 + Real.log (C₀ + 2) + A')
              ≤ 135000000 :=
            le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 44795000 / (91/50)))
              (by norm_num)
          calc 44795000 / (91/50)
                * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3))
              = (44795000 / (91/50) * (Real.log 3 + Real.log (C₀ + 2) + A'))
                * Real.log (|t| + 3) := by ring
            _ ≤ 135000000 * Real.log (|t| + 3) :=
                mul_le_mul_of_nonneg_right hfold hlogT3nn


/-! ## E3: explicit mu-increment constant -/

/-- mu agrees with the chi-side muq at (kappa, q) = (0, 1). -/
theorem mu_eq_muq01 : Zeta23.mu = Zeta23.ThmE.muq 0 1 := by
  funext τ
  simp only [Zeta23.mu, Zeta23.ThmE.muq]
  have h1 : Real.log ((1:ℕ) / Real.pi) = -Real.log Real.pi := by
    push_cast
    rw [one_div, Real.log_inv]
  rw [h1]
  have h2 : (1/4 : ℂ) + ((0:ℕ):ℂ) / 2 + Complex.I * (τ:ℂ) / 2
      = 1/4 + Complex.I * (τ:ℂ) / 2 := by
    push_cast
    ring
  rw [h2]
  ring

/-- **E3a**: explicit derivative bound for the ζ-side μ: |μ′(τ)| ≤ (24/π)/|τ| for |τ| ≥ 1. -/
theorem mu_deriv_bound_explicit (τ : ℝ) (hτ : 1 ≤ |τ|) :
    |deriv Zeta23.mu τ| ≤ (24 / Real.pi) / |τ| := by
  rw [mu_eq_muq01]
  exact Zeta23.ThmE.GammaChi.muq_deriv_bound_const (q := 1) (by norm_num) τ hτ

/-- **E3**: fully explicit μ-increment bound, K = 16: for t ≥ 2 and t + r ≥ 2,
|μ(t+r) − μ(t)| ≤ 16·(|r| + r²)/t.  (Both-endpoints-≥-2 is exactly what the prime-side
consumers use — the Ix-window keeps both points in [T, 2T].)  Proof: MVT with
mu_deriv_bound_explicit; for r ≥ −t/2 the whole segment has |τ| ≥ t/2 so |μ′| ≤ (48/π)/t;
otherwise t + r < t/2 forces |r| > t/2, and |μ′| ≤ 12/π on [2, ∞) gives
|Δμ| ≤ (12/π)|r| ≤ (24/π)·r²/t.  48/π ≤ 16. -/
theorem mu_increment_explicit (t : ℝ) (ht : 2 ≤ t) (r : ℝ) (htr : 2 ≤ t + r) :
    |Zeta23.mu (t + r) - Zeta23.mu t| ≤ 16 * (|r| + r ^ 2) / t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hsmooth : ContDiff ℝ ⊤ (Zeta23.mu) := by
    rw [mu_eq_muq01]
    exact (Zeta23.ThmE.GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) (by norm_num)).smooth
  have hdiff : Differentiable ℝ Zeta23.mu := hsmooth.differentiable (by simp)
  -- derivative bound on [m, ∞) for m ≥ 1
  have hderiv_on : ∀ m : ℝ, 1 ≤ m → ∀ τ ∈ Set.Icc (min t (t+r)) (max t (t+r)),
      m ≤ |τ| → |deriv Zeta23.mu τ| ≤ (24 / Real.pi) / m := by
    intro m hm τ _ hmτ
    have h1 := mu_deriv_bound_explicit τ (le_trans hm hmτ)
    calc |deriv Zeta23.mu τ| ≤ (24 / Real.pi) / |τ| := h1
      _ ≤ (24 / Real.pi) / m := by
          gcongr
  rcases le_or_gt (t/2) (t + r) with hbig | hsmall
  · -- whole segment in [t/2, ∞), t/2 ≥ 1
    have hm1 : (1:ℝ) ≤ t/2 := by linarith
    have hseg : ∀ τ ∈ Set.Icc (min t (t+r)) (max t (t+r)), (t/2 : ℝ) ≤ |τ| := by
      intro τ hτ
      have h1 : t/2 ≤ τ := by
        rcases le_total t (t+r) with h | h
        · rw [min_eq_left h] at hτ
          linarith [hτ.1]
        · rw [min_eq_right h] at hτ
          linarith [hτ.1]
      calc t/2 ≤ τ := h1
        _ ≤ |τ| := le_abs_self τ
    have hbound : ∀ τ ∈ Set.Icc (min t (t+r)) (max t (t+r)),
        ‖deriv Zeta23.mu τ‖ ≤ (24 / Real.pi) / (t/2) := by
      intro τ hτ
      rw [Real.norm_eq_abs]
      exact hderiv_on (t/2) hm1 τ hτ (hseg τ hτ)
    have hmem1 : t ∈ Set.Icc (min t (t+r)) (max t (t+r)) :=
      ⟨min_le_left _ _, le_max_left _ _⟩
    have hmem2 : t + r ∈ Set.Icc (min t (t+r)) (max t (t+r)) :=
      ⟨min_le_right _ _, le_max_right _ _⟩
    have hmvt := (convex_Icc (min t (t+r)) (max t (t+r))).norm_image_sub_le_of_norm_deriv_le
      (f := Zeta23.mu) (fun τ _ => hdiff τ) hbound hmem1 hmem2
    rw [Real.norm_eq_abs, show t + r - t = r by ring, Real.norm_eq_abs] at hmvt
    have hπ3 : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hcoef : (24 / Real.pi) / (t/2) ≤ 16 / t := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ ht0 ht0]
      have h24 : 24 / Real.pi ≤ 8 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]
        linarith
      nlinarith
    calc |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (24 / Real.pi) / (t/2) * |r| := hmvt
      _ ≤ 16 / t * |r| := by
          have : (0:ℝ) ≤ |r| := abs_nonneg r
          exact mul_le_mul_of_nonneg_right hcoef this
      _ ≤ 16 * (|r| + r ^ 2) / t := by
          rw [div_mul_eq_mul_div]
          gcongr
          nlinarith [sq_nonneg r, abs_nonneg r]
  · -- t + r < t/2: then |r| > t/2; both endpoints ≥ 2 so |μ′| ≤ 12/π on the segment
    have hr2 : t + r < t/2 := hsmall
    have hrneg : r < -(t/2) := by linarith
    have hrabs : t/2 < |r| := by
      rw [abs_of_neg (by linarith : r < 0)]
      linarith
    have hseg2 : ∀ τ ∈ Set.Icc (min t (t+r)) (max t (t+r)), (2:ℝ) ≤ |τ| := by
      intro τ hτ
      have hmin : min t (t+r) = t + r := min_eq_right (by linarith)
      rw [hmin] at hτ
      have h1 : 2 ≤ τ := le_trans htr hτ.1
      calc (2:ℝ) ≤ τ := h1
        _ ≤ |τ| := le_abs_self τ
    have hbound2 : ∀ τ ∈ Set.Icc (min t (t+r)) (max t (t+r)),
        ‖deriv Zeta23.mu τ‖ ≤ (24 / Real.pi) / 2 := by
      intro τ hτ
      rw [Real.norm_eq_abs]
      exact hderiv_on 2 (by norm_num) τ hτ (hseg2 τ hτ)
    have hmem1 : t ∈ Set.Icc (min t (t+r)) (max t (t+r)) :=
      ⟨min_le_left _ _, le_max_left _ _⟩
    have hmem2 : t + r ∈ Set.Icc (min t (t+r)) (max t (t+r)) :=
      ⟨min_le_right _ _, le_max_right _ _⟩
    have hmvt := (convex_Icc (min t (t+r)) (max t (t+r))).norm_image_sub_le_of_norm_deriv_le
      (f := Zeta23.mu) (fun τ _ => hdiff τ) hbound2 hmem1 hmem2
    rw [Real.norm_eq_abs, show t + r - t = r by ring, Real.norm_eq_abs] at hmvt
    have hπ3 : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have h24 : 24 / Real.pi ≤ 8 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]
      linarith
    -- (12/π)|r| ≤ 4|r| ≤ 8 r²/t  (since |r| > t/2 → r² > |r|·t/2 → r²/t > |r|/2)
    calc |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (24 / Real.pi) / 2 * |r| := hmvt
      _ ≤ 4 * |r| := by nlinarith [abs_nonneg r]
      _ ≤ 16 * (|r| + r ^ 2) / t := by
          rw [le_div_iff₀ ht0]
          have hr2' : |r| * t ≤ 2 * r ^ 2 := by
            have h1 : |r| * t < |r| * (2 * |r|) := by
              have : (0:ℝ) < |r| := by linarith
              nlinarith
            nlinarith [sq_abs r]
          nlinarith [abs_nonneg r, sq_nonneg r]

/-! ## E2(i): explicit local zero count away from the origin -/

set_option maxHeartbeats 800000 in
/-- **E2(i)**: for |t + 1/2| ≥ 6, the unit-window zero count satisfies
N(t, t+1] ≤ 540000000·log(|t|+3) — explicit, via reflection halving
(zetaZeroConfig.N_le_two_mul_half) + the explicit partial-fraction count conjunct
(the half-window {Re ≥ 1/2, ordinate ∈ (t, t+1]} sits inside the counting ball
of radius (22/25)(91/50) around 2 + (t+1/2)i: distance² ≤ (3/2)² + (1/2)² < 1.6016²). -/
theorem zeta_local_count_explicit_large (t : ℝ) (hc : 6 ≤ |t + 1/2|) :
    (Zeta23.Ncount t (t + 1) : ℝ) ≤ 540000000 * Real.log (|t| + 3) := by
  obtain ⟨Z, hZset, hZcount, -⟩ := zeta_logDeriv_partial_fraction_explicit (t + 1/2) hc
  have hhalf := Zeta23.zetaZeroConfig.N_le_two_mul_half (T₁ := t) (T₂ := t + 1)
  set S : Set ℂ := Zeta23.zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hSdef
  have hsubset : S ⊆ (Z : Set ℂ) := by
    rintro ρ ⟨⟨hcar, him1, him2⟩, hre⟩
    rw [hZset]
    have hnz : Zeta23.IsNontrivialZero ρ := hcar
    refine ⟨?_, hnz.1⟩
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hre2 : ρ.re < 1 := hnz.2.2
    have hremem : (1/2 : ℝ) ≤ ρ.re := hre
    have h1 : |ρ.re - 2| ≤ 3/2 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have h2 : |ρ.im - (t + 1/2)| ≤ 1/2 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hnormsq : ‖ρ - (2 + (t + 1/2 : ℝ) * Complex.I)‖ ^ 2
        = (ρ.re - 2) ^ 2 + (ρ.im - (t + 1/2)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre' : (ρ - (2 + (t + 1/2 : ℝ) * Complex.I)).re = ρ.re - 2 := by simp
      have him' : (ρ - (2 + (t + 1/2 : ℝ) * Complex.I)).im = ρ.im - (t + 1/2) := by simp
      rw [hre', him']
      ring
    have hsq : ‖ρ - (2 + (t + 1/2 : ℝ) * Complex.I)‖ ^ 2 ≤ 5/2 := by
      rw [hnormsq]
      have ha := abs_le.mp h1
      have hb := abs_le.mp h2
      nlinarith [ha.1, ha.2, hb.1, hb.2]
    nlinarith [norm_nonneg (ρ - (2 + (t + 1/2 : ℝ) * Complex.I)), hsq]
  have hSfin : S.Finite := Z.finite_toSet.subset hsubset
  have hsum : (∑ᶠ ρ ∈ S, (Zeta23.zetaZeroConfig.mult ρ : ℝ))
      ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    have hsub2 : hSfin.toFinset ⊆ Z := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      exact Finset.mem_coe.mp (hsubset hρ)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun ρ _ _ => by positivity)
  have hlogfold : Real.log (|t + 1/2| + 3) ≤ 2 * Real.log (|t| + 3) := by
    have h1 : |t + 1/2| + 3 ≤ (|t| + 3) ^ 2 := by
      have := abs_add_le t (1/2 : ℝ)
      nlinarith [abs_nonneg t]
    calc Real.log (|t + 1/2| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
          Real.log_le_log (by positivity) h1
      _ = 2 * Real.log (|t| + 3) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hNle : (Zeta23.Ncount t (t + 1) : ℝ) = (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ) := by
    rw [Zeta23.zetaZeroConfig_N]
  rw [hNle]
  have hlognn : (0:ℝ) ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  calc (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ)
      ≤ 2 * ∑ᶠ ρ ∈ S, (Zeta23.zetaZeroConfig.mult ρ : ℝ) := hhalf
    _ ≤ 2 * ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) := by linarith [hsum]
    _ ≤ 2 * (135000000 * Real.log (|t + 1/2| + 3)) := by linarith [hZcount]
    _ ≤ 2 * (135000000 * (2 * Real.log (|t| + 3))) := by nlinarith [hlogfold]
    _ = 540000000 * Real.log (|t| + 3) := by ring

/-! ## E2(iii) brick 1: the Gamma-norm bound -/

/-- |Γ(z)| ≤ Γ(Re z) for Re z > 0 (integral representation + pointwise norm). -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  calc ‖∫ x in Set.Ioi (0:ℝ), ((-x).exp : ℂ) * (x:ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0:ℝ), ‖((-x).exp : ℂ) * (x:ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        have hx0 : (0:ℝ) < x := hx
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        simp

/-- ξ(s) := s(s−1)/2·Λ₀(s) + 1/2 — ENTIRE by construction (Λ₀ = completedRiemannZeta₀),
and equal to s(s−1)/2·Λ(s) away from {0, 1} (algebra with Λ = Λ₀ − 1/s − 1/(1−s)). -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1/2

theorem xi_differentiable : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _

theorem xi_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold xi
  rw [completedRiemannZeta_eq]
  have h1s : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- The ξ functional equation ξ(1−s) = ξ(s). -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem xi_two : xi 2 = (Real.pi : ℂ) / 6 := by
  rw [xi_eq 2 (by norm_num) (by norm_num)]
  have hΓ : Complex.Gammaℝ 2 ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by
        exact_mod_cast Real.pi_ne_zero))
    · rw [show (2:ℂ)/2 = 1 by norm_num, Complex.Gamma_one]
      norm_num
  have hz : riemannZeta 2 = completedRiemannZeta 2 / Complex.Gammaℝ 2 :=
    riemannZeta_def_of_ne_zero (by norm_num)
  have hΛ2 : completedRiemannZeta 2 = Complex.Gammaℝ 2 * riemannZeta 2 := by
    rw [hz]
    field_simp
  rw [hΛ2]
  have hΓval : Complex.Gammaℝ 2 = 1 / (Real.pi : ℂ) := by
    rw [Complex.Gammaℝ_def, show (2:ℂ)/2 = 1 by norm_num, Complex.Gamma_one, mul_one,
      show (-(2:ℂ))/2 = -1 by norm_num]
    rw [Complex.cpow_neg_one]
    norm_num
  have hζ2 : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := riemannZeta_two
  rw [hΓval, hζ2]
  field_simp
  ring

/-- Γ(x) ≤ 24 on [1/4, 5] (recurrence to [2,4] + monotonicity on [2,∞) + Γ(4) = 6, Γ(5) = 24). -/
theorem Real_Gamma_le_24 {x : ℝ} (hx1 : (1/4 : ℝ) ≤ x) (hx2 : x ≤ 5) :
    Real.Gamma x ≤ 24 := by
  have hΓ4 : Real.Gamma 4 = 6 := by
    rw [show (4:ℝ) = (3:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have hΓ5 : Real.Gamma 5 = 24 := by
    rw [show (5:ℝ) = (4:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rcases le_or_gt 2 x with h2 | h2
  · -- monotone branch
    calc Real.Gamma x ≤ Real.Gamma 5 :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr h2)
            (Set.mem_Ici.mpr (by norm_num)) hx2
      _ = 24 := hΓ5
  · -- recurrence branch: Γ(x) = Γ(x+2)/(x(x+1)), x+2 ∈ [9/4, 4)
    have hx0 : (0:ℝ) < x := by linarith
    have hrec : Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
      rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
        Real.Gamma_add_one (by linarith)]
      ring
    have hG2 : Real.Gamma (x + 2) ≤ 6 := by
      rcases le_or_gt 2 (x + 2) with h | h
      · calc Real.Gamma (x + 2) ≤ Real.Gamma 4 :=
            Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr h)
              (Set.mem_Ici.mpr (by norm_num)) (by linarith)
          _ = 6 := hΓ4
      · linarith
    have hge : (1/4 : ℝ) * (5/4) ≤ x * (x + 1) := by nlinarith
    have hΓpos : (0:ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx0
    have h6 : (x + 1) * x * Real.Gamma x ≤ 6 := by
      rw [← hrec]
      exact hG2
    nlinarith

/-- Pointwise bound for ξ on the right half-strip of the disk: for 1/2 ≤ Re s ≤ 10, s ≠ 1,
‖ξ(s)‖ ≤ ‖s‖/2·24·(‖s−1‖·(1/2 + ‖s‖/Re s) + 1). -/
theorem xi_norm_le_right {s : ℂ} (hre : (1/2 : ℝ) ≤ s.re) (hs1 : s ≠ 1)
    (hup : s.re ≤ 10) :
    ‖xi s‖ ≤ ‖s‖ / 2 * 24 * (‖s - 1‖ * (1/2 + ‖s‖ / s.re) + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hrepos : (0:ℝ) < s.re := by linarith
  rw [xi_eq s hs0 hs1]
  have hζ := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hrepos hs1
  have hΓne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hrepos
  have hΛ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [h]
    field_simp
  have hΓnorm : ‖Complex.Gammaℝ s‖ ≤ 24 := by
    rw [Complex.Gammaℝ_def, norm_mul]
    have h1 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hexp : (-s / 2).re = -(s.re / 2) := by
        simp [Complex.neg_re, Complex.div_re]
        ring
      rw [hexp, Real.rpow_neg Real.pi_pos.le]
      have hππ : (1:ℝ) ≤ Real.pi ^ (s.re / 2 : ℝ) :=
        Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith)
      rw [inv_le_one_iff₀]
      right
      exact hππ
    have h2 : ‖Complex.Gamma (s / 2)‖ ≤ 24 := by
      have hre2 : (0:ℝ) < (s / 2).re := by
        have : (s / 2).re = s.re / 2 := by
          rw [Complex.div_ofNat_re]
        rw [this]
        linarith
      calc ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma ((s / 2).re) := norm_Gamma_le_Gamma_re hre2
        _ ≤ 24 := by
            have heq : (s / 2).re = s.re / 2 := by
              rw [Complex.div_ofNat_re]
            refine Real_Gamma_le_24 ?_ ?_
            · rw [heq]
              linarith
            · rw [heq]
              linarith
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤ 1 * 24 := by
          exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 24 := by norm_num
  have hprod : ‖(s - 1) * riemannZeta s‖ ≤ ‖s - 1‖ * (1/2 + ‖s‖ / s.re) + 1 := by
    rw [norm_mul]
    have h1 : ‖s - 1‖ * ‖riemannZeta s‖
        ≤ ‖s - 1‖ * (1/2 + 1 / ‖1 - s‖ + ‖s‖ / s.re) :=
      mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
    have h2 : ‖s - 1‖ * (1 / ‖1 - s‖) ≤ 1 := by
      rw [norm_sub_rev]
      rcases eq_or_ne (‖(1:ℂ) - s‖) 0 with h | h
      · rw [h]
        norm_num
      · rw [mul_one_div, div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))]
    nlinarith [norm_nonneg (s - 1), norm_nonneg s, norm_nonneg (riemannZeta s),
      div_nonneg (norm_nonneg s) hrepos.le]
  calc ‖s * (s - 1) / 2 * completedRiemannZeta s‖
      = ‖s‖ / 2 * (‖Complex.Gammaℝ s‖ * ‖(s - 1) * riemannZeta s‖) := by
        rw [hΛ]
        rw [show s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s)
          = s / 2 * (Complex.Gammaℝ s * ((s - 1) * riemannZeta s)) by ring]
        rw [norm_mul, norm_mul, norm_div]
        simp [Complex.norm_ofNat]
    _ ≤ ‖s‖ / 2 * (24 * (‖s - 1‖ * (1/2 + ‖s‖ / s.re) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul hΓnorm hprod (norm_nonneg _) (by norm_num)
    _ = ‖s‖ / 2 * 24 * (‖s - 1‖ * (1/2 + ‖s‖ / s.re) + 1) := by ring

/-- Numeric ξ-bound on the counting disk: ‖ξ(s)‖ ≤ 32000 for ‖s − 2‖ ≤ 1992/250 (= 7.968). -/
theorem xi_norm_le_ball {s : ℂ} (hs : ‖s - (2:ℂ)‖ ≤ 1992/250) : ‖xi s‖ ≤ 32000 := by
  have hnorm_s : ‖s‖ ≤ 2 + 1992/250 := by
    calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
      _ ≤ ‖s - (2:ℂ)‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ ≤ 1992/250 + 2 := by
          have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
          linarith [h2 ▸ le_refl (‖(2:ℂ)‖)]
      _ = 2 + 1992/250 := by ring
  have hre_bounds : -6 ≤ s.re ∧ s.re ≤ 10 := by
    have h := Complex.abs_re_le_norm (s - 2)
    have hre2 : (s - 2).re = s.re - 2 := by simp
    rw [hre2] at h
    have := abs_le.mp (h.trans hs)
    constructor <;> linarith [this.1, this.2]
  rcases le_or_gt (1/2 : ℝ) s.re with hgt | hlt
  · -- right branch
    rcases eq_or_ne s 1 with rfl | hs1
    · -- ξ(1) = 1/2
      have : xi 1 = 1/2 := by
        unfold xi
        norm_num
      rw [this]
      rw [show ‖(1/2 : ℂ)‖ = 1/2 by norm_num]
      norm_num
    · have h := xi_norm_le_right hgt hs1 hre_bounds.2
      have hs1n : ‖s - 1‖ ≤ 1 + 1992/250 := by
        calc ‖s - 1‖ = ‖(s - 2) + 1‖ := by ring_nf
          _ ≤ ‖s - (2:ℂ)‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ ≤ 1992/250 + 1 := by
              have h1 : ‖(1:ℂ)‖ = 1 := by norm_num
              linarith [h1 ▸ le_refl (‖(1:ℂ)‖)]
          _ = 1 + 1992/250 := by ring
      have hdiv : ‖s‖ / s.re ≤ (2 + 1992/250) / (1/2) := by
        have h1 : ‖s‖ / s.re ≤ ‖s‖ / (1/2) := by
          gcongr
        refine h1.trans ?_
        gcongr
      refine h.trans ?_
      calc ‖s‖ / 2 * 24 * (‖s - 1‖ * (1/2 + ‖s‖ / s.re) + 1)
          ≤ (2 + 1992/250) / 2 * 24
            * ((1 + 1992/250) * (1/2 + (2 + 1992/250) / (1/2)) + 1) := by
            gcongr <;> first | assumption | positivity
        _ ≤ 32000 := by norm_num
  · -- left branch: reflect through the functional equation
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [← xi_one_sub 0]
      have h1 : (1:ℂ) - 0 = 1 := by norm_num
      rw [h1]
      have : xi 1 = 1/2 := by
        unfold xi
        norm_num
      rw [this, show ‖(1/2 : ℂ)‖ = 1/2 by norm_num]
      norm_num
    · rw [← xi_one_sub s]
      have hwre : (1/2 : ℝ) ≤ (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hwre10 : (1 - s).re ≤ 10 := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [hre_bounds.1]
      have hw1 : (1 : ℂ) - s ≠ 1 := by
        intro h
        exact hs0 (by linear_combination -h)
      have h := xi_norm_le_right hwre hw1 hwre10
      have hns : ‖s‖ ≤ 2 + 1992/250 := hnorm_s
      have hn1s : ‖(1:ℂ) - s‖ ≤ 3 + 1992/250 := by
        calc ‖(1:ℂ) - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le _ _
          _ ≤ 1 + (2 + 1992/250) := by
              have h1 : ‖(1:ℂ)‖ = 1 := by norm_num
              linarith [h1 ▸ le_refl (‖(1:ℂ)‖)]
          _ = 3 + 1992/250 := by ring
      have hmid : ‖(1:ℂ) - s - 1‖ = ‖s‖ := by
        rw [show (1:ℂ) - s - 1 = -s by ring, norm_neg]
      have hdivw : ‖(1:ℂ) - s‖ / (1 - s).re ≤ (3 + 1992/250) / (1/2) := by
        have h1 : ‖(1:ℂ) - s‖ / (1 - s).re ≤ ‖(1:ℂ) - s‖ / (1/2) := by
          gcongr
        refine h1.trans ?_
        gcongr
      refine h.trans ?_
      rw [hmid]
      calc ‖(1:ℂ) - s‖ / 2 * 24 * (‖s‖ * (1/2 + ‖(1:ℂ) - s‖ / (1 - s).re) + 1)
          ≤ (3 + 1992/250) / 2 * 24
            * ((2 + 1992/250) * (1/2 + (3 + 1992/250) / (1/2)) + 1) := by
            gcongr <;> first | assumption | positivity
        _ ≤ 32000 := by norm_num

set_option maxHeartbeats 1600000 in
/-- **E2(ii): the small-box count.**  For |t + 1/2| < 6, N(t, t+1] ≤ 144 (Jensen/Landau disk
for ξ at centre 2, radius 83/10, with the numeric ball bound ‖ξ‖ ≤ 32000 = 62000·‖ξ(2)‖·…). -/
theorem zeta_local_count_box (t : ℝ) (hc : |t + 1/2| < 6) :
    (Zeta23.Ncount t (t + 1) : ℝ) ≤ 144 := by
  have hfa : AnalyticOnNhd ℂ xi (Metric.closedBall (2:ℂ) (83/10)) := fun s _ =>
    xi_differentiable.analyticAt s
  have hxi2 : xi 2 ≠ 0 := by
    rw [xi_two]
    simp only [ne_eq, div_eq_zero_iff]
    push Not
    constructor
    · exact_mod_cast Real.pi_ne_zero
    · norm_num
  have hxi2norm : ‖xi 2‖ = Real.pi / 6 := by
    rw [xi_two]
    rw [show ((Real.pi : ℂ) / 6) = ((Real.pi / 6 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hB2 : (2:ℝ) ≤ 62000 := by norm_num
  have hfB : ∀ w ∈ Metric.closedBall (2:ℂ) (24/25 * (83/10)), ‖xi w‖ ≤ 62000 * ‖xi 2‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hw' : ‖w - (2:ℂ)‖ ≤ 1992/250 := le_trans hw (by norm_num)
    calc ‖xi w‖ ≤ 32000 := xi_norm_le_ball hw'
      _ ≤ 62000 * (Real.pi / 6) := by nlinarith [Real.pi_gt_d2]
      _ = 62000 * ‖xi 2‖ := by rw [hxi2norm]
  obtain ⟨Z, hZset, hZcount, -⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (f := xi) (by norm_num : (0:ℝ) < 83/10) hfa hxi2 hB2 hfB
  -- the window sits inside the zero-ball
  have hhalfwin : Zeta23.zetaZeroConfig.window t (t + 1) ⊆ (Z : Set ℂ) := by
    rintro ρ ⟨hcar, him1, him2⟩
    rw [hZset]
    have hnz : Zeta23.IsNontrivialZero ρ := hcar
    have hre0 : 0 < ρ.re := hnz.2.1
    have hre1 : ρ.re < 1 := hnz.2.2
    have hΛ0 : completedRiemannZeta ρ = 0 :=
      (Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos hre0).mpr hnz.1
    have hρ0 : ρ ≠ 0 := by
      intro h
      rw [h] at hre0
      norm_num at hre0
    have hρ1 : ρ ≠ 1 := by
      intro h
      rw [h] at hre1
      norm_num at hre1
    refine ⟨?_, ?_⟩
    · -- ball membership: |im ρ| ≤ 13/2 and re ∈ (0,1): distance to 2 ≤ sqrt(4 + 42.25) ≤ 7.3
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have him : |ρ.im| ≤ 13/2 := by
        rw [abs_le]
        have h1 := abs_lt.mp hc
        constructor <;> linarith
      have hnormsq : ‖ρ - (2:ℂ)‖ ^ 2 = (ρ.re - 2) ^ 2 + ρ.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have h1 : (ρ - (2:ℂ)).re = ρ.re - 2 := by simp
        have h2 : (ρ - (2:ℂ)).im = ρ.im := by simp
        rw [h1, h2]
        ring
      have hsq : ‖ρ - (2:ℂ)‖ ^ 2 ≤ (22/25 * (83/10)) ^ 2 := by
        rw [hnormsq]
        have ha := abs_le.mp him
        nlinarith
      nlinarith [norm_nonneg (ρ - (2:ℂ))]
    · -- xi ρ = 0
      rw [xi_eq ρ hρ0 hρ1, hΛ0]
      ring
  -- orders: ord_xi = zeroMult on the window
  have hord : ∀ ρ ∈ Zeta23.zetaZeroConfig.window t (t + 1),
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) ≤ (analyticOrderNatAt xi ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨hcar, -, -⟩ := hρ
    have hnz : Zeta23.IsNontrivialZero ρ := hcar
    have hre0 : 0 < ρ.re := hnz.2.1
    have hre1 : ρ.re < 1 := hnz.2.2
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre0; norm_num at hre0
    have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre1; norm_num at hre1
    have hcongr : analyticOrderNatAt xi ρ = analyticOrderNatAt completedRiemannZeta ρ := by
      have hopen : IsOpen {s : ℂ | s ≠ 0 ∧ s ≠ 1} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_ne
        · exact isOpen_ne
      have hmem : ρ ∈ {s : ℂ | s ≠ 0 ∧ s ≠ 1} := ⟨hρ0, hρ1⟩
      have hev : xi =ᶠ[nhds ρ] (fun s => s * (s - 1) / 2) * completedRiemannZeta := by
        refine Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => ?_)
        exact xi_eq s hs.1 hs.2
      have hpre : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ := by
        apply Differentiable.analyticAt
        exact (differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2
      have hΛa : AnalyticAt ℂ completedRiemannZeta ρ :=
        Zeta23.RvM.analyticAt_completedRiemannZeta hρ0 hρ1
      have hpre0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) ρ = 0 := by
        rw [hpre.analyticOrderAt_eq_zero]
        intro h
        have h2 : ρ * (ρ - 1) = 0 := by
          field_simp at h
          simpa using h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact hρ0 h3
        · exact hρ1 (by linear_combination h3)
      unfold analyticOrderNatAt
      rw [analyticOrderAt_congr hev, analyticOrderAt_mul hpre hΛa, hpre0, zero_add]
    rw [hcongr, Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta hre0 hρ1]
    exact le_refl _
  -- assemble
  have hWfin : (Zeta23.zetaZeroConfig.window t (t + 1)).Finite :=
    Zeta23.zetaZeroConfig.window_finite t (t + 1)
  have hNle : (Zeta23.Ncount t (t + 1) : ℝ) = (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ) := by
    rw [Zeta23.zetaZeroConfig_N]
  rw [hNle]
  have hsum : (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ)
      ≤ ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℝ) := by
    have hN : (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ)
        = ∑ ρ ∈ hWfin.toFinset, (Zeta23.zetaZeroConfig.mult ρ : ℝ) := by
      have h1 : Zeta23.zetaZeroConfig.N t (t + 1)
          = ∑ ρ ∈ hWfin.toFinset, Zeta23.zetaZeroConfig.mult ρ := by
        rw [ZeroConfig.N, finsum_mem_eq_finite_toFinset_sum _ hWfin]
      rw [h1]
      push_cast
      rfl
    rw [hN]
    have hsub2 : hWfin.toFinset ⊆ Z := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      exact Finset.mem_coe.mp (hhalfwin hρ)
    calc ∑ ρ ∈ hWfin.toFinset, (Zeta23.zetaZeroConfig.mult ρ : ℝ)
        ≤ ∑ ρ ∈ hWfin.toFinset, (analyticOrderNatAt xi ρ : ℝ) := by
          refine Finset.sum_le_sum (fun ρ hρ => ?_)
          rw [Set.Finite.mem_toFinset] at hρ
          exact hord ρ hρ
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun ρ _ _ => by positivity)
  refine hsum.trans ?_
  refine hZcount.trans ?_
  -- 12·log 62000 ≤ 144
  have hlp : (0:ℝ) < Real.log ((24/25 : ℝ)/(22/25)) := by
    rw [show ((24/25 : ℝ))/(22/25) = 12/11 by norm_num]
    exact Real.log_pos (by norm_num)
  have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25 : ℝ)/(22/25)) := by
    rw [show ((24/25 : ℝ))/(22/25) = 12/11 by norm_num]
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
    rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hlogB : Real.log 62000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have h12 : (2.7182818283:ℝ) ^ (12:ℕ) ≤ Real.exp 12 := by
      have : Real.exp 12 = (Real.exp 1) ^ (12:ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [this]
      gcongr <;> linarith
    calc (62000:ℝ) ≤ 2.7182818283 ^ (12:ℕ) := by norm_num
      _ ≤ Real.exp 12 := h12
  have hlogBnn : (0:ℝ) ≤ Real.log 62000 := Real.log_nonneg (by norm_num)
  calc 1 / Real.log ((24/25 : ℝ)/(22/25)) * Real.log 62000
      ≤ 12 * Real.log 62000 := by
        refine mul_le_mul_of_nonneg_right ?_ hlogBnn
        rw [div_le_iff₀ hlp]
        linarith
    _ ≤ 12 * 12 := by linarith
    _ = 144 := by norm_num

/-- **E2 — the fully explicit local zero count**:
N(t, t+1] ≤ 540000000·log(|t|+3) for every t ∈ ℝ, unconditionally. -/
theorem zeta_local_zero_count_explicit (t : ℝ) :
    (Zeta23.Ncount t (t + 1) : ℝ) ≤ 540000000 * Real.log (|t| + 3) := by
  rcases le_or_gt 6 (|t + 1/2|) with h | h
  · exact zeta_local_count_explicit_large t h
  · refine (zeta_local_count_box t h).trans ?_
    have h1 : (1:ℝ) ≤ Real.log (|t| + 3) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
      have := Real.exp_one_lt_d9
      linarith [abs_nonneg t]
    nlinarith

end WeilEF
end Zeta23
