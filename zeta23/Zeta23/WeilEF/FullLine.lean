/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/FullLine.lean — the R → ∞ limit of the rectangle identity
(Zeta23.WeilEF.rectangle_identity, proved): along good heights R_j ∈ [j, j+1] the horizontal
sides vanish (‖H‖ ≪_k 1/R², ‖Λ'/Λ‖ ≪ log²j on them, reflecting Λ'/Λ(1−s) = −Λ'/Λ(s) for
re s < 1/2), the vertical sides converge to the full-line integral (dominated convergence; the
left side is folded onto the right by the functional equation and t ↦ −t), and the zero sums
over |γ| < R_j converge to the absolutely convergent tsum (EF_zero_sum_summable).  The
resulting statement is consumed by Zeta23/WeilEF/Main.lean.
-/
import Zeta23.WeilEF.Contour

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction

/-! ## Majorant pack -/

section Majorants

/-- `H(σ+it)` as a paper Fourier transform at `t + i(1/2 − σ)`. -/
theorem Hfn_apply (k : ℝ → ℂ) (σ t : ℝ) :
    Hfn k ((σ : ℂ) + t * I) = paperFT k ((t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I) := by
  unfold Hfn
  congr 1
  apply Complex.ext <;> simp

/-- **Uniform decay of H on the strip −1 ≤ re ≤ 2**: `‖H(σ+it)‖ ≤ C_k/(1+t²)`. -/
theorem norm_Hfn_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖Hfn k ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨Λ₁, hΛ₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  set B : ℝ := max Λ₁ 0 with hB
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ B := fun u hu => (hΛ₁ u hu).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set A : ℝ := Real.exp (3 / 2 * B) * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) with hA
  have hI1 : 0 ≤ ∫ u, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  have hI2 : 0 ≤ ∫ u, ‖deriv (deriv k) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * A, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  rw [Hfn_apply]
  set z : ℂ := (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I with hz
  have hzim : z.im = 1 / 2 - σ := by simp [hz]
  have hzre : z.re = t := by simp [hz]
  have him : |z.im| ≤ 3 / 2 := by rw [hzim, abs_le]; constructor <;> linarith
  have hexp : Real.exp (|z.im| * B) ≤ Real.exp (3 / 2 * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hB0)
  have hzn : |t| ≤ ‖z‖ := by rw [← hzre]; exact Complex.abs_re_le_norm z
  have ht2 : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : |t| ≤ 1
  · -- small t: the L¹ bound
    have h1 := Zeta23.norm_paperFT_le hki hsupp z
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * B) * ∫ u, ‖k u‖ := h1
      _ ≤ Real.exp (3 / 2 * B) * ∫ u, ‖k u‖ := by gcongr
      _ ≤ A := by rw [hA]; nlinarith [Real.exp_pos (3 / 2 * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [le_div_iff₀ ht2]
          have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
          nlinarith
  · -- large t: the second-derivative bound
    push Not at ht
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hzn; simp at hzn; rw [hzn] at ht; simp at ht; linarith
    have h2 := Zeta23.norm_paperFT_le_div hk hsupp hz0
    have hzsq : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzn 2
    have ht1 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * B) * (∫ u, ‖deriv (deriv k) u‖) / ‖z‖ ^ 2 := h2
      _ ≤ Real.exp (3 / 2 * B) * (∫ u, ‖deriv (deriv k) u‖) / t ^ 2 := by
          gcongr
      _ ≤ A / t ^ 2 := by
          gcongr; rw [hA]; nlinarith [Real.exp_pos (3 / 2 * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) ht2]; nlinarith

/-- `H` is continuous along vertical lines (indeed paperFT k is entire). -/
theorem continuous_Hfn_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (σ : ℝ) :
    Continuous (fun t : ℝ => Hfn k ((σ : ℂ) + t * I)) := by
  have h := (differentiable_paperFT hk.continuous hkc).continuous
  unfold Hfn
  exact h.comp (by fun_prop)

/-- **ζ'/ζ is bounded on vertical lines to the right of 1**:
`‖ζ'/ζ(c+it)‖ ≤ Σ Λ(n) n^{−c}`. -/
theorem norm_logDeriv_zeta_le_of_one_lt_re {c : ℝ} (hc1 : 1 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖ ≤ M := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    exact summable_norm_iff.mpr h
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre1 : 1 < ((c : ℂ) + t * I).re := by rw [hre]; exact hc1
  have h1 : logDeriv riemannZeta ((c : ℂ) + t * I)
      = -LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre1
    rw [logDeriv, Pi.div_apply, h2]; ring
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖
      = ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖) := by
    simp_rw [hnorm]; exact hsum
  rw [h1, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsum'
    _ = ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ := by simp_rw [hnorm]

/-- `t ↦ ζ'/ζ(c+it)` is continuous for `c > 1`. -/
theorem continuous_logDeriv_zeta_line {c : ℝ} (hc1 : 1 < c) :
    Continuous (fun t : ℝ => logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hs1 : ((c : ℂ) + t * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hre1 : 1 < ((c : ℂ) + t * I).re := by simp; linarith
  have hζ : riemannZeta ((c : ℂ) + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre1
  have han := analyticAt_riemannZeta hs1
  have hd : ContinuousAt (deriv riemannZeta) ((c : ℂ) + t * I) := han.deriv.continuousAt
  have hc : ContinuousAt riemannZeta ((c : ℂ) + t * I) := han.continuousAt
  have : ContinuousAt (fun s => deriv riemannZeta s / riemannZeta s) ((c : ℂ) + t * I) :=
    hd.div hc hζ
  show ContinuousAt ((fun s => deriv riemannZeta s / riemannZeta s) ∘ (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt

/-- generic: a continuous `φ` with `‖φ(t)‖ ≤ C/(1+t²)` times `ζ'/ζ(c+it)` is integrable. -/
theorem integrable_mul_logDeriv_zeta_of_decay {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun t : ℝ => φ t * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zeta_le_of_one_lt_re hc1
  have hC0 : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hφ 0); simpa using this
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * M)))
    (hφc.mul (continuous_logDeriv_zeta_line hc1)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * M := mul_le_mul (hφ t) (hM t) (norm_nonneg _) (by positivity)
    _ = C * M * (1 + t ^ 2)⁻¹ := by ring

/-- **Integrability of `H(c+it)·ζ'/ζ(c+it)`** on `re = c ∈ (1, 3/2]`. -/
theorem integrable_Hfn_mul_logDeriv_zeta {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  exact integrable_mul_logDeriv_zeta_of_decay (continuous_Hfn_line hk hkc c)
    (fun t => hC c t (by linarith) (by linarith)) hc1

/-- elementary: `log(2+x) ≤ 5 (1+x²)^{1/4}` for `x ≥ 0`. -/
theorem log_two_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (2 + x) ≤ 5 * (1 + x ^ 2) ^ (1 / 4 : ℝ) := by
  have h2x : 0 < 2 + x := by linarith
  -- log(2+x) ≤ 2 √(2+x)
  have h1 : Real.log (2 + x) ≤ 2 * Real.sqrt (2 + x) := by
    have hs : 0 < Real.sqrt (2 + x) := Real.sqrt_pos.mpr h2x
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt h2x.le] at this
    linarith
  -- √(2+x) ≤ √2 + √x ≤ 3/2 + √x
  have h2 : Real.sqrt (2 + x) ≤ 3 / 2 + Real.sqrt x := by
    have hsx := Real.sq_sqrt hx
    have hs0 := Real.sqrt_nonneg x
    calc Real.sqrt (2 + x) ≤ Real.sqrt ((3 / 2 + Real.sqrt x) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 / 2 + Real.sqrt x := Real.sqrt_sq (by positivity)
  -- √x ≤ (1+x²)^{1/4}, 1 ≤ (1+x²)^{1/4}
  have hq0 : 0 ≤ (1 + x ^ 2 : ℝ) := by positivity
  have h3 : Real.sqrt x ≤ (1 + x ^ 2) ^ (1 / 4 : ℝ) := by
    have e : Real.sqrt x = (x ^ 2) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hx]; norm_num
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h4 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  linarith

/-- `t ↦ Γℝ'/Γℝ(σ+it)` is continuous for `0 < σ ≤ 3/2`. -/
theorem continuous_logDeriv_Gammaℝ_line {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 3 / 2) :
    Continuous (fun t : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  have hfun : (fun t : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I))
      = fun t : ℝ => -((Real.log Real.pi : ℝ) : ℂ) / 2
        + (1 / 2) * Complex.digamma (((σ : ℂ) + t * I) / 2) := by
    funext t
    exact logDeriv_Gammaℝ (by simp; exact hσ0)
  rw [hfun]
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hz : ((σ : ℂ) + t * I) / 2 ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have him := congrArg Complex.im hn
    simp at hre him
    -- σ/2 ∈ (0, 3/4] is not an integer
    have h1 : (0 : ℝ) < n := by rw [hre]; linarith
    have h2 : (n : ℝ) < 1 := by rw [hre]; linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  show ContinuousAt (Complex.digamma ∘ fun t : ℝ => ((σ : ℂ) + t * I) / 2) t
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun t : ℝ => ((σ : ℂ) + t * I) / 2)
    (Zeta23.Stirling.differentiableAt_digamma hz).continuousAt
    (by fun_prop : Continuous fun t : ℝ => ((σ : ℂ) + t * I) / 2).continuousAt

/-- generic: a continuous `φ` with `‖φ(t)‖ ≤ C/(1+t²)` times `Γℝ'/Γℝ(σ+it)`, `1/2 ≤ σ ≤ 3/2`,
is integrable (digamma growth ≪ log(2+|t|) on the strip). -/
theorem integrable_mul_logDeriv_Gammaℝ_of_decay {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => φ t * logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := digamma_growth_strip
  set a : ℝ := Real.log Real.pi / 2 with ha
  set b : ℝ := Cψ / 2 with hb
  have ha0 : 0 ≤ a := by rw [ha]; have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi); linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  set K : ℝ := C * (a + 5 * b) with hK
  -- majorant K (1 + ‖t‖²)^{−3/4}
  have hmaj : Integrable (fun t : ℝ => K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K
  refine Integrable.mono' hmaj
    (hφc.mul (continuous_logDeriv_Gammaℝ_line (by linarith) hσ2)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hσ0 : 0 < σ := by linarith
  have hq : 0 < (1 + t ^ 2 : ℝ) := by positivity
  -- ‖Γℝ'/Γℝ(σ+it)‖ ≤ a + b log(2+|t|) ≤ (a + 5b)(1+t²)^{1/4}
  have hL : ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)‖ ≤ (a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    rw [logDeriv_Gammaℝ (by simp; exact hσ0)]
    have hw1 : 1 / 4 ≤ (((σ : ℂ) + t * I) / 2).re := by simp; linarith
    have hw2 : (((σ : ℂ) + t * I) / 2).re ≤ 1 := by simp; linarith
    have hψb := hψ _ hw1 hw2
    have him : |(((σ : ℂ) + t * I) / 2).im| = |t| / 2 := by simp [abs_div]
    rw [him] at hψb
    have hlog : Real.log (2 + |t| / 2) ≤ 5 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
      have hlt : Real.log (2 + |t| / 2) ≤ Real.log (2 + |t|) :=
        Real.log_le_log (x := 2 + |t| / 2) (y := 2 + |t|) (by positivity) (by linarith [abs_nonneg t])
      refine le_trans hlt ?_
      have := log_two_add_le (abs_nonneg t)
      rwa [sq_abs] at this
    have hone : (1 : ℝ) ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
    calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖
        ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (((σ : ℂ) + t * I) / 2)‖ :=
          norm_add_le _ _
      _ ≤ a + b * Real.log (2 + |t| / 2) := by
          apply add_le_add
          · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
              show ‖(2:ℂ)‖ = 2 by norm_num, ha]
          · rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num, hb]
            nlinarith
      _ ≤ a * (1 + t ^ 2) ^ (1 / 4 : ℝ) + b * (5 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) := by
          apply add_le_add
          · nlinarith
          · exact mul_le_mul_of_nonneg_left hlog hb0
      _ = (a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by ring
  rw [norm_mul]
  have hH := hC t
  have hpow : (C / (1 + t ^ 2)) * ((a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ))
      = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.norm_eq_abs, sq_abs, hK]
    have e : (1 + t ^ 2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
      rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq, Real.rpow_one]
    rw [e]
    field_simp
  calc ‖φ t‖ * ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * ((a + 5 * b) * (1 + t ^ 2) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hH hL (norm_nonneg _) (by positivity)
    _ = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := hpow

/-- **Integrability of `H(σ+it)·Γℝ'/Γℝ(σ+it)`** for `1/2 ≤ σ ≤ 3/2`. -/
theorem integrable_Hfn_mul_logDeriv_Gammaℝ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => Hfn k ((σ : ℂ) + t * I) * logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  exact integrable_mul_logDeriv_Gammaℝ_of_decay (continuous_Hfn_line hk hkc σ) hC0
    (fun t => hC σ t (by linarith) (by linarith)) hσ1 hσ2

end Majorants

/-! ## Good heights (indexed so that no side conditions remain: R_j ∈ [j+7, j+8]) -/

section Heights

/-- nonvanishing of Λ on the horizontal sides `im = ±R`, `1−c ≤ re ≤ c`, given ζ ≠ 0 on
`im = ±R`, `1/2 ≤ re ≤ 2` (the left half by the functional equation Λ(1−s) = Λ(s)). -/
theorem completedZeta_ne_zero_on_horizontals {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℝ}
    (hζ : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 → riemannZeta s ≠ 0) :
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → completedRiemannZeta s ≠ 0 := by
  -- the right half first
  have aux : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      completedRiemannZeta s ≠ 0 := by
    intro s him h1 h2 h0
    rcases lt_or_ge s.re 1 with hlt | hge
    · have hnt := ((completedZeta_zeros_strip (by linarith) hlt).1).mp h0
      exact hζ s him h1 h2 hnt.1
    · exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_one_le_re hge h0
  intro s him h1 h2
  rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
  · exact aux s him hre (by linarith)
  · -- reflect: Λ s = Λ (1 − s)
    have e : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
      (completedRiemannZeta_one_sub s).symm
    rw [e]
    apply aux (1 - s)
    · rcases him with h | h
      · right; simp [h]
      · left; simp [h]
    · simp; linarith
    · simp; linarith

end Heights

/-! ## The vertical sides -/

section Verticals

variable {k : ℝ → ℂ}

/-- the full-line integrand `F(t) := [H(c+it) + H(1−c−it)]·Λ'/Λ(c+it)`. -/
def Fline (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * logDeriv completedRiemannZeta ((c : ℂ) + t * I)

theorem one_sub_cast (c t : ℝ) : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
  push_cast; ring

/-- continuity of the reflected weight `t ↦ H(1 − c − it)` (= `H((1−c) + i(−t))`). -/
theorem continuous_Hfn_reflect {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (c : ℝ) :
    Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := by
  have : (fun t : ℝ => Hfn k (1 - c - t * I))
      = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
    funext t; simp only [Function.comp_apply, one_sub_cast]
  rw [this]; exact (continuous_Hfn_line hk hkc (1 - c)).comp continuous_neg

/-- on `re = c > 1`: `Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ`. -/
theorem logDeriv_completedZeta_line {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    logDeriv completedRiemannZeta ((c : ℂ) + t * I)
      = logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + logDeriv riemannZeta ((c : ℂ) + t * I) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  refine logDeriv_completedZeta _ ?_ ?_ (by rw [hre]; linarith)
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · exact riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hc1)

/-- **Integrability of the full-line integrand.** -/
theorem integrable_Fline (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) : Integrable (Fline k c) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  set φ : ℝ → ℂ := fun t => Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I) with hφ
  have hφc : Continuous φ := (continuous_Hfn_line hk hkc c).add (continuous_Hfn_reflect hk hkc c)
  have hφb : ∀ t, ‖φ t‖ ≤ (2 * C) / (1 + t ^ 2) := by
    intro t
    have h1 := hC c t (by linarith) (by linarith)
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast] at h2
    rw [neg_sq] at h2
    calc ‖φ t‖ ≤ ‖Hfn k ((c : ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
      _ = (2 * C) / (1 + t ^ 2) := by ring
  have hΓ := integrable_mul_logDeriv_Gammaℝ_of_decay hφc (by positivity) hφb
    (by linarith : (1:ℝ) / 2 ≤ c) hc2
  have hζ := integrable_mul_logDeriv_zeta_of_decay hφc hφb hc1
  refine (hΓ.add hζ).congr (Eventually.of_forall fun t => ?_)
  simp only [Fline, hφ, logDeriv_completedZeta_line hc1 t, Pi.add_apply]
  ring

/-- Folding the left vertical side onto the right one: for every `R`,
`V_f(c; −R, R) − V_f(1−c; −R, R) = I • ∫_{−R}^{R} F`,  `f := H·Λ'/Λ`. -/
theorem verticals_eq (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, Fline k c t := by
  
  set L := logDeriv completedRiemannZeta with hL
  have hLc : Continuous (fun t : ℝ => L ((c : ℂ) + t * I)) := by
    have : (fun t : ℝ => L ((c:ℂ) + t * I)) = fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)
        + logDeriv riemannZeta ((c : ℂ) + t * I) := funext (logDeriv_completedZeta_line hc1)
    rw [this]
    exact (continuous_logDeriv_Gammaℝ_line (by linarith) hc2).add (continuous_logDeriv_zeta_line hc1)
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := continuous_Hfn_reflect hk hkc c
  -- the left-line integrand, pointwise
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * L ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    have h0 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (c : ℂ) + ((-y:ℝ):ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hs, hL, logDeriv_completedZeta_one_sub _ h0 h1]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hLc).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Fline]
  ring

/-- the truncated integrals converge to the full-line integral along any `R_j → ∞`. -/
theorem tendsto_interval_Fline (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, Fline k c t) atTop (𝓝 (∫ t, Fline k c t)) := by
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (integrable_Fline hk hkc hc1 hc2)
    (tendsto_neg_atTop_atBot.comp hRtop) hRtop

end Verticals

end WeilEF
end Zeta23
