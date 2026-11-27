/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.Kernel
import Zeta23.ThmD.Sextuple.Interior
import Zeta23.ThmD.Sextuple.Base
import Zeta23.ThmD.ParamsD
import Zeta23.PrimeSideA.EndsE1
import Zeta23.ZeroSide.SextuplePenalty

/-!
# Transfer from the finite Montgomery--Taylor Gram to the ideal kernel

This file keeps the finite-grid and taper errors explicit.  Its pointwise
bounds apply to real ordinates in the unit-trimmed interval `[T+1,2T-1]`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped BigOperators

namespace Zeta23
namespace ThmD
namespace Sextuple

open PrimeSide

variable {c : ℝ} {p : Setting} {F : LocalFun}

/-- Fourier transform of the unit symmetric interval, in the paper's
normalization. -/
lemma integral_exp_mul_I_half (x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))) =
        (Real.sinc (x / 2) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    norm_num
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
    (a := (-(1 : ℝ) / 2)) (b := (1 / 2)) x
  have hfun : (fun s : ℝ => Complex.exp ((x * s : ℝ) * Complex.I)) =
      (fun s : ℝ => Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))) := by
    funext s
    congr 1
    push_cast
    ring_nf
  rw [hfun] at hscale
  have hb₁ : x * (-(1 : ℝ) / 2) = -(x / 2) := by ring_nf
  have hb₂ : x * (1 / 2 : ℝ) = x / 2 := by ring_nf
  rw [hb₁, hb₂, integral_exp_mul_I_eq_sinc] at hscale
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  refine mul_left_cancel₀ hxC ?_
  calc
    (x : ℂ) * (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
        Complex.exp (Complex.I * (x : ℂ) * (s : ℂ)))
        = 2 * (x / 2 : ℝ) * (Real.sinc (x / 2) : ℂ) := by
          simpa [smul_eq_mul] using hscale
    _ = (x : ℂ) * (Real.sinc (x / 2) : ℂ) := by
          push_cast
          ring_nf

set_option linter.unusedSimpArgs false in
/-- Product-to-sum identity in complex exponential form. -/
lemma cos_mul_cexp (a x s : ℝ) :
    (Real.cos (a * s) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (s : ℂ)) =
      (Complex.exp (Complex.I * ((x + a : ℝ) : ℂ) * (s : ℂ)) +
        Complex.exp (Complex.I * ((x - a : ℝ) : ℂ) * (s : ℂ))) / 2 := by
  apply Complex.ext
  · simp [← Complex.ofReal_mul, Complex.exp_re, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
    have hp : (x + a) * s = a * s + x * s := by ring_nf
    have hm : (x - a) * s = -(a * s) + x * s := by ring_nf
    rw [hp, hm, Real.cos_add, Real.cos_add]
    simp [Real.cos_neg, Real.sin_neg]
  · simp [← Complex.ofReal_mul, Complex.exp_re, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
    have hp : (x + a) * s = a * s + x * s := by ring_nf
    have hm : (x - a) * s = -(a * s) + x * s := by ring_nf
    rw [hp, hm, Real.sin_add, Real.sin_add]
    simp [Real.cos_neg, Real.sin_neg]
    ring_nf

/-- The sharp Montgomery--Taylor profile on the unit interval has the sinc
transform used to define `mtKernel`. -/
lemma integral_cos_sqrtTwo_mul_cexp_half (x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      (Real.cos (Real.sqrt 2 * s) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))) =
      ((Real.sinc ((x + Real.sqrt 2) / 2) +
        Real.sinc ((x - Real.sqrt 2) / 2)) / 2 : ℝ) := by
  rw [intervalIntegral.integral_congr (fun s _ => cos_mul_cexp (Real.sqrt 2) x s)]
  rw [intervalIntegral.integral_div]
  have hi₁ : IntervalIntegrable
      (fun s : ℝ => Complex.exp (Complex.I * ((x + Real.sqrt 2 : ℝ) : ℂ) * (s : ℂ)))
      volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous
      (fun s : ℝ => Complex.exp (Complex.I * ((x + Real.sqrt 2 : ℝ) : ℂ) * (s : ℂ)))).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable
      (fun s : ℝ => Complex.exp (Complex.I * ((x - Real.sqrt 2 : ℝ) : ℂ) * (s : ℂ)))
      volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous
      (fun s : ℝ => Complex.exp (Complex.I * ((x - Real.sqrt 2 : ℝ) : ℂ) * (s : ℂ)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi₁ hi₂]
  rw [integral_exp_mul_I_half, integral_exp_mul_I_half]
  push_cast
  ring_nf

/-- The normalizing sharp mass is strictly positive. -/
lemma sinc_sqrtTwo_half_pos : 0 < Real.sinc (Real.sqrt 2 / 2) := by
  have hθpos : 0 < Real.sqrt 2 / 2 := by positivity
  have hθlt : Real.sqrt 2 / 2 < Real.pi := by
    have hsqrt : Real.sqrt 2 < 2 :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    nlinarith [Real.pi_gt_three]
  rw [Real.sinc_of_ne_zero hθpos.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt) hθpos

@[simp] lemma aStar_one_eq_sinc_sqrtTwo_half :
    aStar 1 = Real.sinc (Real.sqrt 2 / 2) := by
  rw [aStar_eq zero_lt_one]
  simp only [theta, div_one]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have harg : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  rw [harg, Real.sinc_of_ne_zero (by positivity : Real.sqrt 2 / 2 ≠ 0)]
  field_simp
  rw [hsqrt]

/-- Exact unit-scale sharp Fourier identity in the paper convention
`∫ f(s) exp(i x s) ds`. -/
theorem sharpFourier_unit_eq_mtKernel (x : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      (Real.cos (Real.sqrt 2 * s) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))) =
      (Real.sinc (Real.sqrt 2 / 2) * mtKernel x : ℝ) := by
  rw [integral_cos_sqrtTwo_mul_cexp_half, mtKernel]
  field_simp [sinc_sqrtTwo_half_pos.ne']
  ring_nf

/-- Exact Fourier transform of the physical sharp window.  This records
both the paper sign convention and the rescaling `u = L s`. -/
theorem paperFT_sharpW_one_eq_mtKernel {L : ℝ} (hL : 0 < L) (r : ℝ) :
    paperFT (fun u => (sharpW 1 L u : ℂ)) (r : ℂ) =
      (L * Real.sinc (Real.sqrt 2 / 2) * mtKernel (L * r) : ℝ) := by
  have hind : (fun u : ℝ => (sharpW 1 L u : ℂ) *
      Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) =
      (Set.Icc (-(L / 2)) (L / 2)).indicator
        (fun u : ℝ => (vStar 1 (u / L) : ℂ) *
          Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    funext u
    unfold sharpW
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu,
        Complex.ofReal_zero, zero_mul]
  rw [paperFT, hind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  let f : ℝ → ℂ := fun u => (vStar 1 (u / L) : ℂ) *
    Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))
  have hfun : (fun s : ℝ => f (L * s)) = fun s : ℝ =>
      (Real.cos (Real.sqrt 2 * s) : ℂ) *
        Complex.exp (Complex.I * ((L * r : ℝ) : ℂ) * (s : ℂ)) := by
    funext s
    dsimp [f]
    simp only [vStar]
    rw [mul_div_cancel_left₀ s hL.ne']
    congr 2
    · ring_nf
    · rw [Complex.ofReal_mul, Complex.ofReal_mul]
      ring_nf
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := f) (a := (-(1 : ℝ) / 2)) (b := (1 / 2)) L
  rw [hfun] at hscale
  rw [show L * (-(1 : ℝ) / 2) = -(L / 2) by ring_nf,
    show L * (1 / 2 : ℝ) = L / 2 by ring_nf] at hscale
  rw [← hscale, sharpFourier_unit_eq_mtKernel, Complex.real_smul]
  push_cast
  ring_nf

/-- The taper changes the (complex) sharp Fourier transform by at most
its exact `L¹` discrepancy. -/
theorem norm_paperFT_phiD_sq_sub_sharp_le (P : Params) (hP : P.Valid)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    ‖paperFT (fun u => ((P.phiD T u ^ 2 : ℝ) : ℂ)) (r : ℂ) -
        paperFT (fun u => (sharpW P.lam (P.L T) u : ℂ)) (r : ℂ)‖ ≤
      2 * P.w := by
  have hW := admWindow_params hP h8
  let e : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))
  have hec : Continuous e := by
    dsimp [e]
    fun_prop
  have henorm : ∀ u, ‖e u‖ ≤ 1 := by
    intro u
    dsimp [e]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hh : Integrable (fun u => ((P.phiD T u ^ 2 : ℝ) : ℂ)) :=
    hW.vSqC_continuous.integrable_of_hasCompactSupport hW.vSqC_hasCompactSupport
  have hkR : Integrable (sharpW P.lam (P.L T)) := by
    unfold sharpW
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (((by unfold vStar; fun_prop : Continuous fun u : ℝ =>
          vStar P.lam (u / P.L T)).continuousOn).integrableOn_compact
        isCompact_Icc)
  have hk : Integrable (fun u => (sharpW P.lam (P.L T) u : ℂ)) := hkR.ofReal
  have hhe : Integrable (fun u => ((P.phiD T u ^ 2 : ℝ) : ℂ) * e u) :=
    hh.mul_bdd (c := 1) hec.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ henorm)
  have hke : Integrable (fun u => (sharpW P.lam (P.L T) u : ℂ) * e u) :=
    hk.mul_bdd (c := 1) hec.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ henorm)
  rw [paperFT, paperFT, ← MeasureTheory.integral_sub hhe hke]
  calc
    ‖∫ u, ((P.phiD T u ^ 2 : ℝ) : ℂ) * e u -
        (sharpW P.lam (P.L T) u : ℂ) * e u‖
        ≤ ∫ u, ‖((P.phiD T u ^ 2 : ℝ) : ℂ) * e u -
          (sharpW P.lam (P.L T) u : ℂ) * e u‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ u, |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u| := by
      apply MeasureTheory.integral_congr_ae
      apply MeasureTheory.ae_of_all
      intro u
      change ‖((P.phiD T u ^ 2 : ℝ) : ℂ) * e u -
          (sharpW P.lam (P.L T) u : ℂ) * e u‖ =
        |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have heq : ‖e u‖ = 1 := by
        dsimp [e]
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
      rw [heq, mul_one]
    _ ≤ 2 * P.w :=
      integral_abs_phiDsq_sub_sharp (ϱ := P.ϱ) (lam := P.lam)
        (L := P.L T) (w := P.w) hP.taper hP.lam_pos hP.lam_le_one
        (by linarith [hP.one_le_w]) (by linarith [hP.one_le_w])

/-- Real-valued sharp/taper Fourier comparison at `lambda = 1`, before
normalization. -/
theorem abs_localFunD_Phi_sub_sharp_le (P : Params) (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.localFunD T).Phi r -
        P.L T * aStar 1 * mtKernel (P.L T * r)| ≤ 2 * P.w := by
  have hW := admWindow_params hP h8
  have h := norm_paperFT_phiD_sq_sub_sharp_le P hP h8 r
  change ‖AdmWindow.VPhi (P.phiD T) (r : ℂ) -
      paperFT (fun u => (sharpW P.lam (P.L T) u : ℂ)) (r : ℂ)‖ ≤
    2 * P.w at h
  rw [hW.VPhi_ofReal, hlam,
    paperFT_sharpW_one_eq_mtKernel (hL := hW.L_pos)] at h
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [Params.localFunD, AdmWindow.localFun] using h

/-- The normalized sharp Montgomery--Taylor kernel is a correlation
coefficient, hence has absolute value at most one. -/
theorem abs_mtKernel_le_one (x : ℝ) : |mtKernel x| ≤ 1 := by
  have hsharpC :
      (Real.sinc (Real.sqrt 2 / 2) : ℂ) * (mtKernel x : ℂ) =
        ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          (Real.cos (Real.sqrt 2 * s) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (s : ℂ)) := by
    simpa using (sharpFourier_unit_eq_mtKernel x).symm
  have hnorm : ‖(Real.sinc (Real.sqrt 2 / 2) : ℂ) * (mtKernel x : ℂ)‖ ≤
      aStar 1 := by
    rw [hsharpC]
    calc
      ‖∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          (Real.cos (Real.sqrt 2 * s) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))‖
          ≤ ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
              ‖(Real.cos (Real.sqrt 2 * s) : ℂ) *
                Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = aStar 1 := by
        rw [aStar]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le (by norm_num)] at hs
        have hv : 0 ≤ vStar 1 s :=
          vStar_nonneg_on (lam := 1) zero_le_one le_rfl hs
        change ‖(Real.cos (Real.sqrt 2 * s) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (s : ℂ))‖ = vStar 1 s
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by simpa [vStar] using hv), Complex.norm_exp]
        simp [vStar, Complex.mul_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos sinc_sqrtTwo_half_pos,
    aStar_one_eq_sinc_sqrtTwo_half] at hnorm
  nlinarith [sinc_sqrtTwo_half_pos]

/-- Pointwise comparison of the normalized tapered Fourier transform
with the normalized sharp Montgomery--Taylor transform. -/
theorem normalized_localFunD_Phi_sub_mtKernel_le (P : Params) (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ}
    (hF : LocalHypsCore (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T))
    (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.localFunD T).Phi r /
          ((P.localFunD T).a * P.L T) - mtKernel (P.L T * r)| ≤
      12 * P.w / P.L T := by
  have hL : 0 < P.L T := hF.L_pos
  have hw : 0 ≤ P.w := zero_le_one.trans hP.one_le_w
  have haHalf : 1 / 2 ≤ (P.localFunD T).a :=
    hF.b_ge_half.trans hF.b_le_a
  have ha : 0 < (P.localFunD T).a := by linarith
  have hFourier := abs_localFunD_Phi_sub_sharp_le P hP hlam h8 r
  have haCloseRaw := aD_close (ϱ := P.ϱ) (lam := P.lam)
    (L := P.L T) (w := P.w) hP.taper hP.lam_pos hP.lam_le_one
    hP.one_le_w h8
  rw [hlam] at haCloseRaw
  have haClose : |(P.localFunD T).a - aStar 1| ≤
      4 * P.w / P.L T := by
    simpa [Params.localFunD, AdmWindow.localFun, AdmWindow.av,
      Params.phiD, hlam] using haCloseRaw
  have hsecond :
      |P.L T * (aStar 1 - (P.localFunD T).a) *
          mtKernel (P.L T * r)| ≤ 4 * P.w := by
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_sub_comm]
    calc
      P.L T * |(P.localFunD T).a - aStar 1| *
          |mtKernel (P.L T * r)|
          ≤ P.L T * (4 * P.w / P.L T) * 1 := by
        gcongr
        exact abs_mtKernel_le_one _
      _ = 4 * P.w := by field_simp
  have hraw : |(P.localFunD T).Phi r -
      (P.localFunD T).a * P.L T * mtKernel (P.L T * r)| ≤
      6 * P.w := by
    calc
      |(P.localFunD T).Phi r -
          (P.localFunD T).a * P.L T * mtKernel (P.L T * r)| =
          |((P.localFunD T).Phi r -
              P.L T * aStar 1 * mtKernel (P.L T * r)) +
            P.L T * (aStar 1 - (P.localFunD T).a) *
              mtKernel (P.L T * r)| := by
            congr 1
            ring_nf
      _ ≤ |(P.localFunD T).Phi r -
              P.L T * aStar 1 * mtKernel (P.L T * r)| +
            |P.L T * (aStar 1 - (P.localFunD T).a) *
              mtKernel (P.L T * r)| := abs_add_le _ _
      _ ≤ 2 * P.w + 4 * P.w := add_le_add hFourier hsecond
      _ = 6 * P.w := by ring_nf
  have hrewrite :
      (P.localFunD T).Phi r / ((P.localFunD T).a * P.L T) -
          mtKernel (P.L T * r) =
        ((P.localFunD T).Phi r -
          (P.localFunD T).a * P.L T * mtKernel (P.L T * r)) /
            ((P.localFunD T).a * P.L T) := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos (mul_pos ha hL)]
  calc
    |(P.localFunD T).Phi r -
        (P.localFunD T).a * P.L T * mtKernel (P.L T * r)| /
          ((P.localFunD T).a * P.L T)
        ≤ (6 * P.w) / ((P.localFunD T).a * P.L T) := by
          gcongr
    _ ≤ 12 * P.w / P.L T := by
      rw [div_le_iff₀ (mul_pos ha hL)]
      field_simp
      nlinarith

/-- A coarse pointwise bound for the one-sided grid majorant at distance at
least one.  The deliberately loose constant makes the downstream normalized
error transparent. -/
lemma Wfun_le_two_mul_L_mul_sq (hF : LocalHypsCoreW c p F)
    {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    Wfun c p Δ ≤ 2 * p.L * c ^ 2 := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hw : 1 ≤ p.w := hF.one_le_w
  have hL : 8 ≤ p.L := by linarith [hF.w_le]
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  have hpsi0 := psiA_nonneg_of hF Δ
  have hpsi := psiA_le_div_sq (cϱ := c) (p := p) hΔ0.ne'
  have hdiv : c / (p.w * Δ ^ 2) ≤ c := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ p.w * Δ ^ 2 := by nlinarith [sq_nonneg (Δ - 1)]
    nlinarith
  have hpsi_sq : psiA c p Δ ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ hpsi0 (hpsi.trans hdiv) 2
  have hint := setIntegral_psiA_sq_Ioi_le_div hF hΔ0
  have hcw : (c / p.w) ^ 2 ≤ c ^ 2 := by
    have hcdiv : c / p.w ≤ c := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact pow_le_pow_left₀ (by positivity) hcdiv 2
  have hΔcube : 1 ≤ 3 * Δ ^ 3 := by nlinarith [sq_nonneg (Δ - 1), mul_self_nonneg Δ]
  have hint' : ∫ r in Set.Ioi Δ, psiA c p r ^ 2 ≤ c ^ 2 := by
    calc
      _ ≤ (c / p.w) ^ 2 / (3 * Δ ^ 3) := hint
      _ ≤ c ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hcw, sq_nonneg c]
  have hh_inv : p.h⁻¹ ≤ p.L := by
    rw [Setting.h]
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [inv_div]
    exact div_le_self (by linarith) hpi
  have hint0 : 0 ≤ ∫ r in Set.Ioi Δ, psiA c p r ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [Wfun]
  calc
    psiA c p Δ ^ 2 + p.h⁻¹ * ∫ r in Set.Ioi Δ, psiA c p r ^ 2
        ≤ c ^ 2 + p.L * c ^ 2 := by
          gcongr
    _ ≤ 2 * p.L * c ^ 2 := by nlinarith [sq_nonneg c]

/-- On the unit-trimmed interval the omitted-grid diagonal mass is `O(L)` with
an explicit constant. -/
theorem rho_le_six_mul_L_mul_sq (hF : LocalHypsCore c p F)
    (hT : 0 < p.T) (hh : p.h ≤ 1 / 2) {τ : ℝ}
    (hτlo : p.T + 1 ≤ τ) (hτhi : τ ≤ 2 * p.T - 1) :
    rho p F τ ≤ 6 * p.L * c ^ 2 := by
  have hFW := hF.toCoreW
  have hτI : τ ∈ Icc p.T (2 * p.T) := by constructor <;> linarith
  have hmaj := rho_le_majorant hFW hT hτI
  have hleft := Wfun_le_two_mul_L_mul_sq hFW (show 1 ≤ τ - p.T by linarith)
  have hright := Wfun_le_two_mul_L_mul_sq hFW (show 1 ≤ 2 * p.T - τ by linarith)
  have htd := tau_d_gt hF.L_pos hT
  have hδ : 1 / 2 < p.tau p.d - τ := by linarith
  have hpsi0 := psiA_nonneg_of hFW (p.tau p.d - τ)
  have hpsi := psiA_le_div_sq (cϱ := c) (p := p) (lt_trans (by norm_num) hδ).ne'
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  have hw : 1 ≤ p.w := hF.one_le_w
  have hpsi4 : psiA c p (p.tau p.d - τ) ≤ 4 * c := by
    calc
      psiA c p (p.tau p.d - τ)
          ≤ c / (p.w * (p.tau p.d - τ) ^ 2) := hpsi
      _ ≤ 4 * c := by
        rw [div_le_iff₀ (by positivity)]
        have hs : 1 / 4 < (p.tau p.d - τ) ^ 2 := by nlinarith
        have hprod : 1 ≤ 4 * (p.w * (p.tau p.d - τ) ^ 2) := by
          have := mul_le_mul hw hs.le (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith)
          nlinarith
        calc
          c ≤ c * (4 * (p.w * (p.tau p.d - τ) ^ 2)) :=
            le_mul_of_one_le_right hc hprod
          _ = 4 * c * (p.w * (p.tau p.d - τ) ^ 2) := by ring_nf
  have hstray : psiA c p (p.tau p.d - τ) ^ 2 ≤ 2 * p.L * c ^ 2 := by
    have hsq := pow_le_pow_left₀ hpsi0 hpsi4 2
    have hL : 8 ≤ p.L := by linarith [hF.w_le]
    nlinarith [sq_nonneg c]
  linarith

/-- Explicit normalized finite-grid tail bound. -/
theorem normalized_Kfun_sub_Kinf_le (hF : LocalHypsCore c p F)
    (hT : 0 < p.T) (hh : p.h ≤ 1 / 2) {τ τ' : ℝ}
    (hτlo : p.T + 1 ≤ τ) (hτhi : τ ≤ 2 * p.T - 1)
    (hτ'lo : p.T + 1 ≤ τ') (hτ'hi : τ' ≤ 2 * p.T - 1) :
    |Kfun p F τ τ' / (F.a * p.L ^ 2) -
        Kinf p F τ τ' / (F.a * p.L ^ 2)| ≤ 12 * c ^ 2 / p.L := by
  have ha : 1 / 2 ≤ F.a := hF.b_ge_half.trans hF.b_le_a
  have hL : 0 < p.L := hF.L_pos
  have hden : 0 < F.a * p.L ^ 2 := mul_pos (by linarith) (sq_pos_of_pos hL)
  have htail := abs_Kinf_sub_Kfun_le hF.toCoreW τ τ' (s := 1) zero_lt_one
  have hρ := rho_le_six_mul_L_mul_sq hF hT hh hτlo hτhi
  have hρ' := rho_le_six_mul_L_mul_sq hF hT hh hτ'lo hτ'hi
  have hraw : |Kfun p F τ τ' - Kinf p F τ τ'| ≤ 6 * p.L * c ^ 2 := by
    rw [abs_sub_comm]
    norm_num at htail
    linarith
  rw [div_sub_div_same, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  calc
    |Kfun p F τ τ' - Kinf p F τ τ'|
        ≤ 6 * p.L * c ^ 2 := hraw
    _ ≤ (12 * c ^ 2 / p.L) * (F.a * p.L ^ 2) := by
      field_simp
      nlinarith [sq_nonneg c]


/-! ## Exact concrete Gram entries -/

private lemma gammaOf_globalSimpleIndex_eq (Z : ZeroConfig) (T : ℝ) (P : Params)
    (z : GlobalSimpleIndex Z T P) :
    gammaOf (z.1 : ℂ) = (((z.1 : ℂ).im : ℝ) : ℂ) := by
  have hz' : (ZeroSide.sextupleBlockData Z T P).σ z.1 = z.1 ∧
      (ZeroSide.sextupleBlockData Z T P).m z.1 = 1 := by
    simpa only [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
      Finset.mem_univ, true_and] using z.2
  have hz : (ZeroSide.sextupleBlockData Z T P).σ z.1 = z.1 := hz'.1
  change (ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
    (ZeroSide.evalVec_reflect (fun w => GzGp.phiHat_conj P T w))).σ z.1 = z.1 at hz
  have hre : (z.1 : ℂ).re = 1 / 2 :=
    (ZeroSide.mkData_σ_eq_iff Z T _ _ z.1).mp hz
  apply Complex.ext
  · simp [gammaOf, hre]
  · simp [gammaOf, hre]

private lemma evalVec_globalSimpleIndex_eq (Z : ZeroConfig) (T : ℝ) (P : Params)
    (z : GlobalSimpleIndex Z T P) (k : Fin (P.d T)) :
    ZeroSide.evalVec Z T P z k =
      (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) := by
  rw [ZeroSide.evalVec, gammaOf_globalSimpleIndex_eq]
  rw [← Complex.ofReal_sub, GzGp.phiHat_ofReal]

/-- An entry of the actual normalized simple-zero Gram matrix is exactly the
finite Montgomery--Taylor kernel, with the concrete ordered interior indices. -/
theorem simpleZeroGram_interior_apply_eq_Kfun (Z : ZeroConfig) (T : ℝ)
    (P : Params) (hc : 0 < P.a T * P.L T ^ 2)
    (i j : Fin (sInterior Z T P)) :
    ZeroSide.simpleZeroGram Z T P (interiorGramEmbedding Z T P i)
        (interiorGramEmbedding Z T P j) =
      (Kfun (P.toSetting T) (P.localFun T)
          (orderedOrdinate Z T P i) (orderedOrdinate Z T P j) /
        (P.a T * P.L T ^ 2) : ℂ) := by
  rw [ZeroSide.simpleZeroGram, Matrix.mul_apply]
  simp_rw [Matrix.conjTranspose_apply, ZeroSide.simpleZeroColumns_apply,
    evalVec_globalSimpleIndex_eq]
  simp_rw [interiorGramEmbedding_ordinate]
  change (∑ k : Fin (P.d T),
      star ((P.phiHatR T (orderedOrdinate Z T P i - P.tau T k) : ℂ) /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) *
      ((P.phiHatR T (orderedOrdinate Z T P j - P.tau T k) : ℂ) /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ))) =
    ((∑ k : Fin (P.d T),
      P.phiHatR T (orderedOrdinate Z T P i - P.tau T k) *
        P.phiHatR T (orderedOrdinate Z T P j - P.tau T k)) /
      (P.a T * P.L T ^ 2) : ℂ)
  have hsqrt_sq : Real.sqrt (P.a T * P.L T ^ 2) ^ 2 =
      P.a T * P.L T ^ 2 := Real.sq_sqrt hc.le
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  change starRingEnd ℂ
      ((P.phiHatR T (orderedOrdinate Z T P i - P.tau T k) : ℂ) /
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) * _ = _
  rw [map_div₀]
  simp only [Complex.conj_ofReal]
  rw [div_mul_div_comm, ← sq]
  rw [show ((Real.sqrt (P.a T * P.L T ^ 2) : ℝ) : ℂ) ^ 2 =
      ((P.a T * P.L T ^ 2 : ℝ) : ℂ) by exact_mod_cast hsqrt_sq]
  push_cast
  rfl


/-- Uniform transfer at one height for the concrete Montgomery--Taylor
window-realizing family. -/
theorem simpleZeroGram_atD_interior_sub_mtKernel_le (Z : ZeroConfig)
    (P : Params) (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ}
    (hF : LocalHypsCore (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T))
    (hT : 0 < T) (hh : (P.toSetting T).h ≤ 1 / 2)
    (h8 : 8 * P.w ≤ P.L T)
    (i j : Fin (sInterior Z T (P.atD T))) :
    ‖ZeroSide.simpleZeroGram Z T (P.atD T)
          (interiorGramEmbedding Z T (P.atD T) i)
          (interiorGramEmbedding Z T (P.atD T) j) -
        (mtKernel ((P.atD T).L T *
          (orderedOrdinate Z T (P.atD T) i -
            orderedOrdinate Z T (P.atD T) j)) : ℂ)‖ ≤
      (12 * (cDT P.ϱ P.lam) ^ 2 + 12 * P.w) / P.L T := by
  let τ : ℝ := orderedOrdinate Z T (P.atD T) i
  let τ' : ℝ := orderedOrdinate Z T (P.atD T) j
  have hL : 0 < P.L T := hF.L_pos
  have ha : 0 < (P.localFunD T).a := hF.a_pos
  have hc : 0 < (P.atD T).a T * (P.atD T).L T ^ 2 := by
    rw [Params.atD_a T hP]
    exact mul_pos ha (sq_pos_of_pos hL)
  have hGram := simpleZeroGram_interior_apply_eq_Kfun
    Z T (P.atD T) hc i j
  rw [Params.atD_toSetting, Params.atD_localFun T hP,
    Params.atD_a T hP] at hGram
  have hτlo : T + 1 ≤ τ :=
    (orderedOrdinate_lower Z T (P.atD T) i).le
  have hτhi : τ ≤ 2 * T - 1 := orderedOrdinate_upper Z T (P.atD T) i
  have hτ'lo : T + 1 ≤ τ' :=
    (orderedOrdinate_lower Z T (P.atD T) j).le
  have hτ'hi : τ' ≤ 2 * T - 1 := orderedOrdinate_upper Z T (P.atD T) j
  have hfinite := normalized_Kfun_sub_Kinf_le hF hT hh
    hτlo hτhi hτ'lo hτ'hi
  have hsharp := normalized_localFunD_Phi_sub_mtKernel_le
    P hP hlam hF h8 (τ - τ')
  have hKinf :
      Kinf (P.toSetting T) (P.localFunD T) τ τ' /
          ((P.localFunD T).a * P.L T ^ 2) =
        (P.localFunD T).Phi (τ - τ') /
          ((P.localFunD T).a * P.L T) := by
    unfold Kinf
    simp only [Params.toSetting_L]
    field_simp
  rw [← hKinf] at hsharp
  have hreal :
      |Kfun (P.toSetting T) (P.localFunD T) τ τ' /
          ((P.localFunD T).a * P.L T ^ 2) -
        mtKernel (P.L T * (τ - τ'))| ≤
      (12 * (cDT P.ϱ P.lam) ^ 2 + 12 * P.w) / P.L T := by
    calc
      |Kfun (P.toSetting T) (P.localFunD T) τ τ' /
          ((P.localFunD T).a * P.L T ^ 2) -
        mtKernel (P.L T * (τ - τ'))| ≤
          |Kfun (P.toSetting T) (P.localFunD T) τ τ' /
              ((P.localFunD T).a * P.L T ^ 2) -
            Kinf (P.toSetting T) (P.localFunD T) τ τ' /
              ((P.localFunD T).a * P.L T ^ 2)| +
          |Kinf (P.toSetting T) (P.localFunD T) τ τ' /
              ((P.localFunD T).a * P.L T ^ 2) -
            mtKernel (P.L T * (τ - τ'))| := abs_sub_le _ _ _
      _ ≤ 12 * (cDT P.ϱ P.lam) ^ 2 / P.L T +
          12 * P.w / P.L T := add_le_add hfinite hsharp
      _ = (12 * (cDT P.ϱ P.lam) ^ 2 + 12 * P.w) / P.L T := by ring_nf
  rw [hGram]
  have hcomplex :
      ‖((Kfun (P.toSetting T) (P.localFunD T) τ τ' /
          ((P.localFunD T).a * P.L T ^ 2) -
        mtKernel (P.L T * (τ - τ')) : ℝ) : ℂ)‖ ≤
        (12 * (cDT P.ϱ P.lam) ^ 2 + 12 * P.w) / P.L T := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hreal
  push_cast at hcomplex
  simpa only [Params.atD_L, τ, τ'] using hcomplex


/-! ## Proof-free zeta specialization -/

/-- The explicit entrywise transfer error for the zeta Montgomery--Taylor
family.  It contains only the proved grid-tail and taper constants. -/
def gramTransferError (T : ℝ) : ℝ :=
  (12 * (cDT montgomeryTaylorParams.ϱ montgomeryTaylorParams.lam) ^ 2 +
      12 * montgomeryTaylorParams.w) / montgomeryTaylorParams.L T

lemma montgomeryTaylorParams_valid : montgomeryTaylorParams.Valid := by
  unfold montgomeryTaylorParams
  exact paramsOf_valid taperProfile_stdProfile (by norm_num) (by norm_num)

/-- The explicit transfer error tends to zero. -/
theorem gramTransferError_tendsto_zero :
    Tendsto gramTransferError atTop (𝓝 0) := by
  have hP := montgomeryTaylorParams_valid
  have hL := Assembly.tendsto_L_atTop montgomeryTaylorParams hP.lam_pos
  change Tendsto (fun T =>
    (12 * (cDT montgomeryTaylorParams.ϱ montgomeryTaylorParams.lam) ^ 2 +
      12 * montgomeryTaylorParams.w) / montgomeryTaylorParams.L T) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop hL

/-- The explicit transfer error is eventually nonnegative. -/
theorem gramTransferError_eventually_nonneg :
    ∀ᶠ T in atTop, 0 ≤ gramTransferError T := by
  have hP := montgomeryTaylorParams_valid
  have hL := Assembly.tendsto_L_atTop montgomeryTaylorParams hP.lam_pos
  filter_upwards [hL.eventually_gt_atTop 0] with T hLT
  exact div_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by norm_num) (zero_le_one.trans hP.one_le_w))) hLT.le

/-- Eventual uniform approximation of every ordered interior entry of the
actual zeta simple-zero Gram matrix by the real Montgomery--Taylor kernel. -/
theorem eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le :
    ∀ᶠ T in atTop,
      ∀ i j : Fin (sInterior zetaZeroConfig T
          (montgomeryTaylorParams.atD T)),
        ‖ZeroSide.simpleZeroGram zetaZeroConfig T
              (montgomeryTaylorParams.atD T)
              (interiorGramEmbedding zetaZeroConfig T
                (montgomeryTaylorParams.atD T) i)
              (interiorGramEmbedding zetaZeroConfig T
                (montgomeryTaylorParams.atD T) j) -
            (mtKernel ((montgomeryTaylorParams.atD T).L T *
              (orderedOrdinate zetaZeroConfig T
                  (montgomeryTaylorParams.atD T) i -
                orderedOrdinate zetaZeroConfig T
                  (montgomeryTaylorParams.atD T) j)) : ℂ)‖ ≤
          gramTransferError T := by
  let P : Params := montgomeryTaylorParams
  have hP : P.Valid := by
    simpa [P] using montgomeryTaylorParams_valid
  obtain ⟨T₀, hLoc⟩ := localHypsCoreD_eventually hP
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop (0 : ℝ),
    hLtop.eventually_ge_atTop (4 * Real.pi)] with T hT₀ hT hL4
  have hF : LocalHypsCore (cDT P.ϱ P.lam)
      (P.toSetting T) (P.localFunD T) := hLoc T hT₀
  have hh : (P.toSetting T).h ≤ 1 / 2 := by
    have hLP : 0 < P.L T := by simpa using hF.L_pos
    change 2 * Real.pi / P.L T ≤ 1 / 2
    rw [div_le_iff₀ hLP]
    nlinarith
  have h8 : 8 * P.w ≤ P.L T := by
    have hwL := hF.w_le
    change P.w ≤ P.L T / 8 at hwL
    linarith
  intro i j
  have h := simpleZeroGram_atD_interior_sub_mtKernel_le
    zetaZeroConfig P hP (by rfl) hF hT hh h8 i j
  simpa [P, gramTransferError] using h

end Sextuple
end ThmD
end Zeta23
