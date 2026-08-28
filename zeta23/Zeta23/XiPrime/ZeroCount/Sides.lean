/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/Sides.lean — the Y′/Y pieces of the half-contour are O(log T).

  * horizontal_bound : at a good height T with |T| ≥ t₁,  |Im ∫_{1/2}^{2} Y′/Y(σ+iT) dσ| ≤ C log(|T|+3)
      — Landau's partial fraction (ZeroCount/Landau.lean) on the 3/2-ball about 2+iT covering the segment:
        each term m_ρ/(s−ρ) moves the argument by ≤ π (ArgBound (B)), Σ m_ρ ≪ log, remainder ≪ log.
  * vertical_bound   : for t₁ ≤ T₁ ≤ T₂,  |Im ∫_{T₁}^{T₂} Y′/Y(2+it)·i dt| ≤ 3π
      — on Re s = 2, Y = (s(s−1)/2)·ζ·(L + ζ′/ζ) (Seam.Yfn_eq_factor); each factor has positive real part
        (up to the sign of the first), so each log moves by ≤ π (ArgBound (A); RvM.vertical_two for ζ).
-/
import Zeta23.XiPrime.ZeroCount.Landau
import Zeta23.XiPrime.ZeroCount.ArgBound
import Zeta23.XiPrime.ZeroCount.Contour
import Zeta23.RvM.Backlund

open Complex Set Filter Topology MeasureTheory intervalIntegral Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-! ### horizontal sides -/

/-- **Horizontal sides.** -/
theorem horizontal_bound : ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ ∀ T : ℝ, t₁ ≤ |T| → GoodHeight T →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv Yfn (σ + T * I)).im| ≤ C * Real.log (|T| + 3) := by
  obtain ⟨Cf, t₀, hCf, -, hfa, hgrow, hlow⟩ := Yfn_generic_inputs
  obtain ⟨C, t₁, hC, ht₁4, -, h⟩ := Generic.horizontal_bound_two_line hfa hCf hgrow hlow
  refine ⟨C, t₁, hC, ht₁4, fun T hT hgood => h T hT fun ρ hρre h0 => ?_⟩
  exact hgood ρ ((Yfn_eq_zero_iff hρre).mp h0)

/-! ### the vertical side Re s = 2 -/

/-- the polynomial factor, with the sign making its real part positive on Re s = 2, |t| ≥ 2. -/
def Pneg (s : ℂ) : ℂ := -(s * (s - 1) / 2)

/-- G := L + ζ′/ζ = ξ′/ξ (the logarithmic derivative of ξ). -/
def Gfn (s : ℂ) : ℂ := Lfn s + logDeriv riemannZeta s

lemma re_Pneg_two (t : ℝ) : (Pneg (2 + t * I)).re = (t ^ 2 - 2) / 2 := by
  simp [Pneg, Complex.mul_re, Complex.mul_im, pow_two]
  ring

lemma Pneg_analyticAt (s : ℂ) : AnalyticAt ℂ Pneg s := by
  unfold Pneg
  exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const two_ne_zero).neg

/-- L is analytic on Re s > 0 away from s = 1. -/
lemma Lfn_analyticAt {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : AnalyticAt ℂ Lfn s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  unfold Lfn
  have h1 : AnalyticAt ℂ (logDeriv Gammaℝ) s := by
    apply Zeta23.RvM.logDeriv_Gammaℝ_differentiableOn.analyticAt (Zeta23.RvM.isOpen_rightHalfPlane.mem_nhds hs)
  have h2 : AnalyticAt ℂ (fun z : ℂ => 1 / z) s := analyticAt_const.div analyticAt_id hs0
  have h3 : AnalyticAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1)
  exact (h1.add h2).add h3

/-- ζ′/ζ is analytic where ζ ≠ 0 (s ≠ 1). -/
lemma logDeriv_zeta_analyticAt {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have ha := Zeta23.WeilEF.analyticAt_riemannZeta hs1
  have : AnalyticAt ℂ (fun z => deriv riemannZeta z / riemannZeta z) s := ha.deriv.div ha hζ
  exact this.congr (Filter.Eventually.of_forall fun z => (logDeriv_apply _ _).symm)

lemma Gfn_analyticAt_two (t : ℝ) : AnalyticAt ℂ Gfn (2 + t * I) := by
  unfold Gfn
  exact (Lfn_analyticAt (by simp) (two_line_ne_one t)).add
    (logDeriv_zeta_analyticAt (two_line_ne_one t) (zeta_two_line_ne_zero t))

/-- logDeriv Y = logDeriv Pneg + logDeriv ζ + logDeriv G on the line Re s = 2 (where G ≠ 0). -/
lemma logDeriv_Yfn_two {t : ℝ} (hG : Gfn (2 + t * I) ≠ 0) (ht : 2 ≤ |t|) :
    logDeriv Yfn (2 + t * I)
      = logDeriv Pneg (2 + t * I) + logDeriv riemannZeta (2 + t * I) + logDeriv Gfn (2 + t * I) := by
  set s : ℂ := 2 + t * I with hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | 1 < z.re} := by simp [hs]
  set F : ℂ → ℂ := fun z => (-1 : ℂ) * (Pneg z * (riemannZeta z * Gfn z)) with hFdef
  have hev : Yfn =ᶠ[𝓝 s] F := by
    filter_upwards [hopen.mem_nhds hsU] with z hz
    have hz0 : 0 < z.re := lt_trans zero_lt_one hz
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
    rw [Yfn_eq_factor hz0 hz1 (riemannZeta_ne_zero_of_one_lt_re hz)]
    simp only [hFdef, Pneg, Gfn]
    ring
  have hP : Pneg s ≠ 0 := by
    intro h
    have := re_Pneg_two t
    rw [← hs, h] at this
    simp at this
    nlinarith [sq_abs t]
  have hζ : riemannZeta s ≠ 0 := zeta_two_line_ne_zero t
  have hdP : DifferentiableAt ℂ Pneg s := (Pneg_analyticAt s).differentiableAt
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta (two_line_ne_one t)
  have hdG : DifferentiableAt ℂ Gfn s := (Gfn_analyticAt_two t).differentiableAt
  have h1 : logDeriv Yfn s = logDeriv F s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [h1, hFdef, logDeriv_const_mul s (-1 : ℂ) (by norm_num)]
  have h2 : logDeriv (fun z => Pneg z * (riemannZeta z * Gfn z)) s
      = logDeriv Pneg s + logDeriv (fun z => riemannZeta z * Gfn z) s :=
    logDeriv_mul s hP (mul_ne_zero hζ hG) hdP (hdζ.mul hdG)
  have h3 : logDeriv (fun z => riemannZeta z * Gfn z) s = logDeriv riemannZeta s + logDeriv Gfn s :=
    logDeriv_mul s hζ hG hdζ hdG
  rw [h2, h3]
  ring

lemma intervalIntegrable_logDeriv_two {f : ℂ → ℂ} {T₁ T₂ : ℝ}
    (h : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ f (2 + t * I) ∧ f (2 + t * I) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => logDeriv f (2 + t * I) * I) volume T₁ T₂ := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  obtain ⟨ha, hne⟩ := h t ht
  have hc := (continuousAt_logDeriv_of_analyticAt ha hne).comp
    (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t) (by fun_prop)
  exact (hc.mul continuousAt_const).continuousWithinAt

/-- **Vertical side.** -/
theorem vertical_bound : ∃ t₁ : ℝ, 2 ≤ t₁ ∧ ∀ T₁ T₂ : ℝ, t₁ ≤ T₁ → T₁ ≤ T₂ →
    |(∫ t in T₁..T₂, logDeriv Yfn (2 + t * I) * I).im| ≤ 3 * Real.pi := by
  obtain ⟨t₁, ht₁, hlow⟩ := two_line_lower
  refine ⟨t₁, ht₁, fun T₁ T₂ hT₁ h12 => ?_⟩
  have hfacts : ∀ t ∈ Icc T₁ T₂, 2 ≤ |t| ∧ 3 ≤ (Gfn (2 + t * I)).re ∧ 0 < (Pneg (2 + t * I)).re := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have ht' : t₁ ≤ |t| := le_trans (by linarith [ht.1]) (le_abs_self t)
    refine ⟨le_trans ht2 (le_abs_self t), (hlow t ht').1, ?_⟩
    rw [re_Pneg_two]
    nlinarith
  have hGne : ∀ t ∈ Icc T₁ T₂, Gfn (2 + t * I) ≠ 0 := fun t ht h => by
    have := (hfacts t ht).2.1; rw [h] at this; simp at this; linarith
  have hPne : ∀ t ∈ Icc T₁ T₂, Pneg (2 + t * I) ≠ 0 := fun t ht h => by
    have := (hfacts t ht).2.2; rw [h] at this; simp at this
  -- pointwise split
  have hcongr : EqOn (fun t : ℝ => logDeriv Yfn (2 + t * I) * I)
      (fun t : ℝ => (logDeriv Pneg (2 + t * I) * I + logDeriv riemannZeta (2 + t * I) * I)
        + logDeriv Gfn (2 + t * I) * I) (uIcc T₁ T₂) := by
    intro t ht
    rw [uIcc_of_le h12] at ht
    simp only
    rw [logDeriv_Yfn_two (hGne t ht) (hfacts t ht).1]
    ring
  have hIP : IntervalIntegrable (fun t : ℝ => logDeriv Pneg (2 + t * I) * I) volume T₁ T₂ :=
    intervalIntegrable_logDeriv_two fun t ht => by
      rw [uIcc_of_le h12] at ht
      exact ⟨Pneg_analyticAt _, hPne t ht⟩
  have hIZ : IntervalIntegrable (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) volume T₁ T₂ :=
    intervalIntegrable_logDeriv_two fun t _ =>
      ⟨Zeta23.WeilEF.analyticAt_riemannZeta (two_line_ne_one t), zeta_two_line_ne_zero t⟩
  have hIG : IntervalIntegrable (fun t : ℝ => logDeriv Gfn (2 + t * I) * I) volume T₁ T₂ :=
    intervalIntegrable_logDeriv_two fun t ht => by
      rw [uIcc_of_le h12] at ht
      exact ⟨Gfn_analyticAt_two t, hGne t ht⟩
  rw [integral_congr hcongr, integral_add (hIP.add hIZ) hIG, integral_add hIP hIZ]
  simp only [Complex.add_im]
  -- the three bounds
  have e2 : ∀ t : ℝ, (((2 : ℝ) : ℂ) + t * I) = (2 : ℂ) + t * I := fun t => by push_cast; ring
  have b1 : |(∫ t in T₁..T₂, logDeriv Pneg (2 + t * I) * I).im| ≤ Real.pi := by
    have := abs_im_integral_logDeriv_vertical_le_pi (f := Pneg) (σ := 2) h12
      (fun t _ => by rw [e2]; exact Pneg_analyticAt _) (fun t ht => by rw [e2]; exact (hfacts t ht).2.2)
    simpa only [e2] using this
  have b2 : |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi :=
    Zeta23.RvM.vertical_two T₁ T₂
  have b3 : |(∫ t in T₁..T₂, logDeriv Gfn (2 + t * I) * I).im| ≤ Real.pi := by
    have := abs_im_integral_logDeriv_vertical_le_pi (f := Gfn) (σ := 2) h12
      (fun t _ => by rw [e2]; exact Gfn_analyticAt_two t)
      (fun t ht => by rw [e2]; linarith [(hfacts t ht).2.1])
    simpa only [e2] using this
  calc |(∫ t in T₁..T₂, logDeriv Pneg (2 + t * I) * I).im
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im
        + (∫ t in T₁..T₂, logDeriv Gfn (2 + t * I) * I).im|
      ≤ |(∫ t in T₁..T₂, logDeriv Pneg (2 + t * I) * I).im|
        + |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im|
        + |(∫ t in T₁..T₂, logDeriv Gfn (2 + t * I) * I).im| := abs_add_three _ _ _
    _ ≤ Real.pi + Real.pi + Real.pi := by gcongr
    _ = 3 * Real.pi := by ring

end ZeroCount
end XiPrime
end Zeta23
