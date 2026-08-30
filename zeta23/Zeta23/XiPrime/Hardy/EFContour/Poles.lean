/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The pole data of W at 0 and 1 and the regularised Wreg := s(s−1)²·W.

  s·L₂(s) → −½ (s→0),  (s−1)·L₂(s) → ½ (s→1),  (s−1)²ζ′(s) → −1,  s·W(s) → ¼,  (s−1)²·W(s) → −½;
  Wreg := update (update (s ↦ s(s−1)²W(s)) 0 ¼) 1 (−½) is analytic on −2 < Re s < 3 (removable singularities),
  agrees with s(s−1)²W(s) off {0,1}, has W's zeros and orders there, and logDeriv Wreg = logDeriv(s(s−1)²) + W′/W.
-/
import Zeta23.XiPrime.Hardy.EFContour.Analytic

open Complex Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy
namespace EFContour

/-! ### helpers: nonvanishing of Γℝ near 0 and 1, punctured maps -/

lemma eventually_Gammaℝ_ne_zero_nhdsWithin_zero : ∀ᶠ s in 𝓝[≠] (0:ℂ), Gammaℝ s ≠ 0 := by
  have hre : ∀ᶠ s in 𝓝 (0:ℂ), -2 < s.re :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hre] with s hs hsre
  exact Gammaℝ_ne_zero_of_re hsre hs

lemma eventually_Gammaℝ_one_sub_ne_zero_nhds_zero : ∀ᶠ s in 𝓝 (0:ℂ), Gammaℝ (1 - s) ≠ 0 := by
  have h1 : ∀ᶠ s in 𝓝 (0:ℂ), s.re < 3 := (continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp)
  have h2 : ∀ᶠ s in 𝓝 (0:ℂ), s ≠ 1 := isOpen_ne.mem_nhds zero_ne_one
  filter_upwards [h1, h2] with s hs hs1
  exact Gammaℝ_one_sub_ne_zero_of_re hs hs1

lemma eventually_Gammaℝ_ne_zero_nhds_one : ∀ᶠ s in 𝓝 (1:ℂ), Gammaℝ s ≠ 0 := by
  have h1 : ∀ᶠ s in 𝓝 (1:ℂ), -2 < s.re :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by
      simp only [Set.mem_preimage, Complex.one_re, Set.mem_Ioi]; norm_num)
  have h2 : ∀ᶠ s in 𝓝 (1:ℂ), s ≠ 0 := isOpen_ne.mem_nhds one_ne_zero
  filter_upwards [h1, h2] with s hs hs0
  exact Gammaℝ_ne_zero_of_re hs hs0

lemma eventually_Gammaℝ_one_sub_ne_zero_nhdsWithin_one : ∀ᶠ s in 𝓝[≠] (1:ℂ), Gammaℝ (1 - s) ≠ 0 := by
  have h1 : ∀ᶠ s in 𝓝 (1:ℂ), s.re < 3 := (continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h1] with s hs hsre
  exact Gammaℝ_one_sub_ne_zero_of_re hsre hs

/-- s ↦ 1 − s maps 𝓝[≠] 1 to 𝓝[≠] 0. -/
lemma tendsto_one_sub_nhdsWithin : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mem_compl_singleton_iff] at hs ⊢
    exact sub_ne_zero.mpr (Ne.symm hs)

/-- logDeriv of an analytic nonvanishing function is continuous. -/
lemma continuousAt_logDeriv {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) (h0 : f s ≠ 0) :
    ContinuousAt (logDeriv f) s := by
  have e : logDeriv f = fun z => deriv f z / f z := by funext z; rw [logDeriv_apply]
  rw [e]; exact hf.deriv.continuousAt.div hf.continuousAt h0

/-! ### §4. Pole limits -/

theorem tendsto_mul_L2_zero : Tendsto (fun s : ℂ => s * L2 s) (𝓝[≠] 0) (𝓝 (-(1 / 2 : ℂ))) := by
  -- near 0 (s ≠ 0):  s·L₂ = −½ (s·logDeriv(Γℝ∘(1−·)) s + s·logDeriv G s)
  have hA0 : Gammaℝ (1 - 0) ≠ 0 := by simp [Gammaℝ_one]
  have hcontA : ContinuousAt (logDeriv (fun z => Gammaℝ (1 - z))) 0 :=
    continuousAt_logDeriv (analyticAt_Gammaℝ_one_sub hA0) hA0
  have hev : ∀ᶠ s in 𝓝[≠] (0:ℂ), s * L2 s
      = -(1/2) * (s * logDeriv (fun z => Gammaℝ (1 - z)) s + s * logDeriv invGammaℝ s) := by
    filter_upwards [eventually_Gammaℝ_ne_zero_nhdsWithin_zero,
      mem_nhdsWithin_of_mem_nhds eventually_Gammaℝ_one_sub_ne_zero_nhds_zero] with s h0 h1
    rw [L2, logDeriv_chiFE_eq h1 h0]; ring
  have hlim1 : Tendsto (fun s : ℂ => s * logDeriv (fun z => Gammaℝ (1 - z)) s) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_id.continuousAt (x := (0:ℂ))).tendsto.mul hcontA.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0:ℂ)}ᶜ))
    simpa using this
  have hlim : Tendsto (fun s : ℂ => -(1/2) * (s * logDeriv (fun z => Gammaℝ (1 - z)) s
      + s * logDeriv invGammaℝ s)) (𝓝[≠] 0) (𝓝 (-(1/2) * (0 + 1))) :=
    (hlim1.add tendsto_mul_logDeriv_invGammaℝ_zero).const_mul _
  rw [show (-(1 / 2 : ℂ)) = -(1/2) * (0 + 1) by ring]
  exact hlim.congr' (hev.mono fun _ h => h.symm)

theorem tendsto_mul_L2_one : Tendsto (fun s : ℂ => (s - 1) * L2 s) (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) := by
  have hG1 : Gammaℝ 1 ≠ 0 := by simp [Gammaℝ_one]
  have hcontG : ContinuousAt (logDeriv invGammaℝ) 1 :=
    continuousAt_logDeriv (analyticAt_invGammaℝ 1) (invGammaℝ_ne_zero_iff.mpr hG1)
  -- the Γℝ(1−·) half: (s−1)·logDeriv(Γℝ∘(1−·)) s = −((1−s)·logDeriv G (1−s)) → −1
  have hev : ∀ᶠ s in 𝓝[≠] (1:ℂ), (s - 1) * L2 s
      = -(1/2) * (-((1 - s) * logDeriv invGammaℝ (1 - s)) + (s - 1) * logDeriv invGammaℝ s) := by
    filter_upwards [eventually_Gammaℝ_one_sub_ne_zero_nhdsWithin_one,
      mem_nhdsWithin_of_mem_nhds eventually_Gammaℝ_ne_zero_nhds_one] with s h1 h0
    rw [L2, logDeriv_chiFE_eq h1 h0, logDeriv_Gammaℝ_one_sub_eq h1]
    have hcomp : logDeriv (fun z => invGammaℝ (1 - z)) s = logDeriv invGammaℝ (1 - s) * (-1) := by
      have e : (fun z => invGammaℝ (1 - z)) = invGammaℝ ∘ (fun z : ℂ => 1 - z) := rfl
      rw [e, logDeriv_comp (differentiable_invGammaℝ _) (by fun_prop)]
      congr 1
      rw [deriv_const_sub, deriv_id'']
    rw [hcomp]; ring
  have hlim1 : Tendsto (fun s : ℂ => (1 - s) * logDeriv invGammaℝ (1 - s)) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_mul_logDeriv_invGammaℝ_zero.comp tendsto_one_sub_nhdsWithin
  have hlim2 : Tendsto (fun s : ℂ => (s - 1) * logDeriv invGammaℝ s) (𝓝[≠] 1) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => (s - 1) * logDeriv invGammaℝ s) (𝓝 1)
        (𝓝 ((1 - 1) * logDeriv invGammaℝ 1)) :=
      ((tendsto_id (x := 𝓝 (1:ℂ))).sub_const 1).mul hcontG.tendsto
    have h' := h.mono_left (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))
    simpa using h'
  have hlim : Tendsto (fun s : ℂ => -(1/2) * (-((1 - s) * logDeriv invGammaℝ (1 - s))
      + (s - 1) * logDeriv invGammaℝ s)) (𝓝[≠] 1) (𝓝 (-(1/2) * (-1 + 0))) :=
    (hlim1.neg.add hlim2).const_mul _
  rw [show (1 / 2 : ℂ) = -(1/2) * (-1 + 0) by ring]
  exact hlim.congr' (hev.mono fun _ h => h.symm)

/-- the regular part of ζ at 1 in Mathlib's normalisation: F := ζ − (Γℝ)⁻¹/(s−1) is differentiable AT 1
(HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div) and near 1. -/
def zetaReg (s : ℂ) : ℂ := riemannZeta s - 1 / (s - 1) / Gammaℝ s

lemma zetaReg_differentiableAt_one : DifferentiableAt ℂ zetaReg 1 := by
  have h := HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0
  rw [HurwitzZeta.hurwitzZetaEven_zero] at h
  exact h

lemma zetaReg_differentiableAt {s : ℂ} (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) : DifferentiableAt ℂ zetaReg s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    (differentiableAt_const (1:ℂ)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1) / Gammaℝ z) s := h1.div (differentiableAt_Gammaℝ hΓ) hΓ
  exact (differentiableAt_riemannZeta hs1).sub h2

lemma zetaReg_analyticAt_one : AnalyticAt ℂ zetaReg 1 := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [eventually_Gammaℝ_ne_zero_nhds_one] with s hΓ
  rcases eq_or_ne s 1 with rfl | hs1
  · exact zetaReg_differentiableAt_one
  · exact zetaReg_differentiableAt hs1 hΓ

/-- ζ = zetaReg + G/(·−1) as FUNCTIONS (G = (Γℝ)⁻¹; both sides junk-equal at 1 and at the poles of Γℝ). -/
lemma riemannZeta_eq_zetaReg_add : riemannZeta = fun s => zetaReg s + invGammaℝ s / (s - 1) := by
  funext s
  rw [zetaReg, invGammaℝ]
  ring

theorem tendsto_sq_mul_deriv_zeta_one :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv riemannZeta s) (𝓝[≠] 1) (𝓝 (-1)) := by
  -- derivative of the polar part H := G/(s−1) off 1
  have hH : ∀ s : ℂ, s ≠ 1 → deriv (fun z => invGammaℝ z / (z - 1)) s
      = (deriv invGammaℝ s * (s - 1) - invGammaℝ s) / (s - 1) ^ 2 := by
    intro s hs
    have h := (differentiable_invGammaℝ s).hasDerivAt.div
      ((hasDerivAt_id s).sub_const (1:ℂ)) (sub_ne_zero.mpr hs)
    have e : (fun z : ℂ => invGammaℝ z / (z - 1)) = (invGammaℝ / fun x => id x - 1) := rfl
    rw [e, h.deriv]
    simp only [id]
    ring
  have hev : ∀ᶠ s in 𝓝[≠] (1:ℂ), (s - 1) ^ 2 * deriv riemannZeta s
      = (s - 1) ^ 2 * deriv zetaReg s + (deriv invGammaℝ s * (s - 1) - invGammaℝ s) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds eventually_Gammaℝ_ne_zero_nhds_one]
      with s hs hΓ
    have hdz := zetaReg_differentiableAt hs hΓ
    have hdH : DifferentiableAt ℂ (fun z => invGammaℝ z / (z - 1)) s :=
      (differentiable_invGammaℝ s).div (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs)
    rw [riemannZeta_eq_zetaReg_add]
    rw [show (fun s => zetaReg s + invGammaℝ s / (s - 1)) = zetaReg + fun z => invGammaℝ z / (z - 1) from rfl,
      deriv_add hdz hdH, hH s hs, mul_add, mul_div_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hs))]
  -- limits of the three pieces
  have hcont : ContinuousAt (deriv zetaReg) 1 := zetaReg_analyticAt_one.deriv.continuousAt
  have hl1 : Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv zetaReg s) (𝓝[≠] 1) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv zetaReg s) (𝓝 1) (𝓝 ((1 - 1) ^ 2 * deriv zetaReg 1)) :=
      (((tendsto_id (x := 𝓝 (1:ℂ))).sub_const 1).pow 2).mul hcont.tendsto
    have h' := h.mono_left (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))
    simpa using h'
  have hl2 : Tendsto (fun s : ℂ => deriv invGammaℝ s * (s - 1) - invGammaℝ s) (𝓝[≠] 1) (𝓝 (0 - 1)) := by
    have hG1 : invGammaℝ 1 = 1 := by rw [invGammaℝ, Gammaℝ_one, inv_one]
    have hd : ContinuousAt (deriv invGammaℝ) 1 := (analyticAt_invGammaℝ 1).deriv.continuousAt
    have h1 : Tendsto (fun s : ℂ => deriv invGammaℝ s * (s - 1)) (𝓝 1) (𝓝 0) := by
      have : Tendsto (fun s : ℂ => deriv invGammaℝ s * (s - 1)) (𝓝 1) (𝓝 (deriv invGammaℝ 1 * (1 - 1))) :=
        hd.tendsto.mul ((tendsto_id (x := 𝓝 (1:ℂ))).sub_const 1)
      simpa using this
    have h2 : Tendsto invGammaℝ (𝓝 1) (𝓝 1) := by
      have := (differentiable_invGammaℝ.continuous.continuousAt (x := (1:ℂ))).tendsto
      rwa [hG1] at this
    exact (h1.sub h2).mono_left nhdsWithin_le_nhds
  have hlim := hl1.add hl2
  rw [show (-1 : ℂ) = 0 + (0 - 1) by ring]
  exact hlim.congr' (hev.mono fun _ h => h.symm)

theorem tendsto_mul_hardyW_zero : Tendsto (fun s : ℂ => s * hardyW s) (𝓝[≠] 0) (𝓝 (1 / 4 : ℂ)) := by
  -- s·W = s·ζ′ + (s·L₂)·ζ → 0 + (−½)(−½)
  have hζ : AnalyticAt ℂ riemannZeta 0 := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
    filter_upwards [isOpen_ne.mem_nhds (zero_ne_one : (0:ℂ) ≠ 1)] with z hz
    exact differentiableAt_riemannZeta hz
  have h1 : Tendsto (fun s : ℂ => s * deriv riemannZeta s) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_id.continuousAt (x := (0:ℂ))).tendsto.mul hζ.deriv.continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0:ℂ)}ᶜ))
    simpa using this
  have h2 : Tendsto riemannZeta (𝓝[≠] 0) (𝓝 (-1 / 2)) := by
    have := hζ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0:ℂ)}ᶜ))
    rwa [riemannZeta_zero] at this
  have hlim := h1.add (tendsto_mul_L2_zero.mul h2)
  have e : ∀ s : ℂ, s * hardyW s = s * deriv riemannZeta s + s * L2 s * riemannZeta s := by
    intro s; rw [hardyW]; ring
  simp_rw [e]
  convert hlim using 2
  norm_num

theorem tendsto_sq_mul_hardyW_one :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * hardyW s) (𝓝[≠] 1) (𝓝 (-(1 / 2 : ℂ))) := by
  have hlim := tendsto_sq_mul_deriv_zeta_one.add (tendsto_mul_L2_one.mul riemannZeta_residue_one)
  have e : ∀ s : ℂ, (s - 1) ^ 2 * hardyW s
      = (s - 1) ^ 2 * deriv riemannZeta s + (s - 1) * L2 s * ((s - 1) * riemannZeta s) := by
    intro s; rw [hardyW]; ring
  simp_rw [e]
  convert hlim using 2
  norm_num

/-! ### §5. The regularised Wreg -/

/-- p(s) := s(s−1)², the polar polynomial of W on the strip. -/
def polarPoly (s : ℂ) : ℂ := s * (s - 1) ^ 2

/-- Wreg := s(s−1)²·W(s) with the removable singularities at 0, 1 filled in (values ¼, −½). -/
def Wreg : ℂ → ℂ :=
  Function.update (Function.update (fun s : ℂ => polarPoly s * hardyW s) 0 (1 / 4)) 1 (-(1 / 2))

theorem Wreg_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : Wreg s = polarPoly s * hardyW s := by
  simp [Wreg, Function.update_of_ne h1, Function.update_of_ne h0]

theorem Wreg_zero : Wreg 0 = 1 / 4 := by
  simp [Wreg]

theorem Wreg_one : Wreg 1 = -(1 / 2) := by
  simp [Wreg]

lemma polarPoly_analyticAt (s : ℂ) : AnalyticAt ℂ polarPoly s := by
  have e : polarPoly = fun s : ℂ => s * (s - 1) ^ 2 := rfl
  rw [e]; fun_prop

lemma polarPoly_ne_zero {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : polarPoly s ≠ 0 :=
  mul_ne_zero h0 (pow_ne_zero _ (sub_ne_zero.mpr h1))

/-- off {0,1}, Wreg agrees with p·W on a neighbourhood. -/
lemma Wreg_eventuallyEq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Wreg =ᶠ[𝓝 s] fun z => polarPoly z * hardyW z := by
  filter_upwards [isOpen_ne.mem_nhds h0, isOpen_ne.mem_nhds h1] with z hz0 hz1
  exact Wreg_eq hz0 hz1

lemma Wreg_eventuallyEq_nhdsWithin_zero :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), Wreg z = polarPoly z * hardyW z := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (zero_ne_one : (0:ℂ) ≠ 1))]
    with z hz0 hz1
  exact Wreg_eq hz0 hz1

lemma Wreg_eventuallyEq_nhdsWithin_one :
    ∀ᶠ z in 𝓝[≠] (1:ℂ), Wreg z = polarPoly z * hardyW z := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (one_ne_zero : (1:ℂ) ≠ 0))]
    with z hz1 hz0
  exact Wreg_eq hz0 hz1

lemma mem_stripReg_of_near {s : ℂ} (hre : -2 < s.re) (hre' : s.re < 3) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s ∈ stripReg := ⟨hre, hre', h0, h1⟩

/-- Wreg is analytic on the strip −2 < Re s < 3 (including at 0 and 1). -/
theorem Wreg_analyticAt {s : ℂ} (hre : -2 < s.re) (hre' : s.re < 3) : AnalyticAt ℂ Wreg s := by
  -- the strip condition is open
  have hstrip : ∀ᶠ z in 𝓝 s, -2 < z.re ∧ z.re < 3 := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (show s ∈ re ⁻¹' Ioi (-2) from hre),
      (continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds (show s ∈ re ⁻¹' Iio 3 from hre')] with z h1 h2
    exact ⟨h1, h2⟩
  -- differentiability of p·W at points of the strip off {0,1}
  have hdiff : ∀ z : ℂ, -2 < z.re → z.re < 3 → z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ Wreg z := by
    intro z h1 h2 hz0 hz1
    have ha : AnalyticAt ℂ (fun z => polarPoly z * hardyW z) z :=
      (polarPoly_analyticAt z).mul (hardyW_analyticAt_of_mem ⟨h1, h2, hz0, hz1⟩)
    exact (ha.congr (Wreg_eventuallyEq hz0 hz1).symm).differentiableAt
  rcases eq_or_ne s 0 with rfl | h0
  · -- removable singularity at 0
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hstrip,
        mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (zero_ne_one : (0:ℂ) ≠ 1))] with z hz0 hz hz1
      exact hdiff z hz.1 hz.2 hz0 hz1
    · unfold Wreg
      rw [continuousAt_update_of_ne zero_ne_one, continuousAt_update_same]
      have h0 : Tendsto (fun z : ℂ => (z - 1) ^ 2) (𝓝 0) (𝓝 ((0 - 1) ^ 2)) :=
        ((tendsto_id (x := 𝓝 (0:ℂ))).sub_const 1).pow 2
      have h := (h0.mono_left (nhdsWithin_le_nhds (s := {(0:ℂ)}ᶜ))).mul tendsto_mul_hardyW_zero
      have e : ∀ z : ℂ, polarPoly z * hardyW z = (z - 1) ^ 2 * (z * hardyW z) := by
        intro z; rw [polarPoly]; ring
      simp_rw [e]
      convert h using 2; norm_num
  rcases eq_or_ne s 1 with rfl | h1
  · -- removable singularity at 1
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hstrip,
        mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (one_ne_zero : (1:ℂ) ≠ 0))] with z hz1 hz hz0
      exact hdiff z hz.1 hz.2 hz0 hz1
    · unfold Wreg
      rw [continuousAt_update_same]
      -- the inner update differs from p·W only at 0
      have hev : (fun z : ℂ => polarPoly z * hardyW z)
          =ᶠ[𝓝[≠] (1:ℂ)] Function.update (fun s : ℂ => polarPoly s * hardyW s) 0 (1 / 4) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (one_ne_zero : (1:ℂ) ≠ 0))] with z hz0
        rw [Function.update_of_ne hz0]
      refine Tendsto.congr' hev ?_
      have h := (((continuous_id).continuousAt (x := (1:ℂ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))).mul tendsto_sq_mul_hardyW_one
      have e : ∀ z : ℂ, polarPoly z * hardyW z = z * ((z - 1) ^ 2 * hardyW z) := by
        intro z; rw [polarPoly]; ring
      simp_rw [e]
      convert h using 2 <;> simp
  · exact ((polarPoly_analyticAt s).mul (hardyW_analyticAt_of_mem ⟨hre, hre', h0, h1⟩)).congr
      (Wreg_eventuallyEq h0 h1).symm

/-- off {0,1} (inside the strip) Wreg vanishes exactly where W does … -/
theorem Wreg_eq_zero_iff {s : ℂ} (hs : s ∈ stripReg) : Wreg s = 0 ↔ hardyW s = 0 := by
  obtain ⟨-, -, h0, h1⟩ := hs
  rw [Wreg_eq h0 h1, mul_eq_zero, or_iff_right (polarPoly_ne_zero h0 h1)]

/-- … with the same analytic order. -/
theorem analyticOrderAt_Wreg {s : ℂ} (hs : s ∈ stripReg) : analyticOrderAt Wreg s = analyticOrderAt hardyW s := by
  obtain ⟨hre, hre', h0, h1⟩ := hs
  rw [analyticOrderAt_congr (Wreg_eventuallyEq h0 h1)]
  have e : (fun z => polarPoly z * hardyW z) = polarPoly * hardyW := rfl
  rw [e, analyticOrderAt_mul (polarPoly_analyticAt s) (hardyW_analyticAt_of_mem ⟨hre, hre', h0, h1⟩),
    (polarPoly_analyticAt s).analyticOrderAt_eq_zero.mpr (polarPoly_ne_zero h0 h1), zero_add]

/-- logDeriv Wreg = logDeriv p + W′/W off {0,1} where W ≠ 0. -/
theorem logDeriv_Wreg {s : ℂ} (hs : s ∈ stripReg) (hW : hardyW s ≠ 0) :
    logDeriv Wreg s = logDeriv polarPoly s + logDeriv hardyW s := by
  obtain ⟨hre, hre', h0, h1⟩ := hs
  have hev := Wreg_eventuallyEq h0 h1
  have e1 : logDeriv Wreg s = logDeriv (fun z => polarPoly z * hardyW z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [e1]
  exact logDeriv_mul s (polarPoly_ne_zero h0 h1) hW (polarPoly_analyticAt s).differentiableAt
    (hardyW_analyticAt_of_mem ⟨hre, hre', h0, h1⟩).differentiableAt

end EFContour
end Hardy
end XiPrime
end Zeta23

end
