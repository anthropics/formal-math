/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/Count.lean — Riemann–von Mangoldt for the non-real zeros of W.

  riemannVonMangoldt_W (hZ : WZerosInStrip t₀) (hs : WSeam t₀) : RiemannVonMangoldt (wZeros hZ hs)
i.e. |N_W(T,2T) − (T/2π)ℓ₁(T)| ≤ C log T (T ≥ T₀) and the two-sided local count N_W(t,t+1] ≤ A₀ log(|t|+3).
Route: the local count and the horizontal O(log T) bounds are the generic two-line Landau/Jensen
machine (Zeta23/XiPrime/ZeroCount/Generic.lean) instantiated at f := W with the inputs of Hardy/TwoLine.lean; the main
term comes from the argument principle for Ω = Γℝ·W (Hardy/Contour.lean): N_W = (1/π)Im∫_L Ω′/Ω, Ω′/Ω = Γℝ′/Γℝ + W′/W,
the Γℝ-part and the μ-bookkeeping being the generic ZeroCount/GenericRvM.rvM_main_of (Zeta23.RvM.gamma_side), and the W-part O(log T)
(horizontals: Generic; the vertical Re s = 2: W = ζ·(ζ′/ζ + L₂) with each factor of positive real part there, so
each turns by at most π — Zeta23/XiPrime/ZeroCount/ArgBound.lean + vertical_two).
-/
import Zeta23.XiPrime.Hardy.Contour
import Zeta23.XiPrime.ZeroCount
import Zeta23.XiPrime.ZeroCount.Generic
import Zeta23.XiPrime.ZeroCount.ArgBound
import Zeta23.XiPrime.ZeroCount.Sides
import Zeta23.RvM.Backlund

open Complex Set Filter Topology MeasureTheory intervalIntegral Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

open Zeta23.RvM (halfContour)
open Zeta23.XiPrime.ZeroCount (two_line_ne_one zeta_two_line_ne_zero logDeriv_zeta_analyticAt
  continuousAt_logDeriv_of_analyticAt abs_im_integral_logDeriv_vertical_le_pi)

variable {t₀ : ℝ}

/-! ### the vertical side Re s = 2: W = ζ·G, G := ζ′/ζ + L₂ -/

/-- G := ζ′/ζ + L₂ (so W = ζ·G where ζ ≠ 0). -/
def Gw (s : ℂ) : ℂ := logDeriv riemannZeta s + L2 s

lemma Gw_analyticAt {s : ℂ} (hs : s.im ≠ 0) (hζ : riemannZeta s ≠ 0) : AnalyticAt ℂ Gw s := by
  have e : Gw = fun z => logDeriv riemannZeta z + L2 z := rfl
  rw [e]; exact (logDeriv_zeta_analyticAt (ne_one_of_im_ne_zero hs) hζ).add (L2_analyticAt hs)

/-- W = ζ·G near any non-real point where ζ ≠ 0; hence logDeriv W = ζ′/ζ + G′/G there (if also G ≠ 0). -/
lemma logDeriv_hardyW_eq_of_zeta_ne {s : ℂ} (hs : s.im ≠ 0) (hζ : riemannZeta s ≠ 0) (hG : Gw s ≠ 0) :
    logDeriv hardyW s = logDeriv riemannZeta s + logDeriv Gw s := by
  have hs1 := ne_one_of_im_ne_zero hs
  have hcont : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta hs1).continuousAt
  have hev : hardyW =ᶠ[𝓝 s] fun z => riemannZeta z * Gw z := by
    filter_upwards [hcont.eventually_ne hζ] with z hz
    exact hardyW_eq_zeta_mul hz
  have h1 : logDeriv hardyW s = logDeriv (fun z => riemannZeta z * Gw z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [h1, logDeriv_mul s hζ hG (differentiableAt_riemannZeta hs1) (Gw_analyticAt hs hζ).differentiableAt]

/-- **the vertical side**: for t₁ from hardyW_two_line_lower and t₁ ≤ T₁ ≤ T₂,
|Im ∫_{T₁}^{T₂} (W′/W)(2+it)·i dt| ≤ 2π. -/
theorem vertical_boundW : ∃ t₁ : ℝ, 2 ≤ t₁ ∧ ∀ T₁ T₂ : ℝ, t₁ ≤ T₁ → T₁ ≤ T₂ →
    (∀ t ∈ Icc T₁ T₂, hardyW (2 + t * I) ≠ 0) ∧
    |(∫ t in T₁..T₂, logDeriv hardyW (2 + t * I) * I).im| ≤ 2 * Real.pi := by
  obtain ⟨t₁, ht₁, hlow⟩ := hardyW_two_line_lower
  refine ⟨t₁, ht₁, fun T₁ T₂ hT₁ h12 => ?_⟩
  have hfacts : ∀ t ∈ Icc T₁ T₂, t ≠ 0 ∧ ((2 : ℂ) + t * I).im ≠ 0 ∧ 3 ≤ (Gw (2 + t * I)).re ∧
      Gw (2 + t * I) ≠ 0 ∧ hardyW (2 + t * I) ≠ 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have habs : t₁ ≤ |t| := by rw [abs_of_pos ht0]; linarith [ht.1]
    obtain ⟨hre, hnorm⟩ := hlow t habs
    have hG0 : Gw (2 + t * I) ≠ 0 := fun h => by
      have : (Gw (2 + t * I)).re = 0 := by rw [h]; simp
      unfold Gw at this; linarith
    have hW0 : hardyW (2 + t * I) ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
    exact ⟨ht0.ne', by simp [ht0.ne'], hre, hG0, hW0⟩
  refine ⟨fun t ht => (hfacts t ht).2.2.2.2, ?_⟩
  -- pointwise split along the segment
  have heq : EqOn (fun t : ℝ => logDeriv hardyW (2 + t * I) * I)
      (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I + logDeriv Gw (2 + t * I) * I) (uIcc T₁ T₂) := by
    intro t ht
    rw [uIcc_of_le h12] at ht
    obtain ⟨-, hs, -, hG, -⟩ := hfacts t ht
    simp only
    rw [logDeriv_hardyW_eq_of_zeta_ne hs (zeta_two_line_ne_zero t) hG]; ring
  -- integrability (continuity along the segment)
  have hcζ : ContinuousOn (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) (uIcc T₁ T₂) := by
    intro t ht
    rw [uIcc_of_le h12] at ht
    obtain ⟨-, hs, -, -, -⟩ := hfacts t ht
    have hc := continuousAt_logDeriv_of_analyticAt
      (analyticAt_riemannZeta (ne_one_of_im_ne_zero hs)) (zeta_two_line_ne_zero t)
    exact ((hc.comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t) (by fun_prop)).mul
      continuousAt_const).continuousWithinAt
  have hcG : ContinuousOn (fun t : ℝ => logDeriv Gw (2 + t * I) * I) (uIcc T₁ T₂) := by
    intro t ht
    rw [uIcc_of_le h12] at ht
    obtain ⟨-, hs, -, hG, -⟩ := hfacts t ht
    have hc := continuousAt_logDeriv_of_analyticAt (Gw_analyticAt hs (zeta_two_line_ne_zero t)) hG
    exact ((hc.comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t) (by fun_prop)).mul
      continuousAt_const).continuousWithinAt
  rw [integral_congr heq, integral_add hcζ.intervalIntegrable hcG.intervalIntegrable, Complex.add_im]
  have h1 : |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := Zeta23.RvM.vertical_two T₁ T₂
  have h2 : |(∫ t in T₁..T₂, logDeriv Gw (2 + t * I) * I).im| ≤ Real.pi := by
    refine abs_im_integral_logDeriv_vertical_le_pi (σ := 2) h12 (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨-, hs, -, -, -⟩ := hfacts t ht
      have := Gw_analyticAt hs (zeta_two_line_ne_zero t)
      simpa using this
    · obtain ⟨-, -, hre, -, -⟩ := hfacts t ht
      have : ((2 : ℝ) : ℂ) + t * I = 2 + t * I := by push_cast; ring
      rw [this]; linarith
  calc |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im + (∫ t in T₁..T₂, logDeriv Gw (2 + t * I) * I).im|
      ≤ |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im|
        + |(∫ t in T₁..T₂, logDeriv Gw (2 + t * I) * I).im| := abs_add_le _ _
    _ ≤ 2 * Real.pi := by linarith

/-! ### the Generic two-line machine at f := W -/

/-- the packaged Generic hypotheses for W (t₁ from the two-line lower bound). -/
theorem hardyW_generic_inputs : ∃ (Cf t₁ : ℝ), 0 < Cf ∧ 2 ≤ t₁ ∧
    (∀ t : ℝ, t₁ ≤ |t| → AnalyticOnNhd ℂ hardyW (closedBall (2 + t * I) (91 / 50))) ∧
    (∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖hardyW s‖ ≤ Cf * |s.im| ^ 2) ∧
    (∀ t : ℝ, t₁ ≤ |t| → 1 ≤ ‖hardyW (2 + t * I)‖) := by
  obtain ⟨Cf, hCf, hgrow⟩ := hardyW_growth
  obtain ⟨t₁, ht₁, hlow⟩ := hardyW_two_line_lower
  exact ⟨Cf, t₁, hCf, ht₁, fun t ht => hardyW_analyticOnNhd_disc t (le_trans ht₁ ht), hgrow,
    fun t ht => (hlow t ht).2⟩

/-- **horizontal sides**: |Im ∫_{1/2}^{2} (W′/W)(σ+iT) dσ| ≤ C log(|T|+3) at good heights |T| ≥ t₁. -/
theorem horizontal_boundW : ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ ∀ T : ℝ, t₁ ≤ |T| → GoodHeightW T →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv hardyW (σ + T * I)).im| ≤ C * Real.log (|T| + 3) := by
  obtain ⟨Cf, t₁, hCf, ht₁, hfa, hgrow, hlow⟩ := hardyW_generic_inputs
  obtain ⟨C, t₂, hC, ht₂4, ht₁₂, h⟩ := Zeta23.XiPrime.ZeroCount.Generic.horizontal_bound_two_line hfa hCf hgrow hlow
  refine ⟨C, t₂, hC, ht₂4, fun T hT hg => h T hT fun ρ _ h0 him => ?_⟩
  have hT0 : T ≠ 0 := by intro h; rw [h] at hT; norm_num at hT; linarith
  exact hg ρ ⟨h0, by rw [him]; exact hT0⟩ him

/-- **local count** for any ZeroConfig whose carrier consists of non-real W-zeros with m = wMult. -/
theorem local_countW (Zc : ZeroConfig)
    (hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → hardyW ρ = 0 ∧ analyticOrderNatAt hardyW ρ = Zc.mult ρ) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Zc.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨Cf, t₁, hCf, _, hfa, hgrow, hlow⟩ := hardyW_generic_inputs
  exact Zeta23.XiPrime.ZeroCount.Generic.local_count_two_line hfa hCf hgrow hlow Zc hlink

theorem local_count_wZeros (hZ : WZerosInStrip t₀) (hs : WSeam t₀) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, ((wZeros hZ hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) :=
  local_countW (wZeros hZ hs) fun _ hρ _ => ⟨hρ.1.1, rfl⟩

/-! ### splitting Ω′/Ω = Γℝ′/Γℝ + W′/W along the half-contour -/

theorem halfContour_omegaW_split {T₁ T₂ : ℝ} (h1 : 0 < T₁) (h12 : T₁ ≤ T₂)
    (hg₁ : GoodHeightW T₁) (hg₂ : GoodHeightW T₂) (hvert : ∀ t ∈ Icc T₁ T₂, hardyW (2 + t * I) ≠ 0) :
    halfContour (logDeriv omegaW) T₁ T₂ =
      halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ + halfContour (logDeriv hardyW) T₁ T₂ := by
  have hseg : ∀ (T : ℝ), 0 < T → GoodHeightW T → ∀ σ ∈ uIcc (1 / 2 : ℝ) 2,
      0 < ((σ : ℂ) + T * I).re ∧ ((σ : ℂ) + T * I).im ≠ 0 ∧ hardyW ((σ : ℂ) + T * I) ≠ 0 := by
    intro T hT hg σ hσ
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    exact ⟨by simp; linarith [hσ.1], by simp [hT.ne'], goodHeightW_ne_zero hT.ne' hg (by simp)⟩
  have hver : ∀ t ∈ uIcc T₁ T₂, 0 < ((2 : ℂ) + t * I).re ∧ ((2 : ℂ) + t * I).im ≠ 0 ∧
      hardyW ((2 : ℂ) + t * I) ≠ 0 := by
    intro t ht
    rw [uIcc_of_le h12] at ht
    exact ⟨by simp, by simp; linarith [ht.1], hvert t ht⟩
  have hT₂ : 0 < T₂ := lt_of_lt_of_le h1 h12
  have keyb : EqOn (fun σ : ℝ => logDeriv omegaW ((σ : ℂ) + T₁ * I))
      (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T₁ * I) + logDeriv hardyW ((σ : ℂ) + T₁ * I))
      (uIcc (1 / 2 : ℝ) 2) := fun σ hσ => by
    obtain ⟨-, him, hne⟩ := hseg T₁ h1 hg₁ σ hσ
    exact logDeriv_omegaW_eq him hne
  have keyt : EqOn (fun σ : ℝ => logDeriv omegaW ((σ : ℂ) + T₂ * I))
      (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T₂ * I) + logDeriv hardyW ((σ : ℂ) + T₂ * I))
      (uIcc (1 / 2 : ℝ) 2) := fun σ hσ => by
    obtain ⟨-, him, hne⟩ := hseg T₂ hT₂ hg₂ σ hσ
    exact logDeriv_omegaW_eq him hne
  have keyr : EqOn (fun t : ℝ => logDeriv omegaW ((2 : ℂ) + t * I))
      (fun t : ℝ => logDeriv Complex.Gammaℝ ((2 : ℂ) + t * I) + logDeriv hardyW ((2 : ℂ) + t * I))
      (uIcc T₁ T₂) := fun t ht => by
    obtain ⟨-, him, hne⟩ := hver t ht
    exact logDeriv_omegaW_eq him hne
  have hΓc : ∀ {s : ℂ}, 0 < s.re → ContinuousAt (logDeriv Complex.Gammaℝ) s := fun hs =>
    (Zeta23.RvM.logDeriv_Gammaℝ_differentiableOn.differentiableAt
      (Zeta23.RvM.isOpen_rightHalfPlane.mem_nhds hs)).continuousAt
  have hWc : ∀ {s : ℂ}, s.im ≠ 0 → hardyW s ≠ 0 → ContinuousAt (logDeriv hardyW) s := fun hs hne =>
    continuousAt_logDeriv_of_analyticAt (hardyW_analyticAt hs) hne
  have hintbΓ : ∀ (T : ℝ), 0 < T → GoodHeightW T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T * I)) volume (1 / 2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨hre, -, -⟩ := hseg T hT hg σ hσ
    exact ((hΓc hre).comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (x := σ) (by fun_prop)).continuousWithinAt
  have hintbW : ∀ (T : ℝ), 0 < T → GoodHeightW T →
      IntervalIntegrable (fun σ : ℝ => logDeriv hardyW ((σ : ℂ) + T * I)) volume (1 / 2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨-, him, hne⟩ := hseg T hT hg σ hσ
    exact ((hWc him hne).comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (x := σ) (by fun_prop)).continuousWithinAt
  have hintrΓ : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((2 : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((hΓc (hver t ht).1).comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t) (by fun_prop)).continuousWithinAt
  have hintrW : IntervalIntegrable (fun t : ℝ => logDeriv hardyW ((2 : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((hWc (hver t ht).2.1 (hver t ht).2.2).comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t)
      (by fun_prop)).continuousWithinAt
  unfold halfContour
  rw [integral_congr keyb, integral_congr keyt, integral_congr keyr,
    integral_add (hintbΓ T₁ h1 hg₁) (hintbW T₁ h1 hg₁), integral_add (hintbΓ T₂ hT₂ hg₂) (hintbW T₂ hT₂ hg₂),
    integral_add hintrΓ hintrW]
  ring

/-! ### the W-part of the half-contour is O(log T) -/

theorem halfContour_hardyW_bound : ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
    GoodHeightW T₁ → GoodHeightW T₂ →
    (∀ t ∈ Icc T₁ T₂, hardyW (2 + t * I) ≠ 0) ∧
    |(halfContour (logDeriv hardyW) T₁ T₂).im|
      ≤ C * Real.log (|T₁| + 3) + 2 * Real.pi + C * Real.log (|T₂| + 3) := by
  obtain ⟨CH, tH, hCH, htH4, hH⟩ := horizontal_boundW
  obtain ⟨tV, htV2, hV⟩ := vertical_boundW
  refine ⟨CH, max tH tV, hCH, le_trans htH4 (le_max_left _ _), fun T₁ T₂ hT₁ h12 hg₁ hg₂ => ?_⟩
  have h1 := hH T₁ (le_trans (le_trans (le_max_left _ _) hT₁) (le_abs_self _)) hg₁
  have h2 := hH T₂ (le_trans (le_trans (le_max_left _ _) (hT₁.trans h12)) (le_abs_self _)) hg₂
  obtain ⟨hne, h3⟩ := hV T₁ T₂ (le_trans (le_max_right _ _) hT₁) h12
  refine ⟨hne, ?_⟩
  unfold halfContour
  have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₁ * I))
      + (∫ t in T₁..T₂, logDeriv hardyW (2 + t * I)) * I
      - ∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₂ * I)).im
      = (∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₁ * I)).im
        + ((∫ t in T₁..T₂, logDeriv hardyW (2 + t * I)) * I).im
        - (∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₂ * I)).im := by
    simp [Complex.add_im, Complex.sub_im]
  rw [eim]
  have hmulI : ((∫ t in T₁..T₂, logDeriv hardyW (2 + t * I)) * I).im
      = (∫ t in T₁..T₂, logDeriv hardyW (2 + t * I) * I).im :=
    congrArg Complex.im (intervalIntegral.integral_mul_const (μ := volume) I
      (fun t : ℝ => logDeriv hardyW (2 + t * I))).symm
  rw [hmulI]
  calc |(∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₁ * I)).im
        + (∫ t in T₁..T₂, logDeriv hardyW (2 + t * I) * I).im
        - (∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₂ * I)).im|
      ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₁ * I)).im|
        + |(∫ t in T₁..T₂, logDeriv hardyW (2 + t * I) * I).im|
        + |(∫ σ in (1/2:ℝ)..2, logDeriv hardyW (σ + T₂ * I)).im| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ CH * Real.log (|T₁| + 3) + 2 * Real.pi + CH * Real.log (|T₂| + 3) := by linarith

/-! ### the main term -/

/-- **Riemann–von Mangoldt main term for W**: |N_W(T,2T) − (T/2π)ℓ₁(T)| ≤ C log T for T ≥ T₀
(instance of ZeroCount/GenericRvM.rvM_main_of: Zc := wZeros, Good := GoodHeightW, Λ := Ω, residual = the W half-contour). -/
theorem hardyW_rvM_main (hZ : WZerosInStrip t₀) (hs : WSeam t₀) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |((wZeros hZ hs).N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  have ht₀ := hs.pos
  obtain ⟨CY, TY, hCY, hTY4, hYb⟩ := halfContour_hardyW_bound
  refine ZeroCount.GenericRvM.rvM_main_of (wZeros hZ hs) GoodHeightW omegaW ht₀.le
    (fun a ha => exists_goodHeightW hs ha)
    (fun T₁ T₂ h0 h12 hg₁ hg₂ => by
      rw [wZeros_N hZ hs h0]; exact NcountW_eq_im_halfContour hZ hs h0 h12 hg₁ hg₂)
    ⟨CY, 2 * Real.pi, max TY t₀, hCY, by positivity, fun T₁ T₂ hT h12 hg₁ hg₂ => ?_⟩
    (local_count_wZeros hZ hs)
  have hTY : TY ≤ T₁ := le_trans (le_max_left _ _) hT
  have h1 : 0 < T₁ := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) hT)
  obtain ⟨hvert, hbound⟩ := hYb T₁ T₂ hTY h12 hg₁ hg₂
  rw [halfContour_omegaW_split h1 h12 hg₁ hg₂ hvert, Complex.add_im, add_sub_cancel_left]
  exact hbound

/-- **H-RvM for the non-real zeros of W** (|Im| ≥ t₀): main count + two-sided local count. -/
theorem riemannVonMangoldt_W (hZ : WZerosInStrip t₀) (hs : WSeam t₀) : RiemannVonMangoldt (wZeros hZ hs) :=
  ⟨hardyW_rvM_main hZ hs, local_count_wZeros hZ hs⟩

end Hardy

export Hardy (riemannVonMangoldt_W)

/-- with the seam discharged: only the strip hypothesis (and t₀ > 0) remain. -/
theorem riemannVonMangoldt_W' {t₀ : ℝ} (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) :
    RiemannVonMangoldt (wZeros hZ (wSeam_of_strip ht₀ hZ)) :=
  riemannVonMangoldt_W hZ (wSeam_of_strip ht₀ hZ)

end XiPrime
end Zeta23

end
