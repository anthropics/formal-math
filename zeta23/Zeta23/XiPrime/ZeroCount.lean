/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount.lean — the Riemann–von Mangoldt formula for the zeros of ξ′.

  theorem xiDeriv_riemannVonMangoldt (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) : XiDerivRvM hF2 hs
i.e. Zeta23.RiemannVonMangoldt (xiDerivZeros hF2 hs):
  main        : ∃ C T₀, ∀ T ≥ T₀, |N_{ξ′}(T,2T) − (T/2π)·ℓ₁(T)| ≤ C log T      ([XF′ (F3)]: N_{ξ′} = N + O(log))
  local_count : ∃ A₀ ≥ 1, ∀ t, N_{ξ′}(t,t+1] ≤ A₀ log(|t|+3)                 (ZeroCount/Landau.lean).
Route for main (the Zeta23/RvM route for ζ, with Y := ξ′/Γℝ in place of ζ): argument principle for the
entire function ξ′ on [−1,2]×[T₁,T₂] at good heights, folded onto the right half-contour L by
ξ′(1−s̄) = −conj ξ′(s) (ZeroCount/Contour.lean):  N_{ξ′}(T₁,T₂) = (1/π)·Im ∫_L ξ″/ξ′;  on L,
ξ″/ξ′ = Γℝ′/Γℝ + Y′/Y (Seam.logDeriv_xiDeriv_eq); (1/π)·Im ∫_L Γℝ′/Γℝ = ∫_{T₁}^{T₂} μ EXACTLY
(Zeta23.RvM.gamma_side), whose asymptotic is GammaFacts.int_mu (a theorem: Zeta23.gammaFacts); the Y′/Y part
is O(log T) (ZeroCount/Sides.lean: horizontals by Landau's partial fraction, vertical by three argument
pieces).  (F2) enters only through the ZeroConfig (window geometry / no zeros on Re s = −1, 2).
-/
import Zeta23.XiPrime.ZeroCount.Sides
import Zeta23.XiPrime.ZeroCount.Contour
import Zeta23.XiPrime.ZeroCount.GenericRvM
import Zeta23.RvM.GammaSide
import Zeta23.GammaFacts.Complete

open Complex Set Filter Topology MeasureTheory intervalIntegral Metric
open scoped ComplexConjugate

attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23

namespace XiPrime
namespace ZeroCount

open Zeta23.RvM (halfContour)

/-! ### splitting ξ″/ξ′ = Γℝ′/Γℝ + Y′/Y along the half-contour -/

theorem halfContour_xiDeriv_split (hF2 : XiDerivZerosInStrip) {T₁ T₂ : ℝ}
    (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    halfContour (logDeriv xiDeriv) T₁ T₂ =
      halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ + halfContour (logDeriv Yfn) T₁ T₂ := by
  -- facts at horizontal-segment points (good height T): Re s = σ ∈ [1/2,2] > 0, ξ′ ≠ 0
  have hseg : ∀ (T : ℝ), GoodHeight T → ∀ σ ∈ uIcc (1 / 2 : ℝ) 2,
      0 < ((σ : ℂ) + T * I).re ∧ xiDeriv ((σ : ℂ) + T * I) ≠ 0 := by
    intro T hg σ hσ
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    exact ⟨by simp; linarith [hσ.1], goodHeight_xiDeriv_ne_zero hg (by simp)⟩
  -- facts at vertical-segment points (Re s = 2): ξ′ ≠ 0 by (F2)
  have hvert : ∀ t : ℝ, 0 < ((2 : ℂ) + t * I).re ∧ xiDeriv ((2 : ℂ) + t * I) ≠ 0 := by
    intro t
    refine ⟨by simp, fun h => ?_⟩
    have := (hF2 _ h).2
    simp at this
  have keyb : EqOn (fun σ : ℝ => logDeriv xiDeriv ((σ : ℂ) + T₁ * I))
      (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T₁ * I) + logDeriv Yfn ((σ : ℂ) + T₁ * I))
      (uIcc (1 / 2 : ℝ) 2) := fun σ hσ => by
    obtain ⟨hre, hne⟩ := hseg T₁ hg₁ σ hσ
    exact logDeriv_xiDeriv_eq hre hne
  have keyt : EqOn (fun σ : ℝ => logDeriv xiDeriv ((σ : ℂ) + T₂ * I))
      (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T₂ * I) + logDeriv Yfn ((σ : ℂ) + T₂ * I))
      (uIcc (1 / 2 : ℝ) 2) := fun σ hσ => by
    obtain ⟨hre, hne⟩ := hseg T₂ hg₂ σ hσ
    exact logDeriv_xiDeriv_eq hre hne
  have keyr : EqOn (fun t : ℝ => logDeriv xiDeriv ((2 : ℂ) + t * I))
      (fun t : ℝ => logDeriv Complex.Gammaℝ ((2 : ℂ) + t * I) + logDeriv Yfn ((2 : ℂ) + t * I))
      (uIcc T₁ T₂) := fun t _ => by
    obtain ⟨hre, hne⟩ := hvert t
    exact logDeriv_xiDeriv_eq hre hne
  -- integrability: continuity of each piece along each segment
  have hΓc : ∀ {s : ℂ}, 0 < s.re → ContinuousAt (logDeriv Complex.Gammaℝ) s := fun hs =>
    (Zeta23.RvM.logDeriv_Gammaℝ_differentiableOn.differentiableAt
      (Zeta23.RvM.isOpen_rightHalfPlane.mem_nhds hs)).continuousAt
  have hYc : ∀ {s : ℂ}, 0 < s.re → xiDeriv s ≠ 0 → ContinuousAt (logDeriv Yfn) s := fun hs hne =>
    continuousAt_logDeriv_of_analyticAt (Yfn_analyticAt hs) (fun h => hne ((Yfn_eq_zero_iff hs).mp h))
  have hintbΓ : ∀ (T : ℝ), GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ : ℂ) + T * I)) volume (1 / 2) 2 := by
    intro T hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨hre, _⟩ := hseg T hg σ hσ
    exact ((hΓc hre).comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (x := σ) (by fun_prop)).continuousWithinAt
  have hintbY : ∀ (T : ℝ), GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Yfn ((σ : ℂ) + T * I)) volume (1 / 2) 2 := by
    intro T hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨hre, hne⟩ := hseg T hg σ hσ
    exact ((hYc hre hne).comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (x := σ) (by fun_prop)).continuousWithinAt
  have hintrΓ : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((2 : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t _
    exact ((hΓc (hvert t).1).comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t) (by fun_prop)).continuousWithinAt
  have hintrY : IntervalIntegrable (fun t : ℝ => logDeriv Yfn ((2 : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t _
    exact ((hYc (hvert t).1 (hvert t).2).comp (f := fun t : ℝ => (2 : ℂ) + t * I) (x := t)
      (by fun_prop)).continuousWithinAt
  unfold halfContour
  rw [integral_congr keyb, integral_congr keyt, integral_congr keyr,
    integral_add (hintbΓ T₁ hg₁) (hintbY T₁ hg₁), integral_add (hintbΓ T₂ hg₂) (hintbY T₂ hg₂),
    integral_add hintrΓ hintrY]
  ring

/-! ### the Y′/Y part of the half-contour is O(log T) -/

theorem halfContour_Yfn_bound : ∃ C T₀ : ℝ, 0 < C ∧ 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ →
    GoodHeight T₁ → GoodHeight T₂ →
    |(halfContour (logDeriv Yfn) T₁ T₂).im|
      ≤ C * Real.log (|T₁| + 3) + 3 * Real.pi + C * Real.log (|T₂| + 3) := by
  obtain ⟨CH, tH, hCH, htH4, hH⟩ := horizontal_bound
  obtain ⟨tV, htV2, hV⟩ := vertical_bound
  refine ⟨CH, max tH tV, hCH, le_trans htH4 (le_max_left _ _), fun T₁ T₂ hT₁ h12 hg₁ hg₂ => ?_⟩
  have h1 := hH T₁ (le_trans (le_trans (le_max_left _ _) hT₁) (le_abs_self _)) hg₁
  have h2 := hH T₂ (le_trans (le_trans (le_max_left _ _) (hT₁.trans h12)) (le_abs_self _)) hg₂
  have h3 := hV T₁ T₂ (le_trans (le_max_right _ _) hT₁) h12
  unfold halfContour
  have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₁ * I))
      + (∫ t in T₁..T₂, logDeriv Yfn (2 + t * I)) * I
      - ∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₂ * I)).im
      = (∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₁ * I)).im
        + ((∫ t in T₁..T₂, logDeriv Yfn (2 + t * I)) * I).im
        - (∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₂ * I)).im := by
    simp [Complex.add_im, Complex.sub_im]
  rw [eim]
  have hmulI : ((∫ t in T₁..T₂, logDeriv Yfn (2 + t * I)) * I).im
      = (∫ t in T₁..T₂, logDeriv Yfn (2 + t * I) * I).im :=
    congrArg Complex.im (intervalIntegral.integral_mul_const (μ := volume) I
      (fun t : ℝ => logDeriv Yfn (2 + t * I))).symm
  rw [hmulI]
  calc |(∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₁ * I)).im
        + (∫ t in T₁..T₂, logDeriv Yfn (2 + t * I) * I).im
        - (∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₂ * I)).im|
      ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₁ * I)).im|
        + |(∫ t in T₁..T₂, logDeriv Yfn (2 + t * I) * I).im|
        + |(∫ σ in (1/2:ℝ)..2, logDeriv Yfn (σ + T₂ * I)).im| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ CH * Real.log (|T₁| + 3) + 3 * Real.pi + CH * Real.log (|T₂| + 3) := by linarith

/-! ### the main term -/

/-- **Riemann–von Mangoldt main term for ξ′**: |N_{ξ′}(T,2T) − (T/2π)ℓ₁(T)| ≤ C log T for T ≥ T₀
(instance of ZeroCount/GenericRvM.rvM_main_of: good heights, the argument principle + fold, the split
ξ″/ξ′ = Γℝ′/Γℝ + Y′/Y with the Y-part O(log T), and the local count). -/
theorem xiDeriv_rvM_main (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |((xiDerivZeros hF2 hs).N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  refine GenericRvM.rvM_main_of (xiDerivZeros hF2 hs) GoodHeight xiDeriv (a₀ := 0) le_rfl
    (fun a _ => exists_goodHeight hs a) (fun T₁ T₂ _ h12 hg₁ hg₂ => ?_) ?_ (xiDeriv_local_count hF2 hs)
  · rw [xiDerivZeros_N]
    exact Ncount_eq_im_halfContour hF2 hs h12 hg₁ hg₂
  · obtain ⟨CY, TY, hCY, -, hYb⟩ := halfContour_Yfn_bound
    refine ⟨CY, 3 * Real.pi, TY, hCY, by positivity, fun T₁ T₂ hT₁ h12 hg₁ hg₂ => ?_⟩
    rw [halfContour_xiDeriv_split hF2 hg₁ hg₂, Complex.add_im, add_sub_cancel_left]
    exact hYb T₁ T₂ hT₁ h12 hg₁ hg₂

end ZeroCount

/-- **H-RvM for the zeros of ξ′** ([XF′ (F3)], rendered as Zeta23.RiemannVonMangoldt for the ξ′ configuration):
both the main count N_{ξ′}(T,2T) = (T/2π)ℓ₁(T) + O(log T) and the two-sided local count. -/
theorem xiDeriv_riemannVonMangoldt (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) : XiDerivRvM hF2 hs :=
  ⟨ZeroCount.xiDeriv_rvM_main hF2 hs, ZeroCount.xiDeriv_local_count hF2 hs⟩

/-- the same, with the seam discharged: only (F2) remains as a hypothesis. -/
theorem xiDeriv_riemannVonMangoldt' (hF2 : XiDerivZerosInStrip) :
    RiemannVonMangoldt (xiDerivZeros hF2 (xiDerivSeam_of_strip hF2)) :=
  xiDeriv_riemannVonMangoldt hF2 (xiDerivSeam_of_strip hF2)

end XiPrime
end Zeta23
