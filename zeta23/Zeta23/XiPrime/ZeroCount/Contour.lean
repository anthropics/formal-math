/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/Contour.lean — the argument principle for ξ′ on [−1,2]×[T₁,T₂] and the fold onto the
right half-contour.  ξ′-analogue of Zeta23/RvM/CountByIntegral.lean + Zeta23/RvM/Fold.lean;
simpler than Λ there because ξ′ is ENTIRE and its symmetries ξ′(1−s) = −ξ′(s), ξ′(s̄) = conj ξ′(s) hold
everywhere, so logDeriv ξ′(1−s̄) = −conj logDeriv ξ′(s) at every s (Seam.lean).
  N_{ξ′}(T₁,T₂) = (1/π)·Im ∫_L ξ″/ξ′,  L = [½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂]  (good heights T₁ < T₂).
-/
import Zeta23.XiPrime.Seam
import Zeta23.RvM.Defs
import Zeta23.Analytic.RectangleLogDeriv
import Zeta23.XiPrime.ZeroCount.GenericRvM

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-- T is a zero-free ordinate for ξ′: no zero of ξ′ (any real part) has Im ρ = T. -/
def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsXiDerivZero ρ → ρ.im ≠ T

/-- every unit interval [a, a+1] contains a good height (finitely many ordinates per window). -/
theorem exists_goodHeight (hs : XiDerivSeam) (a : ℝ) : ∃ T ∈ Icc a (a + 1), GoodHeight T := by
  have hfin : ((fun ρ : ℂ => ρ.im) '' ({ρ | IsXiDerivZero ρ} ∩ {ρ | a < ρ.im ∧ ρ.im ≤ a + 1})).Finite :=
    (hs.finite_window a (a + 1)).image _
  have hinf : (Ioo a (a + 1)).Infinite := Ioo_infinite (by linarith)
  obtain ⟨T, hT, hTnot⟩ := (hinf.diff hfin).nonempty
  refine ⟨T, ⟨hT.1.le, hT.2.le⟩, ?_⟩
  intro ρ hρ him
  apply hTnot
  exact ⟨ρ, ⟨hρ, by rw [him]; exact hT.1, by rw [him]; exact hT.2.le⟩, him⟩

/-- a good height for two windows at once: T ∈ [a,a+1] avoiding the ordinates of all zeros. (same proof) -/
theorem goodHeight_xiDeriv_ne_zero {T : ℝ} (hg : GoodHeight T) {s : ℂ} (hs : s.im = T) : xiDeriv s ≠ 0 :=
  fun h => hg s h hs

/-- **N_{ξ′}(T₁,T₂) as a contour integral**: (1/2πi)∮_{∂([−1,2]×[T₁,T₂])} ξ″/ξ′ = Ncount T₁ T₂ for good
heights T₁ ≤ T₂ (all zeros have 0 < Re < 1 by (F2), so none sit on the vertical edges). -/
theorem rectangleIntegral'_logDeriv_xiDeriv_eq_Ncount (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    RectangleIntegral' (logDeriv xiDeriv) (-1 + T₁ * I) (2 + T₂ * I) = (Ncount T₁ T₂ : ℂ) := by
  classical
  set z : ℂ := -1 + T₁ * I with hzdef
  set w : ℂ := 2 + T₂ * I with hwdef
  have hzre : z.re = -1 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ xiDeriv (Rectangle z w) := xiDeriv_analyticOnNhd _
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := hs.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w, xiDeriv s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hsR
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsR
    constructor
    · intro h0
      exact ⟨h0, lt_of_le_of_ne hi1 (fun h' => hg₁ s h0 h'.symm), hi2⟩
    · rintro ⟨h0, _⟩
      exact h0
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hsZ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hsZ
    obtain ⟨h0, hi1, hi2⟩ := hsZ
    obtain ⟨ha, hb⟩ := hF2 s h0
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, xiDeriv s ≠ 0 := by
    intro s hsB h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp (rectangleBorder_subset_rectangle z w hsB)
    obtain ⟨ha, hb⟩ := hF2 s h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre,
      hwim] at hsB
    rcases hsB with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hg₁ s h0 h'
    · linarith
    · exact hg₂ s h0 h'
    · linarith
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder
    hfin.toFinset hZ hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv xiDeriv s) = logDeriv xiDeriv from rfl] at key
  rw [key]
  unfold Ncount
  have hset : zerosIn T₁ T₂ = {ρ | IsXiDerivZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ; simp [zerosIn]
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  rfl

/-! ### the fold -/

/-- logDeriv ξ′ is continuous along the whole horizontal line at a good height. -/
lemma continuous_logDeriv_xiDeriv_horizontal {T : ℝ} (hg : GoodHeight T) :
    Continuous fun σ : ℝ => logDeriv xiDeriv (σ + T * I) := by
  refine continuous_iff_continuousAt.mpr fun σ => ?_
  have hne : xiDeriv (σ + T * I) ≠ 0 := goodHeight_xiDeriv_ne_zero hg (by simp)
  have ha := xiDeriv_analyticAt (σ + T * I)
  have hc : ContinuousAt (logDeriv xiDeriv) (σ + T * I) := by
    have := (ha.deriv.continuousAt).div ha.continuousAt hne
    simpa only [logDeriv] using this
  exact hc.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)

/-- horizontal fold at a good height T: ∫_{−1}^{2} F(σ+iT)dσ = 2i·Im ∫_{1/2}^{2} F(σ+iT)dσ, F = ξ″/ξ′. -/
lemma horizontal_fold {T : ℝ} (hgood : GoodHeight T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv xiDeriv (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv xiDeriv (σ + T * I)).im : ℂ) :=
  GenericRvM.horizontal_fold_of T (continuous_logDeriv_xiDeriv_horizontal hgood)
    fun _ _ => logDeriv_xiDeriv_one_sub_conj _

/-- vertical fold: ∫_{T₁}^{T₂} F(−1+it)dt = −conj ∫_{T₁}^{T₂} F(2+it)dt. -/
lemma vertical_fold (T₁ T₂ : ℝ) :
    ∫ t in T₁..T₂, logDeriv xiDeriv (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv xiDeriv (2 + t * I)) :=
  GenericRvM.vertical_fold_of fun _ _ => logDeriv_xiDeriv_one_sub_conj _

/-- **the fold**: for good heights T₁ ≤ T₂,
∮_{∂([−1,2]×[T₁,T₂])} ξ″/ξ′ = 2i · Im(halfContour (ξ″/ξ′) T₁ T₂). -/
theorem rectangleIntegral_logDeriv_xiDeriv_eq_halfContour {T₁ T₂ : ℝ}
    (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    RectangleIntegral (logDeriv xiDeriv) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((Zeta23.RvM.halfContour (logDeriv xiDeriv) T₁ T₂).im : ℂ) :=
  GenericRvM.rectangleIntegral_eq_halfContour_of_fold
    (continuous_logDeriv_xiDeriv_horizontal hg₁) (continuous_logDeriv_xiDeriv_horizontal hg₂)
    (fun _ _ => logDeriv_xiDeriv_one_sub_conj _) (fun _ _ => logDeriv_xiDeriv_one_sub_conj _)
    (fun _ _ => logDeriv_xiDeriv_one_sub_conj _)

/-- **N_{ξ′}(T₁,T₂) = (1/π)·Im ∫_L ξ″/ξ′** for good heights T₁ ≤ T₂. -/
theorem Ncount_eq_im_halfContour (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) {T₁ T₂ : ℝ}
    (h12 : T₁ ≤ T₂) (hg₁ : GoodHeight T₁) (hg₂ : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv xiDeriv) T₁ T₂).im :=
  GenericRvM.natCast_eq_im_halfContour (rectangleIntegral'_logDeriv_xiDeriv_eq_Ncount hF2 hs h12 hg₁ hg₂)
    (rectangleIntegral_logDeriv_xiDeriv_eq_halfContour hg₁ hg₂)

end ZeroCount
end XiPrime
end Zeta23
