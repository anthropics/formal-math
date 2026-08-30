/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/Contour.lean — the argument principle for Ω = Γℝ·W on [−1,2]×[T₁,T₂] and the fold onto the
right half-contour. This is the function-specific part — zeros of Ω on the rectangle ↔ the W count; the fold itself is
the generic ZeroCount/GenericRvM.rectangleIntegral_eq_halfContour_of_fold instantiated at F := logDeriv Ω, valid for
heights T₁ ≥ t₀ > 0 where Ω is analytic and its zeros are W's with equal orders.
  N_W(T₁,T₂) = (1/π)·Im ∫_L Ω′/Ω,  L = [½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂]  (good heights t₀ ≤ T₁ ≤ T₂).
-/
import Zeta23.XiPrime.Hardy.Omega
import Zeta23.XiPrime.ZeroCount.GenericRvM

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

variable {t₀ : ℝ}

/-- T is a zero-free ordinate for W: no non-real zero of W has Im ρ = T. -/
def GoodHeightW (T : ℝ) : Prop := ∀ ρ : ℂ, IsWZero ρ → ρ.im ≠ T

/-- every unit interval [a, a+1] with a ≥ t₀ contains a good height. -/
theorem exists_goodHeightW (hs : WSeam t₀) {a : ℝ} (ha : t₀ ≤ a) : ∃ T ∈ Icc a (a + 1), GoodHeightW T := by
  have hsub : ({ρ | IsWZero ρ} ∩ {ρ | a < ρ.im ∧ ρ.im ≤ a + 1})
      ⊆ {ρ | IsWZero ρ ∧ t₀ ≤ |ρ.im|} ∩ {ρ | a < ρ.im ∧ ρ.im ≤ a + 1} := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨⟨hρ, by rw [abs_of_pos (by linarith [hs.pos])]; linarith⟩, h1, h2⟩
  have hfin : ((fun ρ : ℂ => ρ.im) '' ({ρ | IsWZero ρ} ∩ {ρ | a < ρ.im ∧ ρ.im ≤ a + 1})).Finite :=
    ((hs.finite_window a (a + 1)).subset hsub).image _
  have hinf : (Ioo a (a + 1)).Infinite := Ioo_infinite (by linarith)
  obtain ⟨T, hT, hTnot⟩ := (hinf.diff hfin).nonempty
  refine ⟨T, ⟨hT.1.le, hT.2.le⟩, ?_⟩
  intro ρ hρ him
  apply hTnot
  exact ⟨ρ, ⟨hρ, by rw [him]; exact hT.1, by rw [him]; exact hT.2.le⟩, him⟩

theorem goodHeightW_ne_zero {T : ℝ} (hT : T ≠ 0) (hg : GoodHeightW T) {s : ℂ} (hs : s.im = T) :
    hardyW s ≠ 0 := fun h => hg s ⟨h, by rw [hs]; exact hT⟩ hs

theorem goodHeightW_omegaW_ne_zero {T : ℝ} (hT : T ≠ 0) (hg : GoodHeightW T) {s : ℂ} (hs : s.im = T) :
    omegaW s ≠ 0 := fun h => goodHeightW_ne_zero hT hg hs ((omegaW_eq_zero_iff (by rw [hs]; exact hT)).mp h)

/-- **N_W(T₁,T₂) as a contour integral**: (1/2πi)∮_{∂([−1,2]×[T₁,T₂])} Ω′/Ω = NcountW T₁ T₂ for good heights
t₀ ≤ T₁ ≤ T₂ (all zeros there have 0 < Re < 1 by the strip hypothesis, so none sit on the vertical edges). -/
theorem rectangleIntegral'_logDeriv_omegaW_eq_NcountW (hZ : WZerosInStrip t₀) (hs : WSeam t₀)
    {T₁ T₂ : ℝ} (h0 : t₀ ≤ T₁) (hT : T₁ ≤ T₂) (hg₁ : GoodHeightW T₁) (hg₂ : GoodHeightW T₂) :
    RectangleIntegral' (logDeriv omegaW) (-1 + T₁ * I) (2 + T₂ * I) = (NcountW T₁ T₂ : ℂ) := by
  classical
  have ht₀ := hs.pos
  set z : ℂ := -1 + T₁ * I with hzdef
  set w : ℂ := 2 + T₂ * I with hwdef
  have hzre : z.re = -1 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔ (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num), uIcc_of_le hT, mem_Icc]
  have hoff : Rectangle z w ⊆ {s : ℂ | s.im ≠ 0} := fun s hsR => by
    have := ((hmem s).mp hsR).2.1; exact fun h => by rw [h] at this; linarith
  have hf : AnalyticOnNhd ℂ omegaW (Rectangle z w) := omegaW_analyticOnNhd hoff
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := hs.finite_window T₁ T₂
  have hZf : ∀ s ∈ Rectangle z w, omegaW s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hsR
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsR
    have hsim : s.im ≠ 0 := hoff hsR
    constructor
    · intro h0
      have hW0 := (omegaW_eq_zero_iff hsim).mp h0
      refine ⟨⟨⟨hW0, hsim⟩, by rw [abs_of_pos (by linarith)]; linarith⟩,
        lt_of_le_of_ne hi1 (fun h' => hg₁ s ⟨hW0, hsim⟩ h'.symm), hi2⟩
    · rintro ⟨⟨⟨hW0, -⟩, -⟩, _⟩
      exact (omegaW_eq_zero_iff hsim).mpr hW0
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hsZ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hsZ
    obtain ⟨⟨⟨h0, -⟩, ht⟩, hi1, hi2⟩ := hsZ
    obtain ⟨ha, hb⟩ := hZ s h0 ht
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, omegaW s ≠ 0 := by
    intro s hsB h0
    have hsR := rectangleBorder_subset_rectangle z w hsB
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsR
    have hsim : s.im ≠ 0 := hoff hsR
    have hW0 := (omegaW_eq_zero_iff hsim).mp h0
    obtain ⟨ha, hb⟩ := hZ s hW0 (by rw [abs_of_pos (by linarith)]; linarith)
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre, hwim] at hsB
    rcases hsB with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hg₁ s ⟨hW0, hsim⟩ h'
    · linarith
    · exact hg₂ s ⟨hW0, hsim⟩ h'
    · linarith
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder hfin.toFinset hZf hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv omegaW s) = logDeriv omegaW from rfl] at key
  rw [key]
  unfold NcountW
  have hset : zerosInW T₁ T₂ = {ρ | IsWZero ρ ∧ t₀ ≤ |ρ.im|} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ
    simp only [zerosInW, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨hρ, h1, h2⟩; exact ⟨⟨hρ, by rw [abs_of_pos (by linarith)]; linarith⟩, h1, h2⟩
    · rintro ⟨⟨hρ, -⟩, h1, h2⟩; exact ⟨hρ, h1, h2⟩
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  rw [analyticOrderNatAt_omegaW hρ.1.1.2]

/-! ### the fold -/

lemma continuous_logDeriv_omegaW_horizontal {T : ℝ} (hT : T ≠ 0) (hg : GoodHeightW T) :
    Continuous fun σ : ℝ => logDeriv omegaW (σ + T * I) := by
  refine continuous_iff_continuousAt.mpr fun σ => ?_
  have hne : omegaW (σ + T * I) ≠ 0 := goodHeightW_omegaW_ne_zero hT hg (by simp)
  have ha := omegaW_analyticAt (s := σ + T * I) (by simp [hT])
  have hc : ContinuousAt (logDeriv omegaW) (σ + T * I) := by
    have := (ha.deriv.continuousAt).div ha.continuousAt hne
    simpa only [logDeriv] using this
  exact hc.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)

/-- **the fold**: for good heights 0 < T₁ ≤ T₂, ∮ Ω′/Ω = 2i·Im(halfContour (Ω′/Ω) T₁ T₂)
(instance of ZeroCount/GenericRvM's rectangleIntegral_eq_halfContour_of_fold with F := logDeriv Ω). -/
theorem rectangleIntegral_logDeriv_omegaW_eq_halfContour {T₁ T₂ : ℝ} (h1 : 0 < T₁) (h12 : T₁ ≤ T₂)
    (hg₁ : GoodHeightW T₁) (hg₂ : GoodHeightW T₂) :
    RectangleIntegral (logDeriv omegaW) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((Zeta23.RvM.halfContour (logDeriv omegaW) T₁ T₂).im : ℂ) := by
  have hT₂ : 0 < T₂ := lt_of_lt_of_le h1 h12
  refine ZeroCount.GenericRvM.rectangleIntegral_eq_halfContour_of_fold
    (continuous_logDeriv_omegaW_horizontal h1.ne' hg₁) (continuous_logDeriv_omegaW_horizontal hT₂.ne' hg₂)
    (fun x _ => logDeriv_omegaW_one_sub_conj (by simp [h1.ne']))
    (fun x _ => logDeriv_omegaW_one_sub_conj (by simp [hT₂.ne']))
    (fun t ht => logDeriv_omegaW_one_sub_conj ?_)
  rw [uIcc_of_le h12] at ht
  simp; linarith [ht.1]

/-- **N_W(T₁,T₂) = (1/π)·Im ∫_L Ω′/Ω** for good heights t₀ ≤ T₁ ≤ T₂. -/
theorem NcountW_eq_im_halfContour (hZ : WZerosInStrip t₀) (hs : WSeam t₀) {T₁ T₂ : ℝ}
    (h0 : t₀ ≤ T₁) (h12 : T₁ ≤ T₂) (hg₁ : GoodHeightW T₁) (hg₂ : GoodHeightW T₂) :
    (NcountW T₁ T₂ : ℝ) = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv omegaW) T₁ T₂).im := by
  have h1 : 0 < T₁ := lt_of_lt_of_le hs.pos h0
  exact ZeroCount.GenericRvM.natCast_eq_im_halfContour
    (rectangleIntegral'_logDeriv_omegaW_eq_NcountW hZ hs h0 h12 hg₁ hg₂)
    (rectangleIntegral_logDeriv_omegaW_eq_halfContour h1 h12 hg₁ hg₂)

end Hardy
end XiPrime
end Zeta23

end
