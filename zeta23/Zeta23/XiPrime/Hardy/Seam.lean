/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/Seam.lean — the SEAM facts for W := ζ′ − ½(χ′/χ)ζ (W zero side).

Discharges `WSeam t₀` (Zeta23/XiPrime/Statement.lean §6) given t₀ > 0 and WZerosInStrip t₀:
  theorem wSeam_of_strip (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) : WSeam t₀
(the strip hypothesis is used ONLY for finite_window; one_le_mult / reflect_zero / mult_reflect hold for every
non-real zero: Hardy/Basic.lean's functional equation + Schwarz reflection, and W ≢ 0 on each half-plane by the
explicit points 2 ± it₁ of Hardy/TwoLine.lean).
-/
import Zeta23.XiPrime.Hardy.TwoLine
import Zeta23.Analytic.RectangleLogDeriv
import Mathlib.Analysis.Complex.Convex

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

/-- In this import closure typeclass search does not find `ContinuousSMul ℝ ℂ` on its own; the convexity lemmas below need it, so the instance is supplied explicitly. -/
local instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ :=
  ⟨((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd).congr fun p => by
    simp [Complex.real_smul]⟩

variable {t₀ : ℝ}

/-! ### W ≢ 0 near any non-real point -/

theorem analyticOrderAt_hardyW_ne_top {s : ℂ} (hs : s.im ≠ 0) : analyticOrderAt hardyW s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · -- lower half-plane
    have hU : IsPreconnected {z : ℂ | z.im < 0} := (convex_halfSpace_im_lt 0).isPreconnected
    have hall : EqOn hardyW 0 {z : ℂ | z.im < 0} :=
      (hardyW_analyticOnNhd.mono fun z (hz : z.im < 0) => hz.ne).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        hU hneg htop
    obtain ⟨z, hz, hne⟩ := exists_hardyW_ne_zero_lower
    exact hne (hall hz)
  · have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
    have hall : EqOn hardyW 0 {z : ℂ | 0 < z.im} :=
      (hardyW_analyticOnNhd.mono fun z (hz : 0 < z.im) => hz.ne').eqOn_zero_of_preconnected_of_eventuallyEq_zero
        hU hpos htop
    obtain ⟨z, hz, hne⟩ := exists_hardyW_ne_zero_upper
    exact hne (hall hz)

theorem wMult_cast {ρ : ℂ} (hρ : ρ.im ≠ 0) : (wMult ρ : ℕ∞) = analyticOrderAt hardyW ρ := by
  unfold wMult; exact ENat.coe_toNat (analyticOrderAt_hardyW_ne_top hρ)

theorem analyticOrderNatAt_hardyW (ρ : ℂ) : analyticOrderNatAt hardyW ρ = wMult ρ := rfl

/-- 1 ≤ m_ρ ↔ W(ρ) = 0, for non-real ρ. -/
theorem one_le_wMult_iff {ρ : ℂ} (hρ : ρ.im ≠ 0) : 1 ≤ wMult ρ ↔ hardyW ρ = 0 := by
  have ha := hardyW_analyticAt hρ
  have h0 : wMult ρ = 0 ↔ hardyW ρ ≠ 0 := by
    rw [← ha.analyticOrderAt_eq_zero, ← wMult_cast hρ]; norm_cast
  constructor
  · intro h; by_contra hne; have := h0.mpr hne; omega
  · intro h; by_contra hlt; exact (h0.mp (by omega)) h

/-! ### finiteness of height windows (uses the strip hypothesis) -/

/-- zeros of W with |Im| ≥ t₀ inside a compact height range are finite (in the half-strip [0,2] × [a,b], a ≥ t₀ > 0,
or its mirror image). -/
theorem finite_upper (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) (b : ℝ) :
    ({ρ | IsWZero ρ ∧ t₀ ≤ |ρ.im|} ∩ {ρ | 0 < ρ.im ∧ ρ.im ≤ b}).Finite := by
  obtain ⟨t₁, ht₁, hlow⟩ := hardyW_two_line_lower
  set M : ℝ := max b (max t₁ t₀) with hM
  set z : ℂ := (0 : ℂ) + (t₀ : ℝ) * I with hz
  set w : ℂ := (2 : ℂ) + (M : ℝ) * I with hw
  have hzre : z.re = 0 := by simp [hz]
  have hzim : z.im = t₀ := by simp [hz]
  have hwre : w.re = 2 := by simp [hw]
  have hwim : w.im = M := by simp [hw]
  have ht₀M : t₀ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmem : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → t₀ ≤ s.im → s.im ≤ M → s ∈ Rectangle z w := by
    intro s h1 h2 h3 h4
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim, uIcc_of_le (by norm_num : (0:ℝ) ≤ 2),
      uIcc_of_le ht₀M, mem_Icc]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hsub : Rectangle z w ⊆ {s : ℂ | s.im ≠ 0} := by
    intro s hs
    simp only [Rectangle, mem_reProdIm, hzim, hwim, uIcc_of_le ht₀M, mem_Icc] at hs
    exact fun h0 => by linarith [hs.2.1]
  have hx : (2 : ℂ) + (max t₁ t₀ : ℝ) * I ∈ Rectangle z w :=
    hmem _ (by simp) (by simp) (by simp) (by simp [hM])
  have hfx : hardyW ((2 : ℂ) + (max t₁ t₀ : ℝ) * I) ≠ 0 := by
    intro h0
    have := (hlow (max t₁ t₀) (by rw [abs_of_pos (by positivity)]; exact le_max_left _ _)).2
    rw [h0, norm_zero] at this; linarith
  have hfin := Zeta23.Analytic.finite_zeros_rectangle (hardyW_analyticOnNhd.mono hsub) hx hfx
  refine hfin.subset ?_
  rintro ρ ⟨⟨⟨hρ0, hρim⟩, hρt⟩, hpos, hle⟩
  have habs : |ρ.im| = ρ.im := abs_of_pos hpos
  obtain ⟨ha, hb⟩ := hZ ρ hρ0 hρt
  refine ⟨hmem ρ ha.le (by linarith) (by rw [← habs]; exact hρt) (le_trans hle (le_max_left _ _)), ?_⟩
  simpa using hρ0

theorem finite_lower (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) (a : ℝ) :
    ({ρ | IsWZero ρ ∧ t₀ ≤ |ρ.im|} ∩ {ρ | a ≤ ρ.im ∧ ρ.im < 0}).Finite := by
  -- the mirror image under conj of the upper set with b := −a
  have h := (finite_upper ht₀ hZ (-a)).image conj
  refine h.subset ?_
  rintro ρ ⟨⟨hρ, hρt⟩, ha, hneg⟩
  refine ⟨conj ρ, ⟨⟨?_, by simpa using hρt⟩, by simp; linarith, by simp; linarith⟩, Complex.conj_conj ρ⟩
  exact ⟨(hardyW_conj_eq_zero_iff hρ.2).mpr hρ.1, by simpa using hρ.2⟩

theorem finite_window_W (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) (T₁ T₂ : ℝ) :
    ({ρ | IsWZero ρ ∧ t₀ ≤ |ρ.im|} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  refine ((finite_upper ht₀ hZ T₂).union (finite_lower ht₀ hZ T₁)).subset ?_
  rintro ρ ⟨hρ, h1, h2⟩
  rcases lt_or_gt_of_ne hρ.1.2 with hneg | hpos
  · exact Or.inr ⟨hρ, h1.le, hneg⟩
  · exact Or.inl ⟨hρ, hpos, h2⟩

/-! ### the seam -/

/-- **The W seam**, given t₀ > 0 and the strip hypothesis (used only for finite_window). -/
theorem wSeam_of_strip {t₀ : ℝ} (ht₀ : 0 < t₀) (hZ : WZerosInStrip t₀) : WSeam t₀ where
  pos := ht₀
  one_le_mult := fun _ h _ => (one_le_wMult_iff h.2).mpr h.1
  reflect_zero := fun ρ h _ => (isWZero_reflect_iff ρ).mpr h
  mult_reflect := fun _ h _ => wMult_reflect h.2
  finite_window := finite_window_W ht₀ hZ

end Hardy

export Hardy (wSeam_of_strip)

end XiPrime
end Zeta23

end
