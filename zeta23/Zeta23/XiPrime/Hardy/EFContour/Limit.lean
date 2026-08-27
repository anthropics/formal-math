/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The R → ∞ passage of the explicit-formula contour argument,
generic in the integrand.

The integrand 'logDeriv f' of an entire f replaced by an arbitrary F : ℂ → ℂ and the rectangle values replaced by a
given convergent sequence E_j → L: fold of the two verticals by the odd symmetry F(1−s) = −F(s) on the
line, vanishing of the horizontals from ‖H‖ ≤ C_H/(1+R²) (WeilEF.norm_Hfn_le) and an O(log²) bound for
F at the heights R_j ∈ [j+j₀, j+j₀+1], truncated → full integral by dominated convergence, and
uniqueness of limits.  Nothing about zeros, poles or good heights lives here (they enter only through
hE / hlim / hhor).
-/
import Zeta23.XiPrime.ExplicitFormula.FullLine

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy
namespace EFContour

open Complex Topology Filter Set MeasureTheory
open Zeta23.WeilEF (Hfn norm_Hfn_le continuous_Hfn_line one_sub_cast log_two_add_le)

variable {F : ℂ → ℂ} {k : ℝ → ℂ} {c : ℝ}

/-- the full-line integrand against an abstract F:  [H(c+it) + H(1−c−it)] · F(c+it). -/
def FlineF (F : ℂ → ℂ) (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * F ((c : ℂ) + t * I)

/-! ## Integrability of the full-line integrand -/

/-- **Integrability** of FlineF from continuity + a log bound for F on Re s = c (−1 ≤ c ≤ 2). -/
theorem integrable_FlineF_of (hFc : Continuous fun t : ℝ => F ((c : ℂ) + t * I))
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|))
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hc0 : -1 ≤ c) (hc2 : c ≤ 2) :
    Integrable (FlineF F k c) := by
  obtain ⟨C, hC0, hC⟩ := norm_weight_le hk hkc hc0 hc2
  obtain ⟨M, hM⟩ := hline
  have hM' : ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ max M 0 * Real.log (2 + |t|) := fun t =>
    (hM t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith [abs_nonneg t])))
  exact integrable_decay_mul_log (continuous_weight hk hkc c) hFc hC0 hC (le_max_right _ _) hM'

/-! ## The vertical sides -/

/-- Folding the left vertical side onto the right one by  F(1−s) = −F(s) on the line:
V(c; −R, R) − V(1−c; −R, R) = I • ∫_{−R}^{R} FlineF. -/
theorem verticals_eq_F (hFc : Continuous fun t : ℝ => F ((c : ℂ) + t * I))
    (hsymm : ∀ t : ℝ, F (1 - ((c : ℂ) + t * I)) = -F ((c : ℂ) + t * I))
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (R : ℝ) :
    VIntegral (fun s => Hfn k s * F s) c (-R) R
      - VIntegral (fun s => Hfn k s * F s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, FlineF F k c t := by
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := by
    have h := continuous_Hfn_line hk hkc (1 - c)
    have : (fun t : ℝ => Hfn k (1 - c - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp_apply, one_sub_cast]
    rw [this]; exact h.comp continuous_neg
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * F (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * F ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hs, hsymm]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * F ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hFc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * F ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hFc).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * F (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * F ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * F ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [FlineF]
  ring

/-! ## The horizontal sides -/

/-- **Horizontal sides vanish**: ‖H‖ ≤ C_H/(1+R_j²) on the segment and ‖F‖ ≤ K log²(j+j₀+3) there,
R_j ≥ j + j₀ ≥ 1, so  ‖HIntegral‖ ≤ (2c−1)·C_H·K·log²/(1+R_j²) → 0. -/
theorem horizontal_vanish_F (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hc : 1 - c ≤ c) (hc2 : c ≤ 2) {K : ℝ} (hK : 0 ≤ K) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + j₀ ≤ R j ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 - c ≤ s.re → s.re ≤ c →
        ‖F s‖ ≤ K * (Real.log ((j : ℝ) + j₀ + 3)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * F s) (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * F s) (1 - c) c (-(R j))) atTop (𝓝 0) := by
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  set n : ℕ → ℝ := fun j => (j : ℝ) + j₀ with hndef
  have hn1 : ∀ j, 1 ≤ n j := fun j => by
    have : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    simp only [hndef]; linarith
  set Lg : ℕ → ℝ := fun j => Real.log (n j + 3) with hLgdef
  have hLg_eq : ∀ j : ℕ, Real.log ((j : ℝ) + j₀ + 3) = Lg j := fun j => by simp only [hLgdef, hndef]
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * F s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hc] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    refine mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2])) ?_ (norm_nonneg _)
      (by positivity)
    rw [← hLg_eq]
    have hxre : ((x : ℂ) + y * I).re = x := by simp
    exact (hR j).2 ((x : ℂ) + y * I) (by rcases hy with h | h <;> simp [h])
      (by rw [hxre]; exact hx.1.le) (by rw [hxre]; exact hx.2)
  -- the majorant tends to 0
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb_le : ∀ j : ℕ, b j ≤ (CH * K * |c - (1 - c)|) * (Lg j ^ 2 / (1 * (n j + 3) + (-3))) := by
    intro j
    have hnR : n j ≤ R j := (hR j).1
    have hn0 : 0 < n j := by linarith [hn1 j]
    have hden : n j ≤ 1 + R j ^ 2 := by nlinarith [hnR, hn1 j]
    have e1 : (1 : ℝ) * (n j + 3) + (-3) = n j := by ring
    rw [e1]
    have h1 : Lg j ^ 2 / (1 + R j ^ 2) ≤ Lg j ^ 2 / n j :=
      div_le_div_of_nonneg_left (sq_nonneg _) hn0 hden
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by rw [hbdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hntop : Tendsto (fun j : ℕ => n j + 3) atTop atTop := by
    simp only [hndef]
    exact tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim0 : Tendsto (fun j : ℕ => Lg j ^ 2 / (1 * (n j + 3) + (-3))) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) 2 one_ne_zero).comp hntop
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim := hlim0.const_mul (CH * K * |c - (1 - c)|)
    rw [mul_zero] at hlim
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

/-! ## Assembly -/

/-- **Generic passage to the full line.**  If the normalised rectangle integrals of H·F over
[1−c, c] × [−R_j, R_j] have known values E_j → L, F is continuous with log growth on Re s = c, odd under
s ↦ 1−s between the two vertical lines, and O(log²) on the horizontal segments at the heights R_j ∈ [j+j₀, j+j₀+1],
then the full-line integral exists and (1/2π)∫[H(c+it)+H(1−c−it)]F(c+it)dt = L. -/
theorem full_line_of_rectangles {F : ℂ → ℂ} {k : ℝ → ℂ} {c : ℝ}
    (hc : 1 / 2 < c) (hc2 : c ≤ 2) (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hFc : Continuous fun t : ℝ => F ((c : ℂ) + t * I))
    (hsymm : ∀ t : ℝ, F (1 - ((c : ℂ) + t * I)) = -F ((c : ℂ) + t * I))
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|))
    {R : ℕ → ℝ} {j₀ : ℕ} (hj₀ : 1 ≤ j₀) {K : ℝ} (hK : 0 ≤ K)
    (hR : ∀ j : ℕ, (j : ℝ) + j₀ ≤ R j ∧ R j ≤ (j : ℝ) + j₀ + 1)
    (hhor : ∀ j : ℕ, ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 - c ≤ s.re → s.re ≤ c →
      ‖F s‖ ≤ K * (Real.log ((j : ℝ) + j₀ + 3)) ^ 2)
    {E : ℕ → ℂ} (hE : ∀ j : ℕ,
      RectangleIntegral' (fun s => Hfn k s * F s) (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I) = E j)
    {L : ℂ} (hlim : Tendsto E atTop (𝓝 L)) :
    Integrable (FlineF F k c) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * F ((c : ℂ) + t * I))
      = L := by
  have hcc : 1 - c < c := by linarith
  have hRge : ∀ j : ℕ, (j : ℝ) ≤ R j := fun j => by
    have := (hR j).1; have : (0:ℝ) ≤ j₀ := Nat.cast_nonneg j₀; linarith
  have hInt : Integrable (FlineF F k c) := integrable_FlineF_of hFc hline hk hkc (by linarith) hc2
  refine ⟨hInt, ?_⟩
  set G : ℂ → ℂ := fun s => Hfn k s * F s with hG
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish_F (F := F) hk hkc hcc.le hc2 hK hj₀ (R := R)
    (fun j => ⟨(hR j).1, hhor j⟩)
  have hV := tendsto_intervalIntegral_of_integrable hInt hRge
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' G (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral G (1 - c) c (-(R j)) - HIntegral G (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, FlineF F k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := Zeta23.WeilEF.corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq_F hFc hsymm hk hkc (R j)
    rw [hG]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, Zeta23.WeilEF.inv_two_pi_I_mul_I]
  -- rectangle_j → (1/2π) ∫ FlineF
  have hLHS : Tendsto (fun j : ℕ => RectangleIntegral' G (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, FlineF F k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  -- rectangle_j = E_j → L
  have hRHS : Tendsto (fun j : ℕ => RectangleIntegral' G (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 L) := hlim.congr fun j => (hE j).symm
  have huniq := tendsto_nhds_unique hLHS hRHS
  -- ∫ FlineF is literally the displayed integral
  exact huniq

end EFContour
end Hardy
end XiPrime
end Zeta23

end
