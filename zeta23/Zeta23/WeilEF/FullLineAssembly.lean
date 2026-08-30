/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/FullLineAssembly.lean — the R → ∞ assembly of
`full_line_identity` from: rectangle_identity (Contour), the majorant pack + heights +
vertical limits (FullLine), horizontal_vanish (Horizontal), zero_sum_limit (ZeroSumLimit).
-/
import Zeta23.WeilEF.FullLine
import Zeta23.WeilEF.Horizontal
import Zeta23.WeilEF.ZeroSumLimit

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory

/-- corners of the rectangle: real and imaginary parts. -/
theorem corner_re_im (c R : ℝ) :
    ((((1 - c : ℝ) : ℂ) - R * I).re = 1 - c) ∧ ((((1 - c : ℝ) : ℂ) - R * I).im = -R) ∧
    ((((c : ℝ) : ℂ) + R * I).re = c) ∧ ((((c : ℝ) : ℂ) + R * I).im = R) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- `(1/(2πi))·(i·X) = (1/2π)·X`. -/
theorem inv_two_pi_I_mul_I (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) = (1 / (2 * Real.pi) : ℂ) * X := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp

/-- **Full-line identity** (R → ∞ along good heights; horizontal pieces vanish by
good_heights + digamma growth + the 1/R² decay of H):
(1/2π)∫ [H(c+it) + H(1−c−it)]·Λ'/Λ(c+it) dt = Σ_ρ m_ρ H(ρ) − H(0) − H(1),
with the zero-side sum the (absolutely convergent) tsum over the carrier. -/
theorem full_line_identity (hs : ZetaSeam) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv completedRiemannZeta ((c:ℂ) + t * I)
      = (∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)
        - Hfn k 0 - Hfn k 1 := by
  obtain ⟨Cg, hCg, R, hR⟩ := good_heights
  set f : ℂ → ℂ := fun s => Hfn k s * logDeriv completedRiemannZeta s with hf
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = (∑ ρ ∈ Z, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hR j
    exact rectangle_identity hk hkc hc1 hc2 (R := R j) (by linarith)
      (completedZeta_ne_zero_on_horizontals hc1 hc2 (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish hk hkc hc1 hc2 hCg hR
  have hZlim := zero_sum_limit hs hk hkc (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := tendsto_interval_Fline hk hkc hc1 hc2 (R := R) (fun j => by linarith [(hR j).1])
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral f (1 - c) c (-(R j)) - HIntegral f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, Fline k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq hk hkc hc1 hc2 (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  -- RHS → Σ' − H0 − H1
  have hRt : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1)
      atTop (𝓝 ((∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)
        - Hfn k 0 - Hfn k 1)) :=
    (hZlim.sub_const _).sub_const _
  have hL' : Tendsto (fun j : ℕ => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline k c t)) :=
    hL.congr fun j => hE j
  have := tendsto_nhds_unique hL' hRt
  exact this

end WeilEF
end Zeta23
