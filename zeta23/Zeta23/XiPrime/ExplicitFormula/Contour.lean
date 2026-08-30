/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
(EF1) contour step, generic in the function f.

The weighted argument principle on the rectangle [1−c, c] × [−R, R] for an entire f whose zeros all
lie in the open vertical strip 1−c < Re s < c and which does not vanish on the two horizontal sides:
    (1/2πi) ∮ g · f′/f = Σ_{ρ : f ρ = 0, |Im ρ| < R} ord_ρ(f) · g(ρ).
No pole terms (contrast Zeta23.WeilEF.rectangle_identity for Λ, which has − H(0) − H(1)).
-/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.WeilEF.FullLineAssembly

noncomputable section

namespace Zeta23
namespace XiPrime

open Complex Topology Filter Set MeasureTheory
open Zeta23.WeilEF (Hfn)

/-- `H = Hfn k` is entire (paperFT of a compactly supported C² function). -/
theorem differentiable_Hfn {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Differentiable ℂ (Hfn k) := by
  unfold Hfn
  exact (Zeta23.WeilEF.differentiable_paperFT hk.continuous hkc).comp
    ((differentiable_id.sub_const _).div_const _)

/-- membership in the closed rectangle with corners (1−c) − iR and c + iR. -/
theorem mem_rectangle_iff {c R : ℝ} (hc : 1 - c ≤ c) (hR : 0 ≤ R) (s : ℂ) :
    s ∈ Rectangle (((1 - c : ℝ) : ℂ) - R * I) ((c : ℝ) + R * I) ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
  obtain ⟨e1, e2, e3, e4⟩ := Zeta23.WeilEF.corner_re_im c R
  simp only [Rectangle, Complex.mem_reProdIm, e1, e2, e3, e4, Set.uIcc_of_le hc,
    Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]

/-- **Generic rectangle identity.**  f, g entire; every zero of f has 1−c < Re < c (Zset = zero set);
f ≠ 0 on the horizontal lines Im s = ±R, 1−c ≤ Re s ≤ c.  Then the zeros of f with |Im| < R form a
finite set Z and (1/2πi)∮_{∂([1−c,c]×[−R,R])} g·f′/f = Σ_{ρ∈Z} ord_ρ(f)·g(ρ). -/
theorem rectangle_identity_of {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {c : ℝ} (hc : 1 - c < c) {Zset : Set ℂ} (hZ : ∀ s, f s = 0 ↔ s ∈ Zset)
    (hstrip : ∀ ρ ∈ Zset, 1 - c < ρ.re ∧ ρ.re < c) {R : ℝ} (hR : 0 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → f s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ Zset ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => g s * logDeriv f s)
          (((1 - c : ℝ) : ℂ) - R * I) ((c : ℝ) + R * I)
        = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  classical
  set z : ℂ := ((1 - c : ℝ) : ℂ) - R * I with hzdef
  set w : ℂ := (c : ℝ) + R * I with hwdef
  have hzre : z.re = 1 - c := by simp [hzdef]
  have hzim : z.im = -R := by simp [hzdef]
  have hwre : w.re = c := by simp [hwdef]
  have hwim : w.im = R := by simp [hwdef]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
    intro s
    simp only [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le (show (1 - c : ℝ) ≤ c by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  have hfA : AnalyticOnNhd ℂ f (Rectangle z w) := fun s _ => hf.analyticAt s
  have hgA : AnalyticOnNhd ℂ g (Rectangle z w) := fun s _ => hg.analyticAt s
  have hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0 := by
    intro s hs h0
    have hsrect := rectangleBorder_subset_rectangle z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood s (Or.inr h') hr1 hr2 h0
    · have h1 := (hstrip s ((hZ s).mp h0)).1
      rw [h'] at h1
      exact lt_irrefl _ h1
    · exact hgood s (Or.inl h') hr1 hr2 h0
    · have h1 := (hstrip s ((hZ s).mp h0)).2
      rw [h'] at h1
      exact lt_irrefl _ h1
  have hzB : z ∈ RectangleBorder z w := Or.inl (Or.inl (Or.inl ⟨Set.left_mem_uIcc, rfl⟩))
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hfA
    (rectangleBorder_subset_rectangle z w hzB) (hborder z hzB)
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmem : ∀ ρ, ρ ∈ Z ↔ ρ ∈ Rectangle z w ∧ f ρ = 0 := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
  have hZcoe : (Z : Set ℂ) = {ρ : ℂ | ρ ∈ Zset ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, hZmem, Set.mem_setOf_eq, hmem]
    constructor
    · rintro ⟨⟨⟨hr1, hr2⟩, hi1, hi2⟩, h0⟩
      have hρZ := (hZ ρ).mp h0
      refine ⟨hρZ, lt_of_le_of_ne hi1 ?_, lt_of_le_of_ne hi2 ?_⟩
      · intro h; exact hgood ρ (Or.inr h.symm) hr1 hr2 h0
      · intro h; exact hgood ρ (Or.inl h) hr1 hr2 h0
    · rintro ⟨hρZ, hi1, hi2⟩
      have h1 := hstrip ρ hρZ
      exact ⟨⟨⟨h1.1.le, h1.2.le⟩, hi1.le, hi2.le⟩, (hZ ρ).mpr hρZ⟩
  refine ⟨Z, hZcoe, ?_⟩
  refine Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hfA hgA hborder Z ?_ ?_
  · intro s hs
    rw [hZmem]
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  · intro ρ hρ
    exact ((hZmem ρ).mp hρ).1

/-- **Rectangle identity for ξ′** under (F2):  at a height R ≥ 0 where ξ′ ≠ 0 on Im s = ±R,
1−c ≤ Re s ≤ c (c > 1):  (1/2πi)∮ H·ξ″/ξ′ = Σ_{ξ′(ρ)=0, |Im ρ|<R} m_ρ H(ρ)  — no pole terms. -/
theorem rectangle_identity (hF2 : XiDerivZerosInStrip) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) {R : ℝ} (hR : 0 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → xiDeriv s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsXiDerivZero ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv xiDeriv s)
          (((1 - c : ℝ) : ℂ) - R * I) ((c : ℝ) + R * I)
        = ∑ ρ ∈ Z, (xiDerivMult ρ : ℂ) * Hfn k ρ :=
  rectangle_identity_of xiDeriv_differentiable (differentiable_Hfn hk hkc) (by linarith)
    (Zset := {ρ : ℂ | IsXiDerivZero ρ}) (fun _ => Iff.rfl)
    (fun ρ hρ => by
      have h := hF2 ρ hρ
      constructor <;> linarith [h.1, h.2])
    hR hgood

end XiPrime
end Zeta23
