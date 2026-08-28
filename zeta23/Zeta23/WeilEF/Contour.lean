/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Contour.lean — The main contour: rectangle identity for H·Λ'/Λ,
horizontal vanishing along good heights, and the R → ∞ full-line identity.
Consumes: Zeta23.Analytic.rectangleIntegral'_mul_logDeriv_of_poles,
Zeta23.WeilEF.GoodHeights, differentiable_paperFT,
XiLogDeriv zeros/poles data, Mathlib completedRiemannZeta_residue_one /
completedHurwitzZetaEven_residue_zero.
-/
import Zeta23.WeilEF.VerticalLine
import Zeta23.WeilEF.GoodHeights
import Zeta23.Analytic.RectangleLogDeriv
import Zeta23.RvM.CountByIntegral
import Zeta23.Statement.SeamClosed

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set

/-- **Rectangle identity** at a zero-free height R: the weighted argument principle for
H·Λ'/Λ over [1−c, c] × [−R, R]: (1/2πi)∮ = Σ_{|γ_ρ| < R} m_ρ H(ρ) − H(0) − H(1)
(Λ's poles at 0 and 1 are simple with residues 1 and... sign handled by the −m·g(p) pole terms
with m = 1 at both). -/
theorem rectangle_identity {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {R : ℝ} (hR : 7 ≤ R)
    (hgood : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c →
      completedRiemannZeta s ≠ 0) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv completedRiemannZeta s)
          ((1 - c : ℝ) - R * I) ((c : ℝ) + R * I)
        = (∑ ρ ∈ Z, (zeroMult ρ : ℂ) * Hfn k ρ) - Hfn k 0 - Hfn k 1 := by
  classical
  set z : ℂ := (1 - c : ℝ) - R * I with hzdef
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
  set P : Finset ℂ := {0, 1} with hPdef
  have hfin := zetaSeam.finite_window (-R) R
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmemiff : ∀ ρ : ℂ, ρ ∈ Z ↔ (IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im ≤ R) := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  have hZcoe : (Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R} := by
    ext ρ
    rw [Finset.mem_coe, hZmemiff]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, lt_of_le_of_ne h3 ?_⟩
      intro h
      exact hgood ρ (Or.inl h) (by linarith [h1.2.1]) (by linarith [h1.2.2])
        ((Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos h1.2.1).mpr h1.1)
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.le⟩
  refine ⟨Z, hZcoe, ?_⟩
  have hZP : Disjoint Z P := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρP
    have h1 := ((hZmemiff ρ).mp hρ).1
    rw [hPdef] at hρP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρP
    rcases hρP with rfl | rfl
    · have h2 := h1.2.1
      rw [Complex.zero_re] at h2
      exact lt_irrefl _ h2
    · have h2 := h1.2.2
      rw [Complex.one_re] at h2
      exact lt_irrefl _ h2
  have hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him,
      hzre, hzim, hwre, hwim]
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · constructor
      · simp only [Complex.zero_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.zero_im, Set.mem_Ioo]
        constructor <;> linarith
    · constructor
      · simp only [Complex.one_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.one_im, Set.mem_Ioo]
        constructor <;> linarith
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w \ (P : Set ℂ)) := by
    rintro s ⟨_, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    exact Zeta23.RvM.analyticAt_completedRiemannZeta hsP.1 hsP.2
  have hg : AnalyticOnNhd ℂ (Hfn k) (Rectangle z w) := by
    intro s _
    have hdiff : Differentiable ℂ (Hfn k) := by
      unfold Hfn
      exact (differentiable_paperFT hk.continuous hkc).comp
        ((differentiable_id.sub_const _).div_const _)
    exact hdiff.analyticAt s
  have hborder : ∀ s ∈ RectangleBorder z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    have hsrect := rectangleBorder_subset_rectangle z w hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      hzre, hzim, hwre, hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood s (Or.inr h') hr1 hr2 h0
    · exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos (by rw [h']; linarith) h0
    · exact hgood s (Or.inl h') hr1 hr2 h0
    · exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_one_le_re (by rw [h']; linarith) h0
  have hZchar : ∀ s ∈ Rectangle z w \ (P : Set ℂ), (completedRiemannZeta s = 0 ↔ s ∈ Z) := by
    rintro s ⟨hsrect, hsP⟩
    rw [hPdef] at hsP
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hsP
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hsrect
    rw [hZmemiff]
    constructor
    · intro h0
      have hrepos : 0 < s.re := by
        by_contra hle
        exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos (by linarith) h0
      have hrelt : s.re < 1 := by
        by_contra hge
        exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_one_le_re (by linarith) h0
      have hnz : IsNontrivialZero s :=
        ⟨(Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos hrepos).mp h0, hrepos, hrelt⟩
      refine ⟨hnz, ?_, hi2⟩
      rcases lt_or_eq_of_le hi1 with h | h
      · exact h
      · exact absurd h0 (hgood s (Or.inr h.symm) hr1 hr2)
    · rintro ⟨h1, _, _⟩
      exact (Zeta23.RvM.completedRiemannZeta_eq_zero_iff_of_re_pos h1.2.1).mpr h1.1
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro ρ hρ
    rw [Finset.mem_coe, hZmemiff] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1.2.1], by linarith [h1.2.2]⟩, h2.le, h3⟩
  have hpole : ∀ p ∈ P, ∃ cp : ℂ, cp ≠ 0 ∧
      Filter.Tendsto (fun s => (s - p) ^ (1 : ℕ) * completedRiemannZeta s)
        (nhdsWithin p {p}ᶜ) (nhds cp) := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨-1, by norm_num, ?_⟩
      have h := HurwitzZeta.completedHurwitzZetaEven_residue_zero (0 : UnitAddCircle)
      norm_num at h
      refine h.congr (fun s => ?_)
      simp [completedRiemannZeta]
    · refine ⟨1, one_ne_zero, ?_⟩
      refine completedRiemannZeta_residue_one.congr (fun s => ?_)
      simp
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv_of_poles hre him Z P hZP hPint hf hg
    hborder hZchar hZsub (fun _ => 1) hpole
  rw [key]
  have hord : ∀ ρ ∈ Z, (analyticOrderNatAt completedRiemannZeta ρ : ℂ) = (zeroMult ρ : ℂ) := by
    intro ρ hρ
    have h1 := ((hZmemiff ρ).mp hρ).1
    rw [Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta h1.2.1
      (fun h' => by
        have h2 := h1.2.2
        rw [h', Complex.one_re] at h2
        exact lt_irrefl _ h2)]
  have hPsum : ∑ p ∈ P, ((1 : ℕ) : ℂ) * Hfn k p = Hfn k 0 + Hfn k 1 := by
    rw [hPdef, Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hord ρ hρ]), hPsum]
  ring

/- `full_line_identity` (the R → ∞ limit) lives in Zeta23/WeilEF/FullLine.lean,
which imports this file. -/

end WeilEF
end Zeta23
