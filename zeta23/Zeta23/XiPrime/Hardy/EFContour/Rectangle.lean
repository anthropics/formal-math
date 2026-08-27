/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFContour/Rectangle.lean — the rectangle identities at a fixed height R for the two W-integrands.

Rectangle Q := [1−c, c] × [−R, R], 1 < c ≤ 5/4, R > 0; z = (1−c) − iR, w = c + iR (the FullLine/Limit convention);
H = WeilEF.Hfn k (entire).  Every identity is the POLE-FREE weighted argument principle
Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (f analytic on Q, f ≠ 0 on ∂Q, zeros of f in Q listed) applied to:
  G := (Γℝ)⁻¹ (entire; zeros in Q: {0}, simple)                         ⇒ (1/2πi)∮ H·G′/G       = H(0)
  G∘(1−·)     (entire; zeros in Q: {1}, simple)                         ⇒ (1/2πi)∮ H·(G∘(1−·))′/… = H(1)
  q := s(s−1) (FullLine.mulSubOne; zeros 0,1 simple)                    ⇒                          H(0) + H(1)
  p := s(s−1)² (Poles.polarPoly; zeros 0 simple, 1 double)              ⇒                          H(0) + 2H(1)
  Wreg := p·W filled in at 0,1 (Poles.Wreg; analytic on Q; zeros = W's off {0,1}, same orders) ⇒ Σ_{W(ρ)=0} ord_ρ(W)·H(ρ)
and on ∂Q (no point of ∂Q is 0 or 1, and W ≠ 0 on ∂Q by hypothesis):
  Γℝ′/Γℝ = −G′/G,  (Γℝ′/Γℝ)(1−s) = (G∘(1−·))′/(G∘(1−·))(s),  L₂ = ½[Γℝ′/Γℝ(s) + Γℝ′/Γℝ(1−s)],  1/s + 1/(s−1) = q′/q,
  W′/W = Wreg′/Wreg − p′/p.  Hence
  rect_Lminus : (1/2πi)∮ H·(Lfn − L₂)   = ½(H(0) + H(1)),
  rect_FZ     : (1/2πi)∮ H·(L₂ + W′/W)  = Σ_{ρ∈Q, ρ∉{0,1}, W(ρ)=0} ord_ρ(W)·H(ρ) − (3/2)(H(0) + H(1)).
-/
import Zeta23.XiPrime.Hardy.EFContour.Poles
import Zeta23.XiPrime.ExplicitFormula.FullLine

open Complex Set Filter Topology MeasureTheory
open Zeta23.WeilEF (Hfn)

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy
namespace EFContour

variable {k : ℝ → ℂ} {c R : ℝ}

/-! ### §1. The rectangle: corners, membership, border -/

/-- lower-left corner (1−c) − iR. -/
def zc (c R : ℝ) : ℂ := ((1 - c : ℝ) : ℂ) - R * I
/-- upper-right corner c + iR. -/
def wc (c R : ℝ) : ℂ := (c : ℝ) + R * I

@[simp] lemma zc_re (c R : ℝ) : (zc c R).re = 1 - c := by simp [zc]
@[simp] lemma zc_im (c R : ℝ) : (zc c R).im = -R := by simp [zc]
@[simp] lemma wc_re (c R : ℝ) : (wc c R).re = c := by simp [wc]
@[simp] lemma wc_im (c R : ℝ) : (wc c R).im = R := by simp [wc]

lemma mem_rect_iff (hc : 1 - c ≤ c) (hR : 0 ≤ R) (s : ℂ) :
    s ∈ Rectangle (zc c R) (wc c R) ↔ (1 - c ≤ s.re ∧ s.re ≤ c) ∧ (-R ≤ s.im ∧ s.im ≤ R) := by
  simp only [Rectangle, Complex.mem_reProdIm, zc_re, zc_im, wc_re, wc_im, Set.uIcc_of_le hc,
    Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]

lemma border_cases {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) :
    s.re = 1 - c ∨ s.re = c ∨ s.im = -R ∨ s.im = R := by
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    zc_re, zc_im, wc_re, wc_im] at hs
  rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inl h'
  · exact Or.inr (Or.inr (Or.inr h'))
  · exact Or.inr (Or.inl h')

section Geometry
variable (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) (hR : 0 < R)
include hc1 hc2 hR

omit hR in
lemma zc_le_wc_re : (zc c R).re ≤ (wc c R).re := by simp; linarith
omit hc1 hc2 in
lemma zc_le_wc_im : (zc c R).im ≤ (wc c R).im := by simp; linarith

/-- points of the closed rectangle lie in the strip −2 < Re < 3. -/
lemma re_bounds_of_mem {s : ℂ} (hs : s ∈ Rectangle (zc c R) (wc c R)) : -2 < s.re ∧ s.re < 3 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := (mem_rect_iff (by linarith) hR.le s).mp hs
  exact ⟨by linarith, by linarith⟩

/-- 0 and 1 are interior points; no border point is 0 or 1. -/
lemma border_ne_zero_one {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) : s ≠ 0 ∧ s ≠ 1 := by
  rcases border_cases hs with h | h | h | h <;>
    refine ⟨fun e => ?_, fun e => ?_⟩ <;> (rw [e] at h; simp at h) <;> linarith

lemma mem_stripReg_of_border {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) : s ∈ stripReg := by
  obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
  obtain ⟨ha, hb⟩ := re_bounds_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs)
  exact ⟨ha, hb, h0, h1⟩

lemma zero_mem_rect : (0 : ℂ) ∈ Rectangle (zc c R) (wc c R) :=
  (mem_rect_iff (by linarith) hR.le 0).mpr ⟨⟨by simp; linarith, by simp; linarith⟩, by simp; linarith, by simp [hR.le]⟩

lemma one_mem_rect : (1 : ℂ) ∈ Rectangle (zc c R) (wc c R) :=
  (mem_rect_iff (by linarith) hR.le 1).mpr ⟨⟨by simp; linarith, by simp; linarith⟩, by simp; linarith, by simp [hR.le]⟩

lemma Gammaℝ_ne_zero_of_mem {s : ℂ} (hs : s ∈ Rectangle (zc c R) (wc c R)) (h0 : s ≠ 0) : Gammaℝ s ≠ 0 :=
  Gammaℝ_ne_zero_of_re (re_bounds_of_mem hc1 hc2 hR hs).1 h0

lemma Gammaℝ_one_sub_ne_zero_of_mem {s : ℂ} (hs : s ∈ Rectangle (zc c R) (wc c R)) (h1 : s ≠ 1) :
    Gammaℝ (1 - s) ≠ 0 :=
  Gammaℝ_one_sub_ne_zero_of_re (re_bounds_of_mem hc1 hc2 hR hs).2 h1

end Geometry

/-! ### §2. The four explicit pieces -/

variable (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) (hR : 0 < R)
include hk hkc hc1 hc2 hR

omit hc1 hc2 hR in
lemma Hfn_analyticOnNhd (U : Set ℂ) : AnalyticOnNhd ℂ (Hfn k) U := fun s _ => (differentiable_Hfn hk hkc).analyticAt s

/-- (a) (1/2πi)∮ H·G′/G = H(0). -/
theorem rect_invGammaℝ :
    RectangleIntegral' (fun s => Hfn k s * logDeriv invGammaℝ s) (zc c R) (wc c R) = Hfn k 0 := by
  classical
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (zc_le_wc_re hc1 hc2) (zc_le_wc_im hR)
    (f := invGammaℝ) (g := Hfn k) (fun s _ => analyticAt_invGammaℝ s) (Hfn_analyticOnNhd hk hkc _)
    (fun s hs => invGammaℝ_ne_zero_iff.mpr
      (Gammaℝ_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs) (border_ne_zero_one hc1 hc2 hR hs).1))
    {0} (fun s hs => by
      rw [Finset.mem_singleton, invGammaℝ_eq_zero_iff]
      constructor
      · intro h; by_contra h0; exact Gammaℝ_ne_zero_of_mem hc1 hc2 hR hs h0 h
      · rintro rfl; simp [Gammaℝ_eq_zero_iff])
    (by simpa using zero_mem_rect hc1 hc2 hR)
  rw [key, Finset.sum_singleton, analyticOrderNatAt_invGammaℝ_zero]
  simp

/-- (b) (1/2πi)∮ H·(G∘(1−·))′/(G∘(1−·)) = H(1). -/
theorem rect_invGammaℝ_one_sub :
    RectangleIntegral' (fun s => Hfn k s * logDeriv (fun z => invGammaℝ (1 - z)) s) (zc c R) (wc c R) = Hfn k 1 := by
  classical
  have han : ∀ s : ℂ, AnalyticAt ℂ (fun z => invGammaℝ (1 - z)) s := fun s =>
    (analyticAt_invGammaℝ _).comp (analyticAt_const.sub analyticAt_id)
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (zc_le_wc_re hc1 hc2) (zc_le_wc_im hR)
    (f := fun z => invGammaℝ (1 - z)) (g := Hfn k) (fun s _ => han s) (Hfn_analyticOnNhd hk hkc _)
    (fun s hs => invGammaℝ_ne_zero_iff.mpr
      (Gammaℝ_one_sub_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs)
        (border_ne_zero_one hc1 hc2 hR hs).2))
    {1} (fun s hs => by
      rw [Finset.mem_singleton, invGammaℝ_eq_zero_iff]
      constructor
      · intro h; by_contra h1; exact Gammaℝ_one_sub_ne_zero_of_mem hc1 hc2 hR hs h1 h
      · rintro rfl; simp [Gammaℝ_eq_zero_iff])
    (by simpa using one_mem_rect hc1 hc2 hR)
  rw [key, Finset.sum_singleton, analyticOrderNatAt_invGammaℝ_one_sub_one]
  simp

/-- (c) (1/2πi)∮ H·q′/q = H(0) + H(1), q = s(s−1). -/
theorem rect_mulSubOne :
    RectangleIntegral' (fun s => Hfn k s * logDeriv mulSubOne s) (zc c R) (wc c R) = Hfn k 0 + Hfn k 1 := by
  classical
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (zc_le_wc_re hc1 hc2) (zc_le_wc_im hR)
    (f := mulSubOne) (g := Hfn k) (fun s _ => differentiable_mulSubOne.analyticAt s)
    (Hfn_analyticOnNhd hk hkc _)
    (fun s hs => by
      obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
      rw [Ne, mulSubOne_eq_zero_iff]; simp [h0, h1])
    {0, 1} (fun s _ => by rw [mulSubOne_eq_zero_iff]; simp)
    (by
      intro s hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact zero_mem_rect hc1 hc2 hR
      · exact one_mem_rect hc1 hc2 hR)
  rw [key, Finset.sum_insert (by simp), Finset.sum_singleton, analyticOrderNatAt_mulSubOne_zero,
    analyticOrderNatAt_mulSubOne_one]
  simp

/-! #### the polar polynomial p = q · (s−1) -/

omit hk hkc hc1 hc2 hR in
/-- s ↦ s − 1. -/
lemma differentiable_subOne : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop

/-- the second factor, as a named function to keep elaboration syntactic. -/
def subOne (s : ℂ) : ℂ := s - 1

omit hk hkc hc1 hc2 hR in
lemma differentiable_subOne' : Differentiable ℂ subOne := by unfold subOne; fun_prop

omit hk hkc hc1 hc2 hR in
lemma polarPoly_eq_mul : polarPoly = mulSubOne * subOne := by
  funext s; simp only [Pi.mul_apply, polarPoly, mulSubOne, subOne]; ring

omit hk hkc hc1 hc2 hR in
lemma analyticOrderAt_subOne_zero : analyticOrderAt subOne 0 = 0 :=
  (differentiable_subOne'.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp [subOne])

omit hk hkc hc1 hc2 hR in
lemma analyticOrderAt_subOne_one : analyticOrderAt subOne 1 = (1 : ℕ) := by
  rw [(differentiable_subOne'.analyticAt 1).analyticOrderAt_eq_natCast]
  exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z => by simp [subOne]⟩

omit hk hkc hc1 hc2 hR in
/-- from a (nonzero) natural order back to the ℕ∞ order. -/
lemma analyticOrderAt_of_nat {f : ℂ → ℂ} {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : analyticOrderNatAt f z = n) :
    analyticOrderAt f z = n := by
  have hne : analyticOrderAt f z ≠ ⊤ := by
    intro ht; rw [analyticOrderNatAt, ht] at h; simp at h; exact hn h.symm
  rw [← ENat.coe_toNat hne]
  unfold analyticOrderNatAt at h
  rw [h]

omit hk hkc hc1 hc2 hR in
lemma differentiable_polarPoly : Differentiable ℂ polarPoly := by
  unfold polarPoly; fun_prop

omit hk hkc hc1 hc2 hR in
lemma polarPoly_eq_zero_iff (s : ℂ) : polarPoly s = 0 ↔ s = 0 ∨ s = 1 := by
  rw [polarPoly, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

omit hk hkc hc1 hc2 hR in
lemma analyticOrderNatAt_polarPoly_zero : analyticOrderNatAt polarPoly 0 = 1 := by
  unfold analyticOrderNatAt
  rw [polarPoly_eq_mul, analyticOrderAt_mul (differentiable_mulSubOne.analyticAt 0) (differentiable_subOne'.analyticAt 0),
    analyticOrderAt_subOne_zero, add_zero, analyticOrderAt_of_nat one_ne_zero analyticOrderNatAt_mulSubOne_zero]
  rfl

omit hk hkc hc1 hc2 hR in
lemma analyticOrderNatAt_polarPoly_one : analyticOrderNatAt polarPoly 1 = 2 := by
  unfold analyticOrderNatAt
  rw [polarPoly_eq_mul, analyticOrderAt_mul (differentiable_mulSubOne.analyticAt 1) (differentiable_subOne'.analyticAt 1),
    analyticOrderAt_subOne_one, analyticOrderAt_of_nat one_ne_zero analyticOrderNatAt_mulSubOne_one]
  rfl

/-- (d) (1/2πi)∮ H·p′/p = H(0) + 2·H(1). -/
theorem rect_polarPoly :
    RectangleIntegral' (fun s => Hfn k s * logDeriv polarPoly s) (zc c R) (wc c R) = Hfn k 0 + 2 * Hfn k 1 := by
  classical
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (zc_le_wc_re hc1 hc2) (zc_le_wc_im hR)
    (f := polarPoly) (g := Hfn k) (fun s _ => differentiable_polarPoly.analyticAt s)
    (Hfn_analyticOnNhd hk hkc _)
    (fun s hs => by
      obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
      rw [Ne, polarPoly_eq_zero_iff]; simp [h0, h1])
    {0, 1} (fun s _ => by rw [polarPoly_eq_zero_iff]; simp)
    (by
      intro s hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact zero_mem_rect hc1 hc2 hR
      · exact one_mem_rect hc1 hc2 hR)
  rw [key, Finset.sum_insert (by simp), Finset.sum_singleton, analyticOrderNatAt_polarPoly_zero,
    analyticOrderNatAt_polarPoly_one]
  push_cast; ring

/-! ### §3. The W piece -/

/-- (e) (1/2πi)∮ H·Wreg′/Wreg = Σ_{ρ ∈ Q, ρ ∉ {0,1}, W(ρ)=0} ord_ρ(W)·H(ρ), provided W ≠ 0 on ∂Q. -/
theorem rect_Wreg (hW : ∀ s ∈ RectangleBorder (zc c R) (wc c R), hardyW s ≠ 0) :
    ∃ Z : Finset ℂ, ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ Rectangle (zc c R) (wc c R) ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ hardyW ρ = 0}) ∧
      RectangleIntegral' (fun s => Hfn k s * logDeriv Wreg s) (zc c R) (wc c R)
        = ∑ ρ ∈ Z, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ := by
  classical
  have hre := zc_le_wc_re (R := R) hc1 hc2
  have him := zc_le_wc_im (c := c) hR
  have hfA : AnalyticOnNhd ℂ Wreg (Rectangle (zc c R) (wc c R)) := fun s hs =>
    Wreg_analyticAt (re_bounds_of_mem hc1 hc2 hR hs).1 (re_bounds_of_mem hc1 hc2 hR hs).2
  -- membership in stripReg for non-polar rectangle points
  have hreg : ∀ s ∈ Rectangle (zc c R) (wc c R), s ≠ 0 → s ≠ 1 → s ∈ stripReg := fun s hs h0 h1 =>
    ⟨(re_bounds_of_mem hc1 hc2 hR hs).1, (re_bounds_of_mem hc1 hc2 hR hs).2, h0, h1⟩
  have hborder : ∀ s ∈ RectangleBorder (zc c R) (wc c R), Wreg s ≠ 0 := by
    intro s hs
    obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
    rw [Ne, Wreg_eq_zero_iff (hreg s (rectangleBorder_subset_rectangle _ _ hs) h0 h1)]
    exact hW s hs
  have hzB : zc c R ∈ RectangleBorder (zc c R) (wc c R) := Or.inl (Or.inl (Or.inl ⟨Set.left_mem_uIcc, rfl⟩))
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hfA (rectangleBorder_subset_rectangle _ _ hzB) (hborder _ hzB)
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmem : ∀ ρ, ρ ∈ Z ↔ ρ ∈ Rectangle (zc c R) (wc c R) ∧ Wreg ρ = 0 := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  -- zeros of Wreg in Q are exactly W's zeros off {0,1}
  have hchar : ∀ ρ, ρ ∈ Rectangle (zc c R) (wc c R) →
      (Wreg ρ = 0 ↔ ρ ≠ 0 ∧ ρ ≠ 1 ∧ hardyW ρ = 0) := by
    intro ρ hρ
    constructor
    · intro h
      have h0 : ρ ≠ 0 := by rintro rfl; rw [Wreg_zero] at h; norm_num at h
      have h1 : ρ ≠ 1 := by rintro rfl; rw [Wreg_one] at h; norm_num at h
      exact ⟨h0, h1, (Wreg_eq_zero_iff (hreg ρ hρ h0 h1)).mp h⟩
    · rintro ⟨h0, h1, h⟩
      exact (Wreg_eq_zero_iff (hreg ρ hρ h0 h1)).mpr h
  refine ⟨Z, ?_, ?_⟩
  · ext ρ
    rw [Finset.mem_coe, hZmem, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hρ, h⟩; exact ⟨hρ, (hchar ρ hρ).mp h⟩
    · rintro ⟨hρ, h⟩; exact ⟨hρ, (hchar ρ hρ).mpr h⟩
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hfA (Hfn_analyticOnNhd hk hkc _)
    hborder Z (fun s hs => by rw [hZmem]; exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩)
    (fun ρ hρ => ((hZmem ρ).mp hρ).1)
  rw [key]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  obtain ⟨hρQ, hρ0⟩ := (hZmem ρ).mp hρ
  obtain ⟨h0, h1, -⟩ := (hchar ρ hρQ).mp hρ0
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_Wreg (hreg ρ hρQ h0 h1)]

/-! ### §4. The border identities and linear combination -/

omit hk hkc in
/-- on ∂Q:  L₂ = ½ (G∘(1−·))′/(G∘(1−·)) − ½ G′/G. -/
lemma L2_border {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) :
    L2 s = (1 / 2 : ℂ) * logDeriv (fun z => invGammaℝ (1 - z)) s - (1 / 2 : ℂ) * logDeriv invGammaℝ s := by
  obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
  have hsQ := rectangleBorder_subset_rectangle _ _ hs
  have hG0 := Gammaℝ_ne_zero_of_mem hc1 hc2 hR hsQ h0
  have hG1 := Gammaℝ_one_sub_ne_zero_of_mem hc1 hc2 hR hsQ h1
  rw [L2, logDeriv_chiFE_eq hG1 hG0, logDeriv_Gammaℝ_one_sub_eq hG1]
  ring

omit hk hkc in
/-- on ∂Q:  Lfn − L₂ = −½ G′/G − ½ (G∘(1−·))′/(G∘(1−·)) + q′/q. -/
lemma Lminus_border {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) :
    Lfn s - L2 s = -(1 / 2 : ℂ) * logDeriv invGammaℝ s - (1 / 2 : ℂ) * logDeriv (fun z => invGammaℝ (1 - z)) s
      + logDeriv mulSubOne s := by
  obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
  have hsQ := rectangleBorder_subset_rectangle _ _ hs
  have hG0 := Gammaℝ_ne_zero_of_mem hc1 hc2 hR hsQ h0
  rw [L2_border hc1 hc2 hR hs, Lfn, logDeriv_Gammaℝ_eq_neg hG0, logDeriv_mulSubOne_eq h0 h1]
  ring

omit hk hkc in
/-- on ∂Q (W ≠ 0 there):  L₂ + W′/W = ½ (G∘(1−·))′/… − ½ G′/G + Wreg′/Wreg − p′/p. -/
lemma FZ_border (hW : ∀ s ∈ RectangleBorder (zc c R) (wc c R), hardyW s ≠ 0)
    {s : ℂ} (hs : s ∈ RectangleBorder (zc c R) (wc c R)) :
    L2 s + logDeriv hardyW s = (1 / 2 : ℂ) * logDeriv (fun z => invGammaℝ (1 - z)) s
      - (1 / 2 : ℂ) * logDeriv invGammaℝ s + logDeriv Wreg s - logDeriv polarPoly s := by
  rw [L2_border hc1 hc2 hR hs, logDeriv_Wreg (mem_stripReg_of_border hc1 hc2 hR hs) (hW s hs)]
  ring

omit hc1 hc2 hR in
/-- H·φ is integrable along ∂Q when φ is continuous at every border point. -/
lemma borderIntegrable_of_continuousOn {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (RectangleBorder (zc c R) (wc c R))) :
    RectangleBorderIntegrable (fun s => Hfn k s * φ s) (zc c R) (wc c R) :=
  ((differentiable_Hfn hk hkc).continuous.continuousOn.mul hφ).rectangleBorder_integrable

omit hk hkc hc1 hc2 hR in
/-- logDeriv f is continuous on ∂Q when f is analytic and nonzero at every border point. -/
lemma continuousOn_logDeriv_border {f : ℂ → ℂ} (hf : ∀ s ∈ RectangleBorder (zc c R) (wc c R), AnalyticAt ℂ f s)
    (hne : ∀ s ∈ RectangleBorder (zc c R) (wc c R), f s ≠ 0) :
    ContinuousOn (logDeriv f) (RectangleBorder (zc c R) (wc c R)) := by
  intro s hs
  have ha := hf s hs
  exact (ha.deriv.continuousAt.div ha.continuousAt (hne s hs)).continuousWithinAt

omit hk hkc hc1 hc2 hR in
/-- linearity of the normalised rectangle integral in the test integrand (four-term form). -/
lemma rect'_lincomb {z w : ℂ} {φ₁ φ₂ φ₃ φ₄ : ℂ → ℂ} (a₁ a₂ a₃ a₄ : ℂ)
    (h₁ : RectangleBorderIntegrable (fun s => Hfn k s * φ₁ s) z w)
    (h₂ : RectangleBorderIntegrable (fun s => Hfn k s * φ₂ s) z w)
    (h₃ : RectangleBorderIntegrable (fun s => Hfn k s * φ₃ s) z w)
    (h₄ : RectangleBorderIntegrable (fun s => Hfn k s * φ₄ s) z w) :
    RectangleIntegral' (fun s => Hfn k s * (a₁ * φ₁ s + a₂ * φ₂ s + a₃ * φ₃ s + a₄ * φ₄ s)) z w
      = a₁ * RectangleIntegral' (fun s => Hfn k s * φ₁ s) z w + a₂ * RectangleIntegral' (fun s => Hfn k s * φ₂ s) z w
        + a₃ * RectangleIntegral' (fun s => Hfn k s * φ₃ s) z w + a₄ * RectangleIntegral' (fun s => Hfn k s * φ₄ s) z w := by
  -- scalar multiples are border-integrable
  have hsm : ∀ (a : ℂ) (φ : ℂ → ℂ), RectangleBorderIntegrable (fun s => Hfn k s * φ s) z w →
      RectangleBorderIntegrable (fun s => a • (Hfn k s * φ s)) z w := by
    intro a φ h
    exact ⟨h.1.smul a, h.2.1.smul a, h.2.2.1.smul a, h.2.2.2.smul a⟩
  have e : (fun s => Hfn k s * (a₁ * φ₁ s + a₂ * φ₂ s + a₃ * φ₃ s + a₄ * φ₄ s))
      = (((fun s => a₁ • (Hfn k s * φ₁ s)) + (fun s => a₂ • (Hfn k s * φ₂ s)))
          + (fun s => a₃ • (Hfn k s * φ₃ s))) + (fun s => a₄ • (Hfn k s * φ₄ s)) := by
    funext s; simp only [Pi.add_apply, smul_eq_mul]; ring
  have hadd12 : RectangleBorderIntegrable ((fun s => a₁ • (Hfn k s * φ₁ s)) + (fun s => a₂ • (Hfn k s * φ₂ s))) z w := by
    obtain ⟨b1, b2, b3, b4⟩ := hsm a₁ φ₁ h₁; obtain ⟨c1, c2, c3, c4⟩ := hsm a₂ φ₂ h₂
    exact ⟨b1.add c1, b2.add c2, b3.add c3, b4.add c4⟩
  have hadd123 : RectangleBorderIntegrable (((fun s => a₁ • (Hfn k s * φ₁ s)) + (fun s => a₂ • (Hfn k s * φ₂ s)))
      + (fun s => a₃ • (Hfn k s * φ₃ s))) z w := by
    obtain ⟨b1, b2, b3, b4⟩ := hadd12; obtain ⟨c1, c2, c3, c4⟩ := hsm a₃ φ₃ h₃
    exact ⟨b1.add c1, b2.add c2, b3.add c3, b4.add c4⟩
  rw [e, RectangleIntegral', RectangleBorderIntegrable.add hadd123 (hsm a₄ φ₄ h₄),
    RectangleBorderIntegrable.add hadd12 (hsm a₃ φ₃ h₃), RectangleBorderIntegrable.add (hsm a₁ φ₁ h₁) (hsm a₂ φ₂ h₂),
    RectangleIntegral.const_smul, RectangleIntegral.const_smul, RectangleIntegral.const_smul,
    RectangleIntegral.const_smul]
  simp only [RectangleIntegral', smul_eq_mul]
  ring

/-- **(1/2πi)∮ H·(Lfn − L₂) = ½(H(0) + H(1)).** -/
theorem rect_Lminus :
    RectangleIntegral' (fun s => Hfn k s * (Lfn s - L2 s)) (zc c R) (wc c R) = (1 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) := by
  have hb0 : ∀ s ∈ RectangleBorder (zc c R) (wc c R), Gammaℝ s ≠ 0 := fun s hs =>
    Gammaℝ_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs) (border_ne_zero_one hc1 hc2 hR hs).1
  have hb1 : ∀ s ∈ RectangleBorder (zc c R) (wc c R), Gammaℝ (1 - s) ≠ 0 := fun s hs =>
    Gammaℝ_one_sub_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs) (border_ne_zero_one hc1 hc2 hR hs).2
  have hcongr : Set.EqOn (fun s => Hfn k s * (Lfn s - L2 s))
      (fun s => Hfn k s * ((-(1/2:ℂ)) * logDeriv invGammaℝ s + (-(1/2:ℂ)) * logDeriv (fun z => invGammaℝ (1 - z)) s
        + (1:ℂ) * logDeriv mulSubOne s + (0:ℂ) * logDeriv mulSubOne s)) (RectangleBorder (zc c R) (wc c R)) := by
    intro s hs
    simp only
    rw [Lminus_border hc1 hc2 hR hs]; ring
  have hI1 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (fun s _ => analyticAt_invGammaℝ s) (fun s hs => invGammaℝ_ne_zero_iff.mpr (hb0 s hs)))
  have hI2 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (f := fun z => invGammaℝ (1 - z))
      (fun s _ => (analyticAt_invGammaℝ _).comp (analyticAt_const.sub analyticAt_id))
      (fun s hs => invGammaℝ_ne_zero_iff.mpr (hb1 s hs)))
  have hI3 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (f := mulSubOne) (fun s _ => differentiable_mulSubOne.analyticAt s)
      (fun s hs => by
        obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
        rw [Ne, mulSubOne_eq_zero_iff]; simp [h0, h1]))
  rw [RectangleIntegral'_congr hcongr, rect'_lincomb _ _ _ _ hI1 hI2 hI3 hI3,
    rect_invGammaℝ hk hkc hc1 hc2 hR, rect_invGammaℝ_one_sub hk hkc hc1 hc2 hR, rect_mulSubOne hk hkc hc1 hc2 hR]
  ring

/-- **(1/2πi)∮ H·(L₂ + W′/W) = Σ_{W(ρ)=0 in Q, ρ ∉ {0,1}} ord_ρ(W)·H(ρ) − (3/2)(H(0) + H(1))**, if W ≠ 0 on ∂Q. -/
theorem rect_FZ (hW : ∀ s ∈ RectangleBorder (zc c R) (wc c R), hardyW s ≠ 0) :
    ∃ Z : Finset ℂ, ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ Rectangle (zc c R) (wc c R) ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ hardyW ρ = 0}) ∧
      RectangleIntegral' (fun s => Hfn k s * (L2 s + logDeriv hardyW s)) (zc c R) (wc c R)
        = (∑ ρ ∈ Z, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) := by
  obtain ⟨Z, hZ, hE⟩ := rect_Wreg hk hkc hc1 hc2 hR hW
  refine ⟨Z, hZ, ?_⟩
  have hb0 : ∀ s ∈ RectangleBorder (zc c R) (wc c R), Gammaℝ s ≠ 0 := fun s hs =>
    Gammaℝ_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs) (border_ne_zero_one hc1 hc2 hR hs).1
  have hb1 : ∀ s ∈ RectangleBorder (zc c R) (wc c R), Gammaℝ (1 - s) ≠ 0 := fun s hs =>
    Gammaℝ_one_sub_ne_zero_of_mem hc1 hc2 hR (rectangleBorder_subset_rectangle _ _ hs) (border_ne_zero_one hc1 hc2 hR hs).2
  have hcongr : Set.EqOn (fun s => Hfn k s * (L2 s + logDeriv hardyW s))
      (fun s => Hfn k s * ((1/2:ℂ) * logDeriv (fun z => invGammaℝ (1 - z)) s + (-(1/2:ℂ)) * logDeriv invGammaℝ s
        + (1:ℂ) * logDeriv Wreg s + (-1:ℂ) * logDeriv polarPoly s)) (RectangleBorder (zc c R) (wc c R)) := by
    intro s hs
    simp only
    rw [FZ_border hc1 hc2 hR hW hs]; ring
  have hI1 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (f := fun z => invGammaℝ (1 - z))
      (fun s _ => (analyticAt_invGammaℝ _).comp (analyticAt_const.sub analyticAt_id))
      (fun s hs => invGammaℝ_ne_zero_iff.mpr (hb1 s hs)))
  have hI2 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (fun s _ => analyticAt_invGammaℝ s) (fun s hs => invGammaℝ_ne_zero_iff.mpr (hb0 s hs)))
  have hI3 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (f := Wreg)
      (fun s hs => Wreg_analyticAt (mem_stripReg_of_border hc1 hc2 hR hs).1 (mem_stripReg_of_border hc1 hc2 hR hs).2.1)
      (fun s hs => by
        rw [Ne, Wreg_eq_zero_iff (mem_stripReg_of_border hc1 hc2 hR hs)]; exact hW s hs))
  have hI4 := borderIntegrable_of_continuousOn hk hkc
    (continuousOn_logDeriv_border (f := polarPoly) (fun s _ => differentiable_polarPoly.analyticAt s)
      (fun s hs => by
        obtain ⟨h0, h1⟩ := border_ne_zero_one hc1 hc2 hR hs
        rw [Ne, polarPoly_eq_zero_iff]; simp [h0, h1]))
  rw [RectangleIntegral'_congr hcongr, rect'_lincomb _ _ _ _ hI1 hI2 hI3 hI4,
    rect_invGammaℝ hk hkc hc1 hc2 hR, rect_invGammaℝ_one_sub hk hkc hc1 hc2 hR, hE, rect_polarPoly hk hkc hc1 hc2 hR]
  ring

end EFContour
end Hardy
end XiPrime
end Zeta23

end
