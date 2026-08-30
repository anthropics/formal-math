/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/ZeroFree.lean — (F2): every zero of ξ′ lies in the open critical strip.

TARGETS (interface: Zeta23/XiPrime/ExplicitFormula.lean §2):
  re_logDeriv_xi_pos            : 1 ≤ Re s → 0 < Re ξ′/ξ(s)
  xiDeriv_ne_zero_of_one_le_re  : 1 ≤ Re s → ξ′(s) ≠ 0
  xiDeriv_ne_zero_of_re_nonpos  : Re s ≤ 0 → ξ′(s) ≠ 0
  xiDerivZerosInStrip_holds     : XiDerivZerosInStrip
all four in namespace Zeta23.XiPrime; every auxiliary statement lives in Zeta23.XiPrime.ZeroFree.

ROUTE (Hadamard-free; no product formula for ξ is used).  Fix s with ξ(s) ≠ 0, put s′ := reflect s
= 1 − s̄ and the weight  wt s w := 1/(s − w) − 1/(s′ − w)  (two simple poles, O(|w|⁻²) at ∞).
(1) Weighted argument principle with a MEROMORPHIC weight (generic, on top of
    Zeta23.Analytic.residueTheorem_finset): (1/2πi)∮ g·f′/f = Σ_{zeros ρ} ord_ρ(f) g(ρ) + Σ_{poles q of g} r_q f′/f(q).
(2) Applied to f = ξ (entire; zeros = nontrivial zeros of ζ with the same order) and g = wt s on the
    SQUARE [1 − R, R] × [−R, R] at a good height R = R_j of Zeta23.WeilEF.good_heights:
      (1/2πi)∮ = Σ_{|γ_ρ|<R} m_ρ wt s ρ − ξ′/ξ(s) + ξ′/ξ(s′).
(3) The whole border integral → 0 as j → ∞: on the border |wt s| ≤ 4|s − s′|/R² while
    |ξ′/ξ| ≤ C(log²(j+10) + log(2+R)) (good heights + Γℝ′/Γℝ growth in the strip; Stirling for ψ and
    |ζ′/ζ| bounded to the right of 3/2; the functional equation ξ′/ξ(1−w) = −ξ′/ξ(w) to the left),
    and the perimeter is 8R − 2: total O(log²j / j).  [Growing the square kills the vertical sides
    directly, so no full-line integrals are needed, as opposed to sending R → ∞ at fixed width and
    then the width → ∞.]
    The finite zero sums → the tsum over Zeta23.zetaZeroConfig (|wt s ρ| ≤ C_s/(1+|γ_ρ|²) and
    Zeta23.WeilEF.zero_sum_inv_sq).  Hence  ξ′/ξ(s) − ξ′/ξ(s′) = Σ'_ρ m_ρ wt s ρ.
(4) Symmetry: ξ′/ξ(s′) = −conj ξ′/ξ(s), so the left side is 2 Re ξ′/ξ(s); and
    Re wt s ρ = Re 1/(s−ρ) + Re 1/(s − reflect ρ), so reindexing by the involution ρ ↦ reflect ρ of the
    zero set gives  Re ξ′/ξ(s) = Σ'_ρ m_ρ (σ − β)/|s − ρ|²  (re_logDeriv_xi_eq_tsum).
(5) For σ ≥ 1 every term is > 0 (β < 1) and a zero exists (Riemann–von Mangoldt), so Re ξ′/ξ(s) > 0 and
    ξ′(s) = ξ(s)·ξ′/ξ(s) ≠ 0; σ ≤ 0 follows from ξ′(1−s) = −ξ′(s) (Seam.xiDeriv_one_sub).
-/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.WeilEF.ZeroSumLimit
import Zeta23.GammaFacts.StirlingVert
import Zeta23.GammaFacts.Series
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement
import Zeta23.Assembly

open scoped BigOperators ComplexConjugate
open Complex MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroFree

/-! ## §A. Generic residue calculus: a meromorphic weight against f′/f; an ML bound -/

/-- Near a zero ρ of finite order of an analytic f, with a weight g analytic at ρ:
g·f′/f − ord_ρ(f)·g(ρ)/(· − ρ) is bounded on a punctured neighbourhood of ρ. -/
theorem isBigO_mul_logDeriv_near_zero {f g : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hord : analyticOrderAt f ρ ≠ ⊤) (hg : AnalyticAt ℂ g ρ) :
    ((fun s => g s * logDeriv f s) - fun s => (analyticOrderNatAt f ρ : ℂ) * g ρ / (s - ρ))
      =O[𝓝[≠] ρ] (1 : ℂ → ℂ) := by
  obtain ⟨h, hh, hh0, hfh⟩ := hf.analyticOrderAt_ne_top.mp hord
  have hh_ne : ∀ᶠ s in 𝓝 ρ, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
  have h2 : ∀ᶠ s in 𝓝 ρ, f =ᶠ[𝓝 s] (fun s => (s - ρ) ^ analyticOrderNatAt f ρ • h s) :=
    hfh.eventually_nhds
  have h3 : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ h s := hh.eventually_analyticAt
  have hexp : ∀ᶠ s in 𝓝[≠] ρ,
      (analyticOrderNatAt f ρ : ℂ) * ((g s - g ρ) / (s - ρ)) + g s * logDeriv h s
        = ((fun s => g s * logDeriv f s) - fun s =>
            (analyticOrderNatAt f ρ : ℂ) * g ρ / (s - ρ)) s := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
      mem_nhdsWithin_of_mem_nhds hh_ne, mem_nhdsWithin_of_mem_nhds h3]
      with s hs hfs hhs hhas
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    have hld : logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + logDeriv h s := by
      have e1 : logDeriv f s = logDeriv (fun s => (s - ρ) ^ analyticOrderNatAt f ρ * h s) s := by
        simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
      rw [e1, logDeriv_mul (f := fun s : ℂ => (s - ρ) ^ analyticOrderNatAt f ρ) (g := h) s
        (pow_ne_zero _ hsρ) hhs (by fun_prop) hhas.differentiableAt]
      have e2 : logDeriv (fun s : ℂ => (s - ρ) ^ analyticOrderNatAt f ρ) s
          = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
        rw [show (fun s : ℂ => (s - ρ) ^ analyticOrderNatAt f ρ)
            = (fun x : ℂ => x ^ analyticOrderNatAt f ρ) ∘ (fun s => s - ρ) from rfl,
          logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
        simp
      rw [e2]
    simp only [Pi.sub_apply, hld]
    ring
  have hslope : Tendsto (fun s => (g s - g ρ) / (s - ρ)) (𝓝[≠] ρ) (𝓝 (deriv g ρ)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hg.differentiableAt.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] ρ) (𝓝 (g ρ * logDeriv h ρ)) := by
    have : ContinuousAt (fun s => g s * logDeriv h s) ρ := by
      show ContinuousAt (fun s => g s * (deriv h s / h s)) ρ
      exact hg.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hO : (fun s => (analyticOrderNatAt f ρ : ℂ) * ((g s - g ρ) / (s - ρ))
      + g s * logDeriv h s) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) :=
    ((hslope.const_mul (analyticOrderNatAt f ρ : ℂ)).add hcont).isBigO_one ℂ
  exact hO.congr' hexp EventuallyEq.rfl

/-- Near a simple pole q of the weight g (principal part r/(· − q)), with F differentiable at q:
g·F − r·F(q)/(· − q) is bounded on a punctured neighbourhood of q. -/
theorem isBigO_mul_near_weightPole {F g : ℂ → ℂ} {q r : ℂ} (hF : DifferentiableAt ℂ F q)
    (hg : (g - fun s => r / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ)) :
    ((fun s => g s * F s) - fun s => r * F q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
  have hFc : Tendsto F (𝓝[≠] q) (𝓝 (F q)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hFO : F =O[𝓝[≠] q] (1 : ℂ → ℂ) := hFc.isBigO_one ℂ
  have hslope : Tendsto (fun s => (F s - F q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv F q)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hF.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have h1 : (fun s => (g - fun s => r / (s - q)) s * F s) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
    have := hg.mul hFO
    simpa only [Pi.one_apply, mul_one, Pi.one_def] using this
  have h2 : (fun s => r * ((F s - F q) / (s - q))) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
    (hslope.const_mul r).isBigO_one ℂ
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsq : s - q ≠ 0 := sub_ne_zero.mpr hs
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- **Weighted argument principle with a meromorphic weight.**  f analytic on a neighbourhood of
every point of the closed rectangle and nonvanishing on its border, Z its (finite) zero set there;
g analytic on the rectangle off a finite set Q of interior points, disjoint from Z, with principal
part r q/(· − q) at q ∈ Q.  Then
(1/2πi)∮ g·f′/f = Σ_{ρ∈Z} ord_ρ(f)·g(ρ) + Σ_{q∈Q} r q·(f′/f)(q). -/
theorem rectangleIntegral'_mul_logDeriv_weightPoles {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z Q : Finset ℂ) (hZQ : Disjoint Z Q)
    (hQint : ∀ q ∈ Q, Rectangle z w ∈ 𝓝 q)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : ∀ p ∈ Rectangle z w \ (Q : Set ℂ), AnalyticAt ℂ g p)
    (hborder : ∀ p ∈ RectangleBorder z w, f p ≠ 0)
    (hZ : ∀ p ∈ Rectangle z w, f p = 0 ↔ p ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w)
    (r : ℂ → ℂ) (hnear : ∀ q ∈ Q, (g - fun s => r q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ)) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ + ∑ q ∈ Q, r q * logDeriv f q := by
  classical
  have hZnotQ : ∀ ρ ∈ Z, ρ ∉ Q := fun ρ hρ hρQ => Finset.disjoint_left.mp hZQ hρ hρQ
  have hQnotZ : ∀ q ∈ Q, q ∉ Z := fun q hq hqZ => Finset.disjoint_left.mp hZQ hqZ hq
  -- a border point where f ≠ 0, hence all orders in the (preconnected) rectangle are finite
  have hzB : z ∈ RectangleBorder z w := Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hz0 : f z ≠ 0 := hborder z hzB
  have hzR : z ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hzB
  -- (IsPreconnected via a Mathlib-elaborated Convex term: a locally elaborated type ascription
  -- Convex ℝ (Rectangle z w) picks an SMul ℝ ℂ instance for which ContinuousSMul is not found here.)
  have hpre : IsPreconnected (Rectangle z w) := by
    rw [rectangle_eq_convexHull]; exact (convex_convexHull ℝ _).isPreconnected
  have hordz : analyticOrderAt f z ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hz0)]
    exact ENat.zero_ne_top
  have hord : ∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤ := fun ρ hρ =>
    hf.analyticOrderAt_ne_top_of_isPreconnected hpre hzR (hZsub hρ) hordz
  -- zeros are interior points
  have hZint : ∀ ρ ∈ Z, Rectangle z w ∈ 𝓝 ρ := by
    intro ρ hρ
    have hρR : ρ ∈ Rectangle z w := hZsub hρ
    have hρB : ρ ∉ RectangleBorder z w := fun h => hborder ρ h ((hZ ρ hρR).mpr hρ)
    obtain ⟨h1, h2⟩ := hρR
    have h1' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re := by simpa [uIcc_of_le hre] using h1
    have h2' : z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by simpa [uIcc_of_le him] using h2
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, not_or] at hρB
    obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hρB
    rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h => hb2 ⟨h.symm, h2⟩),
      lt_of_le_of_ne h1'.2 (fun h => hb4 ⟨h, h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h => hb1 ⟨h1, h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h => hb3 ⟨h1, h⟩)⟩⟩
  -- residues: ord·g at zeros of f, r·f′/f at poles of g
  let A : ℂ → ℂ := fun p => if p ∈ Q then r p * logDeriv f p else (analyticOrderNatAt f p : ℂ) * g p
  have hint : ∀ p ∈ Z ∪ Q, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    exacts [hZint p hp, hQint p hp]
  have key := Zeta23.Analytic.residueTheorem_finset (f := fun s => g s * logDeriv f s) hre him
    (Z ∪ Q) A hint ?holo ?near
  · rw [key, Finset.sum_union hZQ]
    have hZsum : ∑ p ∈ Z, A p = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ :=
      Finset.sum_congr rfl (fun p hp => by simp [A, hZnotQ p hp])
    have hQsum : ∑ p ∈ Q, A p = ∑ q ∈ Q, r q * logDeriv f q :=
      Finset.sum_congr rfl (fun p hp => by simp [A, hp])
    rw [hZsum, hQsum]
  case holo =>
    intro s hs
    have hsQ : s ∉ Q := fun h => hs.2 (by simp [h])
    have hsZ : s ∉ Z := fun h => hs.2 (by simp [h])
    have hfs : f s ≠ 0 := fun h => hsZ ((hZ s hs.1).mp h)
    have hfa := hf s hs.1
    have hga := hg s ⟨hs.1, by simpa using hsQ⟩
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => g s * (deriv f s / f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near =>
    intro p hp
    rcases Finset.mem_union.mp hp with hρ | hq
    · have hA : A p = (analyticOrderNatAt f p : ℂ) * g p := by simp [A, hZnotQ p hρ]
      have hga := hg p ⟨hZsub hρ, by simpa using hZnotQ p hρ⟩
      rw [hA]
      exact isBigO_mul_logDeriv_near_zero (hf p (hZsub hρ)) (hord p hρ) hga
    · have hA : A p = r p * logDeriv f p := by simp [A, hq]
      have hpR : p ∈ Rectangle z w := mem_of_mem_nhds (hQint p hq)
      have hfp : f p ≠ 0 := fun h => hQnotZ p hq ((hZ p hpR).mp h)
      have hfa := hf p hpR
      have hF : DifferentiableAt ℂ (logDeriv f) p := by
        have : logDeriv f = fun s => deriv f s / f s := by funext s; exact logDeriv_apply f s
        rw [this]
        exact hfa.deriv.differentiableAt.div hfa.differentiableAt hfp
      rw [hA]
      exact isBigO_mul_near_weightPole (F := logDeriv f) hF (hnear p hq)

/-- **ML bound** for a rectangle integral: ‖∮ f‖ ≤ (sup_border ‖f‖) · (perimeter). -/
theorem norm_rectangleIntegral_le {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {M : ℝ} (hf : ∀ p ∈ RectangleBorder z w, ‖f p‖ ≤ M) :
    ‖RectangleIntegral f z w‖ ≤ M * (2 * (w.re - z.re) + 2 * (w.im - z.im)) := by
  have hH : ∀ y : ℝ, (∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + y * I) ∈ RectangleBorder z w) →
      ‖HIntegral f z.re w.re y‖ ≤ M * (w.re - z.re) := by
    intro y hy
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.re) (b := w.re) (C := M)
      (f := fun x : ℝ => f (x + y * I)) (fun x hx => hf _ (hy x (Set.uIoc_subset_uIcc hx)))
    rw [abs_of_nonneg (by linarith)] at this
    exact this
  have hV : ∀ x : ℝ, (∀ y ∈ Set.uIcc z.im w.im, ((x : ℂ) + y * I) ∈ RectangleBorder z w) →
      ‖VIntegral f x z.im w.im‖ ≤ M * (w.im - z.im) := by
    intro x hx
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := z.im) (b := w.im) (C := M)
      (f := fun y : ℝ => f (x + y * I)) (fun y hy => hf _ (hx y (Set.uIoc_subset_uIcc hy)))
    rw [abs_of_nonneg (by linarith)] at this
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    exact this
  have h1 := hH z.im (fun x hx => mapsTo_rectangleBorder_left_im z w hx)
  have h2 := hH w.im (fun x hx => mapsTo_rectangleBorder_right_im z w hx)
  have h3 := hV w.re (fun y hy => mapsTo_rectangleBorder_right_re z w hy)
  have h4 := hV z.re (fun y hy => mapsTo_rectangleBorder_left_re z w hy)
  unfold RectangleIntegral
  calc ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im
        + VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im‖
      ≤ ‖HIntegral f z.re w.re z.im‖ + ‖HIntegral f z.re w.re w.im‖
        + ‖VIntegral f w.re z.im w.im‖ + ‖VIntegral f z.re z.im w.im‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
    _ ≤ M * (2 * (w.re - z.re) + 2 * (w.im - z.im)) := by linarith

/-! ## §B. Facts about ξ: zeros, orders, symmetries of ξ′/ξ -/

/-- The zeros of ξ are exactly the nontrivial zeros of ζ (ξ(0) = ξ(1) = 1/2; off {0,1},
ξ = s(s−1)/2·Λ and the zeros of Λ are the nontrivial zeros of ζ). -/
theorem xi_eq_zero_iff (s : ℂ) : xi s = 0 ↔ IsNontrivialZero s := by
  by_cases h0 : s = 0
  · subst h0
    have : xi 0 = 1 / 2 := by simp [xi]
    rw [this]
    constructor
    · intro h; norm_num at h
    · rintro ⟨_, h, _⟩; simp at h
  by_cases h1 : s = 1
  · subst h1
    have : xi 1 = 1 / 2 := by simp [xi]
    rw [this]
    constructor
    · intro h; norm_num at h
    · rintro ⟨_, _, h⟩; simp at h
  rw [xi_eq s h0 h1, mul_eq_zero, ← Zeta23.RvM.completedRiemannZeta_eq_zero_iff]
  have : s * (s - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  simp [this]

theorem xi_eventuallyEq {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    xi =ᶠ[𝓝 ρ] fun s => s * (s - 1) / 2 * completedRiemannZeta s := by
  filter_upwards [isOpen_compl_singleton.mem_nhds h0, isOpen_compl_singleton.mem_nhds h1]
    with s hs0 hs1
  exact xi_eq s (by simpa using hs0) (by simpa using hs1)

/-- At a nontrivial zero, ord(ξ) = ord(Λ) = ord(ζ) = zeroMult. -/
theorem analyticOrderNatAt_xi {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    analyticOrderNatAt xi ρ = zeroMult ρ := by
  have h0 : ρ ≠ 0 := fun h => by have := hρ.2.1; simp [h] at this
  have h1 : ρ ≠ 1 := fun h => by have := hρ.2.2; simp [h] at this
  have hev := xi_eventuallyEq h0 h1
  have hΛ := Zeta23.RvM.analyticAt_completedRiemannZeta h0 h1
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2)).analyticAt ρ
  have hp0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) ρ = 0 :=
    hp.analyticOrderAt_eq_zero.mpr (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)
  have hmul := analyticOrderAt_mul hp hΛ
  rw [show ((fun s : ℂ => s * (s - 1) / 2) * completedRiemannZeta)
      = fun s => s * (s - 1) / 2 * completedRiemannZeta s from rfl] at hmul
  rw [← Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta hρ.2.1 h1]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev, hmul, hp0, zero_add]

/-- ξ′/ξ(1 − s) = −ξ′/ξ(s). -/
theorem logDeriv_xi_one_sub (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  have hcomp : xi = xi ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [xi_one_sub]
  have hd : DifferentiableAt ℂ xi (1 - s) := xi_differentiable _
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

/-- ξ′/ξ(s̄) = conj ξ′/ξ(s). -/
theorem logDeriv_xi_conj (s : ℂ) : logDeriv xi (conj s) = conj (logDeriv xi s) := by
  rw [logDeriv_apply, logDeriv_apply, show deriv xi = xiDeriv from rfl, xiDeriv_conj, xi_conj,
    ← map_div₀]

/-- ξ(1 − s̄) = conj ξ(s). -/
theorem xi_reflect (s : ℂ) : xi (reflect s) = conj (xi s) := by
  show xi (1 - conj s) = _
  rw [xi_one_sub, xi_conj]

/-- ξ′/ξ(1 − s̄) = −conj ξ′/ξ(s). -/
theorem logDeriv_xi_reflect (s : ℂ) : logDeriv xi (reflect s) = -conj (logDeriv xi s) := by
  show logDeriv xi (1 - conj s) = _
  rw [logDeriv_xi_one_sub, logDeriv_xi_conj]

/-! ## §C. Growth of ξ′/ξ on the contour -/

/-- ψ is differentiable (in particular continuous) on the open right half-plane
(Γ analytic and nonvanishing there; as in Zeta23.WeilEF.digamma_growth_strip). -/
theorem differentiableAt_digamma {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s := by
  have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓan : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hs] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    rw [h] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma s := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hψan.differentiableAt

/-- iterated functional equation: ψ(z + n) = ψ(z) + Σ_{k<n} 1/(z + k)  (Re z > 0). -/
theorem digamma_add_nat {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    Complex.digamma (z + n) = Complex.digamma z + ∑ k ∈ Finset.range n, 1 / (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, z + n ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    rw [Nat.cast_succ, ← add_assoc, Complex.digamma_apply_add_one _ hne, ih, Finset.sum_range_succ,
      one_div]
    ring

/-- ψ grows logarithmically on Re z ≥ 1/2: Stirling (Zeta23.StirlingVert.digamma_stirling) for
|Im z| ≥ 1/2; for |Im z| < 1/2 shift z back into the compact box [1/2,3/2] × [−1/2,1/2] with the
functional equation and bound the harmonic-type sum by 2(1 + log n). -/
theorem norm_digamma_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re →
    ‖Complex.digamma z‖ ≤ C * Real.log (2 + ‖z‖) := by
  -- the compact box
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Complex.digamma (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    intro s hs
    have : 1 / 2 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact (differentiableAt_digamma (by linarith)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by
    rw [Complex.mem_reProdIm, Complex.one_re, Complex.one_im, Set.mem_Icc, Set.mem_Icc]; norm_num))
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : 0 ≤ K₀ := by have := Real.pi_pos; rw [hK₀]; linarith
  refine ⟨(K₀ + M + 4) / Real.log 2 + 2, by positivity, fun z hz => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg z])
  have hL0 : 0 < Real.log (2 + ‖z‖) := hlog2.trans_le hL
  suffices h : ‖Complex.digamma z‖ ≤ 2 * Real.log (2 + ‖z‖) + (K₀ + M + 4) by
    calc ‖Complex.digamma z‖ ≤ 2 * Real.log (2 + ‖z‖) + (K₀ + M + 4) := h
      _ = 2 * Real.log (2 + ‖z‖) + ((K₀ + M + 4) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ 2 * Real.log (2 + ‖z‖) + ((K₀ + M + 4) / Real.log 2) * Real.log (2 + ‖z‖) := by
          have : 0 ≤ (K₀ + M + 4) / Real.log 2 := by positivity
          nlinarith
      _ = ((K₀ + M + 4) / Real.log 2 + 2) * Real.log (2 + ‖z‖) := by ring
  have hzre0 : 0 < z.re := by linarith
  have hnorm_lo : 1 / 2 ≤ ‖z‖ := le_trans hz (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have hnorm0 : 0 < ‖z‖ := by linarith
  rcases le_or_gt (1 / 2 : ℝ) |z.im| with him | him
  · -- Stirling: ‖ψ‖ ≤ ‖ψ − log z + (1/2)/z‖ + ‖log z‖ + ‖(1/2)/z‖ ≤ 12 + (log 4 + log(2+|z|) + π) + 2
    have hst := Zeta23.StirlingVert.digamma_stirling (w := z) hzre0 him
    have hlog_s : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
      calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖z‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi z
            linarith
    have hlog_abs : |Real.log ‖z‖| ≤ Real.log 4 + Real.log (2 + ‖z‖) := by
      rcases le_or_gt (Real.log ‖z‖) 0 with hneg | hpos
      · have h1 : Real.log (1 / 4 : ℝ) ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) (by linarith)
        have h2 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
          rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖z‖ ≤ Real.log (2 + ‖z‖) := Real.log_le_log hnorm0 (by linarith)
        linarith
    have hinv : ‖(1 / 2 : ℂ) / z‖ ≤ 2 := by
      rw [norm_div, div_le_iff₀ hnorm0]
      have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1]; linarith
    have him2 : 3 / z.im ^ 2 ≤ 12 := by
      have h1 : (1 / 4 : ℝ) ≤ z.im ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have hsplit : ‖Complex.digamma z‖
        ≤ ‖Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z‖ + ‖Complex.log z‖
          + ‖(1 / 2 : ℂ) / z‖ := by
      have h2 : Complex.digamma z = (Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z)
          + Complex.log z - (1 / 2 : ℂ) / z := by ring
      calc ‖Complex.digamma z‖
          = ‖(Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) + Complex.log z
              - (1 / 2 : ℂ) / z‖ := by rw [← h2]
        _ ≤ ‖(Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) + Complex.log z‖
            + ‖(1 / 2 : ℂ) / z‖ := norm_sub_le _ _
        _ ≤ _ := by
            have := norm_add_le (Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) (Complex.log z)
            linarith
    rw [hK₀]
    linarith [hL0]
  · -- near the real axis: z = z₀ + n with z₀ in the box
    set n : ℕ := ⌊z.re - 1 / 2⌋₊ with hn
    set z₀ : ℂ := z - n with hz₀
    have hfl : (n : ℝ) ≤ z.re - 1 / 2 := Nat.floor_le (by linarith)
    have hfl2 : z.re - 1 / 2 < n + 1 := Nat.lt_floor_add_one (z.re - 1 / 2)
    have hz₀re : z₀.re = z.re - n := by simp [hz₀]
    have hz₀im : z₀.im = z.im := by simp [hz₀]
    have hz₀B : z₀ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
      rw [Complex.mem_reProdIm, hz₀re, hz₀im, Set.mem_Icc, Set.mem_Icc]
      have := abs_lt.mp him
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hz₀pos : 0 < z₀.re := by rw [hz₀re]; linarith
    have hzeq : z = z₀ + n := by simp [hz₀]
    have hψ : Complex.digamma z = Complex.digamma z₀ + ∑ k ∈ Finset.range n, 1 / (z₀ + k) := by
      rw [hzeq]; exact digamma_add_nat hz₀pos n
    have hterm : ∀ k ∈ Finset.range n, ‖1 / (z₀ + (k : ℂ))‖ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
      intro k _
      have hre : (z₀ + (k : ℂ)).re = z₀.re + k := by simp
      have hpos : 0 < z₀.re + k := by positivity
      have hnk : z₀.re + k ≤ ‖z₀ + (k : ℂ)‖ := by
        calc z₀.re + k = |(z₀ + (k : ℂ)).re| := by rw [hre, abs_of_pos hpos]
          _ ≤ ‖z₀ + (k : ℂ)‖ := Complex.abs_re_le_norm _
      rw [norm_div, norm_one]
      calc 1 / ‖z₀ + (k : ℂ)‖ ≤ 1 / (z₀.re + k) := one_div_le_one_div_of_le hpos hnk
        _ ≤ 1 / (1 / 2 + k) := one_div_le_one_div_of_le (by positivity) (by linarith [hz₀B.1.1])
        _ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
            rw [div_le_iff₀ (by positivity)]
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            field_simp
            nlinarith
    have hlogn : Real.log n ≤ Real.log (2 + ‖z‖) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact hL0.le
      · apply Real.log_le_log (by exact_mod_cast hpos)
        have : z.re ≤ ‖z‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm z)
        linarith
    have hsum : ‖∑ k ∈ Finset.range n, 1 / (z₀ + (k : ℂ))‖ ≤ 2 * (1 + Real.log (2 + ‖z‖)) := by
      calc ‖∑ k ∈ Finset.range n, 1 / (z₀ + (k : ℂ))‖
          ≤ ∑ k ∈ Finset.range n, ‖1 / (z₀ + (k : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range n, 2 * (1 / ((k : ℝ) + 1)) := Finset.sum_le_sum hterm
        _ = 2 * ((harmonic n : ℚ) : ℝ) := by
            rw [← Finset.mul_sum, Zeta23.DigammaSeries.harmonic_cast_eq]
        _ ≤ 2 * (1 + Real.log n) := by
            have := harmonic_le_one_add_log n
            linarith
        _ ≤ 2 * (1 + Real.log (2 + ‖z‖)) := by linarith
    calc ‖Complex.digamma z‖ = ‖Complex.digamma z₀ + ∑ k ∈ Finset.range n, 1 / (z₀ + (k : ℂ))‖ := by
          rw [hψ]
      _ ≤ ‖Complex.digamma z₀‖ + ‖∑ k ∈ Finset.range n, 1 / (z₀ + (k : ℂ))‖ := norm_add_le _ _
      _ ≤ M + 2 * (1 + Real.log (2 + ‖z‖)) := add_le_add (hM z₀ hz₀B) hsum
      _ ≤ 2 * Real.log (2 + ‖z‖) + (K₀ + M + 4) := by linarith

/-- ‖Γℝ′/Γℝ(w)‖ ≤ C log(2 + |w|) for Re w ≥ 1. -/
theorem norm_logDeriv_Gammaℝ_le_far : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 ≤ w.re →
    ‖logDeriv Complex.Gammaℝ w‖ ≤ C * Real.log (2 + ‖w‖) := by
  obtain ⟨C, hC, hψ⟩ := norm_digamma_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi / (2 * Real.log 2) + C / 2, by positivity, fun w hw => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + ‖w‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg w])
  rw [Zeta23.RvM.logDeriv_Gammaℝ (by linarith)]
  have h1 : ‖-(Real.log Real.pi : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogπ,
      Complex.norm_ofNat]
  have h2 : ‖(1 / 2 : ℂ) * Complex.digamma (w / 2)‖ ≤ C / 2 * Real.log (2 + ‖w‖) := by
    rw [norm_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hw2 : 1 / 2 ≤ (w / 2).re := by simp; linarith
    have h3 := hψ (w / 2) hw2
    have h4 : Real.log (2 + ‖w / 2‖) ≤ Real.log (2 + ‖w‖) := by
      apply Real.log_le_log (by positivity)
      rw [norm_div, Complex.norm_ofNat]
      linarith [norm_nonneg w]
    calc 1 / 2 * ‖Complex.digamma (w / 2)‖ ≤ 1 / 2 * (C * Real.log (2 + ‖w‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact h3.trans (mul_le_mul_of_nonneg_left h4 hC.le)
      _ = C / 2 * Real.log (2 + ‖w‖) := by ring
  calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (w / 2)‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (w / 2)‖ := norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 + C / 2 * Real.log (2 + ‖w‖) := by rw [h1]; linarith
    _ = Real.log Real.pi / (2 * Real.log 2) * Real.log 2 + C / 2 * Real.log (2 + ‖w‖) := by
        field_simp
    _ ≤ Real.log Real.pi / (2 * Real.log 2) * Real.log (2 + ‖w‖) + C / 2 * Real.log (2 + ‖w‖) := by
        have : 0 ≤ Real.log Real.pi / (2 * Real.log 2) := by positivity
        nlinarith
    _ = (Real.log Real.pi / (2 * Real.log 2) + C / 2) * Real.log (2 + ‖w‖) := by ring

/-- ‖ζ′/ζ(w)‖ ≤ Σ Λ(n) n^{−3/2} for Re w ≥ 3/2. -/
theorem norm_logDeriv_zeta_le_far : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, 3 / 2 ≤ w.re →
    ‖logDeriv riemannZeta w‖ ≤ M := by
  set a : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with ha
  have hsum : Summable (fun n : ℕ => ‖LSeries.term a ((3 / 2 : ℝ) : ℂ) n‖) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((3 / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; norm_num)
    exact summable_norm_iff.mpr h
  refine ⟨∑' n : ℕ, ‖LSeries.term a ((3 / 2 : ℝ) : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _,
    fun w hw => ?_⟩
  have hre1 : 1 < w.re := by linarith
  have h1 : logDeriv riemannZeta w = -LSeries a w := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre1
    rw [logDeriv, Pi.div_apply, ha, h2]; ring
  have hle : ∀ n : ℕ, ‖LSeries.term a w n‖ ≤ ‖LSeries.term a ((3 / 2 : ℝ) : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · simp [h0, LSeries.term_zero]
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp only [hn.ne', if_false, Complex.ofReal_re]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hw
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term a w n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  rw [h1, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term a w n‖ ≤ ∑' n, ‖LSeries.term a w n‖ := norm_tsum_le_tsum_norm hsum'
    _ ≤ ∑' n, ‖LSeries.term a ((3 / 2 : ℝ) : ℂ) n‖ := hsum'.tsum_le_tsum hle hsum

/-- ‖ξ′/ξ(w)‖ ≤ C log(2 + |w|) for Re w ≥ 3/2  (ξ′/ξ = Γℝ′/Γℝ + 1/w + 1/(w−1) + ζ′/ζ). -/
theorem norm_logDeriv_xi_le_far : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 3 / 2 ≤ w.re →
    ‖logDeriv xi w‖ ≤ C * Real.log (2 + ‖w‖) := by
  obtain ⟨C, hC, hΓ⟩ := norm_logDeriv_Gammaℝ_le_far
  obtain ⟨M, hM0, hζ⟩ := norm_logDeriv_zeta_le_far
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C + (3 + M) / Real.log 2, by positivity, fun w hw => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + ‖w‖) :=
    Real.log_le_log two_pos (by linarith [norm_nonneg w])
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw; norm_num at hw
  have hζne : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [logDeriv_xi_eq hw0 hw1 hζne, Lfn]
  have hn1 : ‖1 / w‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by
      linarith [le_trans (le_abs_self _) (Complex.abs_re_le_norm w)])]
    linarith [le_trans (le_abs_self _) (Complex.abs_re_le_norm w)]
  have hn2 : ‖1 / (w - 1)‖ ≤ 2 := by
    have : 1 / 2 ≤ ‖w - 1‖ := by
      calc (1 / 2 : ℝ) ≤ |(w - 1).re| := by
            rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)]; linarith
        _ ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  calc ‖logDeriv Gammaℝ w + 1 / w + 1 / (w - 1) + logDeriv riemannZeta w‖
      ≤ ‖logDeriv Gammaℝ w‖ + ‖1 / w‖ + ‖1 / (w - 1)‖ + ‖logDeriv riemannZeta w‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ C * Real.log (2 + ‖w‖) + 1 + 2 + M := by
        linarith [hΓ w (by linarith), hζ w hw]
    _ = C * Real.log (2 + ‖w‖) + ((3 + M) / Real.log 2) * Real.log 2 := by field_simp; ring
    _ ≤ C * Real.log (2 + ‖w‖) + ((3 + M) / Real.log 2) * Real.log (2 + ‖w‖) := by
        have : 0 ≤ (3 + M) / Real.log 2 := by positivity
        nlinarith
    _ = (C + (3 + M) / Real.log 2) * Real.log (2 + ‖w‖) := by ring

/-- On the horizontal segments Im w = ±R, −1/2 ≤ Re w ≤ 3/2 of a good height R (ζ ≠ 0 and
‖ζ′/ζ‖ ≤ L on Im = ±R, 1/2 ≤ Re ≤ 2): ‖ξ′/ξ(w)‖ ≤ C (L + log(2 + R)). -/
theorem norm_logDeriv_xi_le_goodHeight : ∃ C : ℝ, 0 < C ∧ ∀ (L R : ℝ), 1 ≤ L → 1 ≤ R →
    (∀ p : ℂ, (p.im = R ∨ p.im = -R) → 1 / 2 ≤ p.re → p.re ≤ 2 →
      riemannZeta p ≠ 0 ∧ ‖logDeriv riemannZeta p‖ ≤ L) →
    ∀ w : ℂ, (w.im = R ∨ w.im = -R) → -1 / 2 ≤ w.re → w.re ≤ 3 / 2 →
      ‖logDeriv xi w‖ ≤ C * (L + Real.log (2 + R)) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le
  refine ⟨CΓ + 3, by positivity, fun L R hL hR hgood => ?_⟩
  -- the right half 1/2 ≤ Re w ≤ 3/2 first
  have aux : ∀ w : ℂ, (w.im = R ∨ w.im = -R) → 1 / 2 ≤ w.re → w.re ≤ 3 / 2 →
      ‖logDeriv xi w‖ ≤ (CΓ + 3) * (L + Real.log (2 + R)) := by
    intro w him h1 h2
    have habs : |w.im| = R := by
      rcases him with h | h
      · rw [h, abs_of_pos (by linarith)]
      · rw [h, abs_neg, abs_of_pos (by linarith)]
    have hw0 : 0 < w.re := by linarith
    have hw1 : w ≠ 1 := fun h => by
      rw [h, Complex.one_im] at habs; rw [← habs] at hR; simp at hR; linarith
    obtain ⟨hζne, hζb⟩ := hgood w him h1 (by linarith)
    rw [logDeriv_xi_eq hw0 hw1 hζne, Lfn]
    have hnorm : R ≤ ‖w‖ := habs ▸ Complex.abs_im_le_norm w
    have hn1 : ‖1 / w‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]; linarith
    have hn2 : ‖1 / (w - 1)‖ ≤ 1 := by
      have : R ≤ ‖w - 1‖ := by
        have := Complex.abs_im_le_norm (w - 1)
        rwa [Complex.sub_im, Complex.one_im, sub_zero, habs] at this
      rw [norm_div, norm_one, div_le_one (by linarith)]; linarith
    have hG : ‖logDeriv Gammaℝ w‖ ≤ CΓ * Real.log (2 + R) := by
      have := hΓ w.re w.im h1 h2
      rwa [Complex.re_add_im, habs] at this
    have hlog0 : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
    calc ‖logDeriv Gammaℝ w + 1 / w + 1 / (w - 1) + logDeriv riemannZeta w‖
        ≤ ‖logDeriv Gammaℝ w‖ + ‖1 / w‖ + ‖1 / (w - 1)‖ + ‖logDeriv riemannZeta w‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ CΓ * Real.log (2 + R) + 1 + 1 + L := by linarith
      _ ≤ (CΓ + 3) * (L + Real.log (2 + R)) := by nlinarith
  intro w him h1 h2
  rcases le_or_gt (1 / 2 : ℝ) w.re with hre | hre
  · exact aux w him hre h2
  · -- reflect: ξ′/ξ(w) = −ξ′/ξ(1 − w)
    have e : logDeriv xi w = -logDeriv xi (1 - w) := by
      rw [← logDeriv_xi_one_sub (1 - w), sub_sub_cancel]
    rw [e, norm_neg]
    apply aux (1 - w)
    · rcases him with h | h
      · right; simp [h]
      · left; simp [h]
    · simp; linarith
    · simp; linarith

/-- lower-left corner of the square contour [1 − R, R] × [−R, R]. -/
def zc (R : ℝ) : ℂ := ((1 - R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I

/-- upper-right corner of the square contour [1 − R, R] × [−R, R]. -/
def wc (R : ℝ) : ℂ := ((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I

@[simp] theorem zc_re (R : ℝ) : (zc R).re = 1 - R := by simp [zc]
@[simp] theorem zc_im (R : ℝ) : (zc R).im = -R := by simp [zc]
@[simp] theorem wc_re (R : ℝ) : (wc R).re = R := by simp [wc]
@[simp] theorem wc_im (R : ℝ) : (wc R).im = R := by simp [wc]

/-- ‖ξ′/ξ‖ ≤ C (L + log(2 + R)) on the whole border of the square at a good height R ≥ 2. -/
theorem norm_logDeriv_xi_le_border : ∃ C : ℝ, 0 < C ∧ ∀ (L R : ℝ), 1 ≤ L → 2 ≤ R →
    (∀ p : ℂ, (p.im = R ∨ p.im = -R) → 1 / 2 ≤ p.re → p.re ≤ 2 →
      riemannZeta p ≠ 0 ∧ ‖logDeriv riemannZeta p‖ ≤ L) →
    ∀ p ∈ RectangleBorder (zc R) (wc R), ‖logDeriv xi p‖ ≤ C * (L + Real.log (2 + R)) := by
  obtain ⟨C₁, hC₁, hmid⟩ := norm_logDeriv_xi_le_goodHeight
  obtain ⟨C₂, hC₂, hfar⟩ := norm_logDeriv_xi_le_far
  refine ⟨C₁ + 2 * C₂, by positivity, fun L R hL hR hgood p hp => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hLl : Real.log (2 + R) ≤ L + Real.log (2 + R) := by linarith
  -- size of border points
  have hpR : p ∈ Rectangle (zc R) (wc R) := rectangleBorder_subset_rectangle _ _ hp
  have hmem : (1 - R ≤ p.re ∧ p.re ≤ R) ∧ (-R ≤ p.im ∧ p.im ≤ R) := by
    simpa only [Rectangle, Complex.mem_reProdIm, zc_re, zc_im, wc_re, wc_im,
      Set.uIcc_of_le (show (1 - R : ℝ) ≤ R by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc] using hpR
  have hpn : ‖p‖ ≤ 2 * R := by
    calc ‖p‖ ≤ |p.re| + |p.im| := Complex.norm_le_abs_re_add_abs_im p
      _ ≤ R + R := add_le_add (abs_le.mpr ⟨by linarith [hmem.1.1], hmem.1.2⟩)
          (abs_le.mpr ⟨hmem.2.1, hmem.2.2⟩)
      _ = 2 * R := by ring
  -- log(2 + |q|) ≤ 2 log(2 + R) whenever |q| ≤ 2R + 2
  have hlogq : ∀ q : ℂ, ‖q‖ ≤ 2 * R + 2 → Real.log (2 + ‖q‖) ≤ 2 * Real.log (2 + R) := by
    intro q hq
    have e : 2 * Real.log (2 + R) = Real.log ((2 + R) ^ 2) := by
      rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by positivity)
    nlinarith [norm_nonneg q]
  -- far right, far left (by reflection), middle
  have hR' : ∀ q : ℂ, ‖q‖ ≤ 2 * R + 2 → 3 / 2 ≤ q.re →
      ‖logDeriv xi q‖ ≤ 2 * C₂ * Real.log (2 + R) := by
    intro q hq hre
    calc ‖logDeriv xi q‖ ≤ C₂ * Real.log (2 + ‖q‖) := hfar q hre
      _ ≤ C₂ * (2 * Real.log (2 + R)) := mul_le_mul_of_nonneg_left (hlogq q hq) hC₂.le
      _ = 2 * C₂ * Real.log (2 + R) := by ring
  have hL' : ∀ q : ℂ, ‖q‖ ≤ 2 * R + 1 → q.re ≤ -1 / 2 →
      ‖logDeriv xi q‖ ≤ 2 * C₂ * Real.log (2 + R) := by
    intro q hq hre
    have e : logDeriv xi q = -logDeriv xi (1 - q) := by
      rw [← logDeriv_xi_one_sub (1 - q), sub_sub_cancel]
    rw [e, norm_neg]
    apply hR' (1 - q)
    · calc ‖1 - q‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ := norm_sub_le _ _
        _ ≤ 2 * R + 2 := by rw [norm_one]; linarith
    · simp; linarith
  have htot : ‖logDeriv xi p‖ ≤ 2 * C₂ * Real.log (2 + R) ∨
      ‖logDeriv xi p‖ ≤ C₁ * (L + Real.log (2 + R)) := by
    rcases le_or_gt (3 / 2 : ℝ) p.re with h1 | h1
    · exact Or.inl (hR' p (by linarith) h1)
    rcases le_or_gt p.re (-1 / 2 : ℝ) with h2 | h2
    · exact Or.inl (hL' p (by linarith) h2)
    -- middle: p must be on a horizontal side
    right
    have him : p.im = R ∨ p.im = -R := by
      simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
        zc_re, zc_im, wc_re, wc_im] at hp
      rcases hp with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
      · exact Or.inr h'
      · exfalso; linarith
      · exact Or.inl h'
      · exfalso; linarith
    exact hmid L R hL (by linarith) hgood p him (by linarith) (by linarith)
  rcases htot with h | h
  · calc ‖logDeriv xi p‖ ≤ 2 * C₂ * Real.log (2 + R) := h
      _ ≤ 2 * C₂ * (L + Real.log (2 + R)) := mul_le_mul_of_nonneg_left hLl (by positivity)
      _ ≤ (C₁ + 2 * C₂) * (L + Real.log (2 + R)) := by nlinarith
  · calc ‖logDeriv xi p‖ ≤ C₁ * (L + Real.log (2 + R)) := h
      _ ≤ (C₁ + 2 * C₂) * (L + Real.log (2 + R)) := by nlinarith

/-- the weight: wt s w = 1/(s − w) − 1/(s′ − w), s′ = reflect s = 1 − s̄. -/
def wt (s w : ℂ) : ℂ := 1 / (s - w) - 1 / (reflect s - w)

theorem wt_eq (s w : ℂ) (h1 : s - w ≠ 0) (h2 : reflect s - w ≠ 0) :
    wt s w = (reflect s - s) / ((s - w) * (reflect s - w)) := by
  unfold wt
  field_simp
  ring

/-- on the border of the square, |wt s| ≤ 4|s − s′|/R² once R ≥ 2|s| + 4. -/
theorem norm_wt_le_border {s : ℂ} {R : ℝ} (hR : 2 * ‖s‖ + 4 ≤ R) :
    ∀ p ∈ RectangleBorder (zc R) (wc R), ‖wt s p‖ ≤ 4 * ‖s - reflect s‖ / R ^ 2 := by
  have hR0 : 0 < R := by linarith [norm_nonneg s]
  -- every point a with 2|a| + 2 ≤ R is at distance ≥ R/2 from the border
  have hdist : ∀ a : ℂ, 2 * ‖a‖ + 2 ≤ R → ∀ p ∈ RectangleBorder (zc R) (wc R), R / 2 ≤ ‖a - p‖ := by
    intro a ha p hp
    have hare : |a.re| ≤ ‖a‖ := Complex.abs_re_le_norm a
    have haim : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
    have h1 : |(a - p).re| ≤ ‖a - p‖ := Complex.abs_re_le_norm _
    have h2 : |(a - p).im| ≤ ‖a - p‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    have hare' := abs_le.mp hare
    have haim' := abs_le.mp haim
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      zc_re, zc_im, wc_re, wc_im] at hp
    rcases hp with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · -- bottom: p.im = −R
      have : R / 2 ≤ |a.im - p.im| := by rw [h']; rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    · -- left: p.re = 1 − R
      have : R / 2 ≤ |a.re - p.re| := by rw [h']; rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    · -- top: p.im = R
      have : R / 2 ≤ |a.im - p.im| := by rw [h']; rw [abs_of_nonpos (by linarith)]; linarith
      linarith
    · -- right: p.re = R
      have : R / 2 ≤ |a.re - p.re| := by rw [h']; rw [abs_of_nonpos (by linarith)]; linarith
      linarith
  intro p hp
  have hrs : ‖reflect s‖ ≤ 1 + ‖s‖ := by
    calc ‖reflect s‖ = ‖1 - conj s‖ := rfl
      _ ≤ ‖(1 : ℂ)‖ + ‖conj s‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one, Complex.norm_conj]
  have d1 := hdist s (by linarith) p hp
  have d2 := hdist (reflect s) (by linarith) p hp
  have h1 : s - p ≠ 0 := norm_pos_iff.mp (by linarith)
  have h2 : reflect s - p ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [wt_eq s p h1 h2, norm_div, norm_mul, norm_sub_rev (reflect s) s]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul d1 d2 (by positivity) (norm_nonneg _)
  nlinarith [norm_nonneg (s - reflect s)]

/-! ## §D. The square identity at a good height -/

/-- **Square identity.**  ξ(s) ≠ 0, Re s ≠ 1/2, R ≥ |s| + 2 with ζ ≠ 0 on Im = ±R, 1/2 ≤ Re ≤ 2:
(1/2πi)∮_{∂([1−R,R]×[−R,R])} wt s · ξ′/ξ = Σ_{|Im ρ| < R} m_ρ wt s ρ − ξ′/ξ(s) + ξ′/ξ(reflect s).
(ζ ≠ 0 on Re ∈ [1/2, 2] of the lines Im = ±R keeps ALL zeros of ξ off those lines: a zero ρ with
Re ρ < 1/2 would give the zero 1 − ρ with Re ∈ (1/2, 1) on the mirrored line —
Zeta23.WeilEF.completedZeta_ne_zero_on_horizontals.) -/
theorem square_identity {s : ℂ} (hxi : xi s ≠ 0) (hs : s.re ≠ 1 / 2) {R : ℝ} (hR : ‖s‖ + 2 ≤ R)
    (hζ : ∀ p : ℂ, (p.im = R ∨ p.im = -R) → 1 / 2 ≤ p.re → p.re ≤ 2 → riemannZeta p ≠ 0) :
    ∃ Z : Finset ℂ, ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R}) ∧
      RectangleIntegral' (fun p => wt s p * logDeriv xi p) (zc R) (wc R)
        = (∑ ρ ∈ Z, (zeroMult ρ : ℂ) * wt s ρ) - logDeriv xi s + logDeriv xi (reflect s) := by
  classical
  have hσ := abs_le.mp (Complex.abs_re_le_norm s)
  have ht := abs_le.mp (Complex.abs_im_le_norm s)
  have hR1 : 2 ≤ R := by linarith [norm_nonneg s]
  have hre : (zc R).re ≤ (wc R).re := by simp; linarith
  have him : (zc R).im ≤ (wc R).im := by simp; linarith
  have hmem : ∀ p : ℂ, p ∈ Rectangle (zc R) (wc R) ↔
      (1 - R ≤ p.re ∧ p.re ≤ R) ∧ (-R ≤ p.im ∧ p.im ≤ R) := by
    intro p
    simp only [Rectangle, Complex.mem_reProdIm, zc_re, zc_im, wc_re, wc_im,
      Set.uIcc_of_le (show (1 - R : ℝ) ≤ R by linarith),
      Set.uIcc_of_le (show (-R : ℝ) ≤ R by linarith), Set.mem_Icc]
  have hint : ∀ p : ℂ, Rectangle (zc R) (wc R) ∈ 𝓝 p ↔
      (1 - R < p.re ∧ p.re < R) ∧ (-R < p.im ∧ p.im < R) := by
    intro p
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him,
      zc_re, zc_im, wc_re, wc_im, Set.mem_Ioo, Set.mem_Ioo]
  -- no zero of ξ on the lines Im = ±R
  have hΛ := Zeta23.WeilEF.completedZeta_ne_zero_on_horizontals (c := 3 / 2) (R := R)
    (by norm_num) le_rfl hζ
  have hnoZ : ∀ p : ℂ, (p.im = R ∨ p.im = -R) → xi p ≠ 0 := by
    intro p hp h0
    have hnz := (xi_eq_zero_iff p).mp h0
    exact hΛ p hp (by linarith [hnz.2.1]) (by linarith [hnz.2.2])
      (Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hnz)
  -- the zero finset
  have hfin : {ρ : ℂ | IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R}.Finite :=
    (zetaSeam.finite_window (-R) R).subset (fun ρ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.le⟩)
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmem : ∀ ρ, ρ ∈ Z ↔ IsNontrivialZero ρ ∧ -R < ρ.im ∧ ρ.im < R := by
    intro ρ; rw [hZdef, Set.Finite.mem_toFinset]; rfl
  refine ⟨Z, hfin.coe_toFinset, ?_⟩
  -- the two poles of the weight
  have hsr : s ≠ reflect s := by
    intro h; apply hs
    have := congrArg Complex.re h
    simp [reflect] at this; linarith
  have hxi' : xi (reflect s) ≠ 0 := by rw [xi_reflect]; exact (map_ne_zero _).mpr hxi
  set Q : Finset ℂ := {s, reflect s} with hQdef
  have hZQ : Disjoint Z Q := by
    rw [Finset.disjoint_right]
    intro q hq hqZ
    have hz := (xi_eq_zero_iff q).mpr ((hZmem q).mp hqZ).1
    simp only [hQdef, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    exacts [hxi hz, hxi' hz]
  have hsint : Rectangle (zc R) (wc R) ∈ 𝓝 s := by
    rw [hint]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hs'int : Rectangle (zc R) (wc R) ∈ 𝓝 (reflect s) := by
    rw [hint]
    have e1 : (reflect s).re = 1 - s.re := by simp [reflect]
    have e2 : (reflect s).im = s.im := by simp [reflect]
    rw [e1, e2]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hQint : ∀ q ∈ Q, Rectangle (zc R) (wc R) ∈ 𝓝 q := by
    intro q hq
    simp only [hQdef, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    exacts [hsint, hs'int]
  have hf : AnalyticOnNhd ℂ xi (Rectangle (zc R) (wc R)) := fun p _ => xi_differentiable.analyticAt p
  have hg : ∀ p ∈ Rectangle (zc R) (wc R) \ (Q : Set ℂ), AnalyticAt ℂ (wt s) p := by
    rintro p ⟨_, hpQ⟩
    simp only [hQdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hpQ
    have hopen : IsOpen (({s, reflect s} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    apply DifferentiableOn.analyticAt (s := (({s, reflect s} : Set ℂ)ᶜ))
    · intro w hw
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
      have h1 : s - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw.1)
      have h2 : reflect s - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw.2)
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun w => 1 / (s - w) - 1 / (reflect s - w)) w
      fun_prop (disch := assumption)
    · exact hopen.mem_nhds (by simp [hpQ.1, hpQ.2])
  have hborder : ∀ p ∈ RectangleBorder (zc R) (wc R), xi p ≠ 0 := by
    intro p hp h0
    have hnz := (xi_eq_zero_iff p).mp h0
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      zc_re, zc_im, wc_re, wc_im] at hp
    rcases hp with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hnoZ p (Or.inr h') h0
    · linarith [hnz.2.1]
    · exact hnoZ p (Or.inl h') h0
    · linarith [hnz.2.2]
  have hZchar : ∀ p ∈ Rectangle (zc R) (wc R), xi p = 0 ↔ p ∈ Z := by
    intro p hp
    rw [hZmem, xi_eq_zero_iff]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem p).mp hp
    constructor
    · intro hnz
      refine ⟨hnz, lt_of_le_of_ne hi1 (fun h => ?_), lt_of_le_of_ne hi2 (fun h => ?_)⟩
      · exact hnoZ p (Or.inr h.symm) ((xi_eq_zero_iff p).mpr hnz)
      · exact hnoZ p (Or.inl h) ((xi_eq_zero_iff p).mpr hnz)
    · exact fun h => h.1
  have hZsub : (Z : Set ℂ) ⊆ Rectangle (zc R) (wc R) := by
    intro ρ hρ
    rw [Finset.mem_coe, hZmem] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    exact (hmem ρ).mpr ⟨⟨by linarith [h1.2.1], by linarith [h1.2.2]⟩, h2.le, h3.le⟩
  -- principal parts of the weight: −1/(w − s) at s, +1/(w − s′) at s′
  set r : ℂ → ℂ := fun q => if q = s then -1 else 1 with hrdef
  have hr1 : r s = -1 := by simp [hrdef]
  have hr2 : r (reflect s) = 1 := by simp [hrdef, hsr.symm]
  have hnear : ∀ q ∈ Q, (wt s - fun w => r q / (w - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
    intro q hq
    simp only [hQdef, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h
    · subst h
      have hne : reflect q - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hsr)
      have hc : ContinuousAt (fun w => -(1 / (reflect q - w))) q := by
        have h1 : ContinuousAt (fun w : ℂ => reflect q - w) q := by fun_prop
        exact (continuousAt_const.div h1 hne).neg
      have hO : (fun w => -(1 / (reflect q - w))) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      refine hO.congr' ?_ EventuallyEq.rfl
      have hev : ∀ᶠ w in 𝓝 q, reflect q - w ≠ 0 :=
        (continuous_const.sub continuous_id).continuousAt.eventually_ne hne
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with w hw hw2
      have hwq : w - q ≠ 0 := sub_ne_zero.mpr hw
      have hqw : q - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
      simp only [Pi.sub_apply, wt, hr1]
      field_simp
      ring
    · subst h
      have hne : s - reflect s ≠ 0 := sub_ne_zero.mpr hsr
      have hc : ContinuousAt (fun w => 1 / (s - w)) (reflect s) := by
        have h1 : ContinuousAt (fun w : ℂ => s - w) (reflect s) := by fun_prop
        exact continuousAt_const.div h1 hne
      have hO : (fun w => 1 / (s - w)) =O[𝓝[≠] (reflect s)] (1 : ℂ → ℂ) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      refine hO.congr' ?_ EventuallyEq.rfl
      have hev : ∀ᶠ w in 𝓝 (reflect s), s - w ≠ 0 :=
        (continuous_const.sub continuous_id).continuousAt.eventually_ne hne
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with w hw hw2
      have hwq : w - reflect s ≠ 0 := sub_ne_zero.mpr hw
      have hqw : reflect s - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
      simp only [Pi.sub_apply, wt, hr2]
      field_simp
      ring
  have key := rectangleIntegral'_mul_logDeriv_weightPoles hre him Z Q hZQ hQint hf hg hborder
    hZchar hZsub r hnear
  rw [key]
  have hZsum : ∑ ρ ∈ Z, (analyticOrderNatAt xi ρ : ℂ) * wt s ρ = ∑ ρ ∈ Z, (zeroMult ρ : ℂ) * wt s ρ :=
    Finset.sum_congr rfl (fun ρ hρ => by rw [analyticOrderNatAt_xi ((hZmem ρ).mp hρ).1])
  have hQsum : ∑ q ∈ Q, r q * logDeriv xi q = -logDeriv xi s + logDeriv xi (reflect s) := by
    rw [hQdef, Finset.sum_insert (by simpa using hsr), Finset.sum_singleton, hr1, hr2]
    ring
  rw [hZsum, hQsum]
  ring

/-! ## §E. Limits along the good heights -/

/-- the border integral tends to 0 along the good heights. -/
theorem tendsto_rectangleIntegral (s : ℂ) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    (hgood : ∀ j : ℕ, ∀ p : ℂ, (p.im = R j ∨ p.im = -R j) → 1 / 2 ≤ p.re → p.re ≤ 2 →
      riemannZeta p ≠ 0 ∧ ‖logDeriv riemannZeta p‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => RectangleIntegral' (fun p => wt s p * logDeriv xi p) (zc (R j)) (wc (R j)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := norm_logDeriv_xi_le_border
  set K : ℝ := 32 * ‖s - reflect s‖ * C * (Cg + 2) with hK
  -- the comparison sequence K log²(j+10)/(j+7) → 0
  have hlim : Tendsto (fun j : ℕ => K * (Real.log ((j : ℝ) + 10) ^ 2 / ((j : ℝ) + 7)))
      atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) 2 one_ne_zero
    have h2 : Tendsto (fun j : ℕ => (j : ℝ) + 10) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h3 := (h1.comp h2).const_mul K
    rw [mul_zero] at h3
    refine h3.congr (fun j => ?_)
    simp only [Function.comp_apply]
    ring_nf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun j => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (Nat.ceil (2 * ‖s‖))] with j hj
  have hRj := hR j
  have hj' : 2 * ‖s‖ ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hR4 : 2 * ‖s‖ + 4 ≤ R j := by linarith
  have hR2 : 2 ≤ R j := by linarith [norm_nonneg s]
  have hR0 : 0 < R j := by linarith
  set L : ℝ := Cg * Real.log ((j : ℝ) + 10) ^ 2 + 1 with hL
  have hlog10 : 1 ≤ Real.log ((j : ℝ) + 10) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hlogsq : Real.log ((j : ℝ) + 10) ≤ Real.log ((j : ℝ) + 10) ^ 2 := by nlinarith
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Cg * Real.log ((j : ℝ) + 10) ^ 2 := by positivity
    rw [hL]; linarith
  have hgoodL : ∀ p : ℂ, (p.im = R j ∨ p.im = -R j) → 1 / 2 ≤ p.re → p.re ≤ 2 →
      riemannZeta p ≠ 0 ∧ ‖logDeriv riemannZeta p‖ ≤ L :=
    fun p hp h1 h2 => ⟨(hgood j p hp h1 h2).1, by rw [hL]; linarith [(hgood j p hp h1 h2).2]⟩
  have hM : ∀ p ∈ RectangleBorder (zc (R j)) (wc (R j)),
      ‖wt s p * logDeriv xi p‖ ≤ (4 * ‖s - reflect s‖ / R j ^ 2) * (C * (L + Real.log (2 + R j))) := by
    intro p hp
    rw [norm_mul]
    exact mul_le_mul (norm_wt_le_border hR4 p hp) (hb L (R j) hL1 hR2 hgoodL p hp)
      (norm_nonneg _) (by positivity)
  have hI := norm_rectangleIntegral_le (f := fun p => wt s p * logDeriv xi p)
    (by simp; linarith) (by simp; linarith) hM
  simp only [zc_re, wc_re, zc_im, wc_im] at hI
  -- numerator: L + log(2 + R) ≤ (Cg + 2) log²(j+10)
  have hA : L + Real.log (2 + R j) ≤ (Cg + 2) * Real.log ((j : ℝ) + 10) ^ 2 := by
    have h1 : Real.log (2 + R j) ≤ Real.log ((j : ℝ) + 10) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [hL]; nlinarith
  have hB : (4 * ‖s - reflect s‖ / R j ^ 2) * (C * (L + Real.log (2 + R j)))
      * (2 * (R j - (1 - R j)) + 2 * (R j - -R j))
      ≤ K * (Real.log ((j : ℝ) + 10) ^ 2 / ((j : ℝ) + 7)) := by
    calc (4 * ‖s - reflect s‖ / R j ^ 2) * (C * (L + Real.log (2 + R j)))
          * (2 * (R j - (1 - R j)) + 2 * (R j - -R j))
        ≤ (4 * ‖s - reflect s‖ / R j ^ 2) * (C * ((Cg + 2) * Real.log ((j : ℝ) + 10) ^ 2))
          * (8 * R j) := by
          apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hC.le) (by positivity)
      _ = K * Real.log ((j : ℝ) + 10) ^ 2 / R j := by
          rw [hK]; field_simp; ring
      _ ≤ K * Real.log ((j : ℝ) + 10) ^ 2 / ((j : ℝ) + 7) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hRj.1
      _ = K * (Real.log ((j : ℝ) + 10) ^ 2 / ((j : ℝ) + 7)) := by ring
  -- ‖(1/2πi) • ∮‖ ≤ ‖∮‖
  have h2π : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  calc ‖RectangleIntegral' (fun p => wt s p * logDeriv xi p) (zc (R j)) (wc (R j))‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖
        * ‖RectangleIntegral (fun p => wt s p * logDeriv xi p) (zc (R j)) (wc (R j))‖ := by
        rw [RectangleIntegral', norm_smul]
    _ ≤ 1 * ‖RectangleIntegral (fun p => wt s p * logDeriv xi p) (zc (R j)) (wc (R j))‖ :=
        mul_le_mul_of_nonneg_right h2π (norm_nonneg _)
    _ ≤ K * (Real.log ((j : ℝ) + 10) ^ 2 / ((j : ℝ) + 7)) := by rw [one_mul]; exact hI.trans hB

/-- a point off the zero set is at distance ≫_s (1 + |γ_ρ|²)^{1/2} from every zero ρ. -/
theorem exists_normSq_sub_ge {s : ℂ} (hxi : xi s ≠ 0) : ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ,
    IsNontrivialZero ρ → c * (1 + Complex.normSq (gammaOf ρ)) ≤ Complex.normSq (s - ρ) := by
  classical
  set t : ℝ := s.im with ht
  have hfin := zetaSeam.finite_window (t - 1) (t + 1)
  set F : Finset ℂ := hfin.toFinset with hF
  have hmemF : ∀ ρ : ℂ, ρ ∈ F ↔ IsNontrivialZero ρ ∧ t - 1 < ρ.im ∧ ρ.im ≤ t + 1 := by
    intro ρ; rw [hF, Set.Finite.mem_toFinset]; rfl
  -- a positive lower bound d for normSq (s − ρ) over the finitely many zeros at height within 1 of t
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ, 0 < d ∧ ∀ ρ ∈ F, d ≤ Complex.normSq (s - ρ) := by
    by_cases hne : F.Nonempty
    · refine ⟨F.inf' hne (fun ρ => Complex.normSq (s - ρ)), ?_, fun ρ hρ => Finset.inf'_le _ hρ⟩
      obtain ⟨ρ₀, hρ₀, heq⟩ := Finset.exists_mem_eq_inf' hne (fun ρ => Complex.normSq (s - ρ))
      rw [heq]
      refine Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun h => hxi ?_))
      rw [h]
      exact (xi_eq_zero_iff ρ₀).mpr ((hmemF ρ₀).mp hρ₀).1
    · exact ⟨1, one_pos, fun ρ hρ => (hne ⟨ρ, hρ⟩).elim⟩
  refine ⟨min (d / (5 / 4 + (|t| + 1) ^ 2)) (1 / (13 / 4 + 2 * t ^ 2)), lt_min (by positivity)
    (by positivity), fun ρ hρ => ?_⟩
  have hN : Complex.normSq (gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]; ring
  have hβ1 := hρ.2.1
  have hβ2 := hρ.2.2
  have hNle : Complex.normSq (gammaOf ρ) ≤ ρ.im ^ 2 + 1 / 4 := by
    rw [hN]; nlinarith
  have hns : Complex.normSq (s - ρ) = (s.re - ρ.re) ^ 2 + (t - ρ.im) ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ht]; ring
  by_cases hwin : t - 1 < ρ.im ∧ ρ.im ≤ t + 1
  · -- a nearby zero: use d
    have hρF : ρ ∈ F := (hmemF ρ).mpr ⟨hρ, hwin⟩
    have h1 : 1 + Complex.normSq (gammaOf ρ) ≤ 5 / 4 + (|t| + 1) ^ 2 := by
      have : ρ.im ^ 2 ≤ (|t| + 1) ^ 2 := by
        have h : |ρ.im| ≤ |t| + 1 :=
          abs_le.mpr ⟨by linarith [hwin.1, neg_abs_le t], by linarith [hwin.2, le_abs_self t]⟩
        calc ρ.im ^ 2 = |ρ.im| ^ 2 := (sq_abs _).symm
          _ ≤ (|t| + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    calc min (d / (5 / 4 + (|t| + 1) ^ 2)) (1 / (13 / 4 + 2 * t ^ 2)) * (1 + Complex.normSq (gammaOf ρ))
        ≤ (d / (5 / 4 + (|t| + 1) ^ 2)) * (5 / 4 + (|t| + 1) ^ 2) := by
          apply mul_le_mul (min_le_left _ _) h1
            (by linarith [Complex.normSq_nonneg (gammaOf ρ)]) (by positivity)
      _ = d := by field_simp
      _ ≤ Complex.normSq (s - ρ) := hd ρ hρF
  · -- a far zero: |t − Im ρ| ≥ 1
    have hfar : 1 ≤ (t - ρ.im) ^ 2 := by
      rcases not_and_or.mp hwin with h | h
      · push Not at h; nlinarith
      · push Not at h; nlinarith
    have h1 : 1 + Complex.normSq (gammaOf ρ) ≤ (13 / 4 + 2 * t ^ 2) * (t - ρ.im) ^ 2 := by
      have : ρ.im ^ 2 ≤ 2 * (ρ.im - t) ^ 2 + 2 * t ^ 2 := by nlinarith [sq_nonneg (ρ.im - 2 * t)]
      nlinarith
    calc min (d / (5 / 4 + (|t| + 1) ^ 2)) (1 / (13 / 4 + 2 * t ^ 2)) * (1 + Complex.normSq (gammaOf ρ))
        ≤ (1 / (13 / 4 + 2 * t ^ 2)) * ((13 / 4 + 2 * t ^ 2) * (t - ρ.im) ^ 2) := by
          apply mul_le_mul (min_le_right _ _) h1
            (by linarith [Complex.normSq_nonneg (gammaOf ρ)]) (by positivity)
      _ = (t - ρ.im) ^ 2 := by field_simp
      _ ≤ Complex.normSq (s - ρ) := by rw [hns]; nlinarith

/-- |wt s ρ| ≤ C_s/(1 + |γ_ρ|²) on the zero set. -/
theorem norm_wt_le_zero {s : ℂ} (hxi : xi s ≠ 0) : ∃ C : ℝ, ∀ ρ : ℂ, IsNontrivialZero ρ →
    ‖wt s ρ‖ ≤ C / (1 + Complex.normSq (gammaOf ρ)) := by
  have hxi' : xi (reflect s) ≠ 0 := by
    rw [xi_reflect]; exact (map_ne_zero _).mpr hxi
  obtain ⟨c, hc, h⟩ := exists_normSq_sub_ge hxi
  obtain ⟨c', hc', h'⟩ := exists_normSq_sub_ge hxi'
  refine ⟨‖reflect s - s‖ / 2 * (1 / c + 1 / c'), fun ρ hρ => ?_⟩
  have hz : xi ρ = 0 := (xi_eq_zero_iff ρ).mpr hρ
  have h1 : s - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hxi (e ▸ hz))
  have h2 : reflect s - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hxi' (e ▸ hz))
  set N : ℝ := 1 + Complex.normSq (gammaOf ρ) with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith [Complex.normSq_nonneg (gammaOf ρ)]
  have ha : c * N ≤ ‖s - ρ‖ ^ 2 := by rw [Complex.sq_norm]; exact h ρ hρ
  have hb : c' * N ≤ ‖reflect s - ρ‖ ^ 2 := by rw [Complex.sq_norm]; exact h' ρ hρ
  have ha0 : 0 < ‖s - ρ‖ := norm_pos_iff.mpr h1
  have hb0 : 0 < ‖reflect s - ρ‖ := norm_pos_iff.mpr h2
  rw [wt_eq s ρ h1 h2, norm_div, norm_mul]
  -- 1/(ab) ≤ (1/a² + 1/b²)/2 ≤ (1/(cN) + 1/(c′N))/2
  have key : 1 / (‖s - ρ‖ * ‖reflect s - ρ‖) ≤ (1 / (c * N) + 1 / (c' * N)) / 2 := by
    have hab : 1 / (‖s - ρ‖ * ‖reflect s - ρ‖) ≤ (1 / ‖s - ρ‖ ^ 2 + 1 / ‖reflect s - ρ‖ ^ 2) / 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (‖s - ρ‖ - ‖reflect s - ρ‖), mul_pos ha0 hb0]
    have h3 : 1 / ‖s - ρ‖ ^ 2 ≤ 1 / (c * N) :=
      one_div_le_one_div_of_le (by positivity) ha
    have h4 : 1 / ‖reflect s - ρ‖ ^ 2 ≤ 1 / (c' * N) :=
      one_div_le_one_div_of_le (by positivity) hb
    linarith
  calc ‖reflect s - s‖ / (‖s - ρ‖ * ‖reflect s - ρ‖)
      = ‖reflect s - s‖ * (1 / (‖s - ρ‖ * ‖reflect s - ρ‖)) := by ring
    _ ≤ ‖reflect s - s‖ * ((1 / (c * N) + 1 / (c' * N)) / 2) :=
        mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = ‖reflect s - s‖ / 2 * (1 / c + 1 / c') / N := by
        field_simp

/-- Σ_ρ m_ρ φ(ρ) converges absolutely whenever |φ(ρ)| ≤ C/(1 + |γ_ρ|²) on the zeros. -/
theorem summable_mult_mul {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ ρ : ℂ, IsNontrivialZero ρ → ‖φ ρ‖ ≤ C / (1 + Complex.normSq (gammaOf ρ))) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zeroMult ρ : ℂ) * φ ρ) := by
  have hS := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left C
  refine Summable.of_norm_bounded hS (fun ρ => ?_)
  have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
  rw [norm_mul, Complex.norm_natCast]
  have hN : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  calc (zeroMult (ρ : ℂ) : ℝ) * ‖φ ρ‖
      ≤ (zeroMult (ρ : ℂ) : ℝ) * (C / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left (hφ ρ hρ) (Nat.cast_nonneg _)
    _ = C * ((zeroMult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        field_simp

/-- the finite zero sums over {|Im ρ| < R_j} converge to the tsum (generic form of
Zeta23.WeilEF.zero_sum_limit). -/
theorem zero_sum_limit_gen {φ : ℂ → ℂ}
    (hφ : Summable (fun ρ : zetaZeroConfig.carrier => (zeroMult ρ : ℂ) * φ ρ))
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8) {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * φ ρ) atTop
      (𝓝 (∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℂ) * φ ρ)) := by
  classical
  set g : zetaZeroConfig.carrier → ℂ := fun ρ => (zeroMult ρ : ℂ) * φ ρ with hg
  have hsum : Summable g := hφ
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  set sF : ℕ → Finset zetaZeroConfig.carrier :=
    fun j => (Z j).subtype (· ∈ zetaZeroConfig.carrier) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ sF j, g x = ∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * φ ρ := by
    intro j
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Z j)
      (p := (· ∈ zetaZeroConfig.carrier)) (fun ρ : ℂ => (zeroMult ρ : ℂ) * φ ρ)
    have h2 : (Z j).filter (· ∈ zetaZeroConfig.carrier) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemZ j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
  have hRmono : ∀ i j : ℕ, i ≤ j → R i ≤ R j := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2, (hR j).1]
  have hmono : Monotone sF := by
    intro i j hij x hx
    rw [Finset.mem_subtype, hmemZ] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have := hRmono i j hij
    exact ⟨h1, by linarith, by linarith⟩
  have hexh : ∀ b : Finset zetaZeroConfig.carrier, ∃ j, b ≤ sF j := by
    intro b
    set M : ℝ := ∑ x ∈ b, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ b, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : zetaZeroConfig.carrier => |((x : ℂ)).im|)
        (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have hx0 : IsNontrivialZero (x : ℂ) := x.2
    have habs := abs_le.mp (hMle x hx)
    have hRj := (hR j).1
    exact ⟨hx0, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto sF atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset zetaZeroConfig.carrier => ∑ x ∈ S, g x) atTop
      (𝓝 (∑' x, g x)) := by
    have hHas := hsum.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hHas
    exact hHas
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]

theorem summable_wt {s : ℂ} (hxi : xi s ≠ 0) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zeroMult ρ : ℂ) * wt s ρ) := by
  obtain ⟨C, hC⟩ := norm_wt_le_zero hxi
  exact summable_mult_mul hC

/-- **ξ′/ξ(s) − ξ′/ξ(1 − s̄) = Σ'_ρ m_ρ [1/(s−ρ) − 1/(1 − s̄ − ρ)]**  (ξ(s) ≠ 0; the tsum converges
absolutely by summable_wt hxi). -/
theorem logDeriv_xi_sub_reflect {s : ℂ} (hxi : xi s ≠ 0) :
    logDeriv xi s - logDeriv xi (reflect s)
      = ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℂ) * wt s ρ := by
  by_cases hs : s.re = 1 / 2
  · -- s = reflect s and the weight vanishes identically
    have hsr : reflect s = s := by
      apply Complex.ext <;> norm_num [reflect, hs]
    have hwt : ∀ w, wt s w = 0 := fun w => by simp [wt, hsr]
    simp [hsr, hwt]
  obtain ⟨Cg, hCg, R, hR⟩ := Zeta23.WeilEF.good_heights
  have hRb : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 := fun j => ⟨(hR j).1, (hR j).2.1⟩
  have hgood : ∀ j : ℕ, ∀ p : ℂ, (p.im = R j ∨ p.im = -R j) → 1 / 2 ≤ p.re → p.re ≤ 2 →
      riemannZeta p ≠ 0 ∧ ‖logDeriv riemannZeta p‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2 :=
    fun j => (hR j).2.2
  have hZex : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) := by
    intro j
    have hfin : {ρ : ℂ | IsNontrivialZero ρ ∧ -R j < ρ.im ∧ ρ.im < R j}.Finite :=
      (zetaSeam.finite_window (-R j) (R j)).subset (fun ρ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.le⟩)
    exact ⟨hfin.toFinset, hfin.coe_toFinset⟩
  choose Z hZ using hZex
  have hlim := zero_sum_limit_gen (summable_wt hxi) hRb hZ
  have hI := tendsto_rectangleIntegral s hCg hRb hgood
  have hev : ∀ᶠ j : ℕ in atTop,
      RectangleIntegral' (fun p => wt s p * logDeriv xi p) (zc (R j)) (wc (R j))
        = (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * wt s ρ) - logDeriv xi s + logDeriv xi (reflect s) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil ‖s‖)] with j hj
    have hRj : ‖s‖ + 2 ≤ R j := by
      have h1 := (hRb j).1
      have h2 : (⌈‖s‖⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
      linarith [Nat.le_ceil ‖s‖]
    obtain ⟨Z', hZ', hid⟩ := square_identity hxi hs hRj (fun p hp h1 h2 => (hgood j p hp h1 h2).1)
    have : Z' = Z j := Finset.coe_injective (hZ'.trans (hZ j).symm)
    rw [← this]
    exact hid
  have h2 : Tendsto (fun j => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * wt s ρ) - logDeriv xi s
      + logDeriv xi (reflect s)) atTop (𝓝 0) := hI.congr' hev
  have h3 : Tendsto (fun j => (∑ ρ ∈ Z j, (zeroMult ρ : ℂ) * wt s ρ) - logDeriv xi s
      + logDeriv xi (reflect s)) atTop
      (𝓝 ((∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℂ) * wt s ρ) - logDeriv xi s
        + logDeriv xi (reflect s))) :=
    (hlim.sub_const _).add_const _
  have := tendsto_nhds_unique h2 h3
  linear_combination this

/-! ## §F. Real parts: the partial-fraction formula for Re ξ′/ξ, and positivity -/

theorem re_one_div (s ρ : ℂ) : ((1 : ℂ) / (s - ρ)).re = (s.re - ρ.re) / Complex.normSq (s - ρ) := by
  rw [one_div, Complex.inv_re, Complex.sub_re]

theorem re_wt (s ρ : ℂ) :
    (wt s ρ).re = ((1 : ℂ) / (s - ρ)).re + ((1 : ℂ) / (s - reflect ρ)).re := by
  have h : reflect s - ρ = -conj (s - reflect ρ) := by
    simp only [reflect, map_sub, map_one, Complex.conj_conj]; ring
  unfold wt
  rw [Complex.sub_re, h, one_div, one_div, one_div, Complex.inv_re, Complex.inv_re, Complex.inv_re,
    Complex.normSq_neg, Complex.normSq_conj, Complex.neg_re, Complex.conj_re]
  ring

theorem summable_re_one_div {s : ℂ} (hxi : xi s ≠ 0) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℝ) * ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ))) := by
  obtain ⟨c, hc, h⟩ := exists_normSq_sub_ge hxi
  have hS := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left ((|s.re| + 1) / c)
  refine Summable.of_norm_bounded hS (fun ρ => ?_)
  have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
  set N : ℝ := 1 + Complex.normSq (gammaOf (ρ : ℂ)) with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  have hcN : c * N ≤ Complex.normSq (s - ρ) := h ρ hρ
  have hpos : 0 < Complex.normSq (s - ρ) := lt_of_lt_of_le (by positivity) hcN
  have hnum : |s.re - (ρ : ℂ).re| ≤ |s.re| + 1 := by
    have := hρ.2.1; have := hρ.2.2
    calc |s.re - (ρ : ℂ).re| ≤ |s.re| + |(ρ : ℂ).re| := abs_sub _ _
      _ ≤ |s.re| + 1 := by rw [abs_of_pos (a := (ρ : ℂ).re) (by assumption)]; linarith
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_div, abs_of_pos hpos]
  calc (zeroMult (ρ : ℂ) : ℝ) * (|s.re - (ρ : ℂ).re| / Complex.normSq (s - ρ))
      ≤ (zeroMult (ρ : ℂ) : ℝ) * ((|s.re| + 1) / (c * N)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact div_le_div₀ (by positivity) hnum (by positivity) hcN
    _ = (|s.re| + 1) / c * ((zeroMult (ρ : ℂ) : ℝ) / N) := by
        field_simp

/-- the involution ρ ↦ 1 − ρ̄ of the zero set. -/
def reflectEquiv : zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun ρ := ⟨reflect ρ, zetaZeroConfig.reflect_mem ρ ρ.2⟩
  invFun ρ := ⟨reflect ρ, zetaZeroConfig.reflect_mem ρ ρ.2⟩
  left_inv ρ := by ext; simp [reflect]
  right_inv ρ := by ext; simp [reflect]

theorem tsum_re_one_div_reflect (s : ℂ) :
    ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - reflect ρ)).re
      = ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re := by
  rw [← Equiv.tsum_eq reflectEquiv
    (fun ρ : zetaZeroConfig.carrier => (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re)]
  refine tsum_congr (fun ρ => ?_)
  have hm : zeroMult (reflect (ρ : ℂ)) = zeroMult ρ := zetaZeroConfig.mult_reflect ρ ρ.2
  simp only [reflectEquiv, Equiv.coe_fn_mk, hm]

/-- **Re ξ′/ξ(s) = Σ'_ρ m_ρ (σ − β)/|s − ρ|²** over the distinct nontrivial zeros ρ = β + iγ of ζ
weighted by their multiplicity, for every s with ξ(s) ≠ 0 — inside the strip too.  The tsum is a
genuine sum, not Lean's junk value 0: summable_re_one_div hxi proves absolute convergence. -/
theorem re_logDeriv_xi_eq_tsum {s : ℂ} (hxi : xi s ≠ 0) :
    (logDeriv xi s).re = ∑' ρ : zetaZeroConfig.carrier,
      (zeroMult ρ : ℝ) * ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ)) := by
  have hmain := congrArg Complex.re (logDeriv_xi_sub_reflect hxi)
  rw [logDeriv_xi_reflect, Complex.sub_re, Complex.neg_re, Complex.conj_re, sub_neg_eq_add,
    Complex.re_tsum (summable_wt hxi)] at hmain
  have hterm : ∀ ρ : zetaZeroConfig.carrier, ((zeroMult ρ : ℂ) * wt s ρ).re
      = (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re
        + (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - reflect ρ)).re := by
    intro ρ
    rw [show (zeroMult (ρ : ℂ) : ℂ) = ((zeroMult (ρ : ℂ) : ℝ) : ℂ) by norm_cast,
      Complex.re_ofReal_mul, re_wt]
    ring
  simp_rw [hterm] at hmain
  have hS1 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re :=
    (summable_re_one_div hxi).congr (fun ρ => by rw [re_one_div])
  have hS2 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - reflect ρ)).re := by
    have := (Equiv.summable_iff reflectEquiv (f := fun ρ : zetaZeroConfig.carrier =>
      (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re)).mpr hS1
    refine this.congr (fun ρ => ?_)
    have hm : zeroMult (reflect (ρ : ℂ)) = zeroMult ρ := zetaZeroConfig.mult_reflect ρ ρ.2
    simp only [Function.comp_apply, reflectEquiv, Equiv.coe_fn_mk, hm]
  rw [hS1.tsum_add hS2, tsum_re_one_div_reflect, ← two_mul] at hmain
  have : (logDeriv xi s).re
      = ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℝ) * ((1 : ℂ) / (s - ρ)).re := by
    linarith
  rw [this]
  exact tsum_congr (fun ρ => by rw [re_one_div])

/-- ζ has a nontrivial zero (Riemann–von Mangoldt: N(T,2T) ≫ T log T). -/
theorem exists_isNontrivialZero : ∃ ρ : ℂ, IsNontrivialZero ρ := by
  have hRvM := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  have h1 := Zeta23.Assembly.eventually_N_ge zetaZeroConfig hRvM
  have h2 : ∀ᶠ T : ℝ in atTop, 4 * Real.pi < T * l T :=
    Zeta23.Assembly.tendsto_Tl_atTop.eventually_gt_atTop _
  obtain ⟨T, hT1, hT2⟩ := (h1.and h2).exists
  have hpos : (0 : ℝ) < (zetaZeroConfig.N T (2 * T) : ℝ) := by
    refine lt_of_lt_of_le ?_ hT1
    rw [lt_div_iff₀ (by positivity), zero_mul]
    linarith [Real.pi_pos]
  have hne : (zetaZeroConfig.window T (2 * T)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [ZeroConfig.N, h] at hpos
  obtain ⟨ρ, hρ, _⟩ := hne
  exact ⟨ρ, hρ⟩

theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  rw [Ne, xi_eq_zero_iff]
  rintro ⟨_, _, h⟩
  linarith

end ZeroFree

open ZeroFree in
/-- **Re ξ′/ξ(s) > 0 for Re s ≥ 1.** -/
theorem re_logDeriv_xi_pos {s : ℂ} (hs : 1 ≤ s.re) : 0 < (logDeriv xi s).re := by
  have hxi := xi_ne_zero_of_one_le_re hs
  rw [re_logDeriv_xi_eq_tsum hxi]
  have hsum := summable_re_one_div hxi
  have hpos : ∀ ρ : zetaZeroConfig.carrier,
      0 < (zeroMult ρ : ℝ) * ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ)) := by
    intro ρ
    have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hm : (1 : ℝ) ≤ zeroMult (ρ : ℂ) := by exact_mod_cast zetaSeam.one_le_mult ρ hρ
    have h1 : 0 < s.re - (ρ : ℂ).re := by linarith [hρ.2.2]
    have h2 : 0 < Complex.normSq (s - ρ) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun h => by rw [h] at hs; linarith [hρ.2.2]))
    exact mul_pos (by linarith) (div_pos h1 h2)
  obtain ⟨ρ₀, hρ₀⟩ := exists_isNontrivialZero
  exact hsum.tsum_pos (fun ρ => (hpos ρ).le) ⟨ρ₀, hρ₀⟩ (hpos _)

theorem xiDeriv_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiDeriv s ≠ 0 := by
  have h := re_logDeriv_xi_pos hs
  intro h0
  have : logDeriv xi s = 0 := by
    rw [logDeriv_apply, show deriv xi s = xiDeriv s from rfl, h0, zero_div]
  rw [this] at h
  simp at h

theorem xiDeriv_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xiDeriv s ≠ 0 := by
  have h1 : 1 ≤ (1 - s).re := by simp; linarith
  have := xiDeriv_ne_zero_of_one_le_re h1
  rw [xiDeriv_one_sub] at this
  exact neg_ne_zero.mp this

/-- **(F2), unconditionally**: every zero of ξ′ lies in the open critical strip. -/
theorem xiDerivZerosInStrip_holds : XiDerivZerosInStrip := by
  intro ρ hρ
  by_contra h
  rcases not_and_or.mp h with h1 | h1
  · exact xiDeriv_ne_zero_of_re_nonpos (not_lt.mp h1) hρ
  · exact xiDeriv_ne_zero_of_one_le_re (not_lt.mp h1) hρ

end XiPrime
end Zeta23
