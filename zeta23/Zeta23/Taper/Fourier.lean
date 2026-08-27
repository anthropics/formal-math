/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Fourier.lean  (Fourier-side facts about the taper).
Canonical text: the paper, §2.2 [subsec:family]:
  "Thus φ̂ and Φ are real, even, entire; φ̂(0) ≤ L, Φ(0) = aL; φ̂² = Â_φ and Φ² = ĝ on ℝ;
   ∫_ℝ Φ² = 2π g(0) = 2π bL; g and A_φ are even".
Conventions: generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's
side condition is 1 ≤ w ≤ L/8 [eq:wrange]; each lemma carries the minimal hypothesis it needs.
The decay needed for integrability is taken directly
from Zeta23/Poisson/PaperFT.lean (norm_paperFT_le, norm_paperFT_mul_sq_le).

MATHLIB INVENTORY, what this file leans on:
* dictionary  Zeta23.paperFT_ofReal_eq_fourier : paperFT f s = 𝓕 f (-s/(2π))  (PaperFT.lean);
* convolution theorem  Real.fourier_mul_convolution_eq  (Mathlib/Analysis/Fourier/Convolution.lean)
  for integrable + continuous f₁ f₂ : ℝ → ℂ, 𝓕 (f₁ ⋆[mul ℂ ℂ] f₂) = 𝓕 f₁ · 𝓕 f₂ — the paper's
  autocorrelation (v ⋆ v)(y) = ∫ v(u) v(u+y) du coincides with Mathlib's convolution for EVEN v;
* Fourier inversion  MeasureTheory.Integrable.fourierInv_fourier_eq  (Mathlib/Analysis/Fourier/
  Inversion.lean): f, 𝓕 f integrable, f continuous at v ⇒ 𝓕⁻ (𝓕 f) v = f v.  "Plancherel"
  ∫ φ̂² = 2π ∫ φ² is obtained as inversion of Â_φ = φ̂² at 0 (no L² theory needed);
* smoothness  Real.contDiff_fourier  (Mathlib/Analysis/Fourier/FourierTransformDeriv.lean);
* integrable_inv_one_add_sq  (dominating function (1+r²)⁻¹ for the decay |φ̂(r)| ≤ min(C₀, C₂/r²)).
-/
import Mathlib
import Zeta23.Taper.Strip

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate

namespace Zeta23

/-! ### ℂ-specialized restatements of RCLike-generic integral lemmas
(same workaround as `integral_const_mul_C` in PaperFT.lean: `rw` with the
RCLike-stated lemma can fail to unify the `NormedAddCommGroup ℂ` instance path). -/

theorem integral_ofReal_C (f : ℝ → ℝ) : ∫ x, (f x : ℂ) = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal

theorem integral_conj_C (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj

theorem integral_re_C {f : ℝ → ℂ} (hf : Integrable f) : ∫ x, (f x).re = (∫ x, f x).re :=
  integral_re hf

namespace Taper

/-! ## Generic facts about the paper-convention transform `h_v(z) = ∫ v(u) e^{izu} du` of a REAL
function `v`.  Everything in the [eq:PhigA] sentence is an instance of these with `v = φ` or `v = φ²`. -/

section Generic

variable {v : ℝ → ℝ}

/-- For real `v`: `conj h_v(z) = h_v(−conj z)`. -/
theorem conj_paperFT_ofReal (v : ℝ → ℝ) (z : ℂ) :
    conj (paperFT (fun u => (v u : ℂ)) z) = paperFT (fun u => (v u : ℂ)) (-conj z) := by
  rw [paperFT_def, paperFT_def, ← integral_conj_C]
  congr 1 with u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- For even `v`: `h_v(−z) = h_v(z)` (all complex `z`). -/
theorem paperFT_neg_of_even (hv : ∀ u, v (-u) = v u) (z : ℂ) :
    paperFT (fun u => (v u : ℂ)) (-z) = paperFT (fun u => (v u : ℂ)) z := by
  rw [paperFT_def, paperFT_def]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1 with u
  rw [hv]
  congr 1
  push_cast
  ring_nf

/-- For real even `v` and real `r`, `h_v(r)` is real. -/
theorem paperFT_ofReal_eq_re (hv : ∀ u, v (-u) = v u) (r : ℝ) :
    paperFT (fun u => (v u : ℂ)) r = ((paperFT (fun u => (v u : ℂ)) r).re : ℂ) := by
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  rw [conj_paperFT_ofReal, Complex.conj_ofReal, paperFT_neg_of_even hv]

/-- `h_v` restricted to ℝ is smooth when `v` is continuous with compact support
(via the dictionary to Mathlib's `𝓕` and `Real.contDiff_fourier`). Stated for complex-valued `f`. -/
theorem contDiff_paperFT_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (n : ℕ∞) : ContDiff ℝ n (fun r : ℝ => paperFT f r) := by
  have h1 : ContDiff ℝ n (𝓕 f) := by
    apply Real.contDiff_fourier
    intro k _
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact hs.norm.mul_left
  have h2 : (fun r : ℝ => paperFT f r) = fun r => 𝓕 f (-r / (2 * π)) :=
    funext (paperFT_ofReal_eq_fourier f)
  rw [h2]
  exact h1.comp (by fun_prop)

theorem contDiff_re_paperFT_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (n : ℕ∞) : ContDiff ℝ n (fun r : ℝ => (paperFT f r).re) :=
  Complex.reCLM.contDiff.comp (contDiff_paperFT_ofReal hf hs n)

/-- A continuous `h : ℝ → ℝ` with `|h r| (1 + r²) ≤ K` is integrable (dominated by `K/(1+r²)`). -/
theorem integrable_of_abs_mul_one_add_sq_le {h : ℝ → ℝ} (hc : Continuous h) {K : ℝ}
    (hK : ∀ r, |h r| * (1 + r ^ 2) ≤ K) : Integrable h := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hc.aestronglyMeasurable ?_
  refine Eventually.of_forall fun r => ?_
  have hpos : 0 < 1 + r ^ 2 := by positivity
  rw [Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hK r

/-- Integrability of `(Re h_f)²` and `(Re h_f)² |r|` on ℝ for `f ∈ C_c²`, from the decay
[eq:hfbound]: `|h_f(r)| ≤ ‖f‖₁` and `|h_f(r)| r² ≤ ‖f''‖₁` (Zeta23.norm_paperFT_le / norm_paperFT_mul_sq_le). -/
theorem integrable_re_paperFT_sq_and {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun r : ℝ => (paperFT f r).re ^ 2) ∧
      Integrable (fun r : ℝ => (paperFT f r).re ^ 2 * |r|) := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  set C₀ : ℝ := ∫ u, ‖f u‖
  set C₂ : ℝ := ∫ u, ‖deriv (deriv f) u‖
  set K : ℝ := C₀ + C₂
  -- pointwise decay at real points
  have hG : ∀ r : ℝ, ‖paperFT f r‖ ≤ C₀ := by
    intro r
    simpa using norm_paperFT_le hfi hsupp (r : ℂ)
  have hG2 : ∀ r : ℝ, ‖paperFT f r‖ * r ^ 2 ≤ C₂ := by
    intro r
    have := norm_paperFT_mul_sq_le hf hsupp (r : ℂ)
    simpa [sq_abs] using this
  have hGK : ∀ r : ℝ, ‖paperFT f r‖ * (1 + r ^ 2) ≤ K := by
    intro r
    have := hG r; have := hG2 r
    simp only [K]; nlinarith
  have hGr : ∀ r : ℝ, ‖paperFT f r‖ * |r| ≤ K := by
    intro r
    refine le_trans ?_ (hGK r)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    nlinarith [abs_nonneg r, sq_abs r]
  have hre : ∀ r : ℝ, (paperFT f r).re ^ 2 ≤ ‖paperFT f r‖ ^ 2 := fun r =>
    sq_le_sq' (by linarith [abs_le.mp (Complex.abs_re_le_norm (paperFT f r))])
      (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  have hC₀ : 0 ≤ C₀ := integral_nonneg fun _ => norm_nonneg _
  have hcont : Continuous fun r : ℝ => (paperFT f r).re :=
    (contDiff_re_paperFT_ofReal hf.continuous hcs 0).continuous
  constructor
  · apply integrable_of_abs_mul_one_add_sq_le (by fun_prop) (K := C₀ * K)
    intro r
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (paperFT f r).re ^ 2 * (1 + r ^ 2)
        ≤ ‖paperFT f r‖ ^ 2 * (1 + r ^ 2) := mul_le_mul_of_nonneg_right (hre r) (by positivity)
      _ = ‖paperFT f r‖ * (‖paperFT f r‖ * (1 + r ^ 2)) := by ring
      _ ≤ C₀ * K := mul_le_mul (hG r) (hGK r) (by positivity) hC₀
  · apply integrable_of_abs_mul_one_add_sq_le (by fun_prop) (K := K * K)
    intro r
    rw [abs_of_nonneg (by positivity)]
    calc (paperFT f r).re ^ 2 * |r| * (1 + r ^ 2)
        ≤ ‖paperFT f r‖ ^ 2 * |r| * (1 + r ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hre r) (abs_nonneg r))
            (by positivity)
      _ = (‖paperFT f r‖ * |r|) * (‖paperFT f r‖ * (1 + r ^ 2)) := by ring
      _ ≤ K * K := mul_le_mul (hGr r) (hGK r) (by positivity) (le_trans (by positivity) (hGr r))

/-! ### The paper's autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] versus Mathlib's convolution -/

/-- `v ⋆ v` is even (no hypothesis on `v`: substitute `u ↦ u − y`). -/
theorem autocorr_neg (v : ℝ → ℝ) (y : ℝ) : Params.autocorr v (-y) = Params.autocorr v y := by
  simp only [Params.autocorr]
  rw [← integral_add_right_eq_self _ y]
  congr 1 with u
  rw [mul_comm]
  ring_nf

/-- For EVEN real `v`, the complexified autocorrelation is Mathlib's convolution `v_ℂ ⋆ v_ℂ`:
`∫ v(u)v(u+y) du = ∫ v(t) v(y−t) dt` (substitute `u = −t`, use `v(−t) = v(t)`). -/
theorem ofReal_autocorr_eq_convolution (hv : ∀ u, v (-u) = v u) :
    (fun y => (Params.autocorr v y : ℂ)) =
      convolution (fun u => (v u : ℂ)) (fun u => (v u : ℂ)) (ContinuousLinearMap.mul ℂ ℂ)
        volume := by
  funext y
  rw [convolution_def, Params.autocorr, ← integral_ofReal_C, ← integral_neg_eq_self]
  congr 1 with t
  rw [hv, ContinuousLinearMap.mul_apply', neg_add_eq_sub]
  push_cast
  ring

theorem autocorr_continuous_of_even (hv : ∀ u, v (-u) = v u) (hc : Continuous v)
    (hs : HasCompactSupport v) : Continuous (Params.autocorr v) := by
  have hsC : HasCompactSupport (fun u => (v u : ℂ)) := hs.comp_left Complex.ofReal_zero
  have hcC : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hc
  have : Continuous (fun y => (Params.autocorr v y : ℂ)) := by
    rw [ofReal_autocorr_eq_convolution hv]
    exact hsC.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
      (hcC.locallyIntegrable) hcC
  simpa [Function.comp_def] using Complex.continuous_re.comp this

theorem autocorr_integrable_of_even (hv : ∀ u, v (-u) = v u) (hc : Continuous v)
    (hs : HasCompactSupport v) : Integrable (Params.autocorr v) := by
  have hsC : HasCompactSupport (fun u => (v u : ℂ)) := hs.comp_left Complex.ofReal_zero
  have hcC : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hc
  have hiC : Integrable (fun u => (v u : ℂ)) := hcC.integrable_of_hasCompactSupport hsC
  have : Integrable (fun y => (Params.autocorr v y : ℂ)) := by
    rw [ofReal_autocorr_eq_convolution hv]
    exact hiC.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hiC
  simpa using this.re

/-- `(v ⋆ v)^ = (v̂)²` on ℝ for even real continuous compactly supported `v` — the paper's
"`(f∗g)^ = f̂ ĝ`" [Notation] through the dictionary and `Real.fourier_mul_convolution_eq`. -/
theorem paperFT_autocorr (hv : ∀ u, v (-u) = v u) (hc : Continuous v) (hs : HasCompactSupport v)
    (r : ℝ) :
    paperFT (fun y => (Params.autocorr v y : ℂ)) r = (paperFT (fun u => (v u : ℂ)) r) ^ 2 := by
  have hsC : HasCompactSupport (fun u => (v u : ℂ)) := hs.comp_left Complex.ofReal_zero
  have hcC : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hc
  have hiC : Integrable (fun u => (v u : ℂ)) := hcC.integrable_of_hasCompactSupport hsC
  rw [ofReal_autocorr_eq_convolution hv, paperFT_ofReal_eq_fourier, paperFT_ofReal_eq_fourier,
    Real.fourier_mul_convolution_eq hiC hiC, sq]

/-! ## Fourier inversion in the paper's convention, cosine form -/

/-- If `A : ℝ → ℝ` is continuous and integrable and `h_A(r) = G(r)` (`r ∈ ℝ`) with `G` real and
integrable, then `∫ G(r) cos(ry) dr = 2π A(y)`.  (Inversion `A = 𝓕⁻ 𝓕 A`, the substitution
`r = −2πξ`, and real parts; the sine part drops because `A` is real.)  This is the form in which
the paper uses "Fourier inversion" for `A_φ` [prop:trace, P-part] and `g` [eq:Phi2FT]. -/
theorem integral_mul_cos_of_paperFT_eq {A G : ℝ → ℝ} (hA : Continuous A) (hAi : Integrable A)
    (hG : Integrable G) (hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (G r : ℂ)) (y : ℝ) :
    ∫ r, G r * Real.cos (r * y) = 2 * π * A y := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set Ac : ℝ → ℂ := fun u => (A u : ℂ) with hAc
  have hF' : ∀ ξ : ℝ, 𝓕 Ac ξ = (G (-(2 * π) * ξ) : ℂ) := by
    intro ξ
    rw [fourier_eq_paperFT, ← hFT]
    congr 1
    push_cast
    ring
  have hF : 𝓕 Ac = fun ξ : ℝ => (G (-(2 * π) * ξ) : ℂ) := funext hF'
  have hFi : Integrable (𝓕 Ac) := by
    rw [hF]
    exact (hG.comp_mul_left' (by linarith : -(2 * π) ≠ 0)).ofReal
  have e1 : 𝓕⁻ (𝓕 Ac) y = Ac y :=
    hAi.ofReal.fourierInv_fourier_eq hFi (Complex.continuous_ofReal.comp hA).continuousAt
  set g : ℝ → ℂ := fun r => (G r : ℂ) * cexp ((-(y * r) : ℝ) * I) with hg
  have hgc : Continuous fun r : ℝ => cexp ((-(y * r) : ℝ) * I) := by fun_prop
  have hgi : Integrable g := by
    refine (hG.ofReal (𝕜 := ℂ)).norm.mono'
      ((hG.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hgc.aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    simp only [hg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  have e2 : 𝓕⁻ (𝓕 Ac) y = ∫ ξ, g (-(2 * π) * ξ) := by
    rw [fourierInv_eq_fourier_neg, fourier_eq_paperFT, paperFT_def]
    congr 1 with ξ
    rw [hF']
    simp only [hg]
    congr 2
    push_cast
    ring
  have e3 : (∫ r, g r).re = ∫ r, G r * Real.cos (r * y) := by
    rw [← integral_re_C hgi]
    congr 1 with r
    simp only [hg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg, mul_comm y r]
  have habs : |(-(2 * π))⁻¹| = (2 * π)⁻¹ := by
    rw [abs_inv, abs_neg, abs_of_pos hπ]
  have e2b : (∫ ξ, g (-(2 * π) * ξ)) = ((2 * π)⁻¹ : ℝ) • ∫ r, g r := by
    have := Measure.integral_comp_mul_left g (-(2 * π))
    rw [habs] at this
    exact this
  have e4 : A y = (2 * π)⁻¹ * ∫ r, G r * Real.cos (r * y) := by
    have := congrArg Complex.re (e1.symm.trans (e2.trans e2b))
    rw [Complex.smul_re, smul_eq_mul, e3] at this
    simpa [hAc] using this
  rw [e4, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]

end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/

theorem phi_sq_even (u : ℝ) : phi ϱ L w (-u) ^ 2 = phi ϱ L w u ^ 2 := by rw [phi_even]

theorem phi_sq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => phi ϱ L w u ^ 2) :=
  (phi_hasCompactSupport hϱ hw).comp_left (g := fun x : ℝ => x ^ 2) (by simp)

theorem phiC_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (fun u => (phi ϱ L w u : ℂ)) :=
  Complex.continuous_ofReal.comp (phi_continuous hϱ hw hwL)

theorem phiC_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => (phi ϱ L w u : ℂ)) :=
  (phi_hasCompactSupport hϱ hw).comp_left Complex.ofReal_zero

theorem phiC_contDiff_two (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (phi ϱ L w u : ℂ)) :=
  (phiC_contDiff hϱ hw hwL).of_le (by norm_num)

/-- alias of `Strip.phiC_support`. -/
theorem phiC_supp (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := phiC_support hϱ hw

theorem phiSqC_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp ((phi_continuous hϱ hw hwL).pow 2)

theorem phiSqC_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
  (phi_hasCompactSupport hϱ hw).comp_left (g := fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) (by simp)

theorem phiSqC_contDiff_two (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) := by
  have := Complex.ofRealCLM.contDiff.comp (((phi_contDiff hϱ hw hwL).pow 2).of_le (m := 2) (by norm_num))
  simpa [Function.comp_def] using this

theorem phiSqC_supp (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (((phi ϱ L w u) ^ 2 : ℝ) : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  apply phiC_supp hϱ hw u
  intro h
  apply hu
  rw [Complex.ofReal_eq_zero] at h
  simp [h]

/-! #### real / even / conjugation symmetry (hypothesis-free: only "φ real and even" is used) -/

/-- `φ̂` real on ℝ: `φ̂(r) = ↑(Re φ̂(r))` for real `r` (φ even and real). -/
theorem phiHat_ofReal (r : ℝ) : phiHat ϱ L w r = (phiHatR ϱ L w r : ℂ) :=
  paperFT_ofReal_eq_re (v := phi ϱ L w) phi_even r

theorem Phi_ofReal (r : ℝ) : Phi ϱ L w r = (PhiR ϱ L w r : ℂ) :=
  paperFT_ofReal_eq_re (v := fun u => phi ϱ L w u ^ 2) phi_sq_even r

/-- "since `φ̂` is real on ℝ we have `conj φ̂(z̄) = φ̂(z)`" [text after eq:fk], stated as
`φ̂(conj z) = conj (φ̂ z)`. -/
theorem phiHat_conj (z : ℂ) : phiHat ϱ L w (starRingEnd ℂ z) = starRingEnd ℂ (phiHat ϱ L w z) := by
  unfold phiHat
  rw [conj_paperFT_ofReal, paperFT_neg_of_even phi_even]

theorem phiHatR_even (r : ℝ) : phiHatR ϱ L w (-r) = phiHatR ϱ L w r := by
  simp only [phiHatR, phiHat, Complex.ofReal_neg, paperFT_neg_of_even phi_even]

theorem PhiR_even (r : ℝ) : PhiR ϱ L w (-r) = PhiR ϱ L w r := by
  simp only [PhiR, Phi, Complex.ofReal_neg]
  rw [paperFT_neg_of_even (v := fun u => phi ϱ L w u ^ 2) phi_sq_even]

/-! #### continuity / differentiability on ℝ ("entire" is more than any consumer needs) -/

theorem phiHatR_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiHatR ϱ L w) :=
  (contDiff_re_paperFT_ofReal (phiC_continuous hϱ hw hwL) (phiC_hasCompactSupport hϱ hw)
    0).continuous

theorem PhiR_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (PhiR ϱ L w) :=
  (contDiff_re_paperFT_ofReal (phiSqC_continuous hϱ hw hwL) (phiSqC_hasCompactSupport hϱ hw)
    0).continuous

/-- `Φ` is `C¹` on ℝ (indeed entire; C¹ is what [prop:cross] differentiates). -/
theorem PhiR_contDiff_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 1 (PhiR ϱ L w) :=
  contDiff_re_paperFT_ofReal (phiSqC_continuous hϱ hw hwL) (phiSqC_hasCompactSupport hϱ hw) 1

/-! #### values at 0 -/

/-- `h_f(0) = ∫ f` for a real `f` (cast to ℂ). -/
theorem paperFT_ofReal_zero (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) 0 = ((∫ u, f u : ℝ) : ℂ) := by
  simp only [paperFT, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_complex_ofReal

/-- "`φ̂(0) ≤ L`". -/
theorem phiHatR_zero_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    phiHatR ϱ L w 0 ≤ L := by
  rw [phiHatR, phiHat, Complex.ofReal_zero, paperFT_ofReal_zero, Complex.ofReal_re]
  exact integral_phi_le hϱ hw hwL

/-- "`Φ(0) = aL`". -/
theorem PhiR_zero (_hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    PhiR ϱ L w 0 = aConst ϱ L w * L := by
  have hL : L ≠ 0 := by linarith
  rw [PhiR, Phi, Complex.ofReal_zero, paperFT_ofReal_zero, Complex.ofReal_re, aConst,
    mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]

theorem g_zero (_hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    g ϱ L w 0 = bConst ϱ L w * L := by
  have hL : L ≠ 0 := by linarith
  rw [g, Params.autocorr, bConst, mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1; funext u; rw [add_zero]; ring

theorem Aphi_zero (_hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Aphi ϱ L w 0 = aConst ϱ L w * L := by
  have hL : L ≠ 0 := by linarith
  rw [Aphi, Params.autocorr, aConst, mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1; funext u; rw [add_zero, sq]

/-! #### "`φ̂² = Â_φ` and `Φ² = ĝ` on ℝ" — convolution theorem -/

/-- "`φ̂² = (A_φ)^` on ℝ". -/
theorem phiHatR_sq_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    ((phiHatR ϱ L w r) ^ 2 : ℂ) = paperFT (fun u => (Aphi ϱ L w u : ℂ)) r := by
  have h := paperFT_autocorr (v := phi ϱ L w) phi_even (phi_continuous hϱ hw hwL)
    (phi_hasCompactSupport hϱ hw) r
  have h2 : paperFT (fun u => (phi ϱ L w u : ℂ)) r = (phiHatR ϱ L w r : ℂ) := phiHat_ofReal r
  rw [h2] at h
  exact h.symm

/-- "`Φ² = ĝ` on ℝ". -/
theorem PhiR_sq_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    ((PhiR ϱ L w r) ^ 2 : ℂ) = paperFT (fun u => (g ϱ L w u : ℂ)) r := by
  have h := paperFT_autocorr (v := fun u => phi ϱ L w u ^ 2) phi_sq_even
    ((phi_continuous hϱ hw hwL).pow 2) (phi_sq_hasCompactSupport hϱ hw) r
  have h2 : paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) r = (PhiR ϱ L w r : ℂ) :=
    Phi_ofReal r
  beta_reduce at h
  rw [h2] at h
  exact h.symm

/-! #### integrability of `φ̂², φ̂²|r|, Φ², Φ²|r|` (decay [eq:hfbound] via PaperFT.lean) -/

theorem integrable_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2) :=
  (integrable_re_paperFT_sq_and (phiC_contDiff_two hϱ hw hwL) (phiC_supp hϱ hw)).1

theorem integrable_phiHatR_sq_mul_abs (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2 * |r|) :=
  (integrable_re_paperFT_sq_and (phiC_contDiff_two hϱ hw hwL) (phiC_supp hϱ hw)).2

theorem integrable_PhiR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2) :=
  (integrable_re_paperFT_sq_and (phiSqC_contDiff_two hϱ hw hwL) (phiSqC_supp hϱ hw)).1

theorem integrable_PhiR_sq_mul_abs (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2 * |x|) :=
  (integrable_re_paperFT_sq_and (phiSqC_contDiff_two hϱ hw hwL) (phiSqC_supp hϱ hw)).2

/-! #### Plancherel / inversion identities -/

/-- Fourier inversion of `φ̂² = (A_φ)^` in cosine form: `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)`
(used at [prop:trace] P-part: "∫φ̂(τ−τ_k)²cos(τy)dτ = 2πA_φ(y)cos(τ_k y)"). -/
theorem integral_phiHatR_sq_mul_cos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (y : ℝ) : ∫ r, phiHatR ϱ L w r ^ 2 * Real.cos (r * y) = 2 * π * Aphi ϱ L w y :=
  integral_mul_cos_of_paperFT_eq (A := Aphi ϱ L w) (G := fun r => phiHatR ϱ L w r ^ 2)
    (autocorr_continuous_of_even phi_even (phi_continuous hϱ hw hwL) (phi_hasCompactSupport hϱ hw))
    (autocorr_integrable_of_even phi_even (phi_continuous hϱ hw hwL) (phi_hasCompactSupport hϱ hw))
    (integrable_phiHatR_sq hϱ hw hwL)
    (fun r => by rw [← phiHatR_sq_eq hϱ hw hwL r]; push_cast; ring) y

/-- [eq:Phi2FT]: "`∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (`y ∈ ℝ`)", in cosine form (`Φ²` is even
and real, so the sine part vanishes). -/
theorem integral_PhiR_sq_mul_cos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (y : ℝ) : ∫ x, PhiR ϱ L w x ^ 2 * Real.cos (x * y) = 2 * π * g ϱ L w y :=
  integral_mul_cos_of_paperFT_eq (A := g ϱ L w) (G := fun r => PhiR ϱ L w r ^ 2)
    (autocorr_continuous_of_even phi_sq_even ((phi_continuous hϱ hw hwL).pow 2)
      (phi_sq_hasCompactSupport hϱ hw))
    (autocorr_integrable_of_even phi_sq_even ((phi_continuous hϱ hw hwL).pow 2)
      (phi_sq_hasCompactSupport hϱ hw))
    (integrable_PhiR_sq hϱ hw hwL)
    (fun r => by rw [← PhiR_sq_eq hϱ hw hwL r]; push_cast; ring) y

/-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` (Plancherel; [prop:trace] μ-part, "∫φ̂(r)²dr = 2π∫φ² = 2πaL").
Obtained as the `y = 0` case of the inversion formula, with `A_φ(0) = ∫φ² = aL`. -/
theorem integral_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 = 2 * π * aConst ϱ L w * L := by
  have h := integral_phiHatR_sq_mul_cos hϱ hw hwL 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, Aphi_zero hϱ hw hwL]
  ring

/-- "`∫_ℝ Φ² = 2π g(0) = 2π b L`". -/
theorem integral_PhiR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ r, PhiR ϱ L w r ^ 2 = 2 * π * bConst ϱ L w * L := by
  have h := integral_PhiR_sq_mul_cos hϱ hw hwL 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, g_zero hϱ hw hwL]
  ring

end PhigA

end Taper

end Zeta23
